From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun.
From mathcomp Require Import div finset seq fintype finfun choice.
From pcm Require Import axioms prelude ordtype finmap pred pcm.
From pcm Require Import unionmap heap autopcm automap.
From htt Require Import options model heapauto llist array.
From htt Require Import kvmaps hashtab congmath.

(***********************************)
(* Congruence closure verification *)
(***********************************)

(* Spec, code and proofs for the verification of the *)
(* Barcelogic Congruence Closure algorithm. *)
(* Described in the POPL10 paper: *)
(* Structure the verification of heap-manipulating programs *)
(* by Nanevski, Vafeiadis and Berdine *)

(* This file contains the verification of the stateful programs. *)
(* The associated math properties used in the verification are *)
(* proved in the accompanying file congmath.v *)

Notation finE := finset.inE.

Prenex Implicits sepit.
Arguments nil {K V}.

From mathcomp Require Import bigop.
From Coq Require Import Setoid.
Prenex Implicits star.

Add Parametric Morphism U : (@star U) with signature
 @Eq_Pred _ _ ==> @Eq_Pred _ _ ==> @Eq_Pred _ _ as star_morph.
Proof.
move=>x y E x1 y1 E1 m /=.
split; case=>h1 [h2][-> H1 H2]; exists h1, h2; split=>//.
  by apply/E. by apply/E1.
  by apply/E. by apply/E1.
Qed.

Lemma sepit0' (U : pcm) A (f : A -> Pred U) : 
        IterStar.sepit [::] f <~> emp.
Proof. exact: IterStar.sepit0. Qed.

Lemma sepit_cons' (U : pcm) A x (s : seq A) (f : A -> Pred U) : 
        IterStar.sepit (x :: s) f <~> 
        f x # IterStar.sepit s f.
Proof. exact: IterStar.sepit_cons. Qed.

Lemma sepitX (U : pcm) A (s : seq A) (f : A -> Pred U) : 
         IterStar.sepit s f <~>
         \big[star/emp]_(i <- s) f i.
Proof. 
elim: s=>[|x s IH]. 
- rewrite sepit0'. rewrite big_nil. by [].
rewrite sepit_cons'.
rewrite big_cons. 
move=>m. 
split; case=>h1 [h2][Em H1 H2]; exists h1, h2; split=>//.
- by rewrite -IH. 
by rewrite IH.
Qed.

Lemma Iter_sepit0 (U : pcm) A (f : A -> Pred U) : 
        IterStar.sepit [::] f <~> emp.
Proof. by rewrite sepitX big_nil. Qed.

Lemma sepit_cons (U : pcm) A x (s : seq A) (f : A -> Pred U) : 
        IterStar.sepit (x::s) f <~> f x # IterStar.sepit s f.
Proof. by rewrite sepitX big_cons sepitX. Qed.

(* U has the laws of commutative monoids from bigop *)
(* but doesn't really, as it's up to extensional equality *)
Lemma starA (U : pcm) (x y z : Pred U) : 
        x # y # z <~> (x # y) # z.
Proof.
move=>m /=; split; case=>h1 [h2][H1 H2].
- case=>h3 [h4][H3 H4 H5]. 
  subst h2.
  eexists (h1 \+ h3), h4.  rewrite -joinA. split=>//.
  by exists h1, h3. 
case: H2=>h3 [h4][? H2 H3 H4]. subst h1.
exists h3, (h4 \+ h2). rewrite joinA. split=>//.
by exists h4, h2.
Qed.

Lemma starC (U : pcm) (x y : Pred U) : 
        x # y <~> y # x.
Proof.
move=>m /=.
split.
- case=>h1 [h2][H H1 H2].
  exists h2, h1. rewrite joinC. by [].
case=>h1 [h2][H H1 H2].
exists h2, h1. by rewrite joinC.
Qed.

Lemma starL (U : pcm) (x : Pred U) : 
        emp # x <~> x.
Proof.
move=>m /=.
split.
- case=>h1 [h2][->->]. rewrite unitL. by [].
move=>H.
exists Unit, m. rewrite unitL. by [].
Qed.

Lemma starR (U : pcm) (x : Pred U) : 
        x # emp <~> x.
Proof. by rewrite starC starL. Qed.

(*
HB.instance Definition _ (U : pcm) := 
  Monoid.isComLaw.Build (Pred U) emp (@star U) (@starA U) (@starC U) (@starL U).
*)

Lemma big_sepit_seq (U : pcm) A (s : seq A) (f : A -> U) m : 
        m = \big[join/Unit]_(i <- s) f i  <->
        m \In IterStar.sepit s (fun i h => h = f i).
Proof.
rewrite sepitX.
elim: s m=>[|x xs IH] /= m.
- by rewrite !big_nil.
rewrite !big_cons. 
split.
- move=>E. rewrite InE. exists (f x), (\big[join/Unit]_(j <- xs) f j).
  split=>//. rewrite -IH. by [].
case=>h1 [h2][Em H1 H2]. rewrite -toPredE /= in H1.
rewrite Em H1.  
congr (_ \+ _).
by rewrite IH.
Qed.

Lemma Iter_sepit_emp (U : pcm) (A : eqType) (s : seq A) (f : A -> Pred U) : 
         (forall x, x \in s -> f x <~> emp (U:=U)) -> 
         IterStar.sepit s f <~> emp.
Proof.
move=>H. 
rewrite sepitX.
elim: s H=>[|a xs IH] H.
- by rewrite big_nil.
rewrite big_cons.
rewrite H; last by rewrite inE eqxx.
rewrite starL IH //.  
move=>x X. apply: H.
by rewrite inE X orbT.
Qed.


Lemma big_sepit (U : pcm) (I : finType) (s : {set I}) (f : I -> U) m : 
        m = \big[join/Unit]_(i in s) (f i) <->
        m \In sepit s (fun i h => h = f i).
Proof. by rewrite /sepit /= -big_sepit_seq -big_enum. Qed.

(* empty congruence only relates constant symbols to themselves *)
Definition empty_cong s := closure (graph (@const s)).

(*************)
(* Signature *)
(*************)

Module Type CongrSig.
(* abstract type for collection of root pointers *)
(* seq const is the list of constants over which *)
(* structure computes *)
(* this is a global argument, hence exposed by tp *)
Parameter tp : seq constant -> Set. 

(* abstract predicate tying roots, (congruence) relation, heap *)
Parameter shape : forall {s}, tp s -> rel_exp s -> Pred heap.

(* initialize empty congruence structure; return roots *)
Parameter init : forall {s}, 
  STsep (emp, [vfun rt m => m \In shape rt (empty_cong s)]).

(* merge new equation into the structure rooted by rt *)
Parameter merge : forall {s} rt (e : Eq s),
  STsep {R} (fun i => i \In shape rt R,
            [vfun (_ : unit) m => 
               m \In shape rt (closure (R \+p eq2rel e))]).

(* check if two expressions are congruent in the structure rooted by rt *)
Parameter check : forall {s} rt (t1 t2 : exp s),
  STsep {R} (fun i => i \In shape rt R,
            [vfun (b : bool) m => m \In shape rt R /\ 
               (b <-> (t1, t2) \In R)]).
End CongrSig.

(******************)
(* Implementation *)
(******************)

(* faithful to Barcelogic's actual implementation *)

Module Congr : CongrSig.
Section Congr.
Variable s : seq constant.
Notation symb := (symb s).

(* the lookup table is represented as a hash table with 10 buckets *)
Local Definition K : Set := symb * symb.
Local Definition V : Set := symb * symb * symb.

Definition hash (n : nat) (k : K) := index k (enum (@predT K)) %% n.

Lemma hash_ord n k : 
        0 < n -> 
        hash n k < n.
Proof. exact: ltn_pmod. Qed.

Definition hash10 k : 'I_10 := Ordinal (@hash_ord 10 k erefl).

(* the tables relating arrays with the content of the lists *)
(* ctab is for class lists, utab is for use lists *)

Definition llist (T : Set) : Set := ptr.

Definition ctab := @table symb ptr (seq symb) (@lseq symb). 
Definition utab := 
  @table symb ptr (seq (symb * symb * symb)) (@lseq (symb * symb * symb)).

Definition n := #|{: symb}|.

(* roots for the structure *)
(* all components are isomorphic to pointers *)
Inductive ptrs : Set :=
  Ptrs of 
   (* array of representatives; for each c *)
   (* returns symbol that represents c's class *)
   {array symb -> symb} & 
   (* class list; for each c *)
   (* singly-linked list storing whole class of c *)
   {array symb -> llist symb} &
   (* use list; internal structure *)
   (* see the paper for description *)
   {array symb -> llist (symb*symb*symb)} & 
   (* hash table; for each pair of representatives *)
   (* stores equations; see paper for description *)
   htab V hash10 & 
   (* list of pending equations *)
   ptr.

(* renaming type to satisfy the signature check *)
Definition tp := ptrs.

Section ShapePredicates.
Variable rt : ptrs.
Notation r := (let: Ptrs r _ _ _ _ := rt in r).
Notation clist := (let: Ptrs _ clist _ _ _ := rt in clist).
Notation ulist := (let: Ptrs _ _ ulist _ _ := rt in ulist).
Notation htb := (let: Ptrs _ _ _ htb _ := rt in htb).
Notation p := (let: Ptrs _ _ _ _ p := rt in p).

(* Data structure's layout in the heap *)

Definition ashape D :=
  [Pred h | let: (d, ct, ut) := D in
     h \In 
     Array.shape r (rep d : {ffun symb -> symb}) #
     (Array.shape clist ct # sepit setT (ctab ct (class d))) #
     (Array.shape ulist ut # sepit setT (utab ut (use d))) #
     kvm_shape htb (lookup d) #
     [Pred h' | exists l, h' \In Pred1 (p :-> l) # lseq l (pending d)]].

Definition bshape d :=
  [Pred h | class_inv d /\ exists ct ut, h \In ashape (d, ct, ut)].

Definition shape (R : rel_exp s) : Pred heap :=
  [Pred h | exists d, h \In bshape d /\ propagate_inv d /\
                      pending d = [::] /\ CRel d <~> R].

End ShapePredicates.  

(* Initialization procedure to generate *)
(* the empty structure and its root pointers *)

Definition iT (clist : {array symb -> llist symb}): Type := forall k,
  STsep (fun i => k <= n /\ exists f, i \In Array.shape clist f #
            sepit [set c | indx c < k] (ctab f [ffun c => [:: c]]),
        [vfun (_ : unit) m => exists f, m \In Array.shape clist f #
            sepit setT (ctab f [ffun c => [:: c]])]).

Program Definition init :
  STsep (emp, [vfun rt m => m \In shape rt (empty_cong s)]) :=
  Do (rx <-- Array.newf [ffun x : symb => x];
      cl <-- Array.new null;
      ffix (fun (loop : iT cl) k =>
           Do (if decP (b:= k < n) idP is left pf then 
                 x <-- allocb (ith k pf) 2;
                 x.+1 ::= null;;
                 Array.write cl (ith k pf) x;;
                 loop k.+1
               else ret tt)) 0;;
      ul <-- Array.new null;
      htb <-- kvm_new (htab V hash10);
      p <-- alloc null;
      ret (Ptrs rx cl ul htb p)).
Next Obligation. 
case=>i [pf][/= f][hc][hct][->{i} Hc Hct].
case: decP=>[{}pf|] /=; last first.
- case: (ltngtP k n) pf=>// Ekn _ _; step=>_.
  exists f, hc, hct; split=>//. 
  apply: tableP2 Hct=>// x; rewrite !finE Ekn.
  by rewrite /n cardE index_mem /index mem_enum.
step=>x; step; apply: [stepX f]@hc=>//= [[m]] Em.
apply: [gE]=>//=; split=>//.
eexists [ffun z => if z == ith k pf then x else f z].
rewrite (_ : _ \+ _ = m \+ (x :-> ith k pf \+ 
  x.+1 :-> null \+ hct)); last by heap_congr.
hhauto; rewrite (sepitS (ith k pf)) finE /= indx_ith ltnSn. 
rewrite /ctab/table !ffunE eqxx; hhauto.
apply: tableP2 Hct=>// a. 
- by rewrite !finE ltnS indx_injE; case: ltngtP.
by rewrite !finE !ffunE indx_injE; case: eqP=>// ->; rewrite ltnn.
Qed.
Next Obligation.
case=>_ ->; apply: [stepE]=>//= rx hr Er; apply: [stepU]=>//= cl hc Ec.
apply: [stepX]@hc=>//=.
- split=>//; exists [ffun x => null], hc, Unit; rewrite unitR.
  by split=>//; rewrite (_ : [set c | indx c < 0] = set0) // sepit0.
case=>_ [f][hc'][hrest][-> Hc' Hrest].
apply: [stepU]=>//= ul hu Ehu; apply: [stepU]=>//= htb ht Ht.
set d := Data [ffun x => x] [ffun c => [:: c]] [ffun c => [::]] (@nil K V) [::].
step=>px; step; exists d; split; last by case: (initP s).
split=>[a b|/=]; first by rewrite !ffunE !inE. 
exists f, [ffun s => null].
rewrite (_ : px :-> null \+ _ = hr \+ ((hc' \+ hrest) \+ (hu \+ Unit \+ 
  (ht \+ (px :-> null \+ Unit))))); last by rewrite unitR; heap_congr. 
hhauto; rewrite /sepit Iter_sepit_emp // => k.
by rewrite /utab/table !ffunE; split=>//; case=>_ ->.
Qed.

(* Method implementations use various input root pointers. *)
(* These are given explicit names as projections from rt. *)

Section Internal.
Variable rt : ptrs.
Notation ashape' := (ashape rt).
Notation bshape' := (bshape rt).
Notation shape' := (shape rt).

Notation r := (let: Ptrs r _ _ _ _ := rt in r).
Notation clist := (let: Ptrs _ clist _ _ _ := rt in clist).
Notation ulist := (let: Ptrs _ _ ulist _ _ := rt in ulist).
Notation htb := (let: Ptrs _ _ _ htb _ := rt in htb).
Notation p := (let: Ptrs _ _ _ _ p := rt in p).

Definition cT (a' b' : symb) : Type :=
  forall x : unit, STsep {D}
    (fun i => i \In ashape' D /\ a' != b',
    [vfun (_ : unit) m => exists ct, exists ut,
       let: (d, _, _) := D in
        m \In ashape'
               (Data [ffun s => if s \in class d a' then b'
                                else rep d s]
                     [ffun s => if s == a' then [::] else
                                if s == b' then rev (class d a') ++ class d b'
                                else class d s]
                     (use d) (lookup d) (pending d), ct, ut)]).

Program Definition join_hclass (a' b' : symb) :
  STsep {d} (fun i => i \In bshape' d /\ a' != b',
            [vfun (_ : unit) m => m \In bshape' (join_class d a' b')]) :=
  Do (ffix (fun (loop : cT a' b') (xx : unit) =>
        Do (a <-- Array.read clist a';
            b <-- Array.read clist b';
            if a == null then ret tt
            else
              s <-- !a;
              next <-- !a.+1;
              a.+1 ::= b;;
              Array.write clist b' a;;
              Array.write clist a' next;;
              Array.write r s b';;
              loop tt)) tt).
Next Obligation.
case=>[[[/= d ct] ut]][i][H N] /=.
case: H=>/= rh [_][->{i} Rh][_][h][->][th][ctx][->] Th Ctx H. 
rewrite (sepitT1 a') in Ctx; case: Ctx=>cta [w][->{ctx}Cta].
rewrite (sepitS b') !finE eq_sym {1}N /=.  
case=>ctb [ctx][->{w}Ctb Ctx]; rewrite /ctab/table in Cta Ctb.
apply: [stepX ct, th]@th=>//= _ _ [->->].
apply: [stepX ct, th]@th=>//= _ _ [->->].
apply: vrfV=>V; case: (ct a' =P null) Cta=>[/[dup] Ea' ->|/eqP Na'].
- case/(lseq_null (validX V))=>/= ->->{cta V}; step=>{}V; exists ct, ut.
  rewrite (_ : rh \+ _ = rh \+ (th \+ (Unit \+ 
    (ctb \+ ctx)) \+ h)); last by heap_congr.
  rewrite -fin_eta; hhauto; rewrite (sepitT1 a'); hhauto.
  - by rewrite /ctab/table ffunE eqxx /= /= Ea'.
  rewrite (sepitS b') !finE eq_sym N; hhauto.
  - by rewrite /ctab/table /= ffunE eqxx eq_sym (negbTE N).
  apply: tableP Ctx=>// x; rewrite !finE andbT ffunE.
  by case/andP=>/negbTE -> /negbTE ->.
case/(lseq_pos Na')=>a {V} [next][cta'][Eca ->{cta}Cta'].
do 3!step; apply: [stepX ct]@th=>//= [_] {th Th} th1 Th1.
set ct1 := (finfun _) in Th1.
apply: [stepX ct1]@th1=>//= [_] {th1 Th1} th2 Th2.
set ct2 := (finfun _) in Th2.
apply: [stepX rep d]@rh=>//= _ {rh Rh} rh1 Rh1.
set r1 := (finfun _) in Rh1.
set cv2 := [ffun z => if z == a' then (behead (class d a'))
            else if z == b' then a :: class d b' else class d z].
apply: [gE (Data r1 cv2 (use d) (lookup d) (pending d), ct2, ut)]=>/=; 
last by move=>?? [].
- rewrite (_ : rh1 \+ _ = rh1 \+ (th2 \+ (cta' \+ (ct a' :-> a \+ 
    ((ct a').+1 :-> ct b' \+ ctb) \+ ctx)) \+ h)); last by heap_congr.
  hhauto; rewrite (sepitT1 a'); hhauto. 
  - by rewrite /ctab/table/ct2/cv2 !ffunE /= eqxx.
  rewrite (sepitS b') !finE eq_sym N; hhauto.
  - rewrite /ctab/table/ct2/cv2/ct1 !ffunE /= ffunE /= eqxx;
    by rewrite eq_sym (negbTE N); hhauto.
  apply: tableP Ctx=>x; rewrite /ct2/cv2/ct1 !ffunE /= ?ffunE /=;
  by rewrite !finE andbT; case/andP=>/negbTE -> /negbTE ->.
case=>m [{Th2}ct2][ut2] /= Hm _; exists ct2, ut2.
congr (m \In ashape' (Data _ _ _ _ _, ct2, ut2)): Hm; apply/ffunP=>x.
- by rewrite !ffunE eqxx {2}Eca inE /=; case: (x =P a)=>//= _; rewrite if_same.
rewrite !ffunE !eqxx /= (eq_sym b') (negbTE N).
case: (x =P a')=>// _; case: (x =P b')=>// _.  
by rewrite Eca rev_cons cat_rcons.
Qed.
Next Obligation.
case=>d [i][[C]][/= ct][ut H] N.
apply: [gE (d, ct, ut)]=>//= [[m]][ct1][ut1] W _. 
set d' := (Data _ _ _ _ _) in W; suff E : join_class d a' b' = d'.
- by split; [apply: join_class_classP|rewrite E; eauto].
by congr Data; apply/ffunP=>x; rewrite !ffunE /= C.
Qed.

Definition uT (a' b' : symb) := forall x : unit,
  STsep {d} (fun i => exists don, a' != b' /\
               i \In bshape' (join_use' d a' b' don) /\
               use d a' = don ++ use (join_use' d a' b' don) a',
            [vfun (_ : unit) m => m \In bshape' (join_use d a' b')]).

Program Definition join_huse (a' b' : symb) :
  STsep {d} (fun i => a' != b' /\ i \In bshape' d,
            [vfun (_ : unit) m => m \In bshape' (join_use d a' b')]) :=
  Do (ffix (fun (loop : uT a' b') xx =>
       Do (a <-- Array.read ulist a';
           if a == null then ret tt
           else
             eq <-- !a;
             next <-- !a.+1;
             Array.write ulist a' next;;
             c1 <-- Array.read r eq.1.2;
             c2 <-- Array.read r eq.2;
             v <-- kvm_lookup htb (c1, c2);
             if v is Some d then 
               dealloc a;;
               dealloc a.+1;;
               p' <-- !p;
               q <-- insert p' (comp_pend eq d);
               p ::= q;;
               loop tt
             else 
               kvm_insert htb (c1, c2) eq;;
               b <-- Array.read ulist b';
               a.+1 ::= b;;
               Array.write ulist b' a;;
               loop tt)) tt).
Next Obligation.
case=>[/= d][i][don][N][H Eu].
set d1 := join_use' d a' b' don in H Eu.  
case: H=>C [/= ct][ut][rh][_][->{i} Rh][cth][_][-> Htc][_][_][->]
[ru][hu][-> Ut Hu][ht][_][-> Ht][p'][_][hp][->-> Hp]. 
move: Hu; rewrite (sepitT1 a'); case=>ha' [w][->{hu} Ua]. 
rewrite (sepitS b') !finE eq_sym {1}N; case=>hb' [h][->{w} Ub R]. 
rewrite /utab/table/= in Ua Ub. 
apply: [stepX ut, ru]@ru=>//= _ _ [->->]; apply: vrfV=>V.
case: (ut a' =P null) Ua=>[/[dup] Ea' ->|/eqP Na' {V}].
- case/(lseq_null (validX V))=>/= {V} Eu1 ->{ha'}; step.
  rewrite (_ : rh \+ _ = rh \+ (cth \+ (ru \+ (Unit \+ (hb' \+ h)) \+ 
    (ht \+ (p:-> p' \+ hp))))); last by heap_congr.
  rewrite /join_use Eu Eu1 cats0 -/d1; split=>//=; exists ct, ut.
  hhauto; rewrite (sepitT1 a'); hhauto; first by rewrite /utab/table Ea' Eu1.
  by rewrite (sepitS b') !finE eq_sym N; hhauto.    
case/(lseq_pos Na')=>[[[c1 c2 c3]]][nxt][hh][Eu1 ->{ha'} Hh]; step; step.
set c := (c1, c2, c3) in Eu1 *; apply: [stepX ut]@ru=>//= [[]] {Ut}ru Ut2.
set ut2 := (finfun _) in Ut2.
apply: [stepX rep d1, rh]@rh=>//= _ _ [->->].
apply: [stepX rep d1, rh]@rh=>//= _ _ [->->].
apply: [stepX lookup d1]@ht=>//= v {Ht}ht [Ht Eqv].
rewrite Eu1 in Eu; set d2 := join_use' d a' b' (don ++ [:: c]).
set a1' := behead (use d1 a') in Eu.
have Eu2 : use d2 a' = a1'.
- by rewrite /d2 (join_useT (t:=behead (use d1 a'))) //; apply: join_use_useE.  
have Ej2: join_use d2 a' b' = join_use d1 a' b'.
- rewrite /join_use/d2 Eu2.
  by rewrite -!(join_useT (t:=[::])) ?cats0 -?catA //= ?Eu -?Eu1.
case: v Eqv=>[[[e1 e2 e3]]|] /= /esym Eqv.
- set e := (e1, e2, e3) in Eqv.
  do 3!step; apply: [stepX pending d1]@hp=>//= q _ [r0][{Hp}hp [-> Hp]]. 
  step; apply: [gE d]=>[||??[]] //=.
  exists (don ++ [:: c]); rewrite -/d2 Eu2 -catA; do 2!split=>//.
  rewrite /bshape'/class_inv/ashape/d2 (join_useT (t:=a1')) //= Eqv -/d1 /=.  
  rewrite (_ : _ \+ _ = rh \+ (cth \+ ((ru \+ (hh \+ (hb' \+ h))) \+ (ht \+ 
     (p :-> q \+ (q :-> comp_pend c e \+ 
    (q.+1 :-> r0 \+ hp))))))); last by heap_congr.
  case: Htc=>x [y][->] X1 X2; hhauto; [eauto|eauto|exact: Ut2|].
  rewrite (sepitT1 a'); hhauto.
  - by rewrite /utab/table/ut2 !ffunE /= eqxx.
  rewrite (sepitS b') !finE eq_sym N; hhauto.
  - by rewrite /utab/table/ut2 !ffunE /= eq_sym (negbTE N). 
  apply: tableP R=>a /=; rewrite !finE andbT /ut2 ?ffunE /=;
  by case/andP=>_ /negbTE ->.
apply: [stepX lookup d1]@ht=>//= [[{Ht}ht Ht]].  
apply: [stepX ut2, ru]@ru=>//= _ _ [->->]; step.
apply: [stepX ut2]@ru=>//= [[]] {Ut2}ru Ut3; set ut3 := (finfun _) in Ut3. 
apply: [gE d]=>[||??[]] //=; exists (don ++ [:: c]). 
rewrite -/d2 Eu2 -catA; do 2!split=>//.
rewrite /bshape'/class_inv/ashape/d2 (join_useT (t:=a1')) //= Eqv -/d1 /=.  
rewrite (_ : _ \+ _ = rh \+ (cth \+ ((ru \+ (hh \+ ((ut a' :-> c \+
 ((ut a').+1 :-> ut2 b' \+ hb')) \+ h))) \+ (ht \+ (p :-> p' \+ hp))))); 
  last by heap_congr.
case: Htc=>x [y][->] X1 X2; hhauto; [eauto|eauto|exact: Ut3|].
rewrite (sepitT1 a'); hhauto.
- by rewrite /utab/table/ut3 ffunE /= (negbTE N) /ut2 !ffunE /= eqxx. 
rewrite (sepitS b') !finE eq_sym N /=; hhauto. 
- by rewrite /utab/table/=/ut3 !ffunE /= eqxx eq_sym (negbTE N); hhauto.
apply: tableP R=>a /=; rewrite !finE andbT /ut3/ut2 !ffunE /= ?ffunE /=;
by case/andP=>/negbTE -> /negbTE ->.
Qed.
Next Obligation.
by case=>d [i][N H]; apply: [gE d]=>[||??[]] //; exists [::]. 
Qed.

Definition pT : Type := forall x : unit,
  STsep {d} (fun i => i \In bshape' d,
            [vfun (_ : unit) m => m \In bshape' (propagate d)]).

(* left/right symbol in pending equation *)
Definition pendL (e : pend s) :=
  let: (simp_pend a _ | comp_pend (a,_,_) _) := e in a.
Definition pendR (e : pend s) :=
  let: (simp_pend _ b | comp_pend _ (b,_,_)) := e in b.

Program Definition hpropagate :=
  ffix (fun (loop : pT) x =>
       Do (q <-- @read ptr p;
           if q == null then ret tt (* pending list is empty *)
           else
             eq <-- !q;
             next <-- !q.+1;
             p ::= (next : ptr);;
             dealloc q;;
             dealloc q.+1;;
             a' <-- Array.read r (pendL eq);
             b' <-- Array.read r (pendR eq);
             if a' == b' then loop tt : ST _
             else 
               join_hclass a' b';;
               join_huse a' b';;
               loop tt)) tt.
Next Obligation.
case=>/= d [i][C][/= ct][ut][hr][_][-> Hr][hc][_][-> Hc]
[hu][_][-> Hu][ht][_][-> Ht][q][_][hp][->] -> Hp.
step; case: (q =P null) Hp=>[->{q}|/eqP N] Hp.
- apply: vrfV=>V; case/(lseq_null (validX V)): Hp=>{V} Ep /= ->{hp}.
  step; rewrite propagate_equation Ep; split=>//=.
  by exists ct, ut; hhauto; rewrite Ep.
case/(lseq_pos N): Hp=>eq [next][hnext][Ep] ->{hp} Hp; do !step. 
apply: [stepX rep d, hr]@hr=>//= a' _ [-> Ea']. 
apply: [stepX rep d, hr]@hr=>//= b' _ [-> Eb']. 
set d1 := Data (rep d) (class d) (use d) (lookup d) (behead (pending d)).
case: ifPn=>[E|E].  
- have T1 : propagate d = propagate d1.
  - rewrite propagate_equation Ep.
    by case: eq Ep Ea' Eb' E=>[a2 b2 _|[[a2 ??]][[b2 ??]] _] ->->->.
  apply: [gE d1]=>[||??[] //] /=; last by rewrite T1.
  by split=>//=; exists ct, ut; hhauto.
apply: [stepE d1]=>//=; first by do 2split=>//; exists ct, ut; hhauto.
set d2 := (join_class _ _ _); case=>m H; apply: [stepE d2]=>//= [[n]] Hn.
set d3 := (join_use _ _ _) in Hn.
suff -> : propagate d = propagate d3 by apply: [gE d3]. simpl in Hu.
rewrite /d3/d2 propagate_equation Ep;
by case: eq Ep Ea' Eb' E=>[a2 b2 _|[[a2 ??]][[b2 ??]] _] ->-> /negbTE ->. 
Qed.

Program Definition merge (e : Eq s) :
    STsep {R} (fun i => i \In shape' R,
              [vfun (_ : unit) m => 
                   m \In shape' (closure (R \+p eq2rel e))]) :=
  match e with
  | simp_eq a b =>
      Do (q <-- !p;
          x <-- insert q (simp_pend a b);
          p ::= x;;
          hpropagate)
  | comp_eq c c1 c2 =>
      Do (c1' <-- Array.read r c1;
          c2' <-- Array.read r c2;
          v <-- kvm_lookup htb (c1', c2');
          if v is Some b then 
            q <-- !p;
            x <-- insert q (comp_pend (c, c1, c2) b);
            p ::= x;;
            hpropagate
          else
            kvm_insert htb (c1', c2') (c, c1, c2);;
            u1 <-- Array.read ulist c1';
            x <-- insert u1 (c, c1, c2);
            (* if c1' == c2' the equation will be added twice *)
            (* but this is okay, so we need not check for equality *)
            (* this will rarely occur in practice, because an equation *)
            (* c = c1' c1' means that a function c1' is applied to itself *)
            (* so by avoiding the check, we optimize for the common case *)
            (* this complicates the proof somewhat, however *)
            Array.write ulist c1' x;;
            u2 <-- Array.read ulist c2';
            x <-- insert u2 (c, c1, c2);
            Array.write ulist c2' x)
   end.
Next Obligation.
case=>R [_][d][[C]][/= ct][ut][hr][_][-> Hr][hc][_][-> Hc][_][_]
[->][hu][hu'][-> Hu Hu'][ht][_][-> Ht][q][_][hp][->] -> Hp [PI][Ep Erel].
step; apply: [stepX (pending d)]@hp=>//= x _ [r0][{Hp}hp][-> Hp].
set d1:=Data (rep d) (class d) (use d) (lookup d) (simp_pend a b :: pending d).
step; apply: [gE d1]=>//=.
- rewrite Ep /= in Hp; case: Hp=>->{r0} ->{hp}.
  rewrite (_ : _ \+ _ = hr \+ (hc \+ (hu \+ hu' \+ (ht \+ 
    (p :-> x \+ (x :-> simp_pend a b \+ (x.+1 :-> null \+ Unit))))))); 
  last by heap_congr.
  by split=>//=; exists ct, ut; hhauto; rewrite Ep.
case=>m Hm _.
have L: propagate_inv d1 by apply: propagate_pendP PI.
case: (propagatePE L)=>L1 [L2 L3]; exists (propagate d1); do 3!split=>//.
by rewrite -L3 -Erel clos_clos /CRel -!orrA orrAC.
Qed.
Next Obligation.
case=>R [_][d][[C]][/= ct][ut][hr][_][-> Hr][hc][_][-> H]
[_][_][->][hu][hu'][-> Hu Hu'][ht][_][-> Ht][q][_]
[hp][->] -> Hp [PI][Ep Erel]; set cx := (c, c1, c2).
apply: [stepX rep d, hr]@hr=>//= _ _ [->->].
apply: [stepX rep d, hr]@hr=>//= _ _ [->->].
apply: [stepX lookup d]@ht=>//= v {Ht}ht [Ht Ev].
case: v Ev=>[[[e0 e1 e2]]|] Ev. 
- set ex := (e0, e1, e2).
  set d1 := Data (rep d) (class d) (use d) 
                 (lookup d) (comp_pend cx ex :: pending d).
  step; apply: [stepX pending d]@hp=>//= x _ [x1][{}hp][-> {}Hp]. 
  step; apply: [gE d1]=>//=.
  - rewrite (_ : _ \+ _ = hr \+ (hc \+ (hu \+ hu' \+ (ht \+ (p :-> x \+ 
      (x :-> comp_pend cx ex \+ (x.+1 :-> x1 \+ hp))))))); 
    last by heap_congr.
    by split=>//; exists ct, ut; hhauto.
  case=>m Hm _.
  have L : propagate_inv d1 by apply: propagate_pendP PI.
  case: (propagatePE L)=>L1 [L2] L3; exists (propagate d1).
  by rewrite -L3 -Erel propagate_clos_pendP.
apply: [stepX lookup d]@ht=>//= _ {Ht}ht Ht. 
apply: [stepX ut, hu]@hu=>//= _ _ [->->].
move: Hu'; rewrite (sepitT1 (rep d c1)).
case=>hu'' [hu2][->{hu'} Hu'' Hu'].
apply: [stepX use d (rep d c1)]@hu''=>//= x _ [r0][{Hu''}hu''][-> Hu''].
apply: [stepX ut]@hu=>//= _ {Hu}hu Hu; set ut1 := (finfun _) in Hu.
apply: [stepX ut1, hu]@hu=>//= _ _ [->->]. 
set u1' := [ffun z => if z == rep d c1 then cx :: use d z else use d z].
set u' := [ffun z => if z == rep d c2 then cx :: u1' z else u1' z].
set l' := (ins _ _ _) in Ht.
set d1 := Data (rep d) (class d) u' l' (pending d).
pose ut2 x' := [ffun z => if z == rep d c2 then x' else ut1 z].
case E : (rep d c2 == rep d c1).
- apply: [stepX cx::use d (rep d c1)]@(x :-> _ \+ x.+1 :-> _ \+ hu'')=>//=.
  - by exists r0, hu''; rewrite joinA (eqP E) /ut1 !ffunE /= eqxx.  
  move=>v {Hu''}_ [x'][_][->][r1][{}hu''][-> Hu'']. 
  apply: [gX ut1]@hu=>//= [[]] {Hu}hu Hu _.
  rewrite (_ : _ \+ _ = hr \+ (hc \+ (hu \+ (v :-> cx \+ 
    (v.+1 :-> x' \+ (x' :-> cx \+ (x'.+1 :-> r1 \+ hu''))) \+ 
      hu2) \+ (ht \+ (p :-> q \+ hp))))); last by heap_congr.
  exists d1; split=>//; last first.
  - split; first by apply: propagate_nopendP.
    by rewrite -Erel propagate_clos_nopendP.
  split=>//=; exists ct, (ut2 v); hhauto.
  rewrite (sepitT1 (rep d c1)) /utab/table/ut2 /= !ffunE eq_sym eqxx E /=. 
  hhauto; apply: tableP Hu'=>// a; rewrite !finE /u'/u1' !ffunE /= andbT;
  by rewrite (eqP E)=>/negbTE ->.
move: Hu'; rewrite (sepitS (rep d c2)) !finE E /=.
case=>hu1 [hu3][->{hu2} Hu1' Hu2']. 
apply: [stepX use d (rep d c2)]@hu1=>//=; first by rewrite /ut1 ffunE /= E.
move=>v _ [x'][{Hu1'}hu1][-> Hu1'].
apply: [gX ut1]@hu=>//= [[]] {Hu}hu Hu _.
rewrite (_ : _ \+ _ = hr \+ (hc \+ (hu \+ 
  (x :-> cx \+ (x.+1 :-> r0 \+ hu'') \+
  ((v :-> cx \+ (v.+1 :-> x' \+ hu1) \+ hu3))) \+
  ((ht \+ (p :-> q \+ hp)))))); last by heap_congr.
exists d1; split; last first.
- split; first by apply: propagate_nopendP.
  split; first by rewrite /d1.
  by rewrite -Erel; apply: propagate_clos_nopendP.
split=>//; exists ct, (ut2 v); hhauto.
rewrite (sepitT1 (rep d c1))/utab/table/ut2 !ffunE /= eqxx eq_sym E. 
hhauto; rewrite (sepitS (rep d c2)) !finE !ffunE /= !eqxx E /=.
hhauto; apply: tableP Hu2'=>/= a; rewrite !finE !ffunE /= andbT; 
by case/andP=>/negbTE -> /negbTE ->. 
Qed.

Definition nT : Type :=
  forall t, STsep {d} (fun i => i \In bshape' d,
                      [vfun y m => y = norm d t /\ m \In bshape' d]).

Program Definition hnorm :=
  ffix (fun (hnorm : nT) (t : exp s) =>
    Do (match t with 
        | const a => 
            a' <-- Array.read r a;
            ret (const a')
        | app t1 t2 =>
            u1 <-- hnorm t1;
            u2 <-- hnorm t2;
            if (u1, u2) is (const w1, const w2) then
              v <-- kvm_lookup htb (w1, w2);
              if v is Some a then 
                a' <-- Array.read r a.1.1;
                       ret (const a')
              else ret (app u1 u2)
            else ret (app u1 u2)
        end)).
Next Obligation.
case=>d [_][Ci][/= ct][ut][hr][hrest][-> Hr Hrest].
case: t=>[a|t1 t2].
- apply: [stepX rep d, hr]@hr=>//= _ _ [->->].
  by step; do 2!split=>//; exists ct, ut; hhauto.
apply: [stepE d]=>//=; first by split=>//; exists ct, ut; hhauto.
move=>u1 m [E1 H]; apply: [stepE d]=>//=.
move=>u2 {}m [E2 {}H] {Ci ct ut hr hrest Hr Hrest}.
case: H=>Ci [/= ct][ut][hr][w][->{m} Hr][hc][w']
[->{w} Hc][hu][w][->{w'} Hu][ht][hrest][->{w} Ht Hrest].
case: u1 E1=>[w1|??] /= E1; last first.
- by rewrite -E1 E2; step; do 2!split=>//; exists ct, ut; hhauto.
case: u2 E2=>[w2|??] /= E2; last first.
- by rewrite -E1 -E2; step; do 2!split=>//; exists ct, ut; hhauto.
rewrite -E1 -E2; apply: [stepX lookup d]@ht=>//= v {Ht}ht [Ht Ev]. 
case: v Ev=>[[[a1 a2 a3]]|] <-; last first.
- by step; do 2!split=>//; exists ct, ut; hhauto.
apply: [stepX rep d, hr]@hr=>//= _ _ [->->].
by step; do 2!split=>//; exists ct, ut; hhauto.
Qed.

Program Definition check t1 t2 :
    STsep {R} (fun i => i \In shape' R,
              [vfun (b : bool) m => m \In shape' R /\
                 (b <-> (t1, t2) \In R)]) :=
  Do (u1 <-- hnorm t1;
      u2 <-- hnorm t2;
      ret (u1 == u2)).
Next Obligation.
case=>R [h][d][H][[RI X]][Ep PI].
apply: [stepX d]@h=>//= _ {H}h [-> H].
apply: [stepX d]@h=>//= _ {H}h [-> H].
step; split; first by exists d. 
by case: normP=>//; rewrite PI.
Qed.

End Internal.
End Congr.
End Congr.

