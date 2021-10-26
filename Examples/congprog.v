(*******************************)
(* Stateful congruence closure *)
(*******************************)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun div finset seq fintype finfun.
From mathcomp Require Import choice.
From fcsl Require Import axioms ordtype finmap pred (*pcm unionmap heap.
From HTT Require Import stmod stsep llistR array.
(* universe inconsistency from finmap in data in congmath *)
From HTT Require Import congmath*).

From HTT Require Import kvmaps hashtab.
From Coq Require SetoidTactics.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

Ltac add_morphism_tactic := SetoidTactics.add_morphism_tactic.
Notation " R ===> R' " := (@Morphisms.respectful _ _ R R')
  (right associativity, at level 55) : signature_scope.

Cumulative Polymorphic Inductive constant : Type := const_with_arity of nat & nat.

(* constants are an equality type *)
Polymorphic Definition eqcnst (c1 c2 : constant) : bool :=
  match c1, c2 with
    | const_with_arity s1 n1, const_with_arity s2 n2 =>
        (s1 == s2) && (n1 == n2)
  end.

Polymorphic Lemma eqconstantP : Equality.axiom eqcnst.
Proof.
move=>[s1 n1][s2 n2] /=.
do ![case: eqP=>/=[->|H]; last by apply: ReflectF; case].
by apply: ReflectT.
Qed.

Polymorphic Canonical Structure constant_eqMixin := EqMixin eqconstantP.
Polymorphic Canonical Structure constant_eqType := EqType _ constant_eqMixin.

(* constants are a countable type *)

Polymorphic Definition tagconst (p : constant) :=
  let: const_with_arity s n := p in @Tagged nat s (fun _ => nat) n.

Polymorphic Definition consttag (u : {i : nat & nat}) :=
  const_with_arity (tag u) (tagged u).

Polymorphic Lemma tagconstK : cancel tagconst consttag.
Proof. by case. Qed.

Polymorphic Lemma consttagK : cancel consttag tagconst.
Proof. by case. Qed.

Polymorphic Definition const_countMixin := CanCountMixin tagconstK.
Polymorphic Definition const_choiceMixin := CountChoiceMixin const_countMixin.
Polymorphic Canonical Structure const_choiceType := Eval hnf in ChoiceType _ const_choiceMixin.
Polymorphic Canonical Structure const_countType := Eval hnf in CountType _ const_countMixin.

(***********************************************************)
(* The symbols are a predetermined finite set of constants *)
(***********************************************************)

Polymorphic Variable symbs : seq constant.
Polymorphic Definition symb := @seq_sub const_choiceType symbs.

Polymorphic Canonical Structure symb_eqType := [eqType of symb].
Polymorphic Canonical Structure symb_finType := [finType of symb for @seq_sub_finType _ _].
(* symb is an ordered type *)
Polymorphic Definition symb_ordMixin := [fin_ordMixin of symb].
Polymorphic Canonical Structure symb_ordType := OrdType _ symb_ordMixin.


(* the lookup table is represented as a hash table with 10 buckets *)
#[universes(polymorphic=yes)]
Section Lookup.


Inductive KK : Type := uno | dos | tres.

Definition eqkk (c1 c2 : KK) : bool :=
  match c1, c2 with
    | uno , uno  => true
    | dos , dos  => true
    | tres, tres => true
    | _   , _    => false
  end.

Lemma eqkkP : Equality.axiom eqkk.
Proof.
by case; case=>/=; try by [apply: ReflectT | apply: ReflectF].
Qed.

Canonical Structure kk_eqMixin := EqMixin eqkkP.
Canonical Structure kk_eqType := EqType _ kk_eqMixin.

Definition lekk : rel KK := fun k1 k2 => match k1, k2 with
  | uno, dos  => true
  | uno, tres => true
  | dos, tres => true
  | _  , _    => false
end.

Lemma irr_ltn_kk : irreflexive lekk. Proof. by case. Qed.
Lemma trans_ltn_kk : transitive lekk. Proof. by case; case=>//; case. Qed.
Lemma semiconn_ltn_kk (x y : KK) : x != y -> (lekk x y) || (lekk y x).
Proof. by case: x; case: y. Qed.

Definition kk_ordMixin := OrdMixin irr_ltn_kk trans_ltn_kk semiconn_ltn_kk.
Canonical Structure kk_ordType := Eval hnf in OrdType KK kk_ordMixin.

Definition hash3 (k : KK) := match k with
  | uno => 0
  | dos => 1
  | tres => 2
end.

Lemma hash3_ord k : hash3 k < 3.
Proof. by case: k. Qed.
Let hash_3 k : 'I_3 := Ordinal (hash3_ord k).

Eval lazy in symb.

Definition LT3 := (@HT kk_ordType unit 3 hash_3).

Definition hash (n : nat) (k : symb) := index k (enum symb_finType) %% n.
Lemma hash_ord (n : nat) k : 0 < n -> hash n k < n.
Proof. by move=>H; rewrite ltn_pmod. Qed.
Let hash10 k : 'I_10 := Ordinal (hash_ord (n := 10) k erefl).

Definition LT := (@HT symb_ordType unit _ hash10).

(*
Let K := (symb*symb)%type.
Let V := (symb*symb*symb)%type.
Canonical Structure eqTypeK := [eqType of K].
Canonical Structure finTypeK := [finType of K].
Canonical Structure ordTypeK := [ordType of K].
Canonical Structure eqTypeV := [eqType of V].


Definition hash (n : nat) (k : K) := index k (enum finTypeK) %% n.
Lemma hash_ord (n : nat) k : 0 < n -> hash n k < n.
Proof. by move=>H; rewrite ltn_pmod. Qed.
Let hash10 k : 'I_10 := Ordinal (hash_ord (n := 10) k erefl).

Definition LT := (@HT ordTypeK unit _ hash10).
*)
End Lookup.

(*

#[universes(polymorphic=yes)]
Section Lookup.
Polymorphic Universes uu1 uu2 uu3 uu4 uu5 uu6 uu7.

Definition K := (symb*symb)%type.


Definition V : Type@{uu2} := prod (prod symb symb) symb.
About V.
(*Polymorphic Canonical Structure eqTypeK := [eqType of K].*)
Polymorphic Canonical Structure ordTypeK := [ordType of K].

(*Polymorphic Canonical Structure finTypeK := [finType of K].
Definition hash (n : nat) (k : K) := index k (enum finTypeK) %% n.
Lemma hash_ord (n : nat) k : 0 < n -> hash n k < n.
Proof. by move=>H; rewrite ltn_pmod. Qed.
Definition hash10 k : 'I_10 := Ordinal (hash_ord (n := 10) k erefl).*)

Definition  ordSS := [ordType of prod symb symb].


Polymorphic Cumulative Inductive constant : Type := const_with_arity of nat & nat.

(* constants are an equality type *)
Definition eqcnst (c1 c2 : constant) : bool :=
  match c1, c2 with
    | const_with_arity s1 n1, const_with_arity s2 n2 =>
        (s1 == s2) && (n1 == n2)
  end.

Lemma eqconstantP : Equality.axiom eqcnst.
Proof.
move=>[s1 n1][s2 n2] /=.
do ![case: eqP=>/=[->|H]; last by apply: ReflectF; case].`
by apply: ReflectT.
Qed.

Polymorphic Canonical Structure constant_eqMixin := EqMixin eqconstantP.
Polymorphic Canonical Structure constant_eqType := EqType _ constant_eqMixin.

Definition consttag (u : {i : nat & nat}) :=
  const_with_arity (tag u) (tagged u).

Definition tagconst (p : constant) :=
  let: const_with_arity s n := p in @Tagged nat s (fun _ => nat) n.

Lemma tagconstK : ssrfun.cancel tagconst consttag.
Proof. by case. Qed.

Lemma consttagK : ssrfun.cancel consttag tagconst.
Proof. by case. Qed.

Definition const_countMixin := CanCountMixin tagconstK.
Definition const_choiceMixin := CountChoiceMixin const_countMixin.
Canonical Structure const_choiceType := Eval hnf in ChoiceType _ const_choiceMixin.


Variable symbs : seq constant.

Polymorphic Definition symb := @seq_sub const_choiceType symbs.

Polymorphic Canonical Structure symb_finType := [finType of symb for @seq_sub_finType _ _].
(* symb is an ordered type *)
Polymorphic Definition symb_ordMixin := [fin_ordMixin of symb].
About symb_ordMixin.
Polymorphic Canonical Structure symb_ordType := OrdType _ symb_ordMixin.

Polymorphic Definition ordS := [ordType of symb].


About ordS.
About AssocList.AssocList.
Polymorphic Definition Bkt := AssocList.AssocList@{Equality.type.u0 uu1 Equality.type.u0 Equality.type.u0 Equality.type.u0 Equality.type.u0} ordS.
Definition LT := (HT V hash10).
Definition LT := HashTab.HashTab (AssocList.AssocList K V) hash10.
*)
End Lookup.

(* the tables relating arrays with the content of the lists *)
(* ctab is for class lists, utab is for use lists *)
Notation ctab := (@table symb_finType (llist symb) _ (@lseq symb)).
Notation utab := (@table symb_finType (llist (symb*symb*symb)) _
                                      (@lseq (symb*symb*symb)))%type.

Definition n := #|symb_finType|.

(* the empty congruence is one that only relates constant symbols to themselves *)
Definition empty_cong := closure (graph const).

Section ShapePredicates.

(* the algorithm starts with root pointers for the data *)

Inductive ptrs : Type :=
  Ptrs of {array symb -> symb} & {array symb -> llist symb} &
          {array symb -> llist (symb*symb*symb)} & KVmap.tp LT & loc.

Variable (r : {array symb -> symb}).
Variable (clist : {array symb -> llist symb}).
Variable (ulist : {array symb -> llist (symb*symb*symb)}).
Variable (htab : KVmap.tp LT).
Variable (p : loc).

(* The layout of the data structure *)

Definition ashape D :=
  [Rel h | let: (d, ct, ut) := D in
           h \In Array.shape r (rep d) #
           (Array.shape clist ct # sepit setT (ctab ct (class d))) #
           (Array.shape ulist ut # sepit setT (utab ut (use d))) #
           KVmap.shape htab (lookup d) #
           [Rel h' | exists l, h' \In p --> l # lseq l (pending d)]].

Lemma ashapeD D : proper (ashape D).
Proof. move=>[[d]] ct ut h1 [h2][h3]; tauto. Qed.

Lemma ashape_invert : invertible ashape.
Proof.
move=>[[[r1]]] c1 u1 t1 p1 ct1 ut1 [[[r2]]] c2 u2 t2 p2 ct2 ut2 h1 h2 /=.
move=>[hr1][w][->][R1][[hc1]][w'][->{w}][C1][[hu1]][w][->{w'}][U1]
      [[ht1]][w'][->{w}][T1][[l1]][hl1][hp1][->{w'}][L1][P1] _ _ _ _ _.
move=>[hr2][w][->][R2][[hc2]][w'][->{w}][C2][[hu2]][w][->{w'}][U2]
      [[ht2]][w'][->{w}][T2][[l2]][hl2][hp2][->{w'}][L2][P2] _ _ _ _ _ A.
case: (Array.shape_invert R1 R2 (agreeUnK A)) (A)=>/= -> -> {A}; move/agreeKUn=>A.
case: (table_invert (@lseq_invert _) C1 C2 (agreeUnK A)) (A) =>/= ->;
move/ffunP=>->-> {A}; move/agreeKUn => A.
case: (table_invert (@lseq_invert _) U1 U2 (agreeUnK A)) (A)=>/= ->;
move/ffunP=>->-> {A}; move/agreeKUn => A.
case: (KVmap.shape_invert T1 T2 (agreeUnK A)) (A)=>/= -> -> {A}; move/agreeKUn=>A.
case: (ptr_invert L1 L2 (agreeUnK A)) (A)=>/= E -> {A}; move/agreeKUn=>A.
by rewrite -{}E in P2; case: (lseq_invert P1 P2 A)=>/= -> ->.
Qed.

Lemma ashape_inv D1 D2 h : h \In ashape D1 -> h \In ashape D2 -> D1 = D2.
Proof. by apply: iinv; [apply: ashape_invert | apply: ashapeD]. Qed.

Definition bshape d :=
  [Rel h | class_inv d /\ exists ct, exists ut, h \In ashape (d, ct, ut)].

Lemma bshapeD d : proper (bshape d).
Proof. by move=>d h [_][ct][ut]; apply: ashapeD. Qed.

Lemma bshape_invert : invertible bshape.
Proof.
move=>d1 d2 h1 h2 [_][ct1][ut1] H1 [_][ct2][ut2] H2.
by case/(ashape_invert H1 H2)=>[[->]] _ _ ->.
Qed.

Lemma bshape_inv d1 d2 h : h \In bshape d1 -> h \In bshape d2 -> d1 = d2.
Proof. by apply: iinv; [apply: bshape_invert | apply: bshapeD]. Qed.

Definition shape (R : rel_exp) :=
  [Rel h | exists d, h \In bshape d /\ propagate_inv d /\ pending d = [::] /\
                     CRel d =r R].

Lemma shapeD (R : rel_exp) : Def (shape R).
Proof. by move=>R h [d][H] _; apply: bshapeD H. Qed.

Lemma shape_invert R1 R2 h1 h2 :
        h1 \In shape R1 -> h2 \In shape R2 -> agree h1 h2 -> R1 =r R2 /\ h1 = h2.
Proof.
move=>R1 R2 h1 h2 [d1][S1][_][_] <- [d2][S2][_][_] <- A.
by move: (bshape_invert S1 S2 A)=>[<- <-].
Qed.

Lemma shape_inv R1 R2 h : h \In shape R1 -> h \In shape R2 -> R1 =r R2.
Proof.
by move=>??? H; case/(shape_invert H)=>//; apply: agree_refl; apply: shapeD H.
Qed.

End ShapePredicates.

Add Parametric Morphism r clist ulist htab p : (shape r clist ulist htab p) with
  signature @releq _ ===> @releq _ as shape_morph.
Proof.
move=>R1 R2 H.
split=>x [d1][H1][H2][H3] H4; exists d1;
by [rewrite -H | rewrite H].
Qed.

(* Initialization procedure to generate the empty structure *)
Section Initialization.

Definition iT (clist : {array symb -> llist symb}): Type := forall k,
  STsep unit (fun i => k <= n /\ exists f, i \In Array.shape clist f #
                       sepit [set c | indx c < k] (ctab f [ffun c => [:: c]]),
              fun y i m => y = Val tt /\ exists f, m \In Array.shape clist f #
                       sepit setT (ctab f [ffun c => [:: c]])).

Program Definition init :
  STsep ptrs (emp, fun y i m => exists ptr : ptrs, y = Val ptr /\
                   let: Ptrs r c u h p := ptr in
                   m \In shape r c u h p empty_cong) :=
  Do (r <-- Array.newf [ffun x => x];
      clist <-- Array.new _ null;
      Fix (fun (loop : iT clist) k =>
           Do (Match_dec (dec (k < n))
                 (fun pf => x <-- Allocb (ith pf) 2;
                            x .+ 1 ::= null;;
                            Array.write clist (ith pf) x;;
                            loop k.+1)
                 (fun _ => ret tt))) 0;;
      ulist <-- Array.new _ null;
      htab <-- KVmap.new LT;
      p <-- Alloc null;
      ret (Ptrs r clist ulist htab p)).
Next Obligation.
move:H H0 H1=>pf f [hc][hct][->{i}][Hc][Hct].
case: dec=>[{pf} pf|]; last first.
- case: leqP pf (eqn_leq k n)=>// _ -> /= pf _ D; apply: val_ret=>//.
  split=>//; exists f; hauto D.
  by apply: tableP2 Hct=>//; move=>?; rewrite !in_set (eqP pf) /n enum_rank_subproof.
apply: bnd_allocb=>{x} /= x; rewrite unh0 -(unA (x :-> _)) -(push (x .+ 1)).
apply: bnd_write; rewrite -2!(unCA hc); apply: {hc} bnd_gh Hc=>[[] hc [Hc] _|??[]//].
rewrite (push (x .+ 1)) (unA (x :-> _))=>D; apply: cons0=>//=; split=>//.
exists [ffun z => if z == ith pf then x else f z]; hauto D.
rewrite (sepitS (ith pf)) !in_set indx_ith ltnSn /table !ffunE eq_refl; hauto D.
- by rewrite unh0.
apply: tableP2 Hct=>//; last first.
- by move=>? _; rewrite !in_set !ffunE indx_injE; case: eqP=>//->; rewrite ltnn.
move=>s; rewrite !in_set ltnS indx_injE (leq_eqVlt (indx s)).
by case: ltngtP=>//=; rewrite (ltnNge _ k) (leq_eqVlt k)=>->; rewrite orbT.
Qed.
Next Obligation.
apply: bnd_do0=>[|_ hr [r] [[->]] Hr|??[?][]|] //.
apply: bnd_do0=>[|_ hc [clist] [[->]] Hc|??[?][]] // => D.
apply: bnd_do (D)=>[||??[]] //=.
- split=>//; exists [ffun x:symb => null]; rewrite -(unh0 hc); hauto D.
  rewrite (_ : [set c | indx c < 0] = set0); first by rewrite sepit0.
  by rewrite -setP=>x; rewrite !in_set.
move=>[] m [_] [f][hc'][hrest][->{m}][Hc'][Hrest] _ {hc Hc D}.
apply: bnd_do0=>[|ulist hu [ut][[<-]] Hu|??[?][]] //.
apply: bnd_do0=>[|w ht /= [htab][][->] Ht|??[?][]] //.
apply: bnd_alloc=>p D; apply: val_ret=>//; move: D.
rewrite (_ : _ :+ _ = hr :+ ((hc' :+ hrest) :+ (hu :+ empty :+
        (ht :+ (p :-> null :+ empty))))); last by heap_congr.
move=>D; exists (Ptrs r clist ulist htab p); split=>//.
exists (Data [ffun x => x] [ffun c => [:: c]] [ffun c => [::]] (nil _ _) [::]); split=>//;
  last by move: initP=>[PI] Cl.
split=>//; first by move=>s a; rewrite !ffunE !inE.
exists f; exists [ffun s:symb => null]; hauto D.
by rewrite sepit_emp=>// x _; rewrite /table /= !ffunE mem_rel => h; split; case.
Qed.

End Initialization.

Module Dummy2. End Dummy2.

Variable (r : {array symb -> symb}).
Variable (clist : {array symb -> llist symb}).
Variable (ulist : {array symb -> llist (symb*symb*symb)}).
Variable (htab : KVmap.tp LT).
Variable (p : loc).

Notation ashape' := (ashape r clist ulist htab p).
Notation bshape' := (bshape r clist ulist htab p).
Notation shape' := (shape r clist ulist htab p).

Definition cT (a' b' : symb) : Type :=
  forall x:unit, STsep unit
    (fun i => (exists D, i \In ashape' D) /\ a' != b',
     fun y i m => forall D, i \In ashape' D -> y = Val tt /\ exists ct, exists ut,
                  let: (d, _, _) := D in
                  m \In ashape'
                    (Data [ffun s => if s \in (class d a') then b'
                                     else rep d s]
                          [ffun s => if s == a' then [::] else
                                     if s == b' then rev (class d a') ++ class d b'
                                     else class d s]
                     (use d) (lookup d) (pending d), ct, ut)).

Program
Definition join_hclass (a' b' : symb) :
             STsep unit (fun i => (exists d, i \In bshape' d) /\ a' != b',
                         fun y i m => forall d, i \In bshape' d ->
                                  y = Val tt /\
                                   m \In bshape' (join_class d a' b')) :=
  Do (Fix (fun (loop : cT a' b') (x : unit) =>
        Do (a <-- Array.read clist a';
            b <-- Array.read clist b';
            If a == null :> loc then ret tt
            else
              s <-- !a;
              next <-- !(a .+ 1);
              a .+ 1 ::= b;;
              Array.write clist b' a;;
              Array.write clist a' next;;
              Array.write r s b';;
              loop tt)) tt).
Next Obligation.
apply: (ghost (d, f0, f)) H1.
move: H0=>{loop f0 f d} N [[d]] ct ut H.
move: (H)=>[i1][w][->][R][[w']][i4][->{w}][[i2]][i3][->{w'}][Ct][Cv] _ [R'] _ D.
move: Cv; rewrite (sepitT1 a') (sepitS b') 3!in_set eq_sym N {1 2}/table /= => Cv.
move: Cv D=>[i5][w][->{i3}][Ca][[i3]][i6][->{w}][Cb][Cc] _ _.
rewrite -(unA i2) -(unCA i2); apply: bnd_gh (Ct)=>[a w [[->]] <-{w}|??[] //].
apply: bnd_gh (Ct)=>[b w [[->]] <-{w}|??[] //]; rewrite (unCA i2) (unA i2).
case: ifP Ca=>E.
- rewrite (eqP E); case/lseq_null=>Ce -> D.
  apply: val_ret=>//; split=>//; exists ct; exists ut.
  rewrite InE /= (sepitT1 a') (sepitS b') 3!in_set eq_sym N {1 2}/table /=
    (eqP E) Ce /= !ffunE !eq_refl eq_sym (negbTE N) /=
    (_ : [ffun s => rep d s] = rep d); last first.
  - by rewrite -ffunP => ?; rewrite ffunE.
  hauto D; apply: tableP Cc=>?; rewrite !in_set // !ffunE.
  by case: ifP=>W; [rewrite (eqP W) Ce | case: eqP].
case/(lseq_pos (negbT E))=>s [q][i7][Ca] _ [<-{i5}] /= Cq.
rewrite -(unA i2) -2!(unA (ct a' :-> _)) -2!(unA (ct a' .+ 1 :-> _))
        -(unA i7) -(unA i3).
rewrite -2!(push (ct a'))=>D; apply: bnd_read=>//; rewrite 2!(push (ct a')) in D *.
rewrite -3!(push (ct a' .+ 1)) in D *; apply: bnd_read=>//.
apply: bnd_write=>{D} //; rewrite 3!(push (ct a' .+ 1)) -(unCA i2).
do 2![apply: {i2} bnd_gh Ct=>[[] i2 [Ct _]|[?]?[]] //]; rewrite (unCA i2).
apply: {i1} bnd_gh R=>[[] i1 [R _]|[?]?[]] //.
rewrite (unA i3) (unA i7) 2!(unA (ct a' .+ 1 :-> _)) 2!(unA (ct a' :-> _)) (unA i2).
set r2 := (finfun _ )in R; set ct2 := (finfun _) in Ct=>D.
set cv2 := [ffun z => if z == a' then (behead (class d a'))
            else if z == b' then s :: (class d b') else class d z].
apply: (cons_gh1 (Data r2 cv2 (use d) (lookup d) (pending d), ct2, ut))=>
       [P|[] m [_][ct1][ut1] /= Wm Dm|??[]||] //=; last 1 first.
- hauto D; rewrite /ct2 (sepitT1 a') (sepitS b') 3!in_set eq_sym N /= /table /=
  !ffunE !eq_refl !(eq_sym b') (negbTE N) -!unA -!(unCA i7) !unA unC -!unA unC -unA.
  by hauto D; apply: tableP Cc=>?; rewrite !in_set !ffunE; do 2![case: eqP=>//].
- by split=>//; first by eauto.
split=>{ct2 Ct D} //; exists ct1; exists ut1.
set r1 := (finfun _) in Wm; set c1 := (finfun _) in Wm.
rewrite (_ : (finfun _) = r1); last first.
- rewrite /r1 -ffunP=>?; rewrite !ffunE eq_refl.
  case: eqP=>[->|]; first by rewrite if_same Ca inE eq_refl.
  by rewrite Ca inE; case: eqP.
rewrite (_ : (finfun _) = c1) //.
rewrite /c1 -ffunP=>?; rewrite !ffunE !eq_refl !(eq_sym b') (negbTE N).
case: eqP=>// H1; case: eqP=>// H2.
by rewrite Ca rev_cons cat_rcons.
Qed.
Next Obligation.
apply: (ghost H) H1; move: H0 {H}=> N d [I][ct][ut] H; move: (ashapeD H).
apply: (cons_gh1 (d, ct, ut))=>[||??[]|] //; first by eauto.
move=>[] m [_] [ct1][ut1] W; split=>//; set d' := (Data _ _ _ _ _) in W.
suff E : join_class d a' b' = d'
  by split; [apply: join_class_classP | rewrite E; eauto].
congr Data.
by set v := (finfun _); rewrite -(ffunP v) /v => x; rewrite !ffunE /= I.
Qed.

Module Dummy23. End Dummy23.

Let proj0 (e : symb*symb*symb) := let: (c, c1, c2) := e in c.
Let proj1 (e : symb*symb*symb) := let: (c, c1, c2) := e in c1.
Let proj2 (e : symb*symb*symb) := let: (c, c1, c2) := e in c2.
Notation "e ..0" := (proj0 e) (at level 2).
Notation "e ..1" := (proj1 e) (at level 2).
Notation "e ..2" := (proj2 e) (at level 2).

Definition uT (a' b' : symb) := forall x : unit,
  STsep unit (fun i => exists d, exists done, a' != b' /\
                         i \In bshape' (join_use' d a' b' done) /\
                         use d a' = done ++ use (join_use' d a' b' done) a',
              fun y i m => forall d, i \In bshape' d -> y = Val tt /\
                             m \In bshape' (join_use d a' b')).

Program Definition join_huse (a' b' : symb) :
           STsep unit (fun i => exists d, a' != b' /\ i \In bshape' d,
                       fun y i m => forall d, i \In bshape' d ->
                         y = Val tt /\ m \In bshape' (join_use d a' b')) :=
  Do (Fix (fun (loop : uT a' b') x =>
       Do (a <-- Array.read ulist a';
           If a == null :> loc then ret tt
           else
             eq <-- !a;
             next <-- !(a .+ 1);
             Array.write ulist a' next;;
             c1 <-- Array.read r eq..1;
             c2 <-- Array.read r eq..2;
             v <-- KVmap.lookup htab (c1, c2);
             match_opt v then
               KVmap.insert htab (c1, c2) eq;;
               b <-- Array.read ulist b';
               a .+ 1 ::= b;;
               Array.write ulist b' a;;
               loop tt
             else [d]
               dealloc a;;
               dealloc a .+ 1;;
               p' <-- !p;
               q <-- insert p' (comp_pend eq d);
               p ::= q;;
               loop tt)) tt).
Next Obligation.
apply: (ghost1 (join_use' H a' b' H0))=>[?|]; first by apply: bshape_inv.
move: H H0 H1 H2 H3=>d done N.
set d1 := join_use' d a' b' done.
move=>[C1][ct][ut][h1][w][->][H1][[h2]][w'][->{w}][H2][[w]][w''][->{w'}];
move=>[[h3]][u][->{w}][Ut][U] _ [[h7]][w][->{w''}][H7][[l]][w'][h8][->{w}][];
case/swp=>->{w'} _ [H8] _ _ _ _ D E; move: D.
move: U; rewrite (sepitT1 a') (sepitS b') 3!in_set eq_sym N {1 2} /table /=.
move=>[h4][w][->{u}][Ua][[h5]][h6][->{w}][Ub][Ru] _ _.
rewrite -(unA h3) -2!(unCA h3); apply: bnd_gh (Ut)=>[_ _ [[->]] <-|??[]] //.
case: ifP=>E1.
- rewrite (eqP E1) in Ua; case/lseq_null: Ua=>E2 ->.
  rewrite 2!(unCA h3) (unA h3) /join_use E2=>D; apply: val_ret=>//; do !split=>//.
  exists ct; exists ut; hauto D.
  by rewrite (sepitT1 a') (sepitS b') 3!in_set eq_sym N /table (eqP E1) E2; hauto D.
case/(lseq_pos (negbT E1)): Ua.
move=>[[c1 c2] c][next][h9][E2] _ [<-{h4}] H9.
rewrite -2!(unA (ut a' :-> _)) -3!(push (ut a'))=>D; apply: bnd_read=>//.
rewrite -2!(unA (ut a' .+ 1 :-> _)) -4!(push (ut a' .+ 1)) in D *.
apply: bnd_read=>//; move: D; rewrite -2!(unCA h3).
apply: {h3} bnd_gh Ut=>[[] h3 [Ut _]|??[] //]; rewrite -3!(unCA h1).
apply: bnd_gh (H1)=>[c1' _ [[Ec1]] <-|??[] //].
apply: bnd_gh (H1)=>[c2' _ [[Ec2]] <-|??[] //].
rewrite -(unA h9) -(unA h5) -8!(unCA h7).
apply: {h7} bnd_gh H7=>[v h7 [H7][Eqv]|??[] //].
set d2 := join_use' d a' b' (done ++ [:: (c1, c2, c)]).
have E3: use d2 a' = behead (use d1 a').
- rewrite /d2 (@join_useT (behead (use d1 a'))); last by rewrite /= -E2.
  by apply: join_use_useE; rewrite /= -E2.
have E4: join_use d2 a' b' = join_use d1 a' b'.
- by rewrite /join_use E3 -!(@join_useT [::]) ?cats0 -?catA ?E /= -?E2.
case: v Eqv=>[[[e1 e2] e]|] /= Eqv.
- rewrite -4!(push (ut a')); apply: bnd_dealloc.
  rewrite -3!(push (ut a' .+ 1)); apply: bnd_dealloc.
  rewrite -7!(push p)=>D; apply: bnd_read=>//; move: D.
  rewrite -(unC h8) -7!(unCA h8).
  apply: bnd_gh H8=>{h8 x0} [_ h8 [q][H8][->]|??[?][]//].
  rewrite -(push p); apply: bnd_write=>D.
  apply: (cons_gh1 d2)=>[?|[] m [_] P _|??[]||] //.
  - by exists d; exists (done ++ [:: (c1, c2, c)]); rewrite -/d2 E3 -catA /= -E2.
  - by rewrite -E4.
  rewrite (_ : _ :+ _ =
           h1 :+ (h2 :+ (h3 :+ (h9 :+ (h5 :+ h6)) :+ (h7 :+ (p :-> q :+ h8))))) in D *;
  last by heap_congr.
  case: H8 D=>x0 [h'] [_] <- H8 D.
  rewrite /d2 (@join_useT (behead (use d1 a'))) -/d1 /= -?E2 // -Ec1 -Ec2 -Eqv; split=>//.
  set ut2 := (finfun _) in Ut.
  exists ct; exists ut2; hauto D.
  rewrite (sepitT1 a') (sepitS b') 3!in_set eq_sym N /table /=.
  rewrite !ffunE !eq_refl !(eq_sym b') (negbTE N); hauto D.
  by apply: tableP Ru=>s; rewrite !in_set /ut2 ffunE;
     case: (s == a')=>//; rewrite andbF.
apply: bnd_gh H7=>{h7} [[] h7 [H7 _]|??[] //]; rewrite -2!(unCA h3).
apply: bnd_gh (Ut)=>[_ _ [[->]] <-|??[] //]; rewrite -3!(push (ut a' .+ 1)).
apply: bnd_write; rewrite ffunE (eq_sym b') (negbTE N) -(unCA h3).
apply: {h3} bnd_gh Ut=>[[] h3 [Ut _]|??[] //]=>D.
apply: (cons_gh1 d2)=>[||??[]||] //.
- by exists d; exists (done ++ [:: (c1, c2, c)]); rewrite -/d2 E3 -catA /= -E2.
- by rewrite -E4.
rewrite (_ : _ :+ _ = h1 :+ (h2 :+ (h3 :+ (h9 :+ ((ut a' :-> (c1, c2, c) :+
        (ut a' .+ 1 :-> ut b' :+ h5)) :+ h6)) :+ (h7 :+ (p :-> l :+ h8)))));
  last by heap_congr.
rewrite /d2 (@join_useT (behead (use d1 a'))) -/d1 /= -?E2 // -Ec1 -Ec2 -Eqv.
set ut2 := (finfun _) in Ut; split=>//.
exists ct; exists ut2; hauto D.
rewrite (sepitT1 a') (sepitS b') 3!in_set eq_sym N /table /=.
rewrite /ut2 !ffunE !eq_refl (eq_sym b') (negbTE N); hauto D.
by apply: tableP Ru=>s; rewrite !in_set !ffunE; case: (s == b')=>//; case: (s == a').
Qed.
Next Obligation.
by apply: cons0=>//; [exists H; exists (Nil (symb*symb*symb)) | apply: bshapeD H1].
Qed.

Module Dummy56. End Dummy56.

Let pend0 (e : pend) :=
  match e with simp_pend a b => a | comp_pend (a,_,_) (b,_,_) => a end.
Let pend1 (e : pend) :=
  match e with simp_pend a b => b | comp_pend (a,_,_) (b,_,_) => b end.
Notation "e ..0" := (pend0 e) (at level 2).
Notation "e ..1" := (pend1 e) (at level 2).

Definition pT : Type := forall x:unit,
  STsep unit (fun i => exists d, i \In bshape' d,
              fun y i m => forall d, i \In bshape' d ->
                             y = Val tt /\ m \In bshape' (propagate d)).

Program Definition hpropagate :=
  Fix (fun (loop : pT) x =>
       Do (q <-- !p;
           If q == null then ret tt (* pending list is empty *)
           else
             eq <-- !q;
             next <-- !(q .+ 1);
             p ::= (next : loc);;
             dealloc q;;
             dealloc q .+ 1;;
             a' <-- Array.read r eq..0;
             b' <-- Array.read r eq..1;
             If (a' == b') then loop tt
             else join_hclass a' b';;
                  join_huse a' b';;
                  loop tt)) tt.
Next Obligation.
apply: (ghost1 H)=>[?|]; first by apply: bshape_inv.
move: {loop} H H0=>d [CI][ct][ut][hr][w][->][Hr][[hc]][w'][->{w}][Hc].
move=>[[hu]][w][->{w'}][Hu][[ht]][w'][->{w}][Ht][[q]][w''][hp][->{w'}][].
case/swp=>-> _ [Hp] _ _ _ _ {w' w''}.
rewrite -4!(push p)=>D; apply: bnd_read=>//.
case: ifP Hp D=>Eq.
- rewrite (eqP Eq); case/lseq_null=>Ep ->{hp} D.
  apply: val_ret=>//; rewrite propagate_equation Ep; do 2!split=>//.
  exists ct; exists ut; rewrite 4!(push p) in D *; hauto D.
  by rewrite Ep.
case/(lseq_pos (negbT Eq))=>eq [next][hnext][Ep] _ <-{hp} Hp.
rewrite -5!(push q)=>D; apply: bnd_read=>//; rewrite -6!(push (q .+ 1)) in D *.
apply: bnd_read=>//; move: D; rewrite -2!(push p); apply: bnd_write; rewrite -2!(push q).
apply: bnd_dealloc; rewrite -(push (q .+ 1)); apply: bnd_dealloc; rewrite -(unCA hr).
apply: bnd_gh (Hr)=>[a' _ [[Ea]] <-|??[] //].
apply: bnd_gh (Hr)=>[b' _ [[Eb]] <-|??[] //].
set d1 := Data (rep d) (class d) (use d) (lookup d) (behead (pending d)).
rewrite 3!(push p).
case: ifP=>E D.
- have T1: propagate d = propagate d1.
  - rewrite propagate_equation Ep /=.
    by case: eq Ep Ea Eb=>[a2 b2 _ <-<-| [[a2 ?]?][[b2 ?]?] _ <-<-]; rewrite E.
  apply: (cons_gh d1)=>[[] m|??[] //||//]; first by rewrite T1.
  by split=>//; exists ct; exists ut; hauto D.
rewrite -(unh0 (_ :+ _)) in D *.
apply: (bnd_gh1 d1)=>[|[] m [_] Wm|??[]//||//]; last 1 first.
- by split=>//; exists ct; exists ut; hauto D.
- by rewrite E; eauto.
set d2 := (join_class _ _ _) in Wm.
apply: (bnd_gh1 d2)=>[|{m Wm} [] m [_] Wm|??[]|] //; first by rewrite E /=; eauto.
rewrite unh0; apply: cons0=>/= [|y m2]; first by eauto.
case/(_ _ Wm)=>->{Wm} Wm Dm; split=>//.
rewrite (_ : propagate d = propagate (join_use d2 a' b')) // /d2
         propagate_equation Ep.
by case: eq Ep Ea Eb=>[a2 b2 _ <- <-|[[a2 ?]?][[b2 ?]?] _ <- <-]; rewrite E.
Qed.

Module Dummy57. End Dummy57.

Program Definition merge (e : Eq) :
           STsep unit (fun i => exists R, i \In shape' R,
                       fun y i m => forall R, i \In shape' R -> y = Val tt /\
                                    m \In shape' (closure (R +r eq2rel e))) :=
  match e with
    simp_eq a b =>
      Do (q <-- !p;
          x <-- insert q (simp_pend a b);
          p ::= x;;
          hpropagate)
  | comp_eq c c1 c2 =>
      Do (c1' <-- Array.read r c1;
          c2' <-- Array.read r c2;
          v <-- KVmap.lookup htab (c1', c2');
          match_opt v then
            KVmap.insert htab (c1', c2') (c, c1, c2);;
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
            Array.write ulist c2' x
          else [b]
            q <-- !p;
            x <-- insert q (comp_pend (c, c1, c2) b);
            p ::= x;;
            hpropagate)
   end.
Next Obligation.
apply: (ghost2 (t:=H)); first by move=>???; move/(shape_inv H0)=>->.
move: H H0=>R [d][[CI]][ct][ut][hr][w][->][Hr][[hc]][w'][->{w}][Hc].
move=>[[w]][w''][->{w'}][[hu]][hu'][->{w}][Hu][Hu'] _ [[ht]][w'].
move=>[->{w''}][Ht][[q]][w''][hp][->{w'}][].
case/swp=>-> _ [Hp] _ _ _ _ {w''} D [PI][Ep] ERel; move: D.
set d1 := Data (rep d) (class d) (use d) (lookup d) (simp_pend a b :: pending d).
rewrite -(unA hu) -5!(push p)=>D; apply: bnd_read=>//; move: D.
rewrite -(unC hp) -5!(unCA hp).
apply: {hp} bnd_gh Hp=>[_ hp [q'] [Hp] [->{x}]|??[?][]] //.
rewrite -(push p); apply: bnd_write=>D.
apply: (cons_gh d1)=>[[] m [_] Wm Dm|??[] //||//]; last first.
- rewrite 4!(unCA hp) (unC hp) 5!(push p) (unA hu) in D *.
  move: Hp D=>[x][h'][_] <-; rewrite Ep=>[[->]] ->=>D.
  split=>//; exists ct; exists ut; hauto D.
  by rewrite Ep.
have L: propagate_inv d1 by apply: propagate_pendP PI.
move: (propagatePE L)=>[L1][L2] L3; split=>//; exists (propagate d1).
by rewrite -L3 -ERel {4}/d1 /CRel /= clos_clos -!orrA orrAC.
Qed.
Next Obligation.
apply: (ghost2 (t:=H)); first by move=>???; move/(shape_inv H0)=>->.
move: H H0=>R [d][[CI]][ct][ut][hr][w][->][Hr][[hc]][w'][->{w}][Hc].
move=>[[w]][w''][->{w'}][[hu]][hu'][->{w}][Hu][Hu'] _ [[ht]][w'].
move=>[->{w''}][Ht][[q]][w''][hp][->{w'}][].
case/swp=>-> _ [Hp] _ _ _ _ {w''} D [PI][Ep] ERel; move: D.
do 2!apply: bnd_gh (Hr)=>[_ _ [[->]] <-|??[]//]; rewrite -3!(unCA ht).
apply: {ht} bnd_gh Ht=>[v ht [Ht] [Ev]|??[]//].
case: v Ev=>[[[e e1] e2]|] Ev.
- set d1 := Data (rep d) (class d) (use d) (lookup d)
                 (comp_pend (c, c1, c2) (e, e1, e2) :: pending d).
  have L: propagate_inv d1 by apply: propagate_pendP PI.
  rewrite -4!(push p)=>D; apply: bnd_read=>//; move: D.
  rewrite -(unC hp) -4!(unCA hp).
  apply: {hp} bnd_gh Hp=>[_ hp [x][Hp][->]|??[?][]//].
  rewrite -(push p); apply: bnd_write.
  rewrite 3!(unCA hp) (unC hp) 4!(push p) 3!(unCA ht)=>D.
  case: Hp D=>[x1][h'][_] <-; rewrite Ep; case=>->-> D.
  apply: (cons_gh d1)=>[[] m [_] Wm Dm |??[]//||//]; last first.
  - by split=>//; exists ct; exists ut; hauto D; rewrite Ep.
  move: (propagatePE L)=>[L1][L2] L3; split=>//; exists (propagate d1).
  rewrite -L3 {4}/d1 -ERel; do 3!split=>//.
  by apply: propagate_clos_pendP.
apply: bnd_gh Ht=>{ht x} [_ ht [Ht] _|??[]//]; rewrite -(unA hu) -3!(unCA hu).
apply: bnd_gh (Hu)=>[_ _ [[->]] <-|??[]//]; move: Hu'.
rewrite (sepitT1 (rep d c1)) {1}/table=>[[hu'']][hu2][->{hu'}][Hu''][Hu'] _.
rewrite -(unA hu'') -4!(unCA hu'').
apply: {hu''} bnd_gh Hu''=>[_ hu'' [x] [Hu''][->]|??[?][]//].
rewrite -(unCA hu); apply: {hu} bnd_gh Hu=>[_ hu [Hu] _|??[] //].
apply: bnd_gh (Hu)=>[_ _ [[->]] <-|??[]//].
set ut1 := (finfun _) in Hu.
set u1' := [ffun z => if z == rep d c1 then (c, c1, c2) :: use d z else use d z].
set u' := [ffun z => if z == rep d c2 then (c, c1, c2) :: u1' z else u1' z].
set l' := (ins _ _ _) in Ht.
set d1 := Data (rep d) (class d) u' l' (pending d).
pose ut2 x' := [ffun z => if z == rep d c2 then x' else ut1 z].
case E: (rep d c2 == rep d c1).
- rewrite -(unCA hu'').
  apply: (bnd_gh ((c, c1, c2) :: use d (rep d c1))); last first.
  - by rewrite ffunE E.
  - by move=>??[?][].
  move=>_ {hu'' Hu''} hu'' [x'] [Hu''] [->].
  rewrite -(unCA hu); apply: {hu} val_gh Hu=>[[] hu [Hu] _|??[]//].
  rewrite (_ : _ :+ _ = hr :+ (hc :+ (hu :+ (hu'' :+ hu2) :+ (ht :+ (p :-> q :+ hp)))));
    last by heap_congr.
  move=>D; split=>//; exists d1; split; last first.
  - split; first by apply: propagate_nopendP.
    split; first by rewrite /d1.
    by rewrite -ERel; apply: propagate_clos_nopendP.
  split=>//; exists ct; exists (ut2 x'); hauto D.
  rewrite (sepitT1 (rep d c1)) {1}/table !ffunE (eq_sym (rep d c1)) E eq_refl.
  hauto D; apply: tableP Hu' => x0; rewrite !in_set andbT /ut1 !ffunE;
  by case: ifP=>H1; by [rewrite (eqP H1) E | case: eqP].
move: Hu'; rewrite (sepitS (rep d c2)) !in_set E /=.
case=>[hu1][hu3][->][Hu1'][Hu2'] _; rewrite -(unA hu1) -5!(unCA hu1).
apply: (bnd_gh (use d (rep d c2))); last first.
- by rewrite ffunE E.
- by move=>??[?][].
move=>_ {hu1 Hu1'} hu1 [x'] [Hu1'] [->].
rewrite -!(unCA hu); apply: {hu} val_gh Hu=>[[] hu [Hu] _|??[]//].
rewrite (_ : _ :+ _ = hr :+ (hc :+ (hu :+ (hu'' :+ (hu1 :+ hu3)) :+ (ht :+ (p :-> q :+ hp)))));
  last by heap_congr.
move=>D; split=>//; exists d1; split; last first.
- split; first by apply: propagate_nopendP.
  split; first by rewrite /d1.
  by rewrite -ERel; apply: propagate_clos_nopendP.
split=>//; exists ct; exists (ut2 x'); hauto D.
rewrite (sepitT1 (rep d c1)) /table !ffunE eq_sym E eq_refl; hauto D.
rewrite (sepitS (rep d c2)) !in_set E /= !ffunE eq_refl E; hauto D.
apply: tableP Hu2'=>y; rewrite !in_set /u' !ffunE;
(case: ifP=>H1; first by rewrite (eqP H1) eq_refl);
by case: ifP=>H2 //; rewrite (eqP H2) eq_refl andbF.
Qed.

Module Dummy5. End Dummy5.

Program
Definition Match_exp (A : Type) (t : exp) (p1 : symb -> spec A) (p2 : exp -> exp -> spec A)
                     (c1 : forall s, STsep A (p1 s))
                     (c2 : forall t1 t2, STsep A (p2 t1 t2)) :
            STsep A (match t with const s => (p1 s) | app t1 t2 => (p2 t1 t2) end) :=
  match t with const s => st.do (c1 s) _ | app t1 t2 => st.do (c2 t1 t2) _ end.

Let pend3 (e : symb*symb*symb) := let: (a, _, _) := e in a.
Notation "e ..0" := (pend3 e) (at level 2).

Definition nT : Type :=
  forall t, STsep exp (fun i => exists d, i \In bshape' d,
                       fun y i m => forall d, i \In bshape' d ->
                         m \In bshape' d /\ y = Val (norm d t)).

Program Definition hnorm :=
  Fix (fun (hnorm : nT) (t : exp) =>
    Do (Match_exp t
          (fun a => a' <-- Array.read r a;
                    ret (const a'))
          (fun t1 t2 =>
             u1 <-- hnorm t1;
             u2 <-- hnorm t2;
             Match_exp u1
               (fun w1 =>
                  Match_exp u2
                    (fun w2 =>
                       v <-- KVmap.lookup htab (w1, w2);
                       match_opt v then ret (app u1 u2)
                       else [a] a' <-- Array.read r (a..0);
                                ret (const a'))
                    (fun _ _ => ret (app u1 u2)))
                (fun _ _ => ret (app u1 u2))))).
Next Obligation.
apply: (ghost2 (t:=H)); first by move=>???; move/(bshape_inv H0)=>->.
move: H H0=>d [CI][ct][ut][hr][hrest][->][Hr][Hrest].
case: t=>[s|t1 t2].
- apply: bnd_gh (Hr)=>[_ _ [[->]] <-|??[]//]=>D.
  by apply: val_ret=>//; do 2!split=>//; exists ct; exists ut; hauto D.
rewrite -(unh0 (_ :+ _))=>D.
apply: (bnd_gh d)=>[u1 m1 [W1] [E1] D1|??[]//||//]; last first.
- by split=>//; exists ct; exists ut; hauto D.
apply: (bnd_gh d)=>[u2 m2 [W2] [E2]|??[]||] //; rewrite unh0.
move: W2=>{CI ct ut hr hrest Hr Hrest D}[CI][ct][ut][hr][w][->][Hr][[hc]][w'].
move=>[->{w}][Hc][[hu]][w][->{w'}][Hu][[ht]][hrest][->{w}][Ht][Hrest] _ _ _ _ D.
case: u1 E1=>[w1|??] /= E1; last first.
- rewrite -E1 E2; apply: val_ret=>//; do 2!split=>//.
  by exists ct; exists ut; hauto D.
case: u2 E2=>[w2|??] /= E2; last first.
- rewrite -E1 -E2; apply: val_ret=>//; do 2!split=>//.
  by exists ct; exists ut; hauto D.
move: D; rewrite -3!(unCA ht).
apply: bnd_gh Ht=>{ht x} [v ht [Ht][Ev]|??[]//]; rewrite 3!(unCA ht) -E1 -E2.
case: v Ev=>[[[a0 a1] a2]|] /= <- D; last first.
- by apply: val_ret=>//; do 2!split=>//; exists ct; exists ut; hauto D.
apply: bnd_gh (Hr) (D)=>[a' _ [[->]] <-|??[]//].
by apply: val_ret; do 2!split=>//; exists ct; exists ut; hauto D.
Qed.

Module Dummy6. End Dummy6.

Program Definition check t1 t2 :
           STsep bool (fun i => exists R, i \In shape' R,
                       fun y i m => forall R, i \In shape' R -> m \In shape' R /\
                               exists b, y = Val b /\ (b <-> (t1, t2) \In R)) :=
  Do (u1 <-- hnorm t1;
      u2 <-- hnorm t2;
      ret (u1 == u2)).
Next Obligation.
apply: (ghost2 (t:=H)).
- by move=>???; move/(shape_inv H0)=>E [L1][b][->] L2; move: L1 L2; rewrite E; eauto.
move: H H0 (shapeD H0)=>R [d][H][[RI]H1][P] H2; rewrite -(unh0 i).
apply: {i} bnd_gh H=>[u1 i [H] [->]|??[]//].
apply: {i} bnd_gh H=>[u2 i [H] [->]|??[]//].
apply: val_ret=>//; rewrite unh0; split; first by exists d.
exists (norm d t1 == norm d t2); split=>//.
by case: normP=>//; rewrite H2; move=>H3; split.
Qed.
