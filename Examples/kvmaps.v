(******************)
(* Key-Value maps *)
(******************)

From Coq Require Import Program.Wf ssrfun.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype tuple finfun path.
From fcsl Require Import axioms pred ordtype finmap.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import domain stmod stsep stlog stlogR.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

(********************)
(* stateful KV maps *)
(********************)

Module KVmap.
Record Sig (K : ordType) (V : Type) : Type :=
  make {tp :> Type;
        default : tp;
        shape : tp -> {finMap K -> V} -> Pred heap;
        shapeD : forall x s h, h \In shape x s -> valid h;
        shape_invert : forall x s1 s2 h, valid h -> h \In shape x s1 -> h \In shape x s2 -> s1 = s2;

        new : STsep (emp, [vfun x => shape x (nil K V)]);

        free : forall x, {s}, STsep (shape x s,
                                     [vfun _ : unit => emp]);

        insert : forall x k v,
                   {s}, STsep (shape x s,
                               [vfun y => shape y (ins k v s)]);

        remove : forall x k,
                   {s}, STsep (shape x s,
                               [vfun y => shape y (rem k s)]);

        lookup : forall x k,
                   {s}, STsep (shape x s,
                               [vfun y m => m \In shape x s /\ y = fnd k s])}.
End KVmap.

(**************************************************)
(* KVmap implemented as a sorted association list *)
(**************************************************)

Module AssocList.
Section AssocList.

Variable (K : ordType) (V : Set).
Notation fmap := (finMap K V).
Notation nil := (nil K V).

(* TODO this should be expressible directly *)
Lemma path_relax (k k' : K) ks : ord k k' -> path ord k' ks -> path ord k ks.
Proof.
move=>O; case: ks=>//= a l /andP [O2 P2].
apply/andP; split=>//.
by apply/trans/O2.
Qed.

(* Data is stored in a sorted associative linked list. *)

Definition entry (p q : ptr) (k : K) (v : V) : heap := p :-> k \+ (p .+ 1 :-> v \+ p .+ 2 :-> q).

Fixpoint shape_seg' (x y : ptr) (xs : seq (K * V)) : Pred heap :=
  match xs with
    | (k,v)::tl =>
       fun h => exists q h',
       h = x :-> k \+ (x .+ 1 :-> v \+ (x .+ 2 :-> q \+ h'))
        /\
       h' \In shape_seg' q y tl
    | [::] => [Pred h | x = y /\ h = Unit]
  end.

Definition shape_seg (x y : ptr) (s : finMap K V) : Pred heap :=
  shape_seg' x y (seq_of s).

Definition shape' (x : ptr) (xs : seq (K * V)) : Pred heap :=
  shape_seg' x null xs.

Definition shape (x : ptr) (s : finMap K V) : Pred heap :=
  shape_seg x null s.

Lemma shape_null (s : fmap) h : valid h -> h \In shape null s -> s = nil /\ h = Unit.
Proof.
move=>D; case: s; case=>/=.
- by move=>? [_ ->] //; rewrite fmapE.
move=>[??]??[?][?][H].
by rewrite H validPtUn in D.
Qed.

Lemma shape_cont (s : fmap) p h :
        p != null -> h \In shape p s ->
        exists k v q h',
         [/\ s = ins k v (behd s),
             path ord k (supp (behd s)),
             h = p :-> k \+ (p .+ 1 :-> v \+ (p .+ 2 :-> q \+ h'))
           & h' \In shape q (behd s)].
Proof.
move=>E; case: s=>xs srt /=.
elim: xs srt=>/=.
- by move=>? [E0]; rewrite E0 in E.
move=>[k v] /= l IH srt [q][h'][-> H].
exists k,v,q,h'; split=>//.
by rewrite fmapE /= last_ins'.
Qed.

Lemma shape_cons (s : fmap) p q h k v :
   path ord k (supp s) -> h \In shape q s ->
   (p :-> k \+ (p .+ 1 :-> v \+ (p .+ 2 :-> q \+ h))) \In shape p (ins k v s).
Proof.
move=>S H.
suff: ins k v s = FinMap (seq_of := (k,v)::seq_of s) S by move=>->; exists q,h.
rewrite fmapE /=; case: s {H}S=>/= xs ??.
by rewrite last_ins'.
Qed.

Lemma shape_seg_rcons (s : fmap) x p q h k v :
   (forall k0, k0 \in supp s -> ord k0 k) -> h \In shape_seg x p s ->
   (h \+ entry p q k v) \In shape_seg x q (ins k v s).
Proof.
case: s=>xs; elim: xs h x=>/=.
- move=>??? S [->->]; rewrite unitL.
  by exists q, Unit; rewrite unitR.
move=>[k' v'] /= xs IH h x S O H.
rewrite /shape_seg /= in IH H *.
have O' : ord k' k by apply: O; rewrite inE eq_refl.
move/nsym/negP/negbTE: (O')=>->.
case E: (k==k')=>/=; first by move: O'; move/eqP: E=>->; move: (irr k')=>->.
case: H=>x0[h'][-> H'].
exists x0, (h' \+ entry p q k v); rewrite -!joinA; split=>//.
apply: IH=>//; first by apply: (path_sorted S).
move=>S0 k0 H0; apply: O.
by rewrite inE /=; apply/orP; right.
Qed.

Lemma shape_fcat s1 s2 h1 h2 x y :
  (forall k0, k0 \in supp s1 -> path ord k0 (supp s2)) ->
  h1 \In shape_seg x y s1 -> h2 \In shape y s2 ->
  h1 \+ h2 \In shape x (fcat s1 s2).
Proof.
move=>O1 H1.
case: s2 O1=>xs; elim: xs h1 y h2 s1 H1=>/=.
- by move=>???? H1 ?? [Eq ->]; rewrite Eq in H1; rewrite unitR.
move=>[k' v'] xs; rewrite /fcat /= => IH /= h1 y h2 s1 H1 srt O2 H2.
case: H2=>z[h'][-> H']; rewrite !joinA.
apply: IH; first 1 last.
- by apply/path_sorted/srt.
- move=>H0 k0; rewrite supp_ins !inE =>/orP; case; first by move/eqP=>->.
  by case/O2/andP; apply: path_relax.
- by move=>?; apply: H'.
rewrite -!joinA; apply shape_seg_rcons=>//.
by move=>k0; case/O2/andP.
Qed.

(* main procedures *)

Program Definition new : STsep (emp, [vfun x => shape x nil]) :=
  Do (ret null).
Next Obligation. by move=>/= ?->; step. Qed.

Definition freeT : Type :=
  forall p, {fm}, STsep (shape p fm, [vfun _ : unit => emp]).

Program Definition free : freeT :=
 Fix (fun (go : freeT) p =>
      Do (if p == null then ret tt
          else pnext <-- !(p .+ 2);
               dealloc p;;
               dealloc (p .+ 1);;
               dealloc (p .+ 2);;
               go pnext)).
Next Obligation.
move=>go p; apply: ghR=>i s H D.
case: eqP.
- move=>E; step=>_; rewrite E in H.
  by case: (shape_null D H).
move/eqP=>E; case: (shape_cont E H)=>k[v][q][h'][_ _ -> H2].
do 4!step; rewrite !unitL.
by apply/(gh_ex (behd s))/val_doR.
Qed.

Definition lookupT k : Type :=
  forall p, {fm}, STsep (shape p fm, [vfun y m => m \In shape p fm /\ y = fnd k fm]).

Program Definition lookup (k : K) : lookupT k :=
 Fix (fun (go : lookupT k) (cur : ptr) =>
      Do (if cur == null then ret None
          else
            k' <-- !cur;
            if k == k'
              then v <-- !(cur .+ 1);
                   ret (Some v)
              else if ord k' k
                then next <-- !(cur .+ 2);
                     go next
                else ret None)).
Next Obligation.
move=>k go cur; apply: ghR=>h fm H Vh.
case: eqP.
- move=>Ec; step=>_; rewrite Ec in H.
  by case: (shape_null Vh H)=>->.
move/eqP=>Ec; case: (shape_cont Ec H)=>k'[v][next][h'][Ef O' Ei H'].
rewrite {Vh}Ei in H *; step; case: eqP.
- move=>Ek; do 2!step; move=>_; split=>//.
  by rewrite Ef fnd_ins Ek eq_refl.
move/eqP=>Ek; case: ifP=>Ho'.
- step; rewrite !joinA joinC.
  apply/frame/(gh_ex (behd fm))/val_doR=>//=.
  move=>v0 h0' [??] _ _; rewrite Ef; split.
  - by rewrite joinC -!joinA; apply: shape_cons.
  by rewrite fnd_ins (negbTE Ek).
move: (semiconnex Ek); rewrite {}Ho' orbC /= =>Ho'.
step=>_; split=>//.
apply/esym/fnd_supp.
rewrite Ef supp_ins inE negb_or; apply/andP; split=>//.
by apply/notin_path/path_relax/O'.
Qed.

Definition removeT p k : Type :=
  forall (prevcur : ptr * ptr),
    {fm}, STsep (fun h => exists fml fmr k' v',
                  [/\ fm = fcat (ins k' v' fml) fmr,
                      (forall kl : K, kl \in supp fml -> ord kl k') /\ path ord k' (supp fmr),
                      k \notin supp fml /\ k != k' &
                      h \In
                       (shape_seg p prevcur.1 fml #
                       (fun h => h = entry prevcur.1 prevcur.2 k' v') #
                       shape prevcur.2 fmr)],
                 [vfun _ : unit => shape p (rem k fm)]).

Program Definition remove x (k : K) : {fm}, STsep (shape x fm,
                                                   [vfun y => shape y (rem k fm)]) :=
  Do (let: rm := Fix (fun (go : removeT x k) '(prev, cur) =>
                      Do (if cur == null then ret tt
                          else k' <-- !cur;
                               if k == k'
                                 then next <-- !(cur .+ 2);
                                      dealloc cur;;
                                      dealloc (cur .+ 1);;
                                      dealloc (cur .+ 2);;
                                      prev .+ 2 ::= (next : ptr);;
                                      ret tt
                                 else if ord k' k
                                      then next <-- !(cur .+ 2);
                                           go (cur, next)
                                      else ret tt))
      in
      if x == null then ret null
        else k' <-- !x;
             if k == k'
                then next <-- !(x .+ 2);
                     dealloc x;;
                     dealloc (x .+ 1);;
                     dealloc (x .+ 2);;
                     ret next
                else if ord k' k
                     then next <-- !(x .+ 2);
                          rm (x, next);;
                          ret x
                     else ret x).
Next Obligation.
move=>x k0 go ? prev cur ?.
apply: ghR=>h fm [fml][fmr][k][v][Ef [Ol Or][Nkl Nk]]/=[hl][h1][{h}-> [Hl [h2][hr][{h1}-> [{h2}-> Hr]]]] Vh.
case: eqP.
- move=>Ec; step=>_.
  rewrite Ec in Hr; rewrite !joinA in Vh.
  rewrite Ef; case: (shape_null (validR Vh) Hr)=>->->.
  rewrite fcats0 unitR rem_ins (negbTE Nk) (rem_supp Nkl) Ec.
  by apply: shape_seg_rcons.
move/eqP=>Ec; case: (shape_cont Ec Hr)=>k'[v'][next][hr'][Efr Or' Ehr Hr'].
rewrite {hr Hr Vh Ec}Ehr joinA joinC.
step; case: eqP.
- move=>Ek; do 4!step; rewrite !unitL; do 2!step; move=>_.
  rewrite Ef Efr -fcat_srem; last by rewrite supp_ins inE negb_or; apply/andP.
  rewrite rem_ins {1}Ek eq_refl rem_supp; last by rewrite Ek; apply: notin_path.
  rewrite joinC; apply/shape_fcat/Hr'; last by apply: shape_seg_rcons.
  move=>kl; rewrite Efr in Or; case/andP: (path_supp_ins_inv Or' Or)=>_ Or''.
  rewrite supp_ins !inE=>/orP; case; first by move/eqP=>->.
  by move/Ol=>?; apply/path_relax/Or''.
move/eqP=>Ek; case: ifP=>Ho0.
- step.
  apply/(gh_ex (fcat (ins k' v' (ins k v fml)) (behd fmr)))/val_doR=>//=.
  - move=>_; exists (ins k v fml), (behd fmr), k', v'; do!split=>//.
    - move=>kl; rewrite Efr in Or; case/andP: (path_supp_ins_inv Or' Or)=>Ho' _.
      rewrite supp_ins inE =>/orP; case; first by move/eqP=>->.
      by move/Ol=>?; apply/trans/Ho'.
    - by rewrite supp_ins inE negb_or; apply/andP.
    exists (hl \+ entry prev cur k v), (entry cur next k' v' \+ hr').
    rewrite joinC !joinA; do!split=>//; last by exists (entry cur next k' v'), hr'.
    by rewrite -!joinA; apply: shape_seg_rcons.
  move=>_ m Hm _; rewrite Ef Efr.
  rewrite fcat_inss // in Hm; first by rewrite -fcat_sins in Hm.
  apply: notin_path; rewrite Efr /= in Or.
  by case/andP: (path_supp_ins_inv Or' Or).
move: (semiconnex Ek); rewrite {}Ho0 orbC /= =>Ho0.
step=>_; rewrite rem_supp Ef.
- rewrite joinC; apply: shape_fcat.
  - move=>kl; rewrite supp_ins !inE=>/orP; case; first by move/eqP=>->.
    by move/Ol=>?; apply/path_relax/Or.
  - by apply: shape_seg_rcons.
  by rewrite Efr; apply: shape_cons.
rewrite Efr supp_fcat !inE negb_or; apply/andP; split;
rewrite supp_ins !inE negb_or; apply/andP; split=>//.
by apply/notin_path/path_relax/Or'.
Qed.
Next Obligation.
move=>/= x k0; apply: ghR=>h fm H Vh.
case: eqP.
- by move: H=>/[swap] ->/(shape_null Vh) [->->]; step=>_.
move/eqP=>Ex {Vh}; case: (shape_cont Ex H)=>k[v][next][h'][Ef Of Eh H']; rewrite Eh.
step; case: eqP.
- move=>->; do 5!step; rewrite !unitL=>_.
  rewrite Ef rem_ins eq_refl rem_supp //.
  by apply: notin_path.
move/eqP=>Ek; case: ifP=>Ho0.
- step.
  apply/bnd_seq/(gh_ex fm)/val_do0=>//=; last by move=>_ ???; step.
  move=>_; exists nil, (behd fm), k, v; do!split=>//.
  - by rewrite fcat_inss; [rewrite fcat0s|apply: notin_path].
  exists Unit, (entry x next k v \+ h'); do!split; first by rewrite /entry unitL !joinA.
  by exists (entry x next k v), h'.
move: (semiconnex Ek); rewrite {}Ho0 orbC /= =>Ho0.
step=>_.
rewrite -Eh rem_supp // Ef supp_ins !inE negb_or; apply/andP; split=>//.
by apply/notin_path/path_relax/Of.
Qed.

Definition insertT p k v : Type :=
  forall (prevcur : ptr * ptr),
    {fm}, STsep (fun h => exists fml fmr k' v',
                  [/\ fm = fcat (ins k' v' fml) fmr,
                      (forall kl : K, kl \in supp fml -> ord kl k') /\ path ord k' (supp fmr),
                      k \notin supp fml /\ ord k' k &
                      h \In
                       (shape_seg p prevcur.1 fml #
                       (fun h => h = entry prevcur.1 prevcur.2 k' v') #
                       shape prevcur.2 fmr)],
                 [vfun _ : unit => shape p (ins k v fm)]).

Program Definition insert x (k : K) (v : V) : {fm}, STsep (shape x fm,
                                                          [vfun y => shape y (ins k v fm)]) :=
  Do (let: ns := Fix (fun (go : insertT x k v) '(prev, cur) =>
                      Do (if cur == null
                            then new <-- allocb k 3;
                                 new .+ 1 ::= v;;
                                 new .+ 2 ::= null;;
                                 prev .+ 2 ::= new;;
                                 ret tt
                            else k' <-- !cur;
                                 if k == k'
                                   then cur .+ 1 ::= v;;
                                        ret tt
                                   else if ord k' k
                                        then next <-- !(cur .+ 2);
                                             go (cur, next)
                                        else new <-- allocb k 3;
                                             new .+ 1 ::= v;;
                                             new .+ 2 ::= cur;;
                                             prev .+ 2 ::= new;;
                                             ret tt))
      in
      if x == null
        then new <-- allocb k 3;
             new .+ 1 ::= v;;
             new .+ 2 ::= null;;
             ret new
        else k' <-- !x;
             if k == k'
               then x .+ 1 ::= v;;
                    ret x
               else if ord k' k
                    then next <-- !(x .+ 2);
                         ns (x, next);;
                         ret x
                    else new <-- allocb k 3;
                         new .+ 1 ::= v;;
                         new .+ 2 ::= x;;
                         ret new).
Next Obligation.
move=>x k0 v0 go ? prev cur ?.
apply: ghR=>h fm [fml][fmr][k][v][Ef [Ol Or][Nkl Ho0]]/=[hl][h1][{h}-> [Hl [h2][hr][{h1}-> [{h2}-> Hr]]]] Vh.
case: eqP.
- move=>Ec; step=>p; rewrite ptrA unitR; do 2!step.
  rewrite joinC /entry; do 2!step; move=>_.
  rewrite Ec in Hr; rewrite !joinA in Vh.
  rewrite Ef; case: (shape_null (validR Vh) Hr)=>->->.
  rewrite fcats0 unitR.
  apply: shape_seg_rcons.
  - move=>kl; rewrite supp_ins !inE =>/orP; case; first by move/eqP=>->.
    by move/Ol=>?; apply/trans/Ho0.
  by apply: shape_seg_rcons.
move/eqP=>Ec; case: (shape_cont Ec Hr)=>k'[v'][next][hr'][Efr Or' Ehr Hr'].
rewrite {hr Hr Vh Ec}Ehr joinA joinC.
step; case: eqP.
- move=>Ek; do 2!step; move=>_.
  rewrite Ef Efr -fcat_sins ins_ins -Ek eq_refl joinC.
  apply: shape_fcat.
  - move=>kl; rewrite supp_ins !inE =>/orP; case.
    - move/eqP=>->; apply: path_supp_ins=>//.
      by rewrite Efr in Or; case/andP: (path_supp_ins_inv Or' Or).
    move/Ol=>Hol; have Hol0: ord kl k0 by apply/trans/Ho0.
    apply: path_supp_ins=>//.
    by rewrite -Ek in Or'; apply/path_relax/Or'.
  - by apply: shape_seg_rcons.
  by apply: shape_cons=>//; rewrite Ek.
move/eqP=>Ek; case: ifP=>Ho'0.
- step.
  apply/(gh_ex (fcat (ins k' v' (ins k v fml)) (behd fmr)))/val_doR=>//=.
  - move=>_; exists (ins k v fml), (behd fmr), k', v'; do!split=>//.
    - move=>kl; rewrite Efr in Or; case/andP: (path_supp_ins_inv Or' Or)=>Ho' _.
      rewrite supp_ins inE =>/orP; case; first by move/eqP=>->.
      by move/Ol=>?; apply/trans/Ho'.
    - rewrite supp_ins inE negb_or; apply/andP; split=>//.
      by apply/negP=>/eqP; move: Ho0=>/[swap]->; rewrite irr.
    exists (hl \+ entry prev cur k v), (entry cur next k' v' \+ hr').
    rewrite joinC !joinA; do!split=>//; last by exists (entry cur next k' v'), hr'.
    by rewrite -!joinA; apply: shape_seg_rcons.
  move=>_ m Hm _; rewrite Ef Efr.
  rewrite fcat_inss // in Hm; first by rewrite -fcat_sins in Hm.
  apply: notin_path; rewrite Efr /= in Or.
  by case/andP: (path_supp_ins_inv Or' Or).
move: (semiconnex Ek); rewrite {}Ho'0 orbC /= =>Ho0'.
step=>new; rewrite ptrA unitR; do 2!step.
rewrite joinA joinC /entry; do 2!step; move=>_.
rewrite Ef Efr -fcat_sins; apply: shape_fcat.
- move=>kl; rewrite supp_ins !inE =>/orP; case.
  - have Ho': ord k k' by apply/trans/Ho0'.
    move/eqP=>->; do 2!apply: path_supp_ins=>//.
    by apply/path_relax/Or'.
  move/Ol=>Ho.
  have Hol0: ord kl k0 by apply/trans/Ho0.
  have Ho': ord kl k' by apply/trans/Ho0'.
  do 2!apply: path_supp_ins=>//.
  by apply/path_relax/Or'.
- by apply: shape_seg_rcons.
rewrite -!joinA; apply: shape_cons.
- by apply: path_supp_ins=>//; apply/path_relax/Or'.
by apply: shape_cons.
Qed.
Next Obligation.
move=>/= x k0 v0; apply: ghR=>h fm H Vh.
case: eqP.
- move: H=>/[swap] ->/(shape_null Vh) [->->].
  step=>p; rewrite ptrA !unitR; do 3!step; move=>_.
  by exists null, Unit; rewrite unitR.
move/eqP=>Ex; case: (shape_cont Ex H)=>k[v][next][h'][Ef Of -> H'].
step; case: eqP.
- move=>->; do 2!step; move=>_.
  rewrite Ef ins_ins eq_refl.
  by apply: shape_cons.
move/eqP=>Ek; case: ifP=>Ho0.
- step.
  apply/bnd_seq/(gh_ex fm)/val_do0=>//=; last by move=>_ ???; step.
  move=>_; exists nil, (behd fm), k, v; do!split=>//.
  - by rewrite fcat_inss; [rewrite fcat0s|apply: notin_path].
  exists Unit, (entry x next k v \+ h'); do!split; first by rewrite /entry unitL !joinA.
  by exists (entry x next k v), h'.
move: (semiconnex Ek); rewrite {}Ho0 orbC /= =>Ho0.
step=>q; rewrite ptrA unitR; do 3!step; move=>_.
rewrite Ef -!joinA; apply: shape_cons.
- by apply: path_supp_ins=>//; apply/path_relax/Of.
by apply: shape_cons.
Qed.

(*
Definition AssocList := KVmap.make null shapeD shape_invert new free insert remove lookup.
*)
End AssocList.
End AssocList.
