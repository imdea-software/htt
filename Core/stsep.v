From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype fintype finset bigop.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import interlude stmod.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope stsep_scope.
Delimit Scope stsep_scope with stsep.
Open Scope stsep_scope.

Definition star (p1 p2 : Pred heap) : Pred heap :=
  [Pred h | exists h1 h2, [ /\ h = h1 \+ h2, h1 \In p1 & h2 \In p2] ].
Definition emp : Pred heap := eq^~ Unit.
Definition top : Pred heap := PredT.

Notation "p1 '#' p2" := (star p1 p2)
  (at level 57, right associativity) : rel_scope.

Module Iter.
Section Iter.
Variable A : Type.

Definition bigjoin (s : seq heap) : heap :=
  \big[PCM.join/Unit]_(i <- s) i.

Definition bigand {T : Type} (s : seq T) (f : T -> Prop) : Prop :=
  \big[and/True]_(i <- s) (f i).

Lemma bigand_cat {T : Type} (s1 s2 : seq T) f :
        bigand (s1 ++ s2) f <-> bigand s1 f /\ bigand s2 f.
Proof.
rewrite /bigand big_cat_nested; elim: s1.
- by rewrite !big_nil; split=>// [[]].
move=>a l IH; rewrite !big_cons; split.
- by case=>?; move/IH=>[??].
by case=>[[??]?]; split=>//; rewrite IH.
Qed.

Definition sepit (s : seq A) (f : A -> Pred heap) : Pred heap :=
  [Pred h | exists hs : seq heap,
              [ /\ size hs = size s, h = bigjoin hs &
                   bigand (zip s hs) [pts a h | h \In f a] ] ].

Lemma sepit0 f : sepit [::] f =p emp.
Proof.
move=>h; split.
- by case=>/= hs [/size0nil -> -> _]; rewrite /bigjoin !big_nil.
by move=>->; exists [::]; rewrite /bigjoin /bigand !big_nil.
Qed.

Lemma sepit_cons x s f : sepit (x::s) f =p f x # sepit s f.
Proof.
move=>h; split.
- case=>/=; case=>[|h0 hs]; case=>//= /eqP; rewrite eqSS =>/eqP Hs.
  rewrite /bigjoin /bigand !big_cons /= =>->[H0 H1].
  by exists h0, (bigjoin hs); do!split=>//; exists hs.
case=>h1[_][{h}-> H1][hs][E -> H].
by exists (h1 :: hs); rewrite /= E /bigjoin /bigand !big_cons.
Qed.

Lemma sepit_cat s1 s2 f : sepit (s1 ++ s2) f =p sepit s1 f # sepit s2 f.
Proof.
elim: s1 s2=>[|x s1 IH] s2 h /=; split.
- case=>hs [E {h}-> H2].
  exists Unit, (bigjoin hs); rewrite unitL.
  by split=>//; [rewrite sepit0 | exists hs].
- by case=>h1[h2][{h}->]; rewrite sepit0=>->; rewrite unitL.
- case=>/=; case=>[|h0 hs]; case=>//= /eqP; rewrite eqSS=>/eqP E.
  rewrite /bigjoin /bigand !big_cons /= =>->[H0 HS].
  case: (IH s2 (bigjoin hs)).1; first by exists hs.
  move=>h1[h2][HJ H1 H2]; rewrite /bigjoin in HJ.
  exists (h0 \+ h1), h2; rewrite HJ joinA; split=>//.
  by rewrite sepit_cons; exists h0, h1.
case=>h1[h2][{h}->[]]; case=>[|h0 hs1]; case=>//= /eqP; rewrite eqSS=>/eqP E1.
rewrite /bigjoin /bigand !big_cons /= =>{h1}->[H0 H1]; case=>hs2[E2 {h2}-> H2].
exists (h0 :: hs1 ++ hs2); rewrite /bigjoin /bigand big_cons big_cat joinA; split=>//=.
- by rewrite !size_cat E1 E2.
rewrite big_cons zip_cat //=; split=>//.
by apply/bigand_cat.
Qed.

End Iter.

Section IterEq.
Variable A : eqType.

Lemma sepitP (x : A) (s : seq A) f : uniq s ->
       sepit s f =p if x \in s then f x # sepit (filter (predC1 x) s) f
                    else sepit s f.
Proof.
case E: (x \in s)=>//.
elim: s E=>[|y s IH] //= /[swap]; case/andP=>Hy Hu; rewrite inE=>/orP.
case; [move/eqP=>->; rewrite eq_refl /=|move=>Hx]; rewrite sepit_cons=>h0.
- by split; case=>h1[h2][{h0}-> H1 H]; exists h1, h2; split=>//;
  [rewrite filter_predC1 | rewrite filter_predC1 in H].
have ->: (y != x) by apply/eqP=>Hxy; rewrite Hxy Hx in Hy.
by split; case=>ha[h1][{h0}-> Ha]; [rewrite (IH Hx Hu) | rewrite sepit_cons];
case=>hb[h][{h1}-> Hb H]; rewrite joinCA;
exists hb, (ha \+ h); split=>//;
[rewrite sepit_cons | rewrite (IH Hx Hu)]; exists ha, h.
Qed.

Lemma eq_sepitF (s : seq A) (f1 f2 : A -> Pred heap) :
        (forall x, x \in s -> f1 x =p f2 x) -> sepit s f1 =p sepit s f2.
Proof.
elim: s=>[|x s IH] H h; first by rewrite !sepit0.
have /IH {IH}H': forall x : A, x \in s -> f1 x =p f2 x
  by move=>? H0; apply: H; rewrite !inE H0 orbT.
have Hx : x \in x :: s by rewrite inE eq_refl.
by rewrite !sepit_cons; split; case=>h1[h2][{h}-> H1 H2]; exists h1, h2;
split=>//; [rewrite -H | rewrite -H' | rewrite H | rewrite H'].
Qed.

Lemma perm_sepit (s1 s2 : seq A) f :
        perm_eq s1 s2 -> sepit s1 f =p sepit s2 f.
Proof.
elim: s1 s2 =>[|x s1 IH] s2 /=.
- by rewrite perm_sym=>/perm_size/size0nil->.
move=>H.
have Hx: x \in s2 by rewrite -(perm_mem H) inE eq_refl.
move: (mem_split Hx)=>[t1][t2] E; rewrite E in H *.
have {H Hx s2 E}Hp : perm_eq s1 (t1 ++ t2).
- by rewrite -(perm_cons x); apply: (perm_trans H); rewrite perm_catCA.
rewrite sepit_cons sepit_cat /= =>h0; split.
- case=>h1[h2][{h0}-> H1]; rewrite (IH _ Hp) sepit_cat.
  case=>_[_][{h2}-> [hs3][E3 -> H3] [hs4][E4 -> H4]]; rewrite joinCA.
  exists (bigjoin hs3), (h1 \+ bigjoin hs4); split=>//; first by exists hs3.
  by rewrite sepit_cons; exists h1, (bigjoin hs4); split=>//; exists hs4.
case=>_[h2][{h0}-> [hs1][Hs1 -> H1]]; rewrite sepit_cons.
case=>h3[_][{h2}-> H3 [hs2][Hs2 -> H2]]; rewrite joinCA.
exists h3, (bigjoin hs1 \+ bigjoin hs2); split=>//.
rewrite (IH _ Hp); exists (hs1 ++ hs2); split.
- by rewrite !size_cat Hs1 Hs2.
- by rewrite /bigjoin big_cat.
by rewrite /bigand zip_cat //; apply/bigand_cat.
Qed.

End IterEq.

End Iter.

Module FinIter.
Section FinIter.
Variable I : finType.

Definition seq_of (s : {set I}) := [seq x <- enum I | x \in s].

Lemma mem_seq_of (s : {set I}) x : (x \in seq_of s) = (x \in s).
Proof. by rewrite /seq_of mem_filter mem_enum andbT. Qed.

Lemma setq (s1 s2 : {set I}) : s1 = s2 <-> seq_of s1 =i seq_of s2.
Proof.
split=>[->|H] //; rewrite -setP=>x; move: (H x).
by rewrite /seq_of !mem_filter -enumT mem_enum !andbT /in_mem.
Qed.

Lemma uniq_seq_of (s : {set I}) : uniq (seq_of s).
Proof. by rewrite /seq_of filter_uniq // enum_uniq. Qed.

Lemma perm_seqP (s1 s2 : {set I}) :
       reflect (seq_of s1 =i seq_of s2)
               (perm_eq (seq_of s1) (seq_of s2)).
Proof.
case E: (perm_eq _ _); constructor.
- by apply: perm_mem.
by move=>H; elim: (elimF idP E); apply: uniq_perm H; rewrite uniq_seq_of.
Qed.

Definition sepit (s : {set I}) (Ps : I -> Pred heap) :=
  Iter.sepit (seq_of s) Ps.

Lemma sepit0 f : sepit set0 f =p emp.
Proof.
rewrite /sepit /seq_of.
rewrite (Iter.perm_sepit (s2 := filter pred0 (enum I))); first by rewrite filter_pred0 Iter.sepit0.
apply: uniq_perm; try by rewrite filter_uniq // enum_uniq.
by move=>x; rewrite !mem_filter /= in_set0.
Qed.

Lemma sepitF (s : {set I}) f1 f2 :
        (forall x, x \in s -> f1 x =p f2 x) -> sepit s f1 =p sepit s f2.
Proof.
move=>H; apply: Iter.eq_sepitF=>x H1; apply: H.
by rewrite -mem_seq_of.
Qed.

Lemma eq_sepit (s1 s2 : {set I}) f : s1 =i s2 -> sepit s1 f =p sepit s2 f.
Proof.
rewrite setP setq.
suff: perm_eq (seq_of s1) (seq_of s2) -> sepit s1 f =p sepit s2 f.
- by move=>H H2; apply: H; case: perm_seqP.
by apply: Iter.perm_sepit.
Qed.

Lemma sepitS x (s : {set I}) f :
        sepit s f =p if x \in s then f x # sepit (s :\ x) f
                     else sepit s f.
Proof.
case E: (x \in s)=>//.
rewrite (Iter.sepitP x (s:=seq_of s) f (uniq_seq_of s)) mem_seq_of E.
have Hp: perm_eq [seq y <- seq_of s | predC1 x y] (seq_of (s :\ x)).
- rewrite /seq_of -filter_predI.
  apply: uniq_perm=>[||y]; try by rewrite filter_uniq // enum_uniq.
  by rewrite !mem_filter /= in_setD1.
by move=>h0; split; case=>h1[h2][{h0}-> H1 H]; exists h1, h2; split=>//;
rewrite Iter.perm_sepit; try by [exact: H]; [rewrite perm_sym |].
Qed.

Lemma sepitT1 x f : sepit setT f =p f x # sepit (setT :\ x) f.
Proof. by rewrite (sepitS x) in_setT. Qed.

End FinIter.
End FinIter.

(****************************************************)
(* Notation to move from binary posts to unary ones *)
(****************************************************)

Notation "'Do' e" := (@STprog _ _ _ e _) (at level 80).

Definition logbase A (p : pre) (q : post A) : spec unit A :=
  fun => (p, q).

Definition logvar {B A} (G : A -> Type) (s : forall x : A, spec (G x) B) :
             spec {x : A & G x} B :=
  fun '(existT x g) => s x g.

Notation "'STsep' ( p , q ) " := (STspec (logbase p q)) (at level 0).

Notation "{ x .. y }, 'STsep' ( p , q ) " :=
  (STspec (logvar (fun x => .. (logvar (fun y => logbase p q)) .. )))
   (at level 0, x binder, y binder, right associativity).

Notation "x '<--' c1 ';' c2" := (Model.bind c1 (fun x => c2))
  (at level 78, right associativity) : stsep_scope.
Notation "c1 ';;' c2" := (Model.bind c1 (fun _ => c2))
  (at level 78, right associativity) : stsep_scope.
Notation "'!' x" := (Model.read_st _ x) (at level 50) : stsep_scope.
Notation "e1 '::=' e2" := (Model.write_st e1 e2) (at level 60) : stsep_scope.
