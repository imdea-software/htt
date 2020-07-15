Require Import ssreflect ssrfun.
From mathcomp.ssreflect Require Import ssrbool ssrnat seq eqtype path.
From HTT Require Import pred.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(****************************************************)
(* A theory of permutations over non-equality types *)
(****************************************************)

Section Permutations.
Variable A : Type.

Inductive perm : seq A -> seq A -> Prop :=
| permutation_nil : perm [::] [::]
| permutation_skip x s1 s2 of perm s1 s2 : perm (x :: s1) (x :: s2)
| permutation_swap x y s1 s2 of perm s1 s2 : perm [:: x, y & s1] [:: y, x & s2]
| permutation_trans t s1 s2 of perm s1 t & perm t s2 : perm s1 s2.

Lemma pperm_refl (s : seq A) : perm s s.
Proof. by elim: s=>*; [apply: permutation_nil | apply: permutation_skip]. Qed.

Hint Resolve pperm_refl : core.

Lemma pperm_nil (s : seq A) : perm [::] s <-> s = [::].
Proof.
split; last by move=>->; apply: permutation_nil.
move E: {1}[::]=>l H; move: H {E}(esym E).
by elim=>//??? _ IH1 _ IH2 /IH1/IH2.
Qed.

Lemma pperm_sym s1 s2 : perm s1 s2 <-> perm s2 s1.
Proof.
suff {s1 s2} L : forall s1 s2, perm s1 s2 -> perm s2 s1 by split; apply: L.
apply: perm_ind=>[|||??? _ H1 _ H2] *;
by [apply: permutation_nil | apply: permutation_skip |
    apply: permutation_swap | apply: permutation_trans H2 H1].
Qed.

Lemma pperm_trans s2 s1 s3 : perm s1 s2 -> perm s2 s3 -> perm s1 s3.
Proof. by apply: permutation_trans. Qed.

Lemma pperm_in s1 s2 x : perm s1 s2 -> x \In s1 -> x \In s2.
Proof. elim=>//??? =>[|?|_ I1 _ I2 /I1/I2]; rewrite ?InE; tauto. Qed.

Lemma pperm_catC s1 s2 : perm (s1 ++ s2) (s2 ++ s1).
Proof.
elim: s1 s2=>[|x s1 IH1] s2 /=; first by rewrite cats0.
apply: (@pperm_trans (x::s2++s1)); first by apply: permutation_skip.
elim: s2=>[|y s2 IH2] //=.
apply: (@pperm_trans (y::x::s2++s1)); first by apply: permutation_swap.
by apply: permutation_skip.
Qed.

Hint Resolve pperm_catC : core.

Lemma pperm_cat2lL s s1 s2 : perm s1 s2 -> perm (s ++ s1) (s ++ s2).
Proof. by elim: s=>[//|e s IH /IH]; apply: permutation_skip. Qed.

Lemma pperm_cat2rL s s1 s2 : perm s1 s2 -> perm (s1 ++ s) (s2 ++ s).
Proof.
move=>?.
apply: (@pperm_trans (s ++ s1)); first by apply: pperm_catC.
apply: (@pperm_trans (s ++ s2)); last by apply: pperm_catC.
by apply: pperm_cat2lL.
Qed.

Lemma pperm_catL s1 t1 s2 t2 :
        perm s1 s2 -> perm t1 t2 -> perm (s1 ++ t1) (s2 ++ t2).
Proof. by move/(pperm_cat2rL t1)=>H1/(pperm_cat2lL s2); apply: pperm_trans. Qed.

Lemma pperm_cat_consL s1 t1 s2 t2 x :
        perm s1 s2 -> perm t1 t2 -> perm (s1 ++ x :: t1) (s2 ++ x :: t2).
Proof. by move=>*; apply: pperm_catL=>//; apply: permutation_skip. Qed.

Lemma pperm_cons_catCA s1 s2 x : perm (x :: s1 ++ s2) (s1 ++ x :: s2).
Proof.
rewrite -cat1s -(cat1s _ s2) !catA.
by apply/pperm_cat2rL/pperm_catC.
Qed.

Lemma pperm_cons_catAC s1 s2 x : perm (s1 ++ x :: s2) (x :: s1 ++ s2).
Proof. by apply/pperm_sym/pperm_cons_catCA. Qed.

Hint Resolve pperm_cons_catCA pperm_cons_catAC : core.

Lemma pperm_cons_cat_consL s1 s2 s x :
        perm s (s1 ++ s2) -> perm (x :: s) (s1 ++ x :: s2).
Proof.
move=>?.
apply: (@pperm_trans (x :: (s1 ++ s2))); first by apply: permutation_skip.
by apply: pperm_cons_catCA.
Qed.

Lemma pperm_size l1 l2: perm l1 l2 -> size l1 = size l2.
Proof. by elim=>//=???? =>[|?|]->. Qed.

Lemma pperm_cat_consR s1 s2 t1 t2 x :
        perm (s1 ++ x :: t1) (s2 ++ x :: t2) -> perm (s1 ++ t1) (s2 ++ t2).
Proof.
move: s1 t1 s2 t2 x.
suff H:
  forall r1 r2, perm r1 r2 -> forall x s1 t1 s2 t2,
    r1 = s1 ++ x :: t1 -> r2 = s2 ++ x :: t2 -> perm (s1 ++ t1) (s2 ++ t2).
- by move=>s1 t1 s2 t2 x /H; apply.
apply: perm_ind; last 1 first.
- move=>s2 s1 s3 H1 IH1 H2 IH2 x r1 t1 r2 t2 E1 E2.
  case: (@In_split _ x s2).
  - by apply: pperm_in H1 _; rewrite E1 Mem_cat; right; left.
  move=>s4 [s5] E; apply: (@pperm_trans (s4++s5)); first by apply: IH1 E1 E.
  by apply: IH2 E E2.
- by move=>x [].
- move=>x t1 t2 H IH y [|b s1] s2 [|c p1] p2 /= [E1 E2] [E3 E4]; subst x;
    rewrite ?E1 ?E2 ?E3 ?E4 in H * =>//.
  - by subst y; apply: pperm_trans H _.
  - by apply: pperm_trans H.
  by apply: permutation_skip=>//; apply: IH E2 E4.
move=>x y p1 p2 H IH z [|b s1] t1 [|c s2] t2 /= [E1 E2] [E3 E4]; subst x y;
  rewrite -?E2 -?E4 in H IH * =>//.
- by apply: permutation_skip.
- case: s2 E4=>/=[|a s2][<-]=>[|E4]; apply: permutation_skip=>//.
  by subst p2; apply: pperm_trans H _; apply pperm_cons_catAC.
- case: s1 E2=>/=[|a s1][<-]=>[|E2]; apply: permutation_skip=>//.
  by subst p1; apply: pperm_trans H; apply pperm_cons_catCA.
case: s1 E2=>/=[|a s1][->]=>E2; case: s2 E4=>/=[|d s2][->]=>E4;
  rewrite ?E2 ?E4 in H IH *.
- by apply: permutation_skip.
- apply: (@pperm_trans [:: d, z & s2 ++ t2]); last by apply: permutation_swap.
  by apply: permutation_skip=>//; apply/(pperm_trans H _ )/pperm_cons_catAC.
- apply: (@pperm_trans [:: a, z & s1 ++ t1]); first by apply: permutation_swap.
  by apply: permutation_skip=>//; apply/pperm_trans/H/pperm_cons_catCA.
by apply: permutation_swap; apply: IH.
Qed.

Lemma pperm_cons x s1 s2 : perm (x :: s1) (x :: s2) <-> perm s1 s2.
Proof.
by split; [apply/(@pperm_cat_consR [::] [::]) | apply: permutation_skip].
Qed.

Lemma pperm_cat2l s s1 s2: perm (s ++ s1) (s ++ s2) <-> perm s1 s2.
Proof. by split; [elim: s=>// ??? /pperm_cons | apply: pperm_cat2lL]. Qed.

Lemma pperm_cat2r s s1 s2 : perm (s1 ++ s) (s2 ++ s) <-> perm s1 s2.
Proof.
split; last by apply: pperm_cat2rL.
by elim: s=>[|??? /pperm_cat_consR]; rewrite ?cats0.
Qed.

Lemma pperm_catAC s1 s2 s3 : perm ((s1 ++ s2) ++ s3) ((s1 ++ s3) ++ s2).
Proof. by move=>*; rewrite -!catA pperm_cat2l. Qed.

Lemma pperm_catCA s1 s2 s3 : perm (s1 ++ s2 ++ s3) (s2 ++ s1 ++ s3).
Proof. by move=>*; rewrite !catA pperm_cat2r. Qed.

Lemma pperm_cons_cat_cons x s1 s2 s :
        perm (x :: s) (s1 ++ x :: s2) <-> perm s (s1 ++ s2).
Proof.
by split; [apply: (@pperm_cat_consR [::]) | apply: pperm_cons_cat_consL].
Qed.

Lemma pperm_cat_cons x s1 s2 t1 t2 :
        perm (s1 ++ x :: t1) (s2 ++ x :: t2) <-> perm (s1 ++ t1) (s2 ++ t2).
Proof.
split=>[|H]; first by apply: pperm_cat_consR.
apply: (@pperm_trans (x::s1++t1))=>//; apply: (@pperm_trans (x::s2++t2))=>//.
by apply/pperm_cons.
Qed.

End Permutations.

Hint Resolve pperm_refl pperm_catC pperm_cons_catCA
             pperm_cons_catAC pperm_catAC pperm_catCA : core.

(* perm and map *)
Lemma pperm_map A B (f : A -> B) (s1 s2 : seq A) :
        perm s1 s2 -> perm (map f s1) (map f s2).
Proof.
elim=>[//|||??? _ IH1 _ IH2]*;
by [apply/pperm_cons | apply/permutation_swap | apply/(pperm_trans IH1 IH2)].
Qed.

(* mapping to ssreflect decidable perm *)
Lemma perm_eq_perm (A : eqType) (s1 s2 : seq A) :
        reflect (perm s1 s2) (perm_eq s1 s2).
Proof.
apply: (iffP idP); last first.
- elim=>[|||??? _ H1 _ H2]*.
  - by apply seq.perm_refl.
  - by rewrite seq.perm_cons.
  - by rewrite -![[:: _, _ & _]]/([::_] ++ [::_] ++ _) seq.perm_catCA;
       rewrite !seq.perm_cat2l.
  by apply: seq.perm_trans H1 H2.
elim: s2 s1 =>[s1 /seq.perm_size/size0nil->// | x s2 IH s1 H].
move: (seq.perm_mem H x); rewrite mem_head=>H'; move: H' H.
move/splitPr=>[p1 p2]; rewrite -cat1s seq.perm_catCA seq.perm_cons=>/IH.
by rewrite -[_::s2]cat0s pperm_cat_cons.
Qed.
