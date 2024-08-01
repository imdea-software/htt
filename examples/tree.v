From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq bigop choice.
From pcm Require Import pred prelude seqext.

(* arbitrarily branching tree *)
Inductive tree A := TNode of A & seq (tree A).
Arguments TNode [A].

Section Tree.
Context {A : Type}.

Definition rt (t : tree A) := let: TNode r _ := t in r.
Definition ch (t : tree A) := let: TNode _ ts := t in ts.

Lemma tree_ext (t : tree A) : TNode (rt t) (ch t) = t.
Proof. by case: t. Qed.

(* a leaf is a node with an empty list *)
Definition lf a : tree A := TNode a [::].

Lemma tree_ind' (P : tree A -> Prop) :
  (forall a l, All P l -> P (TNode a l)) ->
  forall t, P t.
Proof.
move=> indu; fix H 1.
elim => a l; apply indu.
by elim: l.
Qed.

Lemma tree_rec' (P : tree A -> Type) :
  (forall a l, AllT P l -> P (TNode a l)) ->
  forall t, P t.
Proof.
move=>indu; fix H 1.
elim => a l; apply: indu.
by elim: l.
Qed.

(* custom induction principles *)

Lemma tree_ind1 (P : tree A -> Prop) :
        (forall a ts, (forall t, t \In ts -> P t) -> P (TNode a ts)) ->
        forall t, P t.
Proof.
move=>H; apply: tree_ind'=>a [_|x xs] /=; first by apply: H.
case=>H1 /AllP H2; apply: H=>t; rewrite InE; case=>[->|] //.
by apply: H2.
Qed.

Fixpoint preorder (t : tree A) : seq A :=
  let: TNode a ts := t in
  foldl (fun s t => s ++ preorder t) [::a] ts.

Corollary foldl_cat {B C} z (fs : seq B) (a : B -> seq C):
        foldl (fun s t => s ++ a t) z fs =
        z ++ foldl (fun s t => s ++ a t) [::] fs.
Proof.
apply/esym/fusion_foldl; last by rewrite cats0.
by move=>x y; rewrite catA.
Qed.

Lemma preorderE t : preorder t = rt t :: \big[cat/[::]]_(c <- ch t) (preorder c).
Proof.
case: t=>a cs /=; rewrite foldl_cat /=; congr (_ :: _).
elim: cs=>/= [| c cs IH]; first by rewrite big_nil.
by rewrite big_cons foldl_cat; rewrite IH.
Qed.

End Tree.

Arguments tree_ind1 [A P].

Section EncodeDecodeTree.
Variable A : Type.

Fixpoint encode_tree (t : tree A) : GenTree.tree A :=
  match t with
  | TNode a [::] => GenTree.Leaf a
  | TNode a l => GenTree.Node O(*dummy*) (GenTree.Leaf a :: map encode_tree l)
  end.

Fixpoint decode_tree (t : GenTree.tree A) : option (tree A) :=
  match t with
  | GenTree.Leaf a => Some (TNode a [::])
  | GenTree.Node _ (GenTree.Leaf h :: l) => Some (TNode h (pmap decode_tree l))
  | GenTree.Node _ _ => None
  end.

Lemma pcancel_tree : pcancel encode_tree decode_tree.
Proof.
elim/(@tree_ind' A) => a [//|b s /= [-> H2 /=]]; congr (Some (TNode _ (_ :: _))).
elim: s H2 => // c s IH /= [-> K2 /=]; by rewrite IH.
Qed.

End EncodeDecodeTree.

Definition tree_eqMixin (A : eqType) := PcanEqMixin (@pcancel_tree A).
Canonical tree_eqType (A : eqType) := Eval hnf in EqType _ (@tree_eqMixin A).

Section TreeEq.
Context {A : eqType}.

Fixpoint mem_tree (t : tree A) : pred A :=
  let: TNode x l := t in
  fun a => (a == x) || has (mem_tree^~ a) l.

Definition tree_eqclass := tree A.
Identity Coercion tree_of_eqclass : tree_eqclass >-> tree.
Coercion pred_of_tree (t : tree_eqclass) : {pred A} := mem_tree t.

Canonical tree_predType := ssrbool.PredType (pred_of_tree : tree A -> pred A).
(* The line below makes mem_tree a canonical instance of topred. *)
Canonical mem_tree_predType := ssrbool.PredType mem_tree.

Lemma in_tnode a t ts : (t \in TNode a ts) = (t == a) || has (fun q => t \in q) ts.
Proof. by []. Qed.

(* frequently used facts about membership in a tree *)

Lemma in_tnode1 a (ts : seq (tree A)) : a \in TNode a ts.
Proof. by rewrite in_tnode eq_refl. Qed.

Lemma in_tnode2 x y a (ts : seq (tree A)) :
        x \In ts -> y \in x -> y \in TNode a ts.
Proof.
move=>X Y; rewrite in_tnode; apply/orP; right; apply/hasP=>/=.
by exists x=>//; apply/mem_seqP.
Qed.

Lemma rt_in (t : tree A) : rt t \in t.
Proof. by case: t=>/= a ts; exact: in_tnode1. Qed.

Lemma in_preorder t : preorder t =i t.
Proof.
elim/tree_ind1: t=>t cs IH x.
rewrite preorderE in_tnode /= inE; case: eqVneq=>//= N.
rewrite big_cat_mem_seq; apply: eq_in_has=>z Hz.
by rewrite IH //; apply/mem_seqP.
Qed.

Lemma tallP (p : pred A) t :
        reflect {in t, forall x, p x} (all p (preorder t)).
Proof.
by apply: (iffP allP)=>H x Hx; apply: H;
  [rewrite in_preorder | rewrite -in_preorder].
Qed.

End TreeEq.

Arguments in_tnode2 [A x y a ts].
#[export] Hint Resolve in_tnode1 : core.

(* a simplified induction principle for eq types *)
(* to avoid switching with mem_seqP all the time *)
Lemma tree_ind2 (A : eqType) (P : tree A -> Prop) :
        (forall a ts, (forall t, t \in ts -> P t) -> P (TNode a ts)) ->
        forall t, P t.
Proof.
move=>H; apply: tree_ind1=>a ts IH.
by apply: H=>t /mem_seqP; apply: IH.
Qed.

Arguments tree_ind2 [A P].

