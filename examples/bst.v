From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq path.
From fcsl Require Import options axioms pred ordtype.
From fcsl Require Import pcm unionmap heap autopcm automap.
From HTT Require Import interlude model heapauto.
From HTT Require Import bintree.

Section BST.
Context {T : ordType}.

(* A binary _search_ tree remains a binary tree structurally, plus: *)
(* 1. its elements must have an ordering defined on them            *)
(* 2. a recursive invariant should be satisfied:                    *)
(*    all left branch elements are smaller than the node value &    *)
(*    all right branch elements are larger than the node value      *)

(* Search tree operations *)

Fixpoint insert x (t : tree T) : tree T :=
  if t is Node l a r
    then
      if x == a then Node l a r
        else if ord x a then Node (insert x l) a r
                        else Node l a (insert x r)
  else Node leaf x leaf.

Fixpoint search (t : tree T) x : bool :=
  if t is Node l a r
    then
      if x == a then true
        else if ord x a then search l x
                        else search r x
  else false.

(* Search tree invariant & its interaction with operations *)

Fixpoint bst (t : tree T) : bool :=
  if t is Node l a r
    then [&& all (ord^~ a) (inorder l), all (ord a) (inorder r), bst l & bst r]
    else true.

(* Both BSTs and sorted lists can be used to implement lookup structures, but trees *)
(* are more efficient computationally, while lists are simpler to reason about,     *)
(* since the operations on them are associative and commute in many cases. We can   *)
(* switch between two specification styles via the in-order traversal.              *)

Lemma bst_to_sorted (t : tree T) :
        bst t = sorted ord (inorder t).
Proof.
elim: t=>//=l -> a r ->.
by rewrite sorted_cat_cons_cat /= cats1 sorted_rconsE //
  (path_sortedE (@trans T)) andbACA -andbA.
Qed.

(* An in-order specification for insertion *)
Lemma inorder_insert x (t : tree T) :
        bst t ->
        perm_eq (inorder (insert x t))
                (if x \in inorder t then inorder t else x :: inorder t).
Proof.
elim: t=>//=l IHl a r IHr /and4P [Hal Har /IHl Hl /IHr Hr] {IHl IHr}.
rewrite mem_cat inE; case: (ifP [|| _, _ | _]).
- case/or3P=>H.
  - rewrite H in Hl.
    move/allP: Hal=>/(_ x H) /[dup] Hxa /ord_neq/negbTE ->; rewrite Hxa /=.
    by apply/permEl/perm_catr.
  - by rewrite H.
  rewrite H in Hr.
  move/allP: Har=>/(_ x H) /[dup] /nsym/negP/negbTE ->.
  move/ord_neq; rewrite eq_sym =>/negbTE -> /=.
  by apply/permEl/perm_catl; rewrite perm_cons.
move/negbT; rewrite !negb_or; case/and3P=>/negbTE Hxl /negbTE -> /negbTE Hxr;
rewrite {}Hxl in Hl; rewrite {}Hxr in Hr.
case: ifP=>/= H.
- by rewrite -cat_cons; apply/permEl/perm_catr.
rewrite -(cat1s x) -(cat1s a) -(cat1s a (inorder r)).
rewrite perm_sym perm_catC -!catA catA perm_sym catA.
apply/permEl/perm_catl; apply: (perm_trans Hr).
by rewrite cats1 -perm_rcons.
Qed.

(* As a corollary, we can show that insertion preserves the tree invariant *)
Lemma bst_insert x (t : tree T) : bst t -> bst (insert x t).
Proof.
elim: t=>//=l IHl a r IHr /and4P [Hal Har Hl Hr].
case: ifP; first by move=>_ /=; rewrite Hal Har Hl Hr.
move=>Hx; case: ifP=>Ho /=.
- rewrite Har (IHl Hl) Hr /= andbT (perm_all _ (inorder_insert x Hl)).
  by case: ifP=>//= _; rewrite Ho.
rewrite Hal Hl (IHr Hr) /= andbT (perm_all _ (inorder_insert x Hr)).
case: ifP=>//= _; rewrite Har andbT.
by case: ordP=>//; [rewrite Ho| rewrite Hx].
Qed.

(* Insertion commutes on in-order representation *)
Lemma insert_insert_perm x1 x2 (t : tree T) :
        bst t ->
        perm_eq (inorder (insert x1 (insert x2 t)))
                (inorder (insert x2 (insert x1 t))).
Proof.
move=>H.
have H1: (bst (insert x1 t)) by apply: bst_insert.
have H2: (bst (insert x2 t)) by apply: bst_insert.
apply: (perm_trans (inorder_insert x1 H2)); rewrite perm_sym.
apply: (perm_trans (inorder_insert x2 H1)).
move: (inorder_insert x1 H)=>{H1}Hi1.
move: (inorder_insert x2 H)=>{H2}Hi2.
rewrite (perm_mem Hi1 x2) (perm_mem Hi2 x1).
case Hx1: (x1 \in inorder t); case Hx2: (x2 \in inorder t).
- apply: (perm_trans Hi1); rewrite Hx1 perm_sym.
  by apply: (perm_trans Hi2); rewrite Hx2.
- rewrite inE Hx1 orbT perm_sym.
  apply: (perm_trans Hi2); rewrite Hx2 perm_cons perm_sym.
  by apply: (perm_trans Hi1); rewrite Hx1.
- rewrite Hx1 inE Hx2 orbT.
  apply: (perm_trans Hi1); rewrite Hx1 perm_cons perm_sym.
  by apply: (perm_trans Hi2); rewrite Hx2.
rewrite !inE Hx2 Hx1 !orbF; case: ifP.
- by move/eqP=>->; rewrite eq_refl.
rewrite eq_sym =>->.
move: Hi1; rewrite -(perm_cons x2) Hx1=>H'; apply: (perm_trans H').
rewrite -cat1s -(cat1s x1) perm_catCA /= perm_cons perm_sym.
by apply: (perm_trans Hi2); rewrite Hx2.
Qed.

(* Moreover, such representations are equal *)
Corollary insert_insert x1 x2 (t : tree T) :
            bst t ->
            inorder (insert x1 (insert x2 t)) = inorder (insert x2 (insert x1 t)).
Proof.
move=>H; apply: ord_sorted_eq.
- by rewrite -bst_to_sorted; do 2!apply: bst_insert.
- by rewrite -bst_to_sorted; do 2!apply: bst_insert.
by apply/perm_mem/insert_insert_perm.
Qed.

(* Lookup in the tree is equivalent to lookup in the in-order *)
Lemma inorder_search (t : tree T) :
        bst t ->
        search t =i inorder t.
Proof.
move=>+ x; elim: t=>//=l IHl a r IHr /and4P [Hal Har /IHl Hl /IHr Hr] {IHl IHr}.
rewrite -topredE /= in Hl; rewrite -topredE /= in Hr.
rewrite -topredE /= mem_cat inE {}Hl {}Hr.
case: ifP=>_ /=; first by rewrite orbT.
case: ifP=>Hx.
- suff: x \notin inorder r by move/negbTE=>->/=; rewrite orbF.
  by apply: (all_notin Har); apply/negP/nsym.
suff: x \notin inorder l by move/negbTE=>->.
by apply: (all_notin Hal)=>/=; rewrite Hx.
Qed.

(* Pointer-based procedures *)

Opaque mknode.

(* Inserting into the BST *)

Definition inserttreeT x : Type :=
  forall p,
    {t : tree T}, STsep (shape p t,
                        [vfun p' => shape p' (insert x t)]).

Program Definition inserttree x : inserttreeT x :=
  Fix (fun (go : inserttreeT x) p =>
    Do (if p == null
          then n <-- mknode x;
               ret n
          else a <-- !(p.+ 1);
               if x == a then ret p
                 else if ord x a
                   then l <-- !p;
                        l' <-- go l;
                        p ::= l';;
                        ret p
                   else r <-- !(p.+ 2);
                        r' <-- go r;
                        p.+ 2 ::= r';;
                        ret p)).
Next Obligation.
(* pull out ghost + precondition, branch on null check *)
move=>x go p [t][] i /= H; case: eqP H=>[{p}->|/eqP E] H.
- (* the tree is empty, make a new node *)
  apply: vrfV=>V; case: (shape_null V H)=>{t H}->{i V}->.
  by apply: [stepE]=>// n m H; step.
(* the tree is a node, deconstruct it *)
case: (shape_cont E H)=>l[z][r][pl][pr][_][{t H}->{i}->][hl][hr][-> Hl Hr].
(* read the value, if the element is equal to it, just exit *)
(* the tree shouldn't have duplicates *)
step; case: eqP=>_; first by step; vauto.
(* branch on comparison, read corresponding pointer *)
case: ifP=>Ho; step.
- (* insert in the left branch, update the left pointer *)
  apply: [stepX l]@hl=>//= p' h' H'.
  by do 2!step; vauto.
(* insert in the right branch, update the right pointer *)
apply: [stepX r]@hr=>//= p' h' H'.
by do 2!step; vauto.
Qed.

(* Lookup in the BST *)

(* lopp invariant: the tree is unchanged, return true if the element is found *)
Definition searchtreeT x : Type :=
  forall p,
    {t : tree T}, STsep (shape p t,
                        [vfun b h => shape p t h /\ b == search t x]).

Program Definition searchtree x : searchtreeT x :=
  Fix (fun (go : searchtreeT x) p =>
    Do (if p == null
          then ret false
          else a <-- !(p.+ 1);
               if x == a then ret true
                 else if ord x a
                   then l <-- !p;
                        go l
                   else r <-- !(p.+ 2);
                        go r)).
Next Obligation.
(* pull out ghost + precondition, branch on null check *)
move=>x go p [t][] i /= H; case: eqP H=>[{p}->|/eqP E] H.
- (* tree is empty, it can't contain anything *)
  by apply: vrfV=>V; case: (shape_null V H)=>{t H}->{i V}->; step.
(* the tree is a node, deconstruct it *)
case: (shape_cont E H)=>l[z][r][pl][pr][_][{t H}->{i}->][hl][hr][-> Hl Hr].
(* read the value, compare it to the element, return true if it matches *)
step; case: eqP=>_; first by step; vauto.
(* branch on comparison, read corresponding pointer *)
case: ifP=>Ho; step.
- (* loop on the left branch *)
  by apply: [gX l]@hl=>//= b h' [H' E'] _; vauto.
(* loop on the right branch *)
by apply: [gX r]@hr=>//= b h' [H' E'] _; vauto.
Qed.

(* test that the API is consistent, i.e. BST invariant is preserved *)
(* and lookup finds previously inserted elements *)
Program Definition test p x1 x2 :
  {t : tree T}, STsep (fun h => shape p t h /\ bst t,
                       [vfun (pb : ptr * bool) h =>
                         let t' := insert x2 (insert x1 t) in
                         [/\ shape pb.1 t' h, bst t' & pb.2]]) :=
  Do (p1 <-- inserttree x1 p;
      p2 <-- inserttree x2 p1;
      b <-- searchtree x1 p2;
      ret (p2, b)).
Next Obligation.
(* pull out ghost + precondition *)
move=>p x1 x2 [t][] i /= [Ht Hi].
(* run the subroutines, return the final tree and the lookup result *)
apply: [stepE t]=>//= {p i Ht} p1 h1 H1.
apply: [stepE (insert x1 t)]=>//= {p1 h1 H1} p2 h2 H2.
apply: [stepE (insert x2 (insert x1 t))]=>//= {h2 H2} b h3 [H3 /eqP Hb].
step=>_.
(* insertions preserve the invariant *)
have Hi2: bst (insert x2 t) by apply: bst_insert.
have Hi21: bst (insert x2 (insert x1 t)) by do 2!apply: bst_insert.
(* at this point we're done with the separation logic part, i.e. the mutable state *)
(* the only non-trivial goal remaining is search being consistent with insert *)
split=>//{p2 h3 H3}; rewrite {b}Hb.
(* switch to in-order lookup *)
move: (inorder_search Hi21 x1); rewrite -topredE /= =>->.
(* use the insertion commutativity, unroll the insertion spec *)
rewrite (insert_insert _ _ Hi) (perm_mem (inorder_insert x1 Hi2) x1).
(* the goal is now trivially solved by case *)
by case: ifP=>// _; rewrite inE eq_refl.
Qed.

End BST.
