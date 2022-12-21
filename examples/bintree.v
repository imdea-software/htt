
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq ssrnat.
From pcm Require Import options axioms pred.
From pcm Require Import pcm unionmap heap autopcm automap.
From htt Require Import options model heapauto.
From htt Require Import llist.

(* Binary tree specification *)

Inductive tree A := Leaf | Node of tree A & A & tree A.

Definition leaf {A} : tree A := @Leaf A.

Fixpoint size_tree {A} (t : tree A) : nat :=
  if t is Node l _ r
    then (size_tree l + size_tree r).+1
  else 0.

Fixpoint inorder {A} (t : tree A) : seq A :=
  if t is Node l x r
    then inorder l ++ x :: inorder r
  else [::].

(* Add an element to the rightmost branch *)

Fixpoint addr {A} (y : A) (t : tree A) : tree A :=
  if t is Node l x r
    then Node l x (addr y r)
  else Node leaf y leaf.

(* Tree heap predicate: [left branch pointer, value, right branch pointer] *)

Fixpoint shape {A} (p : ptr) (t : tree A) :=
  if t is Node l a r then
    [Pred h | exists l' r' h',
          h = p :-> l' \+ (p .+ 1 :-> a \+ (p .+ 2 :-> r' \+ h'))
       /\ h' \In shape l' l # shape r' r]
  else [Pred h | p = null /\ h = Unit].

(* Null pointer represents a leaf *)

Lemma shape_null {A} (t : tree A) h :
        valid h -> h \In shape null t ->
        t = leaf /\ h = Unit.
Proof.
move=>V; case: t=>/= [|l a r]; first by case=>_->.
by case=>?[?][?][E]; rewrite E validPtUn in V.
Qed.

(* Non-null pointer represents a node *)

Lemma shape_cont {A} (t : tree A) p h :
        p != null -> h \In shape p t ->
        exists l a r l' r' h',
         [/\ t = Node l a r,
             h = p :-> l' \+ (p .+ 1 :-> a \+ (p .+ 2 :-> r' \+ h'))
           & h' \In shape l' l # shape r' r].
Proof.
move=>E; case: t=>/= [|l a r].
- by case=>E0; rewrite E0 in E.
case=>l'[r'][h'][E1 E2].
by exists l,a,r,l',r',h'.
Qed.

Section Tree.
Variable A : Type.

(* Node creation *)

Program Definition mknode (x : A) :
  STsep (emp,
        [vfun p => shape p (Node leaf x leaf)]) :=
  Do (n <-- allocb null 3;
      n.+ 1 ::= x;;
      ret n).
Next Obligation.
(* the starting heap is empty *)
move=>x [] _ /= ->.
(* run all the steps *)
step=>n; rewrite !unitR ptrA; step; step=>_.
(* the postcondition is satisfied *)
by exists null, null, Unit; vauto; rewrite unitR.
Qed.

(* Recursive tree disposal *)

(* We start from a well-formed tree and arrive at an empty heap *)
Definition disposetreeT : Type :=
  forall p, {t : tree A}, STsep (shape p t, [vfun _ : unit => emp]).

Program Definition disposetree : disposetreeT :=
  Fix (fun (loop : disposetreeT) p =>
       Do (if p == null then ret tt
           else l <-- !p;
                r <-- !(p.+ 2);
                loop l;;
                loop r;;
                dealloc p;;
                dealloc p.+ 1;;
                dealloc p.+ 2
                )).
Next Obligation.
(* pull out ghost var + precondition, branch on null check *)
move=>loop p [t][] i /= H; case: eqP H=>[{p}->|/eqP E] H.
- (* null pointer is an empty tree, so the heap is empty *)
  by apply: vrfV=>V; step=>_; case: (shape_null V H).
(* non-null pointer is a node, deconstruct it, read branch pointers *)
case: (shape_cont E H)=>l[a][r][l'][r'][_][{t H E}_ {i}-> [hl][hr][-> Hl Hr]].
do 2!step.
(* recursive calls vacate left+right subheaps *)
apply: [stepX l]@hl=>//= _ _ ->; rewrite unitL.
apply: [stepX r]@hr=>//= _ _ ->; rewrite unitR.
(* deallocating the node vacates the remainder *)
by do 3!step; rewrite !unitL.
Qed.

(* Calculation of tree size *)

(* loop invariant: *)
(* the subtree size is added to the accumulator *)
Definition treesizeT : Type := forall (ps : ptr * nat),
  {t : tree A}, STsep (shape ps.1 t,
                      [vfun s h => s == ps.2 + size_tree t /\ shape ps.1 t h]).

Program Definition treesize p :
  {t : tree A}, STsep (shape p t,
                      [vfun s h => s == size_tree t /\ shape p t h]) :=
  Do (let len := Fix (fun (go : treesizeT) '(p, s) =>
                       Do (if p == null then ret s
                           else l <-- !p;
                                r <-- !(p.+ 2);
                                ls <-- go (l, s);
                                go (r, ls.+1)))
      in len (p, 0)).
Next Obligation.
(* pull out ghost var + precondition, branch on null check *)
move=>_ go _ p s /= [t][] i /= H; case: eqP H=>[{p}->|/eqP Ep] H.
- (* empty tree has size 0 *)
  by step=>V; case: (shape_null V H)=>->->/=; rewrite addn0.
(* non-null pointer is a node, deconstruct it, read branch pointers *)
  case: (shape_cont Ep H)=>l[a][r][l'][r'][_][{t H}-> {i}-> [hl][hr][-> Hl Hr]] /=.
do 2!step.
(* calculate left branch size, update the accumulator *)
apply: [stepX l]@hl=>//= _ hl' [/eqP -> Hl'].
(* add 1 to accumulator and calculate right branch size *)
apply: [gX r]@hr=>//= _ hr' [/eqP -> Hr'] _.
(* finish with simple arithmetic and heap manipulation *)
by split; [rewrite addnS addSn addnA | vauto].
Qed.
Next Obligation.
(* pull out ghost var + precondition, start the loop with empty accumulator *)
by move=>/= p [t][] i /= H; apply: [gE t].
Qed.

(* Tree in-order traversal, storing the values in a linked list *)

Opaque insert new.

(* loop invariant: *)
(* the subtree is unchanged, its values are prepended to the accumulator list *)
Definition inordertravT : Type := forall (ps : ptr * ptr),
  {(t : tree A) (l : seq A)},
     STsep (shape ps.1 t # lseq ps.2 l,
           [vfun s h => h \In shape ps.1 t # lseq s (inorder t ++ l)]).

Program Definition inordertrav p :
  {t : tree A}, STsep (shape p t,
                      [vfun s h => h \In shape p t # lseq s (inorder t)]) :=
  Do (let loop := Fix (fun (go : inordertravT) '(p, s) =>
                       Do (if p == null then ret s
                           else l <-- !p;
                                a <-- !(p.+ 1);
                                r <-- !(p.+ 2);
                                s1 <-- go (r, s);
                                s2 <-- insert s1 (a : A);
                                go (l, s2)))
      in n <-- new A;
         loop (p, n)).
Next Obligation.
(* pull out ghosts + precondition, deconstruct the heap, branch on null check *)
move=>_ go _ p s /= [t][xs][] _ /= [h1][h2][-> H1 H2].
case: eqP H1=>[{p}->|/eqP Ep] H1.
- (* return the accumulated list - empty tree has no values *)
  by step=>V; case: (shape_null (validL V) H1)=>->->/=; vauto.
(* non-empty tree is a node, deconstruct the node, read the pointers and the value *)
case: (shape_cont Ep H1)=>l[a][r][l'][r'][_][{t H1}-> {h1}-> [hl][hr][-> Hl Hr]] /=.
do 3!step.
(* run traversal on the right branch first (it's cheaper to grow a linked list to the left) *)
apply: [stepX r, xs]@(hr \+ h2)=>//=; first by vauto.
(* we have subheaps corresponding to the left+right branches and the updated list *)
move=>s1 _ [hr'][hs][-> Hr' Hs].
(* prepend the node value to the list *)
apply: [stepX (inorder r ++ xs)]@hs=>//= pa _ [s2][h'][-> H'].
(* run the traversal on the left branch with updated list *)
apply: [gX l, (a::inorder r ++ xs)]@(hl \+ pa :-> a \+ pa.+ 1 :-> s2 \+ h')=>//=.
- (* the precondition is satisfied by simple heap manipulation *)
  move=>_; exists hl, (pa :-> a \+ (pa.+ 1 :-> s2 \+ h')).
  by split=>//=; [rewrite !joinA | vauto].
(* the postcondition is also satisfied by simple massaging *)
move=>s3 _ [hl''][hs'][-> Hl'' Hs'] _.
exists (p :-> l' \+ (p.+ 1 :-> a \+ (p.+ 2 :-> r' \+ (hl'' \+ hr')))), hs'.
split; try by hhauto.
by rewrite -catA.
Qed.
Next Obligation.
(* pull out ghost var + precondition *)
move=>/= p [t][] i /= H.
(* make an empty list by framing on Unit *)
(* this just sets n to null, but we stick to the list API *)
apply: [stepU]=>//= _ _ [->->]; rewrite unitL.
(* start the loop, conditions are satisfied by simple massaging *)
apply: [gE t, [::]]=>//=.
- by exists i, Unit; split=>//; rewrite unitR.
by move=>s m; rewrite cats0.
Qed.

(* Expanding the tree to the right *)

Opaque mknode.

(* loop invariant: the value is added to the rightmost branch *)
Definition expandrightT x : Type := forall (p : ptr),
  {t : tree A}, STsep (shape p t,
                      [vfun p' => shape p' (addr x t)]).

Program Definition expandright x : expandrightT x :=
  Fix (fun (go : expandrightT x) p =>
      Do (if p == null
            then n <-- mknode x;
                 ret n
          else pr <-- !(p.+ 2);
               p' <-- go pr;
               p.+ 2 ::= p';;
               ret p)).
Next Obligation.
(* pull out ghost + precondition, branch on null check *)
move=>x go p [t []] i /= H; case: eqP H=>[{p}->|/eqP Ep] H.
- (* tree is empty, make a new node and return it *)
  apply: vrfV=>V; case: (shape_null V H)=>{t H}->{i V}->.
  by apply: [stepE]=>//= n m H; step.
(* tree is non-empty, i.e. a node, deconstruct it *)
case: (shape_cont Ep H)=>l[z][r][pl][pr][_][{t H}->{i}->][hl][hr][-> Hl Hr].
(* run the rest of the program on the right branch + subheap *)
by step; apply: [stepX r]@hr=>//= p' h' H'; do 2!step; vauto.
Qed.

End Tree.
