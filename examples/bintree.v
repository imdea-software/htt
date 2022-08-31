
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq ssrnat.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap autopcm automap.
From HTT Require Import model heapauto.
From HTT Require Import llist.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

(* Binary trees *)

Inductive tree A := Leaf | Node of (tree A) & A & (tree A).

Fixpoint size_tree {A} (t : tree A) : nat :=
  if t is Node l _ r
    then (size_tree l + size_tree r).+1
  else 0.

Fixpoint inorder {A} (t : tree A) : seq A :=
  if t is Node l x r
    then inorder l ++ x :: inorder r
  else [::].

(* Tree predicate *)

Fixpoint treep {A} (p : ptr) (t : tree A) :=
  if t is Node l a r then
    [Pred h | exists l' r' h',
          h = p :-> l' \+ (p .+ 1 :-> a \+ (p .+ 2 :-> r' \+ h'))
       /\ h' \In treep l' l # treep r' r]
  else [Pred h | p = null /\ h = Unit].

Lemma treep_null {A} (t : tree A) h :
  valid h -> h \In treep null t ->
  t = @Leaf A /\ h = Unit.
Proof.
move=>V; case: t=>/= [|l a r].
- by case=>_->.
by case=>?[?][?][E]; rewrite E validPtUn in V.
Qed.

Lemma treep_cont {A} (t : tree A) p h :
  p != null -> h \In treep p t ->
  exists l a r l' r' h',
   [/\ t = Node l a r,
       h = p :-> l' \+ (p .+ 1 :-> a \+ (p .+ 2 :-> r' \+ h'))
     & h' \In treep l' l # treep r' r].
Proof.
move=>E; case: t=>/= [|l a r].
- by case=>E0; rewrite E0 in E.
case=>l'[r'][h'][E1 E2].
by exists l,a,r,l',r',h'; split.
Qed.

Section Tree.
Variable A : Type.

(* Tree deletion *)

Definition disposetreeT : Type :=
  forall p, {t : tree A}, STsep (treep p t, [vfun _ : unit => emp]).

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
move=>loop p [t][] i /= H; case: eqP=>[|/eqP] E.
- by apply: vrfV=>D; step=>_; rewrite E in H; case: (treep_null D H).
case: (treep_cont E H)=>l[a][r][l'][r'][_][{t H E}_ {i}-> [hl][hr][-> Hl Hr]].
do 2!step.
apply: [stepX l]@hl=>//= _ _ ->; rewrite unitL.
apply: [stepX r]@hr=>//= _ _ ->; rewrite unitR.
by do 3!step; rewrite !unitL.
Qed.

(* Tree size *)

Definition treesizeT : Type := forall (ps : ptr * nat),
  {t : tree A}, STsep (treep ps.1 t,
                      [vfun s h => s == ps.2 + size_tree t /\ treep ps.1 t h]).

Program Definition treesize p :
  {t : tree A}, STsep (treep p t,
                      [vfun s h => s == size_tree t /\ treep p t h]) :=
  Do (let len := Fix (fun (go : treesizeT) '(p, s) =>
                       Do (if p == null then ret s
                           else l <-- !p;
                                r <-- !(p.+ 2);
                                ls <-- go (l, s);
                                go (r, ls + 1)))
      in len (p, 0)).
Next Obligation.
move=>_ go _ p s /= _ [t][] i /= H; case: eqP H=>[->|/eqP Ep] H.
- by step=>V; case: (treep_null V H)=>->->/=; rewrite addn0.
case: (treep_cont Ep H)=>l[a][r][l'][r'][_][{t H}-> {i}-> [hl][hr][-> Hl Hr]] /=.
do 2!step.
apply: [stepX l]@hl=>//= _ hl' [/eqP -> Hl'].
apply: [gX r]@hr=>//= _ hr' [/eqP -> Hr'] _.
split; first by rewrite -addnA add1n -addnA addnS.
by exists l', r', (hl' \+ hr'); split=>//; exists hl', hr'.
Qed.
Next Obligation.
by move=>/= p [t][] i /= H; apply: [gE t].
Qed.

(* Tree inorder traversal *)

Opaque insert new.

Definition inordertravT : Type := forall (ps : ptr * ptr),
  {(t : tree A) (l : seq A)},
     STsep (treep ps.1 t # lseq ps.2 l,
           [vfun s h => h \In treep ps.1 t # lseq s (inorder t ++ l)]).

Program Definition inordertrav p :
  {t : tree A}, STsep (treep p t,
                      [vfun s h => h \In treep p t # lseq s (inorder t)]) :=
  Do (let loop := Fix (fun (go : inordertravT) '(p, s) =>
                       Do (if p == null then ret s
                           else l <-- !p;
                                a <-- !(p.+ 1);
                                r <-- !(p.+ 2);
                                s1 <-- go (r, s);
                                s2 <-- @insert A s1 a;
                                go (l, s2)))
      in n <-- new A;
         loop (p, n)).
Next Obligation.
move=>_ go _ p s _ /= [t][xs][] _ /= [h1][h2][-> H1 H2].
case: eqP H1=>[->|/eqP Ep] H1.
- step=>V; case: (treep_null (validL V) H1)=>->->/=.
  by exists Unit, h2.
case: (treep_cont Ep H1)=>l[a][r][l'][r'][_][{t H1}-> {h1}-> [hl][hr][-> Hl Hr]] /=.
do 3!step.
apply: [stepX r, xs]@(hr \+ h2)=>//=; first by move=>_; exists hr, h2.
move=>s1 _ [hr'][hs][-> Hr' Hs].
apply: [stepX (inorder r ++ xs)]@hs=>//= pa _ [s2][h'][-> H'].
apply: [gX l, (a::inorder r ++ xs)]@(hl \+ pa :-> a \+ pa.+ 1 :-> s2 \+ h')=>//=.
- move=>_; exists hl, (pa :-> a \+ (pa.+ 1 :-> s2 \+ h')); split=>//=.
  - by rewrite !joinA.
  by rewrite /lseq /=; exists s2, h'.
move=>s3 _ [hl''][hs'][-> Hl'' Hs'] _.
exists (p :-> l' \+ (p.+ 1 :-> a \+ (p.+ 2 :-> r' \+ (hl'' \+ hr')))), hs'; split.
- by rewrite [RHS](pullX (hl'' \+ hs' \+ hr')) [LHS](pullX (hl'' \+ hs' \+ hr')).
- by exists l', r', (hl'' \+ hr'); split=>//; exists hl'', hr'.
by rewrite -catA.
Qed.
Next Obligation.
move=>/= p [t][] i /= H.
rewrite -(unitL i); apply: [stepR]@Unit=>//= _ _ [->->]; rewrite unitL.
apply: [gE t, [::]]=>/=.
- by exists i, Unit; split=>//; rewrite unitR.
by case=>//= s m _; rewrite cats0.
Qed.

End Tree.
