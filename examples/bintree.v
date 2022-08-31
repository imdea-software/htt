
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq ssrnat.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap autopcm automap.
From HTT Require Import model heapauto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

(* Binary trees *)

Inductive tree A := Leaf | Node of (tree A) & A & (tree A).

Fixpoint size_tree {A} (t : tree A) : nat :=
  if t is Node l _ r
    then size_tree l + size_tree r + 1
  else 0.

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
                                ls <-- go(l, s);
                                go (r, ls + 1)))
      in len (p, 0)).
Next Obligation.
move=>_ go _ p s /= _ [t][] i /= H; case: eqP H=>[->|/eqP Ep] H.
- by step=>V; case: (treep_null V H)=>->->/=; rewrite addn0.
case: (treep_cont Ep H)=>l[a][r][l'][r'][_][{t H}-> {i}-> [hl][hr][-> Hl Hr]] /=.
do 2!step.
apply: [stepX l]@hl=>//= _ hl' [/eqP -> Hl'].
apply: [gX r]@hr=>//= _ hr' [/eqP -> Hr'] V.
split; first by rewrite -!addnA 2!eqn_add2l addnC.
exists l', r', (hl' \+ hr'); split=>//.
by exists hl', hr'.
Qed.
Next Obligation.
by move=>/= p [t][] i /= H; apply: [gE t].
Qed.

End Tree.
