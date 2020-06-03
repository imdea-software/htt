
From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype.
From mathcomp.ssreflect
Require Import tuple finfun finset.
From fcsl
Require Import pred pcm unionmap heap.
From HTT
Require Import heaptac domain stmod stsep stlog stlogR.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section LList.

Variables (T S : Type).
Notation empty := Unit.
Notation map := seq.map.

(* Inductive definition of linked lists *)
Fixpoint llist (p : ptr) {A : Type}  (xs : seq A) := 
  if xs is x :: xt then 
    fun h => exists r h', 
        h = p :-> x \+ (p .+ 1 :-> r \+ h') /\ llist r xt h'
  else fun h => p = null /\ h = empty.

(******************************************************************)
(***********      Facts about linked lists       ******************)
(******************************************************************)

Lemma llist_null {A : Type} (xs : seq A) h : 
         valid h -> llist null xs h -> 
         [/\ xs = [::] & h = empty].
Proof.
case: xs=>[|x xs] D /= H; first by case: H.
by case: H D=>r [h'][->] _.
Qed. 

Lemma llist_pos {A : Type} (xs : seq A) p h : 
        p != null -> llist p xs h -> 
        exists x r h', 
         [/\ xs = x :: behead xs, p :-> x \+ (p .+ 1 :-> r \+ h') = h & 
             llist r (behead xs) h'].
Proof.
case: xs=>[|x xs] /= H []; last by move=>y [h'][->] H1; hhauto.
by move=>E; rewrite E eq_refl in H.
Qed.

(******************************************************************)

(* Type of recursive map *)
Definition llist_map_type (f : T -> S) :=
  forall (p : ptr),   
    {xs : seq T}, STsep (fun h => llist p xs h,
                         fun (_ : ans unit) h => llist p (map f xs) h).

Program Definition llist_map f : llist_map_type f := 
  Fix (fun (lmap : llist_map_type f) p => 
    Do (if p == null
        then ret tt 
        else t <-- !p;
             p ::= f t;;
             nxt <-- !p .+ 1;
             lmap nxt)).

Next Obligation.
(* Deconstruct the precondition *)
apply: ghR=>h xs P V.

(* Use if-rule *)
case: ifP=>[X|/negbT X].

(* 1. p == null ==> The list is empty. *)
by move/eqP: X=>Z; subst p; case: (llist_null V P)=>->->; heval.
  
(* 2. p != null => The list is non-empty. *)
case/(llist_pos X): P=>t [nxt][h'][->]Z/=P; subst h.
(* Decompose the list predicate *) 
rewrite joinA joinC in V *; heval.
apply: (gh_ex (behead xs)).
by apply: (@val_do _ _ _ h')=>//=_ h2 Q V'; rewrite joinC;
   exists nxt, h2; rewrite joinA. 
Qed.

End LList.
