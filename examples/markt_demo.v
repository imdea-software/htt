From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From pcm Require Import axioms pred.
From pcm Require Import pcm unionmap heap autopcm automap.
From htt Require Import options model heapauto.

Export Set Implicit Arguments.
Export Unset Strict Implicit.

(* Linked lists, storing a value and next pointer in consecutive locations. *)
(* We start with a more general "segment" definition, where the last node's *)
(* next pointer is an arbitrary q *)

Definition star {U : pcm} (P1 P2 : Pred U) := 
  [Pred s | exists s1 s2 : U, [/\ s = s1 \+ s2, s1 \In P1 & s2 \In P2]].

Notation "P '**' Q" := (star P Q)
  (at level 57, right associativity) : rel_scope.

Section MarktoberdorfDemo1.
Variable A : Type.

Fixpoint list (i : ptr) (xs : seq A) := 
  if xs is x::xs' then 
       [Pred h | exists k h', 
                 h = i :-> x \+ (i .+ 1 :-> k \+ h') /\ h' \In list k xs']
  else [Pred h | i = null /\ h = Unit].

(* null pointer represents empty list *)
Lemma list_nil (alpha : seq A) h :
        h \In list null alpha ->
        valid h -> 
        alpha = [::] /\ h = Unit.
Proof.
by case: alpha=>[[]|a alpha] //= [k][h'][->]; rewrite validPtUn.
Qed.

Lemma list_cons (alpha : seq A) i h :
        h \In list i alpha ->
        i != null -> 
        exists a k h',
          [/\ alpha = a :: behead alpha,
              h = i :-> a \+ (i .+ 1 :-> k \+ h') &
              h' \In list k (behead alpha)].
Proof. 
by case: alpha=>[[->]|a alpha] //= [k][h'][-> Hk]; exists a, k, h'.
Qed.

(* in-place reversal by pointer swinging *)

(* the loop invariant: *)
(* 1. the processed part (beta) and remaining part (alpha) don't overlap *)
(* 2. the result is reversal of remainder (alpha) ++ processed part (beta) *)
(* catrev alpha beta == rev alpha ++ beta *)

Definition revT : Type := forall p : ptr * ptr,
  {alpha beta : seq A}, STsep (list p.1 alpha ** list p.2 beta,
                              [vfun j h => h \In list j (catrev alpha beta)]).

Program Definition reverse i :
  {alpha0 : seq A}, STsep (list i alpha0, 
                           [vfun j h => h \In list j (rev alpha0)]) :=
  Do (let reverse := Fix (fun (go : revT) '(i, j) =>
                          Do (if i == null then ret j
                              else k <-- !i .+ 1;
                                   i .+ 1 ::= j;;
                                   go (k, i)))
      in reverse (i, null)).
(* the loop *)
Next Obligation. 
move=>_ go _ i j [alpha][beta][h][/= h1][h2][-> H1 H2]. 
case: (i =P null) H1=>[-> H|/eqP N].
- by apply: hstep=>/validL/(list_nil H) [->->]; rewrite unitL.
case/list_cons=>//= a [k][h'][->->] /= H'.
do !apply: hstep=>//=; apply: [gE (behead alpha), a::beta]=>//=.
by rewrite !(pull h') -!joinA; do ![eexists _, _; split].
Qed.
(* the outer call *)
Next Obligation.
move=>i [alpha0][h /= H]; apply: [gE alpha0, nil]=>//=. 
by eexists h, Unit; rewrite unitR. 
Qed.

End MarktoberdorfDemo1.


Module MarktoberdordDemo2.
Section MarktoberdorfDemo2.

Inductive tp := 
  pair inv of {v : nat}, STsep (inv v, 
                                [vfun r h => inv r h /\ r = v + 1]).

Definition inv x := let 'pair inv _ := x in inv.

Program Definition fetch_add (x : ptr) : 
  {v : nat}, STsep (fun h => h = x :-> v, 
                   [vfun r h => h = x :-> r /\ r = v + 1]) := 
  Do (z <-- !x;
      x ::= z + 1;;
      ret (z+1)).
Next Obligation. by move=>x [v][_] -> /=; do !step. Qed.

Program Definition alloc_fetch_add : 
  STsep (emp, [vfun r => inv r 0]) := 
  Do (x <-- alloc 0;
      ret (pair (fetch_add x))).
Next Obligation.
by case=>_ -> /=; apply: vrf_bind; step=>x _; step; rewrite unitR.
Qed.

End MarktoberdorfDemo2.
End MarktoberdordDemo2.

(* the same example done using sigma types *)

Module MarktoberdordDemo3.
Section MarktoberdorfDemo3.

Definition tp := 
  sigT (fun inv => {v : nat}, 
    STsep (inv v, [vfun r h => inv r h /\ r = v + 1])).

Definition inv (x : tp) := let 'existT y _ := x in y.

Program Definition alloc_fetch_add : STsep (emp, [vfun r => inv r 0]) := 
  Do (x <-- alloc 0;
      ret (existT _ (fun v h => h = x :-> v) 
             (Do (z <-- !x;
                 x ::= z + 1;;
                 ret (z + 1))))).
Next Obligation. by move=>x [v][_] -> /=; do !step. Qed.
Next Obligation.
by case=>_ -> /=; apply: vrf_bind; step=>x _; step; rewrite unitR.
Qed.

End MarktoberdorfDemo3.
End MarktoberdordDemo3.

