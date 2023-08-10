From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
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

(*
move=>i [alpha0][h /= H]; set f := Fix _; simpl in f.
apply: [gE alpha0, nil]=>/=. 
- by eexists h, Unit; rewrite unitR.  
- by rewrite /rev.
by [].
Qed.
*)

End MarktoberdorfDemo1.


Module MarktoberdorfDemo2.
Section MarktoberdorfDemo2.

Inductive tp := 
  pair inv of {v : nat}, STsep (inv v, 
                                [vfun r h => r = v.+1 /\ inv r h]).

Definition inv x := let 'pair inv _ := x in inv.

Definition code x := 
  let 'pair _ comp := x 
    return {v : nat}, STsep (inv x v, 
       [vfun r h => r = v.+1 /\ inv x r h])
  in comp.

Program Definition fetch_add (x : ptr) : 
  {v : nat}, STsep (fun h => h = x :-> v, 
                   [vfun r h => r = v.+1 /\ h = x :-> r]) := 
  Do (z <-- !x;
      x ::= z.+1;;
      ret (z.+1)).
Next Obligation. by move=>x [v][_] -> /=; do !step. Qed.

Program Definition alloc_fetch_add : 
  STsep (emp, [vfun r => inv r 0]) := 
  Do (x <-- alloc 0;
      ret (pair (fetch_add x))).
Next Obligation.
by case=>_ -> /=; apply: vrf_bind; step=>x _; step; rewrite unitR.
Qed.

Program Definition silly_client : 
  STsep (emp, [vfun r => inv r 3]) := 
  Do (x <-- alloc_fetch_add;  (* open invariant of alloc_fetch_add *)
      code x;;
      code x;;
      code x;; 
      ret x).                 (* close invariant back up *)
Next Obligation.
case=>_ ->; apply: vrf_bind; apply: [gE]=>//= [x i0 H _].
apply: vrf_bind; apply: [gE 0]=>//= _ i1 [->] {i0}H _.
apply: vrf_bind; apply: [gE 1]=>//= _ i2 [->] {i1}H _.
apply: vrf_bind; apply: [gE 2]=>//= _ i3 [->] {i2}H _.
by apply: vrf_ret.
Qed.

End MarktoberdorfDemo2.
End MarktoberdorfDemo2.



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


(* Examples from Ranjit Jhala's blog post *)

Section Ranjit.

(* we define a function that takes a number *)
(* and puts it in a list *)
Definition pos (x1 : nat) := [:: 0; x1]. 

(* And then we prove that the size of the list is two. *)
(* No proof is actually required if we work in a purely-functional manner *)
(* as Jhala advocates doing in Liquid Haskell. *)
(* The reason is that Coq can just compute with values *)
(* whereas Liquid Haskell doesn't seem to be able to do that. *)
Lemma test1 : forall x1, size (pos x1) = 2. Proof. by []. Qed.

(* If, however, we want to use Hoare-Floyd logic, as Dafny would *)
(* then we have an overhead of half a line. *)
(* The overhead arises because every proof has a preamble *)
(* that requires binding some heap variables (though this is automatable). *)
(* However, even such a proof is still shorter than Jhala's annotations *)
(* in Liquid Haskell. *)
Program Definition test2 (x1 : nat) :
  STsep (fun h => True, [vfun pos h => size pos = 2]) := 
    Do (let: pos := [:: 0; x1] in ret pos).
Next Obligation. by move=>??*; step. Qed.

(* The proof is also more general than his approach of annotating type constructors *)
(* with size information. For we can prove non-size properties if we wanted *)
(* whereas he can't, unless he re-annotates the constructors, which *)
(* may not be possible if the constructors are library code. *)
(* For example, we can assert and prove sortedness of pos *)
(* again with essentially no work. *)

Lemma test3 : forall x1, sorted leq (pos x1). Proof. by []. Qed.

Program Definition test4 (x1 : nat) : 
  STsep (fun h => True, [vfun pos h => sorted leq pos]) := 
    Do (let: pos := [:: 0; x1] in ret pos).
Next Obligation. by move=>??*; step. Qed.

End Ranjit.


