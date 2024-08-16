(*
Copyright 2010 IMDEA Software Institute
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype tuple finfun finset.
From pcm Require Import options axioms prelude pred.
From pcm Require Import pcm unionmap heap.
From htt Require Import options model heapauto.

(*********************************)
(* Arrays indexed by finite type *)
(*********************************)

(* array is (pointer to) a contiguous memory region *)
(* holding the array values *)

Record array (I : finType) (T : Type) : Set := Array {orig :> ptr}.
Arguments Array {I T}.

Definition array_for (I : finType) (T : Type) of phant (I -> T) := array I T.
Identity Coercion array_for_array : array_for >-> array.
Notation "{ 'array' aT }" := (array_for (Phant aT))
  (at level 0, format "{ 'array'  '[hv' aT ']' }") : type_scope.

Module Type ArraySig.
Parameter shape : forall {I : finType} {T : Type}, 
  {array I -> T} -> {ffun I -> T} -> Pred heap.

(* build new array with all cells initialized to x *)
Parameter new : forall {I : finType} {T : Type} (x : T),
  STsep (emp, [vfun (a : {array I -> T}) h => h \In shape a [ffun => x]]).

(* build new array with cells initialized by finite function f *)
Parameter newf : forall {I : finType} {T : Type} (f : {ffun I -> T}),
  STsep (emp, [vfun a h => h \In shape a f]).

(* free the array *)
Parameter free : forall {I : finType} {T : Type} (a : {array I -> T}),
  STsep (fun i => exists f, i \In shape a f, [vfun _ : unit => emp]).

(* read k-th cell *)
Parameter read : forall {I : finType} {T : Type} (a : {array I -> T}) (k : I),
   STsep {f h} (fun i => i = h /\ i \In shape a f,
               [vfun (y : T) m => m = h /\ y = f k]).

(* write k-th cell *)
Parameter write : forall {I : finType} {T : Type} (a : {array I -> T}) k x,
  STsep {f} (shape a f,
            [vfun (_ : unit) h => h \In shape a (finfun [eta f with k |-> x])]).
End ArraySig.


Module Array : ArraySig.
Section Array.
Context {I : finType} {T : Type}.
Notation array := {array I -> T}.

(* array is specified by finite function *)
Definition shape (a : array) (f : {ffun I -> T}) : Pred heap :=
  [Pred h | h = updi a (fgraph f)].

(* main methods *)

(* new empty array preallocates all cells for all possible index values *)
(* initializing all of them to `x` *)
Program Definition new (x : T) :
  STsep (emp, [vfun a => shape a [ffun => x]]) :=
  Do (x <-- allocb x #|I|;
      ret (Array x)).
Next Obligation.
(* pull out ghost vars, run the program *)
move=>x [] _ /= ->; step=>y; step.
(* simplify *)
rewrite unitR=>_; congr updi; rewrite /= codomE cardE.
by elim: (enum I)=>[|t ts] //= ->; rewrite (ffunE _ _).
Qed.

(* new array corresponding to a domain of a finite function f *)

(* loop invariant: *)
(* partially filled array corresponds to finite function g *)
(* acting as prefix of f *)
Definition fill_loop a (f : {ffun I -> T}) : Type :=
  forall s : seq I, STsep (fun i => exists g s',
                                      [/\ i \In shape a g,
                                          s' ++ s = enum I &
                                          forall x, x \in s' -> g x = f x],
                          [vfun a => shape a f]).

Program Definition newf (f : {ffun I -> T}) :
  STsep (emp, [vfun a => shape a f]) :=
  (* `return` helps to avoid extra obligations *)
  (* test I for emptiness *)
  Do (if [pick x in I] is Some v return _ then
        (* preallocate a new array *)
        x <-- new (f v);
        (* fill it with values of f on I *)
        let fill := ffix (fun (loop : fill_loop x f) s =>
          Do (if s is k::t return _ then
                x .+ (indx k) ::= f k;;
                loop t
              else ret x))
        in fill (enum I)
      else ret (Array null)).
(* first the loop *)
Next Obligation.
(* pull out preconditions (note that there are no ghost vars), split *)
move=>f v x loop s [] /= _ [g][s'][->]; case: s=>[|k t] /= H1 H2.
- (* we've reached the end, return the array *)
  (* g spans the whole f *)
  rewrite cats0 in H1; step=>_; rewrite (_ : g = f) // -ffunP=>y.
  by apply: H2; rewrite H1 mem_enum.
(* run the loop iteration, split the heap and save its validity *)
rewrite (updi_split x k); step; apply: vrfV=>V; apply: [gE]=>//=.
(* add the new index+value to g *)
exists (finfun [eta g with k |-> f k]), (s' ++ [:: k]).
(* massage the heap, simplify *)
rewrite /shape (updi_split x k) takeord dropord (ffunE _ _) /= eq_refl -catA.
split=>// y; rewrite ffunE /= mem_cat inE /=.
(* the new g is still a prefix of f *)
by case: eqP=>[->|_] //; rewrite orbF; apply: H2.
Qed.
(* now the outer program *)
Next Obligation.
(* pull out params, check if I is empty *)
move=>f [] _ ->; case: fintype.pickP=>[v|] H /=.
- (* run the `new` subroutine, simplify *)
  apply: [stepE]=>//= a _ ->.
  (* invoke the loop, construct g from the first value of f *)
  by apply: [gE]=>//=; exists [ffun => f v], nil.
(* I is empty, so should be the resulting heap *)
step; rewrite /shape /= codom_ffun.
suff L: #|I| = 0 by case: (fgraph f)=>/=; rewrite L; case.
by rewrite cardE; case: (enum I)=>[|x s] //; move: (H x).
Qed.

(* freeing an array by deallocating all of its cells *)

(* the loop invariant: *)
(* a partially freed array still contains valid #|I| - k cells *)
(* corresponding to some suffix xs of the original array's spec *)
Definition free_loop (a : ptr) : Type :=
  forall k, STsep (fun i => exists xs: seq T,
                            [/\ i = updi (a .+ k) xs,
                                valid i &
                                size xs + k = #|I|],
                  [vfun _ : unit => emp]).

Program Definition free (a : array) :
  STsep (fun i => exists f, i \In shape a f,
        [vfun _ : unit => emp]) :=
  Do (let go := ffix (fun (loop : free_loop a) k =>
                   Do (if k == #|I| then ret tt
                       else dealloc a.+k;;
                            loop k.+1))
      in go 0).
(* first the loop *)
Next Obligation.
(* pull out params, if the remaining suffix xs is empty, we're done *)
move=>a loop k [] i /= [[|v xs]][->] /= _; first by rewrite add0n=>/eqP ->; step.
(* the suffix is non-empty so k < #|I| *)
case: eqP=>[->|_ H]; first by move/eqP; rewrite -{2}(add0n #|I|) eqn_add2r.
(* run the program, simplify *)
step; apply: vrfV=>V; apply: [gE]=>//=; exists xs.
by rewrite V unitL -addSnnS H -addnS. 
Qed.
(* now the outer program *)
Next Obligation.
(* pull out params, invoke the loop *)
move=>a [] /= _ [f ->]; apply: vrfV=>V; apply: [gE]=>//=.
(* the suffix xs is the whole codomain of f *)
exists (tval (fgraph f))=>/=.
by rewrite ptr0 V {3}codomE size_map -cardE addn0.
Qed.

(* reading from an array, doesn't modify the heap *)
Program Definition read (a : array) (k : I) :
   STsep {f h} (fun i => i = h /\ i \In shape a f,
               [vfun (y : T) m => m = h /\ y = f k]) :=
  Do (!a .+ (indx k)).
Next Obligation.
(* pull out ghost vars *)
move=>a k [f][_][] _ [->->].
(* split the heap and run the program *)
by rewrite (updi_split a k); step.
Qed.

(* writing to an array, updates the spec function with a new value *)
Program Definition write (a : array) (k : I) (x : T) :
  STsep {f} (shape a f,
            [vfun _ : unit => shape a (finfun [eta f with k |-> x])]) :=
  Do (a .+ (indx k) ::= x).
Next Obligation.
(* pull out ghost vars, split the heap *)
move=>a k x [f][] _ -> /=; rewrite /shape !(updi_split a k).
(* run the program, simplify *)
by step; rewrite takeord dropord ffunE /= eq_refl.
Qed.

End Array.
End Array.


(* Tabulating a finite function over another one *)
(* Useful in building linked data structures that are pointed to by *)
(* array elements, such as hashtables *)

Section Table.
Variables (I : finType) (T S : Type) (x : ptr)
          (Ps : T -> S -> Pred heap).

Definition table (t : I -> T) (b : I -> S) (i : I) : Pred heap :=
  Ps (t i) (b i).

Lemma tableP (s : {set I}) t1 t2 b1 b2 h :
        (forall x, x \in s -> t1 x = t2 x) ->
        (forall x, x \in s -> b1 x = b2 x) ->
        h \In sepit s (table t1 b1) -> 
        h \In sepit s (table t2 b2).
Proof.
move=>H1 H2 H.
apply/(sepitF (f1 := table t1 b1))=>//.
by move=>y R; rewrite /table (H1 _ R) (H2 _ R).
Qed.

Lemma tableP2 (s1 s2 : {set I}) t1 t2 b1 b2 h :
        s1 =i s2 ->
        (forall x, s1 =i s2 -> x \in s1 -> t1 x = t2 x) ->
        (forall x, s1 =i s2 -> x \in s1 -> b1 x = b2 x) ->
        h \In sepit s1 (table t1 b1) -> 
        h \In sepit s2 (table t2 b2).
Proof.
move=>H1 H2 H3; rewrite (eq_sepit _ H1).
by apply: tableP=>y; rewrite -H1=>R; [apply: H2 | apply: H3].
Qed.

End Table.

Prenex Implicits table.
