From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype tuple finfun finset.
From pcm Require Import options axioms prelude pred.
From pcm Require Import pcm unionmap heap.
From htt Require Import options model heapauto.

Definition indx {I : finType} (x : I) := index x (enum I).

Prenex Implicits indx.

(***********************************)
(* Arrays indexed by a finite type *)
(***********************************)

(* an array is a pointer to a contiguous memory region holding its values *)

Record array (I : finType) (T : Type) : Type := Array {orig :> ptr}.
Arguments Array [I T].

Definition array_for (I : finType) (T : Type) of phant (I -> T) := array I T.
Identity Coercion array_for_array : array_for >-> array.
Notation "{ 'array' aT }" := (array_for (Phant aT))
  (at level 0, format "{ 'array'  '[hv' aT ']' }") : type_scope.

Module Array.
Section Array.
Variable (I : finType) (T : Type).
Notation array := {array I -> T}.

(* an array is specified by a finite function *)

Definition shape (a : array) (f : {ffun I -> T}) :=
  [Pred h | h = updi a (fgraph f) /\ valid h].

(*
(* helper lemmas *)

Lemma enum_split k :
        enum I = take (indx k) (enum I) ++ k :: drop (indx k).+1 (enum I).
Proof.
case: path.splitP; first by rewrite mem_enum.
by move=>p1 p2; rewrite -cats1 -catA.
Qed.

Lemma updi_split (a : array) k (f : {ffun I -> T}) :
        updi a (fgraph f) = updi a (take (indx k) (fgraph f)) \+
                            a.+(indx k) :-> f k \+
                            updi (a.+(indx k).+1) (drop (indx k).+1 (fgraph f)).
Proof.
rewrite fgraph_codom /= codomE {1}(enum_split k) map_cat updi_cat /=.
rewrite map_take map_drop size_takel ?joinA ?ptrA ?addn1 //.
by rewrite size_map index_size.
Qed.

Lemma takeord k x (f : {ffun I -> T}) :
        take (indx k) (fgraph [ffun y => [eta f with k |-> x] y]) =
        take (indx k) (fgraph f).
Proof.
set f' := (finfun _).
suff E: {in take (indx k) (enum I), f =1 f'}.
- by rewrite !fgraph_codom /= !codomE -2!map_take; move/eq_in_map: E.
move: (enum_uniq I); rewrite {1}(enum_split k) cat_uniq /= =>H4.
move=>y H5; rewrite /f' /= !ffunE /=; case: eqP H5 H4=>// -> ->.
by rewrite andbF.
Qed.

Lemma dropord k x (f : {ffun I -> T}) :
        drop (indx k).+1 (fgraph [ffun y => [eta f with k |->x] y]) =
        drop (indx k).+1 (fgraph f).
Proof.
set f' := (finfun _).
suff E: {in drop (indx k).+1 (enum I), f =1 f'}.
- by rewrite !fgraph_codom /= !codomE -2!map_drop; move/eq_in_map: E.
move: (enum_uniq I); rewrite {1}(enum_split k) cat_uniq /= => H4.
move=>y H5; rewrite /f' /= !ffunE /=; case: eqP H5 H4=>// -> ->.
by rewrite !andbF.
Qed.
*)
(* main methods *)

(* a new empty array preallocates all cells for all possible index values *)
(* initializing all of them to `x` *)

Program Definition new (x : T) :
  STsep (emp, [vfun a => shape a [ffun => x]]) :=
  Do (x <-- allocb x #|I|;
      ret (Array x)).
Next Obligation.
(* pull out ghost vars, run the program *)
move=>x [] _ /= ->; step=>y; step.
(* simplify *)
rewrite unitR=>H; split=>//; congr updi; rewrite codomE cardE.
by elim: (enum I)=>[|t ts] //= ->; rewrite (ffunE _ _).
Qed.

Opaque new.

(* a new array corresponding to a domain of a finite function f *)

(* the loop invariant: *)
(* a partially filled array corresponds to some finite function g acting as a prefix of f *)
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
        let fill := Fix (fun (loop : fill_loop x f) s =>
                      Do (if s is k::t return _ then
                             x .+ (indx k) ::= f k;;
                             loop t
                          else ret (Array x)))
        in fill (enum I)
      else ret (Array null)).
(* first the loop *)
Next Obligation.
(* pull out preconditions (note that there are no ghost vars), split *)
move=>f v x loop s [] /= _ [g][s'][[-> _]]; case: s=>[|k t] /= H1 H2.
- (* we've reached the end, return the array *)
  rewrite cats0 in H1; step=>H; split=>//.
  (* g spans the whole f *)
  by rewrite (_ : g = f) // -ffunP=>y; apply: H2; rewrite H1 mem_enum.
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
  apply: [stepE]=>//= a _ [-> V].
  (* invoke the loop, construct g from the first value of f *)
  by apply: [gE]=>//=; exists [ffun => f v], nil.
(* I is empty, so should be the resulting heap *)
step=>_; split=>//; rewrite codom_ffun.
suff L: #|I| = 0 by case: (fgraph f)=>/=; rewrite L; case.
by rewrite cardE; case: (enum I)=>[|x s] //; move: (H x).
Qed.

(* freeing an array by deallocating all of its cells *)

(* the loop invariant: *)
(* a partially freed array still contains valid #|I| - k cells *)
(* corresponding to some suffix xs of the original array's spec *)
Definition free_loop (a : array) : Type :=
  forall k, STsep (fun i => exists xs: seq T,
                            [/\ i = updi (a .+ k) xs,
                                valid i &
                                size xs + k = #|I|],
                   [vfun _ : unit => emp]).

Program Definition free (a : array) :
  STsep (fun i => exists f, i \In shape a f,
         [vfun _ : unit => emp]) :=
  Do (let go := Fix (fun (loop : free_loop a) k =>
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
step; apply: vrfV=>V; apply: [gE]=>//=.
by exists xs; rewrite V ptrA addn1 -addSnnS unitL.
Qed.
(* now the outer program *)
Next Obligation.
(* pull out params, invoke the loop *)
move=>a [] /= _ [f][-> V]; apply: [gE]=>//=.
(* the suffix xs is the whole codomain of f *)
exists (tval (fgraph f))=>/=.
by rewrite ptr0 V {3}codomE size_map -cardE addn0.
Qed.

(* reading from an array, doesn't modify the heap *)

Program Definition read (a : array) (k : I) :
   {f h}, STsep (fun i => i = h /\ i \In shape a f,
                 [vfun (y : T) m => m = h /\ y = f k]) :=
  Do (!a .+ (indx k)).
Next Obligation.
(* pull out ghost vars *)
move=>a k [f][_][] _ [->][/= -> _].
(* split the heap and run the program *)
by rewrite (updi_split a k); step.
Qed.

(* writing to an array, updates the spec function with a new value *)

Program Definition write (a : array) (k : I) (x : T) :
  {f}, STsep (shape a f,
              [vfun _ : unit => shape a (finfun [eta f with k |-> x])]) :=
  Do (a .+ (indx k) ::= x).
Next Obligation.
(* pull out ghost vars, split the heap *)
move=>a k x [f][] _ [-> _] /=; rewrite /shape !(updi_split a k).
(* run the program, simplify *)
by step; rewrite takeord dropord ffunE /= eq_refl.
Qed.

End Array.
End Array.

(* Tabulating a finite function over another one *)
(* Useful in building linked data structures that are pointed to by *)
(* array elements, such as hashtables *)

Section Table.

Variables (I : finType) (T S : Type) (x : {array I -> T})
          (Ps : T -> S -> Pred heap).

Definition table (t : I -> T) (b : I -> S) (i : I) : Pred heap :=
  Ps (t i) (b i).

Lemma tableP (s : {set I}) t1 t2 b1 b2 h :
        (forall x, x \in s -> t1 x = t2 x) ->
        (forall x, x \in s -> b1 x = b2 x) ->
        h \In sepit s (table t1 b1) -> h \In sepit s (table t2 b2).
Proof.
move=>H1 H2 H.
apply/(sepitF (f1 := table t1 b1))=>//.
by move=>y R; rewrite /table (H1 _ R) (H2 _ R).
Qed.

Lemma tableP2 (s1 s2 : {set I}) t1 t2 b1 b2 h :
        s1 =i s2 ->
        (forall x, s1 =i s2 -> x \in s1 -> t1 x = t2 x) ->
        (forall x, s1 =i s2 -> x \in s1 -> b1 x = b2 x) ->
        h \In sepit s1 (table t1 b1) -> h \In sepit s2 (table t2 b2).
Proof.
move=>H1 H2 H3; rewrite (eq_sepit _ H1).
by apply: tableP=>y; rewrite -H1=>R; [apply: H2 | apply: H3].
Qed.

End Table.

Prenex Implicits table.
