From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype tuple finfun finset.
From fcsl Require Import axioms prelude pred.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import domain heap_extra model heapauto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "None".
Obligation Tactic := auto.

Definition indx {I : finType} (x : I) := index x (enum I).

Prenex Implicits indx.

(***********************************)
(* Arrays indexed by a finite type *)
(***********************************)

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

Definition shape (a : array) (f : {ffun I -> T}) :=
  [Pred h | h = updi a (fgraph f) /\ valid h].

(* helper lemmas *)

Lemma enum_split k :
        enum I = take (indx k) (enum I) ++ k :: drop (indx k).+1 (enum I).
Proof.
rewrite -{2}(@nth_index I k k (enum I)) ?mem_enum //.
by rewrite -drop_nth ?index_mem ?mem_enum // cat_take_drop.
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

(* main methods *)

Program Definition new (x : T) : STsep (emp, [vfun y => shape y [ffun => x]]) :=
  Do (x <-- allocb x #|I|;
      ret (Array x)).
Next Obligation.
move=>x [] _ /= ->; step=>y; step.
rewrite unitR=>H; split=>//; congr updi.
rewrite ?fgraph_codom /= codomE cardE.
by elim: (enum I)=>[|t ts] //= ->; rewrite (ffunE _ _).
Qed.

Definition newf_loop a (f : {ffun I -> T}) : Type :=
  forall s : seq I, STsep (fun i => exists g s', [/\ i \In shape a g,
                                      s' ++ s = enum I &
                                      forall x, x \in s' -> g x = f x],
                           [vfun y => shape y f]).

Program Definition newf (f : {ffun I -> T}) :
  STsep (emp, [vfun y => shape y f]) :=
  Do (if [pick x in I] is Some v return _ then
        x <-- new (f v);
        let f := Fix (fun (loop : newf_loop x f) s =>
                   Do (if s is k::t return _ then
                          x .+ (indx k) ::= f k;;
                          loop t
                       else ret (Array x)))
        in f (enum I)
      else ret (Array null)).
Next Obligation.
move=>f v x loop s [] /= _ [g][s'][[-> _]]; case: s=>[|k t] /= H1 H2.
- rewrite cats0 in H1; step=>H; split=>//.
  by rewrite (_ : g = f) // -ffunP=>y; apply: H2; rewrite H1 mem_enum.
rewrite (updi_split x k); step; apply: vrfV=>V; apply: [gE]=>//=.
exists (finfun [eta g with k |-> f k]), (s' ++ [:: k]).
rewrite /shape (updi_split x k) takeord dropord (ffunE _ _) /= eq_refl -catA.
split=>// y; rewrite ffunE /= mem_cat inE /=.
by case: eqP=>[->|_] //; rewrite orbF; apply: H2.
Qed.
Next Obligation.
move=>f [] _ ->; case: fintype.pickP=>[v|] H /=.
- apply: vrf_bind=>/=; step=>x; rewrite unitR; step=>_ V.
  apply: [gE]=>//=; exists [ffun => f v], nil; do!split=>//=.
  congr updi; rewrite codomE cardE.
  by elim: (enum I)=>//= ?? ->/=; rewrite ffunE.
step=>_; split=>//; rewrite codom_ffun.
suff L: #|I| = 0 by case: (fgraph f)=>/=; rewrite L; case.
by rewrite cardE; case: (enum I)=>[|x s] //; move: (H x).
Qed.

Definition loop_inv (a : array) : Type :=
  forall k, STsep (fun i => exists xs:seq T, [/\ i = updi (a .+ k) xs, valid i &
                              size xs + k = #|I|],
                   [vfun _ : unit => emp]).

Program Definition free (a : array) :
    STsep (fun i => exists f, i \In shape a f, [vfun _ => emp]) :=
  Do (let: f := Fix (fun (f : loop_inv a) k =>
                  Do (if k == #|I| then ret tt
                      else
                        dealloc a.+k;;
                        f k.+1))
      in f 0).
Next Obligation.
move=>a f k [] i /= [[|v xs]][->] /= _; first by rewrite add0n=>/eqP ->; step.
case: eqP=>[->|_ H]; first by move/eqP; rewrite -{2}(add0n #|I|) eqn_add2r.
step; apply: vrfV=>V; apply: [gE]=>//=.
by exists xs; rewrite V ptrA addn1 -addSnnS unitL.
Qed.
Next Obligation.
move=>a [] /= _ [f][-> V]; apply: [gE]=>//=.
exists (tval (fgraph f))=>/=.
by rewrite ptr0 V {3}codomE size_map -cardE addn0.
Qed.

Program Definition read (a : array) (k : I) :
   {f h}, STsep (fun i => i = h /\ i \In shape a f,
                 [vfun y m => m = h /\ y = f k]) :=
  Do (!a .+ (indx k)).
Next Obligation.
move=>a k [f][_][] _ [->][/= -> _].
by rewrite (updi_split a k); step.
Qed.

Program Definition write (a : array) (k : I) (x : T) :
  {f}, STsep (shape a f,
              [vfun _ => shape a [ffun z => [eta f with k |-> x] z]]) :=
  Do (a .+ (indx k) ::= x).
Next Obligation.
move=>a k x [f][] _ [-> _] /=; rewrite /shape !(updi_split a k).
by step; rewrite takeord dropord ffunE eq_refl.
Qed.

End Array.
End Array.

(* Tabulating a finite function over another one *)
(* Useful in building linked data structures that are pointed to by *)
(* array elements, such as hashtables *)

Section Table.
Import FinIter.
Variables (I : finType) (T S : Type) (x : {array I -> T})
          (Ps : T -> S -> Pred heap).
Definition table := fun (t : I -> T) (b : I -> S) (i:I) => Ps (t i) (b i).

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