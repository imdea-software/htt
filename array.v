Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
Require Import fintype tuple finfun finset.
Require Import pred pcm unionmap heap heaptac domain stmod stsep stlog stlogR. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Definition indx {I : finType} (x : I) := index x (enum I).

Prenex Implicits indx.

(***********************************)
(* Arrays indexed by a finite type *)
(***********************************)

Record array (I : finType) (T : Type) : Type := Array {orig :> ptr}.
Implicit Arguments Array [I T]. 

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

Program Definition new (x : T) : 
  STsep (emp, fun y h => exists a, y = Val a /\ h \In shape a [ffun => x]) :=
  Do (x <-- allocb x #|I|; 
      ret (Array x)).
Next Obligation.
move=>i ->; step=>y; step; vauto; rewrite unitR; congr updi. 
rewrite fgraph_codom /= codomE cardE.
by elim: (enum I)=>[|t ts] //= ->; rewrite (ffunE _ _). 
Qed.


Definition newf_loop a (f : {ffun I -> T}) : Type :=
  forall s : seq I, STsep (fun i => exists g, exists s', [/\ i \In shape a g, 
                                      s' ++ s = enum I & 
                                      forall x, x \in s' -> g x = f x], 
                           fun y m => exists a, y = Val a /\ m \In shape a f).

Program Definition newf (f : {ffun I -> T}) : 
          STsep (emp, fun y h => exists a, y = Val a /\ h \In shape a f) :=
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
move=>_ /= [g][s'][[->]]; case: s=>[|k t] /= _ H1 H2.
- rewrite cats0 in H1; step; vauto.  
  by rewrite (_ : g = f) // -ffunP=>y; apply: H2; rewrite H1 mem_enum.
rewrite (updi_split x k); step; apply: val_do0=>//. 
exists (finfun [eta g with k |-> f k]), (s' ++ [:: k]).
rewrite /shape (updi_split x k) takeord dropord (ffunE _ _) /= eq_refl -catA.
split=>// y; rewrite ffunE /= mem_cat inE /=.
by case: eqP=>[->|_] //; rewrite orbF; apply: H2.
Qed.
Next Obligation.
move=>_ ->; case: fintype.pickP=>[v|] H /=; last first. 
- step; exists (@Array I T null); do !split=>//.
  have L: #|I| = 0 by rewrite cardE; case: (enum I)=>[|x s] //; move: (H x).
  by case: (fgraph f)=>/=; rewrite L; case.
apply: vrf_seq; apply: val_do0=>[|x m [_][[<-]] K _|??[?][]] //.  
by apply: val_do0=>//; exists [ffun => f v], nil. 
Qed.


Definition loop_inv (a : array) : Type := 
  forall k, STsep (fun i => exists xs:seq T, [/\ i = updi (a .+ k) xs, valid i &
                              size xs + k = #|I|],
                   fun y m => y = Val tt /\ m = Unit).
 
Program 
Definition free (a : array) : STsep (fun i => exists f, i \In shape a f, 
                                     fun y m => y = Val tt /\ m = Unit) :=
  Do (let: f := Fix (fun (f : loop_inv a) k =>  
                  Do (if k == #|I| then ret tt 
                      else 
                        dealloc a.+k;; 
                        f k.+1)) 
      in f 0).
Next Obligation.
move=>_ /= [[|v xs]][->] /= _; first by rewrite add0n=>/eqP ->; apply: val_ret. 
case: eqP=>[->|_ H]; first by move/eqP; rewrite -{2}(add0n #|I|) eqn_add2r. 
step; apply: val_doR=>[V|[] m|e m []] //. 
by exists xs; rewrite V ptrA addn1 -addSnnS unitL.  
Qed.
Next Obligation.
move=>_ /= [f][->] _; rewrite -[updi _ _]unitR. 
apply: val_do=>[V|x m|e m []] /=; try by rewrite unitR.
exists (tval (fgraph f)).
by rewrite ptr0 V {3}fgraph_codom /= codomE size_map -cardE. 
Qed.


Program Definition read (a : array) (k : I) :
   STbin (fun i => exists f, i \In shape a f, 
          fun y i m => forall f, i \In shape a f -> y = Val (f k) /\ i = m) :=
  Do (!a .+ (indx k)).
Next Obligation.
by apply: ghE=>// _ f [->] _ _ _; rewrite /shape (updi_split a k); step.
Qed.


Program Definition write (a : array) (k : I) (x : T) : 
  {f}, STsep (fun i => i \In shape a f, 
              fun y m => m \In shape a [ffun z => [eta f with k |-> x] z] /\ 
                         y = Val tt) :=
  Do (a .+ (indx k) ::= x). 
Next Obligation.
apply: ghE=>// i f [->] _ _ V; rewrite /shape !(updi_split a k).
by step; rewrite takeord dropord ffunE eq_refl.  
Qed.

End Array. 
End Array.

