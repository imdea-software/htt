From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype tuple finfun fingroup perm interval.
From pcm Require Import options axioms prelude pred ordtype slice.
From pcm Require Import pcm unionmap heap.
From htt Require Import options interlude model heapauto.
From htt Require Import array.

(* hack to avoid "_ *p _" notation clash *)
From mathcomp Require order.
Import order.Order.NatOrder order.Order.TTheory.

Lemma leq_choose a b : a < b -> sumbool (a.+1 == b) (a.+1 < b).
Proof.
move=>H.
case: (decP (b:=a.+1 < b) idP)=>[H2|/negP H2]; first by right.
by left; rewrite eqn_leq H /= leqNgt.
Qed.

(* TODO copied from bubble *)
Section OrdArith.

Fact ord_trans {n} (j : 'I_n) (i : 'I_n) (Hi : i < j) : (i.+1 < n)%N.
Proof.
case: j Hi=>j Hj /= Hi.
by apply/leq_trans/Hj.
Qed.

(* increase within the bound *)
Definition So_lower n (i : 'I_n) (prf : (i.+1 < n)%N) : 'I_n.
Proof. case: i prf=>/= m Hm; apply: Ordinal. Defined.

Lemma So_lower_lift n (i j : 'I_n) (H1 : i < j) : i.+1 < j -> So_lower (ord_trans H1) < j.
Proof. by case: i H1. Qed.

Lemma So_lower_leq n (i j k : 'I_n) (H1 : i <= j) (H2 : j < k) : So_lower (ord_trans (leq_ltn_trans H1 H2)) <= So_lower (ord_trans H2).
Proof. by case: j H1 H2; case: i. Qed.

Lemma So_lower_lt n (i j k : 'I_n) (H1 : i <= j) (H2 : j < k) : i <= So_lower (ord_trans H2).
Proof. by case: j H1 H2; case: i=>/=x Hx y Hy Hxy Hyk; apply/ltnW. Qed.

End OrdArith.

Section Lomuto.
Variable (n : nat) (A : ordType).

Opaque Array.write Array.read.

Program Definition swap (a : {array 'I_n -> A}) (i j : 'I_n) :
  {f : {ffun 'I_n -> A}},
  STsep (Array.shape a f,
        [vfun _ h =>
           h \In Array.shape a (pffun (tperm i j) f)]) :=
  Do (x <-- Array.read a i;
      y <-- Array.read a j;
      Array.write a i y;;
      Array.write a j x).
Next Obligation.
move=>a i j /= [f][] h /= H.
do 2!apply: [stepE f, h]=>//= _ _ [->->].
apply: [stepE f]=>//= _ _ [-> V1]; set f1 := finfun [eta f  with i |-> f j].
apply: [gE   f1]=>//= _ _ [-> V2]; set f2 := finfun [eta f1 with j |-> f i].
move=>{h H}_; split=>//=; suff {V1 V2}: f2 = pffun (tperm i j) f by move=>->.
rewrite {}/f2 {}/f1; apply/ffunP=>/= x; rewrite !ffunE /= ffunE /=.
case: tpermP=>[->|->|/eqP/negbTE->/eqP/negbTE->] {x}//; rewrite eqxx //.
by case: eqP=>// ->.
Qed.

Opaque swap.

Definition partition_lm_loop (a : {array 'I_n -> A}) (pivot : A) (hi : 'I_n) :=
  forall ij : sigT (fun i : 'I_n => sig (fun j : 'I_n => i <= j /\ j < hi)),
  {f : {ffun 'I_n -> A}},
  STsep (Array.shape a f,
        [vfun (i : 'I_n) h =>
           exists p,
           h \In Array.shape a (pffun p f)]).


Program Definition partition_lm_pass (a : {array 'I_n -> A}) (pivot : A) (lo hi : 'I_n) (Hlo : lo < hi):
  {f : {ffun 'I_n -> A}},
  STsep (Array.shape a f,
        [vfun (i : 'I_n) h =>
          exists p,
          h \In Array.shape a (pffun p f)]) :=
  Fix (fun (loop : partition_lm_loop a pivot hi) '(existT i (exist j (conj Hi Hj))) =>
    Do (x <-- Array.read a j;
        if oleq x pivot then
          swap a i j;;
          let i1 := So_lower (ord_trans (leq_ltn_trans Hi Hj)) in  (*i+1*)
          if leq_choose Hj is right pf then
            loop (@existT _ _ i1
                 (@exist _ _ (So_lower (ord_trans Hj)) (*j+1*)
                             (conj (So_lower_leq Hi Hj)
                                   (So_lower_lift Hj pf))))
            else ret i1
        else if leq_choose Hj is right pf then
               loop (@existT _ _ i
                    (@exist _ _ (So_lower (ord_trans Hj)) (*j+1*)
                                (conj (So_lower_lt Hi Hj)
                                      (So_lower_lift Hj pf))))
          else ret i)) (@existT _ _ lo
                        (@exist _ _ lo
                              (conj erefl Hlo))).
Next Obligation.
move=>a pivot lo hi Hlo loop ? i ? j ? Hi Hj [f][] h /= [E V].
apply: [stepE f, h]=>//= _ _ [->->].
case: oleqP=>Hfp.
- apply: [stepE f]=>//= _ m Hm.
  case: (leq_choose Hj)=>Hj1.
  - by step=>_; exists (tperm i j).
  apply: [gE f]=>//=.

(*
Program Definition partition_lm (a : {array 'I_n -> A}) (lo hi : 'I_n) :
  {f : {ffun 'I_n -> A}},
  STsep (Array.shape a f,
        [vfun _ h =>
           h \In Array.shape a (pffun (tperm i j) f)]) :=
  Do (pivot <-- Array.read a hi;
      y <-- Array.read a j;
      Array.write a i y;;
      Array.write a j x).
*)

(*

Lomuto

// Divides array into two partitions
algorithm partition(A, lo, hi) is
  pivot := A[hi] // Choose the last element as the pivot

  // Temporary pivot index
  i := lo - 1

  for j := lo to hi - 1 do
    // If the current element is less than or equal to the pivot
    if A[j] <= pivot then
      // Move the temporary pivot index forward
      i := i + 1
      // Swap the current element with the element at the temporary pivot index
      swap A[i] with A[j]

  // Move the pivot element to the correct pivot position (between the smaller and larger elements)
  i := i + 1
  swap A[i] with A[hi]
  return i // the pivot index

// Sorts a (portion of an) array, divides it into partitions, then sorts those
algorithm quicksort(A, lo, hi) is
  // Ensure indices are in correct order
  if lo >= hi || lo < 0 then
    return

  // Partition array and get the pivot index
  p := partition(A, lo, hi)

  // Sort the two partitions
  quicksort(A, lo, p - 1) // Left side of pivot
  quicksort(A, p + 1, hi) // Right side of pivot

quicksort(A, 0, length(A) - 1)

*)


(*

Hoare

// Divides array into two partitions
algorithm partition(A, lo, hi) is
  // Pivot value
  pivot := A[ floor((hi + lo) / 2) ] // The value in the middle of the array

  // Left index
  i := lo - 1

  // Right index
  j := hi + 1

  loop forever
    // Move the left index to the right at least once and while the element at
    // the left index is less than the pivot
    do i := i + 1 while A[i] < pivot

    // Move the right index to the left at least once and while the element at
    // the right index is greater than the pivot
    do j := j - 1 while A[j] > pivot

    // If the indices crossed, return
    if i >= j then return j

    // Swap the elements at the left and right indices
    swap A[i] with A[j]

// Sorts a (portion of an) array, divides it into partitions, then sorts those
algorithm quicksort(A, lo, hi) is
  if lo >= 0 && hi >= 0 && lo < hi then
    p := partition(A, lo, hi)
    quicksort(A, lo, p) // Note: the pivot is now included
    quicksort(A, p + 1, hi)

quicksort(A, 0, length(A) - 1).

*)