From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype tuple finfun finset fingroup perm interval.
From pcm Require Import options axioms prelude pred ordtype slice.
From pcm Require Import pcm unionmap heap.
From htt Require Import options interlude model heapauto.
From htt Require Import array.

(* hack to avoid "_ *p _" notation clash *)
From mathcomp Require order.
Import order.Order.NatOrder order.Order.TTheory.

(* TODO added *)
Corollary slice_oPR {A : Type} a x (s : seq A) :
        0 < x ->
        &:s (Interval a (BRight x.-1)) = &:s (Interval a (BLeft x)).
Proof. by move=>Hx; rewrite -{2}(prednK Hx) slice_oSR. Qed.

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
Definition Sbo n (i : 'I_n) (prf : (i.+1 < n)%N) : 'I_n.
Proof. case: i prf=>/= m Hm; apply: Ordinal. Defined.

Lemma Sbo_eq n (i : 'I_n) (prf : (i.+1 < n)%N) : nat_of_ord (Sbo prf) = i.+1.
Proof. by case: i prf. Qed.

Lemma Sbo_lift n (i j : 'I_n) (H1 : i < j) : i.+1 < j -> Sbo (ord_trans H1) < j.
Proof. by case: i H1. Qed.

Lemma Sbo_leq n (i j k : 'I_n) (H1 : i <= j) (H2 : j < k) : Sbo (ord_trans (leq_ltn_trans H1 H2)) <= Sbo (ord_trans H2).
Proof. by case: j H1 H2; case: i. Qed.

Lemma Sbo_lt n (i j k : 'I_n) (H1 : i <= j) (H2 : j < k) : i <= Sbo (ord_trans H2).
Proof. by case: j H1 H2; case: i=>/=x Hx y Hy Hxy Hyk; apply/ltnW. Qed.

(* decrease by 1 *)
Definition Po n : 'I_n -> 'I_n :=
  fun '(@Ordinal _ m prf) => @Ordinal n m.-1 (leq_ltn_trans (leq_pred _) prf).

Lemma Po_eq n (i : 'I_n) : nat_of_ord (Po i) = i.-1.
Proof. by case: i. Qed.

End OrdArith.

Section PermFgraphEq.
Variable (n : nat) (A : eqType).

Lemma perm_fgraph (p : 'S_n) (f : {ffun 'I_n -> A}) :
  perm_eq (fgraph (pffun p f))
          (fgraph f).
Proof.
apply/tuple_permP.
exists (cast_perm (esym (card_ord n)) p).
congr val; apply/eq_from_tnth=>/= i.
by rewrite tnth_fgraph tnth_map tnth_fgraph ffunE /= tnth_ord_tuple
  !enum_val_ord cast_permE cast_ordKV esymK.
Qed.


Set Printing All.

rewrite enum_ord.
(* TODO generalize to arb intervals?*)
Lemma perm_on_codom (a b : 'I_n) (p : 'S_n) (f : {ffun 'I_n -> A}) :
  perm_on [set ix : 'I_n | a <= ix & ix <= b] p ->
  perm_eq &:(codom (pffun p f)) `[a : nat, b : nat]
          &:(codom f) `[a : nat, b : nat].
Proof.
move/perm_closed=>/= H.
apply/seq.permP=>pr.
apply/tuple_permP=>/=.
rewrite addn0 addn1.

Section TPermFgraph.
Variable (n : nat) (A : Type).

Lemma tperm_notin (f : {ffun 'I_n -> A}) (x y : 'I_n) (i : interval nat) :
        (x : nat) \notin i -> (y : nat) \notin i ->
        &:(fgraph (pffun (tperm x y) f)) i = &:(fgraph f) i.
Proof.
move=>Hx0 Hx1.
suff E: {in &:(enum 'I_n) i, f =1 pffun (tperm x y) f}.
- by rewrite !fgraph_codom /= !codomE /= -2!slice_map /=; move/eq_in_map: E.
move=>/= z; rewrite slice_mem /=; last first.
- by rewrite count_uniq_mem; [exact: leq_b1|exact: enum_uniq].
case: i Hx0 Hx1=>i j Hx0 Hx1 /=.
case/and3P=>_; rewrite size_enum_ord index_enum_ord =>Hy1 Hy2.
rewrite ffunE; case: tpermP=>// Ez; move: Hy1 Hy2; rewrite {z}Ez /=.
- move: {Hx1}Hx0; rewrite in_itv negb_and; case/orP=>Hij.
  - move=>Hx _; case: i Hx Hij=>[[] ix|[]] //=.
    - by rewrite addn0=>->.
    - by rewrite addn1 ltEnat /= leEnat =>->.
    by rewrite leEnat=>Hnx _; move: (ltn_ord x); rewrite leqNgt ltnS Hnx.
  move=>_ Hx; case: j Hx Hij=>[[] jx|[]] //=.
  - by rewrite addn0=>->.
  by rewrite addn1 ltEnat /= ltnS leEnat =>->.
move: {Hx0}Hx1; rewrite in_itv negb_and; case/orP=>Hij.
- move=>Hx _; case: i Hx Hij=>[[] ix|[]] //=.
  - by rewrite addn0=>->.
  - by rewrite addn1 ltEnat /= leEnat =>->.
  by rewrite leEnat =>Hny _; move: (ltn_ord y); rewrite ltnNge Hny.
move=>_ Hx; case: j Hx Hij=>[[] jx|[]] //=.
- by rewrite addn0=>->.
by rewrite addn1 ltEnat /= ltnS leEnat =>->.
Qed.

End TPermFgraph.

Section Lomuto.
Variable (n : nat) (A : ordType).

Opaque Array.write Array.read.

Program Definition swap (a : {array 'I_n -> A}) (i j : 'I_n) :
  {f : {ffun 'I_n -> A}},
  STsep (Array.shape a f,
        [vfun _ h =>
           h \In Array.shape a (pffun (tperm i j) f)]) :=
  Do (if i == j then skip else
        x <-- Array.read a i;
        y <-- Array.read a j;
        Array.write a i y;;
        Array.write a j x).
Next Obligation.
move=>a i j /= [f][] h /= H.
case: ifP=>[/eqP->|Hij].
- by step=>_; rewrite tperm1 pffunE1.
do 2!apply: [stepE f, h]=>//= _ _ [->->].
apply: [stepE f]=>//= _ _ [-> V1]; set f1 := finfun [eta f  with i |-> f j].
apply: [gE   f1]=>//= _ _ [-> V2]; set f2 := finfun [eta f1 with j |-> f i].
move=>{h H}_; split=>//=; suff {V1 V2}: f2 = pffun (tperm i j) f by move=>->.
rewrite {}/f2 {}/f1; apply/ffunP=>/= x; rewrite !ffunE /= ffunE /=.
by case: tpermP=>[->|->|/eqP/negbTE->/eqP/negbTE->] {x}//; rewrite eqxx // Hij.
Qed.

Opaque swap.

Definition partition_lm_loop (a : {array 'I_n -> A}) (pivot : A) (lo hi : 'I_n) :=
  forall ij : sigT (fun i : 'I_n => sig (fun j : 'I_n => i <= j /\ j < hi)),
  let i := projT1 ij in
  let j := proj1_sig (projT2 ij) in
  {f : {ffun 'I_n -> A}},
  STsep (fun h => [/\ h \In Array.shape a f,
                      lo <= i,
                      all (oleq^~ pivot) (&:(fgraph f) `[lo : nat, i : nat[) &
                      all (ord    pivot) (&:(fgraph f) `[i : nat, j : nat[)],
        [vfun (v : 'I_n) h =>
           i <= v <= hi /\
           exists p, let f' := pffun p f in
             [/\ perm_on [set ix : 'I_n | i <= ix < hi] p,
                 h \In Array.shape a f',
                 all (oleq^~ pivot) (&:(fgraph f') `[lo : nat, v : nat[) &
                 all (ord    pivot) (&:(fgraph f') `[v : nat, hi : nat[)]]).

Program Definition partition_lm_pass (a : {array 'I_n -> A}) (pivot : A) (lo hi : 'I_n) (Hlo : lo < hi):
  {f : {ffun 'I_n -> A}},
  STsep (Array.shape a f,
        [vfun (v : 'I_n) h =>
          lo <= v <= hi /\
          exists p, let f' := pffun p f in
            [/\ perm_on [set ix : 'I_n | lo <= ix < hi] p,
                h \In Array.shape a f',
                all (oleq^~ pivot) (&:(fgraph f') `[lo : nat, v : nat[) &
                all (ord    pivot) (&:(fgraph f') `[v : nat, hi : nat[)]]) :=
  Do (let go :=
    Fix (fun (loop : partition_lm_loop a pivot lo hi) '(existT i (exist j (conj Hi Hj))) =>
      Do (x <-- Array.read a j;
          if oleq x pivot then
            swap a i j;;
            let i1 := Sbo (ord_trans (leq_ltn_trans Hi Hj)) in  (* i+1 *)
            if leq_choose Hj is right pf then
              loop (@existT _ _ i1 (@exist _ _ (Sbo (ord_trans Hj)) (* j+1 *)
                                   (conj (Sbo_leq Hi Hj)
                                         (Sbo_lift Hj pf))))
              else ret i1
          else if leq_choose Hj is right pf then
                 loop (@existT _ _ i (@exist _ _ (Sbo (ord_trans Hj)) (* j+1 *)
                                     (conj (Sbo_lt Hi Hj)
                                           (Sbo_lift Hj pf))))
            else ret i))
  in go (@existT _ _ lo (@exist _ _ lo (conj (leqnn lo) Hlo)))).
Next Obligation.
move=>a pivot lo hi Hlo loop _ i _ j _ Hi Hj [f][] h /= [H Oli Ai Aj].
apply: [stepE f, h]=>//= _ _ [->->].
case: oleqP=>Hfp.
- apply: [stepE f]=>//= _ m Hm.
  case: (leq_choose Hj)=>Hj1.
  - step=>_; split.
    - rewrite Sbo_eq; apply/andP; split=>//.
      by apply/leq_ltn_trans/Hj.
    exists (tperm i j); rewrite Sbo_eq; split=>//.
    - rewrite -(eqP Hj1).
      apply/subsetP=>/= x; rewrite !inE /= ltnS.
      by case: tpermP=>[->_|->_|]; rewrite ?leqnn ?andbT // eqxx.
    - rewrite slice_oSR slice_xR; last by rewrite bnd_simp.
      rewrite onth_codom ffunE tpermL /= all_rcons Hfp /=.
      rewrite tperm_notin // in_itv /= negb_and leEnat ltEnat /= -leqNgt.
      - by rewrite leqnn orbT.
      by rewrite Hi orbT.
    rewrite -(eqP Hj1) /= slice_oSR.
    move: Hi; rewrite leq_eqVlt; case/orP=>[/eqP->|Hi].
    - by rewrite itv_swapped_bnd // bnd_simp ltEnat /= ltnS.
    rewrite slice_xR; last by rewrite bnd_simp.
    move: Aj; rewrite slice_xL; last by rewrite bnd_simp.
    rewrite onth_codom /=; case/andP=>Hpi Aj.
    rewrite onth_codom /= all_rcons; apply/andP; split.
    - by rewrite ffunE tpermR.
    by rewrite tperm_notin -?slice_oSL //
      in_itv /= negb_and leEnat ltEnat /= -!leqNgt leqnn // orbT.
  apply: [gE (pffun (tperm i j) f)]=>//=.
  - split=>//; rewrite !Sbo_eq; first by apply/ltnW.
    - rewrite slice_oSR slice_xR; last by rewrite bnd_simp.
      rewrite onth_codom ffunE tpermL /= all_rcons Hfp /=.
      rewrite tperm_notin // in_itv /= negb_and leEnat ltEnat /= -leqNgt.
      - by rewrite leqnn orbT.
      by rewrite Hi orbT.
    rewrite slice_oSR.
    move: Hi; rewrite leq_eqVlt; case/orP=>[/eqP->|Hi].
    - by rewrite itv_swapped_bnd // bnd_simp ltEnat /= ltnS.
    rewrite slice_xR; last by rewrite bnd_simp.
    move: Aj; rewrite slice_xL; last by rewrite bnd_simp.
    rewrite onth_codom /=; case/andP=>Hpi Aj.
    rewrite onth_codom /= all_rcons; apply/andP; split.
    - by rewrite ffunE tpermR.
    by rewrite tperm_notin -?slice_oSL //
      in_itv /= negb_and leEnat ltEnat /= -!leqNgt leqnn // orbT.
  move=>z k [Hz][p'][Pk Hk Al Ah] Vk; split.
  - by move: Hz; rewrite Sbo_eq; case/andP=>/ltnW->->.
  exists (p' * tperm i j)%g; rewrite pffunEM; split=>//.
  rewrite Sbo_eq in Pk; apply: perm_onM.
  - apply/(subset_trans Pk)/subsetP=>x; rewrite !inE.
    by case/andP=>/ltnW->->.
  apply/subsetP=>/= x; rewrite !inE /=.
  case: tpermP=>[->_|->_|]; first last.
  - by rewrite eqxx.
  - by apply/andP.
  by rewrite leqnn /=; apply/leq_ltn_trans/Hj.
case: (leq_choose Hj)=>Hj1.
- step=>_; split.
  - by rewrite leqnn /= -(eqP Hj1); apply: ltnW.
  exists 1%g; rewrite pffunE1; split=>//.
  - by apply: perm_on1.
  rewrite -(eqP Hj1) slice_oSR slice_xR; last by rewrite bnd_simp.
  by rewrite onth_codom /= all_rcons Hfp.
apply: [gE f]=>//=; split=>//.
rewrite Sbo_eq slice_oSR slice_xR; last by rewrite bnd_simp.
by rewrite onth_codom /= all_rcons Hfp.
Qed.
Next Obligation.
move=>/= a pivot lo hi Hlo [f][] i /= H.
by apply: [gE f]=>//=; split=>//; rewrite slice_kk.
Qed.

Opaque partition_lm_pass.

Program Definition partition_lm (a : {array 'I_n -> A}) (lo hi : 'I_n) (Hlo : lo < hi):
  {f : {ffun 'I_n -> A}},
  STsep (Array.shape a f,
        [vfun (v : 'I_n) h =>
          lo <= v <= hi /\
          exists p, let f' := pffun p f in
            [/\ perm_on [set ix : 'I_n | lo <= ix <= hi] p,
                h \In Array.shape a f',
                all (oleq^~ (f' v)) (&:(fgraph f') `[lo : nat, v : nat[) &
                all (ord    (f' v)) (&:(fgraph f') `]v : nat, hi : nat])]]) :=
  Do (pivot <-- Array.read a hi;
      v <-- partition_lm_pass a pivot Hlo;
      swap a v hi;;
      ret v).
Next Obligation.
move=> a lo hi Hlo /= [f][] h /= [E V].
apply: [stepE f, h]=>//= _ _ [->->].
apply: [stepE f]=>//= v m [Hi][p][Pm Hm Al Ah].
apply: [stepE (pffun p f)]=>//= _ k Hj.
step=>Vk; split=>//.
exists (tperm v hi * p)%g; split=>//.
- apply: perm_onM.
  - apply/subsetP=>/= x; rewrite !inE /=.
    case: tpermP=>[->_|->_|] //; last by rewrite eqxx.
    by rewrite leqnn andbT; apply/ltnW.
  apply/(subset_trans Pm)/subsetP=>x; rewrite !inE.
  by case/andP=>->/ltnW->.
- by rewrite pffunEM.
- rewrite pffunEM ffunE tpermL ffunE (out_perm Pm); last first.
  - by rewrite inE negb_and -!ltnNge leqnn orbT.
  rewrite tperm_notin // in_itv negb_and /= leEnat ltEnat /= -leqNgt.
  - by rewrite leqnn orbT.
  by case/andP: Hi=>_ ->; rewrite orbT.
rewrite pffunEM ffunE tpermL ffunE (out_perm Pm); last first.
- by rewrite inE negb_and -!ltnNge leqnn orbT.
case/andP: Hi=>_; rewrite leq_eqVlt; case/orP=>[/eqP->|Hi].
- by rewrite slice_kk.
move: Ah; rewrite slice_xL; last by rewrite bnd_simp.
rewrite onth_codom /=; case/andP=>Hg Ha.
rewrite slice_xR; last by rewrite bnd_simp.
rewrite onth_codom /= all_rcons; apply/andP; split.
- by rewrite ffunE tpermR.
by rewrite tperm_notin // in_itv negb_and /= ltEnat /= -!leqNgt leqnn // orbT.
Qed.

End Lomuto.

Section LomutoQsort.
Variable (n : nat) (A : ordType).

Opaque partition_lm.

Definition quicksort_lm_loop (a : {array 'I_n.+1 -> A}) :=
  forall (lohi : 'I_n.+1 * 'I_n.+1),
  let lo := lohi.1 in
  let hi := lohi.2 in
  {f : {ffun 'I_n.+1 -> A}},
  STsep (Array.shape a f,
        [vfun (_ : unit) h =>
           exists p, let f' := pffun p f in
             [/\ perm_on [set ix : 'I_n.+1 | lo <= ix <= hi] p,
                 h \In Array.shape a f' &
                 sorted oleq (&:(fgraph f') `[lo : nat, hi : nat])]]).

Program Definition quicksort_lm (a : {array 'I_n.+1 -> A}) :
  {f : {ffun 'I_n.+1 -> A}},
  STsep (Array.shape a f,
        [vfun (_ : unit) h =>
           exists p, let f' := pffun p f in
             h \In Array.shape a f' /\
             sorted oleq (fgraph f')]) :=
  let go :=
    Fix (fun (loop : quicksort_lm_loop a) '(l,h) =>
      Do (if decP (b:=(l : nat) < h) idP isn't left pf then skip
          else v <-- @partition_lm _ _ a l h pf;
               loop (l, Po v);;
               (* this would be caught by previous check on a next recursive call *)
               (* but we have to stay under n *)
               if decP (b:=v.+1 < n.+1) idP isn't left pf
                 then skip
                 else loop (Sbo pf, h)))
  in go (ord0, ord_max).
Next Obligation.
move=>a loop _ l h [f][] i /= Hi.
case: decP=>[Olh|/negP]; last first.
- rewrite -leqNgt => Ohl.
  step=>_; exists 1%g; rewrite pffunE1; split=>//.
  - by apply: perm_on1.
  move: Ohl; rewrite leq_eqVlt; case/orP=>[/eqP->|Ohl].
  - by rewrite slice_kk /= onth_codom.
  by rewrite itv_swapped_bnd.
apply: [stepE f]=>//= v m [/andP [Hvl Hvh]][p][Hp Hm Al Ah].
apply: [stepE (pffun p f)]=>//= _ ml [pl][].
rewrite Po_eq -pffunEM => Hpl Hml Sl.
case: decP=>[pf|/negP]; last first.



- rewrite -leqNgt; move: (ltn_ord v); rewrite !ltnS=>Hvn Hnv.
  have {Hvn Hnv}Ev: (v : nat) = n by apply/eqP; rewrite eqn_leq Hvn.
  have {Hvh}Eh: (h : nat) = (v : nat).
  - apply/eqP; rewrite eqn_leq Hvh Ev andbT.
    by move: (ltn_ord h); rewrite ltnS.
  step=>_; exists (pl * p)%g; split=>//.
  - apply: perm_onM=>//; rewrite Eh.
    apply/(subset_trans Hpl)/subsetP=>z; rewrite !inE.
    case/andP=>-> /= Hz.
    by apply: (leq_trans Hz); exact: leq_pred.
  rewrite Eh; case: (eqVneq v ord0)=>[E|Nv].
  - move: Hvl; rewrite E /= leqn0 => /eqP->.
    by rewrite slice_kk /= (_ : 0 = (ord0 : 'I_n.+1)) // onth_codom.
  rewrite slice_xR // onth_codom /= sorted_rconsE //.
  apply/andP; split; last by rewrite -slice_oPR // lt0n.
  rewrite pffunEM ffunE (out_perm Hpl); last first.
  - by rewrite inE negb_and -!ltnNge ltn_predL lt0n Nv orbT.

  rewrite (perm_all (s2:=&:(codom (pffun p f)) `[l : nat, v : nat[)) //.





- apply: [stepE (pffun p f)]=>//= _ ml [pl][].
  rewrite Po_eq -pffunEM => Hpl Hml Sl.
  apply: [gE (pffun (pl * p) f)]=>//= _ mr [pr][].
  rewrite Sbo_eq -pffunEM => Hpr Hmr Sr _.
  exists (pr * (pl * p))%g; split=>//.
  - apply: perm_onM.
    - apply/(subset_trans Hpr)/subsetP=>/= z; rewrite !inE.
      case/andP=>Hz ->; rewrite andbT.
      by apply/ltnW/leq_ltn_trans/Hz.
    apply: perm_onM=>//.
    apply/(subset_trans Hpl)/subsetP=>/= z; rewrite !inE.
    case/andP=>->/= Hz.
    apply/leq_trans/Hvh/(leq_trans Hz).
    by exact: leq_pred.



 E: (decP idP)=>[x|x].

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