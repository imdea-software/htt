From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype tuple finfun fingroup perm interval.
From pcm Require Import options axioms prelude pred ordtype slice.
From pcm Require Import pcm unionmap heap.
From htt Require Import options interlude model heapauto.
From htt Require Import array.

(* hack to avoid "_ *p _" notation clash *)
From mathcomp Require order.
Import order.Order.NatOrder order.Order.TTheory.

(* Mathematics of (bubble) array sorting:                                   *)
(* A theory of permutations built out of (adjacent-element) swaps acting on *)
(* finite functions from bounded nats to ordered values.                    *)

(* Shorthands for previous/next indices *)
(* TODO use fintype.lift instead ? *)
Section OrdArith.

(* widen by 1 *)
Definition Wo n : 'I_n -> 'I_n.+1 :=
  widen_ord (leqnSn _).

(* increase by 1 *)
Definition So n : 'I_n -> 'I_n.+1 :=
  fun '(@Ordinal _ m prf) => @Ordinal n.+1 m.+1 prf.

Lemma So_eq n (i : 'I_n) : nat_of_ord (So i) = i.+1.
Proof. by case: i. Qed.

Lemma SoN0 n (i : 'I_n) : So i != ord0.
Proof. by case: i. Qed.

Lemma So_WoN n (i : 'I_n) : So i != Wo i.
Proof.
case: i=>/= m prf; rewrite /Wo /widen_ord /=; apply/negP=>/eqP; case=>/eqP.
by rewrite eqn_leq leqnSn andbT ltnn.
Qed.

(* decrease by 1 *)
Definition Po n : 'I_n -> 'I_n :=
  fun '(@Ordinal _ m prf) => @Ordinal n m.-1 (leq_ltn_trans (leq_pred _) prf).

Lemma Po_eq n (i : 'I_n) : nat_of_ord (Po i) = i.-1.
Proof. by case: i. Qed.

(* increase within the bound *)
Definition Sbo n (i : 'I_n) (prf : (i.+1 < n)%N) : 'I_n.
Proof. case: i prf=>/= m Hm; apply: Ordinal. Defined.

Lemma Sbo_eq n (i : 'I_n) (prf : (i.+1 < n)%N) : nat_of_ord (Sbo prf) = i.+1.
Proof. by case: i prf. Qed.

Lemma Wo_Sbo_eq n (i : 'I_n) (prf : (i.+1 < n)%N) : Wo (Sbo prf) = So i.
Proof. by case: i prf=>/= m prf0 prf1; apply/ord_inj. Qed.

(* subtract 2 and decrease bound by 1 *)
Definition M2lo n (i : 'I_n) (pi : 1%N < i) : 'I_n.-1.
Proof.
case: i pi=>m prf /= Hm.
apply: (Ordinal (n:=n.-1) (m:=m.-2)).
rewrite ltn_predRL; case: m prf Hm=>//=; case=>//= m Hm _.
by apply: ltnW.
Defined.

Lemma M2lo_eq n (i : 'I_n) (prf : 1%N < i) : nat_of_ord (M2lo prf) = i.-2.
Proof. by case: i prf. Qed.

End OrdArith.

(* Taking current/next element *)
Section OnthCodom.
Variable (A : Type).

Corollary onth_codom1 {n} (i : 'I_n) (f: {ffun 'I_n.+1 -> A}) :
            onth (fgraph f) i = Some (f (Wo i)).
Proof. by rewrite (onth_codom (Wo i)). Qed.

Corollary onth_codom1S {n} (i : 'I_n) (f: {ffun 'I_n.+1 -> A}) :
            onth (fgraph f) i.+1 = Some (f (So i)).
Proof. by rewrite -(onth_codom (So i)) /= So_eq. Qed.

End OnthCodom.

(* Slicing on finfun codomains *)
Section CodomSlice.
Variable (n : nat) (A : Type).

Lemma codom1_split (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        codom f = &:(fgraph f) `]-oo, i : nat[ ++
                  [:: f (Wo i); f (So i)] ++
                  &:(fgraph f) `]i.+1, +oo[.
Proof.
set i0 := Wo i; set i1 := So i.
rewrite {1}codomE (enum_split i0) /= {2}(enum_split i1) /= /heap.indx
  (index_enum_ord i0) (index_enum_ord i1) drop_cat size_take
  size_enum_ord ltn_ord So_eq ltnn subnn /= map_cat /= map_take map_drop -codomE.
by rewrite /slice /= addn0 addn1 /= drop0 take_size.
Qed.

(* TODO generalize? *)
Lemma codom1_xu_cons (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        &:(fgraph f) `[i.+1, +oo[ = f (So i) :: &:(fgraph f) `]i.+1, +oo[.
Proof. by rewrite slice_xL // onth_codom1S. Qed.

(* TODO notation fails *)
Lemma codom1_ax_rcons (f : {ffun 'I_n.+1 -> A}) (a : itv_bound nat) (i : 'I_n) :
        order.Order.le a (BLeft (i : nat)) ->
               &:(fgraph f) (Interval a (BRight (i : nat))) =
        rcons (&:(fgraph f) (Interval a (BLeft (i : nat)))) (f (Wo i)).
Proof. by move=>H; rewrite slice_xR //= onth_codom1 /=. Qed.

Lemma codom1_ax_rcons2 (f : {ffun 'I_n.+1 -> A}) (a : itv_bound nat) (i : 'I_n) :
        order.Order.le a (BLeft (i : nat)) ->
                      &:(fgraph f) (Interval a (BRight i.+1)) =
        rcons (rcons (&:(fgraph f) (Interval a (BLeft (i : nat)))) (f (Wo i))) (f (So i)).
Proof.
move=>H; rewrite slice_xR; last first.
- by apply: ltW; case: a H=>[[] ax|ab] //; rewrite !bnd_simp ltEnat /= =>/ltnW.
by rewrite onth_codom1S /= slice_oSR codom1_ax_rcons.
Qed.

Lemma codom1_kk (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        &:(fgraph f) `[i:nat, i:nat] = [:: f (Wo i)].
Proof.
rewrite slice_kk /=.
pose i' := cast_ord (esym (card_ord n.+1)) (Wo i).
move: (onth_tnth (codom f) i')=>/= ->.
by move: (@tnth_fgraph _ _ f i'); rewrite enum_val_ord {2}/i' cast_ordKV=>->.
Qed.

Lemma codom1_Skk (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        &:(fgraph f) `[i.+1, i.+1] = [:: f (So i)].
Proof.
rewrite slice_kk /=.
pose i' := cast_ord (esym (card_ord n.+1)) (So i).
move: (onth_tnth (codom f) i')=>/=; rewrite So_eq =>->.
by move: (@tnth_fgraph _ _ f i'); rewrite enum_val_ord {2}/i' cast_ordKV=>->.
Qed.

End CodomSlice.

(* Sortedness on codomain slices *)
Section CodomSliceOrd.
Variable (n : nat) (A : ordType).

Lemma codom1_sortedS (f: {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        oleq (f (Wo i)) (f (So i)) ->
        sorted oleq (&:(fgraph f) `]-oo, i : nat]) ->
        sorted oleq (&:(fgraph f) `]-oo, i.+1]).
Proof.
move=>Hf; rewrite codom1_ax_rcons // codom1_ax_rcons2 // => Hs.
rewrite (sorted_rconsE _ _ (@otrans A)) Hs andbT all_rcons Hf /=.
move: Hs; rewrite (sorted_rconsE _ _ (@otrans A)).
by case/andP=>+ _; apply/sub_all=>z Hz; apply/otrans/Hf.
Qed.

End CodomSliceOrd.

(* Swapping adjacent elements and its interaction with slicing *)
Section SwapNext.
Variable (n : nat) (A : Type).

Definition swnx (i : 'I_n) : 'S_n.+1 := tperm (Wo i) (So i).

Lemma swnxE1 (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        pffun (swnx i) f (Wo i) = f (So i).
Proof.
by rewrite /swnx ffunE; case: tpermP=>// /eqP; rewrite eq_sym (negbTE (So_WoN i)).
Qed.

Lemma swnxE2 (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        pffun (swnx i) f (So i) = f (Wo i).
Proof.
by rewrite /swnx ffunE; case: tpermP=>// /eqP; rewrite (negbTE (So_WoN i)).
Qed.

Lemma swnx_notin (f : {ffun 'I_n.+1 -> A}) (x : 'I_n) (i : interval nat) :
        (x : nat) \notin i -> x.+1 \notin i ->
        &:(fgraph (pffun (swnx x) f)) i = &:(fgraph f) i.
Proof.
move=>Hx0 Hx1.
suff E: {in &:(enum 'I_n.+1) i, f =1 pffun (swnx x) f}.
- by rewrite !fgraph_codom /= !codomE /= -2!slice_map /=; move/eq_in_map: E.
move=>/= y; rewrite slice_mem /=; last first.
- by rewrite count_uniq_mem; [exact: leq_b1|exact: enum_uniq].
case: i Hx0 Hx1=>i j Hx0 Hx1 /=.
case/and3P=>_; rewrite /swnx size_enum_ord index_enum_ord =>Hy1 Hy2.
rewrite ffunE; case: tpermP=>// Ey; move: Hy1 Hy2; rewrite {y}Ey /=.
- move: {Hx1}Hx0; rewrite in_itv negb_and; case/orP=>Hij.
  - move=>Hx _; case: i Hx Hij=>[[] ix|[]] //=.
    - by rewrite addn0=>->.
    - by rewrite addn1 ltEnat /= leEnat =>->.
    by rewrite leEnat=>Hnx _; move: (ltn_ord x)=>/ltnW; rewrite leqNgt Hnx.
  move=>_ Hx; case: j Hx Hij=>[[] jx|[]] //=.
  - by rewrite addn0=>->.
  by rewrite addn1 ltEnat /= ltnS leEnat =>->.
move: {Hx0}Hx1; rewrite in_itv negb_and So_eq; case/orP=>Hij.
- move=>Hx _; case: i Hx Hij=>[[] ix|[]] //=.
  - by rewrite addn0=>->.
  - by rewrite addn1 ltEnat /= leEnat =>->.
  by rewrite leEnat ltnS=>Hnx _; move: (ltn_ord x); rewrite ltnNge Hnx.
move=>_ Hx; case: j Hx Hij=>[[] jx|[]] //=.
- by rewrite addn0=>->.
by rewrite addn1 ltEnat /= ltnS leEnat =>->.
Qed.

Corollary swnx_ao (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) x k :
            (k <= i)%N ->
            &:(fgraph (pffun (swnx i) f)) (Interval x (BLeft k)) =
            &:(fgraph f) (Interval x (BLeft k)).
Proof.
move=>Hk.
apply: swnx_notin; rewrite in_itv /= negb_and ltEnat /= -leqNgt; apply/orP; right=>//.
by apply: ltnW.
Qed.

Corollary swnx_oa (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) k y :
            (i.+1 <= k)%N ->
            &:(fgraph (pffun (swnx i) f)) (Interval (BRight k) y) =
            &:(fgraph f) (Interval (BRight k) y).
Proof.
move=>Hk.
apply: swnx_notin; rewrite in_itv /= negb_and ltEnat /= -leqNgt; apply/orP; left=>//.
by apply: ltnW.
Qed.

Lemma swnx_split (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        codom (pffun (swnx i) f) = &:(fgraph f) `]-oo, i : nat[ ++
                                    [:: f (So i); f (Wo i)] ++
                                    &:(fgraph f) `]i.+1, +oo[.
Proof.
rewrite /= (codom1_split _ i) /=; set i0 := Wo i; set i1 := So i.
by rewrite swnx_ao // swnx_oa //= swnxE1 swnxE2.
Qed.

Lemma swnx_ux_rcons (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        &:(fgraph (pffun (swnx i) f)) `]-oo, i : nat] =
                  rcons (&:(fgraph f) `]-oo, i : nat[) (f (So i)).
Proof. by rewrite codom1_ax_rcons // swnx_ao // swnxE1. Qed.

Lemma swnx_ux_rcons2 (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        &:(fgraph (pffun (swnx i) f)) `]-oo, i.+1] =
           rcons (rcons (&:(fgraph f) `]-oo, i : nat[) (f (So i))) (f (Wo i)).
Proof. by rewrite codom1_ax_rcons2 // swnx_ao // swnxE1 swnxE2. Qed.

Lemma swnx_xu_cons (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        &:(fgraph (pffun (swnx i) f)) `[i.+1, +oo[ =
             f (Wo i) :: &:(fgraph f) `]i.+1, +oo[.
Proof. by rewrite codom1_xu_cons swnx_oa // swnxE2. Qed.

Lemma swnx_Skk (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        &:(fgraph (pffun (swnx i) f)) `[i.+1, i.+1] = [:: f (Wo i)].
Proof. by rewrite codom1_Skk swnxE2. Qed.

End SwapNext.

(* Swaps/slices with decidable equality *)
Section SwapNextEq.
Variable (n : nat) (A : eqType).

Lemma perm_swnx (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
        perm_eq (fgraph f) (fgraph (pffun (swnx i) f)).
Proof.
rewrite /= (codom1_split f i) swnx_split.
by apply/permPl/perm_catl/perm_cons2.
Qed.

Lemma perm_swnx_ux (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) k :
        i <= k ->
        perm_eq (&:(fgraph f) `]-oo, k.+1]) (&:(fgraph (pffun (swnx i) f)) `]-oo, k.+1]).
Proof.
move=>H; move: (perm_swnx f i).
set f' : {ffun 'I_n.+1 -> A} := pffun (swnx i) f.
rewrite {1}(slice_uxou (fgraph f) k.+1) {1}(slice_uxou (fgraph f') k.+1).
by rewrite swnx_oa /=; [rewrite perm_cat2r | rewrite ltnS].
Qed.

End SwapNextEq.

Section Bubble.
Variable (n : nat) (A : ordType).

Opaque Array.write Array.read.

(* We verify 3 versions of the algorithm.                              *)
(*                                                                     *)
(* The flag/swapped index is threaded through as a functional argument *)
(* instead of storing and reading it from the heap. This would be      *)
(* straightforward to implement - just make it a logical variable and  *)
(* add corresponding heap bureacracy.                                  *)

(***************)
(* unoptimized *)
(***************)

(*****************************************************)
(* pseudocode in idealized effectful ML-like lang    *)
(* assuming size a >= 2 and decidable total ordering *)
(* on A                                              *)
(*                                                   *)
(* let cas_next (a : array A) (i : nat) : bool =     *)
(*   let prev = array.read a  i;                     *)
(*   let next = array.read a (i+1);                  *)
(*   if next < prev then                             *)
(*     array.write a  i    next;                     *)
(*     array.write a (i+1) prev;                     *)
(*     true                                          *)
(*    else false                                     *)
(*                                                   *)
(* let bubble_pass (a : array A) : bool =            *)
(*   let go (i : nat) (sw : bool) : bool = {         *)
(*     let sw1 = sw || cas_next a i;                 *)
(*     if i < (size a)-2 then go (i+1) sw1 else sw1  *)
(*   };                                              *)
(*   go 0 false                                      *)
(*                                                   *)
(* let bubble_sort (a : array A) : unit =            *)
(*   if bubble_pass a then bubble_sort a else ().    *)
(*****************************************************)

Program Definition cas_next (a : {array 'I_n.+2 -> A}) (i : 'I_n.+1) :
  {f : {ffun 'I_n.+2 -> A}},
  STsep (Array.shape a f,
        [vfun (b : bool) h =>
          exists (p : 'S_n.+2), let i0 := Wo i in let i1 := So i in
            h \In Array.shape a (pffun p f) /\
            if b
              then p = swnx i /\ ord (f i1) (f i0)
              else p = 1%g /\ oleq (f i0) (f i1)]) :=
  let i0 := Wo i in let i1 := So i in
  Do (prev <-- Array.read a i0;
      next <-- Array.read a i1;
      if ord next prev then
          Array.write a i0 next;;
          Array.write a i1 prev;;
          ret true
        else ret false).
Next Obligation.
move=>a i /= [f][] h /= [E V].
set i0 := Wo i; set i1 := So i.
do 2!apply: [stepE f, h]=>//= _ _ [->->].
case: oleqP=>H; first by step=>_; exists 1%g; split=>//; rewrite pffunE1.
apply: [stepE f ]=>//= _ _ [-> Vs ]; set fs  := finfun [eta f  with i0 |-> f i1].
apply: [stepE fs]=>//= _ _ [-> Vsw]; set fsw := finfun [eta fs with i1 |-> f i0].
step=>_; exists (swnx i); do!split=>//=.
suff: fsw = pffun (swnx i) f by move=>->.
rewrite /fsw /fs /swnx; apply/ffunP=>/= x; rewrite !ffunE /= ffunE /=.
case: tpermP=>[->|->|/eqP/negbTE->/eqP/negbTE->] //; rewrite eqxx //.
by rewrite /i1 eq_sym (negbTE (So_WoN i)).
Qed.

Opaque cas_next.

Definition bubble_pass_loop (a : {array 'I_n.+2 -> A}) :=
  forall isw : 'I_n.+1 * bool,
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => h \In Array.shape a f /\
                  (* if no swaps have happened yet, the prefix is sorted *)
                  ~~ isw.2 ==> sorted oleq (&:(fgraph f) `]-oo, isw.1 : nat]),
        [vfun (b : bool) h =>
          exists (p : 'S_n.+2),
            [/\ h \In Array.shape a (pffun p f),
                isw.2 ==> b &
                ~~ b ==> (p == 1%g) && sorted oleq (fgraph f)]]).

Program Definition bubble_pass (a : {array 'I_n.+2 -> A}) :
  {f : {ffun 'I_n.+2 -> A}},
  STsep (Array.shape a f,
         [vfun (b : bool) h =>
           exists (p : 'S_n.+2),
             h \In Array.shape a (pffun p f) /\
             ~~ b ==> (p == 1%g) && sorted oleq (fgraph f)]) :=
  Do (let go := Fix (fun (loop : bubble_pass_loop a) '(i, sw) =>
                  Do (sw0 <-- cas_next a i;
                      let sw1 := sw || sw0 in
                      if decP (b := i < n) idP is left pf
                        then loop (Sbo (i:=i) pf, sw1)
                        else ret sw1))
      in go (ord0, false)).
Next Obligation.
move=>a loop _ i sw [f][] h /= [H Hs].
set i0 := Wo i; set i1 := So i.
apply: [stepE f]=>//= sw0 m [p][{}H Hsw]; case: decP=>Hin.
- (* i < n, recursive call *)
  apply: [gE (pffun p f)]=>//=.
  - (* precondition *)
    split=>//; rewrite negb_or andbC Sbo_eq.
    case: sw0 Hsw=>//=; case=>{p H}-> Hf; rewrite pffunE1.
    (* swap didn't happen in this iteration *)
    apply/(implyb_trans Hs)/implyP=>{Hs}.
    (* swap didn't happen before *)
    by apply: codom1_sortedS.
  move=>v m0; case: sw0 Hsw=>/= [_|[-> _]]; last by rewrite orbF pffunE1.
  (* swap happened in this iteration *)
  rewrite orbT /=; case=>[p'][Hm0 {v}->/= _] _; rewrite implybT.
  by exists (p' * p)%g; split=>//; rewrite pffunEM.
(* i = n, last iteration *)
have {}Hin : nat_of_ord i = n.
- apply/eqP; rewrite eqn_leq; move: (ltn_ord i); rewrite ltnS=>->/=.
  by move/negP: Hin; rewrite -leqNgt.
step=>Vm; exists p; split=>//; first by apply/implyP=>->.
(* swap didn't happen in last iteration, check initial flag *)
case: sw0 Hsw=>/=; first by rewrite orbT.
(* flag wasn't set, so the pass didn't swap anything - the array is sorted *)
case=>-> Hf; rewrite orbF eqxx /=; apply/(implyb_trans Hs)/implyP=>{}Hs.
rewrite (slice_usize (codom f)) size_codom /= card_ord slice_oSR -[X in `]-oo, X.+1]]Hin.
by apply: codom1_sortedS Hs.
Qed.
Next Obligation.
move=>a [f][] h /= H.
apply: [gE f]=>//= [|v m [p][Hm _ Hv] _]; last by exists p.
split=>//; apply: sorted1.
by rewrite slice_size /= add0n subn0 size_codom /= card_ord.
Qed.

Opaque bubble_pass.

Definition bubble_sort_loop (a : {array 'I_n.+2 -> A}) : Type :=
  unit ->
  {f : {ffun 'I_n.+2 -> A}},
  STsep (Array.shape a f,
        [vfun (_ : unit) h =>
           exists (p : 'S_n.+2),
             h \In Array.shape a (pffun p f) /\
             sorted oleq (fgraph (pffun p f))]).

Program Definition bubble_sort (a : {array 'I_n.+2 -> A}) : bubble_sort_loop a :=
  Fix (fun (go : bubble_sort_loop a) _ =>
    Do (sw <-- bubble_pass a;
        if sw
          then go tt : ST _
          else skip)).
Next Obligation.
move=>a go _ [f][] h /= [E V].
apply: [stepE f]=>//; case=>m /=.
- (* the pass did swap something, loop *)
  case=>p [Hm _].
  apply: [gE (pffun p f)]=>//= _ m2 [p'][H2 Hs] _.
  by exists (p' * p)%g; rewrite pffunEM.
(* no swaps happened, exit *)
case=>p [Hm /= /andP [/eqP Ep Hs]]; rewrite {p}Ep in Hm.
by step=>_; exists 1%g; split=>//; rewrite pffunE1.
Qed.

End Bubble.

Section BubbleOpt.
Variable (n : nat) (A : ordType).

Opaque cas_next.

(*******************)
(* optimization #1 *)
(*******************)

(**********************************************************)
(* making each pass smaller by dropping 1 last element    *)
(* pseudocode, reusing cas_next:                          *)
(*                                                        *)
(* let bubble_pass_opt (a : array A) (k : nat) : bool =   *)
(*   let go (i : nat) (sw : bool) : bool = {              *)
(*     let sw1 = sw || cas_next a i;                      *)
(*     if i < k then go (i+1) sw1 else sw1                *)
(*   };                                                   *)
(*   go 0 false                                           *)
(*                                                        *)
(* let bubble_sort_opt (a : array A) : unit =             *)
(*   let go (k : nat) : unit = {                          *)
(*     if bubble_pass_opt a k then go (k-1) else ()       *)
(*   };                                                   *)
(*   go ((size a)-2).                                     *)
(**********************************************************)

Definition bubble_pass_opt_loop (a : {array 'I_n.+2 -> A}) (k : 'I_n.+1) :=
  forall isw : 'I_n.+1 * bool,
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => [/\ h \In Array.shape a f,
                      (* all elements before f(k+2) are smaller than it *)
                      allrel oleq (&:(fgraph f) `]-oo, k.+1])
                                  (&:(fgraph f) `]k.+1, +oo[),
                      (* and the suffix is sorted *)
                      sorted oleq (&:(fgraph f) `]k.+1, +oo[),
                      (* we don't touch it *)
                      isw.1 <= k,
                      (* all elements before f(i) are smaller than it *)
                      all (oleq^~ (f (Wo isw.1))) (&:(fgraph f) `]-oo, isw.1 : nat[) &
                      ~~ isw.2 ==> sorted oleq (&:(fgraph f) `]-oo, isw.1 : nat[)],
        [vfun (b : bool) h =>
          exists (p : 'S_n.+2), let f' := pffun p f in
          [/\ h \In Array.shape a f',
              isw.2 ==> b &
              if b then
                allrel oleq (&:(fgraph f') `]-oo, k : nat])
                            (&:(fgraph f') `]k : nat, +oo[) &&
                sorted oleq (&:(fgraph f') `]k : nat, +oo[)
              else (p == 1%g) && sorted oleq (fgraph f)]]).

Program Definition bubble_pass_opt (a : {array 'I_n.+2 -> A}) (k : 'I_n.+1) :
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => [/\ h \In Array.shape a f,
                      allrel oleq (&:(fgraph f) `]-oo, k.+1])
                                  (&:(fgraph f) `]k.+1, +oo[) &
                      sorted oleq (&:(fgraph f) `]k.+1, +oo[)],
          [vfun (b : bool) h =>
            exists (p : 'S_n.+2), let f' := pffun p f in
              h \In Array.shape a f' /\
              if b then
                allrel oleq (&:(fgraph f') `]-oo, k : nat])
                            (&:(fgraph f') `]k : nat, +oo[) &&
                sorted oleq (&:(fgraph f') `]k : nat, +oo[)
              else (p == 1%g) && sorted oleq (fgraph f)]) :=
  Do (let go := Fix (fun (loop : bubble_pass_opt_loop a k) '(i, sw) =>
                  Do (sw0 <-- cas_next a i;
                      let sw1 := sw || sw0 in
                      if decP (b := i < k) idP is left pf
                        then loop (Sbo (i:=i) pf, sw1)
                        else ret sw1))
      in go (ord0, false)).
Next Obligation.
(* Sbo is always safe *)
move=>_ k _ _ i _ _ /= E; rewrite E ltnS; symmetry.
by apply: (leq_trans E); rewrite -ltnS; apply: ltn_ord.
Qed.
Next Obligation.
move=>a k loop _ i sw [f][] h /= [H Hak Hsk Hik Hai Hsi].
set i0 := Wo i; set i1 := So i.
apply: [stepE f]=>//= sw0 m [p][Hm Hsw]; case: decP=>{}H.
- (* i < k, recursive call *)
  apply: [gE (pffun p f)]=>//=.
  - (* precondition *)
    rewrite Sbo_eq Wo_Sbo_eq negb_or slice_oSR.
    case: sw0 Hsw=>/=; case=>Ep Hf; rewrite {p}Ep ?pffunE1 in Hm *.
    - (* swap happened before the call *)
      rewrite andbF /= swnx_oa //; split=>//.
      - rewrite (@allrel_in_l _ _ _ _ &:(codom f) `]-oo, k.+1] ) //.
        by apply/perm_mem; rewrite perm_sym; apply: perm_swnx_ux.
      by rewrite swnx_ux_rcons all_rcons swnxE2 Hai andbT; apply: ordW.
    (* swap didn't happen before the call *)
    rewrite andbT codom1_ax_rcons; split=>//.
    - rewrite all_rcons Hf /=.
      by apply/sub_all/Hai=>z /otrans; apply.
    apply/(implyb_trans Hsi)/implyP.
    by rewrite (sorted_rconsE _ _ (@otrans A)) Hai.
  move=>v m0; case: sw0 Hsw=>/= [_|[-> _]]; last by rewrite orbF pffunE1.
  (* swap happened *)
  rewrite orbT /=; case=>p'[Hm0 {v}-> Has] _.
  by exists (p' * p)%g; rewrite implybT pffunEM.
(* i = k, exit *)
have {H}Hik : nat_of_ord i = k.
- apply/eqP; rewrite eqn_leq Hik /=.
  by move/negP: H; rewrite -leqNgt.
step=>Vm; exists p; split=>//; first by apply/implyP=>->.
rewrite -Hik in Hak Hsk *; rewrite slice_oSL.
case: sw0 Hsw=>/=; case=>-> Hf.
- (* swap happened on last iteration *)
  rewrite orbT swnx_xu_cons /=; apply/andP; split.
  - rewrite swnx_ux_rcons allrel_rconsl allrel_consr /=.
    move: Hak; rewrite codom1_ax_rcons2 // !allrel_rconsl -/i0 -/i1 -andbA.
    by case/and3P=>-> _ ->; rewrite (ordW Hf) /= !andbT.
  rewrite (path_sortedE (@otrans A)) Hsk andbT.
  apply/allP=>z Hz; move/allrelP: Hak; apply=>//.
  by rewrite codom1_ax_rcons2 // 4!(mem_rcons, inE) eqxx /= orbT.
(* swap didn't happen on last iteration *)
rewrite orbF pffunE1 eqxx /=; case: sw Hsi=>/=[_|].
- (* flag was set *)
  apply/andP; split.
  - rewrite codom1_ax_rcons // codom1_xu_cons allrel_rconsl allrel_consr /=.
    move: Hak; rewrite codom1_ax_rcons2 // !allrel_rconsl -andbA -/i0 -/i1.
    case/and3P=>->-> _; rewrite Hf /= !andbT.
    by apply/sub_all/Hai=>z /otrans; apply.
  rewrite codom1_xu_cons /= (path_sortedE (@otrans A)) Hsk andbT.
  by move: Hak; rewrite codom1_ax_rcons2 // !allrel_rconsl -andbA; case/and3P.
(* flag wasn't set, so the pass didn't swap anything - the array is sorted *)
move=>Hs2; rewrite (codom1_split f i) -/i0 -/i1 /=; rewrite Hik in Hai Hs2 Hsk *.
rewrite (sorted_pairwise (@otrans A)) pairwise_cat /= -!(sorted_pairwise (@otrans A)).
rewrite Hf Hsk Hs2 /= andbT !allrel_consr -!andbA Hai /=.
move: Hak; rewrite -Hik codom1_ax_rcons2 // !allrel_rconsl -andbA; case/and3P=>->->->/=.
by rewrite andbT Hik; apply/sub_all/Hai=>z /otrans; apply.
Qed.
Next Obligation.
move=>a k [f][] h /= [H Ha Hs].
apply: [gE f]=>//= [|v m [p][Hm _ Hv] _]; last by exists p.
by rewrite itv_under0R.
Qed.

Opaque bubble_pass_opt.

Definition bubble_sort_opt_loop (a : {array 'I_n.+2 -> A}) : Type :=
  forall (k : 'I_n.+1),
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => [/\ h \In Array.shape a f,
                      allrel oleq (&:(fgraph f) `]-oo, k.+1])
                                  (&:(fgraph f) `]k.+1, +oo[) &
                      sorted oleq (&:(fgraph f) `]k.+1, +oo[)],
        [vfun (_ : unit) h =>
          exists (p : 'S_n.+2), let f' := pffun p f in
            h \In Array.shape a f' /\
            sorted oleq (fgraph f')]).

Program Definition bubble_sort_opt (a : {array 'I_n.+2 -> A}) :
  {f : {ffun 'I_n.+2 -> A}},
  STsep (Array.shape a f,
        [vfun (_ : unit) h =>
          exists (p : 'S_n.+2),
            h \In Array.shape a (pffun p f) /\
            sorted oleq (fgraph (pffun p f))]) :=
  Do (let go := Fix (fun (loop : bubble_sort_opt_loop a) k =>
                     Do (sw <-- bubble_pass_opt a k;
                         if sw
                           then loop (Po k) : ST _
                           else skip))
      in go ord_max).
Next Obligation.
move=>a go k [f][] h /= [H Ha Hs].
apply: [stepE f]=>{H Ha Hs}//=; case=>m; case=>p [Hm /andP [H Hs]]; last first.
- (* id permutation *)
  rewrite {p H}(eqP H) in Hm.
  by step=>_; exists 1%g; split=>//; rewrite pffunE1.
apply: [gE (pffun p f)]=>//=; last first.
- by move=> _ m2 [p'][H2 Hs'] _; exists (p' * p)%g; rewrite pffunEM.
rewrite Po_eq; case: (posnP k)=>Hk; last by rewrite (prednK Hk).
move: H Hs; rewrite {}Hk /=.
rewrite slice_oSL (_ : 1 = (@nat_of_ord n.+1 ord0).+1) // codom1_xu_cons /=
  (path_sortedE (@otrans A)) allrel_consr.
case/andP=>_ Ha1; case/andP=>Ha2 Hs; split=>//.
rewrite (_ : (codom (pffun p f)) = fgraph (pffun p f)) //.
have P : 1 < n.+2 := ltn0Sn n; rewrite {1}(_ : 1 = Ordinal P) //.
rewrite codom_ux_rcons /= allrel_rconsl Ha1 /=.
by have -> //: Ordinal P = @Ordinal n.+2 1 (ltn0Sn n); apply/ord_inj.
Qed.
Next Obligation.
move=>a [f][] h /= [E V].
have Hs: size (codom f) <= n.+2 by rewrite size_codom /= card_ord.
apply: [gE f]=>//=; split=>//; rewrite (@itv_overL _ _ (BRight n.+1)) //=;
  try by rewrite addn1.
by exact: allrel0r.
Qed.

End BubbleOpt.

Section BubbleOpt2.
Variable (n : nat) (A : ordType).

Opaque cas_next.

(*******************)
(* optimization #2 *)
(*******************)

(********************************************************)
(* ignoring all unswapped end elements on each pass     *)
(* pseudocode, reusing cas_next:                        *)
(*                                                      *)
(* let bubble_pass_opt2 (a : array A) (k : nat) : nat = *)
(*   let go (i : nat) (ls : nat) : nat = {              *)
(*     let ls1 = if cas_next a i then i+1 else ls;      *)
(*     if i < k then go (i+1) ls1 else ls1              *)
(*   };                                                 *)
(*   go 0 k                                             *)
(*                                                      *)
(* let bubble_sort_opt2 (a : array A) : unit =          *)
(*   let go (k : nat) : unit = {                        *)
(*     let k1 = bubble_pass_opt2 a k;                   *)
(*     if 1 < k1 then go (k1 - 2) else ()               *)
(*   };                                                 *)
(*   go (size a - 2).                                   *)
(********************************************************)

Definition bubble_pass_opt2_loop (a : {array 'I_n.+2 -> A}) (k : 'I_n.+1) :=
  forall ils : 'I_n.+1 * 'I_n.+2,
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => [/\ h \In Array.shape a f,
                      allrel oleq (&:(fgraph f) `]-oo, k.+1])
                                  (&:(fgraph f) `]k.+1, +oo[),
                      sorted oleq (&:(fgraph f) `]k.+1, +oo[),
                      ils.2 <= ils.1 <= k,
                      allrel oleq (&:(fgraph f) `]-oo, ils.2 : nat[)
                                  (&:(fgraph f) `[ils.2 : nat, ils.1 : nat]) &
                      sorted oleq (&:(fgraph f) `[ils.2 : nat, ils.1 : nat])],
        [vfun (j : 'I_n.+2) h =>
          exists (p : 'S_n.+2), let f' := pffun p f in
            [/\ h \In Array.shape a f',
                ils.2 <= j,
                allrel oleq (&:(fgraph f') `]-oo, j : nat[)
                            (&:(fgraph f') `[j : nat, +oo[) &
                sorted oleq (&:(fgraph f') `[j : nat, +oo[)]]).

Program Definition bubble_pass_opt2 (a : {array 'I_n.+2 -> A}) (k : 'I_n.+1) :
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => [ /\ h \In Array.shape a f,
                       allrel oleq (&:(fgraph f) `]-oo, k.+1])
                                   (&:(fgraph f) `]k.+1, +oo[) &
                       sorted oleq (&:(fgraph f) `]k.+1, +oo[)],
          [vfun (j : 'I_n.+2) h =>
            exists (p : 'S_n.+2), let f' := pffun p f in
              [/\ h \In Array.shape a f',
                  allrel oleq (&:(fgraph f') `]-oo, j : nat[)
                              (&:(fgraph f') `[j : nat, +oo[) &
                  sorted oleq (&:(fgraph f') `[j : nat, +oo[)]]) :=
  Do (let go := Fix (fun (loop : bubble_pass_opt2_loop a k) '(i, ls) =>
                  Do (sw <-- cas_next a i;
                      let ls1 := if sw then So i else ls in
                      if decP (b := i < k) idP is left pf
                        then loop (Sbo (i:=i) pf, ls1)
                        else ret ls1))
      in go (ord0, ord0)).
Next Obligation.
(* show that Sbo is always safe *)
move=>_ k _ _ i _ _ /= E; rewrite E ltnS; symmetry.
by apply: (leq_trans E); rewrite -ltnS; apply: ltn_ord.
Qed.
Next Obligation.
move=>a k loop _ i ls [f][] h /= [Hs Hak Hsk /andP [Hils Hik] Hai Hsi].
set i0 := Wo i; set i1 := So i.
apply: [stepE f]=>//= sw m [p][Hm Hsw]; case: decP=>H.
- (* i < k, recursive call *)
  apply: [gE (pffun p f)]=>//=.
  - (* precondition *)
    rewrite Sbo_eq.
    case: sw Hsw=>/=; case=>Ep Hf; rewrite {p}Ep ?pffunE1 in Hm *.
    - (* swap happened before the call *)
      rewrite So_eq swnx_oa; last by rewrite ltnS; apply: ltnW.
      rewrite swnx_Skk /=; split=>//.
      - rewrite (@allrel_in_l _ _ _ _ &:(codom f) `]-oo, k.+1]) //.
        by apply/perm_mem; rewrite perm_sym; apply: perm_swnx_ux.
      - by rewrite ltnS leqnn.
      rewrite allrel1r slice_oSR (@slice_split _ _ true ls); last by rewrite in_itv.
      rewrite /= all_cat; apply/andP; split.
      - rewrite swnx_ao //; move: Hai.
        by rewrite codom1_ax_rcons // allrel_rconsr; case/andP.
      rewrite codom1_ax_rcons // swnxE1 all_rcons (ordW Hf) /=.
      suff ->: &:(codom (pffun (swnx i) f)) `[ls : nat, i : nat[ =
               &:(codom f) `[ls : nat, i : nat[.
      - rewrite codom1_ax_rcons // (sorted_rconsE _ _ (@otrans A)) in Hsi.
        by case/andP: Hsi=>Ha1.
      by apply: swnx_ao.
    (* swap didn't happen before the call *)
    split=>//.
    - by apply/andP; split=>//; apply: ltnW.
    - rewrite codom1_ax_rcons2 // allrel_rconsr -codom1_ax_rcons // Hai /=.
      suff: all (oleq^~ (f (Wo i))) (&:(codom f) `]-oo, ls:nat[).
      - by apply/sub_all=>z /otrans; apply.
      by move: Hai; rewrite codom1_ax_rcons // allrel_rconsr; case/andP.
    rewrite codom1_ax_rcons2 // (sorted_rconsE _ _ (@otrans A)) -{2}codom1_ax_rcons // Hsi andbT.
    rewrite all_rcons Hf /=.
    move: Hsi; rewrite codom1_ax_rcons // (sorted_rconsE _ _ (@otrans A)).
    by case/andP=>+ _; apply/sub_all=>z Hz; apply/otrans/Hf.
  move=>j m0; case: sw Hsw=>/= [_|[-> _]]; last by rewrite pffunE1.
  (* swap happened *)
  case=>[p'][Hm0 Hji Ha' Hs'] _.
  exists (p' * p)%g; rewrite pffunEM; split=>//.
  by apply/leq_trans/Hji; rewrite So_eq; apply: ltnW.
(* i = k, exit *)
have {H}Hik : nat_of_ord i = k.
- apply/eqP; rewrite eqn_leq Hik /=.
  by move/negP: H; rewrite -leqNgt.
rewrite -{loop k}Hik in Hak Hsk *.
step=>Vm; exists p; case: sw Hsw=>/=; case=>Ep Hf.
- (* swap happened on last iteration *)
  rewrite So_eq; split=>//=; first by apply: ltnW.
  - rewrite Ep slice_oSR swnx_ux_rcons swnx_xu_cons allrel_rconsl allrel_consr /=.
    move: Hak; rewrite codom1_ax_rcons2 // !allrel_rconsl -/i0 -/i1 -andbA.
    case/and3P=>-> _ ->; rewrite (ordW Hf) /= !andbT.
    move: Hai; rewrite codom1_ax_rcons //= allrel_rconsr; case/andP=>_ Hals.
    move: Hsi; rewrite codom1_ax_rcons // sorted_rconsE //; case/andP =>Halsi _.
    move: Hils; rewrite leq_eqVlt; case/orP=>[/eqP <-|Hlsi] //.
    rewrite (@slice_split _ _ true ls); last by rewrite in_itv.
    by rewrite /= all_cat Hals.
  rewrite Ep swnx_xu_cons /= (path_sortedE (@otrans A)) Hsk andbT.
  by move: Hak; rewrite codom1_ax_rcons2 // !allrel_rconsl -!andbA; case/and3P.
(* swap didn't happen on last iteration *)
rewrite {p}Ep pffunE1 /= in Hm *.
rewrite (@slice_split _ _ false i `[ls:nat, +oo[); last by rewrite in_itv /= andbT.
split=>//=.
- rewrite allrel_catr Hai /= slice_oSL codom1_xu_cons allrel_consr; apply/andP; split.
  - suff: all (oleq^~ (f (Wo i))) (&:(codom f) `]-oo, ls:nat[).
    - by apply/sub_all=>z /otrans; apply.
    apply/sub_all/Hai=>z /allP; apply.
    by rewrite codom1_ax_rcons // mem_rcons inE eqxx.
  apply/allrel_sub_l/Hak/slice_subset.
  by rewrite subitvE /= bnd_simp leEnat; apply/ltnW.
rewrite (sorted_pairwise (@otrans A)) pairwise_cat -!(sorted_pairwise (@otrans A)) Hsi /=.
rewrite slice_oSL codom1_xu_cons /= allrel_consr -andbA; apply/and3P; split.
- move: Hsi; rewrite (sorted_pairwise (@otrans A)) codom1_ax_rcons // pairwise_rcons.
  case/andP=>H' _; rewrite all_rcons Hf /=.
  by apply/sub_all/H'=>z Hz; apply/otrans/Hf.
- apply/allrel_sub_l/Hak/slice_subset.
  by rewrite subitvE /= bnd_simp leEnat.
rewrite (path_sortedE (@otrans A)) Hsk andbT.
by move: Hak; rewrite codom1_ax_rcons2 // !allrel_rconsl -!andbA; case/and3P.
Qed.
Next Obligation.
move=>a k [f][] h /= [H Ha Hs].
apply: [gE f]=>//= [|v m [p][Hm _ {}Ha {}Hs] _]; last by exists p.
split=>//; first by rewrite itv_underR.
by apply: sorted1; rewrite slice_size size_codom card_ord.
Qed.

Opaque bubble_pass_opt2.

Definition bubble_sort_opt2_loop (a : {array 'I_n.+2 -> A}) : Type :=
  forall (k : 'I_n.+1),
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => [/\ h \In Array.shape a f,
                        allrel oleq (&:(fgraph f) `]-oo, k.+1])
                                    (&:(fgraph f) `]k.+1, +oo[) &
                        sorted oleq (&:(fgraph f) `]k.+1, +oo[)],
        [vfun (_ : unit) h =>
          exists (p : 'S_n.+2), let f' := pffun p f in
            h \In Array.shape a f' /\
            sorted oleq (fgraph f')]).

Program Definition bubble_sort_opt2 (a : {array 'I_n.+2 -> A}) :
  {f : {ffun 'I_n.+2 -> A}},
  STsep (Array.shape a f,
         [vfun (_ : unit) h =>
           exists (p : 'S_n.+2), let f' := pffun p f in
             h \In Array.shape a f' /\
             sorted oleq (fgraph f')]) :=
  Do (let go := Fix (fun (loop : bubble_sort_opt2_loop a) k =>
                     Do (k1 <-- bubble_pass_opt2 a k;
                         if decP (b := 1 < k1) idP is left pf
                           then loop (M2lo (i:=k1) pf) : ST _
                           else skip))
      in go ord_max).
Next Obligation.
move=>a go k [f][] h /= [H Ha Hs].
apply: [stepE f]=>{Ha Hs}//= x m [p][Hm Ha Hs].
case: decP=>Hx; last first.
- step=>Vm; exists p; split=>//.
  move/negP: Hx; rewrite -leqNgt; case: (posnP x).
  - by move=>Hx _; rewrite Hx -slice_0L slice_uu in Hs.
  case: (nat_of_ord x) Ha Hs=>//; case=>//= Ha1 Hs1 _ _.
  rewrite (slice_uoxu (codom (pffun p f)) 1).
  rewrite (sorted_pairwise (@otrans A)) pairwise_cat -!(sorted_pairwise (@otrans A)).
  by apply/and3P; split=>//; apply: sorted1; rewrite slice_size size_codom card_ord.
apply: [gE (pffun p f)]=>//=; last first.
- move=> _ m2 [p'][H2 Hs'] _; exists (p' * p)%g.
  by rewrite pffunEM.
rewrite slice_oSL -slice_oSR (M2lo_eq Hx); suff: x.-2.+2 = x by move=>->.
by rewrite -subn2 -addn2 addnBAC // addnK.
Qed.
Next Obligation.
move=>a [f][] h /= [E V].
apply: [gE f]=>//=.
rewrite (@itv_overL _ _ _ +oo) /=; first by split=>//; exact: allrel0r.
by rewrite leEnat addn1 size_codom /= card_ord.
Qed.

End BubbleOpt2.
