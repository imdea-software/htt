(*
Copyright 2022 IMDEA Software Institute
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

From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype tuple finfun finset.
From mathcomp Require Import fingroup perm.
From mathcomp Require Import interval.
From pcm Require Import options axioms prelude seqext pred ordtype slice.
From pcm Require Import pcm unionmap heap.
From htt Require Import options model heapauto.
From htt Require Import array.

(* hack to avoid "_ *p _" notation clash *)
From mathcomp Require order.
Import order.Order.NatOrder order.Order.TTheory.

(* TODO added to mathcomp > 1.16 *)
Lemma perm_on_id {T : finType} (u : {perm T}) (S : {set T}) :
        perm_on S u -> 
        #|S| <= 1 -> 
        u = 1%g.
Proof.
rewrite leq_eqVlt ltnS leqn0 => pSu S10; apply/permP => t; rewrite perm1.
case/orP : S10; last first.
  by move/eqP/cards0_eq => S0; apply: (out_perm pSu); rewrite S0 inE.
move=> /cards1P[x Sx].
have [-> | ntx] := eqVneq t x; last by apply: (out_perm pSu); rewrite Sx inE.
by apply/eqP; have := perm_closed x pSu; rewrite Sx !inE => ->.
Qed.

Lemma perm_onC {T : finType} (S1 S2 : {set T}) (u1 u2 : {perm T}) :
        perm_on S1 u1 -> 
        perm_on S2 u2 ->
        [disjoint S1 & S2] ->
        commute u1 u2.
Proof.
move=> pS1 pS2 S12; apply/permP => t; rewrite !permM.
case/boolP : (t \in S1) => tS1.
  have /[!disjoint_subset] /subsetP {}S12 := S12.
  by rewrite !(out_perm pS2) //; apply: S12; rewrite // perm_closed.
case/boolP : (t \in S2) => tS2.
  have /[1!disjoint_sym] /[!disjoint_subset] /subsetP {}S12 := S12.
  by rewrite !(out_perm pS1) //; apply: S12; rewrite // perm_closed.
by rewrite (out_perm pS1) // (out_perm pS2) // (out_perm pS1).
Qed.

Lemma tperm_on {T : finType} (x y : T) : 
        perm_on [set x; y] (tperm x y).
Proof.
by apply/subsetP => z /[!inE]; case: tpermP => [->|->|]; rewrite eqxx // orbT.
Qed.

(* TODO added to fcsl-pcm *)
Lemma slice_oPR {A : Type} a x (s : seq A) :
        0 < x ->
        &:s (Interval a (BRight x.-1)) = &:s (Interval a (BLeft x)).
Proof. by move=>Hx; rewrite -{2}(prednK Hx) slice_oSR. Qed.

Lemma slice_FR {A : Type} (s : seq A) x : 
        &:s (Interval x +oo) = &:s (Interval x (BLeft (size s))).
Proof. by rewrite /slice.slice /= addn0. Qed.

Lemma slice_extrude {A : Type} (s : seq A) (i : interval nat) :
        order.Order.lt i.1 i.2 ->
        s = &:s (Interval -oo i.1) ++ &:s i ++ &:s (Interval i.2 +oo).
Proof.
case: i=>[[[] i|[]][[] j|[]]] //=; rewrite bnd_simp=>H;
  rewrite ?itv_minfR ?itv_pinfL /= ?cats0.
- by rewrite -{1}(slice_uu s) (slice_split _ true (x:=i)) //=
    (slice_split _ true (x:=j) (i:=`[i, +oo[)) //= in_itv /= andbT; apply/ltnW.
- by rewrite -{1}(slice_uu s) (slice_split _ true (x:=i)) //=
    (slice_split _ false (x:=j) (i:=`[i, +oo[)) //= in_itv /= andbT.
- by rewrite -{1}(slice_uu s) (slice_split _ true (x:=i)).
- by rewrite -{1}(slice_uu s) (slice_split _ false (x:=i)) //=
    (slice_split _ true (x:=j) (i:=`]i, +oo[)) //= in_itv /= andbT.
- by rewrite -{1}(slice_uu s) (slice_split _ false (x:=i)) //=
    (slice_split _ false (x:=j) (i:=`]i, +oo[)) //= in_itv /= andbT.
- by rewrite -{1}(slice_uu s) (slice_split _ false (x:=i)).
- by rewrite -{1}(slice_uu s) (slice_split _ true (x:=j)).
- by rewrite -{1}(slice_uu s) (slice_split _ false (x:=j)).
by rewrite slice_uu.
Qed.

(****)

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

(* increase by 1 within the bound *)
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

(* increase by 1 with saturation *)
Definition Sso n (i : 'I_n) : 'I_n.
Proof.
case: i=>/= m Hm; case: (ltnP m.+1 n)=>[H|_].
- by apply: (@Ordinal _ m.+1 H).
by apply: (@Ordinal _ m Hm).
Defined.

Lemma Sso_eq n (i : 'I_n) : nat_of_ord (Sso i) = if (i.+1 < n)%N then i.+1 else i.
Proof. by case: i=>/= m prf; case: ltnP. Qed.

(* decrease by 1 *)
Definition Po n : 'I_n -> 'I_n :=
  fun '(@Ordinal _ m prf) => @Ordinal n m.-1 (leq_ltn_trans (leq_pred _) prf).

Lemma Po_eq n (i : 'I_n) : nat_of_ord (Po i) = i.-1.
Proof. by case: i. Qed.

End OrdArith.

Section PermFgraph.
Variable (n : nat) (A : Type).

Lemma perm_on_notin (f : {ffun 'I_n -> A}) (p : 'S_n) (s : {set 'I_n}) (i : interval nat) :
        perm_on s p ->
        [disjoint s & [set x : 'I_n | (x : nat) \in i]] ->
        &:(fgraph (pffun p f)) i = &:(fgraph f) i.
Proof.
move=>Hp Hd.
suff E: {in &:(enum 'I_n) i, f =1 pffun p f}.
- by rewrite !fgraph_codom /= !codomE /= -2!slice_map /=; move/eq_in_map: E.
move=>/= y Hy; rewrite ffunE (@out_perm _ s) //.
apply/negbT/(disjointFl Hd); rewrite inE in_itv.
case: {Hd}i Hy=>i j; rewrite slice_memE1 /=; last first.
- by rewrite count_uniq_mem; [exact: leq_b1|exact: enum_uniq].
case/and3P=>_; rewrite size_enum_ord index_enum_ord.
case: j=>[[] jx|[]]; case: i=>[[] ix|[]];
  rewrite ?andbF ?andbT /= ?addn0 ?addn1 // leEnat ltEnat /=.
- by move=>->.
- by move=>->.
- by rewrite leqNgt (ltn_ord y).
- by move=>->.
- by move=>->.
- by rewrite leqNgt (ltn_ord y).
by rewrite leqNgt (ltn_ord y).
Qed.

Corollary tperm_notin (f : {ffun 'I_n -> A}) (x y : 'I_n) (i : interval nat) :
            (x : nat) \notin i -> (y : nat) \notin i ->
            &:(fgraph (pffun (tperm x y) f)) i = &:(fgraph f) i.
Proof.
move=>Hx0 Hx1.
apply: perm_on_notin; first by exact: tperm_on.
rewrite disjoint_subset; apply/subsetP=>/= z; rewrite 6!inE.
by case/orP=>/eqP->.
Qed.

End PermFgraph.

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

Lemma perm_on_fgraph (i : interval nat) (p : 'S_n) (f : {ffun 'I_n -> A}) :
  perm_on [set x : 'I_n | (x : nat) \in i] p ->
  perm_eq &:(fgraph (pffun p f)) i
          &:(fgraph          f ) i.
Proof.
case: i=>i j H.
case/boolP: (order.Order.lt i j)=>[Hij|]; last first.
- by rewrite -leNgt => H12; rewrite !itv_swapped_bnd.
move: (perm_fgraph p f).
rewrite {1}(slice_extrude (fgraph (pffun p f)) (i:=Interval i j)) //=.
rewrite {1}(slice_extrude (fgraph f) (i:=Interval i j)) //=.
rewrite (perm_on_notin (i:=Interval -oo i) f H); last first.
- rewrite disjoint_subset; apply/subsetP=>/= z.
  rewrite inE=>Hz; rewrite 2!inE; apply/negP=>Hz2.
  suff: (z : nat) \notin order.Order.meet (Interval -oo i) (Interval i j).
  - by move/negP; apply; rewrite in_itvI Hz2.
  rewrite /order.Order.meet /= /order.Order.join /= /order.Order.meet /=.
  move/ltW: Hij; rewrite bound_leEmeet=>/eqP->.
  by rewrite itv_ge // -leNgt.
rewrite (perm_on_notin (i:=Interval j +oo) f H); last first.
- rewrite disjoint_subset; apply/subsetP=>/= z.
  rewrite inE=>Hz; rewrite 3!inE; apply/negP=>Hz2.
  suff: (z : nat) \notin order.Order.meet (Interval i j) (Interval j +oo).
  - by move/negP; apply; rewrite in_itvI Hz.
  rewrite /order.Order.meet /= /order.Order.meet /=.
  move: (bound_lex1 j); rewrite bound_leEmeet=>/eqP->.
  move/ltW: Hij; rewrite leEjoin=>/eqP->.
  by rewrite itv_ge // -leNgt.
by rewrite /= perm_cat2l perm_cat2r.
Qed.

End PermFgraphEq.

Section Lomuto.
Variable (n : nat) (A : ordType).

(***************************************************)
(* pseudocode in idealized effectful ML-like lang  *)
(* assuming size a >= 1                            *)
(*                                                 *)
(* let swap (a : array A) (i j : nat) : unit =     *)
(*   if i == j then () else                        *)
(*     let x = array.read a i;                     *)
(*     let y = array.read a j;                     *)
(*     array.write a i y;                          *)
(*     array.write a j x                           *)
(*                                                 *)
(* let partition_lm_pass (a : array A) (pivot : A) *)
(*                       (lo hi : nat) : nat =     *)
(*   let go (i j : nat) : nat = {                  *)
(*     let x = array.read a j;                     *)
(*     if x <= pivot then {                        *)
(*       swap a i j;                               *)
(*       if j+1 < hi then go (i+1) (j+1) else i+1  *)
(*     } else if j+1 < hi then go i (j+1) else i   *)
(*   };                                            *)
(*   go lo lo                                      *)
(*                                                 *)
(* let partition_lm (a : array A)                  *)
(*                  (lo hi : nat) : nat =          *)
(*   let pivot = array.read a hi;                  *)
(*   let v = partition_lm_pass a pivot lo hi;      *)
(*   swap a v hi;                                  *)
(*   v                                             *)
(*                                                 *)
(* let quick_sort (a : array A) : unit =           *)
(*   let go (i j : nat) : unit =                   *)
(*     if j <= i then () else                      *)
(*       let v = partition_lm a i j;               *)
(*       loop (l, v-1);                            *)
(*       loop (v+1, h)                             *)
(*   };                                            *)
(*   go 0 (size a)-1                               *)
(***************************************************)

Opaque Array.write Array.read.

Program Definition swap (a : {array 'I_n -> A}) (i j : 'I_n) :
  STsep {f : {ffun 'I_n -> A}}
        (Array.shape a f,
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

Definition partition_lm_loop (a : {array 'I_n -> A}) (pivot : A) 
    (lo hi : 'I_n) :=
  forall ij : sigT (fun i : 'I_n => sig (fun j : 'I_n => i <= j /\ j < hi)),
  let i := projT1 ij in
  let j := proj1_sig (projT2 ij) in
  STsep {f : {ffun 'I_n -> A}}
        (fun h => [/\ h \In Array.shape a f,
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

Program Definition partition_lm_pass (a : {array 'I_n -> A}) (pivot : A) 
    (lo hi : 'I_n) (Hlo : lo < hi):
  STsep {f : {ffun 'I_n -> A}}
        (Array.shape a f,
        [vfun (v : 'I_n) h =>
          lo <= v <= hi /\
          exists p, let f' := pffun p f in
            [/\ perm_on [set ix : 'I_n | lo <= ix < hi] p,
                h \In Array.shape a f',
                all (oleq^~ pivot) (&:(fgraph f') `[lo : nat, v : nat[) &
                all (ord    pivot) (&:(fgraph f') `[v : nat, hi : nat[)]]) :=
  Do (let go :=
    ffix (fun (loop : partition_lm_loop a pivot lo hi) '(existT i (exist j (conj Hi Hj))) =>
      Do (x <-- Array.read a j;
          if oleq x pivot then
            swap a i j;;
            let i1 := Sbo (ord_trans (leq_ltn_trans Hi Hj)) in  (* i+1 *)
            let j1 := Sbo (ord_trans Hj) in                     (* j+1 *)
            if leq_choose Hj is right pf then
              loop (@existT _ _ i1 (@exist _ _ j1
                      (conj (Sbo_leq Hi Hj) (Sbo_lift Hj pf))))
              else ret i1
          else if leq_choose Hj is right pf then
                 let j1 := Sbo (ord_trans Hj) in                (* j+1 *)
                 loop (@existT _ _ i (@exist _ _ j1
                         (conj (Sbo_lt Hi Hj) (Sbo_lift Hj pf))))
            else ret i))
  in go (@existT _ _ lo (@exist _ _ lo (conj (leqnn lo) Hlo)))).
Next Obligation.
move=>a pivot lo hi Hlo loop _ i _ j _ Hi Hj [f][] h /= [H Oli Ai Aj].
apply: [stepE f, h]=>//= _ _ [->->].
case: oleqP=>Hfp.
- (* a[j] <= pivot, make swap *)
  apply: [stepE f]=>//= _ m Hm.
  case: (leq_choose Hj)=>Hj1.
  - (* j+1 = hi, exit *)
    step=>_; split.
    - rewrite Sbo_eq; apply/andP; split=>//.
      by apply/leq_ltn_trans/Hj.
    exists (tperm i j); rewrite Sbo_eq; split=>//.
    - rewrite -(eqP Hj1).
      apply/(subset_trans (tperm_on i j))/subsetP=>/= x; rewrite !inE ltnS.
      by case/orP=>/eqP->; rewrite leqnn // andbT.
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
    rewrite !onth_codom /=; case/andP=>Hpi Aj.
    rewrite all_rcons; apply/andP; split.
    - by rewrite ffunE tpermR.
    by rewrite tperm_notin ?slice_oSL //
      in_itv /= negb_and leEnat ltEnat /= -!leqNgt leqnn // orbT.
  (* j+1 < hi, loop *)
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
    rewrite !onth_codom /=; case/andP=>Hpi Aj.
    rewrite all_rcons; apply/andP; split.
    - by rewrite ffunE tpermR.
    by rewrite tperm_notin ?slice_oSL //
      in_itv /= negb_and leEnat ltEnat /= -!leqNgt leqnn // orbT.
  move=>z k [Hz][p'][Pk Hk Al Ah] Vk; split.
  - by move: Hz; rewrite Sbo_eq; case/andP=>/ltnW->->.
  exists (p' * tperm i j)%g; rewrite pffunEM; split=>//.
  rewrite Sbo_eq in Pk; apply: perm_onM.
  - apply/(subset_trans Pk)/subsetP=>x; rewrite !inE.
    by case/andP=>/ltnW->->.
  apply/(subset_trans (tperm_on i j))/subsetP=>/= x; rewrite !inE /=.
  case/orP=>/eqP->; last by apply/andP.
  by rewrite leqnn /=; apply/leq_ltn_trans/Hj.
(* pivot < a[j] *)
case: (leq_choose Hj)=>Hj1.
- (* j+1 = hi, exit *)
  step=>_; split.
  - by rewrite leqnn /= -(eqP Hj1); apply: ltnW.
  exists 1%g; rewrite pffunE1; split=>//; first by exact: perm_on1.
  rewrite -(eqP Hj1) slice_oSR slice_xR; last by rewrite bnd_simp.
  by rewrite onth_codom /= all_rcons Hfp.
(* j+1 < hi, loop *)
apply: [gE f]=>//=; split=>//.
rewrite Sbo_eq slice_oSR slice_xR; last by rewrite bnd_simp.
by rewrite onth_codom /= all_rcons Hfp.
Qed.
Next Obligation.
move=>/= a pivot lo hi Hlo [f][] i /= H.
by apply: [gE f]=>//=; split=>//; rewrite slice_kk.
Qed.

Opaque partition_lm_pass.

Program Definition partition_lm (a : {array 'I_n -> A}) 
    (lo hi : 'I_n) (Hlo : lo < hi):
  STsep {f : {ffun 'I_n -> A}}
        (Array.shape a f,
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
    apply/(subset_trans (tperm_on v hi))/subsetP=>/= x; rewrite !inE /=.
    by case/orP=>/eqP->//; rewrite leqnn andbT; apply/ltnW.
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
  STsep {f : {ffun 'I_n.+1 -> A}}
        (Array.shape a f,
        [vfun (_ : unit) h =>
           exists p, let f' := pffun p f in
             [/\ perm_on [set ix : 'I_n.+1 | lo <= ix <= hi] p,
                 h \In Array.shape a f' &
                 sorted oleq (&:(fgraph f') `[lo : nat, hi : nat])]]).

Program Definition quicksort_lm (a : {array 'I_n.+1 -> A}) :
  STsep {f : {ffun 'I_n.+1 -> A}}
        (Array.shape a f,
        [vfun (_ : unit) h =>
           exists p, let f' := pffun p f in
             h \In Array.shape a f' /\
             sorted oleq (fgraph f')]) :=
  Do (let go :=
    ffix (fun (loop : quicksort_lm_loop a) '(l,h) =>
      Do (if decP (b:=(l : nat) < h) idP isn't left pf then skip
          else v <-- partition_lm a pf;
               loop (l, Po v);;
               (* we use saturating increment to stay under n+1 *)
               (* and keep the classical form of the algorithm *)
               (* the overflow case will exit on next call because v = h = n-1 *)
               loop (Sso v, h)))
  in go (ord0, ord_max)).
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
apply: [gE (pffun (pl * p) f)]=>//= _ mr [pr][].
rewrite Sso_eq ltnS -pffunEM => Hpr Hmr Sr _.
exists (pr * (pl * p))%g; split=>//.
- apply: perm_onM.
  - apply/(subset_trans Hpr)/subsetP=>/= z; rewrite !inE.
    case/andP=>+ ->; rewrite andbT; case: ltnP=>_ Hz.
    - by apply/ltnW/leq_ltn_trans/Hz.
    by apply/leq_trans/Hz.
  apply: perm_onM=>//.
  apply/(subset_trans Hpl)/subsetP=>/= z; rewrite !inE.
  case/andP=>->/= Hz.
  apply/leq_trans/Hvh/(leq_trans Hz).
  by exact: leq_pred.
(* we need to handle two edge cases: v=0 and v=n *)
case: (eqVneq v ord0)=>[Ev|Nv0].
- (* if v=0, then l=0 and left partition is empty *)
  have El: l = ord0.
  - by move: Hvl; rewrite Ev leqn0 => /eqP El; apply/ord_inj.
  rewrite Ev El /= in Hpl.
  have Epl: pl = 1%g.
  - apply: (perm_on_id Hpl).
    have ->: (1 = #|[set (@ord0 n)]|) by rewrite cards1.
    apply/subset_leqif_cards/subsetP=>/= z.
    by rewrite !inE leqn0 =>/eqP E; apply/eqP/ord_inj.
  move: Sr Hpr; rewrite El Ev Epl mul1g; case: ifP=>// H Sr Hpr.
  rewrite slice_xL // onth_codom /= -slice_oSL path_sortedE // Sr andbT.
  move: Ah; rewrite Ev slice_oSL /=.
  have ->: pffun (pr * p) f ord0 = pffun p f ord0.
  - by rewrite !ffunE permM (out_perm Hpr) // inE negb_and ltnn.
  have HS: subpred (ord (pffun p f ord0)) (oleq (pffun p f ord0)).
  - by move=>z /ordW.
  move/(sub_all HS); congr (_ = _); apply: perm_all.
  rewrite pffunEM perm_sym -!slice_oSL (_ : 0 = (ord0 : 'I_n.+1)) //.
  by apply: perm_on_fgraph.
move: (ltn_ord v); rewrite ltnS leq_eqVlt; case/orP=>[/eqP Ev|Nv].
- (* if v=n, then h=n and right partition is empty *)
  have Eh: (h : nat) = n.
  - apply/eqP; rewrite eqn_leq; move: Hvh; rewrite Ev=>->; rewrite andbT.
    by move: (ltn_ord h); rewrite ltnS.
  rewrite Ev Eh /= ltnn in Hpr.
  have Epr: pr = 1%g.
  - apply: (perm_on_id Hpr).
    have ->: (1 = #|[set (@ord_max n)]|) by rewrite cards1.
    apply/subset_leqif_cards/subsetP=>/= z.
    by rewrite !inE -eqn_leq =>/eqP E; apply/eqP/ord_inj.
  move: Sl Hpl; rewrite Eh Ev Epr mul1g => Sl Hpl.
  rewrite slice_xR; last by rewrite bnd_simp leEnat; move: Hvl; rewrite Ev.
  rewrite {22}(_ : n = (ord_max : 'I_n.+1)) // onth_codom /= sorted_rconsE //=.
  move: Sl; rewrite slice_oPR; last by rewrite lt0n -Ev.
  move=>->; rewrite andbT; move: Al; rewrite Ev.
  have ->: pffun (pl * p) f ord_max = pffun p f ord_max.
  - rewrite !ffunE permM (out_perm Hpl) // inE negb_and -!ltnNge /=.
    by rewrite ltn_predL lt0n -{3}Ev Nv0 orbT.
  have ->: v = ord_max by apply/ord_inj. 
  rewrite [in X in X -> _](perm_all (s2:=&:(codom (pffun (pl * p) f)) `[l: nat, n[)) //.
  rewrite pffunEM perm_sym. 
  rewrite {8 15}(_ : n = (ord_max : 'I_n.+1)) //; apply: perm_on_fgraph.
  apply/(subset_trans Hpl)/subsetP=>/= z; rewrite 2!inE in_itv /= leEnat ltEnat /=.
  by case/andP=>->/= Hz; apply: (leq_ltn_trans Hz); rewrite ltn_predL lt0n -Ev.
(* the general case *)
rewrite Nv in Hpr Sr.
rewrite (slice_split _ true (x:=v) (i:=`[l : nat, h : nat])) /=; last first.
- by rewrite in_itv /= leEnat; apply/andP.
rewrite (slice_xL (x:=v)) // onth_codom /=.
have -> : pffun (pr * (pl * p)) f v = pffun p f v.
- rewrite !ffunE mulgA; suff ->: (pr * pl * p)%g v = p v by [].
  rewrite permM.
  have Hmul : perm_on [set ix : 'I_n.+1| (l <= ix <= v.-1) || (v < ix <= h)] 
                      (pr * pl)%g.
  - apply: perm_onM.
    - by apply/(subset_trans Hpr)/subsetP=>/= z; rewrite !inE=>->; rewrite orbT.
    by apply/(subset_trans Hpl)/subsetP=>/= z; rewrite !inE=>->.
  rewrite (out_perm Hmul) // inE negb_or !negb_and -leqNgt -!ltnNge leqnn /=.
  by rewrite andbT ltn_predL lt0n Nv0 orbT.
rewrite {1}pffunEM (perm_on_notin _ Hpr); last first.
- rewrite disjoint_subset; apply/subsetP=>/= z.
  rewrite 3!inE in_itv /= negb_and leEnat ltEnat /= -leqNgt -ltnNge.
  by case/andP=>/ltnW-> _; rewrite orbT.
rewrite slice_oSL in Sr.
rewrite mulgA (perm_onC Hpr Hpl) in Sr *; last first.
- rewrite disjoint_subset; apply/subsetP=>/= z; rewrite !inE negb_and -!ltnNge.
  case/andP=>Hz _; apply/orP; right.
  by apply/leq_ltn_trans/Hz; exact: leq_pred.
rewrite -mulgA (pffunEM _ (pr * p)%g) (perm_on_notin _ Hpl) in Sr *; last first.
- rewrite disjoint_subset; apply/subsetP=>/= z.
  rewrite 3!inE in_itv /= negb_and leEnat /= -leqNgt -ltnNge.
  case/andP=>_ Hz; apply/orP; left; apply: (leq_trans Hz).
  exact: leq_pred.
rewrite sorted_pairwise // pairwise_cat /=.
rewrite allrel_consr -andbA -!sorted_pairwise //.
apply/and5P; split=>//.
- move: Al; congr (_ = _); apply/esym/perm_all; rewrite pffunEM.
  apply/perm_on_fgraph/(subset_trans Hpl)/subsetP=>/= z.
  rewrite 2!inE in_itv /= leEnat ltEnat /=.
  by case/andP=>->/= Hz; apply: (leq_ltn_trans Hz); rewrite ltn_predL lt0n.
- apply/allrelP=>x y Hx Hy; apply: (otrans (y:=pffun p f v)).
  - move/allP: Al=>/(_ x); apply.
    move: Hx; congr (_ = _); move: x; apply: perm_mem.
    rewrite pffunEM; apply: perm_on_fgraph.
    apply/(subset_trans Hpl)/subsetP=>/= z; rewrite 2!inE in_itv /= leEnat ltEnat /=.
    by case/andP=>->/= Hz; apply: (leq_ltn_trans Hz); rewrite ltn_predL lt0n.
  apply/ordW; move/allP: Ah=>/(_ y); apply.
  move: Hy; congr (_ = _); move: y; apply: perm_mem.
  by rewrite pffunEM; apply: perm_on_fgraph.
- by rewrite slice_oPR // in Sl; rewrite lt0n.
have HS: subpred (ord (pffun p f v)) (oleq (pffun p f v)).
- by move=>z /ordW.
move/(sub_all HS): Ah; congr (_ = _); apply/esym/perm_all.
by rewrite pffunEM; apply/perm_on_fgraph.
Qed.
Next Obligation.
move=>a [f][] i /= H.
apply: [gE f]=>//= _ m [p][Hp Hm Hs] _.
exists p; split=>//.
by rewrite -(slice_uu (codom _)) slice_0L slice_FR size_codom card_ord slice_oSR.
Qed.

End LomutoQsort.

(* TODO Hoare variant *)
