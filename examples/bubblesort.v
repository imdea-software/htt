From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype tuple finfun fingroup perm.
From fcsl Require Import options axioms prelude pred ordtype.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import interlude model heapauto.
From HTT Require Import array.

Lemma allrel_rconsl (T S : Type) (r : T -> S -> bool)
                    x xs ys : allrel r (rcons xs x) ys = allrel r xs ys && all (r x) ys.
Proof. by rewrite -cats1 allrel_catl allrel1l. Qed.

Lemma allrel_rconsr (T S : Type) (r : T -> S -> bool)
                    y xs ys : allrel r xs (rcons ys y) = allrel r xs ys && all (r^~ y) xs.
Proof. by rewrite -cats1 allrel_catr allrel1r. Qed.

Lemma implyb_trans a b c : a ==> b -> b ==> c -> a ==> c.
Proof. by case: a=>//=->. Qed.

Lemma cat2s {T} (a b : T) xs : [:: a, b & xs] = [::a] ++ [::b] ++ xs.
Proof. by []. Qed.

Lemma ord_indx n (i : 'I_n) : heap.indx i = i.
Proof. by exact: index_enum_ord. Qed.

Lemma sorted1 {T: Type} (r : rel T) xs : size xs == 1 -> sorted r xs.
Proof. by case: xs=>// x; case. Qed.

Section FindLast.

Variables (T : Type).
Implicit Types (x : T) (p : pred T) (s : seq T).

Definition find_last p s :=
  let i := seq.find p (rev s) in
  if i == size s then size s else (size s - i).-1.

Lemma find_last_size p s : find_last p s <= size s.
Proof.
rewrite /find_last; case: ifP=>// _.
by rewrite -subnS; apply: leq_subr.
Qed.

Lemma has_find_last p s : has p s = (find_last p s < size s).
Proof.
rewrite /find_last -has_rev has_find -(size_rev s); case: ltngtP=>/=.
- move=>H; case/posnP: (size (rev s))=>[/eqP/nilP|] E.
  - by rewrite E /= in H.
  by rewrite -subnS ltn_subrL E.
- by rewrite ltnNge find_size.
by rewrite ltnn.
Qed.

Lemma hasNfind_last p s : ~~ has p s -> find_last p s = size s.
Proof. by rewrite has_find_last; case: ltngtP (find_last_size p s). Qed.

Lemma has_drop p s i : has p s -> has p (drop i.+1 s) = (i < find_last p s).
Proof.
rewrite /find_last -has_rev -(size_rev s) => /[dup] E.
rewrite has_find =>/[dup] H.
rewrite ltn_neqAle; case/andP=>/negbTE -> _.
move/(has_take (size s - i).-1): E.
rewrite take_rev has_rev -subnS.
case/boolP: (i < size s)=>[Hi|].
- rewrite subKn // =>->; rewrite size_rev in H *.
  by rewrite ltn_subCr -[RHS]ltnS prednK // subn_gt0.
rewrite -ltnNge ltnS => Hi _.
rewrite drop_oversize /=; last by apply: (leq_trans Hi).
symmetry; apply/negbTE; rewrite size_rev -ltnNge ltnS.
by apply/leq_trans/Hi; rewrite -subnS; exact: leq_subr.
Qed.

Lemma find_gtn p s i : has p (drop i.+1 s) -> i < find_last p s.
Proof.
case/boolP: (has p s)=>Hp; first by rewrite (has_drop _ Hp).
suff: ~~ has p (drop i.+1 s) by move/negbTE=>->.
move: Hp; apply: contra; rewrite -{2}(cat_take_drop i.+1 s) has_cat=>->.
by rewrite orbT.
Qed.

End FindLast.

Section FindLastEq.

Variables (T : eqType).
Implicit Type p : seq T.

Definition index_last (x : T) := find_last (pred1 x).

Lemma memNindex_last x s : x \notin s -> index_last x s = size s.
Proof. by rewrite -has_pred1=>/hasNfind_last. Qed.

Lemma index_last_cons x y t : index_last x (y::t) =
  if x \in t then (index_last x t).+1 else if y == x then 0 else (size t).+1.
Proof.
rewrite /index_last /find_last /= rev_cons -cats1 find_cat /= has_rev has_pred1.
case/boolP: (x \in t)=>H; last first.
- rewrite size_rev; case/boolP: (y == x)=>/= _; last by rewrite addn1 eqxx.
  by rewrite addn0 eqn_leq leqnSn /= ltnn subSnn.
rewrite -mem_rev -has_pred1 has_find in H; rewrite -(size_rev t).
case: ltngtP H=>//= H _.
case: ifP=>[/eqP E|_]; first by rewrite E ltnNge leqnSn in H.
by rewrite predn_sub /= prednK // subn_gt0.
Qed.

Lemma index_gtn x s i : x \in drop i.+1 s -> i < index_last x s.
Proof. by rewrite -has_pred1; apply: find_gtn. Qed.

Lemma index_last_uniq x s : uniq s -> index_last x s = index x s.
Proof.
move=>H; case/boolP: (x \in s)=>Hx; last first.
- by rewrite (memNindex_last Hx) (memNindex Hx).
elim: s x H Hx=>//= h t IH x.
rewrite index_last_cons.
case/andP=>Hh Ht; rewrite inE eq_sym; case/orP.
- by move/eqP=>{x}<-; rewrite (negbTE Hh) eqxx.
move=>Hx; rewrite Hx; case: eqP=>[E|_]; last by congr S; apply: IH.
by rewrite E Hx in Hh.
Qed.

End FindLastEq.

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
Definition So_lower n (i : 'I_n) (prf : i.+1 < n) : 'I_n.
Proof. case: i prf=>/= m Hm; apply: Ordinal. Defined.

Lemma So_lower_eq n (i : 'I_n) (prf : i.+1 < n) : nat_of_ord (So_lower prf) = i.+1.
Proof. by case: i prf. Qed.

Lemma Wo_So_lower_eq n (i : 'I_n) (prf : i.+1 < n) : Wo (So_lower prf) = So i.
Proof. by case: i prf=>/= m prf0 prf1; apply/ord_inj. Qed.

(* subtract 2 and decrease bound by 1 *)
Definition Po_lower2 n (i : 'I_n) (pi : 1 < i) : 'I_n.-1.
Proof.
case: i pi=>m prf /= Hm.
apply: (Ordinal (n:=n.-1) (m:=m.-2)).
rewrite ltn_predRL; case: m prf Hm=>//=; case=>//= m Hm _.
by apply: ltnW.
Defined.

Lemma Po_lower_eq2 n (i : 'I_n) (prf : 1 < i) : nat_of_ord (Po_lower2 prf) = i.-2.
Proof. by case: i prf. Qed.

End OrdArith.

Section CodomWS.
Variable (n : nat).

Lemma size_take_codom T (i : 'I_n) (f: {ffun 'I_n.+1 -> T}) : size (take i (codom f)) = i.
Proof.
by rewrite size_take size_codom card_ord ltnS leq_eqVlt ltn_ord orbT.
Qed.

Lemma ffun_split2 A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  codom f = take i (codom f) ++
            [:: f (Wo i); f (So i)] ++
            drop i.+2 (codom f).
Proof.
set i0 := Wo i; set i1 := So i.
rewrite {1}codomE (enum_split i0) /= {2}(enum_split i1) (ord_indx i0) (ord_indx i1).
rewrite drop_cat size_take size_enum_ord ltn_ord So_eq ltnn subnn /=.
by rewrite map_cat /= map_take map_drop -codomE.
Qed.

Lemma take_codom_rcons A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  take i.+1 (codom f) = rcons (take i (codom f)) (f (Wo i)).
Proof.
by rewrite {1}(ffun_split2 f i) take_cat size_take_codom leqNgt ltnS leqnSn /= subSnn /= cats1.
Qed.

Lemma drop_codom_cons A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  drop i.+1 (codom f) = f (So i) :: drop i.+2 (codom f).
Proof.
by rewrite {1}(ffun_split2 f i) drop_cat size_take_codom leqNgt ltnS leqnSn /= subSnn.
Qed.

Lemma take_codom_rcons2 A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  take i.+2 (codom f) = rcons (rcons (take i (codom f)) (f (Wo i))) (f (So i)).
Proof.
rewrite {1}(ffun_split2 f i) take_cat size_take_codom leqNgt ltnS -addn2 leq_addr /=.
by rewrite -addnBAC // subnn /= take0 -cat1s catA !cats1.
Qed.

Lemma sorted_codom_rcons2 {A : ordType} (f: {ffun 'I_n.+1 -> A}) (i : 'I_n) :
   oleq (f (Wo i)) (f (So i)) ->
   sorted oleq (take i.+1 (codom f)) -> sorted oleq (take i.+2 (codom f)).
Proof.
move=>Hf; rewrite take_codom_rcons take_codom_rcons2 => Hs.
rewrite (sorted_rconsE _ _ (@otrans A)) Hs andbT all_rcons Hf /=.
move: Hs; rewrite (sorted_rconsE _ _ (@otrans A)).
by case/andP=>+ _; apply/sub_all=>z Hz; apply/otrans/Hf.
Qed.

End CodomWS.

Section SwapNext.
Variable (n : nat).

Definition pffun {I : finType} {A} (p : {perm I}) (f : {ffun I -> A}) :=
  [ffun i => f (p i)].

Lemma pffunE1 {I : finType} {A} (f : {ffun I -> A}) :
  pffun 1%g f = f.
Proof. by apply/ffunP => i; rewrite !ffunE permE. Qed.

Lemma pffunEM {I : finType} {A}
              (p p' : {perm I}) (f : {ffun I -> A}) :
  pffun (p * p') f = pffun p (pffun p' f).
Proof. by apply/ffunP => i; rewrite !ffunE permM. Qed.

Definition pswnx (i : 'I_n) : 'S_n.+1 := tperm (Wo i) (So i).

Lemma swapnxE1 A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  pffun (pswnx i) f (Wo i) = f (So i).
Proof.
by rewrite /pswnx ffunE; case: tpermP=>// /eqP; rewrite eq_sym (negbTE (So_WoN i)).
Qed.

Lemma swapnxE2 A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  pffun (pswnx i) f (So i) = f (Wo i).
Proof.
by rewrite /pswnx ffunE; case: tpermP=>// /eqP; rewrite (negbTE (So_WoN i)).
Qed.

Lemma swapnx_take A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) k :
  k <= i ->
  take k (fgraph (pffun (pswnx i) f)) = take k (fgraph f).
Proof.
move=>Hk.
suff E: {in take k (enum 'I_n.+1), f =1 pffun (pswnx i) f}.
- by rewrite !fgraph_codom /= !codomE -2!map_take; move/eq_in_map: E.
move=>/= y /index_ltn; rewrite /pswnx ffunE index_enum_ord=>Hy.
case: tpermP=>//; move: (leq_trans Hy Hk)=>/[swap]->/=.
- by rewrite ltnn.
by rewrite So_eq ltnNge leqnSn.
Qed.

Lemma swapnx_drop A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) k :
  i.+2 <= k ->
  drop k (fgraph (pffun (pswnx i) f)) = drop k (fgraph f).
Proof.
case: k=>//= k; rewrite ltnS=>Hk.
suff E: {in drop k.+1 (enum 'I_n.+1), f =1 (pffun (pswnx i) f)}.
- by rewrite /= !codomE -2!map_drop /=; move/eq_in_map: E.
move=>/= y /index_gtn; rewrite index_last_uniq; last by apply: enum_uniq.
rewrite /pswnx ffunE index_enum_ord=>Hy.
have {Hk}Hy: i.+1 < y.
- rewrite -ltn_predRL; apply: (leq_trans Hk).
  by case: y Hy =>/=; case.
case: tpermP=>//; move: Hy=>/[swap]->/=.
- by rewrite ltnNge leqnSn.
by rewrite So_eq ltnn.
Qed.

Lemma swap_split2 A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  codom (pffun (pswnx i) f) = take i (codom f) ++
                              [:: f (So i); f (Wo i)] ++
                              drop i.+2 (codom f).
Proof.
rewrite /= (ffun_split2 _ i) /=; set i0 := Wo i; set i1 := So i.
by rewrite swapnx_take // swapnx_drop //= swapnxE1 swapnxE2.
Qed.

Lemma take_swap_rcons A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  take i.+1 (fgraph (pffun (pswnx i) f)) = rcons (take i (fgraph f)) (f (So i)).
Proof.
by rewrite !fgraph_codom /= swap_split2 take_cat size_take_codom
  (leqNgt i.+2) ltnS leqnSn /= subSnn /= cats1.
Qed.

Lemma take_swap_rcons2 A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  take i.+2 (fgraph (pffun (pswnx i) f)) = rcons (rcons (take i (fgraph f)) (f (So i))) (f (Wo i)).
Proof.
by rewrite !fgraph_codom /= swap_split2 take_cat size_take_codom
  leqNgt ltnS -addn2 leq_addr /= -addnBAC // subnn /= take0 -cat1s catA !cats1.
Qed.

Lemma drop_swap_cons A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  drop i.+1 (fgraph (pffun (pswnx i) f)) = f (Wo i) :: drop i.+2 (fgraph f).
Proof.
by rewrite fgraph_codom /= swap_split2 drop_cat size_take size_codom /= card_ord
  !ltnS (leq_eqVlt i) ltn_ord orbT (leqNgt i.+2) ltnS leqnSn /= subSnn.
Qed.

Lemma perm_take_swap_gt {A : eqType} (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) k :
  i <= k ->
  perm_eq (take k.+2 (codom f)) (take k.+2 (codom (pffun (pswnx i) f))).
Proof.
move=>H.
rewrite (ffun_split2 f i) swap_split2 /= !take_cat size_take_codom leqNgt ltnS.
have ->/= : i <= k.+2 by apply: (leq_trans H); rewrite -addn2; apply: leq_addr.
rewrite -(addn2 k) -addnBAC // addn2 /=.
by apply/permPl/perm_catl; rewrite !cat2s perm_catCA.
Qed.

End SwapNext.

Section Bubble.
Variable (n : nat) (A : ordType).

Opaque Array.write Array.read.

(***************)
(* unoptimized *)
(***************)

(*****************************************************)
(* pseudocode in idealized ML-like language,         *)
(* assuming size a >= 2                              *)
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
              then p = pswnx i /\ ord (f i1) (f i0)
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
step=>_; exists (pswnx i); do!split=>//=.
suff: fsw = pffun (pswnx i) f by move=>->.
rewrite /fsw /fs /pswnx; apply/ffunP=>/= x; rewrite !ffunE /= ffunE /=.
case: tpermP=>[->|->|/eqP/negbTE->/eqP/negbTE->] //; rewrite eqxx //.
by rewrite /i1 eq_sym (negbTE (So_WoN i)).
Qed.

Opaque cas_next.

Definition bubble_loopT (a : {array 'I_n.+2 -> A}) :=
  forall isw : 'I_n.+1 * bool,
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => h \In Array.shape a f /\
                  ~~ isw.2 ==> sorted oleq (take isw.1.+1 (fgraph f)),
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
  Do (let go := Fix (fun (loop : bubble_loopT a) '(i, sw) =>
                  Do (sw0 <-- cas_next a i;
                      let sw1 := sw || sw0 in
                      if decP (b := i < n) idP is left pf
                        then loop (So_lower (i:=i) pf, sw1)
                        else ret sw1))
      in go (ord0, false)).
Next Obligation.
move=>a loop _ i sw [f][] h /= [H Hs].
set i0 := Wo i; set i1 := So i.
apply: [stepE f]=>//= sw0 m [p][{}H Hsw]; case: decP=>Hin.
- (* i < n, recursive call *)
  apply: [gE (pffun p f)]=>//=.
  - (* precondition *)
    split=>//; rewrite negb_or andbC So_lower_eq.
    case: sw0 Hsw=>//=; case=>{p H}-> Hf; rewrite pffunE1.
    (* swap didn't happen in this iteration *)
    apply/(implyb_trans Hs)/implyP=>{Hs}.
    (* swap didn't happen before *)
    by apply: sorted_codom_rcons2.
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
rewrite -(take_size (codom f)) size_codom /= card_ord -[X in take X.+2 _]Hin.
by apply: sorted_codom_rcons2.
Qed.
Next Obligation.
move=>a [f][] h /= H.
apply: [gE f]=>//= [|v m [p][Hm _ Hv] _]; last by exists p.
by split=>//; apply: sorted1; rewrite size_take size_codom card_ord.
Qed.

Opaque bubble_pass.

Definition bubble_sortT (a : {array 'I_n.+2 -> A}) : Type :=
  unit ->
  {f : {ffun 'I_n.+2 -> A}},
  STsep (Array.shape a f,
        [vfun (_ : unit) h =>
           exists (p : 'S_n.+2),
             h \In Array.shape a (pffun p f) /\
             sorted oleq (fgraph (pffun p f))]).

Program Definition bubble_sort (a : {array 'I_n.+2 -> A}) : bubble_sortT a :=
  Fix (fun (go : bubble_sortT a) _ =>
    Do (sw <-- bubble_pass a;
        if sw
          then go tt : ST _
          else skip)).
Next Obligation.
move=>a go _ [f][] h /= [E V].
apply: [stepE f]=>//=; case=>m.
- case=>p [Hm _].
  apply: [gE (pffun p f)]=>//= _ m2 [p'][H2 Hs] _.
  by exists (p' * p)%g; rewrite pffunEM.
case=>p [Hm /= /andP [/eqP Ep Hs]]; rewrite {p}Ep in Hm.
by step=>_; exists 1%g; split=>//; rewrite pffunE1.
Qed.

(*******************)
(* optimization #1 *)
(*******************)

(**********************************************************)
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

Definition bubble_loop_optT (a : {array 'I_n.+2 -> A}) (k : 'I_n.+1) :=
  forall isw : 'I_n.+1 * bool,
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => [/\ h \In Array.shape a f,
                      allrel oleq (take k.+2 (fgraph f)) (drop k.+2 (fgraph f)),
                      sorted oleq (drop k.+2 (fgraph f)),
                      isw.1 <= k,
                      all (oleq^~ (f (Wo isw.1))) (take isw.1 (fgraph f)) &
                      ~~ isw.2 ==> sorted oleq (take isw.1 (fgraph f))],
        [vfun (b : bool) h =>
          exists (p : 'S_n.+2), let f' := pffun p f in
          [/\ h \In Array.shape a f',
              isw.2 ==> b &
              if b then
                allrel oleq (take k.+1 (fgraph f')) (drop k.+1 (fgraph f')) &&
                sorted oleq (drop k.+1 (fgraph f'))
              else (p == 1%g) && sorted oleq (fgraph f)]]).

Program Definition bubble_pass_opt (a : {array 'I_n.+2 -> A}) (k : 'I_n.+1) :
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => [/\ h \In Array.shape a f,
                      allrel oleq (take k.+2 (fgraph f)) (drop k.+2 (fgraph f)) &
                      sorted oleq (drop k.+2 (fgraph f))],
          [vfun (b : bool) h =>
            exists (p : 'S_n.+2), let f' := pffun p f in
              h \In Array.shape a f' /\
              if b then
                allrel oleq (take k.+1 (fgraph f')) (drop k.+1 (fgraph f')) &&
                sorted oleq (drop k.+1 (fgraph f'))
              else (p == 1%g) && sorted oleq (fgraph f)]) :=
  Do (let go := Fix (fun (loop : bubble_loop_optT a k) '(i, sw) =>
                  Do (sw0 <-- cas_next a i;
                      let sw1 := sw || sw0 in
                      if decP (b := i < k) idP is left pf
                        then loop (So_lower (i:=i) pf, sw1)
                        else ret sw1))
      in go (ord0, false)).
Next Obligation.
(* So_lower is always safe *)
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
    rewrite So_lower_eq Wo_So_lower_eq negb_or.
    case: sw0 Hsw=>/=; case=>Ep Hf; rewrite {p}Ep ?pffunE1 in Hm *.
    - (* swap happened before the call *)
      rewrite andbF /= swapnx_drop //; split=>//.
      - rewrite (@allrel_in_l _ _ _ _ (take k.+2 (codom f))) //.
        by apply/perm_mem; rewrite perm_sym; apply: perm_take_swap_gt.
      by rewrite take_swap_rcons all_rcons swapnxE2 Hai andbT; apply: ordW.
    (* swap didn't happen before the call *)
    rewrite andbT take_codom_rcons; split=>//.
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
rewrite -Hik in Hak Hsk *.
case: sw0 Hsw=>/=; case=>-> Hf.
- (* swap happened on last iteration *)
  rewrite orbT drop_swap_cons /=; apply/andP; split.
  - rewrite take_swap_rcons allrel_rconsl allrel_consr /=.
    move: Hak; rewrite take_codom_rcons2 !allrel_rconsl -/i0 -/i1 -andbA.
    by case/and3P=>-> _ ->; rewrite (ordW Hf) /= !andbT.
  rewrite (path_sortedE (@otrans A)) Hsk andbT.
  apply/allP=>z Hz; move/allrelP: Hak; apply=>//.
  by rewrite take_codom_rcons2 4!(mem_rcons, inE) eqxx /= orbT.
(* swap didn't happen on last iteration *)
rewrite orbF pffunE1 eqxx /=; case: sw Hsi=>/=[_|].
- (* flag was set *)
  apply/andP; split.
  - rewrite take_codom_rcons drop_codom_cons allrel_rconsl allrel_consr /=.
    move: Hak; rewrite take_codom_rcons2 !allrel_rconsl -andbA -/i0 -/i1.
    case/and3P=>->-> _; rewrite Hf /= !andbT.
    by apply/sub_all/Hai=>z /otrans; apply.
  rewrite drop_codom_cons /= (path_sortedE (@otrans A)) Hsk andbT.
  by move: Hak; rewrite take_codom_rcons2 !allrel_rconsl -andbA; case/and3P.
(* flag wasn't set, so the pass didn't swap anything - the array is sorted *)
move=>Hs2; rewrite (ffun_split2 f i) -/i0 -/i1 /=; rewrite Hik in Hai Hs2 Hsk *.
rewrite (sorted_pairwise (@otrans A)) pairwise_cat /= -!(sorted_pairwise (@otrans A)).
rewrite Hf Hsk Hs2 /= andbT !allrel_consr -!andbA Hai /=.
move: Hak; rewrite -Hik take_codom_rcons2 !allrel_rconsl -andbA; case/and3P=>->->->/=.
by rewrite andbT Hik; apply/sub_all/Hai=>z /otrans; apply.
Qed.
Next Obligation.
move=>a k [f][] h /= [H Ha Hs].
apply: [gE f]=>//= [|v m [p][Hm _ Hv] _]; last by exists p.
by rewrite take0.
Qed.

Opaque bubble_pass_opt.

Definition bubble_sort_optT (a : {array 'I_n.+2 -> A}) : Type :=
  forall (k : 'I_n.+1),
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => [/\ h \In Array.shape a f,
                      allrel oleq (take k.+2 (fgraph f)) (drop k.+2 (fgraph f)) &
                      sorted oleq (drop k.+2 (fgraph f))],
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
  Do (let go := Fix (fun (loop : bubble_sort_optT a) k =>
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
move: H Hs; rewrite {}Hk /= (ffun_split2 _ ord0) /= take0 /= take0 drop0.
rewrite (path_sortedE (@otrans A)) allrel1l /=; case/andP=>_ Ha0; case/andP=>Ha1 Hs2.
by split=>//; rewrite allrel_consl allrel1l Ha0.
Qed.
Next Obligation.
move=>a [f][] h /= [E V].
have Hs: size (codom f) <= n.+2 by rewrite size_codom /= card_ord.
by apply: [gE f]=>//=; split=>//; rewrite drop_oversize // allrel0r.
Qed.

(*******************)
(* optimization #2 *)
(*******************)

(********************************************************)
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

Definition bubble_loop_opt2T (a : {array 'I_n.+2 -> A}) (k : 'I_n.+1) :=
  forall ils : 'I_n.+1 * 'I_n.+2,
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => [/\ h \In Array.shape a f,
                      allrel oleq (take k.+2 (fgraph f)) (drop k.+2 (fgraph f)),
                      sorted oleq (drop k.+2 (fgraph f)),
                      ils.2 <= ils.1 <= k,
                      allrel oleq (take ils.2 (fgraph f)) (drop ils.2 (take ils.1.+1 (codom f))) &
                      sorted oleq (drop ils.2 (take ils.1.+1 (fgraph f)))],
        [vfun (j : 'I_n.+2) h =>
          exists (p : 'S_n.+2), let f' := pffun p f in
            [/\ h \In Array.shape a f',
                ils.2 <= j,
                allrel oleq (take j (fgraph f')) (drop j (fgraph f')) &
                sorted oleq (drop j (fgraph f'))]]).

Program Definition bubble_pass_opt2 (a : {array 'I_n.+2 -> A}) (k : 'I_n.+1) :
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => [ /\ h \In Array.shape a f,
                       allrel oleq (take k.+2 (fgraph f)) (drop k.+2 (fgraph f)) &
                       sorted oleq (drop k.+2 (fgraph f)) ],
          [vfun (j : 'I_n.+2) h =>
            exists (p : 'S_n.+2), let f' := pffun p f in
              [/\ h \In Array.shape a f',
                  allrel oleq (take j (fgraph f')) (drop j (fgraph f')) &
                  sorted oleq (drop j (fgraph f'))]]) :=
  Do (let go := Fix (fun (loop : bubble_loop_opt2T a k) '(i, ls) =>
                  Do (sw <-- cas_next a i;
                      let ls1 := if sw then So i else ls in
                      if decP (b := i < k) idP is left pf
                        then loop (So_lower (i:=i) pf, ls1)
                        else ret ls1))
      in go (ord0, ord0)).
Next Obligation.
(* show that So_lower is always safe *)
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
    rewrite So_lower_eq; case: sw Hsw=>/=;
    case=>Ep Hf; rewrite {p}Ep ?pffunE1 in Hm *.
    - (* swap happened before the call *)
      rewrite So_eq swapnx_drop; last by rewrite ltnS; apply: ltnW.
      have Ei: size (rcons (take i (codom f)) (f (So i))) = i.+1.
      - by rewrite size_rcons size_take_codom.
      have ->: drop i.+1 (take i.+2 (codom (pffun (pswnx i) f))) = [:: f (Wo i)].
      - rewrite swap_split2 take_cat size_take_codom leqNgt ltnS -(addn2 i) leq_addr /=.
        rewrite -addnBAC // subnn /= take0 /= -cat1s catA !cats1 drop_rcons; last by rewrite Ei.
        by rewrite -Ei drop_size.
      split=>//.
      - rewrite (@allrel_in_l _ _ _ _ (take k.+2 (codom f))) //.
        by apply/perm_mem; rewrite perm_sym; apply: perm_take_swap_gt.
      - by rewrite ltnS leqnn.
      rewrite allrel1r take_swap_rcons all_rcons (ordW Hf) /=.
      move: Hsi; rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
      rewrite (sorted_rconsE _ _ (@otrans A)); case/andP=>Ha1 Hs1.
      rewrite -(cat_take_drop ls (take i (codom f))) all_cat Ha1 andbT take_take //.
      apply/sub_all/Hai=>z /= /allP; apply.
      rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
      by rewrite mem_rcons inE eqxx.
    (* swap didn't happen before the call *)
    split=>//.
    - by apply/andP; split=>//; apply: ltnW.
    - rewrite take_codom_rcons2 drop_rcons; last by rewrite size_rcons size_take_codom; apply: ltnW.
      rewrite -take_codom_rcons allrel_rconsr Hai /=.
      suff: all (oleq^~ (f (Wo i))) (take ls (codom f)).
      - by apply/sub_all=>z /otrans; apply.
      apply/sub_all/Hai=>z /= /allP; apply.
      rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
      by rewrite mem_rcons inE eqxx.
    rewrite take_codom_rcons2 drop_rcons; last by rewrite size_rcons size_take_codom; apply: ltnW.
    rewrite (sorted_rconsE _ _ (@otrans A)) -{2}take_codom_rcons Hsi andbT.
    rewrite drop_rcons; last by rewrite size_take_codom.
    rewrite all_rcons Hf /=.
    move: Hsi; rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
    rewrite (sorted_rconsE _ _ (@otrans A)).
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
  rewrite So_eq; split=>//=.
  - by apply: ltnW.
  - rewrite Ep take_swap_rcons drop_swap_cons allrel_rconsl allrel_consr /=.
    move: Hak; rewrite take_codom_rcons2 !allrel_rconsl -/i0 -/i1 -andbA.
    case/and3P=>-> _ ->; rewrite (ordW Hf) /= !andbT.
    rewrite -(cat_take_drop ls (take i (codom f))) all_cat take_take //.
    move: Hsi; rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
    rewrite (sorted_rconsE _ _ (@otrans A)); case/andP=>-> _; rewrite andbT.
    apply/sub_all/Hai=>z /= /allP; apply.
    rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
    by rewrite mem_rcons inE eqxx.
  rewrite Ep drop_swap_cons /= (path_sortedE (@otrans A)) Hsk andbT.
  apply/allP=>z Hz; move/allrelP: Hak; apply=>//.
  by rewrite take_codom_rcons2 4!(mem_rcons, inE) eqxx /= orbT.
(* swap didn't happen on last iteration *)
rewrite {p}Ep pffunE1 /= in Hm *.
have El2 : ls <= i.+2 by apply/ltnW/ltnW.
set q := i.+2 - ls; have E1 : i.+2 = ls + q by rewrite subnKC.
split=>//.
- rewrite -{2}(cat_take_drop i.+1 (codom f)) drop_cat size_take size_codom card_ord ltnS ltn_ord ltnS Hils.
  rewrite allrel_catr Hai /= drop_codom_cons allrel_consr; apply/andP; split.
  - suff: all (oleq^~ (f (Wo i))) (take ls (codom f)).
    - by apply/sub_all=>z Hz; apply/otrans/Hf.
    apply/sub_all/Hai=>z /allP; apply.
    rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
    by rewrite mem_rcons inE eqxx.
  apply/allrel_sub_l/Hak=>z Hz.
  by rewrite -(cat_take_drop ls (take i.+2 (codom f))) take_take // mem_cat Hz.
rewrite -(cat_take_drop q (drop ls (codom f))) drop_drop addnC -E1.
rewrite (sorted_pairwise (@otrans A)) pairwise_cat -!(sorted_pairwise (@otrans A)).
rewrite Hsk andbT take_drop addnC -E1; apply/andP; split.
- apply/allrel_sub_l/Hak=>z Hz.
  by rewrite -{1}(cat_take_drop ls ((take i.+2 (codom f)))) mem_cat Hz orbT.
rewrite take_codom_rcons2 drop_rcons; last by rewrite size_rcons size_take_codom; apply: ltnW.
rewrite (sorted_rconsE _ _ (@otrans A)) -{2}take_codom_rcons Hsi andbT.
rewrite drop_rcons; last by rewrite size_take_codom.
rewrite all_rcons Hf /=.
move: Hsi; rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
rewrite (sorted_rconsE _ _ (@otrans A)).
by case/andP=>+ _; apply/sub_all=>z /otrans; apply.
Qed.
Next Obligation.
move=>a k [f][] h /= [H Ha Hs].
apply: [gE f]=>//= [|v m [p][Hm _ {}Ha {}Hs] _]; last by exists p.
rewrite take0 drop0 allrel0l; split=>//.
by apply: sorted1; rewrite size_take size_codom card_ord.
Qed.

Opaque bubble_pass_opt2.

Definition bubble_sort_opt2T (a : {array 'I_n.+2 -> A}) : Type :=
  forall (k : 'I_n.+1),
  {f : {ffun 'I_n.+2 -> A}},
  STsep (fun h => [/\ h \In Array.shape a f,
                        allrel oleq (take k.+2 (codom f)) (drop k.+2 (codom f)) &
                        sorted oleq (drop k.+2 (codom f))],
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
  Do (let go := Fix (fun (loop : bubble_sort_opt2T a) k =>
                     Do (k1 <-- bubble_pass_opt2 a k;
                         if decP (b := 1 < k1) idP is left pf
                           then loop (Po_lower2 (i:=k1) pf) : ST _
                           else skip))
      in go ord_max).
Next Obligation.
move=>a go k [f][] h /= [H Ha Hs].
apply: [stepE f]=>{Ha Hs}//= x m [p][Hm Ha Hs].
case: decP=>Hx; last first.
- step=>Vm; exists p; split=>//.
  move/negP: Hx; rewrite -leqNgt; case: (posnP x).
  - by move=>Hx _; rewrite Hx drop0 in Hs.
  case: (nat_of_ord x) Ha Hs=>//; case=>//= Ha1 Hs1 _ _.
  rewrite -(cat_take_drop 1 (codom (pffun p f))).
  rewrite (sorted_pairwise (@otrans A)) pairwise_cat -!(sorted_pairwise (@otrans A)).
  by rewrite Ha1 Hs1 /= andbT; apply: sorted1; rewrite size_take size_codom card_ord.
apply: [gE (pffun p f)]=>//=; last first.
- move=> _ m2 [p'][H2 Hs'] _; exists (p' * p)%g.
  by rewrite pffunEM.
rewrite (Po_lower_eq2 Hx); suff: x.-2.+2 = x by move=>->.
by rewrite -subn2 -addn2 addnBAC // addnK.
Qed.
Next Obligation.
move=>a [f][] h /= [E V].
have Hs: size (codom f) <= n.+2 by rewrite size_codom /= card_ord.
by apply: [gE f]=>//=; split=>//; rewrite drop_oversize // allrel0r.
Qed.

End Bubble.
