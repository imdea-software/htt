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

(* decrease bound by 1 *)
Definition Po_lower n (i : 'I_n) (pi : i.+1 < n) : 'I_n.-1.
Proof.
case: i pi=>m prf /= Hm.
apply: (Ordinal (n:=n.-1) (m:=m)).
by rewrite ltn_predRL.
Defined.

Lemma Po_lower_eq n (i : 'I_n) (prf : i.+1 < n) : nat_of_ord (Po_lower prf) = i.
Proof. by case: i prf. Qed.
(*
(* decrease bound by 1 *)
Definition Po_lower n (i : 'I_n) (pi : 0 < i) : 'I_n.-1.
Proof.
case: i pi=>m prf /= Hm.
apply: (Ordinal (n:=n.-1) (m:=m.-1)).
by rewrite ltn_predRL prednK.
Defined.

Lemma Po_lower_eq n (i : 'I_n) (prf : 0 < i) : nat_of_ord (Po_lower prf) = i.-1.
Proof. by case: i prf. Qed.
*)
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

Opaque Array.write Array.read.

Section Bubble.
Variable (n : nat).

(* TODO ordType! *)

(***************)
(* unoptimized *)
(***************)

(*****************************************************)
(* pseudocode in idealized ML-like language,         *)
(* assuming size a >= 2                              *)
(*                                                   *)
(* let cas_next (a : array nat) (i : nat) : bool =   *)
(*   let prev = array.read a i;                      *)
(*   let next = array.read a i+1;                    *)
(*   if next < prev then                             *)
(*     array.write a  i    next;                     *)
(*     array.write a (i+1) prev;                     *)
(*     true                                          *)
(*   else false                                      *)
(*                                                   *)
(* let bubble_pass (a : array nat) : bool =          *)
(*   let go (i : nat) (sw : bool) : bool =           *)
(*     let sw1 = sw || cas_next a i;                 *)
(*     if i < (size a)-2 then go (i+1) sw1 else sw1; *)
(*   go 0 false                                      *)
(*                                                   *)
(* let bubble_sort (a : array nat) : unit =          *)
(*   if bubble_pass a then bubble_sort a else ().    *)
(*****************************************************)

Program Definition cas_next (a : {array 'I_n.+2 -> nat}) (i : 'I_n.+1) :
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (Array.shape a f,
        [vfun (b : bool) h =>
          let i0 := Wo i in let i1 := So i in
          exists (p : 'S_n.+2),
            h \In Array.shape a (pffun p f) /\
            if b
              then p = pswnx i /\ f i1 < f i0
              else p = 1%g /\ f i0 <= f i1]) :=
  let i0 := Wo i in let i1 := So i in
  Do (prev <-- Array.read a i0;
      next <-- Array.read a i1;
      if next < prev then
          Array.write a i0 next;;
          Array.write a i1 prev;;
          ret true
        else ret false).
Next Obligation.
move=>a i /= [f][] h /= [E V].
set i0 := Wo i; set i1 := So i.
do 2!apply: [stepE f, h]=>//= _ _ [->->].
case: leqP=>H; first by step=>_; exists 1%g; split=>//; rewrite pffunE1.
apply: [stepE f]=>//= _ _ [-> Vs]; set fs := finfun [eta f with i0 |-> f i1].
apply: [stepE fs]=>//= _ _ [-> Vsw]; set fsw := finfun [eta fs with i1 |-> f i0].
step=>_; exists (pswnx i); do!split=>//=.
suff: fsw = pffun (pswnx i) f by move=>->.
rewrite /fsw /fs /pswnx; apply/ffunP=>/= x; rewrite !ffunE /= ffunE /=.
case: tpermP.
- by move=>->; rewrite eqxx /i1 eq_sym (negbTE (So_WoN i)).
- by move=>->; rewrite eqxx.
by move/eqP/negbTE=>->/eqP/negbTE=>->.
Qed.

Opaque cas_next.

Definition bubble_loopT (a : {array 'I_n.+2 -> nat}) :=
  forall isw : 'I_n.+1 * bool,
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (fun h => h \In Array.shape a f
               /\ ~~ isw.2 ==> sorted leq (take isw.1.+1 (fgraph f)),
        [vfun (b : bool) h =>
          isw.2 ==> b /\
          exists (p : 'S_n.+2),
            h \In Array.shape a (pffun p f) /\
            ~~ b ==> (p == 1%g) && sorted leq (fgraph f)]).

Program Definition bubble_pass (a : {array 'I_n.+2 -> nat}) :
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (Array.shape a f,
          [vfun (b : bool) h =>
            exists (p : 'S_n.+2),
              h \In Array.shape a (pffun p f) /\
              ~~ b ==> (p == 1%g) && sorted leq (fgraph f)]) :=
  Do (let go := Fix (fun (loop : bubble_loopT a) '(i, sw) =>
                  Do (sw0 <-- cas_next a i;
                      let sw1 := sw || sw0 in
                      if decP (b := i < n) idP is left pf
                        then loop (So_lower (i:=i) pf, sw1)
                        else ret sw1))
      in go (ord0, false)).
Next Obligation.
move=>a loop _ i sw [f][] h /= [E V].
set i0 := Wo i; set i1 := So i.
apply: [stepE f]=>//= sw0 m [p][Hm Hsw]; case: decP=>Hin.
- (* i < n, recursive call *)
  apply: [gE (pffun p f)]=>//=.
  - split=>//; rewrite negb_or; case: sw0 Hsw=>/=; first by rewrite andbF.
    (* swap didn't happen *)
    rewrite andbT; case=>{p Hm}-> Hf; rewrite pffunE1.
    apply/(implyb_trans V)/implyP.
    rewrite So_lower_eq take_codom_rcons take_codom_rcons2 => H.
    rewrite sorted_rconsE; last by apply: leq_trans.
    rewrite H andbT all_rcons Hf /=.
    move: H; rewrite sorted_rconsE; last by apply: leq_trans.
    by case/andP=>+ _; apply/sub_all=>z Hz; apply/leq_trans/Hf.
  move=>v m0; case: sw0 Hsw=>/=; last by case=>-> _; rewrite orbF pffunE1.
  (* swap happened *)
  move=>_; rewrite orbT /=; case=>{v}->/= [p'][Hm0 _] _.
  rewrite implybT; split=>//=; exists (p' * p)%g; split=>//.
  by rewrite pffunEM.
(* i = n *)
have {}Hin : nat_of_ord i = n.
- apply/eqP; rewrite eqn_leq; move: (ltn_ord i); rewrite ltnS=>->/=.
  by move/negP: Hin; rewrite -leqNgt.
step=>Vm; split; first by apply/implyP=>->.
case: sw0 Hsw=>/=; case=>Ep Hf.
- (* swap happened on last iteration *)
  by rewrite orbT; exists p.
(* swap didn't happen on last iteration, check initial flag *)
rewrite orbF; case: sw V=>/=; first by move=>_; exists p.
(* flag wasn't set, so the pass didn't swap anything - the array is sorted *)
move=>Hs; exists p; split=>//; rewrite Ep eqxx /=.
rewrite -(take_size (codom f)) size_codom /= card_ord -[X in take X.+2 _]Hin.
rewrite take_codom_rcons in Hs.
rewrite take_codom_rcons2 sorted_rconsE; try by apply: leq_trans.
rewrite Hs andbT all_rcons Hf /=.
move: Hs; rewrite sorted_rconsE; last by apply: leq_trans.
by case/andP=>+ _; apply/sub_all=>z Hz; apply/leq_trans/Hf.
Qed.
Next Obligation.
move=>a [f][] h /= H.
apply: [gE f]=>//=; last by move=>v m [].
by split=>//; rewrite (ffun_split2 f ord0) /= take0.
Qed.

Opaque bubble_pass.

Definition bubble_sortT (a : {array 'I_n.+2 -> nat}) : Type :=
  unit ->
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (Array.shape a f,
        [vfun (_ : unit) h =>
           exists (p : 'S_n.+2),
             h \In Array.shape a (pffun p f) /\
             sorted leq (fgraph (pffun p f))]).

Program Definition bubble_sort (a : {array 'I_n.+2 -> nat}) :=
  Fix (fun (go : bubble_sortT a) _ =>
       Do (sw <-- bubble_pass a;
           if sw
             then skip;; go tt   (* hmm *)
             else skip)).
Next Obligation.
move=>a go _ [f][] h /= [E V].
apply: [stepE f]=>//=; case=>m.
- case=>p [Hm _]; step.
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
(* let bubble_pass_opt (a : array nat) (k : nat) : bool = *)
(*   let go (i : nat) (sw : bool) : bool =                *)
(*     let sw1 = sw || cas_next a i;                      *)
(*     if i < k then go (i+1) sw1 else sw1;               *)
(*   go 0 false                                           *)
(*                                                        *)
(* let bubble_sort_opt (a : array nat) : unit =           *)
(*   let go (k : nat) : unit =                            *)
(*     if bubble_pass_opt a k then go (k-1) else ();      *)
(*   go ((size a)-2).                                     *)
(**********************************************************)

Definition bubble_loop_optT (a : {array 'I_n.+2 -> nat}) (k : 'I_n.+1) :=
  forall isw : 'I_n.+1 * bool,
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (fun h => [/\ h \In Array.shape a f,
                      allrel leq (take k.+2 (fgraph f)) (drop k.+2 (fgraph f)),
                      sorted leq (drop k.+2 (fgraph f)),
                      isw.1 <= k,
                      (* more detailed property *)
                      all (leq^~ (f (Wo isw.1))) (take isw.1 (fgraph f)) &
                      ~~ isw.2 ==> sorted leq (take isw.1 (fgraph f))],
        [vfun (b : bool) h =>
          isw.2 ==> b /\
          exists (p : 'S_n.+2),
            let f' := pffun p f in
            h \In Array.shape a f' /\
            if b then
              allrel leq (take k.+1 (fgraph f')) (drop k.+1 (fgraph f')) &&
              sorted leq (drop k.+1 (fgraph f'))
            else (p == 1%g) && sorted leq (fgraph f)]).

Program Definition bubble_pass_opt (a : {array 'I_n.+2 -> nat}) (k : 'I_n.+1) :
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (fun h => [ /\ h \In Array.shape a f,
                       allrel leq (take k.+2 (fgraph f)) (drop k.+2 (fgraph f)) &
                       sorted leq (drop k.+2 (fgraph f)) ],
          [vfun (b : bool) h =>
            exists (p : 'S_n.+2),
              let f' := pffun p f in
              h \In Array.shape a f' /\
              if b then
                allrel leq (take k.+1 (fgraph f')) (drop k.+1 (fgraph f')) &&
                sorted leq (drop k.+1 (fgraph f'))
              else (p == 1%g) && sorted leq (fgraph f)]) :=
  Do (let go := Fix (fun (loop : bubble_loop_optT a k) '(i, sw) =>
                  Do (sw0 <-- cas_next a i;
                      let sw1 := sw || sw0 in
                      if decP (b := i < k) idP is left pf
                        then loop (So_lower (i:=i) pf, sw1)
                        else ret sw1))
      in go (ord0, false)).
Next Obligation.
(* show that So_lower is always safe *)
move=>_ k _ _ i _ _ /= E; rewrite E ltnS; symmetry.
by apply: (leq_trans E); rewrite -ltnS; apply: ltn_ord.
Qed.
Next Obligation.
move=>a k loop _ i sw [f][] h /= [Hs Ha He Hik Hia Hi].
set i0 := Wo i; set i1 := So i.
apply: [stepE f]=>//= sw0 m [p][Hm Hsw]; case: decP=>H.
- (* i < k, recursive call *)
  apply: [gE (pffun p f)]=>//=.
  - (* precondition *)
    rewrite So_lower_eq Wo_So_lower_eq negb_or; case: sw0 Hsw=>/=;
    case=>Ep Hf; rewrite {p}Ep ?pffunE1 in Hm *.
    - (* swap happened before the call *)
      rewrite andbF /= swapnx_drop //; split=>//.
      - rewrite (@allrel_in_l _ _ _ _ (take k.+2 (codom f))) //.
        by apply/perm_mem; rewrite perm_sym; apply: perm_take_swap_gt.
      rewrite take_swap_rcons all_rcons swapnxE2 Hia andbT.
      by apply: ltnW.
    (* swap didn't happen before the call *)
    rewrite andbT; split=>//.
    - rewrite take_codom_rcons all_rcons Hf /=.
      by apply/sub_all/Hia=>z Hz; apply/leq_trans/Hf.
    apply/(implyb_trans Hi)/implyP.
    rewrite take_codom_rcons sorted_rconsE; last by apply: leq_trans.
    by move=>->; rewrite andbT.
  move=>v m0; case: sw0 Hsw=>/= [_|[-> _]]; last by rewrite orbF pffunE1.
  (* swap happened *)
  rewrite orbT /=; case=>{v}-> [p'][Hm0 H'] _.
  by rewrite implybT; split=>//; exists (p' * p)%g; rewrite pffunEM.
(* i = k, exit *)
have {}Hik : nat_of_ord i = k.
- apply/eqP; rewrite eqn_leq Hik /=.
  by move/negP: H; rewrite -leqNgt.
step=>Vm; split; first by apply/implyP=>->.
case: sw0 Hsw=>/=; case=>Ep Hf.
- (* swap happened on last iteration *)
  rewrite -{H loop k}Hik in Ha He *; rewrite orbT; exists p.
  split=>//; rewrite Ep; apply/andP; split.
  - rewrite take_swap_rcons drop_swap_cons allrel_rconsl allrel_consr /=.
    move: Ha; rewrite take_codom_rcons2 !allrel_rconsl -/i0 -/i1 -andbA.
    by case/and3P=>-> _ ->; rewrite (ltnW Hf) /= !andbT.
  rewrite drop_swap_cons /= path_sortedE; last by exact: leq_trans.
  rewrite He andbT; apply/allP=>z Hz; move/allrelP: Ha; apply=>//.
  by rewrite take_codom_rcons2 4!(mem_rcons, inE) eqxx /= orbT.
(* swap didn't happen on last iteration *)
rewrite orbF; case: sw Hi=>/=.
- (* flag was set *)
  move=>_; exists p; split=>//; rewrite Ep pffunE1; apply/andP; split.
  - rewrite -Hik in Ha *.
    rewrite take_codom_rcons drop_codom_cons allrel_rconsl allrel_consr /=.
    move: Ha; rewrite take_codom_rcons2 !allrel_rconsl -andbA -/i0 -/i1.
    case/and3P=>->-> _; rewrite Hf /= !andbT.
    by apply/sub_all/Hia=>z Hz; apply/leq_trans/Hf.
  rewrite drop_codom_cons /= path_sortedE; last by exact: leq_trans.
  rewrite He andbT.
  by move: Ha; rewrite take_codom_rcons2 !allrel_rconsl -andbA; case/and3P.
(* flag wasn't set, so the pass didn't swap anything - the array is sorted *)
move=>Hs2; rewrite {p}Ep in Hm; exists 1%g; rewrite pffunE1 in Hm *; split=>//.
rewrite eqxx /= (ffun_split2 f i) -/i0 -/i1 /=; rewrite Hik in Hia Hs2 *.
rewrite sorted_pairwise; last by exact: leq_trans.
rewrite pairwise_cat /= -!sorted_pairwise; try by exact: leq_trans.
rewrite Hf He Hs2 /= andbT !allrel_consr -!andbA Hia /=.
move: Ha; rewrite -Hik take_codom_rcons2 !allrel_rconsl -andbA; case/and3P=>H1 H2 H3.
apply/and4P; split=>//.
by rewrite Hik; apply/sub_all/Hia=>z Hz; apply/leq_trans/Hf.
Qed.
Next Obligation.
move=>a k [f][] h /= [H Ha Hs].
apply: [gE f]=>//=; last by move=>v m [].
by rewrite take0.
Qed.

Opaque bubble_pass_opt.

Definition bubble_sort_optT (a : {array 'I_n.+2 -> nat}) : Type :=
  forall (k : 'I_n.+1),
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (fun h => [/\ h \In Array.shape a f,
                        allrel leq (take k.+2 (codom f)) (drop k.+2 (codom f)) &
                        sorted leq (drop k.+2 (codom f))],
        [vfun (_ : unit) h =>
          exists (p : 'S_n.+2),
            h \In Array.shape a (pffun p f) /\
            sorted leq (fgraph (pffun p f))]).

Program Definition bubble_sort_opt (a : {array 'I_n.+2 -> nat}) :
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (Array.shape a f,
        [vfun (_ : unit) h =>
          exists (p : 'S_n.+2),
            h \In Array.shape a (pffun p f) /\
            sorted leq (fgraph (pffun p f))]) :=
  Do (let go := Fix (fun (loop : bubble_sort_optT a) k =>
                     Do (sw <-- bubble_pass_opt a k;
                         if sw
                           then skip;; loop (Po k) (* hmm *)
                           else skip))
      in go ord_max).
Next Obligation.
move=>a go k [f][] h /= [H Ha Hs].
apply: [stepE f]=>{Ha Hs}//=; case=>m; last first.
- case=>p [Hm /andP [/eqP Ep Hsm]]; rewrite {p}Ep in Hm.
  by step=>_; exists 1%g; split=>//; rewrite pffunE1.
case=>p [Hm /andP [Ham Hsm]]; step.
apply: [gE (pffun p f)]=>//=; last first.
- move=> _ m2 [p'][H2 Hs'] _; exists (p' * p)%g.
  by rewrite pffunEM.
rewrite Po_eq; split=>//; last first.
- case: (posnP k)=>Hk; last by rewrite (prednK Hk).
  move: Hsm; rewrite Hk /= (ffun_split2 (pffun p f) ord0) /= take0 /= drop0.
  rewrite path_sortedE; last by exact: leq_trans.
  by case/andP.
case: (posnP k)=>Hk; last by rewrite (prednK Hk).
move: Ham Hsm; rewrite Hk /= (ffun_split2 (pffun p f) ord0) /= take0 /= take0 drop0.
rewrite allrel1l /=; case/andP=>H1 H2.
rewrite allrel_consl allrel1l H2 /= path_sortedE; last by exact: leq_trans.
by case/andP.
Qed.
Next Obligation.
move=>a [f][] h /= [E V].
have Hs: size (codom f) <= n.+2 by rewrite size_codom /= card_ord.
by apply: [gE f]=>//=; split=>//; rewrite drop_oversize // allrel0r.
Qed.

(*******************)
(* optimization #2 *)
(*******************)

(**********************************************************)
(* pseudocode, reusing cas_next:                          *)
(*                                                        *)
(* let bubble_pass_opt2 (a : array nat) (k : nat) : nat = *)
(*   let go (i : nat) (ls : nat) : nat =                  *)
(*     let ls1 = if cas_next a i then i+1 else ls;        *)
(*     if i < k then go (i+1) ls1 else ls1;               *)
(*   go 0 k                                               *)
(*                                                        *)
(* let bubble_sort_opt2 (a : array nat) : unit =          *)
(*   let go (k : nat) : unit =                            *)
(*     let k1 = bubble_pass_opt2 a k;                     *)
(*     if 1 < k1 then go (k1-1) else ();                  *)
(*   go ((size a)-2).                                     *)
(**********************************************************)

Definition bubble_loop_opt2T (a : {array 'I_n.+2 -> nat}) (k : 'I_n.+1) :=
  forall ils : 'I_n.+1 * 'I_n.+2,
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (fun h => [/\ h \In Array.shape a f,
                      allrel leq (take k.+2 (fgraph f)) (drop k.+2 (fgraph f)),
                      sorted leq (drop k.+2 (fgraph f)),
                      ils.2 <= ils.1,
                      ils.1 <= k,
                      (* ? *)
                      allrel leq (take ils.2 (fgraph f)) (drop ils.2 (take ils.1.+1 (codom f)))&
                      sorted leq (drop ils.2 (take ils.1.+1 (fgraph f)))],
        [vfun (j : 'I_n.+2) h =>
          ils.2 <= j < k.+2 /\
          exists (p : 'S_n.+2),
            let f' := pffun p f in
            h \In Array.shape a f' /\
            if 0 < j then
              allrel leq (take j (fgraph f')) (drop j (fgraph f')) &&
              sorted leq (drop j (fgraph f'))
            else (p == 1%g) && sorted leq (fgraph f)]).

Program Definition bubble_pass_opt2 (a : {array 'I_n.+2 -> nat}) (k : 'I_n.+1) :
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (fun h => [ /\ h \In Array.shape a f,
                       allrel leq (take k.+2 (fgraph f)) (drop k.+2 (fgraph f)) &
                       sorted leq (drop k.+2 (fgraph f)) ],
          [vfun (j : 'I_n.+2) h =>
            j < k.+2 /\
            exists (p : 'S_n.+2),
              let f' := pffun p f in
              h \In Array.shape a f' /\
              if 0 < j then
                allrel leq (take j (fgraph f')) (drop j (fgraph f')) &&
                sorted leq (drop j (fgraph f'))
            else (p == 1%g) && sorted leq (fgraph f)]) :=
  Do (let go := Fix (fun (loop : bubble_loop_opt2T a k) '(i, ls) =>
                  Do (sw <-- cas_next a i;
                      let ls1 := if sw then (So i) else ls in
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
move=>a k loop _ i ls [f][] h /= [Hs Ha He Hils Hik Hia Hls].
set i0 := Wo i; set i1 := So i.
apply: [stepE f]=>//= sw m [p][Hm Hsw]; case: decP=>H.
- (* i < k, recursive call *)
  apply: [gE (pffun p f)]=>//=.
  - (* precondition *)
    rewrite So_lower_eq; case: sw Hsw=>/=;
    case=>Ep Hf; rewrite {p}Ep ?pffunE1 in Hm *.
    - (* swap happened before the call *)
      rewrite So_eq swapnx_drop; last by rewrite ltnS; apply: ltnW.
      have Ei : size (rcons (take i (codom f)) (f (So i))) = i.+1.
      - by rewrite size_rcons size_take_codom.
      have -> : drop i.+1 (take i.+2 (codom (pffun (pswnx i) f))) = [:: f (Wo i)].
      - rewrite swap_split2 take_cat size_take_codom leqNgt ltnS -(addn2 i) leq_addr /=.
        rewrite -addnBAC // subnn /= take0 /= -cat1s catA !cats1 drop_rcons; last by rewrite Ei.
        by rewrite -Ei drop_size.
      split=>//.
      - rewrite (@allrel_in_l _ _ _ _ (take k.+2 (codom f))) //.
        by apply/perm_mem; rewrite perm_sym; apply: perm_take_swap_gt.
      rewrite allrel1r take_swap_rcons all_rcons (ltnW Hf) /=.
      move: Hls; rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
      rewrite sorted_rconsE; last by exact: leq_trans.
      case/andP=>Ha1 Hs1; rewrite -(cat_take_drop ls (take i (codom f))) all_cat Ha1 andbT.
      rewrite take_take //.
      apply/sub_all/Hia=>z /= /allP; apply.
      rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
      by rewrite mem_rcons inE eqxx.
    (* swap didn't happen before the call *)
    split=>//.
    - by apply: ltnW.
    - rewrite take_codom_rcons2 drop_rcons; last by rewrite size_rcons size_take_codom; apply: ltnW.
      rewrite -take_codom_rcons allrel_rconsr Hia /=.
      suff: all (leq^~ (f (Wo i))) (take ls (codom f)).
      - by apply/sub_all=>z Hz; apply/leq_trans/Hf.
      apply/sub_all/Hia=>z /= /allP; apply.
      rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
      by rewrite mem_rcons inE eqxx.
    rewrite take_codom_rcons2 drop_rcons; last by rewrite size_rcons size_take_codom; apply: ltnW.
    rewrite sorted_rconsE; last by exact: leq_trans.
    rewrite -{2}take_codom_rcons Hls andbT.
    rewrite drop_rcons; last by rewrite size_take_codom.
    rewrite all_rcons Hf /=.
    move: Hls; rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
    rewrite sorted_rconsE; last by exact: leq_trans.
    by case/andP=>+ _; apply/sub_all=>z Hz; apply/leq_trans/Hf.
  move=>j m0; case: sw Hsw=>/= [_|[-> _]]; last by rewrite pffunE1.
  (* swap happened *)
  case=>/andP [Hji Hjk] [p'][Hm0].
  have->/= : 0 < j by apply/leq_trans/Hji; rewrite lt0n So_eq.
  move=>H' _; split; first by rewrite Hjk andbT; apply/leq_trans/Hji; rewrite So_eq; apply: ltnW.
  by exists (p' * p)%g; rewrite pffunEM.
(* i = k, exit *)
have {H}Hik : nat_of_ord i = k.
- apply/eqP; rewrite eqn_leq Hik /=.
  by move/negP: H; rewrite -leqNgt.
step=>Vm; case: sw Hsw=>/=; case=>Ep Hf.
- (* swap happened on last iteration *)
  rewrite -{loop k}Hik in Ha He *; rewrite So_eq; split=>/=.
  - by rewrite ltnS leqnn andbT; apply: ltnW.
  exists p; split=>//; rewrite Ep; apply/andP; split.
  - rewrite take_swap_rcons drop_swap_cons allrel_rconsl allrel_consr /=.
    move: Ha; rewrite take_codom_rcons2 !allrel_rconsl -/i0 -/i1 -andbA.
    case/and3P=>-> _ ->; rewrite (ltnW Hf) /= !andbT.
    rewrite -(cat_take_drop ls (take i (codom f))) all_cat take_take //.
    move: Hls; rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
    rewrite sorted_rconsE; last by exact: leq_trans.
    case/andP=>-> ?; rewrite andbT.
    apply/sub_all/Hia=>z /= /allP; apply.
    rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
    by rewrite mem_rcons inE eqxx.
  rewrite drop_swap_cons /= path_sortedE; last by exact: leq_trans.
  rewrite He andbT; apply/allP=>z Hz; move/allrelP: Ha; apply=>//.
  by rewrite take_codom_rcons2 4!(mem_rcons, inE) eqxx /= orbT.
(* swap didn't happen on last iteration *)
split; first by rewrite leqnn /= -Hik ltnS; apply: ltnW.
case: (posnP ls); last first.
- (* swap happened previously *)
  move=>Nls; exists p; split=>//; rewrite Ep pffunE1.
  rewrite -{k loop}Hik in Ha He *.
  have El2 : ls <= i.+2 by apply/ltnW/ltnW.
  set q := i.+2 - ls.
  have E1 : i.+2 = ls + q by rewrite subnKC.
  have E2 : nat_of_ord ls = i.+2 - q by rewrite subnA // subnn.
  (* TODO streamline *)
  apply/andP; split; last first.
  - rewrite -(cat_take_drop q (drop ls (codom f))) drop_drop addnC -E1.
    rewrite sorted_pairwise; last by exact: leq_trans.
    rewrite pairwise_cat -!sorted_pairwise; try by exact: leq_trans.
    rewrite He andbT take_drop addnC -E1.
    apply/andP; split.
    - apply/allrel_sub_l/Ha=>z Hz.
      by rewrite -{1}(cat_take_drop ls ((take i.+2 (codom f)))) mem_cat Hz orbT.
    rewrite take_codom_rcons2 drop_rcons; last by rewrite size_rcons size_take_codom; apply: ltnW.
    rewrite sorted_rconsE; last by exact: leq_trans.
    rewrite -{2}take_codom_rcons Hls andbT.
    rewrite drop_rcons; last by rewrite size_take_codom.
    rewrite all_rcons Hf /=.
    move: Hls; rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
    rewrite sorted_rconsE; last by exact: leq_trans.
    by case/andP=>+ _; apply/sub_all=>z Hz; apply/leq_trans/Hf.
  rewrite -{2}(cat_take_drop i.+1 (codom f)) drop_cat size_take size_codom card_ord ltnS ltn_ord ltnS Hils.
  rewrite allrel_catr Hia /=.
  rewrite drop_codom_cons allrel_consr; apply/andP; split.
  - suff: all (leq^~ (f (Wo i))) (take ls (codom f)).
    - by apply/sub_all=>z Hz; apply/leq_trans/Hf.
    apply/sub_all/Hia=>z /allP; apply.
    rewrite take_codom_rcons drop_rcons; last by rewrite size_take_codom.
    by rewrite mem_rcons inE eqxx.
  apply/allrel_sub_l/Ha=>z Hz.
  by rewrite -(cat_take_drop ls (take i.+2 (codom f))) take_take // mem_cat Hz.
move=>Els; exists 1%g; rewrite {p}Ep in Hm; rewrite pffunE1 in Hm *; split=>//.
rewrite eqxx /= (ffun_split2 f i) -/i0 -/i1 /=; rewrite Hik Els drop0 in Hls *.
rewrite sorted_pairwise; last by exact: leq_trans.
rewrite pairwise_cat /= -!sorted_pairwise; try by exact: leq_trans.
rewrite Hf He !allrel_consr -!andbA andbT.
move: Hls; rewrite -Hik take_codom_rcons sorted_rconsE; last by exact: leq_trans.
case/andP=>Ha' -> /=.
move: Ha; rewrite -Hik take_codom_rcons2 !allrel_rconsl -andbA; case/and3P=>H1 H2 H3.
apply/and5P; split=>//.
by apply/sub_all/Ha'=>z Hz; apply/leq_trans/Hf.
Qed.
Next Obligation.
move=>a k [f][] h /= [H Ha Hs].
apply: [gE f]=>//=.
rewrite take0 drop0 allrel0l; split=>//.
by rewrite (ffun_split2 f ord0) /= take0.
Qed.

Opaque bubble_pass_opt2.

Definition bubble_sort_opt2T (a : {array 'I_n.+2 -> nat}) : Type :=
  forall (k : 'I_n.+1),
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (fun h => [/\ h \In Array.shape a f,
                        allrel leq (take k.+2 (codom f)) (drop k.+2 (codom f)) &
                        sorted leq (drop k.+2 (codom f))],
        [vfun (_ : unit) h =>
          exists (p : 'S_n.+2),
            h \In Array.shape a (pffun p f) /\
            sorted leq (fgraph (pffun p f))]).

Program Definition bubble_sort_opt2 (a : {array 'I_n.+2 -> nat}) :
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (Array.shape a f,
        [vfun (_ : unit) h =>
          exists (p : 'S_n.+2),
            h \In Array.shape a (pffun p f) /\
            sorted leq (fgraph (pffun p f))]) :=
  Do (let go := Fix (fun (loop : bubble_sort_opt2T a) k =>
                     Do (k1 <-- bubble_pass_opt2 a k;
                         if decP (b := 1 < k1) idP is left pf
                           then skip;; loop (Po_lower (i:=k1) pf) (* hmm *)
                           else skip))
      in go ord_max).
Next Obligation.
move=>_ _ _ k1 E _; rewrite E; symmetry.
by apply/ltn_trans/E.
Qed.
Next Obligation.
move=>a go k [f][] h /= [H Ha Hs].
apply: [stepE f]=>{Ha Hs}//= x m [Hxk][p][Hm Hx].
case: decP=>Ex; last first.
- step=>Vm; exists p; split=>//.
  move/negP: Ex; rewrite -leqNgt; case: (posnP x).
  - move=>Ex _; move: Hx; rewrite Ex ltnn.
    by case/andP=>/eqP->; rewrite pffunE1.
  case: (nat_of_ord x) Hx=>//; case=>//=; case/andP=>Ha1 Hs1 _ _.
  rewrite -(cat_take_drop 1 (codom (pffun p f))) sorted_pairwise; last by exact: leq_trans.
  rewrite pairwise_cat -!sorted_pairwise; try by exact: leq_trans.
  by rewrite Ha1 Hs1 /= andbT (ffun_split2 (pffun p f) ord0) /= take0.
have Hx0 : (0 < x) by apply/ltn_trans/Ex.
rewrite Hx0 in Hx.
step; apply: [gE (pffun p f)]=>//=; last first.
- move=> _ m2 [p'][H2 Hs'] _; exists (p' * p)%g.
  by rewrite pffunEM.
move: (Po_lower_eq (eq_rect (1 < x) (eq^~ true) Ex (0 < x) (bubble_sort_opt2_obligation_1 Ex)))=>->.
rewrite prednK //; split=>//.
- rewrite take_codom_rcons.

case: (posnP x). by move=>Ex'; rewrite Ex' in Hx0.
case: {Ex}x Hx0 Hx.

move: (Po_lower_eq).


case: (0 < x). case=>m; last first.
- case=>p [Hm /andP [/eqP Ep Hsm]]; rewrite {p}Ep in Hm.
  by step=>_; exists 1%g; split=>//; rewrite pffunE1.
case=>p [Hm /andP [Ham Hsm]]; step.
apply: [gE (pffun p f)]=>//=; last first.
- move=> _ m2 [p'][H2 Hs'] _; exists (p' * p)%g.
  by rewrite pffunEM.
rewrite Po_eq; split=>//; last first.
- case: (posnP k)=>Hk; last by rewrite (prednK Hk).
  move: Hsm; rewrite Hk /= (ffun_split2 (pffun p f) ord0) /= take0 /= drop0.
  rewrite path_sortedE; last by exact: leq_trans.
  by case/andP.
case: (posnP k)=>Hk; last by rewrite (prednK Hk).
move: Ham Hsm; rewrite Hk /= (ffun_split2 (pffun p f) ord0) /= take0 /= take0 drop0.
rewrite allrel1l /=; case/andP=>H1 H2.
rewrite allrel_consl allrel1l H2 /= path_sortedE; last by exact: leq_trans.
by case/andP.
Qed.
Next Obligation.
move=>a [f][] h /= [E V].
have Hs: size (codom f) <= n.+2 by rewrite size_codom /= card_ord.
by apply: [gE f]=>//=; split=>//; rewrite drop_oversize // allrel0r.
Qed.

End Bubble.

