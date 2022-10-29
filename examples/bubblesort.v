From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype tuple finfun finset.
From fcsl Require Import options axioms prelude pred ordtype.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import interlude model heapauto.
From HTT Require Import array.

Lemma implyb_trans a b c : a ==> b -> b ==> c -> a ==> c.
Proof. by case: a=>//=->. Qed.

Lemma cat2s {T} (a b : T) xs : [:: a, b & xs] = [::a] ++ [::b] ++ xs.
Proof. by []. Qed.

(* TODO use fintype.lift instead ? *)

Lemma ord_indx n (i : 'I_n) : heap.indx i = i.
Proof. by exact: index_enum_ord. Qed.

(* widen by 1 *)
Definition Wo n : 'I_n -> 'I_n.+1 :=
  widen_ord (leqnSn _).

(* increase by 1 *)
Definition So n : 'I_n -> 'I_n.+1 :=
  fun '(@Ordinal _ m prf) => @Ordinal n.+1 m.+1 prf.

Lemma So_eq n (i : 'I_n) : nat_of_ord (So i) = i.+1.
Proof. by case: i. Qed.

(* increase within the bound *)
Definition So_lower n (i : 'I_n) (prf : i.+1 < n) : 'I_n.
Proof. case: i prf=>/= m Hm; apply: Ordinal. Defined.

Lemma So_lower_eq n (i : 'I_n) (prf : i.+1 < n) : nat_of_ord (So_lower prf) = i.+1.
Proof. by case: i prf. Qed.

Opaque Array.write Array.read.

Section bubble.
Variable (n : nat).

(* TODO ordType! *)

Lemma ffun_split2 A (f : {ffun 'I_n.+2 -> A}) (i : 'I_n.+1) :
  let i0 := Wo i in let i1 := So i in
  codom f = take i0 (codom f) ++ [:: f i0; f i1] ++ drop i1.+1 (codom f).
Proof.
set i0 := Wo i; set i1 := So i.
rewrite {1}codomE (enum_split i0) /= {2}(enum_split i1) (ord_indx i0) (ord_indx i1).
rewrite drop_cat size_take size_enum_ord ltn_ord So_eq ltnn subnn /=.
by rewrite map_cat /= map_take map_drop -codomE.
Qed.

Program Definition cas_next (a : {array 'I_n.+2 -> nat}) (i : 'I_n.+1) :
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (Array.shape a f,
        [vfun (b : bool) h =>
          let i0 := Wo i in let i1 := So i in
          exists (f' : {ffun 'I_n.+2 -> nat}),
            h \In Array.shape a f' /\
            if b then
              codom f' =
                take i0 (codom f) ++
                [:: f i1; f i0] ++
                drop i1.+1 (codom f)
              /\ f i1 < f i0
            else f' = f /\ f i0 <= f i1]) :=
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
case: leqP=>H; first by step=>_; exists f.
apply: [stepE f]=>//= _ _ [-> Vs]; set fs := finfun [eta f with i0 |-> f i1].
apply: [stepE fs]=>//= _ _ [-> Vsw]; set fsw := finfun [eta fs with i1 |-> f i0].
step=>_; exists fsw; do!split=>//.
(* TODO streamline *)
rewrite /fsw codomE (enum_split i1) /= map_cat /= map_take map_drop takeord dropord /=.
rewrite /fs codomE (enum_split i0) /= map_cat /= map_take map_drop takeord dropord /=.
rewrite !ffunE /= !eqxx take_cat size_take.
rewrite {1 3}(ord_indx i1) {1 2 5 6}(ord_indx i0) size_codom card_ord ltn_ord So_eq /=.
rewrite leqNgt ltnS leqnSn /= subSnn /= take0.
rewrite drop_cat size_take size_codom card_ord.
rewrite {1 3}(ord_indx i1) {2 3 6 7}(ord_indx i0) ltn_ord So_eq /=.
rewrite leqNgt ltnS -[X in _ <= X]addn2 leq_addr /=.
rewrite -[X in drop (X - _)]addn2 -addnBAC // subnn /= drop_drop add1n.
by rewrite {2}(ord_indx i0) -(So_eq i) -(ord_indx i1) -catA ord_indx.
Qed.

Opaque cas_next.

Definition bubble_loopT (a : {array 'I_n.+2 -> nat}) :=
  forall isw : ('I_n.+1 * bool),
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (fun h => h \In Array.shape a f
               /\ (~~ isw.2) ==> sorted leq (take isw.1.+1 (fgraph f)),
        [vfun (b : bool) h =>
          isw.2 ==> b /\
          if b then
            exists f',
              h \In Array.shape a f' /\
              perm_eq (fgraph f) (fgraph f')
            else h \In Array.shape a f /\ sorted leq (codom f)]).

Program Definition bubble_pass (a : {array 'I_n.+2 -> nat}) :
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (Array.shape a f,
          [vfun (b : bool) h =>
            if b then
              exists f',
                h \In Array.shape a f' /\
                perm_eq (fgraph f) (fgraph f')
              else h \In Array.shape a f /\ sorted leq (codom f)]) :=
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
apply: [stepE f]=>//= sw0 m [f'][Hm Hsw]; case: decP=>H.
- (* i < n, recursive call *)
  apply: [gE f']=>//=.
  - split=>//; rewrite negb_or; case: sw0 Hsw=>/=; first by rewrite andbF.
    (* swap didn't happen *)
    rewrite andbT; case=>-> Hf01; apply/(implyb_trans V)/implyP=>Hs.
    rewrite So_lower_eq; move: Hs.
    rewrite (ffun_split2 f i) -/i0 -/i1 !take_cat size_take size_codom /= card_ord.
    rewrite !ltnS (leq_eqVlt i) ltn_ord orbT (leqNgt i.+2) (leqNgt i.+3) !ltnS.
    rewrite leqnSn -(addn2 i) leq_addr /= subSnn -addnBAC // subnn /= take0 cats1=>Hs.
    rewrite -cat1s catA !cats1 sorted_rconsE; last by apply: leq_trans.
    rewrite Hs andbT all_rcons Hf01 /=.
    move: Hs; rewrite sorted_rconsE; last by apply: leq_trans.
    by case/andP=>+ _; apply: sub_all=>z Hz; apply/leq_trans/Hf01.
  move=>v m0; case: sw0 Hsw=>/=; last by case=>-> Hf; rewrite orbF.
  (* swap happened *)
  case=>Hf' Hf; rewrite orbT /=; case=>{v}-> [f''][Hm0 Hf''] Vm0.
  rewrite implybT; split=>//; exists f''; split=>//.
  apply/perm_trans/Hf''; rewrite (ffun_split2 f i) -/i0 -/i1 Hf' /=.
  by apply/permEl/perm_catl; rewrite !cat2s -perm_catCA.
(* i = n *)
have {}H : nat_of_ord i = n.
- apply/eqP; rewrite eqn_leq; move: (ltn_ord i); rewrite ltnS=>->/=.
  by move/negP: H; rewrite -leqNgt.
step=>Vm; split; first by apply/implyP=>->.
case: sw0 Hsw=>/=; case=>Ef' Hf; last first.
- (* swap didn't happen on last iteration *)
  rewrite orbF; case: sw V=>/=.
  - (* flag was set *)
    by move=>_; exists f'; split=>//; rewrite Ef'.
  (* flag wasn't set, so the pass didn't swap anything *)
  move=>Hs; split; first by rewrite -Ef'.
  move: Hs; rewrite (ffun_split2 f i) /= So_eq H !take_cat size_take size_codom /= card_ord.
  rewrite ltnS leqnSn leqNgt ltnS leqnSn /= subSnn /= cats1=>Hs.
  rewrite [X in drop X _](_ : n.+2 = size (codom f)); last by rewrite size_codom /= card_ord.
  rewrite drop_size -cat1s catA !cats1 sorted_rconsE; last by apply: leq_trans.
  rewrite Hs andbT all_rcons Hf /=.
  move: Hs; rewrite sorted_rconsE; last by apply: leq_trans.
  by case/andP=>+ _; apply: sub_all=>z Hz; apply/leq_trans/Hf.
(* swap happened on last iteration *)
rewrite orbT; exists f'; split=>//.
rewrite (ffun_split2 f i) -/i0 -/i1 Ef' /=.
by apply/permEl/perm_catl; rewrite !cat2s -perm_catCA.
Qed.
Next Obligation.
move=>a [f][] h /= [E V].
apply: [gE f]=>//=; first by split=>//; rewrite (ffun_split2 f ord0) /= take0.
by move=>v m; case.
Qed.

Opaque bubble_pass.

Definition bubble_sortT (a : {array 'I_n.+2 -> nat}) : Type :=
  unit ->
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (Array.shape a f,
        [vfun (_ : unit) h => exists f',
          [/\ h \In Array.shape a f',
              perm_eq (fgraph f) (fgraph f') &
              sorted leq (fgraph f')]]).

Program Definition bubble_sort (a : {array 'I_n.+2 -> nat}) :=
  Fix (fun (go : bubble_sortT a) _ =>
       Do (sw <-- bubble_pass a;
           if sw
             then go tt;; skip  (* hmm *)
             else ret tt)).
Next Obligation.
move=>a go _ [f][] h /= [E V].
apply: [stepE f]=>//=; case=>m.
- case=>f' [Hm Hp].
  apply: [stepE f']=>//= _ m2 [f''][H2 Hp' Hs']; step=>_; exists f''.
  by split=>//; apply/perm_trans/Hp'.
by case=>Hm Hs; step=>_; exists f.
Qed.