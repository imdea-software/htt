From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype tuple finfun finset.
From fcsl Require Import options axioms prelude pred ordtype.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import interlude model heapauto.
From HTT Require Import array.

Lemma allrel_rconsl (T S : Type) (r : T -> S -> bool)
                    x xs ys : allrel r (rcons xs x) ys = allrel r xs ys && all (r x) ys.
Proof. by rewrite -cats1 allrel_catl allrel1l. Qed.

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
Proof.
case: i prf=>/= m prf0 prf1.
rewrite /Wo /widen_ord.
by congr Ordinal; apply: pf_irr.
Qed.

Section codom.
Variable (n : nat).

Lemma size_take_codom T (i : 'I_n) (f: {ffun 'I_n.+1 -> T}) : size (take i (codom f)) = i.
Proof.
by rewrite size_take size_codom card_ord ltnS leq_eqVlt ltn_ord orbT.
Qed.

Lemma ffun_split2 A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  let i0 := Wo i in let i1 := So i in
  codom f = take i0 (codom f) ++ [:: f i0; f i1] ++ drop i1.+1 (codom f).
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
by rewrite {1}(ffun_split2 f i) drop_cat size_take_codom leqNgt ltnS leqnSn /= subSnn /= So_eq.
Qed.

Lemma take_codom_rcons2 A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  take i.+2 (codom f) = rcons (rcons (take i (codom f)) (f (Wo i))) (f (So i)).
Proof.
rewrite {1}(ffun_split2 f i) take_cat size_take_codom leqNgt ltnS -addn2 leq_addr /=.
by rewrite -addnBAC // subnn /= take0 -cat1s catA !cats1.
Qed.

End codom.

Section swap.
Variable (n : nat).

Definition swap T n (i : 'I_n) (f: {ffun 'I_n.+1 -> T}) : {ffun 'I_n.+1 -> T} :=
  let i0 := Wo i in let i1 := So i in
  finfun [eta f with i0 |-> f i1, i1 |-> f i0].

Lemma swapE A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  ((swap i f) (Wo i) = f (So i)) * ((swap i f) (So i) = f (Wo i)).
Proof.
rewrite /swap !ffunE /= !eqxx; split=>//.
by case: eqP=>//->.
Qed.

(* TODO generalize to k <= i *)
Lemma swap_take A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  take i (fgraph (swap i f)) = take i (fgraph f).
Proof.
rewrite /swap; set f' := (finfun _).
suff E: {in take i (enum 'I_n.+1), f =1 f'}.
- by rewrite !fgraph_codom /= !codomE -2!map_take; move/eq_in_map: E.
move=>/= y /index_ltn; rewrite /f' /= !ffunE /=; case: eqP.
- by move=>->; rewrite index_enum_ord ltnn.
by case: eqP=>//->_; rewrite index_enum_ord So_eq ltnNge leqnSn.
Qed.

Lemma swap_drop A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  drop i.+2 (fgraph (swap i f)) = drop i.+2 (fgraph f).
Proof.
rewrite /swap; set f' := (finfun _).
suff E: {in drop i.+2 (enum 'I_n.+1), f =1 f'}.
- by rewrite /= !codomE -2!map_drop /=; move/eq_in_map: E.
move=>/= y /index_gtn; rewrite /f' /= !ffunE /=; case: eqP.
- move=>->; rewrite index_last_uniq; last by apply: enum_uniq.
  by rewrite index_enum_ord /= ltnNge leqnSn.
case: eqP=>//->_; rewrite index_last_uniq; last by apply: enum_uniq.
by rewrite index_enum_ord So_eq ltnn.
Qed.

Lemma swap_split2 A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  let i0 := Wo i in let i1 := So i in
  codom (swap i f) = take i0 (codom f) ++ [:: f i1; f i0] ++ drop i1.+1 (codom f).
Proof.
rewrite /swap; set i0 := Wo i; set i1 := So i.
rewrite codomE (enum_split i0) (enum_split i1) !ord_indx /=.
rewrite take_cat drop_cat size_take size_enum_ord ltn_ord So_eq ltnS leqnn ltnn take_take;
  last by exact: leqnSn.
rewrite subnn drop0 map_cat /= !ffunE /= !eqxx.
rewrite (_ : i1 == i0 = false); last by apply/negbTE/So_WoN.
by rewrite map_take map_drop swap_take swap_drop.
Qed.

Lemma drop_swap_cons A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  drop i.+1 (fgraph (swap i f)) = f (Wo i) :: drop i.+2 (fgraph f).
Proof.
rewrite fgraph_codom /= swap_split2 drop_cat size_take size_codom /= card_ord.
rewrite !ltnS (leq_eqVlt i) ltn_ord orbT (leqNgt i.+2) ltnS leqnSn /= subSnn /=.
by rewrite So_eq.
Qed.

Lemma take_swap_rcons A (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  take i.+1 (codom (swap i f)) = rcons (take i (codom f)) (f (So i)).
Proof.
by rewrite swap_split2 take_cat size_take_codom (leqNgt i.+2) ltnS leqnSn /= subSnn /= cats1.
Qed.

Lemma perm_swap {A : eqType} (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) :
  perm_eq (codom f) (codom (swap i f)).
Proof.
rewrite (ffun_split2 f i) swap_split2 /=.
by apply/permEl/perm_catl; rewrite !cat2s -perm_catCA.
Qed.

Lemma perm_take_swap_gt {A : eqType} (f : {ffun 'I_n.+1 -> A}) (i : 'I_n) k :
  i <= k ->
  perm_eq (take k.+2 (codom f)) (take k.+2 (codom (swap i f))).
Proof.
move=>H.
rewrite (ffun_split2 f i) swap_split2 /= !take_cat size_take_codom leqNgt ltnS.
have ->/= : i <= k.+2 by apply: (leq_trans H); rewrite -addn2; apply: leq_addr.
rewrite -(addn2 k) -addnBAC // addn2 /=.
by apply/permPl/perm_catl; rewrite !cat2s perm_catCA.
Qed.

End swap.

Opaque Array.write Array.read.

Section bubble.
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
          exists (f' : {ffun 'I_n.+2 -> nat}),
            h \In Array.shape a f' /\
            if b
              then f' = swap i f /\ f i1 < f i0
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
rewrite /fsw /fs /swap -/i0 -/i1.
apply/ffunP=>/= x; rewrite !ffunE /= ffunE /=.
by case: eqP; case: eqP=>// ->->.
Qed.

Opaque cas_next.

Definition bubble_loopT (a : {array 'I_n.+2 -> nat}) :=
  forall isw : 'I_n.+1 * bool,
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (fun h => h \In Array.shape a f
               /\ ~~ isw.2 ==> sorted leq (take isw.1.+1 (fgraph f)),
        [vfun (b : bool) h =>
          isw.2 ==> b /\
          if b then
            exists f',
              h \In Array.shape a f' /\
              perm_eq (fgraph f) (fgraph f')
            else h \In Array.shape a f /\ sorted leq (fgraph f)]).

Program Definition bubble_pass (a : {array 'I_n.+2 -> nat}) :
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (Array.shape a f,
          [vfun (b : bool) h =>
            if b then
              exists f',
                h \In Array.shape a f' /\
                perm_eq (fgraph f) (fgraph f')
              else h \In Array.shape a f /\ sorted leq (fgraph f)]) :=
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
apply: [stepE f]=>//= sw0 m [f'][Hm Hsw]; case: decP=>Hin.
- (* i < n, recursive call *)
  apply: [gE f']=>//=.
  - split=>//; rewrite negb_or; case: sw0 Hsw=>/=; first by rewrite andbF.
    (* swap didn't happen *)
    rewrite andbT; case=>-> Hf01; apply/(implyb_trans V)/implyP.
    rewrite So_lower_eq take_codom_rcons take_codom_rcons2.
    rewrite !sorted_rconsE; try by apply: leq_trans.
    case/andP=>Ha ->; rewrite Ha /= andbT all_rcons Hf01 /=.
    by apply/sub_all/Ha=>z Hz; apply/leq_trans/Hf01.
  move=>v m0; case: sw0 Hsw=>/=; last by case=>-> Hf; rewrite orbF.
  (* swap happened *)
  case=>Hf' Hf; rewrite orbT /=; case=>{v}-> [f''][Hm0 Hf''] Vm0.
  rewrite implybT; split=>//; exists f''; split=>//.
  by apply/perm_trans/Hf''; rewrite Hf'; apply: perm_swap.
(* i = n *)
have {}Hin : nat_of_ord i = n.
- apply/eqP; rewrite eqn_leq; move: (ltn_ord i); rewrite ltnS=>->/=.
  by move/negP: Hin; rewrite -leqNgt.
step=>Vm; split; first by apply/implyP=>->.
case: sw0 Hsw=>/=; case=>Ef' Hf.
- (* swap happened on last iteration *)
  by rewrite orbT; exists f'; split=>//; rewrite Ef'; exact: perm_swap.
(* swap didn't happen on last iteration *)
rewrite orbF; case: sw V=>/=.
- (* flag was set *)
  by move=>_; exists f'; split=>//; rewrite Ef'.
(* flag wasn't set, so the pass didn't swap anything - the array is sorted *)
move=>Hs; split; first by rewrite -Ef'.
rewrite -(take_size (codom f)) size_codom /= card_ord -[X in take X.+2 _]Hin.
move: Hs; rewrite take_codom_rcons take_codom_rcons2 !sorted_rconsE; try by apply: leq_trans.
case/andP=>Ha ->; rewrite Ha /= andbT all_rcons Hf /=.
by apply/sub_all/Ha=>z Hz; apply/leq_trans/Hf.
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
        [vfun (_ : unit) h => exists f',
          [/\ h \In Array.shape a f',
              perm_eq (fgraph f) (fgraph f') &
              sorted leq (fgraph f')]]).

Program Definition bubble_sort (a : {array 'I_n.+2 -> nat}) :=
  Fix (fun (go : bubble_sortT a) _ =>
       Do (sw <-- bubble_pass a;
           if sw
             then skip;; go tt   (* hmm *)
             else skip)).
Next Obligation.
move=>a go _ [f][] h /= [E V].
apply: [stepE f]=>//=; case=>m.
- case=>f' [Hm Hp]; step.
  apply: [gE f']=>//= _ m2 [f''][H2 Hp' Hs']; exists f''.
  by split=>//; apply/perm_trans/Hp'.
by case=>Hm Hs; step=>_; exists f.
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
(*     if bubble_pass a k then go (k-1) else ();          *)
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
          if b then
            exists f',
              [/\ h \In Array.shape a f',
                  perm_eq (fgraph f) (fgraph f'),
                  allrel leq (take k.+1 (fgraph f')) (drop k.+1 (fgraph f')) &
                  sorted leq (drop k.+1 (fgraph f'))]
            else h \In Array.shape a f /\ sorted leq (fgraph f)]).

Program Definition bubble_pass_opt (a : {array 'I_n.+2 -> nat}) (k : 'I_n.+1) :
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (fun h => [ /\ h \In Array.shape a f,
                       allrel leq (take k.+2 (fgraph f)) (drop k.+2 (fgraph f)) &
                       sorted leq (drop k.+2 (fgraph f)) ],
          [vfun (b : bool) h =>
            if b then
              exists f',
              [/\ h \In Array.shape a f',
                  perm_eq (fgraph f) (fgraph f'),
                  allrel leq (take k.+1 (fgraph f')) (drop k.+1 (fgraph f')) &
                  sorted leq (drop k.+1 (fgraph f'))]
              else h \In Array.shape a f /\ sorted leq (fgraph f)]) :=
  Do (let go := Fix (fun (loop : bubble_loop_optT a k) '(i, sw) =>
                  Do (sw0 <-- cas_next a i;
                      let sw1 := sw || sw0 in
                      if decP (b := i < k) idP is left pf
                        then loop (So_lower (i:=i) pf, sw1)
                        else ret sw1))
      in go (ord0, false)).
Next Obligation.
move=>_ k _ _ i _ _ /= E; rewrite E ltnS; symmetry.
by apply: (leq_trans E); rewrite -ltnS; apply: (ltn_ord k).
Qed.
Next Obligation.
move=>a k loop _ i sw [f][] h /= [Hs Ha He Hik Hia Hi].
set i0 := Wo i; set i1 := So i.
apply: [stepE f]=>//= sw0 m [f'][Hm Hsw]; case: decP=>H.
- (* i < k, recursive call *)
  apply: [gE f']=>//=.
  - (* precondition *)
    rewrite negb_or; case: sw0 Hsw=>/=; case=>Ef H01.
    - (* swap happened before the call *)
      have Hf' : drop k.+2 (codom f') = drop k.+2 (codom f).
      - rewrite Ef swap_split2 drop_cat size_take_codom (leqNgt k.+3).
        have ->/= : i < k.+3 by apply: (ltn_trans H); rewrite ltnS -addn2 leq_addr.
        by rewrite -(addn2 k) -addnBAC // addn2 /= drop_drop So_eq !addnS subnK // addn0.
      rewrite andbF /= Hf'; split=>//.
      - rewrite (@allrel_in_l _ _ _ _ (take k.+2 (codom f))) // Ef.
        by apply/perm_mem; rewrite perm_sym; apply: perm_take_swap_gt.
      - by rewrite So_lower_eq.
      rewrite So_lower_eq Wo_So_lower_eq; rewrite -/i0 -/i1 in Hia *.
      rewrite Ef take_swap_rcons all_rcons.
      suff: (swap i f) i1 = f i0 by move=>->; rewrite Hia andbT; apply: ltnW.
      by rewrite swapE.
    (* swap didn't happen before the call *)
    rewrite andbT Ef in Hm *; split=>//; first by rewrite So_lower_eq.
    - rewrite So_lower_eq Wo_So_lower_eq; rewrite -/i0 -/i1 in Hia *.
      rewrite take_codom_rcons all_rcons H01 /=.
      by apply/sub_all/Hia=>z Hz; apply/leq_trans/H01.
    rewrite So_lower_eq; apply/(implyb_trans Hi)/implyP.
    rewrite take_codom_rcons sorted_rconsE; try by apply: leq_trans.
    by move=>->; rewrite andbT.
  move=>v m0; case: sw0 Hsw=>/=; last by case=>-> Hf; rewrite orbF.
  (* swap happened *)
  case=>Hf' Hf; rewrite orbT /=; case=>{v}-> [f''][Hm0 Hf''] Vm0.
  rewrite implybT; split=>//; exists f''; split=>//.
  by apply/perm_trans/Hf''; rewrite Hf'; exact: perm_swap.
(* i = k, exit *)
have {}Hik : nat_of_ord i = k.
- apply/eqP; rewrite eqn_leq Hik /=.
  by move/negP: H; rewrite -leqNgt.
step=>Vm; split; first by apply/implyP=>->.
case: sw0 Hsw=>/=; case=>Ef' Hf.
- (* swap happened on last iteration *)
  rewrite -{H loop k}Hik in Ha He *; rewrite orbT; exists f'.
  split=>//; rewrite Ef'; first by exact: perm_swap.
  - rewrite take_swap_rcons drop_swap_cons allrel_rconsl allrel_consr /=.
    move: Ha; rewrite take_codom_rcons2 !allrel_rconsl -/i0 -/i1 -andbA.
    by case/and3P=>-> _ ->; rewrite (ltnW Hf) /= !andbT.
  rewrite drop_swap_cons /= path_sortedE; last by exact: leq_trans.
  rewrite He andbT; apply/allP=>z Hz; move/allrelP: Ha; apply=>//.
  by rewrite take_codom_rcons2 4!(mem_rcons, inE) eqxx /= orbT.
(* swap didn't happen on last iteration *)
rewrite orbF; case: sw Hi=>/=.
- (* flag was set *)
  move=>_; exists f'; split=>//; rewrite Ef' //.
  - rewrite -Hik in Ha *.
    rewrite take_codom_rcons drop_codom_cons allrel_rconsl allrel_consr /=.
    move: Ha; rewrite take_codom_rcons2 !allrel_rconsl -andbA -/i0 -/i1.
    case/and3P=>->-> _; rewrite Hf /= !andbT.
    by apply/sub_all/Hia=>z Hz; apply/leq_trans/Hf.
  rewrite drop_codom_cons /= path_sortedE; last by exact: leq_trans.
  rewrite He andbT.
  by move: Ha; rewrite take_codom_rcons2 !allrel_rconsl -andbA; case/and3P.
(* flag wasn't set, so the pass didn't swap anything - the array is sorted *)
move=>Hs2; split; first by rewrite -Ef'.
rewrite (ffun_split2 f i) -/i0 -/i1 /= So_eq; rewrite Hik in Hia Hs2 *.
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
        [vfun (_ : unit) h => exists f',
          [/\ h \In Array.shape a f',
              perm_eq (fgraph f) (fgraph f') &
              sorted leq (fgraph f')]]).

Program Definition bubble_sort_opt (a : {array 'I_n.+2 -> nat}) :
  {f : {ffun 'I_n.+2 -> nat}},
  STsep (Array.shape a f,
        [vfun (_ : unit) h => exists f',
          [/\ h \In Array.shape a f',
              perm_eq (fgraph f) (fgraph f') &
              sorted leq (fgraph f')]]) :=
  Do (let go := Fix (fun (loop : bubble_sort_optT a) k =>
                     Do (sw <-- bubble_pass_opt a k;
                         if sw
                           then skip;; loop (Po k) (* hmm *)
                           else skip))
      in go ord_max).
Next Obligation.
move=>a go k [f][] h /= [H Ha Hs].
apply: [stepE f]=>//=; case=>m; last first.
- by case=>Hm Hsm; step=>_; exists f.
case=>f' [Hm Hpm Ham Hsm]; step.
apply: [gE f']=>//=; last first.
- move=> _ m2 [f''][H2 Hp' Hs'] _; exists f''.
  by split=>//; apply/perm_trans/Hp'.
rewrite Po_eq; split=>//; last first.
- case: (posnP k)=>Hk; last by rewrite (prednK Hk).
  move: Hsm; rewrite Hk /= (ffun_split2 f' ord0) /= take0 /= drop0.
  rewrite path_sortedE; last by exact: leq_trans.
  by case/andP.
case: (posnP k)=>Hk; last by rewrite (prednK Hk).
move: Ham Hsm; rewrite Hk /= (ffun_split2 f' ord0) /= take0 /= take0 drop0.
rewrite allrel1l /=; case/andP=>H1 H2.
rewrite allrel_consl allrel1l H2 /= path_sortedE; last by exact: leq_trans.
by case/andP.
Qed.
Next Obligation.
move=>a [f][] h /= [E V].
have Hs: size (codom f) <= n.+2 by rewrite size_codom /= card_ord.
by apply: [gE f]=>//=; split=>//; rewrite drop_oversize // allrel0r.
Qed.

End bubble.
