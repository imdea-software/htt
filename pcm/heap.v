(*
Copyright 2010 IMDEA Software Institute
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

(******************************************************************************)
(* This file defines heaps as possibly undefined finite maps from pointer     *)
(* type to dynamic type.                                                      *)
(* Heaps are a special case of Partial Commutative Monoids (pcm)              *)
(******************************************************************************)

From HB Require Import structures.
From Coq Require Import ssreflect ssrbool ssrfun Eqdep.
From mathcomp Require Import ssrnat eqtype fintype tuple finfun seq path bigop.
From pcm Require Import options axioms prelude pred finmap.
From pcm Require Import pcm unionmap natmap.

(************)
(* Pointers *)
(************)

(* ptr/null is alternative name for nat/0 *)
Definition ptr := nat.
Definition null : ptr := 0.

(* some pointer arithmetic: offsetting from a base *)
Definition ptr_offset (x : ptr) i := x + i.

Notation "x .+ i" := (ptr_offset x i)
  (at level 5, format "x .+ i").

Lemma ptr0 x : x.+0 = x. 
Proof. by rewrite /ptr_offset addn0. Qed.

Lemma ptr1 x : x .+ 1 = x.+1.
Proof. by rewrite /ptr_offset addn1. Qed.

Lemma ptrA x i j : x.+i.+j = x.+(i+j).
Proof. by rewrite /ptr_offset addnA. Qed.

Lemma ptrK x i j : (x.+i == x.+j) = (i == j).
Proof. by rewrite /ptr_offset eqn_add2l. Qed.

Lemma ptr_null x m : (x.+m == null) = (x == null) && (m == 0).
Proof. by rewrite /ptr_offset addn_eq0. Qed.

Lemma ptrT x y : {m : nat | (x == y.+m) || (y == x.+m)}.
Proof.
exists (if x <= y then (y - x) else (x - y)).
rewrite /ptr_offset leq_eqVlt /=.
by case: (ltngtP x y)=>/= E; rewrite subnKC ?(ltnW E) ?eq_refl ?orbT // E.
Qed.

(*********)
(* Heaps *)
(*********)

Inductive heap :=
  Undef | Def (finmap : {finMap ptr -> dynamic id}) of
               null \notin supp finmap.

Module Heap.
Section NullLemmas.
Variables (f g : {finMap ptr -> dynamic id}) (x : ptr) (v : dynamic id).

Lemma upd_nullP : 
        x != null -> null \notin supp f -> null \notin supp (ins x v f).
Proof. by move=>H1 H2; rewrite supp_ins negb_or /= inE /= eq_sym H1. Qed.

Lemma free_nullP : null \notin supp f -> null \notin supp (rem x f).
Proof. by move=>H; rewrite supp_rem negb_and /= H orbT. Qed.

Lemma un_nullP :
        null \notin supp f -> null \notin supp g ->
          null \notin supp (fcat f g).
Proof. by move=>H1 H2; rewrite supp_fcat negb_or H1 H2. Qed.

Lemma filt_nullP (q : pred ptr) : 
        null \notin supp f -> null \notin supp (kfilter q f).
Proof. by move=>H; rewrite supp_kfilt mem_filter negb_and H orbT. Qed.

Lemma heap_base : null \notin supp f -> all (fun k => k != null) (supp f).
Proof. by move=>H; apply/allP=>k; case: eqP H=>// -> /negbTE ->. Qed.

Lemma base_heap : all (fun k => k != null) (supp f) -> null \notin supp f.
Proof. by move/allP=>H; apply: (introN idP); move/H. Qed.

Lemma heapE (h1 h2 : heap) :
        h1 = h2 <->
        match h1, h2 with
          Def f' pf, Def g' pg => f' = g'
        | Undef, Undef => true
        | _, _ => false
        end.
Proof.
split; first by move=>->; case: h2.
case: h1; case: h2=>// f1 pf1 f2 pf2 E.
rewrite {f2}E in pf1 pf2 *.
by congr Def; apply: eq_irrelevance.
Qed.

End NullLemmas.

(* methods *)

Notation base := (@UM.base ptr (fun k => k != null) (dynamic id)).

Definition def h := if h is Def _ _ then true else false.
Definition empty := @Def finmap.nil is_true_true.
Definition upd k v h :=
  if h is Def hs ns then
    if decP (@idP (k != null)) is left pf then
      Def (@upd_nullP _ _ v pf ns)
    else Undef
  else Undef.
Definition dom h : seq ptr := if h is Def f _ then supp f else [::].
Definition assocs h : seq (ptr * dynamic id) :=
  if h is Def f _ then seq_of f else [::].
Definition free h x :=
  if h is Def hs ns then Def (free_nullP x ns) else Undef.
Definition find (x : ptr) h :=
  if h is Def hs _ then fnd x hs else None.
Definition union h1 h2 :=
  if (h1, h2) is (Def hs1 ns1, Def hs2 ns2) then
    if disj hs1 hs2 then
       Def (@un_nullP _ _ ns1 ns2)
    else Undef
  else Undef.
Definition pts (x : ptr) v := upd x v empty.
Definition empb h := if h is Def hs _ then supp hs == [::] else false.
Definition undefb h := if h is Undef then true else false.
Definition keys_of h : seq ptr :=
  if h is Def f _ then supp f else [::].
Definition from (f : heap) : base :=
  if f is Def hs ns then UM.Def (heap_base ns) else UM.Undef _ _.
Definition to (b : base) : heap :=
  if b is UM.Def hs ns then Def (base_heap ns) else Undef.

Module Exports.
(* heap has union map structure *)
Lemma heap_is_umc : union_map_axiom def empty Undef upd dom 
                                    assocs free find union empb 
                                    undefb pts from to. 
Proof.
split; first by split=>[[]|[]] // f H; rewrite ?UM.umapE ?heapE.
split.
- split; first by split; [split=>[[]|]|rewrite heapE].    
  split; last by case=>[|f H k] //; rewrite heapE.
  split=>[|[]] //; split=>[k v [|h H]|[]] //=.
  by case: decP=>// H1; rewrite heapE. 
split=>[|k v]; last first.
- by rewrite /pts /UM.pts /UM.upd /=; case: decP=>// H; rewrite heapE. 
split=>[|[]] //; split=>[|[]] //; split=>[k []|[|f1 H1][|f2 H2]] //.
by rewrite /union /UM.union /=; case: ifP=>D //; rewrite heapE.
Qed.

HB.instance Definition _ := 
  isUnion_map.Build ptr (fun k => k != null) (dynamic id) heap heap_is_umc.
HB.instance Definition _ := isNatMap.Build (dynamic id) heap.
End Exports.
End Heap. 
Export Heap.Exports.

Notation "x :-> v" := (ptsT heap x (idyn v)) (at level 30).

Canonical heap_PredType : PredType (nat * dynamic id) := um_PredType heap.
Coercion Pred_of_nmap (x : heap) : {Pred _} := [eta Mem_UmMap x].

(********************)
(* points-to lemmas *)
(********************)

(* union_map pts lemmas combined with dyn_inj *)

Section HeapPointsToLemmas.
Implicit Types (x : ptr) (h : heap).

Lemma hcancelPtT A1 A2 x (v1 : A1) (v2 : A2) :
        valid (x :-> v1) -> x :-> v1 = x :-> v2 -> A1 = A2.  
Proof. by move=>V /(cancelPt V)/dyn_injT. Qed.

Lemma hcancelPtT2 A1 A2 x1 x2 (v1 : A1) (v2 : A2) :
        valid (x1 :-> v1) -> x1 :-> v1 = x2 :-> v2 -> (x1, A1) = (x2, A2).
Proof. by move=>V; case/(cancelPt2 V)=>-> E _; rewrite E. Qed.

Lemma hcancelPtV A x (v1 v2 : A) :
        valid (x :-> v1) -> x :-> v1 = x :-> v2 -> v1 = v2.
Proof. by move=>V; move/(cancelPt V)/dyn_inj. Qed.

Lemma hcancelPtV2 A x1 x2 (v1 v2 : A) :
        valid (x1 :-> v1) -> x1 :-> v1 = x2 :-> v2 -> (x1, v1) = (x2, v2).
Proof. by move=>V /(cancelPt2 V) [->] /dyn_inj ->. Qed.

Lemma heap_eta x h :
        x \in dom h -> 
        exists A (v : A),
          find x h = Some (idyn v) /\ 
          h = x :-> v \+ free h x. 
Proof. by case/um_eta; case=>A v H; exists A, v. Qed.

(* restatement of um_eta2, to avoid showing idyn's *)
Lemma heap_eta2 A x h (v : A) :
        find x h = Some (idyn v) -> 
        h = x :-> v \+ free h x.
Proof. exact: um_eta2. Qed.

Lemma hcancelT A1 A2 x (v1 : A1) (v2 : A2) h1 h2 :
        valid (x :-> v1 \+ h1) ->
        x :-> v1 \+ h1 = x :-> v2 \+ h2 -> A1 = A2. 
Proof. by move=>V; case/(cancel V); move/dyn_injT. Qed.

Lemma hcancelV A x (v1 v2 : A) h1 h2 :
        valid (x :-> v1 \+ h1) ->
        x :-> v1 \+ h1 = x :-> v2 \+ h2 -> [/\ v1 = v2, valid h1 & h1 = h2].
Proof. by move=>V; case/(cancel V); move/dyn_inj. Qed.

Lemma hcancel2V A x1 x2 (v1 v2 : A) h1 h2 :
        valid (x1 :-> v1 \+ h1) ->
        x1 :-> v1 \+ h1 = x2 :-> v2 \+ h2 ->
        if x1 == x2 then v1 = v2 /\ h1 = h2
        else [/\ free h2 x1 = free h1 x2,
                 h1 = x2 :-> v2 \+ free h2 x1 &
                 h2 = x1 :-> v1 \+ free h1 x2].
Proof. by move=>V /(cancel2 V); case: ifP=>// _ [/dyn_inj]. Qed.

End HeapPointsToLemmas.

Prenex Implicits heap_eta heap_eta2.

(*******************************************)
(* Block update for reasoning about arrays *)
(*******************************************)

Section BlockUpdate.
Variable A : Type.

Fixpoint updi (x : ptr) (vs : seq A) {struct vs} : heap :=
  if vs is v'::vs' then x :-> v' \+ updi x.+1 vs' else Unit.

Lemma updiS x v vs : updi x (v :: vs) = x :-> v \+ updi x.+1 vs.
Proof. by []. Qed.

Lemma updi_last x v vs :
        updi x (rcons vs v) = updi x vs \+ x.+(size vs) :-> v.
Proof.
elim: vs x v=>[|w vs IH] x v /=.
- by rewrite ptr0 unitR unitL.
by rewrite -(addn1 (size vs)) addnC -ptrA IH joinA ptr1.
Qed.

Lemma updi_cat x vs1 vs2 :
        updi x (vs1 ++ vs2) = updi x vs1 \+ updi x.+(size vs1) vs2.
Proof.
elim: vs1 x vs2=>[|v vs1 IH] x vs2 /=.
- by rewrite ptr0 unitL.
by rewrite -(addn1 (size vs1)) addnC -ptrA IH joinA ptr1.
Qed.

Lemma updi_catI x y vs1 vs2 :
        y = x + size vs1 -> updi x vs1 \+ updi y vs2 = updi x (vs1 ++ vs2).
Proof. by move=>->; rewrite updi_cat. Qed.

(* helper lemma *)
Lemma updiVm' x m xs : m > 0 -> x \notin dom (updi x.+m xs).
Proof.
elim: xs x m=>[|v vs IH] x m H; first by rewrite dom0.
rewrite /= -addnS domPtUn inE /= negb_and negb_or -{4}(addn0 x).
by rewrite eqn_add2l -lt0n H IH // andbT orbT.
Qed.

Lemma updiD x xs : valid (updi x xs) = (x != null) || (size xs == 0).
Proof.
elim: xs x=>[|v xs IH] x; first by rewrite valid_unit orbC.
by rewrite /= validPtUn -addn1 updiVm' // orbF IH addn1 /= andbT.
Qed.

Lemma updiVm x m xs :
        x \in dom (updi x.+m xs) = [&& x != null, m == 0 & size xs > 0].
Proof.
case: m=>[|m] /=; last first.
- by rewrite andbF; apply/negbTE/updiVm'.
case: xs=>[|v xs]; rewrite ptr0 ?andbF ?andbT ?dom0 //=.
by rewrite domPtUn inE /= eq_refl -updiS updiD orbF andbT /=.
Qed.

Lemma updimV x m xs :
        x.+m \in dom (updi x xs) = (x != null) && (m < size xs).
Proof.
case H: (x == null)=>/=.
- case: xs=>[|a s]; first by rewrite dom0.
  by rewrite domPtUn inE validPtUn /= H.
elim: xs x m H=>[|v vs IH] x m H //; case: m=>[|m]; try by rewrite /= dom0.
-by rewrite ptr0 domPtUn inE /= eq_refl andbT -updiS updiD H.
rewrite -addn1 addnC -ptrA updiS domPtUn inE ptr1 IH //.
by rewrite -updiS updiD H /= -{1}(ptr0 x) -ptr1 ptrA ptrK. 
Qed.

Lemma updiP x y xs :
        reflect (y != null /\ exists m, x = y.+m /\ m < size xs)
                (x \in dom (updi y xs)).
Proof.
case H: (y == null)=>/=.
- rewrite (eqP H); elim: xs=>[|z xs IH].
  - by rewrite dom0; constructor; case.
  by rewrite domPtUn inE validPtUn; constructor; case.
case E: (x \in _); constructor; last first.
- by move=>[_][m][H1] H2; rewrite H1 updimV H2 H in E.
case: (ptrT x y) E=>m; case/orP; move/eqP=>->.
- by rewrite updimV H /= => H1; split=>//; exists m.
rewrite updiVm; case/and3P=>H1; move/eqP=>-> H2.
by split=>//; exists 0; rewrite ptrA addn0 ptr0.
Qed.

(* Invertibility *)
Lemma updi_inv x xs1 xs2 :
        valid (updi x xs1) -> updi x xs1 = updi x xs2 -> xs1 = xs2.
Proof.
elim: xs1 x xs2 =>[|v1 xs1 IH] x /=; case=>[|v2 xs2] //= D.
- by case/esym/umap0E=>/unitbP; rewrite um_unitbPt. 
- by case/umap0E=>/unitbP; rewrite um_unitbPt.
by case/(hcancelV D)=><- {}D /(IH _ _ D) <-.
Qed.

Lemma updi_iinv x xs1 xs2 h1 h2 :
        size xs1 = size xs2 -> valid (updi x xs1 \+ h1) ->
        updi x xs1 \+ h1 = updi x xs2 \+ h2 -> xs1 = xs2 /\ h1 = h2.
Proof.
elim: xs1 x xs2 h1 h2=>[|v1 xs1 IH] x /=; case=>[|v2 xs2] //= h1 h2.
- by rewrite !unitL.
move=>[E]; rewrite -!joinA=>D; case/(hcancelV D)=><-{}D.
by case/(IH _ _ _ _ E D)=>->->.
Qed.

Lemma updi_iota n (x : ptr) (f : nat -> A) : 
        updi x (map f (iota 0 n)) = 
        \big[join/Unit]_(i <- iota 0 n) x.+i :-> f i.
Proof.
elim: n x=>[|n IH] x; first by rewrite big_nil.
rewrite -addn1 iotaD add0n map_cat /= big_cat big_seq1 /=.
by rewrite updi_cat /= size_map size_iota /= unitR -IH.
Qed.

Lemma updi_ord n (x : ptr) (f : 'I_n -> A) :
        updi x (map f (enum 'I_n)) =
        \big[join/Unit]_(i in 'I_n) x.+i :-> f i.
Proof.
case: n f=>[|n] f; first by rewrite -big_enum enum_ord0 big_nil.
set F := fun i => 
  if decP (b:=i < n.+1) idP is left pf then f (Ordinal pf)
  else f (Ordinal (n:=n.+1) (m:=0) erefl).
have Ef i : f i = F i.
- rewrite /F; case: decP=>//.
  by case: i=>i pf1 pf2; rewrite (pf_irr pf1 pf2).
set J := RHS.
have -> : J = \big[join/Unit]_(i in 'I_n.+1) x.+i :-> F i.
- by apply: eq_bigr=>i _; rewrite Ef.
rewrite -big_enum -(big_map _ predT (fun i=>x.+i :-> F i)).
rewrite val_enum_ord -updi_iota -val_enum_ord -map_comp. 
by congr updi; apply: eq_map.
Qed.

End BlockUpdate.

Lemma updi_split {I : finType} T p k (f : {ffun I -> T}) :
        updi p (fgraph f) = updi p (take (indx k) (fgraph f)) \+
                            p.+(indx k) :-> f k \+
                            updi (p.+(indx k).+1) (drop (indx k).+1 (fgraph f)).
Proof.
rewrite fgraph_codom /= codomE {1}(enum_split k) map_cat updi_cat /=.
rewrite map_take map_drop size_takel ?joinA; first by rewrite -ptr1 ptrA addn1. 
by rewrite size_map index_size.
Qed.

Lemma domeqUP A1 A2 x (xs1 : seq A1) (xs2 : seq A2) :
        size xs1 = size xs2 -> 
        dom_eq (updi x xs1) (updi x xs2).
Proof.
move=>E; apply/domeqP; split; first by rewrite !updiD E.
apply/domE=>z; case: updiP=>[[H][m][->]|X]; first by rewrite updimV H E.
by case: updiP=>// [[H]][m][Ez S]; elim: X; split=>//; exists m; rewrite Ez E.
Qed.

(*****************************)
(*****************************)
(* Automation of PtUn lemmas *)
(*****************************)
(*****************************)

(* First, the mechanism for search-and-replace for the overloaded lemas, *)
(* pattern-matching on heap expressions.                                 *)

Structure tagged_heap := HeapTag {untag :> heap}.

Definition right_tag := HeapTag.
Definition left_tag := right_tag.
Canonical found_tag i := left_tag i.

Definition partition_axiom k r (h : tagged_heap) := untag h = k \+ r.

Structure partition (k r : heap) :=
  Partition {heap_of :> tagged_heap;
             _ : partition_axiom k r heap_of}.

Lemma partitionE r k (f : partition k r) : untag f = k \+ r.
Proof. by case: f=>[[j]] /=; rewrite /partition_axiom /= => ->. Qed.

Lemma found_pf k : partition_axiom k Unit (found_tag k).
Proof. by rewrite /partition_axiom unitR. Qed.

Canonical found_struct k := Partition (found_pf k).

Lemma left_pf h r (f : forall k, partition k r) k :
        partition_axiom k (r \+ h) (left_tag (untag (f k) \+ h)).
Proof. by rewrite partitionE /partition_axiom /= joinA. Qed.

Canonical left_struct h r (f : forall k, partition k r) k :=
  Partition (left_pf h f k).

Lemma right_pf h r (f : forall k, partition k r) k :
        partition_axiom k (h \+ r) (right_tag (h \+ f k)).
Proof. by rewrite partitionE /partition_axiom /= joinCA. Qed.

Canonical right_struct h r (f : forall k, partition k r) k :=
  Partition (right_pf h f k).

(* now the actual lemmas *)

Lemma defPtUnO A h x (v : A) (f : partition (x :-> v) h) :
        valid (untag f) = [&& x != null, valid h & x \notin dom h].
Proof. by rewrite partitionE validPtUn. Qed.

Arguments defPtUnO [A h] x {v f}.

Lemma defPt_nullO A h x (v : A) (f : partition (x :-> v) h) :
        valid (untag f) -> x != null.
Proof. by rewrite partitionE; apply: validPtUn_cond. Qed.

Arguments defPt_nullO [A h x v f] _.

Lemma defPt_defO A h x (v : A) (f : partition (x :-> v) h) :
        valid (untag f) -> valid h.
Proof. by rewrite partitionE => /validR. Qed.

Arguments defPt_defO [A][h] x [v][f] _.

Lemma defPt_domO A h x (v : A) (f : partition (x :-> v) h) :
        valid (untag f) -> x \notin dom h.
Proof. by rewrite partitionE; apply: validPtUnD. Qed.

Arguments defPt_domO [A][h] x [v][f] _.

Lemma domPtUnO A h x (v : A) (f : partition (x :-> v) h) :
        dom (untag f) =i
        [pred y | valid (untag f) & (x == y) || (y \in dom h)].
Proof. by rewrite partitionE; apply: domPtUn. Qed.

Arguments domPtUnO [A][h] x [v][f] _.

Lemma lookPtUnO A h x (v : A) (f : partition (x :-> v) h) :
        valid (untag f) -> find x (untag f) = Some (idyn v).
Proof. by rewrite partitionE; apply: findPtUn. Qed.

Arguments lookPtUnO [A h x v f] _.

Lemma freePtUnO A h x (v : A) (f : partition (x :-> v) h) :
        valid (untag f) -> free (untag f) x = h.
Proof. by rewrite partitionE; apply: freePtUn. Qed.

Arguments freePtUnO [A h x v f] _.

Lemma updPtUnO A1 A2 x i (v1 : A1) (v2 : A2)
               (f : forall k, partition k i) :
        upd x (idyn v2) (untag (f (x :-> v1))) = f (x :-> v2).
Proof. by rewrite !partitionE; apply: updPtUn. Qed.

Arguments updPtUnO [A1 A2 x i v1 v2] f.

Lemma cancelTO A1 A2 h1 h2 x (v1 : A1) (v2 : A2)
               (f1 : partition (x :-> v1) h1)
               (f2 : partition (x :-> v2) h2) :
        valid (untag f1) -> f1 = f2 :> heap -> A1 = A2.
Proof. by rewrite !partitionE; apply: hcancelT. Qed.

Arguments cancelTO [A1 A2 h1 h2] x [v1 v2 f1 f2] _ _.

Lemma cancelO A h1 h2 x (v1 v2 : A)
              (f1 : partition (x :-> v1) h1)
              (f2 : partition (x :-> v2) h2) :
        valid (untag f1) -> f1 = f2 :> heap ->
        [/\ v1 = v2, valid h1 & h1 = h2].
Proof. by rewrite !partitionE; apply: hcancelV. Qed.

Arguments cancelO [A h1 h2] x [v1 v2 f1 f2] _ _.

Lemma domPtUnXO A (v : A) x i (f : partition (x :-> v) i) :
        valid (untag f) -> x \in dom (untag f).
Proof. by rewrite partitionE domPtUnE. Qed.

(*******************************************************)
(*******************************************************)
(* Custom lemmas about singly-linked lists in the heap *)
(*******************************************************)
(*******************************************************)

Fixpoint llist A p (xs : seq A) {struct xs} :=
  if xs is x::xt then
    fun h => exists r h', h = p :-> (x, r) \+ h' /\ llist r xt h'
  else fun h : heap => p = null /\ h = Unit.

Lemma llist_prec A p (l1 l2 : seq A) h1 h2 g1 g2 :
        valid (h1 \+ g1) ->
        llist p l1 h1 -> llist p l2 h2 ->
        h1 \+ g1 = h2 \+ g2 ->
        [/\ l1 = l2, h1 = h2 & g1 = g2].
Proof.
move=>V H1 H2 E; elim: l1 l2 h1 h2 p H1 H2 E V=>[|a1 l1 IH].
- case=>[|a2 l2] h1 h2 p /= [->->].
  - by case=>_ ->; rewrite !unitL.
  by case=>r [h'][-> _ ->] /validL /validPtUn_cond.
case=>[|a2 l2] h1 h2 p /= [p1][k1][-> H1].
- by case=>->-> _ /validL /validPtUn_cond.
case=>p2 [k2][-> H2]; rewrite -!joinA => E V.
case: {E V} (hcancelV V E) H1 H2; case=>->-> V E H1 H2.
by case: (IH _ _ _ _ H1 H2 E V)=>->->->.
Qed.

Lemma first_exists A p h (ls : seq A) :
        p != null -> llist p ls h ->
        exists x r h',
          [/\ ls = x :: behead ls, h = p :-> (x, r) \+ h' &
              llist r (behead ls) h'].
Proof.
case: ls=>[|a ls] /= H []; first by case: eqP H.
by move=>r [h'][-> H1]; eexists a, r, h'.
Qed.

Lemma llist_null A (xs : seq A) h :
        valid h -> llist null xs h -> xs = [::] /\ h = Unit.
Proof.
case: xs=>[|x xs] /= V H; first by case: H.
by case: H V=>p [h'][-> _] /validPtUn_cond.
Qed.


