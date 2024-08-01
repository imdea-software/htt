(*
Copyright 2017 IMDEA Software Institute
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

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq.
From pcm Require Import options pred prelude.
From pcm Require Export auto.
From pcm Require Import pcm unionmap natmap.

(**************************************************************************)
(**************************************************************************)
(* Canonical structure lemmas for automating three tasks:                 *)
(*                                                                        *)
(* 1. checking if implications of the form valid e1 -> valid e2 hold by   *)
(*    deciding if the terms in e2 are all contained in e1                 *)
(*                                                                        *)
(* 2. checking if dom_eq e1 e2 holds by cancelling the common terms, to   *)
(*    obtain residuals rs1 and rs2, and then issuing a subgoal dom_eq rs1 *)
(*    rs2.                                                                *)
(*                                                                        *)
(* 3. checking if the union e is undef, because it contains duplicate     *)
(*    pointers or an undef                                                *)
(*                                                                        *)
(**************************************************************************)
(**************************************************************************)

(* DEVCOMMENT *)
(* For each task, we have two implementations: a naive and a                  *)
(* sophisticated one. The lemmas validO, domeqO, invalidO are the naive       *)
(* ones, and validX, domeqX, invalidX are the sophisticated ones. I keep      *)
(* both O/X versions for now, for experimentation purposes, but               *)
(* eventually should retain only validX and domeqX.                           *)
(* /DEVCOMMENT *)

(* Context structure for reflection of unionmap expressions. We          *)
(* reflect the keys and the variables of the map expression. (The        *)
(* variables are all expressions that are not recognized as a key, or as *)
(* a disjoint union). We reflect disjoint union as a sequence.           *)
(*                                                                       *)
(* The context of keys is thus seq K. The context of vars is seq U.      *)

Section ReflectionContexts.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).

Structure ctx := Context {keyx : seq K; varx : seq U}.

Definition empx := Context [::] [::].

(* because contexts grow during computation, *)
(* we need a notion of sub-context *)

Definition sub_ctx (i j : ctx) :=
  Prefix (keyx i) (keyx j) /\ Prefix (varx i) (varx j).

Lemma sc_refl i : sub_ctx i i.
Proof. by []. Qed.

Lemma sc_trans i j k : sub_ctx i j -> sub_ctx j k -> sub_ctx i k.
Proof.
by case=>K1 V1 [K2 V2]; split; [move: K2 | move: V2]; apply: Prefix_trans.
Qed.

End ReflectionContexts.

(* Keys and map variables are syntactified as De Bruijn indices in the context. *)
(* Disjoint union is syntactified as concatenation of lists.                    *)
(*                                                                              *)
(* Pts n v : syntax for "key indexed the context under number n" \-> v          *)
(* Var n : syntax for "expression indexed in the context under number n"        *)

(* now for reflection *)

Section Reflection.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Implicit Type i : ctx U.

Inductive term := Pts of nat & T | Var of nat.

(* interpretation function for elements *)
Definition interp' i t :=
  match t with
    Pts n v => if onth (keyx i) n is Some k then pts k v else undef
  | Var n => if onth (varx i) n is Some f then f else undef
  end.

(* main interpretation function *)
Notation fx i := (fun t f => interp' i t \+ f).
Definition interp i ts := foldr (fx i) Unit ts.

Lemma fE i ts x  : foldr (fx i) x ts = x \+ interp i ts.
Proof. by elim: ts x=>[|t ts IH] x; rewrite /= ?unitR // IH joinCA. Qed.

Lemma interp_rev i ts : interp i (rev ts) = interp i ts.
Proof.
elim: ts=>[|t ts IH] //=; rewrite rev_cons -cats1.
by rewrite /interp foldr_cat fE /= unitR IH.
Qed.

(* we also need a pretty-printer, which works the same as interp *)
(* but removes trailing Unit's *)

Fixpoint pprint i ts :=
  if ts is t :: ts' then
    if ts' is [::] then interp' i t else interp' i t \+ pprint i ts'
  else Unit.

Lemma pp_interp i ts : pprint i ts = interp i ts.
Proof. by elim: ts=>[|t ts /= <-] //; case: ts=>//; rewrite unitR. Qed.

Definition key n t := if t is Pts m _ then n == m else false.
Definition var n t := if t is Var m then n == m else false.

Definition kfree n t := rfilter (key n) t.
Definition vfree n t := rfilter (var n) t.
Arguments kfree /.
Arguments vfree /.

Lemma keyN i n ts : ~~ has (key n) ts -> interp i (kfree n ts) = interp i ts.
Proof. by elim: ts=>[|t ts IH] //=; case: ifP=>//= _ /IH ->. Qed.

Lemma varN i n ts : ~~ has (var n) ts -> interp i (vfree n ts) = interp i ts.
Proof. by elim: ts=>[|t ts IH] //=; case: ifP=>//= _ /IH ->. Qed.

Lemma keyP i n k ts :
        has (key n) ts -> onth (keyx i) n = Some k ->
        exists v, interp i ts = pts k v \+ interp i (kfree n ts).
Proof.
elim: ts=>[|t ts IH] //=; case: ifP=>[|_ H].
- by case: t=>//= _ v /eqP <- _ ->; exists v.
by case/(IH H)=>v ->; exists v; rewrite joinCA.
Qed.

Lemma varP i n u ts :
        has (var n) ts -> onth (varx i) n = Some u ->
        interp i ts = u \+ interp i (vfree n ts).
Proof.
elim: ts=>[|t ts IH] //=; case: ifP=>[|_ H].
- by case: t=>//= _ /eqP <- _ ->.
by move/(IH H)=>->; rewrite joinCA.
Qed.

(* interpretation is invariant under context weakening *)
(* under assumption that the interpreted term is well-formed *)

Definition wf i t :=
  match t with
    Pts n _ => n < size (keyx i)
  | Var n => n < size (varx i)
  end.

Lemma sc_wf i j ts : sub_ctx i j -> all (wf i) ts -> all (wf j) ts.
Proof.
case=>/Prefix_size H1 /Prefix_size H2; elim: ts=>[|t ts IH] //=.
case/andP=>H /IH ->; rewrite andbT.
by case: t H=>[n v|v] H; apply: leq_trans H _.
Qed.

Lemma sc_interp i j ts :
        sub_ctx i j -> all (wf i) ts -> interp i ts = interp j ts.
Proof.
case=>H1 H2; elim: ts=>[|t ts IH] //= /andP [H] /IH ->.
by case: t H=>[n v|n] /= /Prefix_onth <-.
Qed.

Lemma valid_wf i ts : valid (interp i ts) -> all (wf i) ts.
Proof.
elim: ts=>[|t ts IH] //= V; rewrite (IH (validR V)) andbT.
case: t {V IH} (validL V)=>[n v|n] /=;
by case X : (onth _ _)=>[a|]; rewrite ?(onth_size X) // valid_undef.
Qed.

Lemma wf_kfree i n ts : all (wf i) ts -> all (wf i) (kfree n ts).
Proof. by elim: ts=>//= t ts IH; case: ifP=>_ /andP [] //= -> /IH ->. Qed.

Lemma wf_vfree i n ts : all (wf i) ts -> all (wf i) (vfree n ts).
Proof. by elim: ts=>//= t ts IH; case: ifP=>_ /andP [] //= -> /IH ->. Qed.

(* sometimes we want to get keys in a list, not in a predicate *)

Definition getkeys :=
  foldr (fun t ks => if t is Pts k _ then k :: ks else ks) [::].

Lemma has_getkeys ts n : n \in getkeys ts = has (key n) ts.
Proof. by elim: ts=>//= t ts IH; case: t=>[m v|m] //; rewrite inE IH. Qed.

End Reflection.


(**********************************************************************)
(**********************************************************************)
(* Purely functional decision procedures for the three tasks. Further *)
(* below, they will be embedded into the canonical programs validX    *)
(* and domeqX and invalidX respectively.                              *)
(**********************************************************************)
(**********************************************************************)

(* subterm is purely functional version of validX *)

Section Subterm.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Implicit Types (i : ctx U) (ts : seq (term T)).

Fixpoint subterm ts1 ts2 :=
  match ts1 with
    Pts n _ :: tsx1 =>
      if has (key n) ts2 then subterm tsx1 (kfree n ts2) else false
  | Var n :: tsx1 =>
      if has (var n) ts2 then subterm tsx1 (vfree n ts2) else false
  | [::] => true
  end.

(* the procedure is sound for deciding wf subterms *)
Lemma subterm_sound i ts1 ts2 :
        all (wf i) ts1 -> all (wf i) ts2 -> subterm ts1 ts2 ->
        exists u, dom_eq (interp i ts1 \+ u) (interp i ts2).
Proof.
elim: ts1 ts2=>[|t ts1 IH] ts2 /= A1 A2.
- by exists (interp i ts2); rewrite unitL.
case/andP: A1; case: t=>[n v|n] /= /size_onth [k] X A1;
rewrite X; case: ifP=>Y //.
- case: (keyP Y X)=>w -> /(IH _ A1 (wf_kfree n A2)) [xs D].
  by exists xs; rewrite -joinA; apply: domeqUn D; apply: domeqPt.
move: (varP Y X)=>-> /(IH _ A1 (wf_vfree n A2)) [xs D].
by exists xs; rewrite -joinA; apply: domeqUn D.
Qed.

End Subterm.

(* subtract is purely functional version of domeqX *)

Section Subtract.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Implicit Types (i : ctx U) (ts : seq (term T)).

(* We need a subterm lemma that returns the uncancelled stuff from *)
(* both sides. xs accumulates uncancelled part of ts1, starting as nil *)

Fixpoint subtract ts1 ts2 xs :=
  match ts1 with
    Pts n v :: tsx1 =>
      if has (key n) ts2 then subtract tsx1 (kfree n ts2) xs
      else subtract tsx1 ts2 (Pts n v :: xs)
  | Var n :: tsx1 =>
      if has (var n) ts2 then subtract tsx1 (vfree n ts2) xs
      else subtract tsx1 ts2 (Var T n :: xs)
  | [::] => (xs, ts2)
  end.

(* below, the existentially quantified u is the cancelled part *)
Lemma subtract_sound i ts1 ts2 rs1 rs2 xs :
        all (wf i) ts1 -> all (wf i) ts2 ->
        subtract ts1 ts2 xs = (rs1, rs2) ->
        exists u, dom_eq (interp i ts1 \+ interp i xs) (interp i rs1 \+ u) /\
                  dom_eq (interp i ts2) (interp i rs2 \+ u).
Proof.
elim: ts1 ts2 xs=>[|t ts1 IH] ts2 xs /= A1 A2.
- by case=><-<-; exists Unit; rewrite unitL !unitR.
case/andP: A1; case: t=>[n v|n] /= /size_onth [x X] A1; rewrite X; case: ifP=>Y.
- case: (keyP Y X)=>w -> /(IH _ _ A1 (wf_kfree n A2)) [u][H1 H2].
  exists (pts x v \+ u); rewrite -joinA !(pull (pts x _)).
  by split=>//; apply: domeqUn=>//; apply: domeqPt.
- by case/(IH _ _ A1 A2)=>u [/= H1 H2]; rewrite X joinCA joinA in H1; exists u.
- move: (varP Y X)=>-> /(IH _ _ A1 (wf_vfree n A2)) [u][H1 H2].
  by exists (x \+ u); rewrite -joinA !(pull x); split=>//; apply: domeqUn.
by case/(IH _ _ A1 A2)=>u [/= H1 H2]; rewrite X joinCA joinA in H1; exists u.
Qed.

End Subtract.

(* invalid is a purely functional test of invalidX *)

Section Invalid.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Implicit Types (i : ctx U) (t : term T) (ts : seq (term T)).

Definition undefx i t :=
  if t is Var n then
    if onth (varx i) n is Some x then undefb x else false
  else false.

Definition isundef i ts := ~~ uniq (getkeys ts) || has (undefx i) ts.

Lemma isundef_sound i ts :
        all (wf i) ts -> isundef i ts -> ~~ valid (interp i ts).
Proof.
elim: ts=>[|t ts IH] //= /andP [W A].
case: t W=>[n v|n] /= /size_onth [k] X; rewrite /isundef /= X; last first.
- rewrite orbCA=>H; case: validUn=>// V; rewrite (negbTE (IH A _)) //.
  by case/orP: H V=>// /undefbE ->; rewrite valid_undef.
rewrite negb_and negbK has_getkeys -orbA /=.
case/orP=>// V; last by rewrite validPtUn andbCA (negbTE (IH A _)).
by case: (keyP V X)=>u ->; rewrite joinA pts_undef2 undef_join valid_undef.
Qed.

End Invalid.


(********************************)
(********************************)
(* Canonical structure programs *)
(********************************)
(********************************)

(* We syntactify a unionmap into a seq term as follows.                         *)
(*                                                                              *)
(* - if the map is f1 \+ f2, then recurse over both and concatenate the results *)
(* - if the map is the empty map, return [::]                                   *)
(* - if the map is k \-> v then add k to the context, and return [Pts x v],     *)
(*      where x is the index for l in the context                               *)
(*  if the map is whatever else, add the map to the context and return          *)
(*      [Var n], where n is the index for the map in the context                *)

Module Syntactify.
Section Syntactify.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Implicit Types (i : ctx U) (ts : seq (term T)).

(* a tagging structure to control the flow of computation *)
Structure tagged_map := Tag {untag : U}.

Local Coercion untag : tagged_map >-> UMC.sort.

(* in reversed order; first test for unions, then empty, pts and vars *)
Definition var_tag := Tag.
Definition key_tag := var_tag.
Definition empty_tag := key_tag.
Canonical Structure union_tag hc := empty_tag hc.

(* Main structure                                    *)
(* - i : input context                               *)
(* - j : output context                              *)
(* - ts : syntactification of map_of using context j *)

Definition axiom i j ts (pivot : tagged_map) :=
  [/\ interp j ts = pivot :> U, sub_ctx i j & all (wf j) ts].
Structure form i j ts := Form {pivot : tagged_map; _ : axiom i j ts pivot}.

Local Coercion pivot : form >-> tagged_map.

(* check for union *)

Lemma union_pf i j k ts1 ts2 (f1 : form i j ts1) (f2 : form j k ts2) :
        axiom i k (ts1 ++ ts2) (union_tag (untag f1 \+ untag f2)).
Proof.
case: f1 f2=>_ [<- S1 W1][_][<- S2 W2]; split.
- by rewrite /interp foldr_cat fE joinC -(sc_interp S2 W1).
- by apply: sc_trans S1 S2.
by rewrite all_cat (sc_wf S2 W1) W2.
Qed.

Canonical union_form i j k ts1 ts2 f1 f2 :=
  Form (@union_pf i j k ts1 ts2 f1 f2).

(* check if reached empty *)

Lemma empty_pf i : axiom i i [::] (empty_tag Unit).
Proof. by []. Qed.

Canonical empty_form i := Form (@empty_pf i).

(* check for pts k v *)

Lemma pts_pf vars keys1 keys2 k v (f : xfind keys1 keys2 k):
        axiom (Context keys1 vars) (Context keys2 vars)
              [:: Pts k v] (key_tag (pts (xuntag f) v)).
Proof. by case: f=>p [E H]; split=>//=; rewrite ?E ?unitR // (onth_size E). Qed.

Canonical pts_form vars keys1 keys2 k v f :=
  Form (@pts_pf vars keys1 keys2 k v f).

(* check for var *)

Lemma var_pf keys vars1 vars2 n (f : xfind vars1 vars2 n) :
        axiom (Context keys vars1) (Context keys vars2)
              [:: Var T n] (var_tag (xuntag f)).
Proof. by case: f=>p [E H]; split=>//=; rewrite ?E ?unitR // (onth_size E). Qed.

Canonical var_form keys vars1 vars2 v f := Form (@var_pf keys vars1 vars2 v f).

End Syntactify.

Module Exports.
Coercion untag : tagged_map >-> UMC.sort.
Coercion pivot : form >-> tagged_map.
Canonical union_tag.
Canonical union_form.
Canonical empty_form.
Canonical pts_form.
Canonical var_form.
End Exports.
End Syntactify.

Export Syntactify.Exports.

(*********************)
(* Automating validX *)
(*********************)

(* validX is a refined lemma for subterm checking which *)
(* automatically discharges the spurious argument from above *)

Module ValidX.
Section ValidX.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Implicit Types (j : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

(* The rform structure has two important components:                      *)
(*                                                                        *)
(* -- a packed/hoisted map m, which will be reified into the ts2 argument *)
(*    of subterm ts2 ts1                                                  *)
(*                                                                        *)
(* -- a boolean b, which will be instantiated with true in the validX     *)
(*    lemma, and will be unified with subterm ts2 ts1 in the start        *)
(*    instance                                                            *)
(*                                                                        *)
(* The other components of rform are j ts1 and pivot, which are forced by *)
(* needing to compose the proofs, but behave plainly in unification.      *)

Structure packed_map (m : U) := Pack {unpack : U}.
Canonical equate (m : U) := Pack m m.

Definition raxiom j ts1 m (b : bool) (pivot : packed_map m) :=
  all (wf j) ts1 -> valid (interp j ts1) -> b -> valid (unpack pivot).

Structure rform j ts1 m b :=
  RForm {pivot :> packed_map m; _ : raxiom j ts1 b pivot}.

(* start instance: note how subterm ts2 ts1 is unified with *)
(* the boolean component of rform *)

Lemma start_pf j k ts1 ts2 (f2 : form j k ts2) :
        @raxiom j ts1 (untag f2) (subterm ts2 ts1) (equate f2).
Proof.
case: f2=>f2 [<- S A2] A1; rewrite (sc_interp S A1)=>V.
case/(subterm_sound A2 (sc_wf S A1))=>xs.
by case/domeqP; rewrite V=>/validL ->.
Qed.

Canonical start j k ts1 ts2 f2 := RForm (@start_pf j k ts1 ts2 f2).

End ValidX.

(* Wrappers for automated versions of joinKx(xK), cancPL(PR) lemmas *)
Section WrappersForCancellationLemmas.
Variable U : cpcm.

Lemma joinKx' (x1 x2 x : U) : x1 \+ x = x2 \+ x -> valid (x1 \+ x) -> x1 = x2.
Proof. by move=>/[swap]; exact: joinKx. Qed.

Lemma joinxK' (x x1 x2 : U) : x \+ x1 = x \+ x2 -> valid (x \+ x1) -> x1 = x2.
Proof. by move=>/[swap]; exact: joinxK. Qed.

Lemma cancPL' (P : U -> Prop) (s1 s2 t1 t2 : U) :
       precise P -> s1 \+ t1 = s2 \+ t2 -> P s1 -> P s2 -> valid (s1 \+ t1) ->
       (s1 = s2) * (t1 = t2).
Proof. by move=>H E H1 H2 V; apply: cancPL H V H1 H2 E. Qed.

Lemma cancPR' (P : U -> Prop) (s1 s2 t1 t2 : U) :
       precise P -> s1 \+ t1 = s2 \+ t2 -> P t1 -> P t2 -> valid (s1 \+ t1) ->
       (s1 = s2) * (t1 = t2).
Proof. by move=>H E H1 H2 V; apply: cancPR H V H1 H2 E. Qed.
End WrappersForCancellationLemmas.

Module Exports.
Canonical equate.
Canonical start.

Section Exports.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Implicit Types (j : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

(* the main lemma; note how the boolean component of rform is set to true *)

Lemma validX m j ts1 (f1 : form (empx U) j ts1) (g: rform j ts1 m true) :
        valid (untag f1) -> valid (unpack (pivot g)).
Proof. by case: g f1; case=>pivot H [f1][<- Sc A] /(H A); apply. Qed.

End Exports.

Arguments validX [K C T U m j ts1 f1 g] _.

Example ex0 (x y z : nat) (v1 v2 : nat) h:
          valid (Unit \+ y \\-> v1 \+ h \+ x \\-> v1) ->
          valid (x \\-> v2 \+ Unit).
Proof. apply: validX. Abort.

(* Automated versions of joinKx(xK), cancPL(PR) lemmas *)
Notation joinKX V E := (joinKx' E (validX V)).
Notation joinXK V E := (joinxK' E (validX V)).
Notation cancPLX pf V H1 H2 E := (cancPL' pf E H1 H2 (validX V)).
Notation cancPRX pf V H1 H2 E := (cancPR' pf E H1 H2 (validX V)).

End Exports.
End ValidX.

Export ValidX.Exports.


(*********************)
(* Automating domeqX *)
(*********************)

Module DomeqX.
Section DomeqX.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Implicit Types (j : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Structure packed_map (m : U) := Pack {unpack : U}.
Canonical equate (m : U) := Pack m m.

(* b is the pair of residual terms *)
Definition raxiom j k ts1 m b (pivot : packed_map m) :=
  all (wf j) ts1 -> sub_ctx j k /\
  (dom_eq (interp k b.1) (interp k b.2) ->
   dom_eq (interp k ts1) (unpack pivot)).

Structure rform j k ts1 m b :=
  RForm {pivot :> packed_map m; _ : raxiom j k ts1 b pivot}.

(* start instance: note how subtract ts1 ts2 [::] is unified with *)
(* the b component of rform thus passing the residual terms *)

Lemma start_pf j k ts1 ts2 (f2 : form j k ts2) :
        @raxiom j k ts1 (untag f2) (subtract ts1 ts2 [::]) (equate f2).
Proof.
case: f2=>f2 [<- S A2]; case E : (subtract _ _ _)=>[rs1 rs2] A1; split=>//.
case/(subtract_sound (sc_wf S A1) A2): E=>ys [/= D1 D2 D].
rewrite unitR in D1; apply: domeq_trans D1 _.
rewrite domeq_symE; apply: domeq_trans D2 _.
by rewrite domeq_symE; apply: domeqUn.
Qed.

Canonical start j k ts1 ts2 f2 := RForm (@start_pf j k ts1 ts2 f2).

End DomeqX.

Module Exports.
Canonical equate.
Canonical start.

Section Exports.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Implicit Types (j : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

(* the main lemma; notice how residuals rs1, rs2 are passed to g to compute *)

Lemma domeqX m j k rs1 rs2 ts1 (f1 : form (empx U) j ts1)
                               (g : rform j k ts1 m (rs1, rs2)) :
        dom_eq (pprint k (rev rs1)) (pprint k rs2) ->
        dom_eq (untag f1) (unpack (pivot g)).
Proof.
case: g f1; case=>pivot R [f1][<- _ A1] /=; case/(_ A1): R=>S D.
by rewrite !pp_interp interp_rev (sc_interp S A1).
Qed.

End Exports.

Arguments domeqX [K C T U m j k rs1 rs2 ts1 f1 g] _.

Example ex0 (x y z : nat) (v1 v2 : nat) h:
          dom_eq (Unit \+ y \\-> v1 \+ h \+ x \\-> v1) (x \\-> v2 \+ Unit).
Proof. apply: domeqX=>/=. Abort.

End Exports.
End DomeqX.

Export DomeqX.Exports.

(***********************)
(* Automating invalidX *)
(***********************)

Module InvalidX.
Section InvalidX.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Implicit Types (i : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Structure packed_map (m : U) := Pack {unpack : U}.
Canonical equate (m : U) := Pack m m.

(* b is the boolean that we want to get out of isundef *)
Definition raxiom i ts m b (pivot : packed_map m) :=
  b -> valid (unpack pivot) = false.

Structure rform i ts m b :=
  RForm {pivot :> packed_map m; _ : raxiom i ts b pivot}.

(* start instance: note how isundef i ts is unified with *)
(* the b component of rform, which will be set to true by lemma statements *)

Lemma start_pf i ts (f : form (empx U) i ts) :
        @raxiom i ts (untag f) (isundef i ts) (equate f).
Proof. by case: f=>f [<- S A] /(isundef_sound A) /negbTE. Qed.

Canonical start i ts f := RForm (@start_pf i ts f).

End InvalidX.

Module Exports.
Canonical equate.
Canonical start.

Section Exports.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Implicit Types (i : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

(* the main lemmas *)

Lemma undefX m i ts (g : rform i ts m true) : unpack (pivot g) = undef.
Proof. by case: g; case=>pivot /= /(_ (erefl _))/negbT/invalidE. Qed.

Lemma invalidX m i ts (g : rform i ts m true) :
        valid (unpack (pivot g)) = false.
Proof. by rewrite undefX valid_undef. Qed.

End Exports.

Arguments invalidX {K C T U m i ts g}.

Example ex0 (x y z : nat) (v1 v2 : nat) h:
          valid (Unit \+ y \\-> v1 \+ h \+ y \\-> v1).
Proof. rewrite invalidX. Abort.

End Exports.
End InvalidX.

Export InvalidX.Exports.

(************************************************)
(* Pushing an omap-like function inside a union *)
(************************************************)

Module OmfX.
Section OmfX.

Inductive syntx A (U : natmap A) :=
  | UnitOmf
  | PtOmf of nat & A
  | UnOmf of syntx U & syntx U
  | OtherOmf of U.

Fixpoint omf_interp A B (U : natmap A) (V : natmap B) (f : omap_fun U V) e : V :=
  match e with
    UnitOmf => Unit
  | PtOmf k v => if omf f (k, v) is Some w then pts k w else Unit
  | UnOmf h1 h2 => omf_interp f h1 \+ omf_interp f h2
  | OtherOmf h => f h
  end.

Structure tagged_natmap A (U : natmap A) := Tag {untag : U}.
Definition unit_tag := Tag.
Definition pt_tag := unit_tag.
Definition union_tag := pt_tag.
Definition recurse_unguard_tag := union_tag.
Canonical recurse_guard_tag A (U : natmap A) f := @recurse_unguard_tag A U f.

Definition guard_ax A B (U : natmap A) (V : natmap B) ts e (f : omap_fun U V) :=
  untag e = f (omf_interp idfun ts).

Structure guarded_form A B (U : natmap A) (V : natmap B) ts := GForm {
  gpivot :> tagged_natmap V;
  guard_of : omap_fun U V;
  _ : guard_ax ts gpivot guard_of}.

Definition unguard_ax A (U : natmap A) (ts : syntx U) e :=
  untag e = omf_interp idfun ts.

Structure unguarded_form A (U : natmap A) (ts : syntx U) := UForm {
  upivot :> tagged_natmap U;
  _ : unguard_ax ts upivot}.

(* we first try to see if there's more function guards *)
Lemma recurse_guard_pf A B C (U : natmap A) (V : natmap B) (W : natmap C)
        ts (f : omap_fun V W)
           (g : @guarded_form A B U V ts) :
        guard_ax ts (recurse_guard_tag (f (untag g)))
                    (f \o guard_of g).
Proof. by case: g=>e g pf /=; rewrite pf. Qed.
Canonical recurse_guard A B C U V W ts f g := GForm (@recurse_guard_pf A B C U V W ts f g).

(* if not, we descend to unguarded form to syntactify the underlying expression *)
Lemma recurse_unguard_pf A (U : natmap A) ts (u : @unguarded_form A U ts) :
        guard_ax ts (recurse_unguard_tag (untag u)) idfun.
Proof. by case: u. Qed.
Canonical recurse_unguard A U ts u := GForm (@recurse_unguard_pf A U ts u).

(* syntactifying union recursively descends to both sides *)
Lemma unguard_union_pf A (U : natmap A) ts1 ts2 
        (u1 : @unguarded_form A U ts1) (u2 : @unguarded_form A U ts2) :
        unguard_ax (UnOmf ts1 ts2) (union_tag (untag u1 \+ untag u2)).
Proof. by case: u1 u2=>u1 pf1 [u2 pf2]; rewrite /= pf1 pf2. Qed.
Canonical unguard_union A U ts1 ts2 u1 u2 := UForm (@unguard_union_pf A U ts1 ts2 u1 u2).

(* base case for syntactifying points-to *)
Lemma unguard_pts_pf A (U : natmap A) k (v : A) : 
        unguard_ax (PtOmf U k v) (pt_tag (pts k v)).
Proof. by []. Qed.
Canonical unguard_pts A U k v := UForm (@unguard_pts_pf A U k v).

(* base case for syntactifying empty map Unit *)
Lemma unguard_unit_pf A (U : natmap A) : unguard_ax (UnitOmf U) (unit_tag Unit).
Proof. by []. Qed.
Canonical unguard_unit A U := UForm (@unguard_unit_pf A U).

(* base case for syntactifying all other expressions *)
Lemma unguard_other_pf A (U : natmap A) (e : U) : unguard_ax (OtherOmf e) (Tag e).
Proof. by []. Qed.
Canonical unguard_other A U e := UForm (@unguard_other_pf A U e).

End OmfX.

Module Exports.
Canonical recurse_guard_tag.
Canonical recurse_guard.
Canonical recurse_unguard.
Canonical unguard_union.
Canonical unguard_pts.
Canonical unguard_unit.
Canonical unguard_other.

(* main lemma *)

Lemma omfX A B C (U : natmap A) (V : natmap B) (W : natmap C) ts 
          (f : omap_fun V W)
          (g : @guarded_form A B U V ts) :
        valid (omf_interp idfun ts) ->
        f (untag g) =
        omf_interp (f \o guard_of g) ts.
Proof.
case: g=>eq g /=; elim: ts eq=>[|s a|ts1 IH1 ts2 IH2|t] /= eq pf X.
- by rewrite pf !pfunit.
- rewrite validPt in X; rewrite pf omfPt // omf_comp /=. 
  by case: (omf g _)=>[x|]; rewrite ?omfPt ?pfunit.
- rewrite pf /= !omfUn //; last by rewrite -omfUn ?pfVE.
  by rewrite IH1 ?(validL X) // IH2 ?(validR X).
by rewrite pf.
Qed.
End Exports.
End OmfX.

Export OmfX.Exports.

