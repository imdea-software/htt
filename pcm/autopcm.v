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

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq.
From pcm Require Import options pred prelude pcm.
From pcm Require Export auto.

(**************************************************************************)
(**************************************************************************)
(* Canonical structure lemmas for automating the following task:          *)
(*                                                                        *)
(* Splitting a PCM expression e into a combination of a input             *)
(* subexpression e1 (modulo AC) and a residual expression obtained by     *)
(* dropping all subterms of e1 from e.                                    *)
(*                                                                        *)
(* This allows us to formulate a generalized "pull"-style transformation, *)
(* which can factor out a given subexpression with one invocation. Note,  *)
(* however, that this rewrites the goal into a right-biased form, losing  *)
(* the associativity information.                                         *)
(*                                                                        *)
(**************************************************************************)
(**************************************************************************)

(* Context structure for reflection of PCM expressions. An expression is *)
(* everything that are not recognized as a disjoint union, i.e., it can  *)
(* be a variable or a literal.                                           *)

Section ReflectionContexts.
Variables (U : pcm).

Structure ctx := Context {expx : seq U}.

Definition empx := Context [::].

(* because contexts grow during computation, we need a notion of sub-context *)

Definition sub_ctx (i j : ctx) :=
  Prefix (expx i) (expx j).

Lemma sc_refl i : sub_ctx i i.
Proof. by []. Qed.

Lemma sc_trans i j k : sub_ctx i j -> sub_ctx j k -> sub_ctx i k.
Proof. by apply: Prefix_trans. Qed.

End ReflectionContexts.

(* Expressions are syntactified as De Bruijn indices in the context. *)
(* Disjoint union is syntactified as concatenation of lists.         *)

(* now for reflection *)

Section Reflection.
Variables (U : pcm).
Implicit Type i : ctx U.

Variant term := Expr of nat.

Definition nat_of (t : term) : nat :=
  let: Expr n := t in n.

(* interpretation function for elements *)
Definition interp' (i : ctx U) (t : term) : option U :=
  let: Expr n := t in onth (expx i) n.

(* main interpretation function *)
Notation fx i := (fun t f => interp' i t \+ f).
Definition interp (i : ctx U) (ts : seq term) : option U :=
  foldr (fx i) Unit ts.

Lemma fE i ts x : foldr (fx i) x ts = x \+ interp i ts.
Proof. by elim: ts x=>[|t ts IH] x /=; rewrite ?unitR // IH /= joinCA. Qed.

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

Definition exp n t := let: Expr m := t in n == m.

Definition efree n t := rfilter (exp n) t.
Arguments efree /.

Lemma expP i n ts :
        has (exp n) ts ->
        interp i ts = onth (expx i) n \+ interp i (efree n ts).
Proof.
elim: ts=>[|t ts IH] //=; case: ifP=>/= [|_ H].
- by case: t=>/= m /eqP->.
by rewrite (IH H) joinCA.
Qed.

(* interpretation is invariant under context weakening *)
(* under assumption that the interpreted term is well-formed *)

Definition wf i t :=
  let: Expr n := t in n < size (expx i).

Lemma sc_wf i j ts : sub_ctx i j -> all (wf i) ts -> all (wf j) ts.
Proof.
move/Prefix_size=>H; elim: ts=>[|t ts IH] //=.
case/andP=>Hi /IH ->; rewrite andbT.
by case: t Hi=>v /= Hi; apply: leq_trans H.
Qed.

Lemma sc_interp i j ts :
        sub_ctx i j -> all (wf i) ts -> interp i ts = interp j ts.
Proof.
move=>H; elim: ts=>[|t ts IH] //= /andP [H0] /IH ->.
by case: t H0=>n /= /Prefix_onth <-.
Qed.

Lemma wf_efree i n ts : all (wf i) ts -> all (wf i) (efree n ts).
Proof. by elim: ts=>//= t ts IH; case: ifP=>_ /andP [] //= -> /IH ->. Qed.

End Reflection.


(************************************************************************)
(************************************************************************)
(* Purely functional decision procedure for the subtraction task.       *)
(* Further below, it will be embedded into the canonical program pullX. *)
(************************************************************************)
(************************************************************************)

(* subtract is purely functional version of pullX *)

Section Subtract.
Variables (U : pcm).
Implicit Types (i : ctx U) (ts : seq term).

(* We need a subterm lemma that returns the residiual of ts1. *)
(* xs accumulates uncancelled part of ts1, starting as nil *)

Fixpoint subtract ts1 ts2 xs : option (seq term) :=
  match ts1 with
    Expr n :: tsx1 =>
      if has (exp n) ts2 then subtract tsx1 (efree n ts2) xs
      else subtract tsx1 ts2 (Expr n :: xs)
  | [::] => if ts2 is [::] then Some xs else None
  end.

Lemma subtract_sound i ts1 ts2 rs1 xs :
        all (wf i) ts1 -> all (wf i) ts2 ->
        subtract ts1 ts2 xs = Some rs1 ->
        interp i ts1 \+ interp i xs = interp i rs1 \+ interp i ts2.
Proof.
elim: ts1 ts2 xs=>[|t ts1 IH] ts2 xs /= =>[_|/andP [At A1]].
- by case: ts2=>//=_; case=>->; rewrite unitR unitL.
case: t At=>n /= /size_onth [x X] A2; case: ifP=>Y.
- rewrite -joinA; move: (expP i Y)=>-> /(IH _ _ A1 (wf_efree n A2))->.
  by rewrite joinCA.
by move/(IH _ _ A1 A2)=><-/=; rewrite joinCA joinA.
Qed.

End Subtract.


(********************************)
(********************************)
(* Canonical structure programs *)
(********************************)
(********************************)

Module Syntactify.
Section Syntactify.
Variables (U : pcm).
Implicit Types (i : ctx U) (ts : seq term).

(* a tagging structure to control the flow of computation *)
Structure tagged_pcm := Tag {untag : U}.

Local Coercion untag : tagged_pcm >-> PCM.sort.

(* in reversed order; first test for unions, then empty, and exprs *)
Definition expr_tag := Tag.
Definition empty_tag := expr_tag.
Canonical Structure union_tag hc := empty_tag hc.

(* Main structure                                 *)
(* - i : input context                            *)
(* - j : output context                           *)
(* - ts : syntactification of pcm using context j *)

Definition axiom i j ts (pivot : tagged_pcm) :=
  [/\ interp j ts = Some (untag pivot), sub_ctx i j & all (wf j) ts].
Structure form i j ts := Form {pivot : tagged_pcm; _ : axiom i j ts pivot}.

Local Coercion pivot : form >-> tagged_pcm.

(* check for union *)

Lemma union_pf i j k ts1 ts2 (f1 : form i j ts1) (f2 : form j k ts2) :
        axiom i k (ts1 ++ ts2) (union_tag (untag f1 \+ untag f2)).
Proof.
case: f1 f2 =>[[u1]] /= [E1 S1 W1][[u2]][E2 S2 W2]; split=>/=.
- by rewrite /interp foldr_cat !fE unitL joinC -(sc_interp S2 W1) E1 E2.
- by apply: sc_trans S1 S2.
by rewrite all_cat (sc_wf S2 W1) W2.
Qed.

Canonical union_form i j k ts1 ts2 (f1 : form i j ts1) (f2 : form j k ts2) :=
  Form (@union_pf i j k ts1 ts2 f1 f2).

(* check if reached empty *)

Lemma empty_pf i : axiom i i [::] (empty_tag Unit).
Proof. by split. Qed.

Canonical empty_form i :=
  Form (@empty_pf i).

(* check for expr *)

Lemma expr_pf exprs1 exprs2 n (f : xfind exprs1 exprs2 n) :
        axiom (Context exprs1) (Context exprs2)
              [:: Expr n] (expr_tag (xuntag f)).
Proof.
case: f=>p [E H]; split=>//=; first by rewrite unitR.
by rewrite andbT (onth_size E).
Qed.

Canonical expr_form exprs1 exprs2 n (f : xfind exprs1 exprs2 n) :=
  Form (@expr_pf exprs1 exprs2 n f).

End Syntactify.

Module Exports.
Coercion untag : tagged_pcm >-> PCM.sort.
Coercion pivot : form >-> tagged_pcm.
Canonical union_tag.
Canonical union_form.
Canonical empty_form.
Canonical expr_form.

End Exports.
End Syntactify.

Export Syntactify.Exports.

(********************)
(* Automating pullX *)
(********************)

Module PullX.
Section PullX.
Variables (U : pcm).
Implicit Types (j k : ctx U) (ts : seq term).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Structure packed_pcm (m : U) := Pack {unpack : U}.

Local Coercion unpack : packed_pcm >-> PCM.sort.

Canonical equate (m : U) := Pack m m.

(* j  : input context                                   *)
(* k  : output context                                  *)
(* ts : (input) the syntactification of subtractee in j *)
(* g  : (aux) copy of the goal                          *)
(* r  : (output) the optional residual term             *)

(* We have a choice of leaving the residual in a syntactified form or printing *)
(* it back into a PCM. Here we choose the second option since in HTT we need   *)
(* to pass the residual to a partitioning autolemma which operates on heaps.   *)

Definition raxiom j k ts g (r : option U) (pivot : packed_pcm g) :=
  all (wf j) ts -> r -> sub_ctx j k /\
  Some (unpack pivot) = interp k ts \+ r.

Structure rform j k ts g r :=
  RForm {pivot : packed_pcm g; _ : @raxiom j k ts g r pivot}.

Local Coercion pivot : rform >-> packed_pcm.

(* start instance: syntactify the goal (by triggering fg),     *)
(* run the subtraction on quoted terms and print the residual. *)

Lemma start_pf j k ts tg (fg : form j k tg) :
  @raxiom j k ts (untag fg)
                 (obind (pprint k \o rev) (subtract tg ts [::]))
                 (equate fg).
Proof.
case: fg=>fg [Eg S Ag]; case E: (subtract _ _ _)=>[rs|] //= Am _; split=>//.
move/(subtract_sound Ag (sc_wf S Am)): E=>/=.
by rewrite unitR joinC Eg pp_interp interp_rev.
Qed.

Canonical start j k ts tg (fg : form j k tg) :=
  RForm (@start_pf j k ts tg fg).

End PullX.

Module Exports.
Coercion unpack : packed_pcm >-> PCM.sort.
Coercion pivot : rform >-> packed_pcm.
Canonical equate.
Canonical start.

Section Exports.
Variables (U : pcm).
Implicit Types (j : ctx U) (ts : seq term).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

(* we need to syntactify first the subtractee (fm), then the goal (fg) *)

Lemma pullX' s j k ts g r (fs : form (empx U) j ts)
                          (fg : rform j k ts g (Some r)) :
        untag fs = s ->
        unpack (pivot fg) = s \+ r.
Proof.
move=><-; case: fg fs; case=>pivot R [fm][E _ A1] /=.
case/(_ A1 erefl): R=>S /=; rewrite -(sc_interp S A1) E.
by case.
Qed.

End Exports.

Arguments pullX' [U] s [j k ts g r fs fg] _.
Notation pullX s := (pullX' s erefl).

Example ex0 (x y z : nat) :
          1 \+ x \+ 2 \+ y \+ 3 \+ z = 0.
Proof.
rewrite [LHS](pullX (3 \+ 2)) /=.
Abort.

End Exports.
End PullX.

Export PullX.Exports.







