(*
Copyright 2013 IMDEA Software Institute
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
From mathcomp Require Import ssrnat seq eqtype.
From pcm Require Import options prelude.

(***************************************************************************)
(* Common infrastructure for syntactifying expressions in automated lemmas *)
(***************************************************************************)

(* In cancellation algorithms for automated lemmas, we iterate over the   *)
(* first expression e1 and remove each of its components from the second  *)
(* expression e2. But, typically, we want to remove only one occurrence   *)
(* of that component.                                                     *)
(*                                                                        *)
(* First, almost always, only one occurrence will exist, lest e2 be       *)
(* undefined. Thus, it's a waste of effort to traverse e2 in full once    *)
(* we've found an occurrence.                                             *)
(*                                                                        *)
(* Second, in some symmetric cancellation problems, e.g., dom_eq e1 e2,   *)
(* we *want* to remove only one occurrence from e2 for each component in  *)
(* e1. Otherwise, we will not produce a sound reduction. E.g.,            *)
(* dom (x \+ x) (x \+ x) is valid, since both expressions are undef.      *)
(* However, after removing x from the left side, and both x's from the    *)
(* right side, we get dom x Unit, which is not valid.                     *)
(*                                                                        *)
(* Thus, as a matter of principle, we want a filter that removes just one *)
(* occurrence of a list element.                                          *)
(*                                                                        *)
(* We write it with p pulled out in a section in order to get it to       *)
(* simplify automatically.                                                *)

Section OneShotFilter.
Variables (A : Type) (p : pred A).

(* a variant of filter that removes only the first occurence *)

Fixpoint rfilter {A} (p : pred A) (ts : seq A) : seq A :=
  if ts is t :: ts' then if p t then ts' else t :: rfilter p ts' else [::].

End OneShotFilter.

(* rfilter can also be thought of as a generalization of rem *)
Lemma rfilter_rem {T : eqType} (ts : seq T) x :
        rfilter (pred1 x) ts = rem x ts.
Proof. by elim: ts=> [|t ts IH] //=; case: eqP=>//= _; rewrite IH. Qed.

(* A canonical structure program for searching and inserting in a list *)

Section XFind.
Variable A : Type.

Structure tagged_elem := XTag {xuntag :> A}.

(* DEVCOMMENT *)
(* remove? *)
(* Local Coercion untag : tagged_elem >-> A. *)
(* /DEVCOMMENT *)

Definition extend_tag := XTag.
Definition recurse_tag := extend_tag.
Canonical found_tag x := recurse_tag x.

(* Main structure:                                                  *)
(* - xs1 : input sequence                                           *)
(* - xs2 : output sequence; if pivot is found, then xs2 = xs1, else *)
(*   xs2 = pivot :: xs1                                             *)
(* - i : output index of pivot in xs2                               *)

Definition axiom xs1 xs2 i (pivot : tagged_elem) :=
  onth xs2 i = Some (xuntag pivot) /\ Prefix xs1 xs2.
Structure xfind (xs1 xs2 : seq A) (i : nat) :=
  Form {pivot :> tagged_elem; _ : axiom xs1 xs2 i pivot}.

(* found the elements *)
Lemma found_pf x t : axiom (x :: t) (x :: t) 0 (found_tag x).
Proof. by []. Qed.
Canonical found_form x t := Form (@found_pf x t).

(* recurse *)
Lemma recurse_pf i x xs1 xs2 (f : xfind xs1 xs2 i) :
        axiom (x :: xs1) (x :: xs2) i.+1 (recurse_tag (xuntag f)).
Proof. by case: f=>pv [H1 H2]; split=>//; apply/Prefix_cons. Qed.
Canonical recurse_form i x xs1 xs2 f := Form (@recurse_pf i x xs1 xs2 f).

(* failed to find; attach the element to output *)
Lemma extend_pf x : axiom [::] [:: x] 0 (extend_tag x).
Proof. by []. Qed.
Canonical extend_form x := Form (@extend_pf x).

End XFind.
