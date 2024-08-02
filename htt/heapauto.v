(*
Copyright 2012 IMDEA Software Institute
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

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From pcm Require Import options axioms pred prelude.
From pcm Require Import auto pcm autopcm unionmap heap. 
From htt Require Import model.
Import Prenex Implicits.

(**************************************************************************)
(* This file implements automations (both unification- and tactics-based) *)
(* related to Hoare logic for heaps.                                      *)
(*                                                                        *)
(* First automation concerns selection of Hoare-style rule for symbolic   *)
(* evaluation. The first command of the program determines the applicable *)
(* rule uniquely. The implemented automation picks out this rule, and     *)
(* applies it, while using AC-theory of heaps to rearrange the goal, if   *)
(* necessary for the rule to apply.                                       *)
(*                                                                        *)
(* Second automation extends this mechanism for a common combination of   *)
(* invoking the ghost lemma together with the frame rule. This allows the *)
(* user to supply the "kernel" heap to frame on directly instead of       *)
(* rearranging the goal manually with AC-rewriting.                       *)
(*                                                                        *)
(* Third, a tactic for canceling common terms in disjoint unions.         *)
(* Currently, it doesn't deal with weak pointers. I.e. if it sees terms   *)
(* like x :-> v1 and x :-> v2, it will reduce to v1 = v2 only if v1, v2   *)
(* are of the same type. A more general tactic would emit obligation      *)
(* dyn v1 = dyn v2, but that's left for future work.                      *)
(*                                                                        *)
(**************************************************************************)

(****************************************************************)
(* First, the reflection mechanism for search-and-replace       *)
(* pattern-matching on heap expressions; the AC theory of heaps *)
(****************************************************************)

Section Partition.

Structure tagged_heap := Tag {untag :> heap}.

Definition right_tag := Tag.
Definition left_tag := right_tag.
Canonical Structure found_tag i := left_tag i.

Definition form_axiom k r (h : tagged_heap) := untag h = k \+ r.

Structure form (k r : heap) :=
  Form {heap_of :> tagged_heap;
        _ : form_axiom k r heap_of}.

Arguments Form : clear implicits.

Lemma formE r k (f : form k r) : untag f = k \+ r.
Proof. by case: f=>[[j]] /=; rewrite /form_axiom /= => ->. Qed.

Lemma found_pf k : form_axiom k Unit (found_tag k).
Proof. by rewrite /form_axiom unitR. Qed.

Canonical Structure heap_found k := Form k Unit (found_tag k) (found_pf k).

Lemma left_pf h r (f : forall k, form k r) k :
        form_axiom k (r \+ h) (left_tag (untag (f k) \+ h)).
Proof. by rewrite formE /form_axiom /= joinA. Qed.

Canonical Structure search_left h r (f : forall k, form k r) k :=
  Form k (r \+ h) (left_tag (untag (f k) \+ h)) (left_pf h f k).

Lemma right_pf h r (f : forall k, form k r) k :
        form_axiom k (h \+ r) (right_tag (h \+ f k)).
Proof. by rewrite formE /form_axiom /= joinCA. Qed.

Canonical Structure search_right h r (f : forall k, form k r) k :=
  Form k (h \+ r) (right_tag (h \+ f k)) (right_pf h f k).

End Partition.

(**********************************************************)
(* Reflective lemmas that apply modulo AC-theory of heaps *)
(**********************************************************)

(* We maintain three different kinds of lemmas *)
(* in order to streamline the stepping *)
(* The only important ones are the val lemmas, the bnd and try *)
(* are there just to remove some spurious hypotheses about validity, and make the *)
(* verification flow easier *)

(* Each call to some bnd_* or try_* lemma is really a call to bnd_seq or try_seq *)
(* followed by a val_* lemma. Except that doing things in such a sequence *)
(* actually gives us some additional, spurious, validity hypotheses, which we *)
(* always discard anyway. However the discarding interrupts automation, so we want to avoid it *)

(* However, we only need gR lemma *)
(* This one is always applied by hand, not automatically, so *)
(* if we need to prefix it with a call to bnd_seq or try_seq, we can *)
(* do that by hand *)

(* If we were to do this by hand, whenever *)
(* there should be a nicer way to do this *)
(* e.g., suppress all the spurious validity as a default *)
(* and let the user generate them by hand at the leaves, when necessary *)


Section EvalRetR.
Variables (A B : Type).

Definition val_retR := vrf_ret.

Lemma try_retR e1 e2 (v : A) i (r : post B) :
        vrf i (e1 v) r -> vrf i (try (ret v) e1 e2) r.
Proof. by move=>H; apply/vrf_try/val_retR. Qed.

Lemma bnd_retR e (v : A) i (r : post B) :
        vrf i (e v) r -> vrf i (bnd (ret v) e) r.
Proof. by move=>H; apply/vrf_bnd/val_retR. Qed.

End EvalRetR.


Section EvalThrowR.
Variables (A B : Type).

Definition val_throwR := vrf_throw.

Lemma try_throwR e e1 e2 i (r : post B) :
        vrf i (e2 e) r ->
        vrf i (try (@throw A e) e1 e2) r.
Proof. by move=>H; apply/vrf_try/val_throwR. Qed.

Lemma bnd_throwR e e1 i (r : post B) :
        (valid i -> r (Exn e) i) ->
        vrf i (bnd (@throw A e) e1) r.
Proof. by move=>H; apply/vrf_bnd/val_throwR. Qed.

End EvalThrowR.


Section EvalReadR.
Variables (A B : Type).

Lemma val_readR v x i (f : form (x :-> v) i) (r : post A) :
        (valid (untag f) -> r (Val v) f) ->
        vrf f (read x) r.
Proof. by rewrite formE; apply: vrf_read. Qed.

Lemma try_readR e1 e2 v x i (f : form (x :-> v) i) (r : post B) :
        vrf f (e1 v) r ->
        vrf f (try (@read A x) e1 e2) r.
Proof. by move=>H; apply/vrf_try/val_readR. Qed.

Lemma bnd_readR e v x i (f : form (x :-> v) i) (r : post B) :
        vrf f (e v) r ->
        vrf f (bnd (@read A x) e) r.
Proof. by move=>H; apply/vrf_bnd/val_readR. Qed.

End EvalReadR.


Section EvalWriteR.
Variables (A B C : Type).

Lemma val_writeR (v : A) (w : B) x i (f : forall k, form k i) (r : post unit) :
        (valid (untag (f (x :-> v))) -> r (Val tt) (f (x :-> v))) ->
        vrf (f (x :-> w)) (write x v) r.
Proof. by rewrite !formE; apply: vrf_write. Qed.

Lemma try_writeR e1 e2 (v : A) (w : B) x i
                 (f : forall k, form k i) (r : post C) :
        vrf (f (x :-> v)) (e1 tt) r ->
        vrf (f (x :-> w)) (try (write x v) e1 e2) r.
Proof. by move=>H; apply/vrf_try/val_writeR. Qed.

Lemma bnd_writeR e (v : A) (w : B) x i (f : forall k, form k i) (r : post C) :
        vrf (f (x :-> v)) (e tt) r ->
        vrf (f (x :-> w)) (bnd (write x v) e) r.
Proof. by move=>H; apply/vrf_bnd/val_writeR. Qed.

End EvalWriteR.


Section EvalAllocR.
Variables (A B : Type).

Definition val_allocR := vrf_alloc.

Lemma try_allocR e1 e2 (v : A) i (r : post B) :
        (forall x, vrf (x :-> v \+ i) (e1 x) r) ->
        vrf i (try (alloc v) e1 e2) r.
Proof. by move=>H; apply/vrf_try/val_allocR. Qed.

Lemma bnd_allocR e (v : A) i (r : post B) :
        (forall x, vrf (x :-> v \+ i) (e x) r) ->
        vrf i (bnd (alloc v) e) r.
Proof. by move=>H; apply/vrf_bnd/val_allocR. Qed.

End EvalAllocR.


Section EvalAllocbR.
Variables (A B : Type).

Definition val_allocbR := vrf_allocb.

Lemma try_allocbR e1 e2 (v : A) n i (r : post B) :
        (forall x, vrf (updi x (nseq n v) \+ i) (e1 x) r) ->
        vrf i (try (allocb v n) e1 e2) r.
Proof. by move=>H; apply/vrf_try/val_allocbR. Qed.

Lemma bnd_allocbR e (v : A) n i (r : post B) :
        (forall x, vrf (updi x (nseq n v) \+ i) (e x) r) ->
        vrf i (bnd (allocb v n) e) r.
Proof. by move=>H; apply/vrf_bnd/val_allocbR. Qed.

End EvalAllocbR.


Section EvalDeallocR.
Variables (A B : Type).

Lemma val_deallocR (v : A) x i (f : forall k, form k i) (r : post unit) :
        (valid (untag (f Unit)) -> r (Val tt) (f Unit)) ->
        vrf (f (x :-> v)) (dealloc x) r.
Proof. by rewrite !formE unitL=>H; apply: vrf_dealloc. Qed.

Lemma try_deallocR e1 e2 (v : A) x i (f : forall k, form k i) (r : post B) :
        vrf (f Unit) (e1 tt) r ->
        vrf (f (x :-> v)) (try (dealloc x) e1 e2) r.
Proof. by move=>H; apply/vrf_try/val_deallocR. Qed.

Lemma bnd_deallocR e (v : A) x i (f : forall k, form k i) (r : post B) :
        vrf (f Unit) (e tt) r ->
        vrf (f (x :-> v)) (bnd (dealloc x) e) r.
Proof. by move=>H; apply/vrf_bnd/val_deallocR. Qed.

End EvalDeallocR.


(****************************************************)
(* Automating the selection of which lemma to apply *)
(* (reflective implementation of the hstep tactic)  *)
(****************************************************)

(* Need to case-split on bnd_, try_, or a val_ lemma. *)
(* Hence, three classes of canonical structures.      *)

Structure val_form A i r (p : Prop):=
  ValForm {val_pivot :> ST A;
           _ : p -> vrf i val_pivot r}.

Structure bnd_form A B i (e : A -> ST B) r (p : Prop) :=
  BndForm {bnd_pivot :> ST A;
           _ : p -> vrf i (bnd bnd_pivot e) r}.

Structure try_form A B i (e1 : A -> ST B)
                         (e2 : exn -> ST B) r (p : Prop) :=
  TryForm {try_pivot :> ST A;
           _ : p -> vrf i (try try_pivot e1 e2) r}.

(* The main lemma which triggers the selection. *)

Lemma hstep A i (r : post A) p (e : val_form i r p) :
        p -> vrf i e r.
Proof. by case:e=>[?]; apply. Qed.

(* First check if matching on bnd_ or try_. If so, switch to searching *)
(* for bnd_ or try_form, respectively. Otherwise, fall through, and    *)
(* continue searching for a val_form. *)

Lemma bnd_case_pf A B i (s : A -> ST B) r p (e : bnd_form i s r p) :
        p -> vrf i (bnd e s) r.
Proof. by case:e=>[?]; apply. Qed.

Canonical Structure
  bnd_case_form A B i (s : A -> ST B) r p (e : bnd_form i s r p) :=
  ValForm (bnd_case_pf e).

Lemma try_case_pf A B i (s1 : A -> ST B) (s2 : exn -> ST B) r p
                        (e : try_form i s1 s2 r p) :
        p -> vrf i (try e s1 s2) r.
Proof. by case:e=>[?]; apply. Qed.

(* After that, find the form in the following list.  Notice that the list *)
(* can be extended arbitrarily in the future. There is no centralized     *)
(* tactic to maintain. *)

Canonical Structure val_ret_form A v i r :=
  ValForm (@val_retR A v i r).
Canonical Structure bnd_ret_form A B s v i r :=
  BndForm (@bnd_retR A B s v i r).
Canonical Structure try_ret_form A B s1 s2 v i r :=
  TryForm (@try_retR A B s1 s2 v i r).

Canonical Structure val_read_form A v x r j f :=
  ValForm (@val_readR A v x j f r).
Canonical Structure bnd_read_form A B s v x r j f :=
  BndForm (@bnd_readR A B s v x j f r).
Canonical Structure try_read_form A B s1 s2 v x r j f :=
  TryForm (@try_readR A B s1 s2 v x j f r).

Canonical Structure val_write_form A B v w x r j f :=
  ValForm (@val_writeR A B v w x j f r).
Canonical Structure bnd_write_form A B C s v w x r j f :=
  BndForm (@bnd_writeR A B C s v w x j f r).
Canonical Structure try_write_form A B C s1 s2 v w x r j f :=
  TryForm (@try_writeR A B C s1 s2 v w x j f r).

Canonical Structure val_alloc_form A v i r :=
  ValForm (@val_allocR A v i r).
Canonical Structure bnd_alloc_form A B s v i r :=
  BndForm (@bnd_allocR A B s v i r).
Canonical Structure try_alloc_form A B s1 s2 v i r :=
  TryForm (@try_allocR A B s1 s2 v i r).

Canonical Structure val_allocb_form A v n i r :=
  ValForm (@val_allocbR A v n i r).
Canonical Structure bnd_allocb_form A B s v n i r :=
  BndForm (@bnd_allocbR A B s v n i r).
Canonical Structure try_allocb_form A B s1 s2 v n i r :=
  TryForm (@try_allocbR A B s1 s2 v n i r).

Canonical Structure val_dealloc_form A v x r j f :=
  ValForm (@val_deallocR A v x j f r).
Canonical Structure bnd_dealloc_form A B s v x r j f :=
  BndForm (@bnd_deallocR A B s v x j f r).
Canonical Structure try_dealloc_form A B s1 s2 v x r j f :=
  TryForm (@try_deallocR A B s1 s2 v x j f r).

Canonical Structure val_throw_form A e Q i :=
  ValForm (@val_throwR A e Q i).
Canonical Structure bnd_throw_form A B e e1 i r :=
  BndForm (@bnd_throwR A B e e1 i r).
Canonical Structure try_throw_form A B e e1 e2 i r :=
  TryForm (@try_throwR A B e e1 e2 i r).

Ltac step := (apply: hstep=>/=).

(*****************************************************************)
(* Another reflection mechanism for splitting the heap into head *)
(* and tail expressions. Note that this is a restricted version  *)
(* of the partitioning mechanism (no right branching).           *)
(*****************************************************************)

Section Uncons.

Structure tagged_heapU := TagU {untagU :> heap}.

Definition head_tagU := TagU.
Canonical Structure left_tagU i := head_tagU i.

(* - k : output head *)
(* - r : output tail *)
Definition uform_axiom k r (h : tagged_heapU) :=
  untagU h = k \+ r.

Structure uform (k : heap) r :=
  UForm {heap_ofU :> tagged_heapU;
         _ : uform_axiom k r heap_ofU}.

Arguments UForm : clear implicits.

Lemma head_pfU k : uform_axiom k Unit (head_tagU k).
Proof. by rewrite /uform_axiom unitR. Qed.

Canonical Structure heap_headU k := UForm k Unit (head_tagU k) (head_pfU k).

Lemma left_pfU h k r (f : uform k r) :
        uform_axiom k (r \+ h) (left_tagU (untagU f \+ h)).
Proof.
case: f=>f; rewrite /uform_axiom /= =>->.
by rewrite joinA.
Qed.

Canonical Structure search_leftU h k r (f : uform k r) :=
  UForm k (r \+ h) (left_tagU (untagU f \+ h)) (left_pfU h f).

End Uncons.

(***************************)
(* Ghost lemma automations *)
(***************************)

(* This is the main automated ghost lemma, which corresponds to a common     *)
(* combination of gE + vrf_frame. It allows the user to manually supply a    *)
(* heap subexpression (here named `m`) to be "consumed" by the frame rule.   *)
(* For proving the postconditions, the automation replaces the first summand *)
(* in the provided expression by a fresh heap variable and drops the rest.   *)
(*                                                                           *)
(* It uses the following algorithm:                                          *)
(*                                                                           *)
(* 1. The subexpression `m` is split into a head part `m0` and a tail part.  *)
(* 2. The tail part is syntactified into a list of terms `tm`.               *)
(* 3. The goal heap is split into a PCM expression corresponding to `tm` and *)
(*    a residual term, using the `pullX` PCM automation.                     *)
(* 4. The residual term is further split into `m0` and the framed-out heap   *)
(*    expression `r2` using the higher-order partitioning automation, which  *)
(*    simultaneously splits the postcondition heap into `n + r2` (where `n`  *)
(*    is fresh and replaces the first expression of `m`).                    *)
(*                                                                           *)
(* There are two caveats for using this lemma and its variants:              *)
(*                                                                           *)
(* 1. It rewrites the goal into a right-biased form (i.e. `x + (y + z)`).    *)
(*    This happens because it quotes the goal into a list of terms, losing   *)
(*    the associativity information. Switching to tree-based AST for quoted  *)
(*    terms could solve this, but will make the implementation more complex. *)
(* 2. It will fail if the supplied subexpression is a singleton `Unit`. This *)
(*    happens because the unconsing mechanism introduces spurious Units into *)
(*    expressions which are later "garbage collected" by quoting & printing, *)
(*    dropping user-provided Units as well.                                  *)
(*                                                                           *)
(* These issues can be circumvented by falling back to simpler (automated)   *)
(* lemmas `gU`, `gR` and their variants.                                     *)

Lemma gX G A (s : spec G A) g (m : heap) m0 j tm k wh r2
          (e : STspec G s)
          (fm : Syntactify.form (empx _) j tm)
          (fu : uform m0 (Syntactify.untag fm))
          (f : forall q, form q r2)
          (fg : PullX.rform j k tm wh (Some (untag (heap_of (f m0)))))
          (Q : post A) :
        untagU fu = m ->
        (valid m -> (s g).1 m) ->
        (forall v n, (s g).2 (Val v) n ->
           valid (untag (f n)) -> Q (Val v) (f n)) ->
        (forall x n, (s g).2 (Exn x) n ->
           valid (untag (f n)) -> Q (Exn x) (f n)) ->
        vrf (PullX.unpack fg) e Q.
Proof.
case: e=>e /= H; case: fu=>_ ->/= Em Hp Hv Hx; rewrite -{}Em in Hp.
rewrite (pullX (Syntactify.untag fm)) formE joinCA joinA.
apply: vrfV=>/validL/Hp/H V.
apply/vrf_frame/vrf_post/V.
by case=>[v|x] n _=>[/Hv|/Hx]; rewrite formE.
Qed.

Arguments gX {G A s} g m {m0 j tm k wh r2 e fm fu f fg Q}.

Notation "[gX] @ m" := (gX tt m erefl) (at level 0).

Notation "[ 'gX' x1 , .. , xn ] @ m" :=
  (gX (existT _ x1 .. (existT _ xn tt) ..) m erefl)
  (at level 0, format "[ 'gX'  x1 ,  .. ,  xn ] @  m").

Definition heapPCM : pcm := heap.

(* combination of gX + vrf_bind *)
Lemma stepX G A B (s : spec G A) g (m : heapPCM) (m0 : heap) (j : ctx heapPCM) tm k wh r2
          (e : STspec G s) (e2 : A -> ST B)
          (fm : Syntactify.form (empx _) j tm)
          (fu : uform m0 (Syntactify.untag fm))
          (f : forall q, form q r2)
          (fg : PullX.rform j k tm wh (Some (untag (heap_of (f m0)))))
          (Q : post B) :
        untagU fu = m ->
        (valid m -> (s g).1 m) ->
        (forall v n, (s g).2 (Val v) n -> vrf (f n) (e2 v) Q) ->
        (forall x n, (s g).2 (Exn x) n ->
           valid (untag (f n)) -> Q (Exn x) (f n)) ->
        vrf (fg : heapPCM) (bnd e e2) Q.
Proof.
move=>Hm Hp Hv Hx; apply/vrf_bnd/(gX _ _ Hm Hp).
- by move=>v n H V; apply: Hv.
by move=>x n H V _; apply: Hx.
Qed.

Arguments stepX [G A B s] g m {m0 j tm k wh r2 e e2 fm fu f fg Q}.

Notation "[stepX] @ m" := (stepX tt m erefl) (at level 0).
Notation "[ 'stepX' x1 , .. , xn ] @ m" :=
  (stepX (existT _ x1 .. (existT _ xn tt) ..) m erefl)
  (at level 0, format "[ 'stepX'  x1 ,  .. ,  xn ] @ m").

(* combination of gX + vrf_try *)
Lemma tryX G A B (s : spec G A) g (m : heap) m0 j tm k wh r2
          (e : STspec G s) (e1 : A -> ST B) (e2 : exn -> ST B)
          (fm : Syntactify.form (empx _) j tm)
          (fu : uform m0 (Syntactify.untag fm))
          (f : forall q, form q r2)
          (fg : PullX.rform j k tm wh (Some (untag (heap_of (f m0)))))
          (Q : post B) :
        untagU fu = m ->
        (valid m -> (s g).1 m) ->
        (forall v n, (s g).2 (Val v) n -> vrf (f n) (e1 v) Q) ->
        (forall x n, (s g).2 (Exn x) n -> vrf (f n) (e2 x) Q) ->
        vrf (PullX.unpack fg) (try e e1 e2) Q.
Proof.
move=>Hm Hp Hv Hx; apply/vrf_try/(gX _ _ Hm Hp).
- by move=>x n H V; apply: Hv.
by move=>ex n H V; apply: Hx.
Qed.

Arguments tryX {G A B s} g m {m0 j tm k wh r2 e e1 e2 fm fu f fg Q}.

Notation "[tryX] @ m" := (stepX tt m erefl) (at level 0).
Notation "[ 'tryX' x1 , .. , xn ] @ m" :=
  (tryX (existT _ x1 .. (existT _ xn tt) ..) m erefl)
  (at level 0, format "[ 'tryX'  x1 ,  .. ,  xn ] @  m").

(**************************************)
(* Simplified ghost lemma automations *)
(**************************************)

(* simpler version of an automated framing+ghost lemma which only works on *)
(* literal heap subexpressions (here `m`) but preserves associativity.       *)
Lemma gR G A (s : spec G A) g m r (e : STspec G s)
          (f : forall k, form k r) (Q : post A) :
        (valid m -> (s g).1 m) ->
        (forall v n, (s g).2 (Val v) n ->
           valid (untag (f n)) -> Q (Val v) (f n)) ->
        (forall x n, (s g).2 (Exn x) n ->
           valid (untag (f n)) -> Q (Exn x) (f n)) ->
        vrf (f m) e Q.
Proof.
case: e=>e /= H Hp Hv Hx; rewrite formE.
apply: vrfV=>/validL/Hp/H V.
apply/vrf_frame/vrf_post/V.
by case=>[x|ex] n _ =>[/Hv|/Hx]; rewrite formE.
Qed.

Arguments gR {G A s} g m {r e f Q}.

Notation "[gR] @ m" := (gR tt m) (at level 0).
Notation "[ 'gR' x1 , .. , xn ] @ m" :=
  (gR (existT _ x1 .. (existT _ xn tt) ..) m)
  (at level 0, format "[ 'gR'  x1 ,  .. ,  xn ] @  m").

(* combination of gR + vrf_bind *)
Lemma stepR G A B (s : spec G A) g i j (e : STspec G s) (e2 : A -> ST B)
          (f : forall k, form k j) (Q : post B) :
        (valid i -> (s g).1 i) ->
        (forall x m, (s g).2 (Val x) m -> vrf (f m) (e2 x) Q) ->
        (forall x m, (s g).2 (Exn x) m ->
           valid (untag (f m)) -> Q (Exn x) (f m)) ->
        vrf (f i) (bnd e e2) Q.
Proof.
move=>Hi H1 H2; apply/vrf_bnd/(gR _ _ Hi). 
- by move=>x m H V; apply: H1 H.
by move=>ex m H V _; apply: H2.
Qed.

Arguments stepR {G A B s} g i {j e e2 f Q}.

Notation "[stepR] @ i" := (stepR tt i) (at level 0).
Notation "[ 'stepR' x1 , .. , xn ] @ i" :=
  (stepR (existT _ x1 .. (existT _ xn tt) ..) i)
  (at level 0, format "[ 'stepR'  x1 ,  .. ,  xn ] @  i").

(* combination of gR + vrf_try *)
Lemma tryR G A B (s : spec G A) g i j (e : STspec G s) 
          (e1 : A -> ST B) (e2 : exn -> ST B)
          (f : forall k, form k j) (Q : post B) :
        (valid i -> (s g).1 i) ->
        (forall x m, (s g).2 (Val x) m -> vrf (f m) (e1 x) Q) ->
        (forall x m, (s g).2 (Exn x) m -> vrf (f m) (e2 x) Q) ->
        vrf (f i) (try e e1 e2) Q.
Proof.
move=>Hi H1 H2.
apply/vrf_try/(gR _ _ Hi)=>[x|ex] m H V.
- by apply: H1 H.
by apply: H2.
Qed.

Arguments tryR {G A B s} g i {j e e1 e2 f Q}.

Notation "[tryR] @ i" := (tryR tt i) (at level 0).
Notation "[ 'tryR' x1 , .. , xn ] @ i" :=
  (tryR (existT _ x1 .. (existT _ xn tt) ..) i)
  (at level 0, format "[ 'tryR'  x1 ,  .. ,  xn ] @  i").

(* The following is brittle, and should eventually be substituted *)
(* with overloaded lemmas. For now, sticking with the hack *)
(* for the purpose of supporting legacy proofs *)

(* First cancelation in hypotheses *)

Section Cancellation.
Implicit Type (h : heap).

Lemma cexit1 h1 h2 h : h1 = h2 -> h1 \+ h = h \+ h2.
Proof. by move=>->; rewrite joinC. Qed.

Lemma cexit2 h1 h : h1 = Unit -> h1 \+ h = h.
Proof. by move=>->; rewrite unitL. Qed.

Lemma cexit3 h1 h : Unit = h1 -> h = h \+ h1.
Proof. by move=><-; rewrite unitR. Qed.

Lemma congUh A h1 h2 x (v1 v2 : A) :
        h1 = h2 -> v1 = v2 -> h1 \+ (x :-> v1) = h2 \+ (x :-> v2).
Proof. by move=>-> ->. Qed.

Lemma congeqUh h1 h2 h : h1 = h2 -> h1 \+ h = h2 \+ h.
Proof. by move=>->. Qed.

End Cancellation.

(* Cancellation in conclusions *)

Ltac congruencer t :=
  match goal with
  | |- ?h1 \+ t = ?h2 =>
     let j := fresh "j" in
     set j := {1}(h1 \+ t);
     rewrite -1?joinA /j {j};
     (apply: cexit1 || apply: cexit2)
  | |- t = ?h2 =>
     rewrite -1?joinA;
     (apply: cexit3 || apply: refl_equal)
  | |- (?h1 \+ (?x :-> ?v) = ?h2) =>
    let j := fresh "j" in
    set j := {1}(h1 \+ (x :-> v));
    (* if x appears in the second union, first bring it to the back *)
    rewrite 1?(joinC (x :-> _)) -?(joinAC _ _ (x :-> _)) /j {j};
    (* then one of the following must apply *)
    (* if x is in the second union then cancel *)
    ((apply: congUh; [congruencer t | idtac]) ||
    (* if not, rotate x in the first union *)
     (rewrite (joinC h1) ?joinA; congruencer t))
  (* if the heap is not a points-to relation, also try to cancel *)
  | |- (?h1 \+ ?h = ?h2) =>
    let j := fresh "j" in
    set j := {1}(h1 \+ h);
    (* if h appears in the second union, first bring it to the back *)
    rewrite 1?(joinC h) -?(joinAC _ _ h) /j {j};
    (* then one of the following must apply *)
    (* if h is in the second union then cancel *)
    (apply: congeqUh ||
    (* if not, rotate h in the first union *)
    rewrite (joinC h1) ?joinA);
    (* and proceed *)
    congruencer t
  | |- _ => idtac
  end.

Ltac heap_congr :=
  match goal with
  | |- ?h1 = ?h2 =>
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in
    let t := fresh "t" in
      set t1 := {1}h1; set t2 := {1}h2;
      (* introduce terminators *)
      rewrite -(unitL t1) -(unitL t2) [Unit]lock;
      set t := locked Unit; rewrite /t1 /t2 {t1 t2};
      (* flatten the goal *)
      rewrite ?joinA;
      (* call the congruence routine and remove the terminator *)
      congruencer t=>{t}
  | |- _ => idtac
  end.

(* we keep some tactics to kill final goals, which *)
(* are usually full of existentials *)
Ltac vauto := (do ?econstructor=>//).
Ltac hhauto := (vauto; try by [heap_congr])=>//.
Ltac heval := do ![step | by hhauto].
