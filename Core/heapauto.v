From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl Require Import axioms pred prelude.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import heaptac model.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(**************************************************************************)
(* This file implements two different automations related to Hoare logic. *)
(*                                                                        *)
(* First automation concerns selection of Hoare-style rule for symbolic   *)
(* evaluation. The first command of the program determines the applicable *)
(* rule uniquely. The implemented automation picks out this rule, and     *)
(* applies it, while using AC-theory of heaps to rearrange the goal, if   *)
(* necessary for the rule to apply.                                       *)
(*                                                                        *)
(* Second automation concerns pulling ghost variables out of a Hoare      *)
(* type. The non-automated lemmas do this pulling one variable at a       *)
(* time. The automation pulls all the variable at once.                   *)
(**************************************************************************)

(****************************************************************)
(* First, the reflection mechanism for search-and-replace       *)
(* pattern-matching on heap expressions; the AC theory of heaps *)
(****************************************************************)

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

(**********************************************************)
(* Reflective lemmas that apply module AC-theory of heaps *)
(**********************************************************)

Section EvalDoR.
Variables (G A B : Type) (s : spec G A).

(* a automated form of gE (is it useful?) *)
Lemma gR g i j (e : STspec s) (f : forall k, form k j) (r : post A) :
        (valid i -> (s g).1 i) ->
        (forall x m, (s g).2 (Val x) m ->
           valid (untag (f m)) -> r (Val x) (f m)) ->
        (forall x m, (s g).2 (Exn x) m ->
           valid (untag (f m)) -> r (Exn x) (f m)) ->
        vrf (f i) e r.
Proof.
case: e=>e /= H H1 H2 H3; rewrite formE.
apply: vrf_frame=>V; move: (H1 V)=>/H [P M].
exists P; case=>[x|ex] m /M.
- by move: (H2 x m); rewrite formE.
by move: (H3 ex m); rewrite formE.
Qed.

End EvalDoR.

(* We maintain three different kinds of lemmas *)
(* in order to streamline the stepping *)
(* The only important ones are the val lemmas, the bnd and try *)
(* are there just to remove some spurious hypotheses about validity, and make the *)
(* verification flow easier *)

(* Each call to some bnd_* or try_* lemma is really a call to bnd_seq or try_seq *)
(* followed by a val_* lemma. Except that doing things in such a sequence *)
(* actually gives us some additional, spurious, validity hypotheses, which we *)
(* always discard anyway. However the discarding interrupts automation, so we want to avoid it *)

(* However, we only need only gR lemma *)
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
        vrf i (e v) r -> vrf i (bind (ret v) e) r.
Proof. by move=>H; apply/vrf_bind/val_retR. Qed.

End EvalRetR.


Section EvalReadR.
Variables (A B : Type).

Lemma val_readR v x i (f : form (x :-> v) i) (r : post A) :
        (valid (untag f) -> r (Val v) f) ->
        vrf f (read A x) r.
Proof. by rewrite formE; apply: vrf_read. Qed.

Lemma try_readR e1 e2 v x i (f : form (x :-> v) i) (r : post B) :
        vrf f (e1 v) r ->
        vrf f (try (read A x) e1 e2) r.
Proof. by move=>H; apply/vrf_try/val_readR. Qed.

Lemma bnd_readR e v x i (f : form (x :-> v) i) (r : post B) :
        vrf f (e v) r ->
        vrf f (bind (read A x) e) r.
Proof. by move=>H; apply/vrf_bind/val_readR. Qed.

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
        vrf (f (x :-> w)) (bind (write x v) e) r.
Proof. by move=>H; apply/vrf_bind/val_writeR. Qed.

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
        vrf i (bind (alloc v) e) r.
Proof. by move=>H; apply/vrf_bind/val_allocR. Qed.

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
        vrf i (bind (allocb v n) e) r.
Proof. by move=>H; apply/vrf_bind/val_allocbR. Qed.

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
        vrf (f (x :-> v)) (bind (dealloc x) e) r.
Proof. by move=>H; apply/vrf_bind/val_deallocR. Qed.

End EvalDeallocR.


Section EvalThrowR.
Variables (A B : Type).

Definition val_throwR := vrf_throw.

Lemma try_throwR e e1 e2 i (r : post B) :
        vrf i (e2 e) r ->
        vrf i (try (throw A e) e1 e2) r.
Proof. by move=>H; apply/vrf_try/val_throwR. Qed.

Lemma bnd_throwR e e1 i (r : post B) :
        (valid i -> r (Exn e) i) ->
        vrf i (bind (throw A e) e1) r.
Proof. by move=>H; apply/vrf_bind/val_throwR. Qed.

End EvalThrowR.


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
           _ : p -> vrf i (bind bnd_pivot e) r}.

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
        p -> vrf i (bind e s) r.
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

(* Second automation *)
(*
(**************************************************************************)
(* A simple canonical structure program to automate applying ghE and gh.  *)
(*                                                                        *)
(* The gh_form pivots on a spec, and computes as output the following.    *)
(* - rT is a product of types of all encounted ghost vars.                *)
(* - p and q are pre and post parametrized by rT that should be output by *)
(*   the main lemma.                                                      *)
(*                                                                        *)
(* In the future, rT should be a list of types, rather than a product,    *)
(* but that leads to arity polimorphism, and dependent programming, which *)
(* I want to avoid for now.                                               *)
(**************************************************************************)

Section Automation.
Structure tagged_spec A := gh_step {gh_untag :> spec A}.
Canonical Structure gh_base A (s : spec A) := gh_step s.

Definition gh_axiom A rT p q (pivot : tagged_spec A) :=
  gh_untag pivot = logvar (fun x : rT => binarify (p x) (q x)).

Structure gh_form A rT (p : rT -> pre) (q : rT -> post A) := GhForm {
   gh_pivot :> tagged_spec A;
   _ : gh_axiom p q gh_pivot}.

(* the main lemma that automates the applications of ghE and gh *)

Lemma ghR A e rT p q (f : @gh_form A rT p q) :
        (forall i x, p x i -> valid i -> vrf i e (q x)) ->
        conseq e f.
Proof. by case: f=>p' ->; apply: gh. Qed.

(* base case; check if we reached binarify *)

Lemma gh_base_pf A rT (p : rT -> pre) (q : rT -> post A) :
        gh_axiom p q (gh_base (logvar (fun x => binarify (p x) (q x)))).
Proof. by []. Qed.

Canonical gh_base_struct A rT p q := GhForm (@gh_base_pf A rT p q).

(* inductive case; merge adjacent logvars and continue *)

Lemma gh_step_pf A B rT p q (f : forall x : A, @gh_form B rT (p x) (q x)) :
        gh_axiom (fun xy => p xy.1 xy.2) (fun xy => q xy.1 xy.2)
                 (gh_step (logvar (fun x => f x))).
Proof.
congr (_, _).
- apply: fext=>i; apply: pext; split.
  - by case=>x; case: (f x)=>[_ ->] /= [y H]; exists (x, y).
  by case; case=>x y; exists x; case: (f x)=>[_ ->]; exists y.
apply: fext=>y; apply: fext=>i; apply: fext=>m; apply: pext; split.
- by move=>H [x z] /= H1; case: (f x) (H x)=>[_ ->]; apply.
by move=>H x; case: (f x)=>[_ ->] z; apply: (H (x, z)).
Qed.

Canonical gh_step_struct A B rT p q f := GhForm (@gh_step_pf A B rT p q f).

End Automation.
*)

(* we keep some tactics to kill final goals, which *)
(* are usually full of existentials *)
Ltac vauto := (do ?econstructor=>//).
Ltac hhauto := (vauto; try by [heap_congr])=>//.
Ltac heval := do ![step | by hhauto].
