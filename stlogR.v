Set Automatic Coercions Import.
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
Require Import pred pcm unionmap heap heaptac stmod stsep stlog. 
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(**********************************************************)
(* First, the reflection mechanism for search-and-replace *)
(* pattern-matching on heap expressions.                  *)
(**********************************************************)

Structure tagged_heap := Tag {untag :> heap}.

Definition right_tag := Tag.
Definition left_tag := right_tag.
Canonical Structure found_tag i := left_tag i.

Definition form_axiom k r (h : tagged_heap) := untag h = k \+ r.

Structure form (k r : heap) :=
  Form {heap_of :> tagged_heap; 
        _ : form_axiom k r heap_of}.

Implicit Arguments Form [].

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

(*********************)
(* Reflective lemmas *)
(*********************)

Notation cont A := (ans A -> heap -> Prop).

Section EvalDoR.
Variables (A B : Type) (p : heap -> Prop) (q : ans A -> heap -> Prop).

(* TODO: We only need the val_do form; the bnd_do and try_do *)
(* should be removed, as they can be avoided by using vrf_seq *)
(* some cleanup required *)

Lemma val_doR e i j (f : forall k, form k j) (r : cont A) :
         (valid i -> p i) -> 
         (forall x m, q (Val x) m -> 
            valid (untag (f m)) -> r (Val x) (f m)) ->
         (forall x m, q (Exn x) m -> 
            valid (untag (f m)) -> r (Exn x) (f m)) -> 
         verify (f i) (with_spec (binarify p q) e) r.
Proof.
move=>H1 H2 H3; rewrite formE; apply: (val_do H1).
- by move=>x m; move: (H2 x m); rewrite formE.
by move=>x m; move: (H3 x m); rewrite formE.
Qed.

(*
Lemma try_doR (e : ST A) e1 e2 i j (f : forall k, form k j) (r : cont B) : 
        (valid i -> pre_of e i) -> 
        (forall x m, post_of e (Val x) i m -> verify (f m) (e1 x) r) ->
        (forall x m, post_of e (Exn x) i m -> verify (f m) (e2 x) r) ->
        verify (f i) (ttry e e1 e2) r.
Proof.
move=>H1 H2 H3; rewrite formE; apply: (try_do' H1).
- by move=>x m; move: (H2 x m); rewrite formE.
by move=>x m; move: (H3 x m); rewrite formE.
Qed.

Lemma bnd_doR (e : ST A) e2 i j (f : forall k, form k j) (r : cont B) : 
        (valid i -> pre_of e i) -> 
        (forall x m, post_of e (Val x) i m -> verify (f m) (e2 x) r) -> 
        (forall x m, post_of e (Exn x) i m -> 
                       valid (untag (f m)) -> r (Exn x) (f m)) ->
        verify (f i) (bind e e2) r.
Proof.
move=>H1 H2 H3; rewrite formE; apply: (bnd_do' H1).
- by move=>x m; move: (H2 x m); rewrite formE.
by move=>x m; move: (H3 x m); rewrite formE.
Qed.
*)

End EvalDoR.

(* ret lemmas need no reflection, as they operate on any heap; still *)
(* rename them for uniformity *)

Definition val_retR := val_ret.
Definition try_retR := try_ret.
Definition bnd_retR := bnd_ret.

Section EvalReadR.
Variables (A B : Type).

Lemma val_readR v x i (f : form (x :-> v) i) (r : cont A) : 
        (valid (untag f) -> r (Val v) f) -> 
        verify f (read A x) r.
Proof. by rewrite formE; apply: val_read. Qed.
 
Lemma try_readR e1 e2 v x i (f : form (x :-> v) i) (r : cont B) : 
        verify f (e1 v) r -> 
        verify f (ttry (read A x) e1 e2) r. 
Proof. by rewrite formE; apply: try_read. Qed.

Lemma bnd_readR e v x i (f : form (x :-> v) i) (r : cont B) : 
        verify f (e v) r -> 
        verify f (bind (read A x) e) r.
Proof. by rewrite formE; apply: bnd_read. Qed. 

End EvalReadR.

Section EvalWriteR. 
Variables (A B C : Type).

Lemma val_writeR (v : A) (w : B) x i (f : forall k, form k i) (r : cont unit) : 
        (valid (untag (f (x :-> v))) -> r (Val tt) (f (x :-> v))) -> 
        verify (f (x :-> w)) (write x v) r.
Proof. by rewrite !formE; apply: val_write. Qed.

Lemma try_writeR e1 e2 (v : A) (w : C) x i 
                 (f : forall k, form k i) (r : cont B) : 
        verify (f (x :-> v)) (e1 tt) r -> 
        verify (f (x :-> w)) (ttry (write x v) e1 e2) r. 
Proof. rewrite !formE; apply: try_write. Qed.

Lemma bnd_writeR e (v : A) (w : C) x i (f : forall k, form k i) (r : cont B) : 
        verify (f (x :-> v)) (e tt) r -> 
        verify (f (x :-> w)) (bind (write x v) e) r. 
Proof. by rewrite !formE; apply: bnd_write. Qed.

End EvalWriteR.

Definition val_allocR := val_alloc.
Definition try_allocR := try_alloc.
Definition bnd_allocR := bnd_alloc.
Definition val_allocbR := val_allocb.
Definition try_allocbR := try_allocb.
Definition bnd_allocbR := bnd_allocb.

Section EvalDeallocR.
Variables (A B : Type).

Lemma val_deallocR (v : A) x i (f : forall k, form k i) (r : cont unit) : 
        (valid (untag (f Unit)) -> r (Val tt) (f Unit)) -> 
        verify (f (x :-> v)) (dealloc x) r.
Proof. by rewrite !formE unitL; apply: val_dealloc. Qed.

Lemma try_deallocR e1 e2 (v : B) x i (f : forall k, form k i) (r : cont A) :
        verify (f Unit) (e1 tt) r -> 
        verify (f (x :-> v)) (ttry (dealloc x) e1 e2) r.
Proof. by rewrite !formE unitL; apply: try_dealloc. Qed.

Lemma bnd_deallocR e (v : B) x i (f : forall k, form k i) (r : cont A) : 
        verify (f Unit) (e tt) r -> 
        verify (f (x :-> v)) (bind (dealloc x) e) r.
Proof. by rewrite !formE unitL; apply: bnd_dealloc. Qed.

End EvalDeallocR.

Definition val_throwR := val_throw.
Definition try_throwR := try_throw. 
Definition bnd_throwR := bnd_throw.


(****************************************************)
(* Automating the selection of which lemma to apply *)
(* (reflective implementation of the hstep tactic)  *)
(****************************************************)

(* Need to case-split on bnd_, try_, or a val_ lemma. *)
(* Hence, three classes of canonical structures.      *)

Structure val_form A i r (p : Prop):=
  ValForm {val_pivot :> ST A;
           _ : p -> verify i val_pivot r}.

Structure bnd_form A B i (e : A -> ST B) r (p : Prop) :=
  BndForm {bnd_pivot :> ST A;
           _ : p -> verify i (bind bnd_pivot e) r}.

Structure try_form A B i (e1 : A -> ST B) 
                         (e2 : exn -> ST B) r (p : Prop) :=
  TryForm {try_pivot :> ST A;
           _ : p -> verify i (ttry try_pivot e1 e2) r}.

(* The main lemma which triggers the selection. *)

Lemma hstep A i (r : cont A) p (e : val_form i r p) :
        p -> verify i e r.
Proof. by case:e=>[?]; apply. Qed.

(* First check if matching on bnd_ or try_. If so, switch to searching *)
(* for bnd_ or try_form, respectively. Otherwise, fall through, and    *)
(* continue searching for a val_form. *)

Lemma bnd_case_pf A B i (s : A -> ST B) r p (e : bnd_form i s r p) :
        p -> verify i (bind e s) r.
Proof. by case:e=>[?]; apply. Qed.

Canonical Structure 
  bnd_case_form A B i (s : A -> ST B) r p (e : bnd_form i s r p) := 
  ValForm (bnd_case_pf e).

Lemma try_case_pf A B i (s1 : A -> ST B) (s2 : exn -> ST B) r p
                        (e : try_form i s1 s2 r p) : 
        p -> verify i (ttry e s1 s2) r.
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




(* we keep some tactics to kill final goals, which *)
(* are usually full of existentials *)
Ltac vauto := (do ?econstructor=>//).
Ltac step := (apply: hstep=>/=).

Ltac hhauto := (vauto; try by [heap_congr])=>//.
Ltac heval := do ![step | by hhauto].

