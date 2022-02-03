From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl Require Import axioms pred prelude.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import model.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(**************************************************************************)
(* This file implements automations related to Hoare logic.               *)
(*                                                                        *)
(* First automation concerns selection of Hoare-style rule for symbolic   *)
(* evaluation. The first command of the program determines the applicable *)
(* rule uniquely. The implemented automation picks out this rule, and     *)
(* applies it, while using AC-theory of heaps to rearrange the goal, if   *)
(* necessary for the rule to apply.                                       *)
(*                                                                        *)
(* Second, a tactic for canceling common terms in disjoint unions         *)
(* Currently, it doesn't deal with weak pointers. I.e. only if it sees    *)
(* terms like x :-> v1 and x :-> v2, it will reduce to v1 = v2            *)
(* only if v1, v2 are of the same type. A more general tactic would emit  *)
(* obligation dyn v1 = dyn v2, but I don't bother with this now.          *)
(*                                                                        *)
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

(* an automated form of vrf_frame + gE *)
Lemma gR G A (s : spec G A) g i j (e : STspec G s)
          (f : forall k, form k j) (Q : post A) :
        (valid i -> (s g).1 i) ->
        (forall x m, (s g).2 (Val x) m ->
           valid (untag (f m)) -> Q (Val x) (f m)) ->
        (forall x m, (s g).2 (Exn x) m ->
           valid (untag (f m)) -> Q (Exn x) (f m)) ->
        vrf (f i) e Q.
Proof.
case: e=>e /= H H1 H2 H3; rewrite formE.
apply: vrfV=>/validL/H1/H V.
apply/vrf_frame/vrf_post/V.
by case=>[x|ex] m Vm =>[/H2|/H3]; rewrite formE.
Qed.

Arguments gR [G A s] g i [j e f Q] _ _ _.

Notation "[gR] @ i" := (gR tt i) (at level 0).

Notation "[ 'gR' x1 , .. , xn ] @ i" :=
  (gR (existT _ x1 .. (existT _ xn tt) ..) i)
  (at level 0, format "[ 'gR'  x1 ,  .. ,  xn ] @  i").

(* vrf_bind + gR *)
Lemma stepR G A B (s : spec G A) g i j (e : STspec G s) (e2 : A -> ST B)
             (f : forall k, form k j) (Q : post B) :
        (valid i -> (s g).1 i) ->
        (forall x m, (s g).2 (Val x) m -> vrf (f m) (e2 x) Q) ->
        (forall x m, (s g).2 (Exn x) m ->
           valid (untag (f m)) -> Q (Exn x) (f m)) ->
        vrf (f i) (bind e e2) Q.
Proof.
move=>Hi H1 H2.
apply/vrf_bind/(gR _ _ Hi)=>[x m H V|ex m H V _].
- by apply: H1 H.
by apply: H2.
Qed.

Arguments stepR [G A B s] g i [j e e2 f Q] _ _ _.

Notation "[stepR] @ i" := (stepR tt i) (at level 0).

Notation "[ 'stepR' x1 , .. , xn ] @ i" :=
  (stepR (existT _ x1 .. (existT _ xn tt) ..) i)
  (at level 0, format "[ 'stepR'  x1 ,  .. ,  xn ] @  i").

(* vrf_try + gR *)
Lemma tryR G A B (s : spec G A) g i j (e : STspec G s) (e1 : A -> ST B) (e2 : exn -> ST B)
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

Arguments tryR [G A B s] g i [j e e1 e2 f Q] _ _ _.

Notation "[tryR] @ i" := (tryR tt i) (at level 0).

Notation "[ 'tryR' x1 , .. , xn ] @ i" :=
  (tryR (existT _ x1 .. (existT _ xn tt) ..) i)
  (at level 0, format "[ 'tryR'  x1 ,  .. ,  xn ] @  i").

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
        vrf f (read x) r.
Proof. by rewrite formE; apply: vrf_read. Qed.

Lemma try_readR e1 e2 v x i (f : form (x :-> v) i) (r : post B) :
        vrf f (e1 v) r ->
        vrf f (try (@read A x) e1 e2) r.
Proof. by move=>H; apply/vrf_try/val_readR. Qed.

Lemma bnd_readR e v x i (f : form (x :-> v) i) (r : post B) :
        vrf f (e v) r ->
        vrf f (bind (@read A x) e) r.
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
        vrf i (try (@throw A e) e1 e2) r.
Proof. by move=>H; apply/vrf_try/val_throwR. Qed.

Lemma bnd_throwR e e1 i (r : post B) :
        (valid i -> r (Exn e) i) ->
        vrf i (bind (@throw A e) e1) r.
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

(* This is really brittle, but I didn't get around yet to substitute it *)
(* with Mtac or overloaded lemmas. So for now, let's stick with the hack *)
(* in order to support the legacy proofs *)

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
