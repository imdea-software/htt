From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl Require Import pred.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import heap_extra domain model.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
Lemma val_do' A (e : ST A) i j (Q : post A) :
        (valid i -> pre_of e i) ->
        (forall x m, exists (pf : )
                     prog_of e (single (bound (Val x))) i m ->
                       valid (m \+ j) -> Q (Val x) (m \+ j)) ->
        (forall x m, prog_of e (Exn x) i m ->
                       valid (m \+ j) -> Q (Exn x) (m \+ j)) ->
        vrf (i \+ j) e Q.
Proof.
move=>H1 H2 H3; apply: frame; apply: frame0=>D; split; first by apply: H1.
by case=>x m H4 D1 D2; [apply: H2 | apply: H3].
Qed.
*)
Lemma val_ret A v i (Q : post A) :
       (valid i -> Q (Val v) i) -> vrf i (Model.ret v) Q.
Proof. by move=>H; apply: Model.vrfV=>Vi; apply/Model.vrf_ret/H. Qed.
(*
Lemma val_read A v x i (Q : post A) :
        (valid (x :-> v \+ i) -> Q (Val v) (x :-> v \+ i)) ->
        vrf (x :-> v \+ i) (Model.read A x) Q.
Proof. by exact: Model.vrf_read. Qed.

Lemma val_write A B (v : A) (w : B) x i (Q : post unit) :
        (valid (x :-> v \+ i) -> Q (Val tt) (x :-> v \+ i)) ->
        vrf (x :-> w \+ i) (Model.write x v) Q.
Proof. by exact: Model.vrf_write. Qed.

Lemma val_alloc A (v : A) i (Q : post ptr) :
        (forall x, valid (x :-> v \+ i) -> Q (Val x) (x :-> v \+ i)) ->
        vrf i (Model.alloc v) Q.
Proof. by exact: Model.vrf_alloc. Qed.

Lemma val_allocb A (v : A) n i (Q : post ptr) :
        (forall x, valid (updi x (nseq n v) \+ i) ->
           Q (Val x) (updi x (nseq n v) \+ i)) ->
        vrf i (Model.allocb v n) Q.
Proof. by exact: Model.vrf_allocb. Qed.
*)
Lemma val_dealloc A (v : A) x i (Q : post unit) :
        (valid i -> Q (Val tt) i) ->
        vrf (x :-> v \+ i) (Model.dealloc x) Q.
Proof. by move=>H; apply: Model.vrf_dealloc=>_. Qed.

Lemma val_throw A x i (Q : post A) :
        (valid i -> Q (Exn x) i) -> vrf i (Model.throw A x) Q.
Proof. by move=>H; apply: Model.vrfV=>Vi; apply/Model.vrf_throw/H. Qed.

(* sequential composition: try e e1 e2 or bind e1 e2 can be reduced to *)
(* a vrf e1 followed by vrf of the postinuations. *)

(*
Lemma try_seq A B e (e1 : A -> ST B) e2 i (Q : post B) :
        vrf i e (fun y m =>
          match y with
            Val x => vrf m (e1 x) Q
          | Exn x => vrf m (e2 x) Q
          end) ->
        vrf i (Model.try e e1 e2) Q.
Proof. by exact: Model.vrf_try. Qed.
*)
Lemma bnd_seq A B e1 (e2 : A -> ST B) i (Q : post B) :
        vrf i e1 (fun y m =>
          match y with
            Val x => vrf m (e2 x) Q
          | Exn x => valid m -> Q (Exn x) m
          end) ->
        vrf i (Model.bind e1 e2) Q.
Proof.
move=>H; apply/Model.vrf_bind/Model.vrf_post/H.
by case=>[x|ex] m Vm //; apply.
Qed.


(*
Lemma gE G A (pq : spec G A) (c : STspec (logvar pq)) (g : G) (Q : post A) s :
        (pq g).1 s ->
        (forall v m, (pq g).2 v m -> coh V m -> Q v m) ->
        vrf c Q s.
Proof. by move=>X Y; apply: (gM g)=>// + + + + _. Qed.
(*
Lemma ghR A e rT p q (f : @gh_form A rT p q) :
        (forall i x, p x i -> valid i -> vrf i e (q x)) ->
        conseq e f.
*)

Lemma gh_conseq A C t (s : C -> spec A) (e : STbin (logvar s)) :
        conseq e (s t).
Proof.
case E: (s t)=>[a b] /= h H; rewrite -[h]unitR.
apply: val_do'=>[|x m|x m]; try by move/(_ t); rewrite E !unitR.
by exists t; rewrite E.
Qed.

(* a lemma for instantiating a ghost *)

Lemma gh_ex A C (t : C) i (s : C -> spec A) e (Q : post A) :
        vrf i (do' (gh_conseq (t:=t) e)) Q ->
        vrf i (with_spec (logvar s) e) Q.
Proof.
move=>H /H /=; case E: (s t)=>[a b] /= [H1 H2]; split=>[|y m].
- case: H1=>h1 [h2][->][T1 T2].
  by exists h1, h2; do !split=>//; exists t; rewrite E.
move=>H3; apply: H2=>h1 h2 E1 Vi E2.
have: exists x, let '(p, _) := s x in p h1.
- by exists t; rewrite E.
case/(H3 _ _ E1 Vi)=>m1 [->][Vm] /(_ t).
by rewrite E; exists m1.
Qed.

Arguments gh_ex [A C] t [i s e Q].


(* Two val_do lemmas which simplify binary posts *)
(* The first lemma applies framing as well; the second is frameless *)
(* We shoudn't need bnd_do or ttry_do, as these can be obtained *)
(* by first calling vrf_seq *)

Section ValDoLemmas.
Variables (A B : Type) (p : Pred heap) (q : ans A -> Pred heap).

Lemma val_do i j {e} (Q : post A) :
        (valid i -> i \In p) ->
        (forall x m, q (Val x) m -> valid (m \+ j) -> Q (Val x) (m \+ j)) ->
        (forall x m, q (Exn x) m -> valid (m \+ j) -> Q (Exn x) (m \+ j)) ->
        vrf (i \+ j) (with_spec (binarify p q) e) Q.
Proof.
move=>H1 H2 H3 V; apply: val_do' (V)=>//=;
move=>x m /(_ (H1 (validL V))); [apply: H2 | apply: H3].
Qed.

Lemma val_do0 i {e} (Q : post A) :
        (valid i -> i \In p) ->
        (forall x m, q (Val x) m -> valid m -> Q (Val x) m) ->
        (forall x m, q (Exn x) m -> valid m -> Q (Exn x) m) ->
        vrf i (with_spec (binarify p q) e) Q.
Proof.
move=>H1 H2 H3; rewrite -[i]unitR; apply: val_do=>// x m;
by rewrite unitR; eauto.
Qed.

End ValDoLemmas.


(******************************************)
(* Lemmas for pulling out ghost variables *)
(******************************************)

Section Ghosts.
Variables (A B C : Type) (e : ST A).

Lemma ghE (s : B -> C -> spec A) :
        conseq e (logvar (fun x => logvar (s x))) <->
        conseq e (logvar (fun xy => s xy.1 xy.2)).
Proof.
split.
- move=>/= H1 i [[x y]] H2.
  have: exists x1 y1, let '(p, _) := s x1 y1 in p i by exists x, y.
  by move/H1; apply: vrf_mono=>y1 m1 T1 [x2 y2]; apply: (T1 x2 y2).
move=>/= H1 i [x][y] H2.
have: exists x, let '(p, _) := s x.1 x.2 in p i by exists (x, y).
by move/H1; apply: vrf_mono=>y1 m1 T1 x2 y2; apply: (T1 (x2, y2)).
Qed.

Lemma gh (p : B -> pre) (q : B -> ans A -> pre) :
        (forall i x, p x i -> valid i -> vrf i e (q x)) ->
        conseq e (logvar (fun x => logbase (p x) (q x))).
Proof.
move=>H1 i /= [x] H2 V; case: (H1 _ _ H2 V V)=>H3 _.
by split=>// y m H5 H6 z H7; case: (H1  _ _ H7 V V)=>_; apply.
Qed.

End Ghosts.

(* some additional stuff *)

Definition pull (A : Type) x (v:A) := (joinC (x :-> v), joinCA (x :-> v)).
Definition push (A : Type) x (v:A) := (joinCA (x :-> v), joinC (x :-> v)).
*)
