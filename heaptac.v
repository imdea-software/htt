Require Import ssreflect ssrfun ssrnat div ssrbool seq path eqtype.
Require Import Eqdep pred idynamic ordtype pcm finmap unionmap heap. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 


(**************************************************************************)
(* Several tactics for canceling common terms in disjoint unions          *)
(* Currently, they don't deal with weak pointers. I.e.  they only if they *)
(* see iterms like x :-> v1 and x :-> v2, they will reduce to v1 = v2     *)
(* only if v1, v2 are of the same type A more general tactic would emit   *)
(* obligation dyn v1 = dyn v2, but I don't bother with this now.          *)
(**************************************************************************)

(* These are really brittle, but I didn't get around yet to substitute them *)
(* all with Mtacs or overloaded lemmas. So for now, let's stick with the hack *)
(* in order to support the legacy proofs *)

(* First cancelation in hypotheses *)

Section Cancellation.
Implicit Type (h : heap).

Lemma injUh A h1 h2 x (v1 v2 : A) : 
        valid (h1 \+ (x :-> v1)) -> 
        h1 \+ (x :-> v1) = h2 \+ (x :-> v2) -> 
          valid h1 /\ h1 = h2 /\ v1 = v2. 
Proof. by rewrite -!(joinC (x :-> _))=>D /(hcancelV D) [->]. Qed.  

Lemma eqUh h1 h2 h : 
        valid (h1 \+ h) -> h1 \+ h = h2 \+ h -> valid h1 /\ h1 = h2. 
Proof. by move=>D E; rewrite {2}(joinKf D E) (validL D). Qed.

Lemma exit1 h1 h2 h : valid (h1 \+ h) -> h1 \+ h = h \+ h2 -> valid h1 /\ h1 = h2.
Proof. by move=>D; rewrite (joinC h); apply: eqUh. Qed.

Lemma exit2 h1 h : valid (h1 \+ h) -> h1 \+ h = h -> valid h1 /\ h1 = Unit.
Proof. by move=>H1; rewrite -{2}(unitR h)=>H2; apply: exit1 H2. Qed.

Lemma exit3 h1 h : valid h -> h = h \+ h1 -> valid (Unit : heap) /\ Unit = h1.
Proof.
move=>H1 H2; split=>//; rewrite -{1}(unitR h) in H2.
by move/joinfK: H2; rewrite unitR; apply.
Qed.

Lemma exit4 h : valid h -> h = h -> valid (Unit : heap) /\ Unit = Unit :> heap. 
Proof. by []. Qed. 

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


Ltac cancelator t H :=
  match goal with 
  (* we exit when we hit the terminator on the left *)
  | |- ?h1 \+ t = ?h2 -> _ => 
     let j := fresh "j" in
     set j := {1}(h1 \+ t); 
     rewrite -1?joinA /j {j};
     (move/(exit1 H)=>{H} [H] || move/(exit2 H)=>{H} [H]) 
  | |- t = ?h2 -> _ => 
     rewrite -?joinA;
     (move/(exit3 H)=>{H} [H] || move/(exit4 H)=>{H} [H])
  | |- (?h1 \+ (?x :-> ?v) = ?h2) -> _ => 
    let j := fresh "j" in 
    set j := {1}(h1 \+ (x :-> v));
    (* if x appears in the second union, first bring it to the back *)
    rewrite 1?(joinC (x :-> _)) -?(joinAC _ _ (x :-> _)) /j {j}; 
    (* then one of the following must apply *)
    (* if x is in the second union then cancel *)
    (move/(injUh H)=>{H} [H []] ||
    (* if not, rotate x in the first union *)
     rewrite (joinC h1) ?joinA in H * );
    (* and proceed *)
    cancelator t H
  (* if the heap is not a points-to relation, also try to cancel *)
  | |- (?h1 \+ ?h = ?h2) -> _ => 
    let j := fresh "j" in 
    set j := {1}(h1 \+ h);
    (* if h appears in the second union, first bring it to the back *)
    rewrite 1?(joinC h) -?(joinAC _ _ h) /j {j}; 
    (* then one of the following must apply *)
    (* if h is in the second union then cancel *)
    (move/(eqUh H)=>{H} [H []] ||
    (* if not, rotate h in the first union *)
    rewrite (joinC h1) ?joinA in H * );
    (* and proceed *)
    cancelator t H
  | |- _ => idtac 
  end.


Ltac heap_cancel := 
  match goal with 
  | |- ?h1 = ?h2 -> ?GG =>
    let t1 := fresh "t1" in
    let t2 := fresh "t2" in 
    let t := fresh "t" in
    let H := fresh "H" in
    let G := fresh "hidden_goal"
    in
      (* generate the obligation to prove that the left heap is defined *)
      suff : valid h1; first (
       (* make sure no sharing of expressions in the goal *)
       set t1 := {1 2}h1; set t2 := {1}h2; set G := GG;
       (* introduce terminators *)
       rewrite -(unitL t1) -(unitL t2) [Unit]lock;
       set t := locked Unit; rewrite /t1 /t2 {t1 t2}; 
       move=>H; 
       (* flatten the goal *)
       rewrite ?joinA in H *; 
       (* call the cancelation routine *)
       cancelator t H; 
       (* remove the terminator and push H onto the goal *)
       move: H {t}; rewrite /G {G})
  | |- _ => idtac
  end.


(* Then cancelation in conclusions *)

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

Lemma test h1 h2 h3 x (v1 v2 : nat) : 
        h3 = h2 -> v1 = v2 -> 
        h1 \+ (x :-> v1) \+ h3= h2 \+ h1 \+ (x :-> v2).
Proof. by move=>H1 H2; heap_congr. Qed.



