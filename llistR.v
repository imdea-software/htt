Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
Require Import pred pcm unionmap heap heaptac stmod stsep stlog stlogR. 
Set Implicit Arguments. 
Unset Strict Implicit. 
Set Automatic Coercions Import.
Unset Printing Implicit Defensive. 

(* linked lists, storing a value and next pointer in consecutive locations *)

Definition llist (T : Type) := ptr.
 
Section LList.
Variable T : Type.
Notation llist := (llist T).

Fixpoint lseg (p q : ptr) (xs : seq T) := 
  if xs is x::xt then 
    [Pred h | exists r h', 
       h = p :-> x \+ (p .+ 1 :-> r \+ h') /\ h' \In lseg r q xt]
  else [Pred h | p = q /\ h = Unit].

Lemma lseg_add_last xs x p r h : 
        h \In lseg p r (rcons xs x) <->
        exists q h', h = h' \+ (q :-> x \+ q .+ 1 :-> r) /\ h' \In lseg p q xs.
Proof.
move: xs x p r h; elim=>[|x xs IH] y p r h /=.
- by split; case=>x [h'][->][<- ->]; [exists p | exists r]; hhauto. 
split.
- case=>z [h1][->]; case/IH=>w [h2][->] H1.
  by exists w, (p :-> x \+ (p .+ 1 :-> z \+ h2)); hhauto. 
case=>q [h1][->][z][h2][->] H1.
exists z, (h2 \+ q :-> y \+ q .+ 1 :-> r).
by rewrite -!joinA; split=>//; apply/IH; eauto.
Qed.

Lemma lseg_null xs q h : 
         valid h -> h \In lseg null q xs -> 
         [/\ q = null, xs = [::] & h = Unit].
Proof.
case: xs=>[|x xs] D /= H; first by case: H=><- ->.
by case: H D=>r [h'][->] _; rewrite hvalidPtUn eq_refl.
Qed. 

Lemma lseg_neq xs p q h : 
        p != q -> h \In lseg p q xs -> 
        exists x r h', 
         [/\ xs = x :: behead xs, p :-> x \+ (p .+ 1 :-> r \+ h') = h & 
             h' \In lseg r q (behead xs)].
Proof.
case: xs=>[|x xs] /= H []; last by move=>y [h'][->] H1; hhauto.
by move=>E; rewrite E eq_refl in H.
Qed.

Lemma lseg_empty xs p q : Unit \In lseg p q xs -> p = q /\ xs = [::].
Proof. 
by case: xs=>[|x xs][] // r [h][/esym/join0E][/empbE]; rewrite gen_empbPt. 
Qed.

Lemma lseg_case xs p q h : 
        h \In lseg p q xs -> 
        [/\ p = q, xs = [::] & h = Unit] \/
        exists x r h',
          [/\ xs = x :: behead xs, h = p :-> x \+ (p .+ 1 :-> r \+ h') & 
              h' \In lseg r q (behead xs)].
Proof.
case: xs=>[|x xs] /=; first by case=>->->; left.
by case=>r [h'][->] H; right; hhauto. 
Qed.

(* Special case when p = null *)
Definition lseq p := lseg p null.

Lemma lseq_null xs h : valid h -> h \In lseq null xs -> xs = [::] /\ h = Unit.
Proof. by move=>D; case/(lseg_null D)=>_ ->. Qed.

Lemma lseq_pos xs p h : 
        p != null -> h \In lseq p xs -> 
        exists x, exists r, exists h', 
          [/\ xs = x :: behead xs, 
              p :-> x \+ (p .+ 1 :-> r \+ h') = h & h' \In lseq r (behead xs)].
Proof. by apply: lseg_neq. Qed.

(* main methods *)

Program 
Definition insert p x : 
  {xs}, STsep (fun i => i \In lseq p xs, 
               fun y m => exists q, m \In lseq q (x::xs) /\ y = Val q) :=
  Do (q <-- allocb p 2; 
      q ::= x;;
      ret q). 
Next Obligation.
by apply: ghE=>// i xs H _ _; step=>q; rewrite unitR -joinA; heval.
Qed.

Program 
Definition remove p : 
  {xs}, STsep (fun i => i \In lseq p xs,
               fun y m => exists q, m \In lseq q (behead xs) /\ y = Val q) :=
  Do (if p == null then ret p 
      else pnext <-- !(p .+ 1);
           dealloc p;; 
           dealloc p .+ 1;;
           ret pnext). 
Next Obligation.
apply: ghE=>// i xs H _ D.
case: ifP H=>H1; first by rewrite (eqP H1); case/(lseq_null D)=>->->; heval. 
case/(lseq_pos (negbT H1))=>x [q][h][->] <- /= H2.
by heval; rewrite 2!unitL; vauto.
Qed.

Definition shape_rev p s := [Pred h | h \In lseq p.1 s.1 # lseq p.2 s.2].


(* hmm, this is a tail recursive program; probably could shave off a few lines
   of proof, if revT is exactly the same as the spec of reverse p *)

Definition revT : Type := 
  forall p, {ps}, STsep (fun i => i \In shape_rev p ps,
                         fun y m => exists r, m \In lseq r (rev ps.1 ++ ps.2) /\
                                              y = Val r). 

Program 
Definition reverse p : 
  {xs}, STsep (fun i => i \In lseq p xs, 
               fun y m => exists q, m \In lseq q (rev xs) /\ y = Val q) :=        
  Do (let: reverse := Fix (fun (reverse : revT) p => 
                        Do (if p.1 == null then ret p.2 
                            else xnext <-- !p.1 .+ 1;
                                 p.1 .+ 1 ::= p.2;;
                                 reverse (xnext, p.1)))
      in reverse (p, null)).
Next Obligation. 
apply: ghE=>// i [x1 x2][i1][i2][->] /= [H1 H2] _ D; case: eqP H1=>[->|E].
- by case/(lseq_null (validL D))=>->->; rewrite unitL; heval. 
case/lseq_pos=>[|xd [xn][h'][->] <- /= H1]; first by case: eqP.
do !step; rewrite -!joinA -!(joinCA h').
apply: (gh_inst (behead x1, xd::x2)).
apply: val_doR; first by vauto.
- by move=>x m [r][/=]; rewrite rev_cons cat_rcons=>H [->] _; vauto.
by move=>e m [r][_].
Qed.
Next Obligation.
apply: ghE=>// i xs H _ _; apply: (gh_inst (xs, Nil T)).
apply: val_do0=>//; first by exists i; hhauto. 
- by move=>x m [r][/= H1][->] _; rewrite cats0 in H1 *; vauto. 
by move=>e m [r][_].
Qed.

End LList. 


