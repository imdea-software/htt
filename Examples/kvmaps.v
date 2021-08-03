(******************)
(* Key-Value maps *)
(******************)

From Coq Require Import Program.Wf ssrfun.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype tuple finfun path.
From fcsl Require Import axioms pred ordtype finmap.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import domain stmod stsep stlog stlogR.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

(********************)
(* stateful KV maps *)
(********************)

Module KVmap.
Record Sig (K : ordType) (V : Type) : Type :=
  make {tp :> Type;
        default : tp;
        shape : tp -> {finMap K -> V} -> Pred heap;
        shapeD : forall x s h, h \In shape x s -> valid h;
        shape_invert : forall x s1 s2 h, valid h -> h \In shape x s1 -> h \In shape x s2 -> s1 = s2;

        new : STsep (emp, [vfun x => shape x (nil K V)]);

        free : forall x, {s}, STsep (shape x s,
                                     [vfun _ : unit => emp]);

        insert : forall x k v,
                   {s}, STsep (shape x s,
                               [vfun _ : unit => shape x (ins k v s)]);

        remove : forall x k,
                   {s}, STsep (shape x s,
                               [vfun y => shape y (rem k s)]);

        lookup : forall x k,
                   {s}, STsep (shape x s,
                               [vfun y m => m \In shape x s /\ y = fnd k s])}.
End KVmap.

(**************************************************)
(* KVmap implemented as a sorted association list *)
(**************************************************)

Module AssocList.
Section AssocList.

Variable (K : ordType) (V : Set).
Notation fmap := (finMap K V).
Notation nil := (nil K V).

(* TODO this should be expressible directly *)
Lemma path_relax (k k' : K) ks : ord k k' -> path ord k' ks -> path ord k ks.
Proof.
move=>O; case: ks=>//= a l /andP [O2 P2].
apply/andP; split=>//.
by apply/trans/O2.
Qed.

(* Data is stored in a sorted associative linked list. *)

Definition entry (p q : ptr) (k : K) (v : V) : heap := p :-> k \+ (p .+ 1 :-> v \+ p .+ 2 :-> q).

Fixpoint shape_seg' (x y : ptr) (xs : seq (K * V)) : Pred heap :=
  match xs with
    | (k,v)::tl =>
       fun h => exists (q : ptr) (h' : heap),
       h = x :-> k \+ (x .+ 1 :-> v \+ (x .+ 2 :-> q \+ h'))
        /\
       h' \In shape_seg' q y tl
    | [::] => [Pred h | x = y /\ h = Unit]
  end.

Definition shape_seg (x y : ptr) (s : finMap K V) : Pred heap :=
  shape_seg' x y (seq_of s).

Definition shape' (x : ptr) (xs : seq (K * V)) : Pred heap :=
  shape_seg' x null xs.

Definition shape (x : ptr) (s : finMap K V) : Pred heap :=
  shape_seg x null s.

Lemma shape_null (s : fmap) h : valid h -> h \In shape null s -> s = nil /\ h = Unit.
Proof.
move=>D; case: s=>xs srt /=.
case: xs srt=>/=.
- by move=>? [_ ->] //; rewrite fmapE.
move=>[??]??[?][?][H].
by rewrite H validPtUn in D.
Qed.

Lemma shape_cont (s : fmap) p h :
        p != null -> h \In shape p s ->
        exists k v q h',
         [/\ s = ins k v (behd s),
             path ord k (supp (behd s)),
             h = p :-> k \+ (p .+ 1 :-> v \+ (p .+ 2 :-> q \+ h'))
           & h' \In shape q (behd s)].
Proof.
move=>E; case: s=>xs srt /=.
elim: xs srt=>/=.
- by move=>? [E0]; rewrite E0 in E.
move=>[k v] /= l IH srt [q][h'][-> H].
exists k,v,q,h'; split=>//.
by rewrite fmapE /=; apply/esym/last_ins'.
Qed.

Lemma shape_cons (s : fmap) p q h k v :
   path ord k (supp s) -> h \In shape q s ->
   (p :-> k \+ (p .+ 1 :-> v \+ (p .+ 2 :-> q \+ h))) \In shape p (ins k v s).
Proof.
move=>S H.
suff: ins k v s = @FinMap _ _ ((k,v)::seq_of s) S by move=>->; exists q,h.
rewrite fmapE /=; case: s {H}S=>/=xs ??.
by rewrite last_ins'.
Qed.

Lemma shape_seg_rcons (s : fmap) x p q h k v :
   (forall k0, k0 \in supp s -> ord k0 k) -> h \In shape_seg x p s ->
   (h \+ entry p q k v) \In shape_seg x q (ins k v s).
Proof.
case: s=>xs srt O H. elim: xs h x srt O H =>/=.
- move=>??? S [->->]; rewrite unitL.
  by exists q, Unit; rewrite unitR.
move=>[k' v'] /= xs IH h x S O H.
rewrite /shape_seg /= in IH H *.
have O' : ord k' k by apply: O; rewrite inE eq_refl.
move/nsym/negP/negbTE: (O')=>->.
case E: (k==k')=>/=; first by move: O'; move/eqP: E=>->; move: (irr k')=>->.
case: H=>x0[h'][-> H'].
exists x0, (h' \+ (p :-> k \+ (p .+ 1 :-> v \+ p .+ 2 :-> q))); rewrite -!joinA; split=>//.
apply: IH=>//; first by apply: (path_sorted S).
move=>S0 k0 H0; apply: O.
by rewrite inE /=; apply/orP; right.
Qed.

Lemma shape_fcat s1 s2 h1 h2 x y :
  (forall k0, k0 \in supp s1 -> path ord k0 (supp s2)) ->
  h1 \In shape_seg x y s1 -> h2 \In shape y s2 ->
  (h1 \+ h2) \In shape x (fcat s1 s2).
Proof.
move=>O1 H1.
case: s2 O1=>xs; elim: xs h1 y h2 s1 H1 =>/=.
- by move=>???? H1 ?? [Eq ->]; rewrite Eq in H1; rewrite unitR.
move=>[k' v'] xs; rewrite /fcat /= => IH /= h1 y h2 s1 H1 srt O2 H2.
rewrite /shape /shape_seg /= in H2.
case: H2=>z[h'][-> H']; rewrite !joinA.
apply: IH; first 1 last.
- by apply/path_sorted/srt.
- move=>H0 k0; rewrite supp_ins !inE => /orP; case.
  - by move/eqP=>->.
  by move/O2=>/andP []; apply: path_relax.
- by move=>?; rewrite /shape /shape_seg /=; apply: H'.
rewrite -!joinA; apply shape_seg_rcons=>//.
by move=>k0 /O2 /andP [].
Qed.

(* main procedures *)

Program Definition new : STsep (emp, [vfun x => shape x nil]) :=
  Do (ret null).
Next Obligation. by move=>/= ?->; step. Qed.

Definition freeT : Type :=
  forall p, {fm}, STsep (shape p fm, [vfun _ : unit => emp]).

Program Definition free : freeT :=
 Fix (fun (go : freeT) p =>
      Do (if p == null then ret tt
          else pnext <-- !(p .+ 2);
               dealloc p;;
               dealloc (p .+ 1);;
               dealloc (p .+ 2);;
               go pnext)).
Next Obligation.
move=>go p; apply: ghR=>i s H D.
case: eqP.
- move=>E; step=>_; rewrite E in H.
  by case: (shape_null D H).
move/eqP=>E; case: (shape_cont E H)=>k[v][q][h'][_ _ -> H2].
do 4!step; rewrite !unitL.
by apply/(gh_ex (behd s))/val_doR.
Qed.

Definition lookupT k : Type :=
  forall p, {fm}, STsep (shape p fm, [vfun y m => m \In shape p fm /\ y = fnd k fm]).

Program Definition lookup (k : K) : lookupT k :=
 Fix (fun (go : lookupT k) (p : ptr) =>
      Do (if p == null then ret None
          else
            k' <-- !p;
            if k == k'
              then v <-- !(p .+ 1);
                   ret (Some v)
              else if ord k' k
                then pnext <-- !(p .+ 2);
                     go pnext
                else ret None)).
Next Obligation.
move=>k go p; apply: ghR=>i s H D.
case: eqP.
- move=>E; step=>_; rewrite E in H.
  by case: (shape_null D H)=>->.
move/eqP=>E; case: (shape_cont E H)=>k'[v][q][h'][Es S' Ei H'].
rewrite {D}Ei in H *; step; case: eqP.
- move=>Ek; do 2!step.
  move=>_; split=>//.
  by rewrite Es fnd_ins Ek eq_refl.
move/eqP=>Ek; case: ifP=>Eo.
- step; rewrite !joinA joinC.
  apply/frame/(gh_ex (behd s))/val_doR=>//=.
  move=>x h'' [??] _ _; rewrite Es; split.
  - by rewrite joinC -!joinA; apply: shape_cons.
  by rewrite fnd_ins (negbTE Ek).
move: (semiconnex Ek); rewrite {}Eo orbC /= => Eo.
step=>_; split=>//.
apply/esym/fnd_supp.
rewrite Es supp_ins inE negb_or; apply/andP; split=>//.
by apply/notin_path/path_relax/S'.
Qed.

Definition removeT p k : Type :=
  forall (qr : ptr * ptr),
    {fm}, STsep (fun h => exists fm1 fm2 k' v',
                  [/\ fm = fcat (ins k' v' fm1) fm2,
                      k \notin supp fm1 /\ k != k',
                      (forall k1 : K, k1 \in supp fm1 -> ord k1 k') /\ path ord k' (supp fm2) &
                      h \In
                      (shape_seg p qr.1 fm1 #
                      (fun h => h = entry qr.1 qr.2 k' v') #
                      shape qr.2 fm2)],
                 [vfun _ : unit => shape p (rem k fm)]).

Program Definition remove x (k0 : K) : {fm}, STsep (shape x fm,
                                                   [vfun y => shape y (rem k0 fm)]) :=
  Do (let: rm := Fix (fun (go : removeT x k0) '(q,r) =>
                      Do (if r == null then ret tt
                          else k' <-- !r;
                               if k0 == k'
                                 then next <-- !(r .+ 2);
                                      dealloc r;;
                                      dealloc (r .+ 1);;
                                      dealloc (r .+ 2);;
                                      q .+ 2 ::= (next : ptr);;
                                      ret tt
                                 else if ord k' k0
                                      then next <-- !(r .+ 2);
                                           go (r, next)
                                      else ret tt))
      in
      if x == null then ret null
        else k' <-- !x;
             if k0 == k'
                then next <-- !(x .+ 2);
                     dealloc x;;
                     dealloc (x .+ 1);;
                     dealloc (x .+ 2);;
                     ret next
                else if ord k' k0
                     then next <-- !(x .+ 2);
                          rm (x, next);;
                          ret x
                     else ret x).
Next Obligation.
move=>x k0 go ? q r ?.
apply: ghR=>h fm [fm1][fm2][k][v][Ef [Nk Nk0][O1 O2]]/=[h1][h0][-> [H1 [h00][h2][{h0}-> [{h00}-> H2]]]] D.
case: eqP.
- move=>Er; step=>_.
  rewrite Er in H2; rewrite !joinA in D.
  rewrite Ef; case: (shape_null (validR D) H2)=>->->.
  rewrite fcats0 unitR rem_ins (negbTE Nk0) (rem_supp Nk) Er.
  by apply: shape_seg_rcons.
move/eqP=>Er; case: (shape_cont Er H2)=>k'[v'][s][h2'][Ef2 Pf Eh2 H2'].
rewrite {h2 D H2}Eh2 joinA joinC.
step; case: eqP.
- move=>Ek; do 4!step; rewrite !unitL; do 2!step.
  move=>D'.
  rewrite Ef Ef2 -fcat_srem; last by rewrite supp_ins inE negb_or; apply/andP.
  rewrite rem_ins {1}Ek eq_refl rem_supp; last by rewrite Ek; apply: notin_path.
  rewrite joinC; apply/shape_fcat/H2'; last by apply: shape_seg_rcons.
  move=>k1; rewrite Ef2 in O2; case/andP: (path_supp_ins_inv Pf O2)=>_ P'.
  rewrite supp_ins !inE=>/orP; case; first by move/eqP=>->.
  move/O1; move: P'=>/[swap]; apply: path_relax.
move/eqP=>Ek; case: ifP.
- move=>Ok; step.
  apply/(gh_ex (fcat (ins k' v' (ins k v fm1)) (behd fm2)))/val_doR=>//.
  - move=>D'; exists (ins k v fm1), (behd fm2), k', v'; do!split=>//.
    - by rewrite supp_ins inE negb_or; apply/andP.
    - move=>k1; rewrite Ef2 in O2; case/andP: (path_supp_ins_inv Pf O2)=>O' _.
      rewrite supp_ins inE => /orP; case; first by move/eqP=>->.
      by move/O1; move: O'=>/[swap]; apply: trans.
    exists (h1 \+ entry q r k v), (entry r s k' v' \+ h2').
    rewrite joinC !joinA; do!split=>//.
    - by rewrite -!joinA; apply: shape_seg_rcons.
    by exists (entry r s k' v'), h2'.
  move=>/= [] m Hm Dm; rewrite Ef Ef2.
  rewrite fcat_inss // in Hm; last first.
  - apply: notin_path; rewrite Ef2 /= in O2.
    by move: (path_supp_ins_inv Pf O2)=>/andP [].
  by rewrite -fcat_sins in Hm.
move=>Eo; move: (semiconnex Ek); rewrite {}Eo orbC /= => Eo.
step=>_; rewrite rem_supp Ef.
- rewrite joinC.
  apply: shape_fcat=>//.
  - move=>k1; rewrite supp_ins !inE=>/orP; case; first by move/eqP=>->.
    by move/O1; move: O2=>/[swap]; apply: path_relax.
  - by apply: shape_seg_rcons.
  by rewrite Ef2; apply: shape_cons.
rewrite Ef2 supp_fcat !inE negb_or; apply/andP; split;
rewrite supp_ins !inE negb_or; apply/andP; split=>//.
by apply/notin_path/path_relax/Pf.
Qed.
Next Obligation.
move=>/= x k0; apply: ghR=>h fm H D.
case: eqP.
- by move: H=>/[swap] -> /(shape_null D) [->->]; step=>_.
move/eqP=>Ex; case: (shape_cont Ex H)=>k[v][p][h'][Ef Of Eh H']; rewrite Eh.
step; case: eqP.
- move=>->; do 5!step; rewrite !unitL => D'.
  rewrite Ef rem_ins eq_refl rem_supp //.
  by apply: notin_path.
move/eqP=>Ek; case: ifP.
- move=>Ok; step.
  apply/bnd_seq/(gh_ex fm)/val_do0=>//=; last by move=>_ ???; step.
  move=>D'; exists nil, (behd fm), k, v; do!split=>//.
  - rewrite fcat_inss; last by apply: notin_path.
    by rewrite fcat0s.
  exists Unit, (entry x p k v \+ h'); do!split; first by rewrite /entry unitL !joinA.
  by exists (entry x p k v), h'.
move=>Eo; move: (semiconnex Ek); rewrite {}Eo orbC /= => Eo.
step=>D'.
rewrite -Eh rem_supp // Ef supp_ins !inE negb_or; apply/andP; split=>//.
by apply/notin_path/path_relax/Of.
Qed.

(*
Program Definition insert x k v : {s}, STsep (shape x s,
                                              [vfun _ : unit => shape x (ins k v s)]) :=
(*  STsep unit (fun i => exists s, i \In shape x s,
              fun y i m => forall s, i \In shape x s ->
                           m \In shape x (ins k v s) /\ y = Val tt) := *)
  Do (s <-- !x; x ::= ins k v s).
Next Obligation.
by apply: (ghost H) H0=>s; case/swp=>->; heval; split=>//; apply/swp.
Qed.



Definition AssocList := KVmap.make null shapeD shape_invert new free insert remove lookup.

*)
End AssocList.
End AssocList.
