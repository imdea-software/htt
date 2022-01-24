From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype tuple finfun finset.
From fcsl Require Import axioms prelude pred ordtype finmap.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import domain heap_extra model heapauto.
From HTT Require Import array kvmaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

Module HashTab.
Section HashTab.
Import FinIter.
Variables (K : ordType) (V : Type) (buckets : KVmap.Sig K V)
          (n : nat) (hash : K -> 'I_n).
Definition hashtab := {array 'I_n -> KVmap.tp buckets}.
Notation KVshape := (@KVmap.shape _ _ buckets).
Notation table := (table KVshape).

(* TODO is there another way to prevent unfolding these? *)
Opaque Array.write Array.new Array.free Array.read.

Definition shape x s :=
  [Pred h | exists tab bucket,
           [/\ forall k, fnd k s = fnd k (bucket (hash k)),
               forall i k, k \in supp (bucket i) -> hash k = i &
               h \In Array.shape x tab # sepit setT (table tab bucket)] ].

Definition new_loopinv x := forall k,
  STsep (fun h => k <= n /\ exists tab,
           h \In Array.shape x tab #
                   sepit [set x:'I_n | x < k] (table tab (fun => nil K V)),
         [vfun y => shape y (nil K V)]).

Program Definition new : STsep (emp, [vfun y => shape y (nil K V)]) :=
  Do (t <-- Array.new _ (KVmap.default buckets);
      Fix (fun (loop : new_loopinv t) k =>
           Do (if decP (b := k < n) idP is left pf then
                 b <-- KVmap.new buckets;
                 Array.write t (Ordinal pf) b;;
                 loop k.+1
               else ret t)) 0).
Next Obligation.
move=>/= arr loop k [] _ /= [Eleq][tab][h1][h2][-> H1]; case: decP; last first.
- case: ltnP Eleq (eqn_leq k n)=>// _ -> /= /eqP Ek _ H.
  step=>_.
  exists tab, (fun _:'I_n => nil K V); split=>//; exists h1, h2; do!split=>//.
  apply/tableP2: H=>//= x.
  by rewrite Ek !in_set ltn_ord.
move=>Ho H2; rewrite -[h1 \+ h2]unitL.
apply/[stepR] @ Unit=>//= b m Hm _.
apply/[stepR tab] @ h1=>{H1}//= [[]] m2 [E2 V2] _.
apply/[gE]=>//=; split=>//; rewrite joinCA.
exists [ffun z => if z == Ordinal Ho then b else tab z], m2, (m \+ h2); split=>//.
rewrite (sepitS (Ordinal Ho)) in_set leqnn {1}/table ffunE eq_refl.
exists m, h2; do!split=>//.
apply: tableP2 H2=>//.
- by case=>x ?; rewrite !in_set -val_eqE /= ltnS (leq_eqVlt x); case: ltngtP.
by move=>x _; rewrite in_set ffunE; case: eqP=>//->; rewrite ltnn.
Qed.
Next Obligation.
move=>/= [] ? ->.
apply: [stepE]=>//=; case=>//= y m _ [H Vm].
apply: [gE]=>//=; split=>//.
exists [ffun => KVmap.default buckets], m, Unit.
do!split=>//=; first by rewrite unitR.
by rewrite (eq_sepit (s2 := set0)) // sepit0.
Qed.

Definition free_loopinv x := forall k,
  STsep (fun h => k <= n /\ exists t b,
          h \In Array.shape x t #
                  sepit [set x:'I_n | x >= k] (table t b),
         [vfun _ : unit => emp]).

Program Definition free x : {s}, STsep (shape x s,
                                        [vfun _ : unit => emp]) :=
  Do (Fix (fun (loop : free_loopinv x) k =>
          Do (if decP (b := k < n) idP is left pf then
                b <-- Array.read x (Ordinal pf);
                KVmap.free b;;
                loop k.+1
               else Array.free x)) 0).
Next Obligation.
move=>/= x loop k [] _ /= [Eleq][tf][bf][h1][h2][-> [H1 H2]]; case: decP; last first.
- case: ltnP Eleq (eqn_leq k n)=>// _ -> /= /eqP Ek _ H.
  apply: [gE]=>//=; exists tf; move: H.
  rewrite (eq_sepit (s2 := set0)); first by rewrite sepit0=>->; rewrite unitR.
  by move=>y; rewrite Ek in_set in_set0 leqNgt ltn_ord.
move=>pf H; apply/[stepR tf, h1] @ h1=>//= _ _ [->->] _.
move: H; rewrite (sepitS (Ordinal pf)) in_set leqnn /table.
case=>h3[h4][{h2}-> H3 H4].
apply/[stepR (bf (Ordinal pf))] @ h3=>//= [[]] _ -> _; rewrite unitL.
apply: [gE]=>//=; split=>//; exists tf, bf, h1, h4; split=>//.
apply/tableP2/H4=>//.
move=>z; rewrite !in_set; case: eqP=>/=.
- by move=>->/=; rewrite ltnn.
by move/eqP; rewrite -val_eqE /=; case: ltngtP.
Qed.
Next Obligation.
move=>/= x [fm][] h /= [tf][bf][_ _ H].
apply: [gE]=>//=; split=>//.
by exists tf, bf.
Qed.

Program Definition insert x k v : {s}, STsep (shape x s,
                                              [vfun y => shape y (ins k v s)]) :=
  Do (let hk := hash k in
      b  <-- Array.read x hk;
      b' <-- KVmap.insert b k v;
      Array.write x hk b';;
      ret x).
Next Obligation.
move=>/= x k v [fm][] _ /= [tf][bf][Hf Hh [h1][h2][-> [/= H1 _] H2]].
apply/[stepR tf, h1] @ h1=>//= _ _ [->->] _.
move: H2; rewrite (sepitT1 (hash k)) /table; case=>h3[h4][{h2}-> H3 H4].
apply/[stepR (bf (hash k))] @ h3=>//= b' m2 H' _.
apply/[stepR tf] @ h1=>{H1}//= [[]] m3 [E3 V3] _.
step=>_.
exists [ffun z => if z == hash k then b' else tf z],
       (fun b => if b == hash k then ins k v (bf b) else bf b); split=>/=.
- move=>k0; rewrite fnd_ins; case: eqP.
  - by move=>->; rewrite eq_refl fnd_ins eq_refl.
  move/eqP=>Ek; case: ifP=>? //.
  by rewrite fnd_ins (negbTE Ek).
- move=>i0 k0; case: eqP; last by move=>_; apply: Hh.
  by move=>->; rewrite supp_ins inE=>/orP; case; [move/eqP=>->|apply: Hh].
exists m3, (m2 \+ h4); do!split=>//.
rewrite (sepitT1 (hash k)) /table /= ffunE eq_refl.
exists m2, h4; do!split=>//.
by apply/tableP/H4=>/= x0; rewrite !in_set andbT ?ffunE; move/negbTE=>->.
Qed.

Program Definition remove x k :
  {s}, STsep (shape x s,
             [vfun y => shape y (rem k s)]) :=
  Do (let hk := hash k in
      b  <-- Array.read x hk;
      b' <-- KVmap.remove b k;
      Array.write x hk b';;
      ret x).
Next Obligation.
move=>/= x k [fm][] _ /= [tf][bf][Hf Hh [h1][h2][-> [/= H1 _] H2]].
apply/[stepR tf, h1] @ h1=>//= _ _ [->->] _.
move: H2; rewrite (sepitT1 (hash k)) /table; case=>h3[h4][{h2}-> H3 H4].
apply/[stepR (bf (hash k))] @ h3=>//= b' m2 H' _.
apply/[stepR tf] @ h1=>{H1}//= [[]] m3 [E3 V3] _.
step=>_.
exists [ffun z => if z == hash k then b' else tf z],
       (fun b => if b == hash k then rem k (bf b) else bf b); split=>/=.
- move=>k0; rewrite fnd_rem; case: eqP.
  - by move=>->; rewrite eq_refl fnd_rem eq_refl.
  move/eqP=>Ek; case: ifP=>? //.
  by rewrite fnd_rem (negbTE Ek).
- move=>i0 k0; case: eqP; last by move=>_; apply: Hh.
  by move=>->; rewrite supp_rem !inE=>/andP [] _; apply: Hh.
exists m3, (m2\+ h4); do!split=>//.
rewrite (sepitT1 (hash k)) /table /= ffunE eq_refl.
exists m2, h4; do!split=>//.
by apply/tableP/H4=>/= x0; rewrite !in_set andbT ?ffunE; move/negbTE=>->.
Qed.

Program Definition lookup x k :
  {s}, STsep (shape x s,
             [vfun y m => m \In shape x s /\ y = fnd k s]) :=
  Do (b <-- Array.read x (hash k);
      KVmap.lookup b k).
Next Obligation.
move=>/= x k [fm][] _ /= [tf][bf][Hf Hh [h1][h2][-> H1 H2]].
apply/[stepR tf, h1] @ h1=>//= _ _ [->->] _.
move: H2; rewrite (sepitT1 (hash k)) /table; case=>h3[h4][{h2}-> H3 H4].
apply/[gR (bf (hash k))] @ h3=>//= r m2 [H2 Hr] _; split; last by rewrite Hf.
exists tf, bf; split=>//=; exists h1, (m2 \+ h4); split=>//.
by rewrite (sepitT1 (hash k)) /table; exists m2, h4.
Qed.

Definition HashTab := KVmap.make (Array null) new free insert remove lookup.

End HashTab.
End HashTab.

Definition HT K V := HashTab.HashTab (AssocList.AssocList K V).