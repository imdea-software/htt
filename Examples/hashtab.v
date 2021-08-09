From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype tuple finfun finset.
From fcsl Require Import axioms prelude pred ordtype finmap.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import domain stmod stsep stlog stlogR.
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

Definition shape x s :=
  [Pred h | exists tab bucket,
           [/\ forall k, fnd k s = fnd k (bucket (hash k)),
               forall i k, k \in supp (bucket i) -> hash k = i &
               h \In Array.shape x tab # sepit setT (table tab bucket)] ].

Definition new_loopinv x := forall k,
  STsep (fun h => k <= n /\ exists tab, h \In Array.shape x tab #
                   sepit [set x:'I_n | x < k] (table tab (fun x:'I_n => nil K V)),
         [vfun y => shape y (nil K V)]).

Program Definition new : STsep (emp, [vfun y => shape y (nil K V)]) :=
  Do (t <-- Array.new _ (KVmap.default buckets);
      Fix (fun (loop : new_loopinv t) k =>
           Do (match decP (b := k < n) idP with
               | left pf => b <-- KVmap.new buckets;
                            Array.write t (Ordinal pf) b;;
                            loop k.+1
               | _ => ret t end)) 0).
Next Obligation.
move=>/= arr loop k h /= [Eleq][tab][h1][h2][-> [H1 H2]]; case: decP; last first.
- move/negP=>Ho; rewrite leq_eqVlt (negbTE Ho) orbF in Eleq.
  step=>Vh [_ [tab2 H12]].
  exists tab, (fun _:'I_n => nil K V); split=>//; exists h1, h2; do!split=>//.
  apply: (tableP2 _ _ _ H2)=>// x; move/eqP: Eleq=>->.
  by rewrite !in_set ltn_ord.
move=>Ho; rewrite -[h1 \+ h2]unitL.
apply: bnd_seq; move=>/= Vs; split; first by exists Unit, (h1 \+ h2).
move=>y m Hm; case: (Hm Unit (h1 \+ h2))=>// m1 [-> [Vm1]] /[swap] _ {Hm}.
case: y=>/= b Hm; last by move=>_ _; apply: Hm.
apply: bnd_seq; move=>/= _; split.
- exists h1, (m1 \+ h2); do!split=>//; first by rewrite joinCA.
  by exists tab.
move=>y m0 Hm0; case: (Hm0 h1 (m1 \+ h2))=>//.
- by rewrite joinCA.
- by exists tab.
move=>m2 [->][Vm2] /[swap] _; move: Hm0.
case: y=>/=; last by move=>_ _ Hx _ _; apply: (Hx tab).
move=>[] _ /(_ tab); case=>// E2 V2.
apply/val_doR=>// _; split=>//.
exists [ffun z => if z == Ordinal Ho then b else tab z].
exists m2, (m1 \+ h2); do!split=>//.
rewrite (sepitS (Ordinal Ho)) in_set leqnn {1}/table ffunE eq_refl.
exists m1, h2; do!split=>//; first by apply: Hm.
apply: tableP2 H2=>//.
- by case=>x ?; rewrite !in_set -val_eqE /= ltnS (leq_eqVlt x); case: ltngtP.
by move=>x _; rewrite in_set ffunE; case: eqP=>//->; rewrite ltnn.
Qed.
Next Obligation.
move=>/= ? ->; apply: bnd_seq=>/= _ /=; split.
- by rewrite -[Unit]unitL; exists Unit, Unit.
move=>y m H Vm; case: y H=>/=; last first.
- move=>_ H _ _; case: (H Unit Unit)=>//; first by rewrite unitR.
  by move=>x [_ [_]]; apply.
move=>arr H; apply: val_do0=>// _; split=>//.
exists [ffun _ => KVmap.default buckets].
exists m, Unit; do!split=>//=.
- by rewrite unitR.
- case: (H Unit Unit)=>//; first by rewrite unitR.
  by move=>x [E [_ {}H]]; case: H=>//; rewrite E unitR.
by rewrite (eq_sepit (s2 := set0)) // sepit0.
Qed.

(*
Definition free_loopinv x := forall k,
  STsep unit (fun h => k <= n /\ exists t, exists b, h \In Array.shape x t #
                       sepit [set x:'I_n | x >= k] (table t b),
              fun y i m => y = Val tt /\ m = empty).

Program Definition free x : STsep unit (fun i => exists s, i \In shape x s,
                                        fun y i m => y = Val tt /\ m = empty) :=
  Do (Fix (fun (loop : free_loopinv x) k =>
             Do (Match_dec (dec (k < n))
                  (fun pf => b <-- Array.read x (Ordinal pf);
                             KVmap.free b;;
                             loop k.+1)
                  (fun _ => Array.free x))) 0).
Next Obligation.
move: i H0 H1 H2=>h t b [h1][h2][->][H1][]; case: dec=>[{H} pf H2|]; last first.
- case: ltnP H (eqn_leq k n)=>// _ -> /=; move/eqP=>-> _.
  rewrite (eq_sepit set0) ?sepit0; last by case=>y p; rewrite in_set inE leqNgt p.
  move=>->; rewrite unh0=>D; apply: cons0=>/=; eauto.
apply: bnd_gh (H1)=>[b' _ [[->]] <-|??[]] //; rewrite pf.
move: H2; rewrite (sepitS (Ordinal pf)) in_set leqnn /table.
move=>[h3][h4][->][H2][H3] _; rewrite unCA.
apply: bnd_do=>[|[]_[_]->|??[]] //=; first by eauto.
rewrite un0h=>D; apply: cons0=>//; split=>//; exists t; exists b; hauto D.
apply: tableP2 H3=>//; move=>[y qf]; rewrite !in_set -val_eqE /=.
by case: eqP=>[->|]; rewrite ?ltnn // leq_eqVlt; case: ltngtP=>// ->.
Qed.
Next Obligation.
by apply: cons0=>//=; [case: H0=>t [b][_][_]; eauto| apply: shapeD H0].
Qed.

Program
Definition insert x k v : STsep unit (fun i => exists s, i \In shape x s,
                                      fun y i m => forall s, i \In shape x s ->
                                        m \In shape x (ins k v s) /\ y = Val tt) :=
  Do (b <-- Array.read x (hash k);
      KVmap.insert b k v).
Next Obligation.
apply: (ghost H) H0=>s [t][b][H1][H2][h1][h2][->][H3][H4].
apply: bnd_gh (H3)=>[b' _ [[->]] <-|??[]] //; move: H4.
rewrite (sepitT1 (hash k)) /table=>[[h2']][h3][->][H4][H5] _; rewrite unCA.
apply: val_gh H4=>[[] h2'' [H4'] _ D|??[]] //; split=>//.
set b'' := [eta b with (hash k) |-> ins k v (b (hash k))].
exists t; exists (b'' : 'I_n -> {fmap K -> V}); do !split.
- move=>k'; rewrite /b'' /= fnd_ins.
  case: ifP=>T1; first by rewrite (eqP T1) eq_refl fnd_ins eq_refl.
  case: ifP=>T2 //; first by rewrite fnd_ins T1 -(eqP T2).
- move=>i' k'; rewrite /b'' /=; case: eqP=>[->|_]; last by apply: H2.
  by rewrite supp_ins inE /=; case: eqP=>[->|_] //=; last by apply: H2.
rewrite (sepitT1 (hash k)) unCA {1}/table /= eq_refl in D * => D; hauto D.
by apply: tableP H5=>// y; rewrite !in_set andbT /b'' /=; move/negbTE=>->.
Qed.

Program
Definition remove x k : STsep unit (fun i => exists s, i \In shape x s,
                                    fun y i m => forall s, i \In shape x s ->
                                      m \In shape x (rem k s) /\ y = Val tt) :=
  Do (b <-- Array.read x (hash k);
      KVmap.remove b k).
Next Obligation.
apply: (ghost H) H0=>s [t][b][H1][H2][h1][h2][->][H3][H4].
apply: bnd_gh (H3)=>[b' _ [[->]] <-|??[]] //; move: H4.
rewrite (sepitT1 (hash k)) /table=>[[h2']][h3][->][H4][H5] _; rewrite unCA.
apply: val_gh H4=>[[] h2'' [H4'] _ D|??[]] //; split=>//.
set b'' := [eta b with (hash k) |-> rem k (b (hash k))].
exists t; exists (b'' : 'I_n -> fmap K V); do !split.
- move=>k'; rewrite /b'' /= fnd_rem.
  case: ifP=>T1; first by rewrite (eqP T1) eq_refl fnd_rem eq_refl.
  case: ifP=>T2 //; first by rewrite fnd_rem T1 -(eqP T2).
- move=>i' k'; rewrite /b'' /=; case: eqP=>[->|_]; last by apply: H2.
  by rewrite supp_rem inE /=; case: eqP=>[->|_] //=; last by apply: H2.
rewrite (sepitT1 (hash k)) unCA {1}/table /= eq_refl in D * => D; hauto D.
by apply: tableP H5=>// y; rewrite !in_set andbT /b'' /=; move/negbTE=>->.
Qed.

Program Definition lookup x k :
  STsep (option V) (fun i => exists s, i \In shape x s,
                    fun y i m => forall s, i \In shape x s ->
                                   m \In shape x s /\ y = Val (fnd k s)) :=
  Do (b <-- Array.read x (hash k);
      KVmap.lookup b k).
Next Obligation.
apply: (ghost H) H0=>s [t][b][H1][H2][h1][h2][->][H3][H4].
apply: bnd_gh (H3)=>[b' _ [[->]] <-|??[]] //; move: H4.
rewrite (sepitT1 (hash k)) /table=>[[h2']][h3][->][H4][H5] _; rewrite unCA.
apply: val_gh H4=>[a h2'' [H4'] [->] {D} D|??[]] //; eauto; rewrite H1; split=>//.
exists t; exists b; do !split=>//.
by rewrite (sepitT1 (hash k)) unCA in D * => D; hauto D.
Qed.

Definition HashTab := KVmap.make (Array null) shapeD shape_invert new free insert remove lookup.
*)
End HashTab. End HashTab.

(*Definition HT K V := HashTab.HashTab (AssocList.AssocList K V).*)