From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq ssrnat.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap automap autopcm.
From HTT Require Import interlude model heapauto.
From HTT Require Import llist.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

(* a queue variant that has a fixed capacity and can overwrite data in a circular way *)

Record buffer (T : Type) : Type :=
  Buf {active: ptr; inactive: ptr; len: ptr; capacity: nat}.

Definition BufferFull : exn := exn_from_nat 10.
Definition BufferEmpty : exn := exn_from_nat 20.

Module Buffer.
Section Buffer.
Variable T : Type.
Notation buffer := (buffer T).

Definition is_buffer (a i : ptr) (m n : nat) (xs : seq T) :=
  [Pred h | exists (ys : seq T) ha hi,
            [/\ h = ha \+ hi,
                n = size xs + size ys,
                m = size xs,
                ha \In lseg a i xs &
                hi \In lseg i a ys]
  ].

Definition shape (b : buffer) (xs : seq T) :=
  [Pred h | exists a i m h',
            [/\ valid (active b :-> a \+ (inactive b :-> i \+ (len b :-> m \+ h'))),
                h = active b :-> a \+ (inactive b :-> i \+ (len b :-> m \+ h')) &
                h' \In is_buffer a i m (capacity b) xs]].

(* main methods *)

(* new buffer *)

Definition new_loopT (n : nat) (init : T) : Type :=
  forall (pk : ptr * nat),
  {q}, STsep (fun h => pk.2 < n /\ h \In lseg pk.1 q (nseq pk.2 init),
             [vfun p' => lseg p' q (nseq n.-1 init)]).

Program Definition new (n : nat) (init : T) :
          STsep (emp, [vfun v => shape v [::]]) :=
  Do (let run := Fix (fun (go : new_loopT n init) '(r,k) =>
                      Do (if k < n.-1 then
                            p' <-- allocb r 2;
                            p' ::= init;;
                            go (p', k.+1)
                          else ret r)) in
      if 0 < n then
        p <-- allocb null 2;
        p ::= init;;
        q <-- run (p, 0);
        p.+ 1 ::= q;;
        m <-- alloc 0;
        pi <-- alloc q;
        pa <-- alloc q;
        ret (Buf T pa pi m n)
      else m <-- alloc 0;
           pi <-- alloc null;
           pa <-- alloc null;
           ret (Buf T pa pi m 0)).
Next Obligation.
move=>n init go [r k] _ _[->->][q []] i /= [Hk H]; case: ltnP=>Hk1.
- step=>p'; step; rewrite unitR.
  apply: [gE q]=>//=; split; first by rewrite -ltn_predRL.
  by exists r, i; rewrite joinA.
move: Hk=>/[dup]/ltn_predK=>{1}<-; rewrite ltnS=>Hk.
by step=>_; have/eqP <-: (k == n.-1) by rewrite eqn_leq Hk1 Hk.
Qed.
Next Obligation.
move=>n init [] _ /= ->; case: ifP.
- move=>H0.
  step=>p; step; rewrite !unitR.
  rewrite -[_ \+ _]unitL; apply: [stepR p]@Unit=>//=q h H.
  step; step=>m; step=>pi; step=>pa; step=>V.
  exists q, q, 0, (h \+ (p :-> init \+ p.+ 1 :-> q)); split=>//.
  exists (nseq n init), Unit, (h \+ (p :-> init \+ p.+ 1 :-> q)); split=>//=.
  - by rewrite unitL.
  - by rewrite add0n size_nseq.
  by rewrite -(ltn_predK H0) -rcons_nseq; apply/lseg_rcons; exists p, h.
move=>_; step=>m; step=>pi; step=>pa; step=>V.
exists null, null, 0, Unit=>/=; split=>//.
by exists [::], Unit, Unit; split=>//; rewrite unitR.
Qed.

Program Definition write (x : T) (b : buffer) :
  {xs}, STsep (shape b xs,
               fun y h => match y with
                          | Val _ => h \In shape b (rcons xs x)
                          | Exn e => e = BufferFull /\ h \In shape b xs
                          end) :=
  Do (m <-- !len b;
      if m < capacity b then
        i <-- !inactive b;
        i ::= x;;
        r <-- !i.+ 1;
        inactive b ::= (r : ptr);;
        len b ::= m.+1
      else throw BufferFull).
Next Obligation.
move=>x b [xs []] _ /= [a][i][_][h][_ -> [ys][ha][hi][E Ec -> Ha Hi]].
rewrite Ec; step; case: ltnP.
- rewrite -{1}(addn0 (size xs)) ltn_add2l => Hys.
  step; rewrite {}E.
  case/lseg_case: Hi; first by case=>_ Eys; rewrite Eys in Hys.
  case=>y[r][h'][_ {hi}-> H'].
  do 4![step]=>{y}V.
  exists a, r, (size xs).+1, (ha \+ (i :-> x \+ (i.+ 1 :-> r \+ h'))); split=>//.
  exists (behead ys), (ha \+ (i :-> x \+ i.+ 1 :-> r)), h'; split=>//.
  - by rewrite !joinA.
  - by rewrite Ec size_rcons size_behead -subn1 addnABC // subn1.
  - by rewrite size_rcons.
  by apply/lseg_rcons; exists i, ha.
rewrite -{2}(addn0 (size xs)) leq_add2l leqn0 => /nilP Eys.
step=>V; split=>//.
exists a, i, (size xs), h; split=>//.
by exists [::], ha, hi; rewrite Eys in Ec Hi.
Qed.

(* we make checking for capacity != 0 the client's problem *)
Program Definition overwrite (x : T) (b : buffer) :
  {xs}, STsep (fun h => 0 < capacity b /\ h \In shape b xs,
               [vfun _ => shape b (drop ((size xs).+1 - capacity b) (rcons xs x))]) :=
  Do (i <-- !inactive b;
      i ::= x;;
      r <-- !i.+ 1;
      inactive b ::= (r : ptr);;
      m <-- !len b;
      if m < capacity b then
         len b ::= m.+1
      else
         active b ::= r).
Next Obligation.
move=>x b [xs []] _ /= [Hc][a][i][_][_][_ -> [ys][ha][hi][-> Ec -> Ha Hi]].
rewrite Ec in Hc *; step.
case/lseg_case: Hi.
- case=>Ei Eys {hi}->; rewrite {i}Ei in Ha *; rewrite {ys}Eys /= addn0 in Hc Ec *.
  case/lseg_case: Ha; first by case=>_ Exs; rewrite Exs in Hc.
  case=>z[r][h'][Exs {ha}-> H'].
  do 4!step; rewrite ltnn subSnn drop1 unitR; step=>V.
  exists r, r, (size xs), (a :-> x \+ (a.+ 1 :-> r \+ h')); split=>//.
  exists [::], (a :-> x \+ (a.+ 1 :-> r \+ h')), Unit; split=>//=.
  - by rewrite unitR.
  - by rewrite addn0 size_behead size_rcons.
  - by rewrite size_behead size_rcons.
  rewrite behead_rcons //; apply/lseg_rcons; exists a, h'; split=>//.
  by rewrite [in RHS]joinC joinA.
case=>y[r][h'][Eys {hi}-> H'].
do 4!step; rewrite -{1}(addn0 (size xs)) ltn_add2l {1}Eys /=; step=>V.
exists a, r, (size xs).+1, (ha \+ (i :-> x \+ (i.+ 1 :-> r \+ h'))); split=>//.
rewrite Eys /= addnS subSS subnDA subnn sub0n drop0.
exists (behead ys), (ha \+ (i :-> x \+ i.+ 1 :-> r)), h'; split=>//.
- by rewrite !joinA.
- by rewrite Ec {1}Eys /= size_rcons addnS addSn.
- by rewrite size_rcons.
by apply/lseg_rcons; exists i, ha.
Qed.

Program Definition read (b : buffer) :
  {xs}, STsep (shape b xs,
               fun y h => match y with
                          | Val x => h \In shape b (behead xs) /\ ohead xs = Some x
                          | Exn e => e = BufferEmpty /\ xs = [::]
                          end) :=
  Do (m <-- !len b;
      if 0 < m then
        a <-- !active b;
        x <-- !a;
        r <-- !a.+ 1;
        active b ::= (r : ptr);;
        len b ::= m.-1;;
        ret x
      else throw BufferEmpty).
Next Obligation.
move=>b [xs []] _ /= [a][i][_][_][_ -> [ys][ha][hi][-> Hc -> Ha Hi]].
step; case: ltnP.
- move=>Hm; step.
  case/lseg_case: Ha; first by case=>_ Exs; rewrite Exs in Hm.
  case=>x[r][h'][Exs {ha}-> H'].
  do 5![step]=>V; split; last by rewrite Exs.
  exists r, i, (size xs).-1, (a :-> x \+ (a.+ 1 :-> r \+ h') \+ hi); split=>//.
  exists (rcons ys x), h', (hi \+ (a :-> x \+ a.+ 1 :-> r)); split=>//.
  - by rewrite [LHS](pullX (h' \+ hi)) !joinA.
  - by rewrite size_rcons Hc {1}Exs /= addnS addSn.
  - by rewrite size_behead.
  by apply/lseg_rcons; exists a, hi.
by rewrite leqn0=>/nilP->; step.
Qed.

Definition free_loopT (n : nat) : Type :=
  forall (pk : ptr * nat),
  {q (xs : seq T)}, STsep (fun h => h \In lseg pk.1 q xs /\ size xs = n - pk.2,
                           [vfun _ : unit => emp]).

Program Definition free (b : buffer) :
  {xs}, STsep (fun h => h \In shape b xs,
               [vfun _ => emp]) :=
  Do (let run := Fix (fun (go : free_loopT (capacity b)) '(r,k) =>
                      Do (if k < capacity b then
                            p' <-- !r.+ 1;
                            dealloc r;;
                            dealloc r.+ 1;;
                            go (p', k.+1)
                          else ret tt)) in
      (if 0 < capacity b then
        a <-- !active b;
        run (a, 0);;
        skip
      else skip);;
      dealloc (active b);;
      dealloc (inactive b);;
      dealloc (len b)).
Next Obligation.
move=>b go [r k][_ _][->->] [q][xs][] h /= [H Hs].
case: ltnP.
- move=>Hk; case/lseg_case: H.
  - case=>_ E; rewrite E /= in Hs; move/eqP: Hs.
    by rewrite eq_sym subn_eq0 leqNgt Hk.
  case=>x[p][h'][E {h}-> H'].
  do 3!step; rewrite !unitL.
  apply: [gE q, behead xs]=>//=; split=>//.
  by rewrite subnS; move: Hs; rewrite {1}E /= =><-.
rewrite -subn_eq0=>/eqP Hc; rewrite Hc in Hs.
by step=>_; move: H; move/eqP/nilP: Hs=>->/=; case.
Qed.
Next Obligation.
move=>b [xs][] _ /= [a][i][m][_][_ -> [ys][ha][hi][-> Hc -> Ha Hi]].
case: ltnP.
- move=>_; apply/vrf_bind; step; apply: [stepX a, xs++ys]@(ha \+ hi)=>//=.
  - move=>_; split; last by rewrite size_cat subn0.
    by apply/lseg_cat; exists i, ha, hi.
  by move=>_ _ ->; rewrite unitR; step=>V; do 3![step]=>_; rewrite !unitR.
rewrite leqn0=>/eqP E.
do 4!step; rewrite !unitL=>_.
move: Hc; rewrite E =>/eqP; rewrite eq_sym addn_eq0; case/andP=>/nilP Ex /nilP Ey.
move: Ha; rewrite Ex /=; case=>_->; move: Hi; rewrite Ey /=; case=>_->.
by rewrite unitR.
Qed.

End Buffer.
End Buffer.