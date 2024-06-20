Require Import Ascii.
Require Import String.
Require Import NArith.
Require Import Nat.
Require Import List.
Open Scope list.
Open Scope string.
Open Scope N.

Definition lcg (s : N) a c m := (a * s + c) mod m.

Definition rand s := lcg s 1103515245 12345 (2 ^ 31).

Definition empty := Empty_set.

Open Scope type.

Fixpoint Fin n :=
match n with
|O => empty
|S n => unit + Fin n
end.

Definition f {n} : nat -> Fin (S n).
 induction n;intro m.
 exact (inl tt).
 destruct m.
 exact (inl tt).
 exact (inr (IHn m)).
Defined.

Definition feq {n} (f f' : Fin n) : bool.
 induction n;destruct f,f'.
 exact true.
 exact false.
 exact false.
 exact (IHn f0 f1).
Defined.

Definition last {n} : Fin (S n).
 induction n.
 exact (inl tt).
 exact (inr IHn).
Defined.

Definition plus1 {n} : Fin n -> Fin n.
 induction n;destruct 1.
 destruct n.
 exact (inl tt).
 exact (inr (inl tt)).
 exact (inr (IHn f0)).
Defined.

Definition f' {n} : nat -> Fin (S n).
 induction 1.
 exact (f 0).
 destruct (feq IHnat last).
 exact (f 0).
 exact (plus1 IHnat).
Defined.

Fixpoint Vector n A :=
match n with
|O => unit : Type
|S n => A * Vector n A
end.

Definition vnil {A} : Vector 0 A := tt.
Notation "<>" := vnil.

Definition vcons {n A} x (v : Vector n A) : Vector (S n) A := (x,v).
Notation "x ;; v" := (vcons x v) (right associativity,at level 51).

Definition get {n A} (v : Vector n A) (f : Fin n) : A.
 induction n;destruct v,f.
 exact a.
 exact (IHn v f0).
Defined.

Definition set {n A} (v : Vector n A) (x : A) (f : Fin n) : Vector n A.
 induction n;destruct v,f.
 exact (x ;; v).
 exact (a ;; IHn v f0).
Defined.

Definition const {n A} (x : A) : Vector n A.
 induction n.
 exact <>.
 exact (x ;; IHn).
Defined.

Definition pushback {A n} (v : Vector n A) (x : A) : Vector (S n) A.
 induction n;destruct v.
 exact (x ;; <>).
 exact (a ;; IHn v).
Defined.

Definition rev {A n} (v : Vector n A) : Vector n A.
 induction n;destruct v.
 exact <>.
 exact (pushback (IHn v) a).
Defined.

Definition addv {n m A} : Vector n A -> Vector m A -> Vector (n+m) A.
 induction n;simpl.
 intros _ v;exact v.
 intros (a,v) v'.
 exact (a,IHn v v').
Defined.

Definition b n :=
match n with
|O => false
|S _ => true
end.

Inductive hex := x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | xA | xB | xC | xD | xE | xF.

Definition hextobool (h : hex) : bool * bool * bool * bool :=
match h with
|x0 => (b 0,b 0,b 0,b 0)
|x1 => (b 0,b 0,b 0,b 1)
|x2 => (b 0,b 0,b 1,b 0)
|x3 => (b 0,b 0,b 1,b 1)
|x4 => (b 0,b 1,b 0,b 0)
|x5 => (b 0,b 1,b 0,b 1)
|x6 => (b 0,b 1,b 1,b 0)
|x7 => (b 0,b 1,b 1,b 1)
|x8 => (b 1,b 0,b 0,b 0)
|x9 => (b 1,b 0,b 0,b 1)
|xA => (b 1,b 0,b 1,b 0)
|xB => (b 1,b 0,b 1,b 1)
|xC => (b 1,b 1,b 0,b 0)
|xD => (b 1,b 1,b 0,b 1)
|xE => (b 1,b 1,b 1,b 0)
|xF => (b 1,b 1,b 1,b 1)
end.

Definition hextonibble (h : hex) : Vector 4 bool.
 destruct (hextobool h) as (((b0,b1),b2),b3).
 exact (b0,(b1,(b2,(b3,tt)))).
Defined.

Definition h {n} (x : Vector n hex) : Vector (n * 4) bool.
 induction n;simpl.
 exact tt.
 destruct x.
 destruct (hextobool h) as (((b0,b1),b2),b3).
 exact (b0,(b1,(b2,(b3,IHn v)))).
Defined.

Definition screen := Vector 32 (Vector 64 bool).

Open Scope bool.
Definition xor b b' := (b && negb b') || (negb b && b').

Definition drawpixel (s : screen) (c : bool) (x : Fin 64) (y : Fin 32) : bool * screen :=
let l := get s y in
let p := get l x in
let p' := xor p c in
let l' := set l p' x in
(p,set s l' y).

Definition drawline {n} (s : screen) (l : Vector n bool) (x : Fin 64) (y : Fin 32) : bool * screen.
 generalize s,x,y;clear s;clear x;clear y;induction n;intros;destruct l.
 exact (false,s).
 destruct (drawpixel s b0 x y) as (b,s').
 destruct (feq x last).
 exact (b,s').
 destruct (IHn v s' (plus1 x) y) as (b',s'').
 exact (b || b',s'').
Defined.

Definition drawsprite {n m} (s : screen) (d : Vector n (Vector m bool)) (x : Fin 64) (y : Fin 32) : bool * screen.
 generalize s,x,y;clear s;clear x;clear y;induction n;intros;destruct d.
 exact (false,s).
 destruct (drawline s v x y) as (b,s').
 destruct (feq y last).
 exact (b,s').
 destruct (IHn v0 s' x (plus1 y)) as (b',s'').
 exact (b || b',s'').
Defined.

Definition blank : screen := const (const false).

Definition showpixel (b : bool) : string :=
if b then
 "*"
else
 "_".

Definition showline {n} (l : Vector n bool) : string.
 induction n;destruct l.
 exact "".
 exact (showpixel b0 ++ IHn v).
Defined.

Definition showscreen {n m} (s : Vector n (Vector m bool)) : string.
 induction n;destruct s.
 exact "
".
 exact ("
" ++ showline v ++ IHn v0).
Defined.

Definition show (s : screen) := showscreen s.

Definition memory := Vector 4096 (Vector 8 bool).
Definition pc := Vector 12 bool.
Definition index := Vector 12 bool.
Definition stack := list (Vector 12 bool).
Definition variable := Vector 16 (Vector 8 bool).
Definition seed := N.
Definition input := option hex.
Definition delay := Vector 8 bool.
Definition sound := Vector 8 bool.

Definition state := screen * memory * pc * index * stack * variable * seed * input * delay * sound.

Open Scope nat.

Definition wrev {n} (b : Vector n bool) : nat.
 induction n;destruct b.
 exact 0.
 destruct b0.
 exact (1+2*IHn v).
 exact (2*IHn v).
Defined.

Definition w {n} (b : Vector n bool) : nat := wrev (rev b).

Inductive instruction :=
|clear
|jump (n : Vector 12 bool)
|returnn
|call (n : Vector 12 bool)
|skipeqval (x : Vector 4 bool) (n : Vector 8 bool)
|skipneqval (x : Vector 4 bool) (n : Vector 8 bool)
|skipeqvar (x : Vector 4 bool) (y : Vector 4 bool)
|skipneqvar (x : Vector 4 bool) (y : Vector 4 bool)
|setval (x : Vector 4 bool) (n : Vector 8 bool)
|addval (x : Vector 4 bool) (n : Vector 8 bool)
|setvar (x : Vector 4 bool) (y : Vector 4 bool)
|or (x : Vector 4 bool) (y : Vector 4 bool)
|and (x : Vector 4 bool) (y : Vector 4 bool)
|xorr (x : Vector 4 bool) (y : Vector 4 bool)
|addvar (x : Vector 4 bool) (y : Vector 4 bool)
|subfrom (x : Vector 4 bool) (y : Vector 4 bool)
|subto (x : Vector 4 bool) (y : Vector 4 bool)
|shiftl (x : Vector 4 bool) (y : Vector 4 bool)
|shiftr (x : Vector 4 bool) (y : Vector 4 bool)
|setindex (n : Vector 12 bool)
|jumpoffset (n : Vector 12 bool)
|random (x : Vector 4 bool) (n : Vector 8 bool)
|display (x : Vector 4 bool) (y : Vector 4 bool) (n : Vector 4 bool)
|skipkey (x : Vector 4 bool)
|skipnkey (x : Vector 4 bool)
|readdelay (x : Vector 4 bool)
|setdelay (x : Vector 4 bool)
|setsound (x : Vector 4 bool)
|addindex (x : Vector 4 bool)
|getkey (x : Vector 4 bool)
|font (x : Vector 4 bool)
|todec (x : Vector 4 bool)
|store (x : Vector 4 bool)
|load (x : Vector 4 bool).

Definition add {n} (x y : Vector n bool) : bool * Vector n bool.
 induction n;destruct x,y.
 exact (false,<>).
 destruct (IHn v v0).
 exact ((b0 && b1) || (b1 && b2) || (b0 && b2),(xor b0 (xor b1 b2)) ;; v1).
Defined.

Definition bor {n} (x y : Vector n bool) : Vector n bool.
 induction n;destruct x,y.
 exact <>.
 exact (b0 || b1 ;; IHn v v0).
Defined.

Definition band {n} (x y : Vector n bool) : Vector n bool.
 induction n;destruct x,y.
 exact <>.
 exact (b0 && b1 ;; IHn v v0).
Defined.

Definition bxor {n} (x y : Vector n bool) : Vector n bool.
 induction n;destruct x,y.
 exact <>.
 exact (xor b0 b1 ;; IHn v v0).
Defined.

Definition bnot {n} (x : Vector n bool) : Vector n bool.
 induction n;destruct x.
 exact <>.
 exact (negb b0 ;; IHn v).
Defined.

Definition one {n} : Vector n bool.
 induction n.
 exact <>.
 destruct n.
 exact (true ;; <>).
 exact (false ;; IHn).
Defined.

Definition neg {n} (x : Vector n bool) : Vector n bool.
 exact (snd (add (bnot x) one)).
Defined.

Definition sub {n} (x y : Vector n bool) : bool * Vector n bool.
 destruct n.
 exact (false,<>).
 pose (snd (add x (neg y))) as xmy.
 exact (negb (fst xmy),xmy).
Defined.

Definition bshiftl {n} (x : Vector n bool) : bool * Vector n bool.
 induction n;destruct x.
 exact (false,<>).
 destruct n.
 exact (b0,false ;; <>).
 exact (b0,IHn v).
Defined.

Definition bshiftr' {n} (x : Vector (S n) bool) : bool * Vector n bool.
 induction n;destruct x.
 exact (b0,<>).
 destruct (IHn v) as (b',v').
 exact (b',b0 ;; v').
Defined.

Definition bshiftr {n} (x : Vector n bool) : bool * Vector n bool.
 destruct n.
 exact (false,<>).
 destruct (bshiftr' x) as (b,x').
 exact (b,false ;; x').
Defined.

Definition incp (p : Vector 12 bool) : Vector 12 bool.
 exact (snd (add (snd (add p one)) one)).
Defined.

Definition read {n A} (v : Vector n A) (i : nat) : option A.
 generalize i;clear i;induction n;intros;destruct v.
 exact None.
 destruct i.
 exact (Some a).
 exact (IHn v i).
Defined.

Definition reads {A n} (v : Vector n A) (i : nat) (m : nat) : option (Vector m A).
 generalize i;clear i;induction m;intros.
 exact (Some <>).
 destruct (read v i).
 destruct (IHm (i+1)).
 exact (Some (a ;; v0)).
 exact None.
 exact None.
Defined.

Definition tobyte (n : nat) : Vector 8 bool.
 induction n.
 exact (const (b 0)).
 exact (snd (add IHn (h (x0 ;; x1 ;; <>)))).
Defined.

Definition num (b : bool) :=
if b then
 1
else
 0.

Definition eqword {n} (b b' : Vector n bool) : bool.
 induction n;destruct b,b'.
 exact true.
 exact (negb (xor b0 b1) && IHn v v0).
Defined.

Definition pad {n} m (b : Vector n bool) : Vector (m+n) bool.
 induction m.
 exact b.
 exact (false ;; IHm).
Defined.

Definition todigits (x : Vector 8 bool) : Vector 8 bool * Vector 8 bool * Vector 8 bool.
 pose (N.of_nat (w x)) as wx.
 pose (N.to_nat (wx mod 10)) as n3.
 pose (N.to_nat (wx/10 mod 10)) as n2.
 pose (N.to_nat (wx/100)) as n1.
 exact (tobyte n1,tobyte n2,tobyte n3).
Defined.

Definition dec {n} (x : Vector n bool) : Vector n bool.
 destruct (eqword x (const false)).
 exact x.
 exact (snd (add x (neg one))).
Defined.

Definition tonibbles (b : Vector 8 bool) : Vector 4 bool * Vector 4 bool.
 destruct b as (b0,(b1,(b2,(b3,(b4,(b5,(b6,(b7,_)))))))).
 exact ((b0,(b1,(b2,(b3,tt)))),(b4,(b5,(b6,(b7,tt))))).
Defined.

Definition fromnibbles (b : Vector 4 bool) (b' : Vector 4 bool) : Vector 8 bool.
 destruct b as (b0,(b1,(b2,(b3,_)))).
 destruct b' as (b4,(b5,(b6,(b7,_)))).
 exact (b0,(b1,(b2,(b3,(b4,(b5,(b6,(b7,tt)))))))).
Defined.

Definition runclear (s : state) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((blank,m),incp p),i),st),v),sd),inp),d),sn).
Defined.

Definition runjump (s : state) (n : Vector 12 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),n),i),st),v),sd),inp),d),sn).
Defined.

Definition runcall (s : state) (n : Vector 12 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),n),i),p :: st),v),sd),inp),d),sn).
Defined.

Definition runreturn (s : state) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct st.
 exact (((((((((s,m),incp p),i),nil),v),sd),inp),d),sn).
 exact (((((((((s,m),incp v0),i),st),v),sd),inp),d),sn).
Defined.

Definition runskipeqval (s : state) (x : Vector 4 bool) (n : Vector 8 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (eqword (get v (f (w x))) n).
 exact (((((((((s,m),incp (incp p)),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),i),st),v),sd),inp),d),sn).
Defined.

Definition runskipneqval (s : state) (x : Vector 4 bool) (n : Vector 8 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (eqword (get v (f (w x))) n).
 exact (((((((((s,m),incp p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp (incp p)),i),st),v),sd),inp),d),sn).
Defined.

Definition runskipeqvar (s : state) (x y : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (eqword (get v (f (w x))) (get v (f (w y)))).
 exact (((((((((s,m),incp (incp p)),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),i),st),v),sd),inp),d),sn).
Defined.

Definition runskipneqvar (s : state) (x y : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (eqword (get v (f (w x))) (get v (f (w y)))).
 exact (((((((((s,m),incp p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp (incp p)),i),st),v),sd),inp),d),sn).
Defined.

Definition runsetval (s : state) (x : Vector 4 bool) (n : Vector 8 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),i),st),set v n (f (w x))),sd),inp),d),sn).
Defined.

Definition runaddval (s : state) (x : Vector 4 bool) (n : Vector 8 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),i),st),set v (snd (add (get v (f (w x))) n)) (f (w x))),sd),inp),d),sn).
Defined.

Definition runsetvar (s : state) (x y : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),i),st),set v (get v (f (w y))) (f (w x))),sd),inp),d),sn).
Defined.

Definition runor (s : state) (x y : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),i),st),set v (bor (get v (f (w x))) (get v (f (w y)))) (f (w x))),sd),inp),d),sn).
Defined.

Definition runand (s : state) (x y : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),i),st),set v (band (get v (f (w x))) (get v (f (w y)))) (f (w x))),sd),inp),d),sn).
Defined.

Definition runxor (s : state) (x y : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),i),st),set v (bxor (get v (f (w x))) (get v (f (w y)))) (f (w x))),sd),inp),d),sn).
Defined.

Definition runaddvar (s : state) (x y : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (add (get v (f (w x))) (get v (f (w y)))) as (c,xpy).
 exact (((((((((s,m),incp p),i),st),set (set v xpy (f (w x))) (tobyte (num c)) (f 15)),sd),inp),d),sn).
Defined.

Definition runsubfrom (s : state) (x y : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (sub (get v (f (w x))) (get v (f (w y)))) as (c,xmy).
 exact (((((((((s,m),incp p),i),st),set (set v xmy (f (w x))) (tobyte (num c)) (f 15)),sd),inp),d),sn).
Defined.

Definition runsubto (s : state) (x y : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (sub (get v (f (w y))) (get v (f (w x)))) as (c,ymx).
 exact (((((((((s,m),incp p),i),st),set (set v ymx (f (w x))) (tobyte (num c)) (f 15)),sd),inp),d),sn).
Defined.

Definition runshiftl (s : state) (x y : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (bshiftl (get v (f (w y)))) as (c,ly).
 exact (((((((((s,m),incp p),i),st),set (set v ly (f (w x))) (tobyte (num c)) (f 15)),sd),inp),d),sn).
Defined.

Definition runshiftr (s : state) (x y : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (bshiftr (get v (f (w y)))) as (c,ry).
 exact (((((((((s,m),incp p),i),st),set (set v ry (f (w x))) (tobyte (num c)) (f 15)),sd),inp),d),sn).
Defined.

Definition runsetindex (s : state) (n : Vector 12 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),n),st),v),sd),inp),d),sn).
Defined.

Definition runjumpoffset (s : state) (n : Vector 12 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),snd (add n (pad 4 (get v (f 0))))),i),st),v),sd),inp),d),sn).
Defined.

Definition runrandom (s : state) (x : Vector 4 bool) (n : Vector 8 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),i),st),set v (band (tobyte (N.to_nat (sd mod 256))) n) (f (w x))),rand sd),inp),d),sn).
Defined.

Definition rundisplay (s : state) (x : Vector 4 bool) (y : Vector 4 bool) (n : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (reads m (w i) (w n)) as [sprite|].
 destruct (drawsprite s sprite (f' (w (get v (f (w x))))) (f' (w (get v (f (w y)))))) as (vf,s').
 exact (((((((((s',m),incp p),i),st),set v (tobyte (num vf)) (f 15)),sd),inp),d),sn).
 exact (((((((((s,m),p),i),st),v),sd),inp),d),sn).
Defined.

Definition runskipkey (s : state) (x : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct inp.
 destruct (eqword (get v (f (w x))) (h (x0 ;; h0 ;; <>))).
 exact (((((((((s,m),incp (incp p)),i),st),v),sd),Some h0),d),sn).
 exact (((((((((s,m),incp p),i),st),v),sd),Some h0),d),sn).
 exact (((((((((s,m),incp p),i),st),v),sd),None),d),sn).
Defined.

Definition runskipnkey (s : state) (x : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct inp.
 destruct (eqword (get v (f (w x))) (h (x0 ;; h0 ;; <>))).
 exact (((((((((s,m),incp p),i),st),v),sd),Some h0),d),sn).
 exact (((((((((s,m),incp (incp p)),i),st),v),sd),Some h0),d),sn).
 exact (((((((((s,m),incp (incp p)),i),st),v),sd),None),d),sn).
Defined.

Definition runreaddelay (s : state) (x : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),i),st),set v d (f (w x))),sd),inp),d),sn).
Defined.

Definition runsetdelay (s : state) (x : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),i),st),v),sd),inp),get v (f (w x))),sn).
Defined.

Definition runsetsound (s : state) (x : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact ((((((((((s,m),incp p),i),st),v),sd),inp),d),get v (f (w x)))).
Defined.

Definition runaddindex (s : state) (x : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),snd (add i (pad 4 (get v (f (w x)))))),st),v),sd),inp),d),sn).
Defined.

Definition rungetkey (s : state) (x : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct inp.
 exact (((((((((s,m),incp p),i),st),set v (h (x0 ;; h0 ;; <>)) (f (w x))),sd),Some h0),d),sn).
 exact (((((((((s,m),p),i),st),v),sd),None),d),sn).
Defined.

Definition runfont (s : state) (x : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 exact (((((((((s,m),incp p),pad 4 (tobyte (80+5*w (get v (f (w x)))))),st),v),sd),inp),d),sn).
Defined.

Definition runtodec (s : state) (x : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (todigits (get v (f (w x)))) as ((d1,d2),d3).
 exact (((((((((s,set (set (set m d1 (f (w i))) d2 (f (w i + 1))) d3 (f (w i + 2))),incp p),i),st),v),sd),inp),d),sn).
Defined.

Open Scope nat.

Definition runstore (s : state) (x : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 pose (set m (get v (f 0)) (f (w i))) as m0.
 refine (if 0 <? w x then _ else (((((((((s,m0),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m0 (get v (f 1)) (f (w i + 1))) as m1.
 refine (if 1 <? w x then _ else (((((((((s,m1),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m1 (get v (f 2)) (f (w i + 2))) as m2.
 refine (if 2 <? w x then _ else (((((((((s,m2),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m2 (get v (f 3)) (f (w i + 3))) as m3.
 refine (if 3 <? w x then _ else (((((((((s,m3),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m3 (get v (f 4)) (f (w i + 4))) as m4.
 refine (if 4 <? w x then _ else (((((((((s,m4),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m4 (get v (f 5)) (f (w i + 5))) as m5.
 refine (if 5 <? w x then _ else (((((((((s,m5),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m5 (get v (f 6)) (f (w i + 6))) as m6.
 refine (if 6 <? w x then _ else (((((((((s,m6),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m6 (get v (f 7)) (f (w i + 7))) as m7.
 refine (if 7 <? w x then _ else (((((((((s,m7),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m7 (get v (f 8)) (f (w i + 8))) as m8.
 refine (if 8 <? w x then _ else (((((((((s,m8),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m8 (get v (f 9)) (f (w i + 9))) as m9.
 refine (if 9 <? w x then _ else (((((((((s,m9),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m9 (get v (f 10)) (f (w i + 10))) as m10.
 refine (if 10 <? w x then _ else (((((((((s,m10),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m10 (get v (f 11)) (f (w i + 11))) as m11.
 refine (if 11 <? w x then _ else (((((((((s,m11),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m11 (get v (f 12)) (f (w i + 12))) as m12.
 refine (if 12 <? w x then _ else (((((((((s,m12),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m12 (get v (f 13)) (f (w i + 13))) as m13.
 refine (if 13 <? w x then _ else (((((((((s,m13),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m13 (get v (f 14)) (f (w i + 14))) as m14.
 refine (if 14 <? w x then _ else (((((((((s,m14),incp p),i),st),v),sd),inp),d),sn)).
 pose (set m14 (get v (f 15)) (f (w i + 15))) as m15.
 exact (((((((((s,m15),incp p),i),st),v),sd),inp),d),sn).
Defined.

Definition runload (s : state) (x : Vector 4 bool) : state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 pose (set v (get m (f (w i))) (f 0)) as v0.
 refine (if 0 <? w x then _ else (((((((((s,m),incp p),i),st),v0),sd),inp),d),sn)).
 pose (set v0 (get m (f (w i + 1))) (f 1)) as v1.
 refine (if 1 <? w x then _ else (((((((((s,m),incp p),i),st),v1),sd),inp),d),sn)).
 pose (set v1 (get m (f (w i + 2))) (f 2)) as v2.
 refine (if 2 <? w x then _ else (((((((((s,m),incp p),i),st),v2),sd),inp),d),sn)).
 pose (set v2 (get m (f (w i + 3))) (f 3)) as v3.
 refine (if 3 <? w x then _ else (((((((((s,m),incp p),i),st),v3),sd),inp),d),sn)).
 pose (set v3 (get m (f (w i + 4))) (f 4)) as v4.
 refine (if 4 <? w x then _ else (((((((((s,m),incp p),i),st),v4),sd),inp),d),sn)).
 pose (set v4 (get m (f (w i + 5))) (f 5)) as v5.
 refine (if 5 <? w x then _ else (((((((((s,m),incp p),i),st),v5),sd),inp),d),sn)).
 pose (set v5 (get m (f (w i + 6))) (f 6)) as v6.
 refine (if 6 <? w x then _ else (((((((((s,m),incp p),i),st),v6),sd),inp),d),sn)).
 pose (set v6 (get m (f (w i + 7))) (f 7)) as v7.
 refine (if 7 <? w x then _ else (((((((((s,m),incp p),i),st),v7),sd),inp),d),sn)).
 pose (set v7 (get m (f (w i + 8))) (f 8)) as v8.
 refine (if 8 <? w x then _ else (((((((((s,m),incp p),i),st),v8),sd),inp),d),sn)).
 pose (set v8 (get m (f (w i + 9))) (f 9)) as v9.
 refine (if 9 <? w x then _ else (((((((((s,m),incp p),i),st),v9),sd),inp),d),sn)).
 pose (set v9 (get m (f (w i + 10))) (f 10)) as v10.
 refine (if 10 <? w x then _ else (((((((((s,m),incp p),i),st),v10),sd),inp),d),sn)).
 pose (set v10 (get m (f (w i + 11))) (f 11)) as v11.
 refine (if 11 <? w x then _ else (((((((((s,m),incp p),i),st),v11),sd),inp),d),sn)).
 pose (set v11 (get m (f (w i + 12))) (f 12)) as v12.
 refine (if 12 <? w x then _ else (((((((((s,m),incp p),i),st),v12),sd),inp),d),sn)).
 pose (set v12 (get m (f (w i + 13))) (f 13)) as v13.
 refine (if 13 <? w x then _ else (((((((((s,m),incp p),i),st),v13),sd),inp),d),sn)).
 pose (set v13 (get m (f (w i + 14))) (f 14)) as v14.
 refine (if 14 <? w x then _ else (((((((((s,m),incp p),i),st),v14),sd),inp),d),sn)).
 pose (set v14 (get m (f (w i + 15))) (f 15)) as v15.
 exact (((((((((s,m),incp p),i),st),v15),sd),inp),d),sn).
Defined.

Definition fetch (s : state) : option (Vector 4 (Vector 4 bool)).
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (reads m (w p) 2) as [(b0,(b1,_))|].
 destruct (tonibbles b0) as (b2,b3).
 destruct (tonibbles b1) as (b4,b5).
 exact (Some (b2,(b3,(b4,(b5,tt))))).
 exact None.
Defined.

Inductive pattern := H (_:hex) | X.

Definition patterns := Vector 4 pattern.

Definition matchp (p : pattern) (b : Vector 4 bool) : option (Vector 4 bool).
 destruct p.
 destruct (eqword b (h (h0 ;; <>))).
 exact (Some (const false)).
 exact None.
 exact (Some b).
Defined.

Definition matchps (p : patterns) (b : Vector 4 (Vector 4 bool)) : option (Vector 4 bool * Vector 4 bool * Vector 4 bool).
 destruct (matchp (get p (f 0)) (get b (f 0)));[|exact None].
 destruct (matchp (get p (f 1)) (get b (f 1)));[|exact None].
 destruct (matchp (get p (f 2)) (get b (f 2)));[|exact None].
 destruct (matchp (get p (f 3)) (get b (f 3)));[|exact None].
 exact (Some (v0,v1,v2)).
Defined.

Definition decode (b : Vector 4 (Vector 4 bool)) : option instruction.
 destruct (matchps (H x0 ;; H x0 ;; H xE ;; H x0 ;; <>) b).
 exact (Some clear).
 destruct (matchps (H x1 ;; X ;; X ;; X ;; <>) b) as [((N1,N2),N3)|].
 exact (Some (jump (addv (addv N1 N2) N3))).
 destruct (matchps (H x0 ;; H x0 ;; H xE ;; H xE ;; <>) b).
 exact (Some returnn).
 destruct (matchps (H x2 ;; X ;; X ;; X ;; <>) b) as [((N1,N2),N3)|].
 exact (Some (call (addv (addv N1 N2) N3))).
 destruct (matchps (H x3 ;; X ;; X ;; X ;; <>) b) as [((X,N1),N2)|].
 exact (Some (skipeqval X (addv N1 N2))).
 destruct (matchps (H x4 ;; X ;; X ;; X ;; <>) b) as [((X,N1),N2)|].
 exact (Some (skipneqval X (addv N1 N2))).
 destruct (matchps (H x5 ;; X ;; X ;; H x0 ;; <>) b) as [((X,Y),_)|].
 exact (Some (skipeqvar X Y)).
 destruct (matchps (H x9 ;; X ;; X ;; H x0 ;; <>) b) as [((X,Y),_)|].
 exact (Some (skipneqvar X Y)).
 destruct (matchps (H x6 ;; X ;; X ;; X ;; <>) b) as [((X,N1),N2)|].
 exact (Some (setval X (addv N1 N2))).
 destruct (matchps (H x7 ;; X ;; X ;; X ;; <>) b) as [((X,N1),N2)|].
 exact (Some (addval X (addv N1 N2))).
 destruct (matchps (H x8 ;; X ;; X ;; H x0 ;; <>) b) as [((X,Y),_)|].
 exact (Some (setvar X Y)).
 destruct (matchps (H x8 ;; X ;; X ;; H x1 ;; <>) b) as [((X,Y),_)|].
 exact (Some (or X Y)).
 destruct (matchps (H x8 ;; X ;; X ;; H x2 ;; <>) b) as [((X,Y),_)|].
 exact (Some (and X Y)).
 destruct (matchps (H x8 ;; X ;; X ;; H x3 ;; <>) b) as [((X,Y),_)|].
 exact (Some (xorr X Y)).
 destruct (matchps (H x8 ;; X ;; X ;; H x4 ;; <>) b) as [((X,Y),_)|].
 exact (Some (addvar X Y)).
 destruct (matchps (H x8 ;; X ;; X ;; H x5 ;; <>) b) as [((X,Y),_)|].
 exact (Some (subfrom X Y)).
 destruct (matchps (H x8 ;; X ;; X ;; H x7 ;; <>) b) as [((X,Y),_)|].
 exact (Some (subto X Y)).
 destruct (matchps (H x8 ;; X ;; X ;; H x6 ;; <>) b) as [((X,Y),_)|].
 exact (Some (shiftr X Y)).
 destruct (matchps (H x8 ;; X ;; X ;; H xE ;; <>) b) as [((X,Y),_)|].
 exact (Some (shiftl X Y)).
 destruct (matchps (H xA ;; X ;; X ;; X ;; <>) b) as [((N1,N2),N3)|].
 exact (Some (setindex (addv (addv N1 N2) N3))).
 destruct (matchps (H xB ;; X ;; X ;; X ;; <>) b) as [((N1,N2),N3)|].
 exact (Some ((jumpoffset (addv (addv N1 N2) N3)))).
 destruct (matchps (H xC ;; X ;; X ;; X ;; <>) b) as [((X,N1),N2)|].
 exact (Some (random X (addv N1 N2))).
 destruct (matchps (H xD ;; X ;; X ;; X ;; <>) b) as [((X,Y),N)|].
 exact (Some (display X Y N)).
 destruct (matchps (H xE ;; X ;; H x9 ;; H xE ;; <>) b) as [((X,_),_)|].
 exact (Some (skipkey X)).
 destruct (matchps (H xE ;; X ;; H xA ;; H x1 ;; <>) b) as [((X,_),_)|].
 exact (Some (skipnkey X)).
 destruct (matchps (H xF ;; X ;; H x0 ;; H x7 ;; <>) b) as [((X,_),_)|].
 exact (Some (readdelay X)).
 destruct (matchps (H xF ;; X ;; H x1 ;; H x5 ;; <>) b) as [((X,_),_)|].
 exact (Some (setdelay X)).
 destruct (matchps (H xF ;; X ;; H x1 ;; H x8 ;; <>) b) as [((X,_),_)|].
 exact (Some (setsound X)).
 destruct (matchps (H xF ;; X ;; H x1 ;; H xE ;; <>) b) as [((X,_),_)|].
 exact (Some (addindex X)).
 destruct (matchps (H xF ;; X ;; H x0 ;; H xA ;; <>) b) as [((X,_),_)|].
 exact (Some (getkey X)).
 destruct (matchps (H xF ;; X ;; H x2 ;; H x9 ;; <>) b) as [((X,_),_)|].
 exact (Some (font X)).
 destruct (matchps (H xF ;; X ;; H x3 ;; H x3 ;; <>) b) as [((X,_),_)|].
 exact (Some (todec X)).
 destruct (matchps (H xF ;; X ;; H x5 ;; H x5 ;; <>) b) as [((X,_),_)|].
 exact (Some (store X)).
 destruct (matchps (H xF ;; X ;; H x6 ;; H x5 ;; <>) b) as [((X,_),_)|].
 exact (Some (load X)).
 exact None.
Defined.

Definition execute (s : state) (i : instruction) : state.
 destruct i.
 exact (runclear s).
 exact (runjump s n).
 exact (runreturn s).
 exact (runcall s n).
 exact (runskipeqval s x n).
 exact (runskipneqval s x n).
 exact (runskipeqvar s x y).
 exact (runskipneqvar s x y).
 exact (runsetval s x n).
 exact (runaddval s x n).
 exact (runsetvar s x y).
 exact (runor s x y).
 exact (runand s x y).
 exact (runxor s x y).
 exact (runaddvar s x y).
 exact (runsubfrom s x y).
 exact (runsubto s x y).
 exact (runshiftl s x y).
 exact (runshiftr s x y).
 exact (runsetindex s n).
 exact (runjumpoffset s n).
 exact (runrandom s x n).
 exact (rundisplay s x y n).
 exact (runskipkey s x).
 exact (runskipnkey s x).
 exact (runreaddelay s x).
 exact (runsetdelay s x).
 exact (runsetsound s x).
 exact (runaddindex s x).
 exact (rungetkey s x).
 exact (runfont s x).
 exact (runtodec s x).
 exact (runstore s x).
 exact (runload s x).
Defined.

Definition step (s : state) : option state.
 destruct (fetch s) as [i|].
 destruct (decode i) as [i'|].
 exact (Some (execute s i')).
 exact None.
 exact None.
Defined.

Definition steps (n : nat) (s : state) : option state.
 generalize s;clear s;induction n;intros.
 exact (Some s).
 destruct (IHn s).
 exact (step s0).
 exact None.
Defined.

Definition frame (input' : input) (s : state) : option state.
 destruct s as (((((((((s,m),p),i),st),v),sd),inp),d),sn).
 destruct (steps 12 (((((((((s,m),p),i),st),v),sd),input'),d),sn)) as [(((((((((s',m'),p'),i'),st'),v'),sd'),inp'),d'),sn')|].
 exact (Some (((((((((s',m'),p'),i'),st'),v'),sd'),inp'),dec d'),dec sn')).
 exact None.
Defined.

Definition run (inputs : list input) (s : state) : option state.
 generalize s;clear s;induction inputs;intros.
 exact (Some s).
 destruct (frame a s).
 exact (IHinputs s0).
 exact None.
Defined.

Definition write' {A n} (v : Vector (S n) A) (l : list A) (m : nat) : Vector (S n) A.
 generalize v,m;clear m;clear v;induction l;intros.
 exact v.
 exact (IHl (set v a (f m)) (m+1)).
Defined.

Definition write {A n} (v : Vector n A) (l : list A) (i : nat) : Vector n A.
 destruct n.
 exact tt.
 exact (write' v l i).
Defined.

Open Scope char.

Definition parsehex (c : ascii) : option hex :=
match c with
|"0" => Some x0
|"1" => Some x1
|"2" => Some x2
|"3" => Some x3
|"4" => Some x4
|"5" => Some x5
|"6" => Some x6
|"7" => Some x7
|"8" => Some x8
|"9" => Some x9
|"A" => Some xA
|"B" => Some xB
|"C" => Some xC
|"D" => Some xD
|"E" => Some xE
|"F" => Some xF
|_ => None
end.

Definition mapstr {A} (f : ascii -> A) : string -> list A.
 induction 1.
 exact nil.
 exact (cons (f a) IHstring).
Defined.

Open Scope list.

Definition nibbles : list (option hex) -> list (Vector 4 bool).
 induction 1.
 exact nil.
 destruct a.
 exact (hextonibble h0 :: IHlist).
 exact IHlist.
Defined.

Fixpoint tobytes (l : list (Vector 4 bool)) : list (Vector 8 bool) :=
match l with
|nil => nil
|b :: nil => fromnibbles b (const false) :: nil
|b :: b' :: l => fromnibbles b b' :: tobytes l
end.

Definition parse (s : string) : list (Vector 8 bool) := tobytes (nibbles (mapstr parsehex s)).

Open Scope string.

Definition chars := parse "
F0 90 90 90 F0
20 60 20 20 70
F0 10 F0 80 F0
F0 10 F0 10 F0
90 90 F0 10 10
F0 80 F0 10 F0
F0 80 F0 90 F0
F0 10 20 40 40
F0 90 F0 90 F0
F0 90 F0 10 F0
F0 90 F0 90 90
E0 90 E0 90 E0
F0 80 80 80 F0
E0 90 90 90 E0
F0 80 F0 80 F0
F0 80 F0 80 80
".

Definition init (c : list (Vector 8 bool)) (s : N) : state.
 exact (((((((((blank,write (write (const (const (b 0))) chars 80) c 512),h (x2 ;; x0 ;; x0 ;; <>)),const (b 0)),nil),const (const (b 0))),s),None),const false),const false).
Defined.

Open Scope string.

Definition showst (s : option state) : option string.
 destruct s as [(((((((((s,m),p),i),st),v),sd),inp),d),sn)|].
 destruct (w sn =? 0)%nat.
 exact (Some (show s)).
 exact (Some ("
beep
"++show s)).
 exact None.
Defined.

Definition showstate (s : option state) : option (string * string * string * list string * string * N * input * string * string).
 destruct s as [(((((((((s,m),p),i),st),v),sd),inp),d),sn)|].
 exact (Some (show s,showline p,showline i,map showline st,showscreen v,sd,inp,showline d,showline sn)).
 exact None.
Defined.

Definition code := parse "".

Compute showst (run (nil) (init code 0)).