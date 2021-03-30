Section type_booleen.

Variable T : Set.

Definition cbool := T -> T -> T.


Definition ctr : cbool := fun x y => x.
Print ctr.
Definition cfa : cbool := fun x y => y.
Print cfa.

Definition cif :=
fun (b : cbool) (t : T) (e : T) =>
b t e.

Variables F V : T.

Compute cif ctr V F.
Compute cif cfa V F.

Definition cand := fun (a:cbool) (b:cbool) =>fun (x:T) (y:T) =>a (b x y) y.
Compute cand ctr ctr.
Compute cand ctr cfa.
Compute cand cfa cfa.
Compute cand cfa ctr.

Definition cor := fun (a:cbool) (b:cbool) =>fun (x:T)(y:T)=>a x (b x y).
Compute cor ctr ctr.
Compute cor ctr cfa.
Compute cor cfa cfa.
Compute cor cfa ctr.
Definition cnot := fun (b:cbool) => fun (x:T) (y:T)=> b y x.
Compute cnot ctr.
Compute cnot cfa.


End type_booleen.
Section type_nat.
Variable T: Set.
Definition compo : (T->T) -> (T->T) -> (T->T) :=
fun g f => fun x => g (f x).

Notation "g ° f" := (compo g f) (at level 10).
Fixpoint iter (f:T->T) (n: nat) :=
match n with
| O => fun x => x
| S p => f ° (iter f p)
end.

Definition cnat := (T->T) -> (T->T).

Definition cnat_of : nat -> cnat := fun n => fun f => (iter f n).
Notation "[ X ]N " := (cnat_of X) (at level 5).

Definition test := [3]N.

Definition c0: cnat := fun (f:T->T) (x:T) => x.
Definition c1: cnat := fun (f:T->T) (x:T) => f x.
Definition c2: cnat := fun (f:T->T) (x:T) => f (f x).
Definition c3: cnat := fun (f:T->T) (x:T) => f (f (f x)).
Definition cS:= fun (n:cnat)=> fun (f:T->T) (x:T)  => ( f (n f x )).
Compute c2.
Definition cadd := fun (n:cnat) (m:cnat) => fun (f:T->T) (x:T) =>  n f (m f x).
Compute cadd c2 c2.
Definition cmult := fun (n:cnat) (m:cnat) => fun (f:T->T)=>  n (m f).
Compute cmult c2 c3.
Definition cseq0 := fun (n:cnat)=> fun (x:T) (y:T)=> n (fun (z:T)=>y) x.
Compute cseq0 c3.

End type_nat.
Section type_de_identite_polymorphe.
Definition tid : Set := forall T: Set, T -> T.
Definition id : tid := fun T:Set => fun x:T => x.
Compute id bool true.

Definition nbtrue1 := fun b =>
match b with true => 1 | false => 0 end.
Compute nbtrue1 true.
Compute nbtrue1 false.
Definition pbool : Set := forall T: Set, T -> T -> T.
Definition ptr : pbool := fun T:Set => fun (x:T) (y:T) => x.
Definition pfa : pbool := fun T:Set => fun (x:T) (y:T) => y.
Definition pnot: pbool -> pbool := fun b: pbool => fun (T:Set)=>fun (x:T)(y:T) => b T y x.
Compute pnot ptr.
Definition pnotv2: pbool -> pbool := fun b => fun T : Set => b(T->T->T)(fun x y => y)(fun x y => x).
Compute pnot ptr.
Definition conjonction: pbool -> pbool -> pbool := fun (a:pbool) (b:pbool) => fun T:Set => fun (x:T) (y:T) => a T (b T x y ) y.  
Compute conjonction pfa pfa.
Compute conjonction pfa ptr.
Compute conjonction ptr pfa.
Compute conjonction ptr ptr.
Definition disjonction: pbool -> pbool -> pbool := fun (a:pbool) (b:pbool) => fun T:Set => fun (x:T) (y:T) => a T x (b T x y ).  
Compute disjonction pfa pfa.
Compute disjonction pfa ptr.
Compute disjonction ptr pfa.
Compute disjonction ptr ptr.
Definition pbvn: pbool -> nat := fun b => b (nat) 3  5 .
Compute pbvn ptr.
Compute pbvn pfa.

End type_de_identite_polymorphe.