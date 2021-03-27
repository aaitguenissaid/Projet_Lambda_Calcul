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
