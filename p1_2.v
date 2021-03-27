Section type_booleen.

Variable T : Set.

Definition cbool := T -> T -> T.


Definition ctr : cbool := fun x y => x.
Definition cfa : cbool := fun x y => y.

Definition cif :=
fun (b : cbool) (t : T) (e : T) =>
b t e.

Variables F V : T.

Compute cif ctr V F.
Compute cif cfa V F.

Definition cand := fun (a:cbool) (b:cbool) => cif a (cif b V F) F.
Compute cand ctr ctr.
Compute cand ctr cfa.
Compute cand cfa cfa.
Compute cand cfa ctr.

Definition cor := fun (a:cbool) (b:cbool) => cif a V (cif b V F).
Compute cor ctr ctr.
Compute cor ctr cfa.
Compute cor cfa cfa.
Compute cor cfa ctr.
Definition cnot := fun (a:cbool) => cif a F V.
Compute cnot ctr.
Compute cnot cfa.


End type_booleen.
