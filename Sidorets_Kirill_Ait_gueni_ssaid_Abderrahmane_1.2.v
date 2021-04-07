(*Sidorets Kirill et Ait gueni ssaid Abderrahmane*)
(* 1.2 λ-calcul simplement typé*)
  (* 1. Booléens (codage des constantes et des opérations de base) *)
  Section type_booleen. 
    (*1.2.1*)
    Variable T : Set. 
    Definition cbool := T -> T -> T.
    (*booléens de Church vrai: λx y.x*)
    Definition ctr : cbool := fun x y => x.
    Print ctr.
    (*booléens de Church faux: λx y.y*)
    Definition cfa : cbool := fun x y => y.
    Print cfa.
    (*if b then m else n : λ b m n .b m n*)    
    Definition cif: cbool -> T ->T ->T :=fun (b : cbool) (t : T) (e : T) =>b t e.
    Variables F V : T.
    Compute cif ctr V F.
    Compute cif cfa V F.
    (* a and  b : λ a b.λx y. a (b x y) y *)
    Definition cand:cbool->cbool->cbool := fun (a:cbool) (b:cbool) =>fun (x:T) (y:T) =>a (b x y) y.
    Compute cand ctr ctr.
    Compute cand ctr cfa.
    Compute cand cfa cfa.
    Compute cand cfa ctr.
    (* a or  b : λ a b.λx y. a x (b x y) *)
    Definition cor :cbool->cbool->cbool:= fun (a:cbool) (b:cbool) =>fun (x:T)(y:T)=>a x (b x y).
    Compute cor ctr ctr.
    Compute cor ctr cfa.
    Compute cor cfa cfa.
    Compute cor cfa ctr.
    (*not b :λ b.λ x y . b y x*)
    Definition cnot:cbool->cbool := fun (b:cbool) => fun (x:T) (y:T)=> b y x.
    Compute cnot ctr.
    Compute cnot cfa.
  End type_booleen.
  (* 2. Entiers naturels (codage de quelques constantes, des opérations
   successeur, addition et multiplication, et du test à 0) *)
  Section type_nat.
  Variable T: Set.
    Definition compo : (T->T) -> (T->T) -> (T->T) :=fun g f => fun x => g (f x).

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
    (* 0 :λ f x .x *)  
    Definition c0: cnat := fun (f:T->T) (x:T) => x.
    (* 1 :λ f x . f x *)  
    Definition c1: cnat := fun (f:T->T) (x:T) => f x.
    (* 2 :λ f x . f (f x) *)  
    Definition c2: cnat := fun (f:T->T) (x:T) => f (f x).
    (* 3 :λ f x . f (f (f x)) *)  
    Definition c3: cnat := fun (f:T->T) (x:T) => f (f (f x)).
    (* csucc(n)=n+1 : λ n.λ f x. f (n f x)*)
    Definition cS:= fun (n:cnat)=> fun (f:T->T) (x:T)  => ( f (n f x )).
    Compute c0.
    Compute c1.
    Compute c2.
    Compute c3.
    Compute cS c0.
    Compute cS c1.
    Compute cS c2.
    Compute cS c3.
    (* cadd (a,b)=a+b :λ n m.λ f x. n f (m f x) *)
    Definition cadd := fun (n:cnat) (m:cnat) => fun (f:T->T) (x:T) =>  n f (m f x).
    Compute cadd c1 c2.
    Compute cadd c0 c2.
    Compute cadd c3 c2.
    Compute cadd c3 c3.
    (* cmult (a,b)=a*b :λ n m.λ f . n (m f) *)
    Definition cmult := fun (n:cnat) (m:cnat) => fun (f:T->T)=>  n (m f).
    Compute cmult c1 c3.
    Compute cmult c2 c2.
    Compute cmult c2 c3.
    Compute cmult c1 c1.
    Compute cmult c2 c0.
    Compute cmult c0 c3.
    (* ceq0(n) = {si n =0 true sinon false}:λ n .λ x y . n (λ z.y ) x*)
    Definition cseq0 := fun (n:cnat)=> fun (x:T) (y:T)=> n (fun (z:T)=>y) x.
    Compute cseq0 c0.
    Compute cseq0 c1.
    Compute cseq0 c3.
  End type_nat.
