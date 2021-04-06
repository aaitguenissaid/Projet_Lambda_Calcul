Section type_booleen.
  (*1.2.1*)
  Variable T : Set. 
  Definition cbool := T -> T -> T.
  Definition ctr : cbool := fun x y => x.
  Print ctr.
  Definition cfa : cbool := fun x y => y.
  Print cfa.
  Definition cif: cbool -> T ->T ->T :=fun (b : cbool) (t : T) (e : T) =>b t e.
  Variables F V : T.
  Compute cif ctr V F.
  Compute cif cfa V F.
  Definition cand:cbool->cbool->cbool := fun (a:cbool) (b:cbool) =>fun (x:T) (y:T) =>a (b x y) y.
  Compute cand ctr ctr.
  Compute cand ctr cfa.
  Compute cand cfa cfa.
  Compute cand cfa ctr.
  Definition cor :cbool->cbool->cbool:= fun (a:cbool) (b:cbool) =>fun (x:T)(y:T)=>a x (b x y).
  Compute cor ctr ctr.
  Compute cor ctr cfa.
  Compute cor cfa cfa.
  Compute cor cfa ctr.
  Definition cnot:cbool->cbool := fun (b:cbool) => fun (x:T) (y:T)=> b y x.
  Compute cnot ctr.
  Compute cnot cfa.
End type_booleen.
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
End type_de_identite_polymorphe.
Section booleens_avec_typage_polymorphe.
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
End booleens_avec_typage_polymorphe.

Section structures_de_données_couples_et_choix.
  Section couples.
    Definition pprod_nb : Set := forall T: Set, (nat -> pbool -> T)->T.
    Definition pcpl_nb:= fun (a:nat)(b:pbool) =>fun T:Set => fun (k:nat -> pbool -> T) =>k a b.
    Definition pprod_bn : Set := forall T: Set, (pbool -> nat -> T)->T.
    Definition pcpl_bn:= fun (a:pbool)(b:nat) =>fun T:Set => fun (k:pbool -> nat ->  T)=>k a b.
    Definition pprod_nb_to_bn := fun (z:pprod_nb)=>fun T:Set => fun (k:pbool -> nat -> T) =>
      k  ((fun (q:pprod_nb)=> q (pbool)(fun (x:nat)(y:pbool)=>y)) z) ((fun (q:pprod_nb)=> q (nat)(fun (x:nat)(y:pbool)=>x)) z).
    Compute pcpl_nb 1 ptr.
    Compute pcpl_bn ptr 1.
    Compute pprod_nb_to_bn (pcpl_nb 1 ptr) .
    Definition pprod :Set->Set->Set:= fun A B => forall T:Set, (A->B->T)->T.
    Definition pcpl:= fun (A:Set) (B:Set) => fun (a:A) (b:B) =>fun T:Set=>fun (k:A->B->T) =>k a b.
    Compute pcpl_nb 1 ptr.
    Compute pcpl nat pbool 1 ptr.
    Compute pcpl_bn ptr 1.
    Compute pcpl pbool pbool ptr ptr.
  End couples.
  Section choix.
    Definition psom (A B: Set) : Set := forall T:Set, (A->T)->(B->T)->T.
    Definition inj1 (A B: Set) : A -> psom A B := fun u => fun T:Set => fun (q:A->T)=>fun (w:B->T)=> q u.
    Definition inj2 (A B: Set) : B -> psom A B := fun v => fun T:Set => fun (q:A->T)=>fun (w:B->T)=> w v.
    Compute inj1 pbool (pprod pbool pbool) pfa .
(*     Definition toutvr : psom pbool (pprod pbool pbool) -> pbool := fun u:(psom pbool (pprod pbool pbool))=>  *)
(*     fun T:Set =>fun q:T=>fun w:T=> u (T->T->T) q w. 
(*     Compute toutvr (inj1 pbool (pprod pbool pbool) ptr).*)  *)
   End choix.  
End structures_de_données_couples_et_choix.
Section entiers_de_church.
  Definition pnat : Set := forall T: Set, (T->T)->(T->T).
  Definition p0:= fun T:Set => fun (f:T->T)=>fun(x:T)=>x.
  Definition pS:= fun n:pnat =>fun T:Set => fun (f:T->T)=>fun(x:T) =>f (n T f x).
  Compute p0.
  Compute pS p0.
  Definition p1:= pS p0. 
  Definition p2:= pS p1.
  Definition p3:= pS p2.
  Definition padd:= fun (n:pnat)(m:pnat) =>fun T:Set => fun (f:T->T)=>fun(x:T) => n T f (m T f x).
  Compute padd p2 p2.
  Definition pmult:= fun (n:pnat)(m:pnat) =>fun T:Set => fun (f:T->T)=>n T (m T f ).
  Compute pmult p3 p2.
  Definition peq0:= fun (n:pnat)=>fun T:Set =>fun(x:T) =>fun(y:T) =>n T (fun (z:T)=> y) x.   
  Compute peq0 p1.
  Compute peq0 p0.
  Definition piter:= fun (n:pnat)=>fun T:Set => fun (f:T->T)=>fun(x:T) => n T f x.
(*   Definition ppred1 := fun (n:pprod)=>·\k·k (snd c) (csucc(snd c)). *)
(*   Definition cpred := \n· fst (iter n cpred1 (cp c0 c0) ). *)
End entiers_de_church.
Section Listes.
  
End Listes.
