(*Sidorets Kirill et Ait gueni ssaid Abderrahmane*)
(* 2 Partie 2 : programmation de structures avancées en λ-calcul  *)
(* 2.1 Exemple simple : l’identité polymorphe *)
Section type_de_identite_polymorphe.
  Definition tid : Set := forall T: Set, T -> T.
  Definition id : tid := fun T:Set => fun x:T => x.
  Compute id bool true.
  Definition nbtrue1 := fun b =>
  match b with true => 1 | false => 0 end.
  Compute nbtrue1 true.
  Compute nbtrue1 false.
End type_de_identite_polymorphe.
(* 2.2 Booléens avec typage polymorphe *)
Section booleens_avec_typage_polymorphe.
  Definition pbool : Set := forall T: Set, T -> T -> T.
  Definition ptr : pbool := fun T:Set => fun (x:T) (y:T) => x.
  Definition pfa : pbool := fun T:Set => fun (x:T) (y:T) => y.
  (*not b ={si b== ptr alor pfa sinon ptr} : λb.ΛT.λ(x:T)(y:T).b T y x *)
  Definition pnot: pbool -> pbool := fun b: pbool => fun (T:Set)=>fun (x:T)(y:T) => b T y x.
  Compute pnot ptr.
  Compute pnot pfa.
  (*not b ={si b== ptr alor pfa sinon ptr} : λb.b(λx y.y)(λx y.x) *)
  Definition pnotv2: pbool -> pbool := fun b => fun T : Set => b(T->T->T)(fun x y => y)(fun x y => x).
  Compute pnotv2 ptr.
  Compute pnotv2 pfa.
  (*conjonction(a,b)= a et b : λa b.λ(x:T)(y:T).a T (b T x y) y *)
  Definition conjonction: pbool -> pbool -> pbool := fun (a:pbool) (b:pbool) => fun T:Set => fun (x:T) (y:T) => a T (b T x y ) y.  
  Compute conjonction pfa pfa.
  Compute conjonction pfa ptr.
  Compute conjonction ptr pfa.
  Compute conjonction ptr ptr.
  (*disjonction(a,b)= a ou b : λa b.λ(x:T)(y:T).a T x (b T x y) *)
  Definition disjonction: pbool -> pbool -> pbool := fun (a:pbool) (b:pbool) => fun T:Set => fun (x:T) (y:T) => a T x (b T x y ).  
  Compute disjonction pfa pfa.
  Compute disjonction pfa ptr.
  Compute disjonction ptr pfa.
  Compute disjonction ptr ptr.
  (*pbvn(b)=k si b == ptr then k=3 else k=5 :λb.b 3 5*)
  Definition pbvn: pbool -> nat := fun b => b (nat) 3  5 .
  Compute pbvn ptr.
  Compute pbvn pfa.
End booleens_avec_typage_polymorphe.
(* 2.3 Structures de données : couples et choix *)
Section structures_de_données_couples_et_choix.
  (* 2.3.1 Couples (produits de types) *)
  Section couples.
    (*pprod_nb couple (nat,pbool)  *)
    Definition pprod_nb : Set := forall T: Set, (nat -> pbool -> T)->T.
    (*pcpl_nb constructer de couple (nat,pbool) λa b.λk:pprod_nb. k a b  *)
    Definition pcpl_nb:= fun (a:nat)(b:pbool) =>fun T:Set => fun (k:nat -> pbool -> T) =>k a b.
    Compute pcpl_nb 1 ptr.
    (*pprod_bn couple (pbool,nat) *)
    Definition pprod_bn : Set := forall T: Set, (pbool -> nat -> T)->T.
    (*pcpl_bn constructer de couple (pbool,nat) λa b.λk:pprod_bn. k a b  *)
    Definition pcpl_bn:= fun (a:pbool)(b:nat) =>fun T:Set => fun (k:pbool -> nat ->  T)=>k a b.
    Compute pcpl_bn ptr 1.
    (*Construir couple pprod_bn apartir pprod_nb - pprod_nb_to_bn(pprod_nb(n,b))=pprod_bn(b,n)
    λ z.λk . k ((λq.q(λx y.y )) z) ((λq.q(λx y.x )) z)*)
    Definition pprod_nb_to_bn := fun (z:pprod_nb)=>fun T:Set => fun (k:pbool -> nat -> T) =>
      k  ((fun (q:pprod_nb)=> q (pbool)(fun (x:nat)(y:pbool)=>y)) z) ((fun (q:pprod_nb)=> q (nat)(fun (x:nat)(y:pbool)=>x)) z).
    Compute pprod_nb_to_bn (pcpl_nb 1 ptr) .
    (*pprod couple (type1,type2)*)
    Definition pprod :Set->Set->Set:= fun A B => forall T:Set, (A->B->T)->T.
    (*pcpl constructer de couple pprod :λa b.λk. k a b   *)
    Definition pcpl:= fun (A:Set) (B:Set) => fun (a:A) (b:B) =>fun T:Set=>fun (k:A->B->T) =>k a b.
    Compute pcpl_nb 1 ptr.
    Compute pcpl nat pbool 1 ptr.
    Compute pcpl_bn ptr 1.
    Compute pcpl pbool pbool ptr ptr.
  End couples.
  (* 2.3.2 Choix (sommes de types) *)
  Section choix.
    (*pprod type de struchture de choix*)
    Definition psom (A B: Set) : Set := forall T:Set, (A->T)->(B->T)->T.
    (*inj1 x rendent λk1k2.k1 x *)
    Definition inj1 (A B: Set) : A -> psom A B := fun u => fun T:Set => fun (q:A->T)=>fun (w:B->T)=> q u.
    Compute inj1 pbool (pprod pbool pbool) pfa .
    (*inj1 x rendent  λk1k2.k2 x *)
    Definition inj2 (A B: Set) : B -> psom A B := fun v => fun T:Set => fun (q:A->T)=>fun (w:B->T)=> w v.
    Compute inj2 pbool (pprod pbool pbool) (pcpl pbool pbool ptr pfa ) .
(*     Definition toutvr : psom pbool (pprod pbool pbool) -> pbool := fun u:(psom pbool (pprod pbool pbool))=>  *)
(*     fun T:Set =>fun q:T=>fun w:T=> u (T->T->T) (fun x y=>q (pbool->pbool->T) x y ) w.  *)
(*     Compute toutvr (inj1 pbool (pprod pbool pbool) ptr).*)  
   End choix.  
End structures_de_données_couples_et_choix.
(* 2.4 Entiers de Church avec typage polymorphe *)
Section entiers_de_church.
  (*pnat  type de entiers de Church *)
  Definition pnat : Set := forall T: Set, (T->T)->(T->T).
  (* p0 represante 0 dans entiers de Church *)
  Definition p0:= fun T:Set => fun (f:T->T)=>fun(x:T)=>x.
  (*pS(n)=n+1 : λ n . λ (f:T->T) (x:T) . f (n f x)*)
  Definition pS:= fun n:pnat =>fun T:Set => fun (f:T->T)=>fun(x:T) =>f (n T f x).
  Compute p0.
  Compute pS p0.
  (* p1 represante 1 dans entiers de Church (0+1)*)
  Definition p1:= pS p0. 
  (* p2 represante 2 dans entiers de Church *)
  Definition p2:= pS p1.
  (* p3 represante 3 dans entiers de Church *)
  Definition p3:= pS p2.
  (* padd (a,b)=a+b :λ n m.λ f x. n f (m f x) *)
  Definition padd:= fun (n:pnat)(m:pnat) =>fun T:Set => fun (f:T->T)=>fun(x:T) => n T f (m T f x).
  Compute padd p2 p2.
  (* pmult (a,b)=a*b :λ n m.λ f . n (m f) *)
  Definition pmult:= fun (n:pnat)(m:pnat) =>fun T:Set => fun (f:T->T)=>n T (m T f ).
  Compute pmult p3 p2.
  (* peq0(n) = {si n =0 true sinon false}:λ n .λ x y . n (λ z.y ) x*)
  Definition peq0:= fun (n:pnat)=>fun T:Set =>fun(x:T) =>fun(y:T) =>n T (fun (z:T)=> y) x.   
  Compute peq0 p1.
  Compute peq0 p0.
  (**)
  Definition piter:= fun (n:pnat)=>fun T:Set => fun (f:T->T)=>fun(x:T) => n T f x.
(*   Definition ppred1 := fun (n:pprod)=>·fun T:Set=> fun k=>·k T ((* snd *) c) (pS(snd c)). *)
(*   Definition cpred := \n· fst (iter n cpred1 (cp c0 c0) ). *)
End entiers_de_church.
Section Listes.
  
End Listes.