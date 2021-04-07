(*Sidorets Kirill et Ait gueni ssaid Abderrahmane*)
Require Import untypedLC. 
(* 1.1 λ-calcul non typé *)

  (* 1. Booléens (codage des constantes et des opérations de base)   *)
  (*booléens de Church vrai: λx y.x*)
  Definition ctr := \x y·x. 
  (*booléens de Church faux: λx y.y*)
  Definition cfa := \x y·y.
  (*if b then m else n : λ b m n .b m n*)
  Definition cif := \b m n · b m n.
  (* a and  b : λ a b.λx y. a (b x y) y *)
  Definition cand := \ a b · (\ x y · a (b x y) y).
  (* a or  b : λ a b.λx y. a x (b x y) *)
  Definition cor := \a b ·\x y·a x(b x y).
  (* a or  b : λ a b.λx y. cif a x (b x y) *)
  Definition cor_cif :=\a b·\x y ·cif a x( b x  y).
  (*Dérivée à partir de la version non factorisée *)
  Definition cor' :=\a·a a.
  (*not a ( if a then {false} else {true}):λ a.cif a cfa ctr*)
  Definition cnot := \ a· cif a cfa ctr .
  (*not a :λ a.a cfa ctr*)
  Definition cnot' := \ a· a cfa ctr .

  
  Compute show_cbn(cif ctr a b).
  Compute show_cbn(cif cfa a b).
  Compute show_cbn(cif (cor_cif cfa (cnot ctr)) a b).
  Compute show_cbn(cor_cif cfa cfa a b).
  Compute show_cbn(cif( cor' (cand cfa ctr) cnot' cfa) a b).
  

  (* 2. Entiers naturels (codage de quelques constantes, 
  des opérations successeur, addition et multiplication, et 
  du test à 0)*)
  (*Codage des entiers naturels en λ-calcul inventé par Alonzo Church *)
  (* 0 :λ f x .x *)  
  Definition c0 := \f x·x. 
  (* 1 :λ f x . f x *)  
  Definition c1 :=\f x·f x.
  (* 2 :λ f x . f (f x) *)  
  Definition c2 :=\f x·f (f x).
  (* 3 :λ f x . f (f (f x)) *)  
  Definition c3 :=\f x·f (f (f x)).
  (* 4 :λ f x . f (f (f (f x))) *)  
  Definition c4 :=\f x·f (f (f (f x))).
  (* csucc(n)=n+1 : λ n.λ f x. f (n f x)*)
  Definition csucc := \n·\f x · f ( n f x).
  (* cadd (a,b)=a+b :λ n m.λ f x. n f (m f x) *)
  Definition cadd := \n m ·\f x · n f ( m f x).
  (* cmult (a,b)=a*b :λ n m.λ f . n (m f) *)
  Definition cmult := \n m ·\f· n( m f).
  (* ceq0(n) = {si n=c0 true sinon false}:λ n .λ x y . n (λ z.y ) x*)
  Definition ceq0 :=\n·\x y·n(\z·y) x.
  

  Compute (show_cbn (csucc c4)).
  Compute (show_cbn (cadd c2 c3)).
  Compute (show_cbn (cmult c2 c4)).
(* l'expression ceq0 retourne a si true sinon elle retourne b  *)
  Compute (show_cbn ((ceq0 c0) a b)).
  Compute (show_cbn ((ceq0 c3) a b )).
  
  (* 3. Couples*)
  (*La fonction cpl prend deux arguments(a,b) et construit un couple : λa b.λk.k a b *)
  Definition cpl := \ a b · \ k·k a b. 
  (*Prends en argument un couple, retournent premier élément : λ x y. x*)
  Definition kfst := \ x y· x.
  (*Prends en argument un couple, retournent deuxième élément : λ x y. y*)
  Definition ksnd := \ x y· y.
  (*fst(c) = x ou c - un couple x - premier élément de c  : λ c. c kfst *)
  Definition fst := \ x · x kfst.
  (*fst(c) = y ou c - une cople x - deuxième élément de c  : λ c. c ksnd *)
  Definition snd := \ x · x ksnd.

  Compute (show_cbn (fst (cpl a b))).
  Compute (show_cbn (snd (cpl ctr cfa))).

  (*ksumcpl(cp(n,m))= n+m Renvoie la somme des éléments d'une couple 
  :λx.(cadd (fst x) (snd x)) *)
  Definition ksumcpl := \x · (cadd (fst x) (snd x)).
  Compute show_cbn(ksumcpl (cpl c2 c3)).

  (*4. Structure de choix (inj1, inj2, donnée optionnelle).*)
  (*Constructeur structure de choix a partir du premier élément : λ a b. a x *)
  Definition inj1 := \a b · a x. 
  (*Constructeur structure de choix a partir du deuxième élément : λ a b. b x *)
  Definition inj2 := \a b · b x.

  Compute show_cbn(inj1 f g).
  Compute show_cbn(inj2 f g).
  (*Fonction prenant en argument une donnée qui est soit un entier n (emballé par
  inj1) soit un booléen b (emballé par inj2) et qui rend le double de n dans le 
  premier cas, la négation de b dans le second *)
  Definition funcinj1inj2:=\a x · a (cmult x c2) (cnot x).
  Compute show_cbn(funcinj1inj2 inj1 c3).
  Compute show_cbn(funcinj1inj2 inj2 ctr).

  (* La donnée optionnelle correspond à un choix entre une donnée (Some x) ou 
  son absence (None). Elle se représente avec une continuation à un argument 
  et une continuation à zéro argument. Coder en Coq les injections Some et None,
  puis une fonction osucc prenant en argument un entier optionnel (Some n ou None)
  et rendant un entier optionnel qui est Some (n+1) dans le premier cas et Some 0
  dans le second *)
  Definition Some:= \f m n · m f. 
  Definition None:= \x y · y. 
  Definition osucc:= \a b · a b csucc c0.
  Compute show_cbn(osucc Some c3).
  Compute show_cbn(osucc None).

  (* 5. Prédécesseur (cpred; cpredo en bonus)*)
  (*la fonction iter qui prend un entier de Church n, une fonction g et
  un argument x et qui applique n fois la fonction g sur x. *)
  Definition iter := \n g x · n g x.
  (*  la fonction cpred1 qui à partir d’un couple λk.k x y donné en
  argument rend le couple λk.k y (csucc y).*)
  Definition cpred1 := \c · \k · k (snd c) (csucc(snd c)).
  Compute show_cbn(cpl c1 c2).
  Compute show_cbn(fst (cpred1 (cpl c1 c2))).
  Compute show_cbn(snd (cpred1 (cpl c1 c2))).
  Compute show_cbn(cpred1 (cpl c1 c2)).
  (* Pour définir le prédécesseur sur les entiers de Church, on utilise les couples.
  L’idée est d’itérer n fois une fonction agissant sur des couples d’entiers. 
  Prenons une fonction g qui à partir de (x, y) donné en argument rend (y, y +1).
  Alors, en itérant n fois g sur (0, 0), on obtient (n −1,n) et il suffit d’extraire
  la première composante de ce couple. Si n est codé comme un entier de Church alors
  itérer n fois une fonction g sur un argument a est juste (n g a).*)
  Definition cpred := \n· fst (iter n cpred1 (cpl c0 c0) ).
  Compute show_cbn(cpred c3).
  Definition cpred_v2 := \n· fst ( n cpred1 (cpl c0 c0) ).
  Compute show_cbn(cpred_v2 c3).

  (*6. Factorielle*)
  (* cfonc -> f if(n==0) alors retourne 1 sinon n*f(n-1)  *)
  Definition cfonc := \f n· cif (ceq0 n) c1 (cmult n (f f (cpred n))). 
  (*cfact(3)=1*2*3=6 *)
  Definition cfact :=\x· cfonc cfonc x.
  Compute red_cbn(cfact c0).
  Compute red_cbn(cfact c1).
  Compute red_cbn(cfact c2).
  Compute red_cbn(cfact c3).