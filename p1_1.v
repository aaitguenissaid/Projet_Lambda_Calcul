

Definition ctr := \x y·x.
Definition cfa := \x y·y.
Definition cif := \b m n · b m n.
Definition cand := \ a b · (\ x y · a (b x y) y).
Definition cor := \a b ·\x y·a x(b x y).
Definition cor_cif :=\a b·\x y ·cif a x( b x  y).
Definition corp :=\a·a a.
Definition cnot := \ a· cif a cfa ctr .
Definition cnot_v2 := \ a· a cfa ctr .

Definition c0 := \f x·x.
Definition c1_1 :=\f x·f x.
Definition c2 :=\f x·f (f x).
Definition c3 :=\f x·f (f (f x)).
Definition c4 :=\f x·f (f (f (f x))).
Definition csucc := \n·\f x · f ( n f x).
Definition cadd := \n m ·\f x · n f ( m f x).
Definition cmult := \n m ·\f· n( m f).
Definition ceq0 :=\n·\x y·n(\z·y) x.

Definition cp := \ a b · \ k·k a b.
Definition kfst := \ x y· x.
Definition ksnd := \ x y· y.
Definition fst := \ x · x kfst.
Definition snd := \ x · x ksnd.
Definition ksumcoup := \x· (cadd (fst x) (snd x)).
Compute show_cbn(ksumcoup (cp c2 c2)).

Definition inj1 := \a b·a x.
Definition inj2 := \a b·b x.
Definition funcinj1inj2:=\a x· a (cmult x c2) (cnot x).
Compute show_cbn(funcinj1inj2 inj1 c2).
Compute show_cbn(funcinj1inj2 inj2 cfa).
(*Definition Some:= \f m n · m f.
Definition None:= \x y · y.
Definition osucc:= \x· y.*)

Definition iter := \n g x·n g x.
Definition cpred1 := \c·\k·k (snd c) (csucc(snd c)).
Compute show_cbn(cp c1_1 c2).
Compute show_cbn(fst (cpred1 (cp c1 c2))).
Compute show_cbn(snd (cpred1 (cp c1 c2))).
Definition cpred := \n· fst (iter n cpred1 (cp c0 c0) ).
Compute show_cbn(cpred c3).
Definition cpred_v2 := \n· fst ( n cpred1 (cp c0 c0) ).
Compute show_cbn(cpred_v2 c3).


Definition cfonc := \f n· cif (ceq0 n) c1_1 (cmult n (f f (cpred n))).
Definition cfact :=\x· cfonc cfonc x.
Compute red_cbn(cfact c3).
