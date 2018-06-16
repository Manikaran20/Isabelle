theory Mereotopology
  imports Main Mereology
begin

section {* theories *}

subsection {* ground Topology *}

text{* ground Topology (T)- "It introduces Connectedness as primitive relation between Individuals
and it's parts. Since, Connections seem to be sharing relations, It is assumed to be
reflexive and symmetric both but not transitive" @{cite "casati_parts_1999"} *}

locale C =
  fixes C :: "i⇒i⇒bool" ("C")--"Connectedness"
 assumes R: "C x x" -- "reflexivity of connectedness "
 and S: "C x y ⟶ C y x" -- "symmetry of connectedness"


locale T = C  
begin

definition E :: "i⇒i⇒bool" ("E")--"Enclosed- since relations are shared with parts, It is assumed 
to be enclosed in it"
  where "E x y ≡ ∀z.(C z x ⟶ C z y)"
end

lemma (in T) "E x x" 
  by (simp add: E_def)
lemma (in T) "((E x y) ∧ (E y z))⟶(E x z)" 
  by (simp add: E_def)
lemma (in T) "((E x Y) ∧ (E y x))⟶(x=y)" nitpick oops

  subsection{* ground mereotopology *}
  text{*ground mereotopology(MT) It envolves the connection between Mereology and Topology *}

locale MT = M + T +
  assumes MTC : "(P x y) ⟶ (E x y)" --" Monotonicity "

begin
 
text{* Since, MTC' immediately implies that mereological overlap is a form of connection. but, when 
we tried to prove that, it failed. This led us to define EC(external connection)- connection that
doesn't share parts which is symmetric but neither reflexive nor transitive *}

definition EC :: "i⇒i⇒bool" ("EC")--"External connection"
  where
"EC x y ≡ (C x y) ∧ ¬(O x y)"

text{* The following definitions are implied on the basis of, The types of parts any individual can 
consist of regarding connectedness *}

definition IP :: "i⇒i⇒bool" ("IP")--"Internel connectedness- It implies to those parts which
also share the relations and also are the connected parts"
  where
"IP x y ≡ P x y ∧ (∀z.(C z x)⟶(O z y))"

definition TP :: "i⇒i⇒bool" ("TP")--"Tangential part"
  where
"TP x y ≡ P x y ∧ ¬(IP x y)"

definition IO :: "i⇒i⇒bool" ("IO")--"Internal overlap"
  where
"IO x y ≡ ∃z.(IP z x ∧ IP z y)"

definition TO :: "i⇒i⇒bool" ("TO")--"Tangential overlap"
  where
"TO x y ≡ O x y ∧ ¬(IO x y)"

definition IU :: "i⇒i⇒ bool" ("IU")--"Internal underlap"
  where
"IU x y ≡ ∃z.(IP x z ∧ IP y z)"

definition TU :: "i⇒i⇒bool" ("TU")--"Tangentially underlap"
  where
"TU x y ≡ U x y ∧ ¬(IU x y)"

text{* More generally, For each mereological predicate "φ" we can define corresponding
 mereotopological predicates replacing "Iφ" and "Tφ" by substituting IP and TP (respectively)
for each occurrence of 'P' in the definies.@{cite "casati_parts_1999" } P-55,4.2.for example.. *}

definition IPP :: "i⇒i⇒bool" ("IPP")--"internal proper part"
  where
"IPP x y ≡ IP x y ∧ ¬(IP y x)"

(*
definition TPP :: "i⇒i⇒bool" ("TPP")--"tangential proper part"
  where
"TPP x y ≡ TP x y ∧ ¬( TP y x)"
text{* just like that all the predicates, defined in the mereology subsection, can be converted to 
mereotopological predicates *}
*)

text{* As we go through the theory of mereotopology,concept of self connectedness begins to rise; A
cat's tail is connected to the rest of it's body-there is nothing separating them. And surely
the two don't overlap-there are no common parts. *}

text{* Below we define the predicate for self connectedness that makes the difference between solod
wholes (such as table or a cup) and scattered wholes (such as bikini or a broken glass; to define self
connectedness we say that x is self connected if any two parts that make the whole of x are 
connected to each other: *}

definition SC :: "i⇒bool" ("SC")--"Self-connectedness"
  where
"SC x ≡ ∀y.∀z.(∀w.(O w x ⟷ O w y ∨ O w z)⟶C y z)"
  
lemma (in MT) "(P x y)⟶ (∀z.(C x z ⟶ C z y))"
 using E_def MTC S by blast

lemma (in MT) "O x y ⟶ C x y"
  using E_def MTC O_def R S by blast


end 

locale CMT= CM + MT +
  assumes "C x y ⟶ U x y "

begin

lemma (in CMT) SCC: "(C x y ∧ SC x ∧ SC y) ⟶ (∃z.(SC z ∧ (∀w.(O w z ⟷ O w x ∨ O w y))))"
proof
  fix p q r s 
  assume "C x y ∧ SC x ∧ SC y"
  hence "∀w.(O w x ⟷ O w p ∨ O w q)⟶C p q"
    using SC_def by blast
  hence "∀w.(O w y ⟷ O w r ∨ O w s) ⟶ C r s"
    using SC_def ‹C x y ∧ SC x ∧ SC y› by auto
    hence "∀w.(∃p.∃q.∃r.∃s.(O w p ∨ O w q)∧(O w r ∨ O w s))"sledgehammer
      using T9 by auto
    hence "∀w.(∃p.∃q.∃r.∃s.( C p q ∧ C r s))"
      using ‹C x y ∧ SC x ∧ SC y› by blast
  hence    "((∀w.(O w x ⟷ O w p ∨ O w q)⟶C p q)) ∧  ((∀w.(O w y ⟷ O w r ∨ O w s)⟶C r s))"
    using ‹∀w. O w x = (O w p ∨ O w q) ⟶ C p q› ‹∀w. O w y = (O w r ∨ O w s) ⟶ C r s› by blast
  hence "∃z.∀w.(C z p ∨ C z q)∧(C z r ∨ C z s)"
    by (metis O_def SC_def ‹C x y ∧ SC x ∧ SC y›)
  hence "∃z.(SC z)"
    using ‹C x y ∧ SC x ∧ SC y› by auto
  hence "∃z.(SC z ∧ C z x ∧ C z y)" 
      using R ‹C x y ∧ SC x ∧ SC y› by blast
    hence "∃z.∃p.∃r.∃q.∃s.(P p x ∧ P q x ∧ P r y ∧ P s y)∧((C z p ∨ C z q)∧(C z r ∨ C z s))∧ SC z⟶(((∀w.(O w z ⟷ O w x ∨ O w y))))"
   using AS by blast
  hence "∃p.∃r.∃q.∃s.∃z.(P p x ∧ P q x ∧ P r y ∧ P s y)∧((C z p ∨ C z q)∧(C z r ∨ C z s))∧ SC z"sledgehammer
    by (smt R T3 ‹C x y ∧ SC x ∧ SC y›)
  hence "∃z.(∀w.(O w z ⟷ O w x ∨ O w y))"
    using CMT.axioms(3) CMT_axioms CMT_axioms_def SC ‹C x y ∧ SC x ∧ SC y› by auto
  hence " (∃z.(SC z ∧ (∀w.(O w z ⟷ O w x ∨ O w y))))"
    by (metis (mono_tags, hide_lams) SC_def ‹C x y ∧ SC x ∧ SC y›)
  hence  "(C x y ∧ SC x ∧ SC y) ⟶ (∃z.(SC z ∧ (∀w.(O w z ⟷ O w x ∨ O w y))))"
    by blast
  have "(C x y ∧ SC x ∧ SC y)"
    by (simp add: ‹C x y ∧ SC x ∧ SC y›)
  hence "(∃z.(SC z ∧ (∀w.(O w z ⟷ O w x ∨ O w y))))"
    using ‹∃z. SC z ∧ (∀w. O w z = (O w x ∨ O w y))› by blast
  thus "(∃z.(SC z ∧ (∀w.(O w z ⟷ O w x ∨ O w y))))" 
    by blast
qed

end

locale CEMT = CEM + T 

begin

definition SC :: "i⇒bool" ("SC") where
"SC x ≡ ∀y.∀z.(x = y ❙+ z ⟶ C y z)"

lemma (in CEMT) "C x y ∧ SC x ∧ SC y ⟶ SC (x❙+y)"nitpick oops

end

locale GEMT = GEM +MT

begin
lemma (in GEMT) "C x y ⟶ U x y" 
  using EU by blast

definition i :: "(i⇒i)" ("❙i")--"interior"
  where
"❙i x ≡ σ z. (IP z x)"

definition e :: "(i⇒i)" ("❙e")--"exterior"
  where
"❙e x ≡ ❙i (❙¬ x)"

definition c :: "i⇒i" ("❙c")--"closure"
  where
"❙c x ≡ ❙¬ (❙e x)"

definition b :: "i⇒i" ("❙b")--"boundary"
  where
"❙b x ≡ ❙¬ (❙i x ❙+ ❙e x)"

end
text{* Note that all the integrated operators in GEMT(GEM+MT) are distinguished by bold font *}

text{* These integrated operators are partially defined, unless we assume the existence of a null 
individual that is part of everything *}

text{* Even so,in GEMT these operators are rather well-behaved. *}

text{* In particular, we can get closer to standard topological theories by supplementing the axiom
of symmetry and reflexivity and the monotonicity axiom of connectedness, with the mereologized 
analogues of the standard kuratowski (1922) axioms for topological closure@{cite "casati_parts_1999"}
, P.59 .*}

text {* Equivalently, we could use the axioms for the interior operator @{cite "casati_parts_1999"}
p.59, . *}

locale GEMTC = GEMT + 
  assumes Inclusion : "P (❙i x) x" 
and Idempotence : "❙i (❙i x) = ❙i x"
and Product : "❙i (x ❙× y) = ❙i x ❙× ❙i y"
and "P x (❙c x) "
and "❙c (❙c x) = ❙c x "
and "❙c (x ❙+ y) = ❙c x ❙+ ❙c y"
and "❙b x = ❙b (❙¬x)"
and "❙b (❙b x) = ❙b x"
and "❙b (x ❙× y) ❙+ ❙b (x ❙+ y) = ❙b x ❙+ ❙b y"
lemma (in GEMTC) "C x y ⟷ O x (❙c y) ∨ O (❙c x) y"
proof
  assume "C x y"
  hence "U x y"
    by (simp add: EU)
  hence "P (❙i x) (❙c x) "sledgehammer
    by (metis GEMTC.axioms(2) GEMTC_axioms GEMTC_axioms_def T)
  hence "C (❙i x) (❙c x)"
    using E_def MTC R by blast
  hence "U (❙i x) (❙c x)" 
    by (simp add: EU)
  hence "P (❙i x) x ∧ C x y"
    using Inclusion ‹C x y› by blast
  hence "C (❙c x) y"
    by (metis E_def GEMTC.axioms(2) GEMTC_axioms GEMTC_axioms_def MTC S)
  hence "C (❙c y) x " 
    by (metis (no_types, hide_lams) E_def GEMTC.axioms(2) GEMTC_axioms GEMTC_axioms_def MTC S ‹❙i x ❙≤ x ∧ C x y›)
  hence "C (❙¬(❙e y) ) x ∧ C y (❙¬(e y) )"
    by (metis C.R C_axioms E_def GEMTC.axioms(2) GEMTC_axioms GEMTC_axioms_def MTC c_def)
  hence "C (❙¬(❙i (❙¬y) ) ) x  ∧  C y (❙¬(❙i (❙¬ x) ) ) "
    using GEMT.c_def GEMT.e_def GEMT_axioms S ‹C (❙c x) y› by auto
  hence "P (σ z .(IP z x)) (❙c x)"
    using ‹❙i x ❙≤ ❙c x› i_def by auto
  hence "P z (❙i x) ⟶ O z x"
  proof -
    show ?thesis
      using T T11 ‹❙i x ❙≤ x ∧ C x y› by blast
  qed
  hence "O (❙c x) x"
    using O_def ‹❙i x ❙≤ ❙c x› ‹❙i x ❙≤ x ∧ C x y› by blast
  hence "P x (❙c x) ∧ P (❙i x) (❙c x) "
    using GEMTC.axioms(2) GEMTC_axioms GEMTC_axioms_def ‹❙i x ❙≤ ❙c x› by blast
  hence "P (❙e x) (❙¬ x)"
    by (simp add: Inclusion e_def)
  hence "P (❙¬ x) z ⟶ O z (❙e x)"
    using T10 T13 by blast
  hence "∃p.(P x p ∧ P y p)"
    using U_def ‹U x y› by auto
  hence "∃p.(P (❙c x) p ∧ P (❙c y) p )" 
    using U by blast
  assume "¬ O x (❙c y)"
  hence "∃p.(P x (❙c x) ∧ P x p ⟶ ¬ O p (❙e x) )"
    using O_def by blast
  hence "∃p.(P x p ∧ P y p ∧ P x (❙c x) ∧ P y (❙c y) ⟶ ¬ O p (❙e x) ∧ ¬ O p (❙e y) ) "
  proof -
    show ?thesis
      using O_def ‹∃p. x ❙≤ ❙c x ∧ x ❙≤ p ⟶ ¬ O p (❙e x)› by blast
  qed
  hence "∃p.(P x p ∧ P y p ∧ P x (❙c x) ∧ P y (❙c y) )"
    by (metis GEMTC.axioms(2) GEMTC_axioms GEMTC_axioms_def ‹∃p. x ❙≤ p ∧ y ❙≤ p›)
  hence "P z (❙e x) ⟶ O z (❙¬ x)"
    using T T11 ‹❙e x ❙≤ ❙¬ x› by blast
  hence "P z (❙c x) ⟷ ¬ O z (❙e x) "
    by (metis CCP GEMT.c_def GEMT_axioms T10 ‹❙e x ❙≤ ❙¬ x› ‹¬ O x (❙c y)›)
  hence " ¬ O x (❙e x) "
    using CCP T10 ‹❙e x ❙≤ ❙¬ x› ‹¬ O x (❙c y)› by blast



 



