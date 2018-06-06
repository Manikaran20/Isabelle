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

begin

definition E :: "i⇒i⇒bool" ("E")--"Enclosed- since relations are shared with parts, It is assumed 
to be enclosed in it"
  where "E x y ≡ ∀z.(C z x ⟶ C z y)"

end

locale T = C + assumes R: "C x x" -- "reflexivity of connectedness "
               and S: "C x y ⟶ C y x" -- "symmetry of connectedness"


lemma (in T) "E x x" 
  by (simp add: E_def)
lemma (in T) "((E x y) ∧ (E y z))⟶(E x z)" 
  by (simp add: E_def)
lemma (in T) "((E x Y) ∧ (E y x))⟶(x=y)" nitpick oops

  subsection{* ground mereotopology *}
  text{*ground mereotopology(MT) It envolves the connection between Mereology and Topology *}

locale MT = M + T +
  assumes MTC : "(P x y) ⟶ (E x y)" --" Monotonicity "
  and MTC' :"(P x y)⟶ (∀z.(C x z ⟶ C z y))"

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


lemma (in MT) "P x y ⟶ C x y"
  using MTC' R by blast

lemma (in MT) "(P x y)⟶ (∀z.(C x z ⟶ C z y))"
  using MT.MTC' MT_axioms by blast

end 

locale CMT= CM + T +
  assumes "C x y ⟶ U x y "

begin

definition SC :: "i⇒bool" ("SC") where
"SC x ≡ ∀y.∀z.(∀w.(O w x ⟷ (O w y ∨ O w z))⟶C y z)"

lemma (in CMT) SCC: "(C x y ∧ SC x ∧ SC y) ⟶ (∃z.(SC z ∧ (∀w.(O w z ⟷ O w x ∨ O w y))))"
proof
  fix p q r s 
  assume "C x y ∧ SC x ∧ SC y"
  hence "∀w.(O w x ⟷ O w p ∨ O w q)⟶C p q"
    using SC_def by blast
  hence "∀w.(O w y ⟷ O w r ∨ O w s) ⟶ C r s"
    using CMT.SC_def CMT_axioms ‹C x y ∧ SC x ∧ SC y› by auto
    hence "∀w.(∃p.∃q.∃r.∃s.(O w p ∨ O w q)∧(O w r ∨ O w s))"
      using  CM.axioms(1) CM_axioms M.R O_def by blast
    hence "∀w.(∃p.∃q.∃r.∃s.( C p q ∧ C r s))"
      using ‹C x y ∧ SC x ∧ SC y› by blast
  hence    "((∀w.(O w x ⟷ O w p ∨ O w q)⟶C p q)) ∧  ((∀w.(O w y ⟷ O w r ∨ O w s)⟶C r s))"
    using CMT.SC_def CMT_axioms ‹C x y ∧ SC x ∧ SC y› by auto
  hence "∃z.∀w.(C z p ∨ C z q)∧(C z r ∨ C z s)"
    by (metis O_def SC_def ‹C x y ∧ SC x ∧ SC y›)
  hence "∃z.(SC z)"
    using ‹C x y ∧ SC x ∧ SC y› by auto
  hence "∃z.(SC z ∧ C z x ∧ C z y)" 
      using R ‹C x y ∧ SC x ∧ SC y› by blast
    hence "∃z.∃p.∃r.∃q.∃s.(P p x ∧ P q x ∧ P r y ∧ P s y)∧((C z p ∨ C z q)∧(C z r ∨ C z s))∧ SC z⟶(((∀w.(O w z ⟷ O w x ∨ O w y))))"
   using AS by blast
  hence "∃p.∃r.∃q.∃s.∃z.(P p x ∧ P q x ∧ P r y ∧ P s y)∧((C z p ∨ C z q)∧(C z r ∨ C z s))∧ SC z"
    using M.R M_axioms R ‹C x y ∧ SC x ∧ SC y› by blast
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

definition ix :: "(i⇒i⇒bool)⇒i" ("❙Φ")--"integrated sum operator"
  where
"❙Φ F ≡ THE z. (∀y. O y z ⟷(∃x. F z x ∧ O x y))"

definition i :: "(i⇒i⇒bool)⇒i" ("❙i")
  where
"❙i x ≡ ❙Φ IP "
