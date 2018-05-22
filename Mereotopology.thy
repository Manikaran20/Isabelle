theory Mereotopology
  imports Main
begin

section {* theories *}

subsection {* ground Mereology *}

typedecl i -- "type for individuals"

locale P =
  fixes P:: "i ⇒ i ⇒ bool" ("P")

begin

text {* The following relations are defined in terms of parthood @{cite "casati_parts_1999"}, p. 36-7: *}

definition PP:: "i ⇒ i ⇒ bool" ("PP") 
  where "PP x y ≡ P x y ∧ ¬ P y x" -- "proper parthood"
definition O:: "i ⇒ i ⇒ bool" ("O")
  where "O x y ≡ ∃ z.(P z x ∧ P z y)" -- "overlap"
definition D:: "i ⇒ i ⇒ bool" ("D")
  where "D x y ≡ ¬ O x y" -- "disjointness"
definition U:: "i ⇒ i ⇒ bool" ("U")
  where "U x y ≡ ∃ z.(P x z ∧ P y z)" -- "underlap"

text {* As are the following operations on individuals @{cite "casati_parts_1999"}, p. 43-5: *}

definition S:: "i ⇒ i ⇒ i" (infix "❙+" 52)
  where "x ❙+ y ≡ THE z. ∀ w. O w z ⟷ O w x ∨ O w y" -- "sum or fusion"
definition T:: "i ⇒ i ⇒ i" (infix "❙×" 53)
  where "x ❙× y ≡ THE z. ∀ w. O w z ⟷ O w x ∧ O w y" -- "product or intersection"
definition u:: "i" ("u")
  where "u ≡ THE z. ∀ w. P w z" -- "definition of the universe"
definition M:: "i ⇒ i ⇒ i" (infix "❙-" 51)
  where "x ❙- y ≡ THE z. ∀ w. O w z ⟷ O w x ∧ ¬ O w y" -- "difference"
definition C:: "i ⇒ i" ("❙¬")
  where "❙¬ x ≡ (u ❙- x)" -- "complement"

text {* And the operations of general sum and product @{cite casati_parts_1999}, p. 46:  *}

definition σ:: "(i ⇒ bool) ⇒ i" ("σ")
  where "σ F ≡ THE z. (∀ y. O y z ⟷ (∃ x. F x ∧ O x y))"
abbreviation σx:: "(i ⇒ bool) ⇒ i" (binder "σ" [8] 9)
  where "σ x. F x ≡ σ F" --  "general sum or fusion of the Fs"
definition π:: "(i ⇒ bool) ⇒ i" ("π")
  where "π F ≡ THE z. (∀ x. F x ⟶ P z x)" -- "general products @{cite casati_parts_1999}, p. 46"
abbreviation πx:: "(i ⇒ bool) ⇒ i" (binder "π" [8] 9)
  where "π x. F x ≡ π F"  --  "general sum or product of the Fs"

(*
definition OX:: "i ⇒ i ⇒ bool" ("OX")
  where "OX x y ≡ O x y ∧ ¬ x ❙≤ y"
definition UX:: "i ⇒ i ⇒ bool" ("UX")
  where "UX x y ≡ U x y ∧ ¬ y ❙≤ x"
definition PO:: "i ⇒ i ⇒ bool" ("PO" )
  where "PO x y ≡ OX x y ∧ OX y x"
definition PU:: "i ⇒ i ⇒ bool" ("PU")
  where "PU x y ≡ UX x y ∧ UX y x"
*)

text {* Note that the symbols for part, proper part, sum, product, difference and complement are
distinguished by bold font. *}

end

locale M = P + assumes R: "P x x" -- "reflexivity of parthood "
               and AS: "P x y ⟶ P y x ⟶ x = y" -- "antisymmetry of parthood"
               and T: "P x y ⟶ P y z ⟶ P x z" -- "transitivity of parthood"


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

definition IPP :: "i\<Rightarrow>i\<Rightarrow>bool" ("IPP")--"internal proper part"
  where
"IPP x y ≡ IP x y ∧ ¬(IP y x)"

definition TPP :: "i\<Rightarrow>i\<Rightarrow>bool" ("TPP")--"tangential proper part"
  where
"TPP x y ≡ TP x y ∧ ¬( TP y x)"

text{* just like that all the predicates, defined in the mereology subsection, can be converted to 
mereotopological predicates *}







