theory Mereology
imports Main
begin
typedecl μ 
consts P :: "μ⇒μ⇒bool"
axiomatization where P_is_antisymmetric:
"(P x y)∧(P y x) ⟶ (x = y)"  
axiomatization where P_is_reflexive:
"P x x"
axiomatization where P_is_transitive:
"∃z. (P x y ∧  P y z)⟶ P x z"

abbreviation overlap :: "μ⇒μ⇒bool" ("O") where
"O x y ≡ ∃z. (P z x ∧ P z y)"


axiomatization where axiom_schema:
"∃x. Φ x ⟶ (∃z. ∀y. ((O y z) ⟷ (φ x ∧ O y x)))"

axiomatization where sum_axiom :
"Φ x = (x=a ∨ x=b)"

lemma "∃z. (P x z ∧ P y z)⟶(∃z. ∀w. ((O w x) ∨ (O w y)))"
proof-
  from axiom_schema sum_axiom have "∃x.(x=a ∨ x=b)⟶(∃z.∃x. ∀y. ((O y z)⟷((x=a ∨ x=b)∧ O y x)))" by auto
  have "Φ x = (x=a ∨ x=b)" using sum_axiom by blast
  hence "∃x. (x=a ∨ x=b)" by auto
  from this have "(∃z.∃x.∀y.(O y z ⟷ ((x=a ∨ x=b)∧ O y x)))" using  ‹∃x. (x=a ∨ x=b)⟶(∃z.∀y. ((O y z)⟷((x=a ∨ x=b)∧ O y x)))› by auto
  then have "((x=a ∨ x=b)∧O y x)⟶(O y a ∨ O y b)" by auto
  moreover  have "(∃z. ∀y. ((O y z)⟷(O a y ∨ O b y)))" by metis
  ultimately show "∃z. (P x z ∧ P y z)⟶(∃z. ∀w. ((O w x) ∨ (O w y)))" by auto
qed

end





