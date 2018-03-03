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
"∃x. Φ x ⟶ (∃z. ∀y. ((O y z) ⟷ (Φ x ∧ O y x)))"
axiomatization where sum_axiom:
 "Φ x = (x=a ∨ x=b)"

theorem "∃z. (P x z ∧ P y z)⟶(∃z. ∀w. ((O w x) ∨ (O w y)))"
proof-
  from axiom_schema sum_axiom have "∃x. (x=a ∨ x=b)⟶(∃z. ∀y. ((O y z)⟷((x=a ∨ x=b)∧ O y x)))" by auto
  from this have "∃x.(x=a ∨ x=b)⟶(∃z. ∀y. ((O y z) ⟷ ((x=a ∨ x=b) ∧ O y x)))" using axiom_schema by blast
  then have "∃x.(x=a ∨ x=b)" by auto
  hence "∃x.(∃z. ∀y.((O y z) ⟷ ((x=a ∨ x=b) ∧ O y x)))" by auto
  then have "∀y.(∃x.(x=a ∨ x=b) ∧ O y x)⟶(O y a ∨ O y b)" by auto
  from this have "∀y.(∃z.((O y z)⟷(O a y ∨ O b y)))" by blast
  hence "∃z. (P x z ∧ P y z)⟶(∃z. ∀w. ((O w x) ∨ (O w y)))" by auto
  show "∃z. (P x z ∧ P y z)⟶(∃z. ∀w. ((O w x) ∨ (O w y)))" by auto
qed

end
