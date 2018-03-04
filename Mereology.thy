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
axiomatization where product_axiom :
"Φ x = (P x a ∧ P x b)"

theorem "∃z.(P x z ∧ P y z)⟶(∃z.(∀w.(P w z ⟷(P w x ∨ P w y))))"
proof-
  from product_axiom axiom_schema have "∃x.((P x a ∧ P x b)⟶(∀y.(∃z.(O y z) ⟷((P x a ∧ P x b)∧ O y x))))" by blast
  have "∃x.(P x a ∧ P x b)" using P_is_reflexive product_axiom by blast
  hence "(∀y.(∃z.(O y z) ⟷(∃x.(P x a ∧ P x b)∧ O y x)))" using product_axiom by blast
  from this have "∀y.∃z.(P y z)⟷(∃x.(P x a ∧ P x b)∧ O y x)" using P_is_reflexive by blast
  from this have "∀y.∃z.(P y z)⟷(∃x.(P x a ∧ P x b)∧ P y x)" by meson
  from this have "∀y.∃z.(P y z)⟷(∃x.(P x a ∧ P y x)∧(P x b ∧ P y x))" by fastforce
  from this have "∀y.∃z.(P y z)⟷(P y a ∧ P y b)" by auto
  then have "O a b" using ‹∃x.(P x a ∧ P x b)› by auto
  from this have "∃z.(P a z ∧ P b z)" using product_axiom by blast
  hence "∃z.(P a z ∧ P b z)⟶ (∀y.(∃z.(P y z)⟷(P y a ∧ P y b)))" by auto
  hence "∃z.(P x z ∧ P y z)⟶(∃z.(∀w.(P w z ⟷(P w x ∨ P w y))))" using product_axiom by blast
  show "∃z.(P x z ∧ P y z)⟶(∃z.(∀w.(P w z ⟷(P w x ∨ P w y))))" using ‹∃z. P x z ∧ P y z ⟶ (∃z. ∀w. P w z = (P w x ∨ P w y))› by blast
qed

end
