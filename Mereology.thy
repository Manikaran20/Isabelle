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


theorem "∃z. (P x z ∧ P y z)⟶(∃z. ∀w. ((O w x) ∨ (O w y)))"
proof-
  have "∃x.(x=a ∨ x=b)⟶(∃z. ∀y. ((O y z) ⟷ ((x=a ∨ x=b) ∧ O y x)))" using axiom_schema by blast
  then have "∃x.(x=a ∨ x=b)" by auto
  hence "∃x.(∃z. ∀y.((O y z) ⟷ ((x=a ∨ x=b) ∧ O y x)))" by auto
  then have "∀y.(∃x.(x=a ∨ x=b) ∧ O y x)⟶(O y a ∨ O y b)" by auto
  from this have "∀y.(∃z.((O y z)⟷(O a y ∨ O b y)))" by blast
  hence "∃z. (P x z ∧ P y z)⟶(∃z. ∀w. ((O w x) ∨ (O w y)))" by auto
  show "∃z. (P x z ∧ P y z)⟶(∃z. ∀w. ((O w x) ∨ (O w y)))" by auto
qed

theorem "∃z.(P z x ∧ P z y)⟶(∃z.(∀w.(P w z ⟷(P w x ∧ P w y))))"
proof-
  have "∃x.(P x a ∧ P x b)⟶(∃z.(∀y.(O y z ⟷((P x a ∧ P x b)∧ O y x))))" using axiom_schema by auto
  from this have "∃x.∀y.(P x a ∧ P x b)∧(O y x)⟶(∀y.(P y a ∧ P y b))" by simp
  hence "∃x.(P x a ∧ P x b)⟶(∃z.(∀y.(O y z ⟷(P y a ∧ P y b))))" using P_is_reflexive by blast
  have "∀y.∃z.(O y z)⟶P y z" using P_is_reflexive by blast
  hence "∃x.(P x a ∧ P x b)⟶(∃z.(∀y.(P y z ⟷(P y a ∧ P y b))))" by auto
  thus "∃z.(P z x ∧ P z y)⟶(∃z.(∀w.(P w z ⟷(P w x ∧ P w y))))" by auto
qed
end
