theory Mereotopology
  imports Main
begin

section {* theories *}

subsection {* ground Topology *}

typedecl i -- "type for individuals"
locale C =
  fixes C :: "i⇒i⇒bool" ("C")
begin

definition E :: "i⇒i⇒bool" (infix "E" 50)
  where "x E y ≡ ∀z.(C z x ⟶ C z y)"

end

locale R = C + assumes R: "C x x" -- "reflexivity of connectedness "
locale S = C + assumes S: "C x y ⟶ C y x" -- "symmetry of connectedness"

locale T = R + S
lemma (in T) "x E x" 
  by (simp add: E_def)
lemma (in T) "((x E y) ∧ (y E z))⟶(x E z)" 
  by (simp add: E_def)




