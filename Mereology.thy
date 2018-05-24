section {* Introduction *}

theory Mereology
imports Main
begin

text {* This is a presentation in Isabelle/HOL of \emph{Classical Extensional Mereology}. The
presentation is based on those in ``Parts'' by Peter Simons @{cite "simons_parts:_1987"}
and ``Parts and Places'' by Roberto Casati and Achille Varzi @{cite "casati_parts_1999"}.
Some corrections and important proofs are from @{cite "pontow_note_2004"} *}

text {* Please note that this is an extremely ROUGH DRAFT. *}

section {* Ground Mereology *}

text {* Ground Mereology (M) introduces parthood as a primitive relation amongst individuals.
It's assumed that parthood is a partial ordering relation - that is reflexive, symmetric and
transitive  @{cite "casati_parts_1999"}, p. 36:  *}

typedecl i -- "the type of individuals"

locale M =
  fixes P:: "i ⇒ i ⇒ bool" ("P")
  assumes R: "P x x" -- "reflexivity of parthood "
    and  AS: "P x y ⟶ P y x ⟶ x = y" -- "antisymmetry of parthood"
    and  T: "P x y ⟶ P y z ⟶ P x z" -- "transitivity of parthood"

begin

text {* The following relations are defined in terms of parthood @{cite "casati_parts_1999"}, p. 36-7: *}

definition PP:: "i ⇒ i ⇒ bool" ("PP") 
  where "PP x  y ≡ P x y ∧ ¬ (P y x)" -- "proper parthood"
definition O:: "i ⇒ i ⇒ bool" ("O")
  where "O x y ≡ ∃ z. P z x ∧ P z  y" -- "overlap"
definition D:: "i ⇒ i ⇒ bool" ("D")
  where "D x y ≡ ¬ O x y" -- "disjointness"
definition U:: "i ⇒ i ⇒ bool" ("U")
  where "U x y ≡ ∃ z. P x z ∧ P y z" -- "underlap"

text {* As are the following operations on individuals @{cite "casati_parts_1999"}, p. 43-5: *}

definition S:: "i ⇒ i ⇒ i" (infix "❙+" 52)
  where "x ❙+ y ≡ THE z. ∀ w. O w z ⟷ O w x ∨ O w y" -- "sum or fusion"
definition T:: "i ⇒ i ⇒ i" (infix "❙×" 53)
  where "x ❙× y ≡ THE z. ∀ w. O w z ⟷ O w x ∧ O w y" -- "product or intersection"
definition u:: "i" ("u")
  where "u ≡ THE z. ∀ w. P w z" -- "universe"
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

section {* Minimal Mereology *}

text {* Minimal mereology (MM) adds to ground mereology the axiom of weak supplementation
@{cite "casati_parts_1999"}, p. 39: *}

locale MM = M +
  assumes WS: "PP x  y ⟶ (∃ z. PP z y ∧ D z x)" -- "weak supplementation"

text {* Weak supplementation is sometimes stated with parthood rather than proper parthood
in the consequent. The following lemma in ground mereology shows that the two definitions
are equivalent, given anti-symmetry: *}

lemma (in M)  "(PP x y ⟶ (∃ z. PP z y ∧ D z x)) ⟷ (PP x y ⟶ (∃ z. P z y ∧ D z x))"
  by (metis AS D_def O_def PP_def R)

text {* The following two lemmas are weaker supplementation principles taken from Simons
@{cite "simons_parts:_1987"}, p. 27. The names \emph{company} and \emph{strong company}
are from Varzi's \emph{Stanford Encyclopedia of Philosophy} entry on mereology
@{cite "varzi_mereology_2016"}. *}

lemma (in MM)  C: "PP x y ⟶ (∃ z. z ≠ x ∧ PP z y)" by (metis WS D_def O_def R) -- "company"
lemma (in MM)  SC: "PP x y ⟶ (∃ z. PP z y ∧ ¬ P z x)" by (metis WS D_def O_def R) -- "strong company"

text {* Minimal Mereology is not strong enough to proved the \emph{Proper Parts Principle},
according to which if x has a proper part, and every proper part of x is a part of y, then
x is a part of y @{cite "simons_parts:_1987"} p. 28:  *}

lemma (in MM) PPP: "∃ z. PP z x ⟹ ∀ z. PP z x ⟶ P z y ⟹ P x y" -- "proper parts principle"
  nitpick [user_axioms]  oops

  text {* The proper parts principle is Simons way of expressing \emph{extensionality}, which is
not a theorem of Minimal Mereology either: *}

lemma (in M) E: "(∃ z. PP z x ∨ PP z y) ⟶ (∀ z. PP z x ⟷ PP z y) ⟶ x = y" -- "extensionality"
  nitpick oops

text {* The failure of weak supplementation to entail the proper parts principle or extensionality
motivates a stronger axiom, to which we turn in the next section.  *}

(*
lemma (in M)
  assumes PPP: "∃ z. PP z x ⟹ ∀ z. PP z x ⟶ P z y ⟹ P x y"
  shows E: "(∃ z. PP z x ∨ PP z y) ⟶ (∀ z. PP z x ⟷ PP z y) ⟶ x = y"
  using PPP AS PP_def by blast

lemma (in MM) 
 assumes E: "(∃ z. PP z x ∨ PP z y) ⟶ (∀ z. PP z x ⟷ PP z y) ⟶ x = y"
 shows PPP: "∃ z. PP z x ⟹ ∀ z. PP z x ⟶ P z y ⟹ P x y" 
  nitpick oops
*)

section {* Extensional Mereology *}

text {* Extensional Mereology (EM) adds the axiom of strong supplementation @{cite "casati_parts_1999"}, p. 39: *}

locale EM = M +
  assumes SS: "¬ (P x y) ⟶ (∃ z. P z x ∧ D z y)" -- "strong supplementation"

text {* Extensional Mereology (@{text "EM"} is so called because it entails the proper parts principle
@{cite "simons_parts:_1987"} p. 29: *}

lemma (in EM) PPP: "∃ z. PP z x ⟹ ∀ z. PP z x ⟶ P z y ⟹ P x y"
  by (metis SS D_def R O_def PP_def T)

text {* And thus extensionality proper @{cite "casati_parts_1999"} p. 40: *}

lemma (in EM)
 E: "(∃ z. PP z x ∨ PP z y) ⟶ (∀ z. PP z x ⟷ PP z y) ⟶ x = y" -- "extensionality"
  by (metis R O_def D_def AS PP_def SS)

text {* In the context of the other axioms, strong supplementation entails weak supplementation
@{cite "simons_parts:_1987"}, p. 29:  *}

lemma (in M) SStoWS:
  assumes SS: "⋀x. ⋀ y. ¬ (P x y) ⟶ (∃ z. P z x ∧ D z y)"
-- "assumes strong supplementation"
  shows WS: "⋀x. ⋀y. PP x y ⟶ (∃ z. PP z y ∧ D z x)"
-- "shows weak supplementation"
  by (metis AS D_def O_def PP_def R assms)

text {* But not vice versa:  *} 

lemma (in M) WStoSS:
  assumes WS: "⋀x. ⋀y. PP x y ⟶ (∃ z. PP z y ∧ D z x)"
-- "assumes weak supplementation"
  shows SS: "⋀x. ⋀ y. ¬ (P x y) ⟶ (∃ z. P z x ∧ D z y)"
-- "shows strong supplementation"
  nitpick oops

text {* So Extensional Mereology is stronger than Minimal Mereology @{cite "casati_parts_1999"} p. 43:  *}

sublocale EM ⊆ MM using T SS SStoWS by (metis MM.intro MM_axioms.intro M_axioms)
sublocale MM ⊆ EM nitpick oops

lemma (in MM)
  assumes PPP: "∃ z. PP z x ⟹ ∀ z. PP z x ⟶ P z y ⟹ P x y"
  shows SS: "¬ P x y ⟶ (∃ z. P z x ∧ D z y)" nitpick oops

(*
  text {* Two alternative formulations of the strong supplementation axiom, which are equivalent given
transitivity are @{cite "pontnow_note_2004"} p. 198: *}

lemma (in M) "((∀ z. P z x ⟶ O z y) ⟶ P x y) ⟷ (¬ P x y ⟶ (∃ z. P z x ∧ D z y))"
  using D_def by blast
lemma (in M)
"((∀ z. O z x ⟶ O z y) ⟶ P x y) ⟷ (¬ P x y ⟶ (∃ z. P z x ∧ D z y))"
  by (metis O_def D_def R T)

lemma (in M) assumes SS: "¬ P x y ⟶ (∃ z. P z x ∧ D z y)"
  shows "(∀ z. P z x ⟶ O z y) ⟶ P x y"
  using D_def SS by blast

lemma (in M) assumes "(∀ z. P z x ⟶ O z y) ⟶ P x y"
  shows "(∀ z. O z x ⟶ O z y) ⟶ P x y"
  using O_def R assms by blast

lemma (in M) assumes "(∀ z. O z x ⟶ O z y) ⟶ P x y" 
  shows SS: "¬ P x y ⟶ (∃ z. P z x ∧ D z y)"
  by (meson D_def O_def T assms)

lemma (in EM) "(∀ z. P z x ⟶ O z y) ⟶ P x y" using SS D_def by blast
lemma (in EM) "(∀ z. O z x ⟶ O z y) ⟶ P x y" by (metis SS T D_def O_def)

*)

section {* Closure Mereology *}

text {* Closure Mereology adds to Ground Mereology the axioms of sum closure and product closure
 @{cite "casati_parts_1999"} p. 43: *}

locale CM = M +
  assumes SC: "U x y ⟶ (∃ z. ∀ w. O w z ⟷ (O w x ∨ O w y))" -- "sum closure"
  assumes PC: "O x y ⟶ (∃ z. ∀ w. P w z ⟷ (P w x ∧ P w y))" -- "product closure"

text {* Combining Closure Mereology with Minimal Mereology yields the theory known as
Closure Minimal Mereology @{term "CMM"} whereas combining Closure Mereology with Extensional
Mereology obtains \emph{Closed Extensional Mereology} @{term "CEM"}
@{cite "casati_parts_1999"} p. 43: *}

locale CMM = CM + MM
locale CEM = EM + CM

text {* In Closed Minimal Mereology, the product closure axiom and weak supplementation jointly
entail strong supplementation.  The proof verified here is from Pontow @{cite "pontow_note_2004"} p. 200: *}

lemma (in CMM) SS: "¬ P x y ⟶ (∃ z. P z x ∧ D z y)"
proof fix x y
  assume "¬ P x y"
  show "(∃ z. P z x ∧ D z y)"
  proof cases
    assume "D x y"
    thus "(∃ z. P z x ∧ D z y)" using R by auto
  next
    assume "¬ D x y"
    hence "O x y" using D_def by simp
    hence "∃ z. ∀ w. P w z ⟷ (P w x ∧ P w y)" using PC by simp
    then obtain z where z: "∀ w. P w z ⟷ (P w x ∧ P w y)"..
    hence "PP z x" using PP_def R ‹¬ P x y› by auto
    hence "(∃ w. PP w x ∧ D w z)" using WS by simp
    then obtain w where "PP w x ∧ D w z"..
    hence "P w x ∧ D w y" by (meson D_def O_def PP_def T z)
    thus "(∃ z. P z x ∧ D z y)"..
  qed
qed

(* Later I might  add here the proof of the proper parts principle from products on 
@{cite "simons_parts:_1987"} p. 33 *)

text {* Because Strong Supplementation is provable in Closed Minimal Mereology, it follows that
Closed Extensional Mereology and Closed Minimal Mereology are the same theory 
@{cite "casati_parts_1999"} p. 44: *}

sublocale CEM ⊆ CMM by (simp add: CMM.intro CM_axioms MM_axioms)
sublocale CMM ⊆ CEM  by (simp add: CEM.intro CM_axioms EM.intro EM_axioms.intro M_axioms SS)

text {* Closure Mereology with Universe (CMU) is obtained by adding  an axiom ensuring existence
of a universe @{cite "casati_parts_1999"} p. 44:  *}

locale CMU = CM +
  assumes U: "∃ z. ∀ x. P x z" -- "universe"

text {* And adding Extensional Mereology (or Minimal Mereology) to this theory results in
Closed Extensional Mereology with Universe @{text "CEMU"}: *}

locale CEMU = EM + CMU

text {* In Closure Extensional Mereology with Universe, it's possible to derive a strengthening of
the sum axiom, since everything underlaps everything else: *}

lemma (in CEMU) EU: "U x y" using U_def U by auto -- "everything underlaps"
lemma (in CEMU) SSC: "(∃ z. ∀ w. O w z ⟷ (O w x ∨ O w y))" using EU SC by simp
 -- "strengthened sum closure"

(*
text {* Does CEMU entail the existence of differences? I should think yes, since the difference
between a and b is the sum of the elements of a that overlap b. However, if a has infinitely many
elements, the sum may not be guaranteed to exist by the product axiom. This might explain why
nitpick does not find a counterexample: *}

lemma (in CEMU) D: "(∃ w. P w x ∧ ¬ O w y) ⟶ (∃ z. ∀ w. P w z ⟷ (P w x ∧ ¬ O w y))" oops

*)

section {* General Mereology *}

text {* General Mereology is obtained from Ground Mereology by adding the axiom of fusion or
unrestricted composition @{cite "casati_parts_1999"} p. 46:  *}

locale GM = M +
  assumes F: "(∃ x. F x) ⟶ (∃ z. ∀ y. O y z ⟷ (∃ x. F x ∧ O x y))" -- "fusion or unrestricted composition"

text {* Substituting @{text "x = a ∨ x = b"} for @{text "F x"} in the fusion axiom allows the derivation of
an unrestricted version of sum closure @{text "GS"}, and so of course sum closure itself, as follows:  *}

lemma (in GM) FS:
"(∃ x. (x = a ∨ x = b)) ⟶ (∃ z. ∀ y. O y z ⟷ (∃ x. (x = a ∨ x = b) ∧ O x y))"
  using F solve_direct.
lemma (in GM) GFS: "(∃ z. ∀ y. O y z ⟷ (∃ x. (x = a ∨ x = b) ∧ O x y))"
  using FS by blast
lemma (in M) GFStoGS:
  assumes GFS: "(∃ z. ∀ y. O y z ⟷ (∃ x. (x = a ∨ x = b) ∧ O x y))"
  shows "(∃z. ∀w. O w z ⟷ (O w a ∨ O w b))" by (metis O_def GFS)
lemma (in GM) GS: "(∃z. ∀w. O w z ⟷ (O w x ∨ O w y))"
  using GFS GFStoGS by simp
lemma (in GM) S: "U x y ⟶ (∃z. ∀w. O w z ⟷ (O w x ∨ O w y))"
  using GS by simp

text {* But product closure cannot be derived: *}

lemma (in GM) T: "O x y ⟶ (∃ z. ∀ w. P w z ⟷ (P w x ∧ P w y))"
  nitpick [show_all] oops

  text {* It follows that General Mereology does not encompass Closure Mereology, contrary to
Simons @{cite "simons_parts:_1987"} p. 36 and Casati and Varzi @{cite "casati_parts_1999"} p. 46
(this point is discussed in detail by Pontow @{cite "pontow_note_2004"}: *}

sublocale GM ⊆ CM nitpick [show_all] oops

text {* It's possible to prove from fusion in General Mereology that there is something that
overlaps everything: *}

lemma (in GM) "∃ z. ∀ x. O x z" -- "something overlaps everything"
proof -
  have "(∃ x. x = x) ⟶ (∃ z. ∀ y. O y z ⟷ (∃ x. x = x ∧ O x y))" using F by fast
  hence  "∃ z. ∀ y. O y z ⟷ (∃ x. x = x ∧ O x y)" by simp
  hence  "∃ z. ∀ y. O y z ⟷ (∃ x. O x y)" by simp
  thus ?thesis by (metis O_def R)
qed

text {* But it doesn't follow that there is a universe, let alone a unique universe. If for example,
there is just an infinite ascending chain, then everything overlaps everything else, but there isn't
a particular thing which everything is a part of, since for anything in particular, the things above it
are not part of the chain: *}

lemma (in GM) U: "∃ z. ∀ x. P x z" nitpick oops

text {* The existence of differences is not guaranteed either: *}

lemma (in GM) D:  "(∃ w. P w x ∧ ¬ O w y) ⟶ (∃ z. ∀ w. P w z ⟷ (P w x ∧ ¬ O w y))" nitpick oops

text {*  Call the combination of General Mereology with weak supplementation General Minimal
Mereology, or @{term "GMM"}: *}

locale GMM = MM + GM -- "General Minimal Mereology"

text {* Although Strong Supplementation can be derived from Weak Supplementation in Closed Minimal
Mereology  via the product axioms, it cannot be derived in General Minimal Mereology, since the
product axiom itself still cannot be derived in General Minimal Mereology:  *}

lemma (in GMM) SS:   "¬ P x y ⟶ (∃ z. P z x ∧ D z y)" nitpick oops
lemma (in GMM) T: "O x y ⟶ (∃ z. ∀ w. P w z ⟷ (P w x ∧ P w y))" nitpick [show_all] oops

text {* Nor can the existence of a universe or differences be proved in General Minimal Mereology: *}

lemma (in GMM) U: "∃ z. ∀ x. x z" nitpick oops
lemma (in GMM) D: "(∃ w. P w x ∧ ¬ O w y) ⟶ (∃ z. ∀ w. P w z ⟷ (P w x ∧ ¬ O w y))" nitpick oops

section {* Classical Extensional Mereology *}

text {* Classical Extensional Mereology @{text "GEM"} is simply Extensional Mereology combined
with General Mereology  @{cite "casati_parts_1999"} p. 46: *}

locale GEM = EM + GM

text {* The presence of strong supplementation in Classical Extensional Mereology enables the derivation of 
product closure from fusion. The following proof is from Pontow  @{cite "pontow_note_2004"} pp. 202-3.  *}

text {* The proof begins by substitutions @{text "z ❙≤ a ∧ z ❙≤ b"} for @{text "F"} in the fusion axiom,
to give the existence of a sum of all the parts of @{text "a"} and @{text "b"}: *}

lemma (in GM) FP: "(∃ z. (P z a ∧ P z b)) ⟶ (∃ z. ∀ w. O w z ⟷ (∃ x. (P x a ∧ P x b) ∧ O x w))"
  using F solve_direct.

text {* Three lemmas are helpful before proceeding with the proof proper. First, strong supplementation
is needed to proceed from the fact that z is \emph{a} sum of the Fs to the fact that z is \emph{the}
sum of the Fs:  *}

lemma (in EM) atothesum:
  assumes asum: "∀ y. O y z ⟷ (∃ x. F x ∧ O x y)"
  shows thesum: "(THE v. ∀ y. O y v ⟷ (∃ x. F x ∧ O x y)) = z"
proof (rule the_equality)
  show "∀ y. O y z ⟷ (∃ x. F x ∧ O x y)" using asum.
  show "⋀v. ∀y. O y v = (∃x. F x ∧ O x y) ⟹ v = z"  by (metis SS AS D_def O_def R asum)
qed

text {* Using this lemma, we can show that if something overlaps z just in case it overlaps an F,
then it is the sum of the Fs: *}

lemma (in EM) UGS: "(∀ y. O y z ⟷ (∃ x. F x ∧ O x y)) ⟶ (σ x. F x) = z"
proof
  assume "(∀ y. O y z ⟷ (∃ x. F x ∧ O x y))"
  hence "(THE v. ∀ y. O y v ⟷ (∃ x. F x ∧ O x y)) = z" using atothesum by simp
  thus "(σ v. F v) = z" using σ_def by blast
qed

text {* With this lemma in hand, we can proceed with a final lemma the proof from
Pontow @{cite "pontow_note_2004"} pp. 202-3, according to which if there is an F, then everything
is part of the sum of the Fs just in case every part of it overlaps with an F. *}

lemma (in GEM) PS: "(∃ x. F x) ⟶ (∀ y. P y (σ v. F v) ⟷ (∀ w. P w y ⟶ (∃ v. F v ∧ O v w)))"
proof
  assume "(∃ x. F x)"
  hence "∃ z. ∀ y. O y z ⟷ (∃ x. F x ∧ O x y)" using F by simp
  then obtain z where z: "∀ y. O y z ⟷ (∃ x. F x ∧ O x y)"..
  hence σ: "(σ v. F v) = z " using UGS by simp
  show "∀ y. P y (σ v. F v) ⟷ (∀ w. P w y ⟶ (∃ v. F v ∧ O v w))"
  proof
    fix y
    show "P y (σ v. F v) ⟷ (∀ w. P w y ⟶ (∃ v. F v ∧ O v w))"
      proof
        assume "P y (σ v. F v)"
        hence "P y z" using σ by simp
        hence "O y z" using O_def R by auto
        hence "(∃ x. F x ∧ O x y)" using z by simp
        thus "(∀ w. P w y ⟶ (∃ v. F v ∧ O v w))" by (metis O_def R T ‹P y z› z)
      next 
        assume "(∀ w. P w y ⟶ (∃ v. F v ∧ O v w))"
        hence "P y z" using z by (meson D_def SS)
        thus "P y (σ v. F v)" using σ by simp
      qed
    qed
  qed

  text {* Continuing to follow the  proof from @{cite "pontow_note_2004"} pp. 204, we can prove
the Product Axiom proper:  *}

lemma (in GEM) T: "O x y ⟶ (∃ z. ∀ w. P w z ⟷ (P w x ∧ P w y))"
proof 
  assume "O x y"
  hence ez:  "(∃ z. (P z x ∧ P z y))" using O_def by simp
  hence "(∃ z. ∀ w. O w z ⟷ (∃ v. (P v x ∧ P v y) ∧ O v w))" using FP by simp
  then obtain z where "(∀ w. O w z ⟷ (∃ v. (P v x ∧ P v y) ∧ O v w))"..
  hence σzxy: "(σ v. P v x ∧ P v y) = z" using UGS by simp
  have gragra: "(∀ s. P s (σ v. P v x ∧ P v y) ⟷
(∀ w. P w s ⟶ (∃ v. P v x ∧ P v y ∧ O v w)))" using PS ez by simp
  have "∀ w. P w z ⟷ (P w x ∧ P w y)"
  proof
    fix w
    show "P w z ⟷ (P w x ∧ P w y)"
      proof
        assume "P w z"
        hence "P w (σ v. P v x ∧ P v y)" using σzxy by simp
        hence dadada: "(∀ t. P t w ⟶ (∃ v. P v x ∧ P v y ∧ O v t))" using gragra by simp
        have "∀ t. P t w ⟶ (O t x ∧ O t y)"
        proof
          fix t
          show "P t w ⟶ (O t x ∧ O t y)"
            proof
              assume "P t w"
              hence "(∃ v. P v x ∧ P v y ∧ O v t)" using dadada by simp
              thus "O t x ∧ O t y" using O_def T by blast
            qed
          qed
          thus "P w x ∧ P w y" using SS T D_def by meson
        next
          assume "P w x ∧ P w y"
          thus "P w z" using O_def R σzxy gragra by fastforce
        qed
      qed
      thus "(∃ z. ∀ w. P w z ⟷ (P w x ∧ P w y))"..
    qed

(* Naming of sentences in this proof need to be tidied up. *)

text {* It follows that General Extensional Mereology is stronger than Closed Extensional Mereology *}

sublocale GEM ⊆ CEM using CEM.intro CM.intro CM_axioms_def EM_axioms M_axioms S T by blast

text {* Likewise, substituting @{text "x = x"} for @{text "F x"} in fusion allows the derivation of the 
existence of a universe: *}

lemma (in GM) selfidentity:
"(∃ x. x = x) ⟶ (∃ z. ∀ y. O y z ⟷ (∃ x. x = x ∧ O x y))"
  using F by fast
lemma (in GM) "(∃ z. ∀ y. O y z ⟷ (∃ x. O x y))" using selfidentity by simp
lemma (in GEM) U: "∃ z. ∀ x. P x z"
  using selfidentity by (metis D_def O_def SS)

text {* It follows that Classical Extensional Mereology is also stronger than Closed Extensional Mereology with Universe: *}

sublocale GEM ⊆ CEMU
proof
  show "∃z. ∀x. P x z" using U by simp
qed

text {* The existence of differences is also derivable in General Extensional Mereology. Like, the proof
of the product axiom, the proof of the existence of differences is quite involved. It can be found
in Pontow @{cite "pontow_note_2004"} p. 209. *}

lemma (in GM) FD: "(∃ x. P x a ∧ ¬ O x b) ⟶ (∃ z. ∀ y. O y z ⟷ (∃ x. (P x a ∧ ¬ O x b) ∧ O x y))" using F solve_direct.

lemma (in GEM) D: "(∃ w. P w x ∧ ¬ O w y) ⟶ (∃ z. ∀ w. P w z ⟷ (P w x ∧ ¬ O w y))"
proof
  assume "(∃ w. P w x ∧ ¬ O w y)"
  hence "(∃ z. ∀ w. O w z ⟷ (∃ v. (P v x ∧ ¬ O v y) ∧ O v w))" using FD by simp
  then obtain Σ where Σ: "∀ w. O w Σ ⟷ (∃ v. (P v x ∧ ¬ O v y) ∧ O v w)"..
  have "∀ w. P w Σ ⟷ (P w x ∧ ¬ O w y)"
  proof
    fix w
    show "P w Σ ⟷ (P w x ∧ ¬ O w y)"
      proof
        assume "P w Σ"
        have "∀ z. P z w ⟶ O z x"
        proof
          fix z
          show "P z w ⟶ O z x"
            proof
              assume "P z w"
              hence "∃ s0. (P s0 x ∧ ¬ O s0 y) ∧ O s0 z"  using M.T M_axioms O_def R Σ ‹w ❙≤ Σ› by blast
              thus "O z x" using M.T M_axioms O_def by blast
            qed
          qed
          hence "P w x" using SS D_def by blast
          have "∀ v. P v w ⟶ ¬ P v y" by (metis O_def M.T M_axioms Σ ‹P w Σ›)
              hence "¬ O w y" using O_def by simp
              thus "P w x ∧ ¬ O w y" using ‹P w x› by blast
            next
              assume "P w x ∧ ¬ O w y"
              show "P w Σ" by (meson D_def O_def R SS Σ ‹P w x ∧ ¬ O w y›)
            qed
           qed
           thus "(∃ z. ∀ w. P w z ⟷ (P w x ∧ ¬ O w y))"..
         qed

section {* Atomism *}

text {* An atom is an individual with no proper parts: *}

definition (in M) A:: "i ⇒ bool" ("A")
  where "A x  ≡ ¬ (∃ y. PP y x)" 

text {* Each theory discussed above can be augmented with an axiom stating that everything has
an atom as a part, viz. @{cite "casati_parts_1999"}, p. 48: *}

locale AM = M +
  assumes A: "∀ x. ∃ y. A y ∧ P y x" -- "atomicity"
locale AMM = AM + MM
locale AEM = AM + EM
locale ACM = AM + CM
locale ACEM = AM + CEM
locale AGM = AM + GM
locale AGEM = AM + GEM

text {* It follows in @{text "AEM"} that if something is not part of another, there is an atom
which is part of the former but not part of the later: *}

lemma (in AEM)
ASS: "¬ P x y ⟶ (∃ z. A z ∧ (P z x ∧ ¬ O z y))"
proof
  assume "¬ P x y"
  hence "(∃ w. P w x ∧ D w y)" using SS by simp
  then obtain w where w: "P w x ∧ D w y"..
  hence "∃ z. A z ∧ P z w" using A by simp
  then obtain z where z: "A z ∧ P z w"..
  hence "A z ∧ (P z x ∧ ¬ O z y)" by (meson D_def O_def T w)
  thus "∃ z. A z ∧ (P z x ∧ ¬ O z y)"..
qed

text {* Moreover, in Minimal Mereology this lemma entails both strong supplementation and atomism,
so it serves as an alternative characterisation of Atomistic Extensional Mereology: *}

lemma (in MM)
  assumes ASS: "¬ P x y ⟶ (∃ z. A z ∧ (P z x ∧ ¬ O z y))"
  shows SS: "¬ P x y ⟶ (∃ z. P z x ∧ D z y)" using D_def assms by blast

lemma (in M)
  assumes ASS: "∀ x. ∀ y. ¬ P x y ⟶ (∃ z. A z ∧ (P z x ∧ ¬ O z y))"
  shows A: "∀ x. ∃ y. A y ∧ P y x"
proof
  fix x
  show "∃ y. A y ∧ P y x"
  proof cases
    assume "A x"
    hence "A x ∧ P x x" using R by simp
    thus "∃ y. A y ∧ P y x"..
  next
    assume "¬ A x"
    hence "∃ y. PP y x" using A_def by simp
    then obtain y where y: "PP y x"..
    hence  "¬ P x y" using PP_def by simp
    hence "∃ z. A z ∧ (P z x ∧ ¬ O z y)" using ASS by blast
    thus "∃ y. A y ∧ P y x" by blast 
  qed
qed

text {* So the axiom of Atomistic Strong Supplementation could be used in place of the two axioms of
Atomicity and Strong Supplementation @{cite "casati_parts_1999"} *}

text {* For the same reason that the Product axiom and  Strong Supplementation do not follow from the 
Fusion Axiom in General Mereology, and so General Mereology is strictly weaker than Classical Extensional
Mereology, the Product Axiom and Strong Supplementation still do not follow from the Fusion Axiom in
Atomistic General Mereology, and so Atomistic General Mereology is also strictly weaker than Atomistic
Classical Extensional Mereology @{cite "pontow_note_2004"}, p. 206: *}

lemma (in AGM) T: "O x y ⟶ (∃ z. ∀ w. P w z ⟷ (P w x ∧ P w y))" nitpick [user_axioms] oops
lemma (in AGM) SS: "¬ P x y ⟶ (∃ z. P z x ∧ D z y)" nitpick [user_axioms] oops

text {* Alternatively, each theory discussed above can be augmented with an axiom stating that there are no
atoms, viz.: *}

locale XAM = M +
  assumes XA: "¬ (∃ x. A x)" -- "atomlessness"
locale XAMM = XAM + MM
locale XAEM = XAM + EM
locale XACM = XAM + CM
locale XACEM = XAM + CEM
locale XAGM = XAM + GM
locale XAGEM = XAM + GEM

text {* Pontow notes that the question of whether the Fusion Axiom entails the Product and
Strong Supplementation axioms in Atomless General Mereology is open @{cite "pontow_note_2004"}.
Nitpick does not find a countermodel (since an infinite countermodel is needed?) and sledgehammer
fails to find a proof, so this problem remains open for now:  *}

lemma (in XAGM) T: "O x y ⟶ (∃ z. ∀ w. P w z ⟷ (P w x ∧ P w y))" oops
lemma (in XAGM) SS: "¬ P x y ⟶ (∃ z. P z x ∧ D z y)" oops

section {* Consistency *}

text {* I conclude by proving the consistency of all the theories mentioned. *}

lemma (in M)  "False" nitpick [show_all] oops
lemma (in MM)  "False" nitpick [show_all] oops
lemma (in EM)  "False" nitpick [show_all] oops
lemma (in CM)  "False" nitpick [show_all] oops
lemma (in CEM)  "False" nitpick [show_all] oops
lemma (in CMU) "False" nitpick [show_all] oops
lemma (in CEMU) "False" nitpick [show_all] oops
lemma (in GM) "False" nitpick [show_all] oops
lemma (in GEM) "False" nitpick [show_all] oops

end
