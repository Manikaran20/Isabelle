theory Rene_Descartes
  imports Main
begin

section {*introduction*}

text {* This paper presents an automated verification of Rene Descartes's argument on @{ Text "my_mind_and_body_are_distinct"}.
here, I'm providing the whole argument to make it easy to the user who read this verification. *}

section {* The_Argument *}

text{*@{ cite "https://www.youtube.com/watch?v=Din_92eKqW8&t=1457s"} I will note that mind differs importantly from body in that body is by it's nature divisible,
 while mind is indivisible when I think about my mind or in other words Myself in so far,
I am just a thinking being .I can't distinguish any parts.I understand myself to be a whole 
unified thing although my whole mind seems united to my whole body.I know cutting off a foot or an
arm, would not take anything away from my mind and the abilities to will,sense and understand can't
be called parts that it is one and the same mind that wills,senses and understands on the other hand
whenever I think of a physical or extended thing, I can mentally divide it
and therefore understand that Object is divisible. the single fact would be enough to
teach me that my mind and my body are distinct. *}

typedecl e -- "type of physically existing things"
text ‹If it can be divided into parts it is divisible›

consts breakable ::"e ⇒ bool"
consts body :: "e" ("body") --"constant symbol for a physical thing"
consts mind :: "e" ("mind") 


prop "breakable(body)" --"body can be divided into parts"

prop "\<not>breakable(mind)  " --"mind can not be divided into parts"

consts P:: "e \<Rightarrow> bool" --"some property for type e"

axiomatization where mind_constrain : "breakable(mind)⟹False"

axiomatization where body_constrain: "breakable(body) ⟹True"

abbreviation leibniz_equality :: "e\<Rightarrow>e\<Rightarrow>bool" ("L=") where
"L= x y \<equiv> \<forall>(λφ.(φx \<longrightarrow> φy))"


abbreviation leibniz_equality_syntax:: " e\<Rightarrow>e\<Rightarrow>bool" (infix "Lb=" 90) where
"x Lb= y \<equiv>  L= x y"
  
function  distinct::"e ⇒ e ⇒ bool" where
"iff (distinct x y = True) (\<not>(x Lb= y)=True)" 

theorem MyBodyAndMyMind_are_distinct : 
  shows "(distinct mind body) = True"
  with mind_constrain  have "breakable(mind) = False"  by blast
  with body_constrain have " breakable(body) = True" by blast

  end-
