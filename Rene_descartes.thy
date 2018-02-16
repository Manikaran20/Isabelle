

theory Rene_Descartes
  imports Main
begin

section {*introduction*}

text{* This paper presents an automated verification of Rene Descartes's argument on @{ Text "my_mind_and_body_are_distinct"}.
here, I'm providing the whole argument to make it easy to the user who read this verification. *}

section {* The_Argument *}

text{* I will note that mind differs importantly from body in that body is by it's nature divisible,
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

fun divisible :: "e ⇒ bool" where
"divisible x \<equiv> can_be_divided_into_parts x"
consts can_be_divided_into_parts :: "e \<Rightarrow> bool"
consts body :: "e" --"constant symbol for a physical thing"
prop "divisible(e) ⟶ can_be_divided_into_parts(e)"--"if a physical thing  can_be_divided_into_parts implies it is divisible"
consts mind :: "e"



fun distinct :: "bool\<times> bool\<Rightarrow> bool" where
"distinct (True, True) = True" |
"distinct (_, _) = False"

theorem Body_is_divisible[simp] : 
  assumes "divisible(body)"
  shows  "can_be_divided_into_parts(body) \<longrightarrow> divisible(body)"
proof -
  {
  assume "can_be_divided_into_parts(body)"
  from assms have "divisible(body)" by -
}
  then have "can_be_divided_into_parts(body) \<longrightarrow> divisible(body)" by (rule impI)
  thus ?thesis .
  qed
theorem Mind_is_indivisible:
  assumes "\<not> divisible(mind)"
  shows "\<not>can_be_divided_into_parts(mind)\<longrightarrow>\<not> divisible(mind)"
proof -
  {
    assume "\<not> can_be_divided_into_parts(mind)"
  from assms have "\<not> divisible(mind)" by -
  }
  then have "\<not> can_be_divided_into_parts(mind) \<longrightarrow> \<not> divisible(mind)" by (rule impI)
  thus ?thesis .
qed 
datatype A = True 
datatype B = False 
definition divisible :: "e\<Rightarrow>bool" where
"divisible x \<equiv> can_be_divided_into_parts x"
value "distinct (divisible(mind), divisible(body))"



