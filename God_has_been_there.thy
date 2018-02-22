theory God_has_been_there
imports Main
begin
section {* Introduction *} 
text{* this theory is just an implementation of what i have thought about God *}
 
section {* Argument *}
text {* when a baby takes birth he knows nothing or we can say his mind is just empty but as he/she
grows up he/she starts gathering/collecting facts and experience which is in her mind only so
mind is just a collection of experience or knowledge which one gathers those experiences and 
facts are in fact knowledge which is true because it is coming from somewhere. if there's anything 
in the world except nature, that is because of someone's  mind and then there are books like Quran,
bhagvat Geeta,Bible,GuruGranth Sahib which claims that there has been god in this world since the 
books are not nature, all the context in those books is coming from someone's mind and then again 
mind is just a collection of memories, experiences which means someone somewhere must hae seen,
 experienced God thus God has been there *}
typedecl e --"type for experience or collections"
consts nature :: "e\<Rightarrow>bool"
consts book :: "e"
consts experiences :: "e\<Rightarrow>e\<Rightarrow>bool" (infix "experiences" 52)
abbreviation mind ::"e\<Rightarrow>bool" where "mind x \<equiv> \<exists> y .(x experiences y)"
abbreviation occured :: "e\<Rightarrow>bool" where " occured x \<equiv> \<exists> y .(x experiences y)\<and> \<not> nature y"
abbreviation books_claims :: "e\<Rightarrow>bool" where "books_claims x \<equiv> occured x" 
abbreviation existed :: "e\<Rightarrow>bool" where "existed x \<equiv> occured x "
axiomatization where experienced_God : "books_claims God \<Longrightarrow> True"
