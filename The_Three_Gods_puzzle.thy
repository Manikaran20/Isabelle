theory The_Three_Gods_puzzle
imports Main
begin
type_synonym ulu = "bool"
type_synonym ozo = "bool"
consts que :: "prop\<Rightarrow>bool"
consts B :: "prop"
 prop  "(que(B) = True) \<Rightarrow> ozo"
function TEE :: "prop \<Rightarrow> bool" where
"TEE prop = if (prop=True) then ozo else ulu"

