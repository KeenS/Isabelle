theory Section2_7
  imports Main
begin

type_synonym number = nat
type_synonym gate = "bool \<Rightarrow> bool \<Rightarrow> bool"
type_synonym ('a, 'b) alist = "('a \<times> 'b) list"
definition nand :: gate where "nand A B \<equiv> \<not> (A \<and> B)"
definition xor :: gate where "xor A B \<equiv> A \<and> \<not>B \<or> \<not> A \<and> B"


end