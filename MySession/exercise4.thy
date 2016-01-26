theory exercise4
  imports Main
begin

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "[+]" 60)
  where "A [+] B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"

notation (xsymbols) xor (infixl "\<oplus>" 60)

datatype currency =
  Euro nat ("\<euro>")
  | Pounds nat ("\<pounds>")
  | Yen nat ("\<yen>")
  | Dollar nat ("$")

(* abbreviation sim2 :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<approx>" 50) *)
(*   where "x \<approx> y \<equiv> (x, y) \<in> sim" *)

(* abbreviation not_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "~=" 50) *)
(*   where "x ~= y \<equiv> \<not> (x = y)" *)

text {* 
  The following datatype definition of @{text "'a bintree"}
  models binary trees with nodes being decorated by elements
  of type @{typ 'a}.
*}

datatype 'a bintree = 
  Leaf | Branch 'a "'a bintree" "'a bintree"

text {*
  \noindent The datatype induction rule generated here is
  of the form @{thm [display] bintree.induct [no_vars]}
*}


lemma "A \<longrightarrow> A"
  -- "a trivality of propositianal logic"
  -- "(should not really bother)"
  by (rule impI) -- "implicit assumption step involved here"

text {*
  This sentence demonstrates quotations and antiquotations:
  @{term "%x y. x"} is a well-typed term.
*}



end