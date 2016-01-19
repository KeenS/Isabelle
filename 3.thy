theory excerise3
  imports Main
begin

lemma "\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ [] \<rbrakk> \<Longrightarrow> ys = zs"
  apply simp
  done

lemma "\<forall> x. f x = g (f (g x)) \<Longrightarrow> f [] = f [] @ []"
  apply (simp (no_asm))
  done

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"xor A B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"

lemma "xor A (\<not> A)"
  apply(simp only: xor_def)
  apply(simp add: xor_def)
  done

lemma "(let xs = [] in xs@ys@xs) = ys"
  apply(simp add: Let_def)
  done

lemma hd_Cons_tl[simp]: "xs \<noteq> [] \<Longrightarrow> hd xs # tl xs = xs"
  apply(case_tac xs, simp, simp)
  done

lemma "\<forall> xs. if xs = [] then rev xs = [] else rev xs \<noteq> []"
  apply(split split_if)
  apply(simp)
  done

lemma "(case xs of [] \<Rightarrow> zs | y#ys \<Rightarrow> y#(ys@zs)) = xs@zs"
  apply(simp split: list.split)
  done

lemma "if xs = [] then ys \<noteq> [] else ys = [] \<Longrightarrow> xs @ ys \<noteq> []"
  apply (split split_if_asm)
  apply simp
  apply simp
  done

primrec itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []     ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"



lemma "\<forall> ys. itrev xs ys = rev xs @ ys"
  apply(induct_tac xs, simp_all)
  done

primrec add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add m 0 = m"|
  "add m (Suc n) = add (Suc m) n"

lemma [simp]: "\<forall> m. add m n = m + n"
  apply(induct_tac n)
  apply simp
  apply simp
  done

lemma "add m n = m + n"
  apply(induct_tac n, simp_all)
  done

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

primrec flatten2 :: "'a tree \<Rightarrow> 'a list => 'a list" where
  "flatten2 Tip ys                 = ys"|
  "flatten2 (Node left a right) ys = flatten2 left (a # (flatten2 right ys))"

primrec flatten :: "'a tree \<Rightarrow> 'a list"
  where
  "flatten Tip = []" |
  "flatten (Node l x r) = (flatten l) @ (x # (flatten r))"


lemma [simp]:"\<forall> xs. flatten2 t xs = flatten t @ xs"
    apply (induct_tac t, simp_all)
    done


lemma "flatten2 t [] = flatten t"
  apply simp
  done

type_synonym 'v binop = "'v \<Rightarrow> 'v \<Rightarrow> 'v"
datatype ('a, 'v) expr = Cex 'v
  | Vex 'a
  | Bex "'v binop" "('a, 'v)expr" "('a, 'v)expr"

primrec "value" :: "('a, 'v)expr \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v" where
  "value (Cex v) env = v" |
  "value (Vex a) env = env a" |
  "value (Bex f e1 e2) env = f (value e1 env) (value e2 env)"

datatype ('a, 'v) instr = Const 'v
  | Load 'a
  | Apply "'v binop"

primrec exec :: "('a, 'v)instr list \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v list \<Rightarrow> 'v list"
  where
  "exec [] s vs = vs" |
  "exec (i#is) s vs = (case i of
  Const v \<Rightarrow> exec is s (v#vs)
  | Load a \<Rightarrow> exec is s ((s a)#vs)
  | Apply f \<Rightarrow> exec is s ((f (hd vs) (hd(tl vs)))#(tl(tl vs))))"

primrec compile:: "('a, 'v)expr \<Rightarrow> ('a, 'v)instr list" where
  "compile (Cex v)       = [Const v]" |
  "compile (Vex a)       = [Load a]" |
  "compile (Bex f e1 e2) = (compile e2) @ (compile e1) @ [Apply f]"

lemma exec_ap[simp]: "\<forall> vs. exec (xs@ys) s vs = exec ys s (exec xs s vs)"
  apply(induct_tac xs, simp_all split: instr.split)
  done

theorem "\<forall> vs. exec (compile e) s vs = (value e s) # vs"
  apply(induct_tac e, simp_all)
  done

datatype 'a aexp = IF "'a bexp" "'a aexp" "'a aexp"
  | Sum "'a aexp" "'a aexp"
  | Diff "'a aexp" "'a aexp"
  | Var 'a
  | Num nat
  and 'a bexp = Less "'a aexp" "'a aexp"
  | And "'a bexp" "'a bexp"
  | Neg "'a bexp"

primrec evala :: "'a aexp \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat" and
  evalb :: "'a bexp \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" where
  "evala (IF b a1 a2) env = (if evalb b env then evala a1 env else evala a2 env)" |
  "evala (Sum a1 a2) env = evala a1 env + evala a2 env" |
  "evala (Diff a1 a2) env = evala a1 env - evala a2 env" |
  "evala (Var v) env = env v" |
  "evala (Num n) env = n" |

  "evalb (Less a1 a2) env = (evala a1 env < evala a2 env)" |
  "evalb (And b1 b2)  env = (evalb b1 env \<and> evalb b2 env)" |
  "evalb (Neg b) env = (\<not> evalb b env)"

primrec substa :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a aexp \<Rightarrow> 'b aexp" and
  substb :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a bexp \<Rightarrow> 'b bexp" where
  "substa s (IF b a1 a2) = IF (substb s b) (substa s a1) (substa s a2)" |
  "substa s (Sum a1 a2) = Sum (substa s a1) (substa s a2)" |
  "substa s (Diff a1 a2) = Diff (substa s a1) (substa s a2)" |
  "substa s (Var v) = s v" |
  "substa s (Num n) = Num n" |

  "substb s (Less a1 a2) = Less (substa s a1) (substa s a2)" |
  "substb s (And b1 b2) = And (substb s b1) (substb s b2)" |
  "substb s (Neg b) = Neg (substb s b)"

lemma "evala (substa s a) env = evala a (\<lambda>x. evala (s x) env) \<and>
  evalb (substb s b) env = evalb b (\<lambda>x. evala (s x) env)"
  apply (induct_tac a and b)
  apply simp_all
  done

(* primrec norma:: "'a aexp \<Rightarrow> 'a aexp" *)
(*  (* and *) *)
(*  (*  normb:: "'a bexp \<Rightarrow> 'a aexp \<Rightarrow> 'a aexp \<Rightarrow> 'a aexp" *) *)
(*   where *)
(*   "norma (IF b a1 a2) = (case b of *)
(*   Less la1 la2 \<Rightarrow> IF (Less (norma la1) (norma la2)) (norma a1) (norma a2) *)
(*   | And b1 b2 \<Rightarrow> norma (IF b1 (IF b2 a1 a2) a2) *)
(*   | Neg b' \<Rightarrow> norma (IF b' (norma a2) (norma a1))) " | *)
(*   "norma (Sum a1 a2) = Sum (norma a1) (norma a2)" | *)
(*   "norma (Diff a1 a2) = Diff (norma a1) (norma a2)" | *)
(*   "norma (Var v) = Var v" | *)
(*   "norma (Num n) = Num n" *)

  (* "normb (Less a1 a2) at ae = IF (Less (norma a1) (norma a2)) (norma at) (norma ae)" | *)
  (* "normb (And b1 b2) at ae = (normb b1 (IF (normb b2 at ae))   (norma ae))" | *)
  (* "normb (Neg b) at ae = IF b (norma at) (norma at)" *)


datatype ('v, 'f)"term" = Var 'v | App 'f "('v, 'f)term list"

primrec
subst  :: "('v \<Rightarrow> ('v, 'f)term) \<Rightarrow> ('v, 'f)term      \<Rightarrow> ('v, 'f)term" and
substs :: "('v \<Rightarrow> ('v, 'f)term) \<Rightarrow> ('v, 'f)term list \<Rightarrow> ('v, 'f)term list"
where
  "subst s (Var x) = s x" |
  subst_App:
  "subst s (App f ts) = App f (substs s ts)" |

  "substs s [] = []" |
  "substs s (t#ts) = subst s t # substs s ts"



lemma subst_id: "subst  Var t  = (t ::('v, 'f)term) \<and>
  substs Var ts = (ts::('v, 'f)term list)"
  apply(induct_tac t and ts, simp_all)
  done

lemma "subst (Var \<circ> f \<circ> g) t = subst (Var \<circ> f) (subst (Var \<circ> g) t)"
  apply(induct_tac t)
  apply simp
  apply simp
  apply simp
  apply simp
  done


primrec trev:: "('v, 'f) term \<Rightarrow> ('v, 'f) term" and
  trevs:: "('v, 'f) term list \<Rightarrow> ('v, 'f) term list \<Rightarrow> ('v, 'f) term list"
  where
  "trev (Var x) = Var x" |
  "trev (App f ts) = App f (trevs ts [])" |

  "trevs [] ts' = ts'" |
  "trevs (t#ts) ts' = trevs ts ((trev t) # ts')"



lemma [simp]: "subst s (App f ts) = App f (map (subst s) ts)"
  apply (induct_tac ts, simp_all)
  done

declare subst_App [simp del]

datatype ('a, 'i) bigtree = Tip | Br 'a "'i \<Rightarrow> ('a, 'i) bigtree"

primrec map_bt ::"('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'i)bigtree \<Rightarrow> ('b, 'i)bigtree"
  where
  "map_bt f Tip = Tip" |
  "map_bt f (Br a F) = Br (f a) (\<lambda>i. map_bt f (F i))"

lemma "map_bt (g \<circ> f) T = map_bt g (map_bt f T)"
  apply(induct_tac T, simp_all)
  done




end