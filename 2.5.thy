theory Excercise
imports Main
begin
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
primrec mirror :: "'a tree \<Rightarrow> 'a tree"
  where
  "mirror Tip = Tip" |
  "mirror (Node l x r) = Node (mirror r) x (mirror l)"
lemma mirror_mirror: "mirror (mirror t) = t"
  apply (induct_tac)
  apply auto
  done

primrec flatten :: "'a tree \<Rightarrow> 'a list"
  where
  "flatten Tip = []" |
  "flatten (Node l x r) = (flatten l) @ (x # (flatten r))"

lemma flatten_mirror: "flatten(mirror t) = rev (flatten t)"
  apply (induct_tac t)
  apply auto
  done

lemma "(case xs of [] \<Rightarrow> [] | y#ys \<Rightarrow> xs) = xs"
  apply (case_tac xs)
  apply auto
  done

datatype boolex = Const bool | Var nat | Neg boolex |  And boolex boolex
primrec "value" :: "boolex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool"  where
  "value (Const b) env = b" |
  "value (Var x) env   = env x" |
  "value (Neg b) env   = (\<not> value b env)" |
  "value (And b c) env = (value b env \<and> value c env)"

datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex
primrec valif :: "ifex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "valif (CIF b)    env = b" |
  "valif (VIF x)    env = env x" |
  "valif (IF b t e) env = (if valif b env then valif t env
                                          else valif e env)"

primrec bool2if :: "boolex \<Rightarrow> ifex" where
  "bool2if (Const b) = CIF b" |
  "bool2if (Var x)   = VIF x" |
  "bool2if (Neg b)   = IF (bool2if b) (CIF False) (CIF True)" |
  "bool2if (And b c) = IF (bool2if b) (bool2if c) (CIF False)"

lemma "valif (bool2if b) env = value b env"
  apply (induct_tac b)
  apply auto
  done

primrec normif :: "ifex \<Rightarrow> ifex \<Rightarrow> ifex \<Rightarrow> ifex" where
  "normif (CIF b) t e    = IF (CIF b) t e" |
  "normif (VIF x) t e    = IF (VIF x) t e" |
  "normif (IF b t e) u f = normif b (normif t u f) (normif e u f)"

primrec norm :: "ifex \<Rightarrow> ifex" where
  "norm (CIF b)    = CIF b" |
  "norm (VIF x)    = VIF x" |
  "norm (IF b t e) = normif b (norm t) (norm e)"

lemma [simp]: "\<forall> t e. valif (normif b t e) env = valif (IF b t e) env"
  apply (induct_tac b)
  apply auto
  done

theorem "valif (norm b) env = valif b env"
  apply (induct_tac b)
  apply auto
  done

primrec normal :: "ifex \<Rightarrow> bool" where
  "normal (CIF b) = True" |
  "normal (VIF x) = True" |
  "normal (IF b t e) = (normal t \<and> normal e \<and>
                       (case b of CIF b \<Rightarrow> True
                                | VIF x \<Rightarrow> True
                                | IF x y z \<Rightarrow> False))"

lemma [simp]: "\<forall> t e. normal (normif b t e) = (normal t \<and> normal e)"
  apply (induct_tac b)
  apply auto
  done


primrec normif_s :: "ifex \<Rightarrow> ifex \<Rightarrow> ifex \<Rightarrow> ifex" where
  "normif_s (CIF b) t e    = (if b then t else e)" |
  "normif_s (VIF x) t e    = IF (VIF x) t e" |
  "normif_s (IF b t e) u f = normif_s b (normif_s t u f) (normif_s e u f)"

primrec norm_s :: "ifex \<Rightarrow> ifex" where
  "norm_s (CIF b)    = CIF b" |
  "norm_s (VIF x)    = VIF x" |
  "norm_s (IF b t e) = normif_s b (norm_s t) (norm_s e)"

lemma [simp]: "\<forall> t e. valif (normif_s b t e) env = valif (IF b t e) env"
  apply (induct_tac b)
  apply auto
  done

theorem "valif (norm b) env = valif b env"
  apply (induct_tac b)
  apply auto
  done

primrec normal_s :: "ifex \<Rightarrow> bool" where
  "normal_s (CIF b) = True" |
  "normal_s (VIF x) = True" |
  "normal_s (IF b t e) = (normal_s t \<and> normal_s e \<and>
                       (case b of CIF b \<Rightarrow> False
                                | VIF x \<Rightarrow> True
                                | IF x y z \<Rightarrow> False))"

lemma [simp]: "\<forall> t e. normal_s (normif_s b t e) \<longrightarrow> (normal_s t \<and> normal_s e)"
  apply (induct_tac b)
  apply auto
  done




end
