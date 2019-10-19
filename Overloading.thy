theory Overloading imports ZF begin
  
section \<open>Relativization and Absoluteness\<close>


subsection\<open>Relativized versions of standard set-theoretic concepts\<close>

definition
  memclass :: "[i,i\<Rightarrow>o] \<Rightarrow> o" (infixl "\<in>" 50) where
  "memclass(x,A) \<equiv> A(x)" 

definition
  Unclass ::  "[i\<Rightarrow>o,i\<Rightarrow>o] \<Rightarrow> i \<Rightarrow> o" (infixl "\<union>" 65) where
  "Unclass(A,B,x) \<equiv> A(x) \<or> B(x)"

lemma memclass_iff [iff]: "x\<in>A \<longleftrightarrow> A(x)"
  unfolding memclass_def by simp

lemma Unclass_iff [iff]: "x \<in> A \<union> B \<longleftrightarrow> A(x) \<or> B(x)"
  unfolding Unclass_def by simp

lemma "y\<in>x \<Longrightarrow> x\<in>Ord \<Longrightarrow> y\<in>Ord"
  using Ord_in_Ord by simp
end
