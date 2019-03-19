theory Cofinality 
  imports 
    Cardinal_AC
    "~~/src/ZF/Constructible/Normal"
begin

definition
  cofinal :: "[i,i,i] \<Rightarrow> o" where
  "cofinal(X,A,r) == \<forall>a\<in>A. \<exists>x\<in>X. <a,x>\<in>r"

definition
  cofinal_predic :: "[i,i,[i,i]\<Rightarrow>o] \<Rightarrow> o" where
  "cofinal_predic(X,A,r) == \<forall>a\<in>A. \<exists>x\<in>X. r(a,x)"

definition
  f_cofinal :: "[i\<Rightarrow>i,i,i,i] \<Rightarrow> o" where
  "f_cofinal(f,C,A,r) == \<forall>a\<in>A. \<exists>x\<in>C. <a,f(x)>\<in>r" (* "predic" version ? *)
  
definition
  cofinal_fun :: "[i,i,i] \<Rightarrow> o" where
  "cofinal_fun(f,A,r) == \<forall>a\<in>A. \<exists>x\<in>domain(f). <a,f`x>\<in>r"

(*
The next definition doesn't work if 0 is the top element of A.
But it works for limit ordinals.
*)

definition
  cofinal_fun' :: "[i,i,i] \<Rightarrow> o" where
  "cofinal_fun'(f,A,r) == f_cofinal(\<lambda>x. f`x,domain(f),A, r)"

lemma range_is_cofinal: 
  assumes "cofinal_fun(f,A,r)" "f:C \<rightarrow> D"
  shows "cofinal(D,A,r)"
  unfolding cofinal_def
proof 
  fix b 
  assume "b \<in> A"
  moreover from assms
  have "a\<in>A \<Longrightarrow> \<exists>x\<in>domain(f). \<langle>a, f ` x\<rangle> \<in> r" for a
    unfolding cofinal_fun_def by simp
  ultimately
  obtain x where "x\<in>domain(f)" "\<langle>b, f ` x\<rangle> \<in> r" 
    by blast
  from \<open>f:C \<rightarrow> D\<close>
  have "domain(f) \<subseteq> C" (* is it needed? *)
    (* using  *) sorry find_theorems "?f:Pi(?A,?B)"
  then
  show  "\<exists>y\<in>D. \<langle>b, y\<rangle> \<in> r" sorry
qed

lemma "Limit(A) \<Longrightarrow> cofinal_fun(f,A,Memrel(A)) \<longleftrightarrow> cofinal_fun'(f,A,Memrel(A))"
  oops

definition
  cf :: "i\<Rightarrow>i" where 
  "cf(\<gamma>) == \<mu> \<alpha>.  \<exists>A. A\<subseteq>\<gamma> \<and> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<and> \<alpha> = ordertype(A,Memrel(\<gamma>))"
  
lemma gamma_cofinal_gamma:
  assumes "Ord(\<gamma>)"
  shows "cofinal(\<gamma>,\<gamma>,Memrel(\<gamma>))" sorry
    
lemma cf_is_ordertype:
  assumes "Ord(\<gamma>)"
  shows "\<exists>A. A\<subseteq>\<gamma> \<and> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<and> cf(\<gamma>) = ordertype(A,Memrel(\<gamma>))" 
    (is "?P(cf(\<gamma>))")
  using gamma_cofinal_gamma LeastI[of ?P \<gamma>] ordertype_Memrel[symmetric] assms 
  unfolding cf_def by blast
(*
proof -
  from assms
  have "\<gamma>\<subseteq>\<gamma> \<and> cofinal(\<gamma>,\<gamma>,Memrel(\<gamma>)) \<and> \<gamma> = ordertype(\<gamma>,Memrel(\<gamma>))"  
    using gamma_cofinal_gamma ordertype_Memrel assms by simp 
  then
  have "\<exists>A. A\<subseteq>\<gamma> \<and> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<and> \<gamma> = ordertype(A,Memrel(\<gamma>))" ..
  then
  show ?thesis 
    using LeastI[of ?P] assms unfolding cf_def by simp
qed
*)
    
locale cofinality =
  assumes 
    (* Better with f_cofinal(f,\<delta>,\<gamma>,Memrel(\<gamma>)) ? *)
    cota : "Ord(\<delta>) \<Longrightarrow> Ord(\<gamma>) \<Longrightarrow> function(f) \<Longrightarrow> domain(f) = \<delta> \<Longrightarrow>
            cofinal_fun(f,\<gamma>,Memrel(\<gamma>)) \<Longrightarrow> cf(\<gamma>)\<le>\<delta>"
    and idemp: "Ord(\<gamma>) \<Longrightarrow> A\<subseteq>\<gamma> \<Longrightarrow> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<Longrightarrow> 
                cf(\<gamma>) = cf(ordertype(A,Memrel(\<gamma>)))"
    (* Is it better?? 
    and idemp': "Limit(\<gamma>) \<Longrightarrow> A\<subseteq>\<gamma> \<Longrightarrow> cofinal_predic(A,\<gamma>,mem) \<Longrightarrow> 
                cf(\<gamma>) = cf(ordertype(A,Memrel(\<gamma>)))" *)
    
begin
(* probar 5.12 y 5.13(1,2) *)
  
lemma cf_indemp:
  assumes "Ord(\<gamma>)"
  shows "cf(\<gamma>) = cf(cf(\<gamma>))"  
proof -
  from assms
  obtain A where "A\<subseteq>\<gamma>" "cofinal(A,\<gamma>,Memrel(\<gamma>))" "cf(\<gamma>) = ordertype(A,Memrel(\<gamma>))"
    using cf_is_ordertype by blast
  with assms
  have "cf(\<gamma>) = cf(ordertype(A,Memrel(\<gamma>)))" using idemp by simp
  also 
  have "... = cf(cf(\<gamma>))" 
    using \<open>cf(\<gamma>) = ordertype(A,Memrel(\<gamma>))\<close> by simp
  finally
  show "cf(\<gamma>) = cf(cf(\<gamma>))"  .
qed
    
end (* cofinality *)
    
end