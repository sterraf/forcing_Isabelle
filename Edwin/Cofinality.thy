theory Cofinality 
  imports 
    Cardinal_AC
    "~~/src/ZF/Constructible/Normal"
begin

definition
  cofinal :: "[i,i,i] \<Rightarrow> o" where
  "cofinal(X,A,r) == \<forall>a\<in>A. \<exists>x\<in>X. <a,x>\<in>r \<or> a = x"

definition
  cofinal_predic :: "[i,i,[i,i]\<Rightarrow>o] \<Rightarrow> o" where
  "cofinal_predic(X,A,r) == \<forall>a\<in>A. \<exists>x\<in>X. r(a,x) \<or> a = x"

definition
  f_cofinal :: "[i\<Rightarrow>i,i,i,i] \<Rightarrow> o" where
  "f_cofinal(f,C,A,r) == \<forall>a\<in>A. \<exists>x\<in>C. <a,f(x)>\<in>r \<or> a = f(x)" (* "predic" version ? *)
  
definition
  cofinal_fun :: "[i,i,i] \<Rightarrow> o" where
  "cofinal_fun(f,A,r) == \<forall>a\<in>A. \<exists>x\<in>domain(f). <a,f`x>\<in>r \<or> a = f`x"

(*
The next definition doesn't work if 0 is the top element of A.
But it works for limit ordinals.
*)

definition
  cofinal_fun' :: "[i,i,i] \<Rightarrow> o" where
  "cofinal_fun'(f,A,r) == f_cofinal(\<lambda>x. f`x,domain(f),A, r)"
  
lemma cofinal_in_cofinal:
  assumes
    "trans(r)" "cofinal(Y,X,r)" "cofinal(X,A,r)" 
  shows 
    "cofinal(Y,A,r)"
  oops

lemma range_is_cofinal: 
  assumes "cofinal_fun(f,A,r)" "f:C \<rightarrow> D"
  shows "cofinal(D,A,r)"
  unfolding cofinal_def
proof 
  fix b 
  assume "b \<in> A"
  moreover from assms
  have "a\<in>A \<Longrightarrow> \<exists>x\<in>domain(f). \<langle>a, f ` x\<rangle> \<in> r \<or> a = f`x" for a
    unfolding cofinal_fun_def by simp
  ultimately
  obtain x where "x\<in>domain(f)" "\<langle>b, f ` x\<rangle> \<in> r \<or> b = f`x" 
    by blast
  from \<open>f:C \<rightarrow> D\<close>
  have "domain(f) \<subseteq> C" (* is it needed? *)
    (* using  *) sorry find_theorems "?f:Pi(?A,?B)"
  then
  show  "\<exists>y\<in>D. \<langle>b, y\<rangle> \<in> r \<or> b = y" sorry
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
  have "\<exists>A. A\<subseteq>\<gamma> \<and> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<and> \<gamma> = ordertype(A,Memrel(\<gamma>))"
    using gamma_cofinal_gamma ordertype_Memrel[symmetric] assms by blast
  then
  show ?thesis 
    using LeastI[of ?P] assms unfolding cf_def by simp
qed
*)

lemma cofinal_mono_map_cf:
  assumes "Ord(\<gamma>)"
  shows "\<exists>j \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>)) . cofinal_fun(j,\<gamma>,Memrel(\<gamma>))"
  sorry
    
lemma cf_succ:
  "Ord(\<alpha>) \<Longrightarrow> cf(succ(\<alpha>)) = 1"
  sorry
    
lemma mono_map_increasing: 
  "j\<in>mono_map(A,r,B,s) \<Longrightarrow> a\<in>A \<Longrightarrow> c\<in>A \<Longrightarrow> <a,c>\<in>r \<Longrightarrow> <j`a,j`c>\<in>s"
  unfolding mono_map_def by simp

lemma lt_trans [trans]: 
  "a<b \<Longrightarrow> b<c \<Longrightarrow> a<c"
  using Ord_trans unfolding lt_def by blast
  
lemma 
  notes le_imp_subset [dest]
  assumes 
    "Ord(\<delta>)" "Limit(\<gamma>)" "function(f)" "domain(f) = \<delta>" "cofinal_fun(f,\<gamma>,Memrel(\<gamma>))" 
  shows
    "\<exists>g \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<delta>,Memrel(\<delta>)). 
      f O g \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>)) \<and> 
      cofinal_fun(f O g,\<gamma>,Memrel(\<gamma>))"
proof -
  from \<open>Limit(\<gamma>)\<close>
  obtain j where "j \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>))" "cofinal_fun(j,\<gamma>,Memrel(\<gamma>))"
    using cofinal_mono_map_cf Limit_is_Ord by blast
  let ?A="\<lambda>\<alpha> g. {\<theta> \<in> \<delta>. j`\<alpha> \<le> f`\<theta> \<and> (\<forall>\<beta><\<alpha> . f`(g`\<beta>) < f`\<theta>)}"
  let ?H="\<lambda>\<alpha> h. if ?A(\<alpha>,h) \<noteq> 0 then Least(##?A(\<alpha>,h)) else \<delta>"
  define G where "G \<equiv> \<lambda>\<alpha>. transrec(\<alpha>,?H)"
  have "\<alpha><cf(\<gamma>) \<Longrightarrow> \<beta>\<in>cf(\<gamma>) \<Longrightarrow> \<beta><\<alpha> \<Longrightarrow> ?A(\<alpha>,g) \<subseteq> ?A(\<beta>,g)" for \<beta> \<alpha> g
  proof -
    assume "\<beta><\<alpha>" "\<alpha><cf(\<gamma>)"
    then 
    have "\<beta>\<in>cf(\<gamma>)" "\<alpha>\<in>cf(\<gamma>)" "\<beta>\<in>\<alpha>" 
      using ltD by (auto intro:lt_trans) 
    with \<open>j \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>))\<close>
    have "j`\<beta> \<in> j`\<alpha>" using mono_map_increasing by blast 
    moreover
    have "Ord(j`\<alpha>)" sorry
    ultimately
    have "j`\<beta> \<le> j`\<alpha>"  unfolding lt_def by blast
    then
    have "j`\<alpha> \<le> f`\<theta> \<Longrightarrow> j`\<beta> \<le> f`\<theta>" for \<theta> using le_trans by blast
    moreover from \<open>\<beta><\<alpha>\<close>
    have "\<forall>x<\<alpha>. f`(g`x) < f`z \<Longrightarrow> y<\<beta> \<Longrightarrow>  f`(g`y) < f`z" for y z sorry
    ultimately
    show ?thesis by blast
  qed
  have "f`G(\<beta>) < f`G(\<alpha>)" 
    if "\<beta><\<alpha>" "G(\<beta>)\<noteq>\<delta>" "G(\<alpha>)\<noteq>\<delta>" "f`G(\<beta>) < f`G(\<alpha>)" "G(\<beta>)<G(\<alpha>)" for \<beta> \<alpha>
  proof -
    show ?thesis sorry
  qed
  have "G(\<beta>)<G(\<alpha>)" 
    if "\<beta><\<alpha>" "G(\<beta>)\<noteq>\<delta>" "G(\<alpha>)\<noteq>\<delta>" "f`G(\<beta>) < f`G(\<alpha>)" "G(\<beta>)<G(\<alpha>)" for \<beta> \<alpha>
  proof -
    show ?thesis sorry
  qed
  have "\<alpha> < cf(\<gamma>) \<Longrightarrow> G(\<alpha>)\<noteq>\<delta>" for \<alpha>
    sorry
  let ?g="\<lambda>\<alpha>\<in>cf(\<gamma>) . G(\<alpha>)"
  have "?g \<in> mono_map(cf(\<gamma>), Memrel(cf(\<gamma>)), \<delta>, Memrel(\<delta>))" sorry
  moreover     
  have "f O ?g \<in> mono_map(cf(\<gamma>), Memrel(cf(\<gamma>)), \<gamma>, Memrel(\<gamma>))" sorry
  moreover
  have "cofinal_fun(f O ?g, \<gamma>, Memrel(\<gamma>))"
    sorry
  ultimately show ?thesis by blast
qed
    
lemma 
  assumes 
    "Ord(\<delta>)" "Ord(\<gamma>)" "function(f)" "domain(f) = \<delta>" "cofinal_fun(f,\<gamma>,Memrel(\<gamma>))" 
  shows
    "cf(\<gamma>)\<le>\<delta>"
  oops
    
    
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
  
lemma surjection_is_cofinal:
  assumes
    "Ord(\<gamma>)" "Ord(\<delta>)" "f \<in> surj(\<delta>,\<gamma>)"
  shows "cofinal_fun(f,\<gamma>,Memrel(\<gamma>))"
  unfolding cofinal_fun_def
proof 
  fix a
  assume "a\<in>\<gamma>"
  with assms
  obtain x where "x\<in>\<delta>" "f`x = a" 
    unfolding surj_def  by blast
  oops
   
    
lemma cf_le_cardinal:
  assumes "Limit(\<gamma>)"
  shows "cf(\<gamma>) \<le> |\<gamma>|"
  sorry    

lemma regular_is_cardinal:
  notes le_imp_subset [dest]
  assumes "Limit(\<gamma>)" "\<gamma> = cf(\<gamma>)"
  shows "Card(\<gamma>)"
proof -
  from assms
  have "|\<gamma>| \<subseteq> \<gamma>" 
    using Limit_is_Ord Ord_cardinal_le by blast
  also from \<open>\<gamma> = cf(\<gamma>)\<close>
  have "\<gamma> \<subseteq> cf(\<gamma>)" by simp
  finally
  have "|\<gamma>| \<subseteq> cf(\<gamma>)" .
  with assms
  show ?thesis unfolding Card_def using cf_le_cardinal by force     
qed 
    
end (* cofinality *)
    
end