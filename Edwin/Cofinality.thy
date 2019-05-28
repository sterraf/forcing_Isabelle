theory Cofinality 
  imports 
    ZF.Cardinal_AC
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
  moreover from \<open>f:C \<rightarrow> D\<close>  \<open>x\<in>domain(f)\<close>
  have "f`x\<in>D"
    using domain_of_fun apply_rangeI by simp
  ultimately
  show  "\<exists>y\<in>D. \<langle>b, y\<rangle> \<in> r \<or> b = y" by auto
qed

lemma "Limit(A) \<Longrightarrow> cofinal_fun(f,A,Memrel(A)) \<longleftrightarrow> cofinal_fun'(f,A,Memrel(A))"
  oops

definition
  cf :: "i\<Rightarrow>i" where 
  "cf(\<gamma>) == \<mu> \<alpha>.  \<exists>A. A\<subseteq>\<gamma> \<and> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<and> \<alpha> = ordertype(A,Memrel(\<gamma>))"

lemma Ord_cf [TC]: "Ord(cf(\<alpha>))"
  unfolding cf_def using Ord_Least by simp
    
lemma gamma_cofinal_gamma:
  assumes "Ord(\<gamma>)"
  shows "cofinal(\<gamma>,\<gamma>,Memrel(\<gamma>))"
  sorry
    
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
    
lemma cofinal_fun_succ:
  "Ord(\<alpha>) \<Longrightarrow> f:1\<rightarrow>succ(\<alpha>) \<Longrightarrow> f`0=\<alpha> \<Longrightarrow> cofinal_fun(f,succ(\<alpha>),Memrel(succ(\<alpha>)))"
  using domain_of_fun unfolding cofinal_fun_def by auto

lemma cf_succ:
  "Ord(\<alpha>) \<Longrightarrow> cf(succ(\<alpha>)) = 1"
  sorry

lemma cf_zero:
  "cf(0) = 0"
  unfolding cf_def cofinal_def using 
    ordertype_0 subset_empty_iff Least_le[of _ 0] by auto

lemma mono_map_increasing: 
  "j\<in>mono_map(A,r,B,s) \<Longrightarrow> a\<in>A \<Longrightarrow> c\<in>A \<Longrightarrow> <a,c>\<in>r \<Longrightarrow> <j`a,j`c>\<in>s"
  unfolding mono_map_def by simp

lemma lt_trans [trans]: 
  "a<b \<Longrightarrow> b<c \<Longrightarrow> a<c"
  using Ord_trans unfolding lt_def by blast

lemma Least_antitone:
  assumes 
    "Ord(j)" "P(j)" "\<And>i. P(i) \<Longrightarrow> Q(i)"
  shows
    "(\<mu> i. Q(i)) \<le> (\<mu> i. P(i))"
  using assms LeastI2[of P j Q] Least_le by simp

lemma Least_set_antitone:
  "Ord(j) \<Longrightarrow> j\<in>A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<mu> i. i\<in>B) \<le> (\<mu> i. i\<in>A)"
  using subset_iff by (auto intro:Least_antitone)

lemma le_neq_imp_lt:
  "x\<le>y \<Longrightarrow> x\<noteq>y \<Longrightarrow> x<y"
  using ltD ltI[of x y] le_Ord2
  unfolding succ_def by auto

lemma apply_in_range:
  assumes "Ord(\<gamma>)" " \<gamma>\<noteq>0" "f: A \<rightarrow> \<gamma>"
shows"f`x\<in>\<gamma>"
proof (cases "x\<in>A")
  case True
  from assms \<open>x\<in>A\<close>
  show ?thesis
    using   domain_of_fun apply_rangeI  by simp
    next
      case False
      from assms \<open>x\<notin>A\<close>
      show ?thesis
        using apply_0  Ord_0_lt ltD domain_of_fun by auto
    qed
       
  

lemma 
  notes le_imp_subset [dest]
  assumes 
    "Ord(\<delta>)" "Limit(\<gamma>)" "f: \<delta> \<rightarrow> \<gamma>" "cofinal_fun(f,\<gamma>,Memrel(\<gamma>))" 
  shows
    "\<exists>g \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<delta>,Memrel(\<delta>)).
     f O g \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>)) \<and> 
     cofinal_fun(f O g,\<gamma>,Memrel(\<gamma>))"
proof -
  from \<open>Limit(\<gamma>)\<close>
  have "Ord(\<gamma>)" using Limit_is_Ord by simp
  then
  obtain j where "j \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>))" "cofinal_fun(j,\<gamma>,Memrel(\<gamma>))"
    using cofinal_mono_map_cf by blast
  let ?A="\<lambda>\<alpha> g. {\<theta> \<in> \<delta>. j`\<alpha> \<le> f`\<theta> \<and> (\<forall>\<beta><\<alpha> . f`(g`\<beta>) < f`\<theta>)} \<union> {\<delta>}"
  define H where "H \<equiv> \<lambda>\<alpha> h. \<mu> x. x\<in>?A(\<alpha>,h)"
  have "\<alpha>\<in>cf(\<gamma>) \<Longrightarrow> \<beta><\<alpha> \<Longrightarrow> ?A(\<alpha>,\<lambda>x\<in>\<alpha>. G(x)) \<subseteq> ?A(\<beta>,\<lambda>x\<in>\<beta>. G(x))" for \<beta> \<alpha> G
  proof -
    assume "\<beta><\<alpha>"
    then 
    have "\<beta>\<in>\<alpha>" using ltD by simp 
    moreover assume "\<alpha>\<in>cf(\<gamma>)" 
    moreover from calculation
    have "\<beta>\<in>cf(\<gamma>)" using Ord_cf Ord_trans by blast
    moreover 
    note \<open>j \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>))\<close>
    ultimately 
    have "j`\<beta> \<in> j`\<alpha>" using mono_map_increasing by blast 
    moreover from \<open>j \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>))\<close> \<open>\<alpha>\<in>cf(\<gamma>)\<close>
    have "j`\<alpha>\<in>\<gamma>" 
      using domain_of_fun apply_rangeI mono_map_is_fun by force
    moreover from this and \<open>Limit(\<gamma>)\<close>
    have "Ord(j`\<alpha>)"
      using Ord_in_Ord Limit_is_Ord by auto
    ultimately
    have "j`\<beta> \<le> j`\<alpha>"  unfolding lt_def by blast
    then
    have "j`\<alpha> \<le> f`\<theta> \<Longrightarrow> j`\<beta> \<le> f`\<theta>" for \<theta> using le_trans by blast
    moreover
    have "f`((\<lambda>w\<in>\<beta>. G(w))`y) < f`z" if "z\<in>\<delta>" "\<forall>x<\<alpha>. f`((\<lambda>w\<in>\<alpha>. G(w))`x) < f`z" "y<\<beta>" for y z
    proof -
      note \<open>y<\<beta>\<close> 
      also
      note \<open>\<beta><\<alpha>\<close>
      finally
      have "y<\<alpha>" by simp
      with \<open>\<forall>x<\<alpha>. f`((\<lambda>w\<in>\<alpha>. G(w))`x) < f`z\<close>
      have "f ` ((\<lambda>w\<in>\<alpha>. G(w)) ` y) < f ` z" by simp
      moreover from \<open>y<\<beta>\<close> \<open>y<\<alpha>\<close>
      have "(\<lambda>w\<in>\<alpha>. G(w)) ` y = (\<lambda>w\<in>\<beta>. G(w)) ` y" 
        using beta_if  by (auto dest:ltD)
      ultimately show ?thesis by simp
    qed
    ultimately
    show ?thesis by blast
  qed
  with \<open>Ord(\<delta>)\<close>
  have H_mono: "\<alpha>\<in>cf(\<gamma>) \<Longrightarrow> \<beta><\<alpha> \<Longrightarrow> H(\<beta>,\<lambda>x\<in>\<beta>. G(x)) \<le> H(\<alpha>,\<lambda>x\<in>\<alpha>. G(x))" for \<beta> \<alpha> G
    unfolding H_def using Least_set_antitone[of \<delta> "?A(\<alpha>,\<lambda>x\<in>\<alpha>. G(x))" "?A(\<beta>,\<lambda>x\<in>\<beta>. G(x))"] 
    by simp
  define G where "G \<equiv> \<lambda>\<alpha>. transrec(\<alpha>,H)"
  then 
  have G_def':"\<And>x. G(x) \<equiv> transrec(x,H)" using G_def by simp
  have G_rec:"G(\<beta>) = H(\<beta>, \<lambda>x\<in>\<beta>. G(x))" for \<beta>
    using def_transrec[OF G_def'] .
  have "G(\<beta>) \<in> ?A(\<beta>,\<lambda>x\<in>\<beta>. G(x))" for \<beta>
  proof -
    note \<open>G(\<beta>) = H(\<beta>, \<lambda>x\<in>\<beta>. G(x))\<close>
    also from \<open>Ord(\<delta>)\<close>
    have "H(\<beta>, \<lambda>x\<in>\<beta>. G(x)) \<in> ?A(\<beta>,\<lambda>x\<in>\<beta>. G(x))"
      unfolding H_def using  LeastI[of "\<lambda>y. y\<in>?A(\<beta>,\<lambda>x\<in>\<beta>. G(x))" \<delta>] by simp
    finally 
    show ?thesis by simp
  qed
  with \<open>Ord(\<delta>)\<close>  
  have "Ord(G(\<beta>))" for \<beta>
    using Ord_in_Ord by auto
  have "G(\<beta>) \<le> G(\<alpha>)" if "\<alpha>\<in>cf(\<gamma>)" "\<beta><\<alpha>" "G(\<beta>)\<noteq>\<delta>" "G(\<alpha>)\<noteq>\<delta>" for \<beta> \<alpha>
  proof -
    note \<open>G(\<beta>) = H(\<beta>, \<lambda>x\<in>\<beta>. G(x))\<close> 
    also from that and H_mono
    have "H(\<beta>, \<lambda>x\<in>\<beta>. G(x)) \<le> H(\<alpha>, \<lambda>x\<in>\<alpha>. G(x))" 
      by simp
    also
    have "H(\<alpha>, \<lambda>x\<in>\<alpha>. G(x)) = G(\<alpha>)" 
      using def_transrec[OF G_def', symmetric] .
    finally show ?thesis .
  qed
  moreover 
  have "f`G(\<beta>) < f`G(\<alpha>)" 
    if "\<alpha>\<in>cf(\<gamma>)" "\<beta><\<alpha>" "G(\<alpha>)\<noteq>\<delta>"  for \<beta> \<alpha>
  proof -
    from \<open>G(\<alpha>) = H(\<alpha>, \<lambda>x\<in>\<alpha>. G(x))\<close> \<open>Ord(\<delta>)\<close> and that 
    have "f ` ((\<lambda>x\<in>\<alpha>. G(x)) ` \<beta>) < f ` G(\<alpha>)"
      unfolding H_def using  LeastI[of "\<lambda>y. y\<in>?A(\<alpha>,\<lambda>x\<in>\<alpha>. G(x))"] 
      by (auto simp del:beta_if)
    with \<open>\<beta><\<alpha>\<close>
    show ?thesis using ltD by auto
  qed
  moreover 
  note \<open>\<And>\<alpha>. Ord(G(\<alpha>))\<close>
  ultimately 
  have "G(\<beta>)<G(\<alpha>)" if "\<alpha>\<in>cf(\<gamma>)" "\<beta><\<alpha>" "G(\<beta>)\<noteq>\<delta>" "G(\<alpha>)\<noteq>\<delta>" for \<beta> \<alpha> 
    using that by (force intro:le_neq_imp_lt)
  then
  have monot:"G(\<beta>)\<in>G(\<alpha>)" if "\<alpha>\<in>cf(\<gamma>)" "\<beta><\<alpha>" "G(\<beta>)\<noteq>\<delta>" "G(\<alpha>)\<noteq>\<delta>" for \<beta> \<alpha> 
    using that and ltD by simp
  have G_not_delta: "\<alpha> \<in> cf(\<gamma>) \<Longrightarrow> G(\<alpha>)\<noteq>\<delta>" for \<alpha>  sorry
  with \<open>Ord(\<delta>)\<close> \<open>\<And>\<beta>. G(\<beta>) \<in> ?A(\<beta>,\<lambda>x\<in>\<beta>. G(x))\<close> 
  have in_delta:"\<alpha> \<in> cf(\<gamma>) \<Longrightarrow> G(\<alpha>)\<in>\<delta>" for \<alpha> by auto 
  let ?g="\<lambda>\<alpha>\<in>cf(\<gamma>) . G(\<alpha>)"
  from \<open>Ord(\<gamma>)\<close> \<open>Ord(\<delta>)\<close> in_delta G_not_delta
  have "?g : cf(\<gamma>) -> \<delta>"
    using ltI lam_type by simp
  then have "?g \<in> mono_map(cf(\<gamma>), Memrel(cf(\<gamma>)), \<delta>, Memrel(\<delta>))"
    unfolding mono_map_def 
  proof (intro CollectI ballI impI) 
    (* Proof that ?g respects membership *)
    fix \<beta> \<alpha> 
    assume 
      "\<beta>\<in>cf(\<gamma>)" "\<alpha>\<in>cf(\<gamma>)" 
    with G_not_delta 
    have "G(\<beta>)\<noteq>\<delta>" "G(\<alpha>)\<noteq>\<delta>" "Ord(\<alpha>)" 
      using Ord_in_Ord Ord_cf by auto
    moreover
    assume "\<langle>\<beta>, \<alpha>\<rangle> \<in> Memrel(cf(\<gamma>))"
    ultimately
    show "\<langle>?g ` \<beta>, ?g ` \<alpha>\<rangle> \<in> Memrel(\<delta>)" 
      using ltI monot in_delta by auto 
  qed
  moreover from \<open>?g : cf(\<gamma>) \<rightarrow> \<delta>\<close> \<open>f: \<delta> \<rightarrow> \<gamma>\<close>
  have "f O ?g \<in> mono_map(cf(\<gamma>), Memrel(cf(\<gamma>)), \<gamma>, Memrel(\<gamma>))" 
     unfolding mono_map_def 
  proof (intro CollectI ballI impI comp_fun[of _ _ \<delta>]) 
    (* Proof that f O ?g respects membership *)
    fix \<beta> \<alpha> 
    assume "\<langle>\<beta>, \<alpha>\<rangle> \<in> Memrel(cf(\<gamma>))"
    then
    have "\<beta><\<alpha>"
      using Ord_in_Ord[of "cf(\<gamma>)"] ltI Ord_cf by blast
    assume
      "\<beta>\<in>cf(\<gamma>)" "\<alpha>\<in>cf(\<gamma>)"   
    moreover from this and  G_not_delta  
    have "G(\<beta>)\<noteq>\<delta>" "G(\<alpha>)\<noteq>\<delta>" using Ord_cf by auto
    moreover
    note \<open>\<alpha> \<in> cf(\<gamma>) \<Longrightarrow> \<beta> < \<alpha> \<Longrightarrow> G(\<alpha>) \<noteq> \<delta> \<Longrightarrow> f ` G(\<beta>) < f ` G(\<alpha>)\<close>
    moreover 
    note \<open>f: \<delta> \<rightarrow> \<gamma>\<close> \<open>\<beta><\<alpha>\<close> \<open>Limit(\<gamma>)\<close> \<open>Ord(\<gamma>)\<close>
    ultimately
    show "\<langle>(f O ?g) ` \<beta>, (f O ?g) ` \<alpha>\<rangle> \<in> Memrel(\<gamma>)" 
      using ltD[of "f ` G(\<beta>)" "f ` G(\<alpha>)"] monot in_delta 
        apply_in_range Limit_nonzero[of \<gamma>]
      apply auto  sorry find_theorems "Limit(?a)"
  qed
  moreover
  have "cofinal_fun(f O ?g, \<gamma>, Memrel(\<gamma>))"  sorry
  ultimately show ?thesis by blast
qed
    
lemma 
  assumes 
    "Ord(\<delta>)" "Ord(\<gamma>)" "function(f)" "domain(f) = \<delta>" "cofinal_fun(f,\<gamma>,Memrel(\<gamma>))" 
  shows
    "cf(\<gamma>)\<le>\<delta>"
    (* Perhaps consider three cases on \<gamma>, using cf_zero and cf_succ *)
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