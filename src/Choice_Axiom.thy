theory Choice_Axiom 
  imports Powerset_Axiom Pairing_Axiom Union_Axiom 
begin
  
definition 
  induced_surj :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i" where
  "induced_surj(f,a,e) == f-``(range(f)-a)\<times>{e} \<union> restrict(f,f-``a)"
  
lemma domain_induced_surj: "domain(induced_surj(f,a,e)) = domain(f)"
  unfolding induced_surj_def using domain_restrict domain_of_prod by auto
    
lemma range_restrict_vimage: 
  assumes "function(f)"
  shows "range(restrict(f,f-``a)) \<subseteq> a"
proof
  from assms 
  have "function(restrict(f,f-``a))" 
    using function_restrictI by simp
  fix y
  assume "y \<in> range(restrict(f,f-``a))"
  then 
  obtain x where "<x,y> \<in> restrict(f,f-``a)"  "x \<in> f-``a" "x\<in>domain(f)"
    using domain_restrict domainI[of _ _ "restrict(f,f-``a)"] by auto
  moreover 
  note \<open>function(restrict(f,f-``a))\<close> 
  ultimately 
  have "y = restrict(f,f-``a)`x" 
    using function_apply_equality by blast
  also from \<open>x \<in> f-``a\<close> 
  have "restrict(f,f-``a)`x = f`x" 
    by simp
  finally 
  have "y=f`x" .
  moreover from assms \<open>x\<in>domain(f)\<close> 
  have "<x,f`x> \<in> f" 
    using function_apply_Pair by auto 
  moreover 
  note assms \<open>x \<in> f-``a\<close> 
  ultimately 
  show "y\<in>a"
    using function_image_vimage[of f a] by auto
qed
  
lemma induced_surj_type: 
  assumes
    "function(f)" (* "relation(f)" (* a function can contain nonpairs *) *)
  shows 
    "induced_surj(f,a,e): domain(f) \<rightarrow> {e} \<union> a"
    and
    "x \<in> f-``a \<Longrightarrow> induced_surj(f,a,e)`x = f`x" 
proof -
  let ?f1="f-``(range(f)-a) \<times> {e}" and ?f2="restrict(f, f-``a)"
  have "domain(?f2) = domain(f) \<inter> f-``a"
    using domain_restrict by simp
  moreover from assms 
  have 1: "domain(?f1) = f-``(range(f))-f-``a"
    using domain_of_prod function_vimage_Diff by simp
  ultimately 
  have "domain(?f1) \<inter> domain(?f2) = 0"
    by auto
  moreover 
  have "function(?f1)" "relation(?f1)" "range(?f1) \<subseteq> {e}"
    unfolding function_def relation_def range_def by auto
  moreover from this and assms 
  have "?f1: domain(?f1) \<rightarrow> range(?f1)"
    using function_imp_Pi by simp
  moreover from assms 
  have "?f2: domain(?f2) \<rightarrow> range(?f2)"
    using function_imp_Pi[of "restrict(f, f -`` a)"] function_restrictI by simp
  moreover from assms 
  have "range(?f2) \<subseteq> a" 
    using range_restrict_vimage by simp
  ultimately 
  have "induced_surj(f,a,e): domain(?f1) \<union> domain(?f2) \<rightarrow> {e} \<union> a"
    unfolding induced_surj_def using fun_is_function fun_disjoint_Un fun_weaken_type by simp
  moreover 
  have "domain(?f1) \<union> domain(?f2) = domain(f)"
    using domain_restrict domain_of_prod by auto 
  ultimately
  show "induced_surj(f,a,e): domain(f) \<rightarrow> {e} \<union> a"
    by simp
  assume "x \<in> f-``a"
  then 
  have "?f2`x = f`x"
    using restrict by simp
  moreover from \<open>x \<in> f-``a\<close> and 1 
  have "x \<notin> domain(?f1)"
    by simp
  ultimately 
  show "induced_surj(f,a,e)`x = f`x" 
    unfolding induced_surj_def using fun_disjoint_apply2[of x ?f1 ?f2] by simp
qed
  
lemma induced_surj_is_surj : 
  assumes 
    "e\<in>a" "function(f)" "domain(f) = \<alpha>" "\<And>y. y \<in> a \<Longrightarrow> \<exists>x\<in>\<alpha>. f ` x = y" 
  shows
    "induced_surj(f,a,e) \<in> surj(\<alpha>,a)"
  unfolding surj_def
proof (intro CollectI ballI)
  from assms 
  show "induced_surj(f,a,e): \<alpha> \<rightarrow> a"
    using induced_surj_type[of f a e] cons_eq cons_absorb by simp
  fix y
  assume "y \<in> a"
  with assms 
  have "\<exists>x\<in>\<alpha>. f ` x = y" 
    by simp
  then
  obtain x where "x\<in>\<alpha>" "f ` x = y" by auto
  with \<open>y\<in>a\<close> assms
  have "x\<in>f-``a" 
    using vimage_iff function_apply_Pair[of f x] by auto
  with \<open>f ` x = y\<close> assms
  have "induced_surj(f, a, e) ` x = y"
    using induced_surj_type by simp
  with \<open>x\<in>\<alpha>\<close> show
    "\<exists>x\<in>\<alpha>. induced_surj(f, a, e) ` x = y" by auto
qed
  
definition
  choice_ax :: "(i\<Rightarrow>o) \<Rightarrow> o" where
  "choice_ax(M) == \<forall>x[M]. \<exists>a[M]. \<exists>f[M]. ordinal(M,a) \<and> surjection(M,a,x,f)"
  
context M_basic begin 
  
lemma choice_ax_abs :
  "choice_ax(M) \<longleftrightarrow> (\<forall>x[M]. \<exists>a[M]. \<exists>f[M]. Ord(a) \<and> f \<in> surj(a,x))"
  unfolding choice_ax_def
  by (simp)
    
end    (* M_basic *)
  
context G_generic begin
  
definition
  upair_name :: "i \<Rightarrow> i \<Rightarrow> i" where
  "upair_name(\<tau>,\<rho>) == {\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>}"
  
definition
  opair_name :: "i \<Rightarrow> i \<Rightarrow> i" where
  "opair_name(\<tau>,\<rho>) == upair_name(upair_name(\<tau>,\<tau>),upair_name(\<tau>,\<rho>))"
  
lemma val_upair_name : "val(G,upair_name(\<tau>,\<rho>)) = {val(G,\<tau>),val(G,\<rho>)}"
  unfolding upair_name_def using val_Upair  generic one_in_G one_in_P by simp
    
lemma val_opair_name : "val(G,opair_name(\<tau>,\<rho>)) = <val(G,\<tau>),val(G,\<rho>)>"
  unfolding opair_name_def Pair_def using val_upair_name  by simp
    
lemma val_RepFun_one: "val(G,{\<langle>f(x),one\<rangle> . x\<in>a}) = {val(G,f(x)) . x\<in>a}"
proof -
  let ?A = "{f(x) . x \<in> a}"
  let ?Q = "\<lambda><x,p> . p = one"
  have "one \<in> P\<inter>G" using generic one_in_G one_in_P by simp
  have "{<f(x),one> . x \<in> a} = {t \<in> ?A \<times> P . ?Q(t)}" 
    using one_in_P by force
  then
  have "val(G,{<f(x),one>  . x \<in> a}) = val(G,{t \<in> ?A \<times> P . ?Q(t)})"
    by simp
  also
  have "... = {val(G,t) .. t \<in> ?A , \<exists>p\<in>P\<inter>G . ?Q(<t,p>)}"
    using val_of_name_alt by simp
  also
  have "... = {val(G,t) . t \<in> ?A }"
    using \<open>one\<in>P\<inter>G\<close> by force
  also
  have "... = {val(G,f(x)) . x \<in> a}"
    by auto
  finally show ?thesis by simp
qed
  
end (* G_generic *)

locale G_generic_extra_repl = G_generic +
  (*     ?f_dot="{\<langle>opair_name(check(\<beta>),s`\<beta>),one\<rangle>. \<beta>\<in>\<alpha>}" *)
  assumes check_repl  : "strong_replacement(##M,\<lambda>p y. y =check(p))"
begin
  
theorem choice_in_MG: 
  assumes "choice_ax(##M)"
  shows "choice_ax(##M[G])"
proof -
  interpret mgb: M_basic"##M[G]" sorry
  {
    fix a
    assume "a\<in>M[G]"
    then
    obtain \<tau> where "\<tau>\<in>M" "val(G,\<tau>) = a" 
      using GenExt_def by auto
    with \<open>\<tau>\<in>M\<close>
    have "domain(\<tau>)\<in>M"
      using domain_closed by simp
    then
    obtain s \<alpha> where "s\<in>surj(\<alpha>,domain(\<tau>))" "Ord(\<alpha>)" "s\<in>M" "\<alpha>\<in>M"
      using assms choice_ax_abs by auto
    then
    have "\<alpha>\<in>M[G]"         
      using M_subset_MG generic one_in_G subsetD by blast
    let ?A="domain(\<tau>)\<times>P"
    let ?g = "{opair_name(check(\<beta>),s`\<beta>). \<beta>\<in>\<alpha>}"
    have "?g \<in> M" sorry
    let ?f_dot="{\<langle>opair_name(check(\<beta>),s`\<beta>),one\<rangle>. \<beta>\<in>\<alpha>}"
    have "?f_dot = ?g \<times> {one}" by blast
    from one_in_M have "{one} \<in> M" using singletonM by simp
    define f where
      "f == val(G,?f_dot)" 
    from \<open>{one}\<in>M\<close> \<open>?g\<in>M\<close> \<open>?f_dot = ?g\<times>{one}\<close> 
    have "?f_dot\<in>M" 
      using cartprod_closed by simp
    then
    have "f \<in> M[G]"
      unfolding f_def by (blast intro:GenExtI)
    have "f = {val(G,opair_name(check(\<beta>),s`\<beta>)) . \<beta>\<in>\<alpha>}"
      unfolding f_def using val_RepFun_one by simp
    also
    have "... = {<\<beta>,val(G,s`\<beta>)> . \<beta>\<in>\<alpha>}"
      using val_opair_name valcheck generic one_in_G one_in_P by simp
    finally
    have "f = {<\<beta>,val(G,s`\<beta>)> . \<beta>\<in>\<alpha>}" .
    then
    have 1: "domain(f) = \<alpha>" "function(f)"
      unfolding function_def by auto
    have 2: "y \<in> a \<Longrightarrow> \<exists>x\<in>\<alpha>. f ` x = y" for y
    proof -
      fix y
      assume
        "y \<in> a"
      with \<open>val(G,\<tau>) = a\<close> 
      obtain \<sigma> where  "\<sigma>\<in>domain(\<tau>)" "val(G,\<sigma>) = y"
        using elem_of_val[of y _ \<tau>] by blast
      with \<open>s\<in>surj(\<alpha>,domain(\<tau>))\<close> 
      obtain \<beta> where "\<beta>\<in>\<alpha>" "s`\<beta> = \<sigma>" 
        unfolding surj_def by auto
      with \<open>val(G,\<sigma>) = y\<close>
      have "val(G,s`\<beta>) = y" 
        by simp
      with \<open>f = {<\<beta>,val(G,s`\<beta>)> . \<beta>\<in>\<alpha>}\<close> \<open>\<beta>\<in>\<alpha>\<close>
      have "<\<beta>,y>\<in>f" 
        by auto
      with \<open>function(f)\<close>
      have "f`\<beta> = y"
        using function_apply_equality by simp
      with \<open>\<beta>\<in>\<alpha>\<close> show
        "\<exists>\<beta>\<in>\<alpha>. f ` \<beta> = y" 
        by auto
    qed
    then
    have "\<exists>\<alpha>\<in>(M[G]). \<exists>f'\<in>(M[G]). Ord(\<alpha>) \<and> f' \<in> surj(\<alpha>,a)"
    proof (cases "a=0")
      case True
      then
      have "0\<in>surj(0,a)" 
        unfolding surj_def by simp
      then
      show ?thesis using zero_in_MG by auto
    next
      case False
      with \<open>a\<in>M[G]\<close> 
      obtain e where "e\<in>a" "e\<in>M[G]" 
        using Transset_MG Transset_intf by blast
      with 1 and 2
      have "induced_surj(f,a,e) \<in> surj(\<alpha>,a)"
        using induced_surj_is_surj by simp
      moreover from \<open>f\<in>M[G]\<close> \<open>a\<in>M[G]\<close> \<open>e\<in>M[G]\<close>
      have "induced_surj(f,a,e) \<in> M[G]"
        unfolding induced_surj_def 
        by (simp del:setclass_iff add:setclass_iff[symmetric])
      moreover note
        \<open>\<alpha>\<in>M[G]\<close> \<open>Ord(\<alpha>)\<close>
      ultimately show ?thesis by auto
    qed
  }
  then
  show ?thesis using mgb.choice_ax_abs by simp
qed
  
end (* G_generic_extra_repl *)
  
end