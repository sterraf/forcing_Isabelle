theory Union_Axiom 
  imports Forcing_data Names  
begin

context forcing_data
begin


lemma Union_aux : 
  assumes "a \<in> M[G]"
  shows "\<exists> b \<in> M[G] . \<Union> a \<subseteq> b"
proof - 
    from \<open>a \<in> M[G]\<close> obtain \<tau> where
    "\<tau> \<in> M" "a = val(G,\<tau>)" "domain(\<tau>) \<in> M" and "\<Union> (domain(\<tau>)) \<in> M" (is "?\<pi> \<in> M")
    using GenExtD  domain_closed Union_closed by force
  then have "val(G,?\<pi>) \<in> M[G]" using GenExtI by simp
  {
    fix x
    assume "x \<in> val(G,\<tau>)"
    then obtain \<theta> p where
      "p \<in> G" "<\<theta>,p> \<in> \<tau>" "val(G,\<theta>) = x"
      using elem_of_val_pair by blast
    then have "\<theta> \<in> domain(\<tau>)" "\<theta> \<subseteq> ?\<pi>" using Union_upper by auto
    then have "val(G,\<theta>) \<subseteq> val(G,?\<pi>)" using val_mono by simp
    with \<open>val(G,\<theta>)=x\<close> have "x \<subseteq> val(G,?\<pi>)" by simp
  }
  with \<open>a=val(G,\<tau>)\<close> have "\<Union> a \<subseteq> val(G,?\<pi>)" (is "_ \<subseteq> ?b") using Union_subset_iff by auto
  with \<open>val(G,?\<pi>) \<in> M[G]\<close> show ?thesis by auto
qed

definition Union_name :: "i \<Rightarrow> i" where
  "Union_name(\<tau>) == 
    {<\<theta>,p> \<in> M \<times> P . \<exists> \<sigma> \<in> M . \<exists> q \<in> P . <\<sigma>,q> \<in> \<tau> \<and> (\<exists> r \<in> P. <\<theta>,r> \<in> \<sigma> \<and> <p,r> \<in> leq \<and> <p,q> \<in> leq) }"
    
lemma Union_name_M : assumes "\<tau> \<in> M"
  shows "Union_name(\<tau>) \<in> M"
    (* We need to internalize the poset in order to use separation_closed. *)
  sorry 

lemma domD : assumes "\<tau> \<in> M" and "\<sigma> \<in> domain(\<tau>)"
  shows "\<sigma> \<in> M"
 proof - 
  from \<open>\<tau> \<in> M\<close> have "domain(\<tau>) \<in> M"
    using domain_closed by simp
  with \<open>\<sigma> \<in> domain(\<tau>)\<close> have "\<sigma> \<in> M" 
    using Transset_M trans_M by blast
  then show ?thesis by simp
qed
  
lemma Union_MG : 
  assumes "a \<in> M[G]" and "a = val(G,\<tau>)" and "filter(G)" and "\<tau> \<in> M"
  shows "\<Union> a = val(G,Union_name(\<tau>)) \<and> big_union(##M[G],a,val(G,Union_name(\<tau>)))"
proof -
  {
    fix x
    assume "x \<in> \<Union> (val(G,\<tau>))"
    then obtain i where "i \<in> val(G,\<tau>)" "x \<in> i" by blast
    with \<open>\<tau> \<in> M\<close> obtain \<sigma> q where
      "q \<in> G" "<\<sigma>,q> \<in> \<tau>" "val(G,\<sigma>) = i" "\<sigma> \<in> M" 
      using elem_of_val_pair domD by blast    
    with \<open>x \<in> i\<close> obtain \<theta> r where
      "r \<in> G" "<\<theta>,r> \<in> \<sigma>" "val(G,\<theta>) = x" "\<theta> \<in> M"
      using elem_of_val_pair domD by blast
    with \<open>filter(G)\<close> \<open>q\<in>G\<close> \<open>r\<in>G\<close> obtain p where
      "p \<in> G" "<p,r> \<in> leq" "<p,q> \<in> leq" "p \<in> P" "r \<in> P" "q \<in> P"
      using low_bound_filter filterD by blast    
    with \<open><\<theta>,r> \<in> \<sigma>\<close> \<open><\<sigma>,q> \<in> \<tau>\<close> \<open>\<sigma> \<in> M\<close> \<open>\<theta> \<in> M\<close> 
    have "<\<theta>,p> \<in> Union_name(\<tau>)" unfolding Union_name_def by force
    with \<open>p\<in>P\<close> \<open>p\<in>G\<close> have "val(G,\<theta>) \<in> val(G,Union_name(\<tau>))" 
      using val_of_elem by simp
    with \<open>val(G,\<theta>)=x\<close> have "x \<in> val(G,Union_name(\<tau>))" by simp
  }
  with \<open>a=val(G,\<tau>)\<close> have 1: "x \<in> \<Union> a \<Longrightarrow> x \<in> val(G,Union_name(\<tau>))" for x by simp
  { fix x 
    assume "\<exists>y[##M[G]]. y \<in> a \<and> x \<in> y"
    then obtain y where
      "y \<in> M[G]" "y \<in> a" "x \<in> y" by force
    then have "x \<in> \<Union> a" by blast
    then have "x \<in> val(G,Union_name(\<tau>))" using 1 by simp
  }
  then have 2:"\<exists>y[##M[G]]. y \<in> a \<and> x \<in> y \<Longrightarrow> x \<in> val(G,Union_name(\<tau>))" for x .
  {
    fix x
    assume "x \<in> (val(G,Union_name(\<tau>)))"
    then obtain \<theta> p where
      "p \<in> G" "<\<theta>,p> \<in> Union_name(\<tau>)" "val(G,\<theta>) = x"
      using elem_of_val_pair by blast
    with \<open>filter(G)\<close> have "p\<in>P" using filterD by simp
    from \<open><\<theta>,p> \<in> Union_name(\<tau>)\<close> obtain \<sigma> q r where
      "\<sigma> \<in> M" "q \<in> P" "r \<in> P" "<\<sigma>,q> \<in> \<tau> " "<\<theta>,r> \<in> \<sigma>" "<p,r> \<in> leq" "<p,q> \<in> leq"
      unfolding Union_name_def by force
    with \<open>p\<in>G\<close> \<open>filter(G)\<close> have "r \<in> G" "q \<in> G"
    using filter_leqD by auto
  with \<open><\<theta>,r> \<in> \<sigma>\<close> \<open><\<sigma>,q>\<in>\<tau>\<close> \<open>q\<in>P\<close> \<open>r\<in>P\<close> have
    "val(G,\<sigma>) \<in> val(G,\<tau>)" "val(G,\<theta>) \<in> val(G,\<sigma>)"
    using val_of_elem by simp_all
  then have "val(G,\<theta>) \<in> \<Union> val(G,\<tau>)" by blast
  with \<open>val(G,\<theta>)=x\<close> \<open>a=val(G,\<tau>)\<close> have
    "x \<in> \<Union> a" by simp
  from \<open>val(G,\<theta>) = x\<close> \<open>\<sigma>\<in>M\<close> \<open>val(G,\<theta>) \<in> val(G,\<sigma>)\<close> have 
    "(##M[G])(val(G,\<sigma>))" "x \<in> val(G,\<sigma>)" using GenExtI by simp_all
  with \<open>a=val(G,\<tau>)\<close> \<open>val(G,\<sigma>) \<in> val(G,\<tau>)\<close> have 
    "val(G,\<sigma>) \<in> a" by simp
  with \<open>(##M[G])(val(G,\<sigma>))\<close> \<open>x \<in> val(G,\<sigma>)\<close> have
    "\<exists>y[##M[G]]. x \<in> y \<and> y \<in> a" by blast
  with \<open>x \<in> \<Union> a\<close> have "\<exists>y[##M[G]]. x \<in> y \<and> y \<in> a" "x \<in> \<Union> a" by simp_all
}
  with \<open>a=val(G,\<tau>)\<close> have 3: "x \<in> val(G,Union_name(\<tau>)) \<Longrightarrow> x \<in> \<Union> a \<and> 
                             (\<exists>y[##M[G]]. x \<in> y \<and> y \<in> a)" for x by blast
  then have 4: "\<Union> a = val(G,Union_name(\<tau>))" using 1 by blast
  then have "big_union(##M[G],a,val(G,Union_name(\<tau>)))" unfolding big_union_def using 2 3 by blast
  then show ?thesis using 4 by simp
qed
        
lemma union_in_MG : assumes "filter(G)"
  shows "Union_ax(##M[G])"
  proof -
  {fix a
   assume "a \<in> M[G]"
   then obtain \<tau> where
     "\<tau> \<in> M" "a=val(G,\<tau>)"
     using GenExtD by blast
   then have "Union_name(\<tau>) \<in> M" (is "?\<pi> \<in> _") using Union_name_M by simp
   then have "val(G,?\<pi>) \<in> M[G]" (is "?U \<in> _") using GenExtI by simp
   then have 1:"(##M[G])(val(G,?\<pi>))" by simp
   with \<open>a\<in>M[G]\<close> \<open>\<tau> \<in> M\<close> \<open>filter(G)\<close> \<open>a=val(G,\<tau>)\<close>  have "big_union(##M[G],a,?U)" 
     using Union_MG by blast
   then  have "\<exists>z[##M[G]]. big_union(##M[G],a,z)" using 1 by blast
  }
  then have "Union_ax(##M[G])" unfolding Union_ax_def by force
  then show ?thesis by simp
 qed

end
end