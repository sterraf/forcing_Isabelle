theory Powerset_Axiom 
  imports Separation_Axiom Pairing_Axiom Union_Axiom
begin
  
lemma (in M_trivial) powerset_subset_Pow:
  assumes 
    "powerset(M,x,y)" "\<And>z. z\<in>y \<Longrightarrow> M(z)"
  shows 
    "y \<subseteq> Pow(x)"
  using assms unfolding powerset_def
  by (auto)
    
lemma (in M_trivial) powerset_abs: 
  assumes
    "M(x)" "\<And>z. z\<in>y \<Longrightarrow> M(z)"
  shows
    "powerset(M,x,y) \<longleftrightarrow> y = {a\<in>Pow(x) . M(a)}"
proof (intro iffI equalityI)
  (* First show the converse implication by double inclusion *)
  assume 
    "powerset(M,x,y)"
  with assms have
    "y \<subseteq> Pow(x)" 
    using powerset_subset_Pow by simp
  with assms show
    "y \<subseteq> {a\<in>Pow(x) . M(a)}"
    by blast
  {
    fix a
    assume 
      "a \<subseteq> x" "M(a)"
    then have 
      "subset(M,a,x)" by simp
    with \<open>M(a)\<close> \<open>powerset(M,x,y)\<close> have
      "a \<in> y"
      unfolding powerset_def by simp
  }
  then show 
    "{a\<in>Pow(x) . M(a)} \<subseteq> y"
    by auto
next (* we show the direct implication *)
  assume 
    "y = {a \<in> Pow(x) . M(a)}"
  then show
    "powerset(M, x, y)"
    unfolding powerset_def
    by simp
qed
  
lemma Collect_inter_Transset:
  assumes 
    "Transset(M)" "b \<in> M"
  shows
    "{x\<in>b . P(x)} = {x\<in>b . P(x)} \<inter> M"
    using assms unfolding Transset_def
  by (auto)  

context G_generic begin
    
lemma name_components_in_M:
  assumes "<\<sigma>,p>\<in>\<theta>" "\<theta> \<in> M"
  shows   "\<sigma>\<in>M" "p\<in>M"
proof -
  from assms obtain a where
    "\<sigma> \<in> a" "p \<in> a" "a\<in><\<sigma>,p>"
    unfolding Pair_def by auto
  moreover from assms have
    "<\<sigma>,p>\<in>M"
    using trans_M  Transset_intf[of _ "<\<sigma>,p>"] by simp
  moreover from calculation have
    "a\<in>M" 
    using trans_M  Transset_intf[of _ _ "<\<sigma>,p>"] by simp
  ultimately show
    "\<sigma>\<in>M" "p\<in>M" 
    using trans_M  Transset_intf[of _ _ "a"] by simp_all
qed
    
lemma Pow_inter_MG:
  assumes
    "a\<in>M[G]"
  shows
    "Pow(a) \<inter> M[G] \<in> M[G]" 
proof -
  from assms obtain \<tau> where
    "\<tau> \<in> M" "val(G, \<tau>) = a"
    using GenExtD by blast
  let
    ?Q="Pow(domain(\<tau>)\<times>P) \<inter> M"
  from \<open>\<tau>\<in>M\<close> have
    "domain(\<tau>)\<times>P \<in> M"
    using domain_closed cartprod_closed P_in_M   
    by simp
  then have
    "?Q \<in> M"
  proof -
    from power_ax \<open>domain(\<tau>)\<times>P \<in> M\<close> obtain Q where
      "powerset(##M,domain(\<tau>)\<times>P,Q)" "Q \<in> M"
      unfolding power_ax_def by auto
    moreover from calculation have
      "z\<in>Q  \<Longrightarrow> z\<in>M" for z
      using Transset_intf trans_M by blast
    ultimately have
      "Q = {a\<in>Pow(domain(\<tau>)\<times>P) . a\<in>M}"
      using \<open>domain(\<tau>)\<times>P \<in> M\<close> powerset_abs[of "domain(\<tau>)\<times>P" Q]     
      by (simp del:setclass_iff add:setclass_iff[symmetric])
    also have
      " ... = ?Q"
      by auto
    finally show
      "?Q \<in> M" 
      using \<open>Q\<in>M\<close> by simp
  qed
  let
    ?\<pi>="?Q\<times>{one}"
  let
    ?b="val(G,?\<pi>)"
  from \<open>?Q\<in>M\<close> have
    "?\<pi>\<in>M"
    using one_in_P P_in_M Transset_intf transM  
    by (simp del:setclass_iff add:setclass_iff[symmetric])
  from \<open>?\<pi>\<in>M\<close> have
    "?b \<in> M[G]" 
    using GenExtI by simp
  have
    "Pow(a) \<inter> M[G] \<subseteq> ?b"
  proof
    fix c
    assume 
      "c \<in> Pow(a) \<inter> M[G]"
    then obtain \<chi> where
      "c\<in>M[G]" "\<chi> \<in> M" "val(G,\<chi>) = c"
      using GenExtD by blast
    let
      ?\<theta>="{sp\<in>domain(\<tau>)\<times>P . sats(M,forces(Member(0,1)),[P,leq,one,snd(sp),fst(sp),\<chi>])}"
    have  
      "?\<theta> \<in> M"
      sorry
    then have 
      "?\<theta> \<in> ?Q"
      by auto
    then have
      "val(G,?\<theta>) \<in> ?b"
      using one_in_G one_in_P generic val_of_elem [of ?\<theta> one ?\<pi> G]
      by auto
    have
      "val(G,?\<theta>) = c"
    proof
      (* val(G,?\<theta>) \<subseteq> c *)
      {
        fix x
        assume 
          "x \<in> val(G,?\<theta>)"
        then obtain \<sigma> p where
          1: "<\<sigma>,p>\<in>?\<theta>" "p\<in>G" "val(G,\<sigma>) =  x"
          using elem_of_val_pair 
          by blast
        moreover from \<open><\<sigma>,p>\<in>?\<theta>\<close> \<open>?\<theta> \<in> M\<close> have
          "\<sigma>\<in>M"
          using name_components_in_M[of _ _ ?\<theta>]  by auto
        moreover from 1 have
          "sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<chi>])" "p\<in>P" 
          "Member(0,1)\<in>formula"
          by simp_all
        moreover note
          \<open>val(G,\<chi>) = c\<close>       
        ultimately have
          "sats(M[G],Member(0,1),[x,c])"
          using \<open>\<chi> \<in> M\<close> generic definition_of_forces
          by auto
        moreover have
          "x\<in>M[G]" 
          using \<open>val(G,\<sigma>) =  x\<close> \<open>\<sigma>\<in>M\<close> GenExtI by blast
        ultimately have
          "x\<in>c"
          using \<open>c\<in>M[G]\<close> by simp
      }
      then show 
        "val(G,?\<theta>) \<subseteq> c"
        by auto
    next
      (* val(G,?\<theta>) \<supseteq> c *)
      {
        fix x
        assume 
          "x \<in> c"
        with \<open>c \<in> Pow(a) \<inter> M[G]\<close> have
          "x \<in> a" "c\<in>M[G]" "x\<in>M[G]"
          by (auto simp add:Transset_intf Transset_MG)
        with \<open>val(G, \<tau>) = a\<close> obtain \<sigma> where
          "\<sigma>\<in>domain(\<tau>)" "val(G,\<sigma>) =  x"
          using elem_of_val
          by blast
        moreover note \<open>x\<in>c\<close> \<open>val(G,\<chi>) = c\<close>
        moreover from calculation have
          "val(G,\<sigma>) \<in> val(G,\<chi>)"
          by simp
        moreover note \<open>c\<in>M[G]\<close> \<open>x\<in>M[G]\<close>
        moreover from calculation have
          "sats(M[G],Member(0,1),[x,c])"
          by simp
        moreover have
          "Member(0,1)\<in>formula" by simp
        moreover have
          "\<sigma>\<in>M" 
        proof -
          from \<open>\<sigma>\<in>domain(\<tau>)\<close> obtain p where
            "<\<sigma>,p> \<in> \<tau>" 
            by auto
          with \<open>\<tau>\<in>M\<close> show ?thesis 
            using name_components_in_M by blast
        qed
        moreover note \<open>\<chi> \<in> M\<close>
        ultimately obtain p where
          "p\<in>G" "sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<chi>])"
          using generic truth_lemma[of "Member(0,1)" "[\<sigma>,\<chi>]" "G"] 
          by auto
        moreover from \<open>p\<in>G\<close> have 
          "p\<in>P" 
          using generic unfolding M_generic_def filter_def by blast
        ultimately  have 
          "<\<sigma>,p>\<in>?\<theta>"
          using \<open>\<sigma>\<in>domain(\<tau>)\<close> by simp
        with \<open>val(G,\<sigma>) =  x\<close> \<open>p\<in>G\<close> have
          "x\<in>val(G,?\<theta>)"
          using val_of_elem [of _ _ "?\<theta>"] by auto
      }
      then show
        "c \<subseteq> val(G,?\<theta>)"
        by auto
    qed
    with \<open>val(G,?\<theta>) \<in> ?b\<close> show
      "c\<in>?b"
      by simp
  qed
  then have
    "Pow(a) \<inter> M[G] = {x\<in>?b . x\<subseteq>a & x\<in>M[G]}" 
    by auto 
  also from \<open>a\<in>M[G]\<close> have
    " ... = {x\<in>?b . sats(M[G],subset_fm(0,1),[x,a]) & x\<in>M[G]}"
    using Transset_MG by force
  also have 
    " ... = {x\<in>?b . sats(M[G],subset_fm(0,1),[x,a])} \<inter> M[G]"
    by auto
  also from \<open>?b\<in>M[G]\<close> have
    " ... = {x\<in>?b . sats(M[G],subset_fm(0,1),[x,a])}"
    using Collect_inter_Transset Transset_MG 
    by simp
  also have
    " ... \<in> M[G]"
  proof -
    have
      "arity(subset_fm(0,1)) \<le> 2"
      by (simp add:  not_lt_iff_le leI nat_union_abs1)
    moreover note
      \<open>?\<pi>\<in>M\<close> \<open>\<tau>\<in>M\<close> \<open>val(G,\<tau>) = a\<close>
    ultimately show ?thesis
      using Collect_sats_in_MG by auto
  qed
  finally show ?thesis .
qed
end
  
sublocale G_generic \<subseteq> M_trivial"##M[G]"
  using generic Union_MG pairing_in_MG zero_in_MG Transset_intf Transset_MG
  unfolding M_trivial_def by simp 
 
context G_generic begin
theorem power_in_MG :
  "power_ax(##(M[G]))"
  unfolding power_ax_def
proof (intro rallI, simp only:setclass_iff rex_setclass_is_bex)
  fix a
  assume 
    "a \<in> M[G]"
  have
    "{x\<in>Pow(a) . x \<in> M[G]} = Pow(a) \<inter> M[G]"
    by auto
  also from \<open>a\<in>M[G]\<close> have
    " ... \<in> M[G]" 
    using Pow_inter_MG by simp
  finally have
    "{x\<in>Pow(a) . x \<in> M[G]} \<in> M[G]" .
  moreover from \<open>a\<in>M[G]\<close> have
    "powerset(##M[G], a, {x\<in>Pow(a) . x \<in> M[G]})"
    using powerset_abs[of a "{x\<in>Pow(a) . x \<in> M[G]}"]
    by simp
  ultimately show 
    "\<exists>x\<in>M[G] . powerset(##M[G], a, x)"
    by auto
qed
end
end