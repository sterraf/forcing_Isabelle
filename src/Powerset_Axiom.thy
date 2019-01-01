theory Powerset_Axiom 
  imports Separation_Axiom 
begin
lemma (in M_trivial)  
    "\<lbrakk> powerset(M,x,y); M(y) \<rbrakk> \<Longrightarrow> y = {a\<in>Pow(x) . M(a)}"
  sorry
    
lemma (in M_trivial) powerset_abs: 
    "\<lbrakk> M(x); M(y) \<rbrakk> \<Longrightarrow> powerset(M,x,y) \<longleftrightarrow> y = {a\<in>Pow(x) . M(a)}"
  sorry

definition
  powerset_fm :: "i"  where
  "powerset_fm == 0" 
    
context G_generic begin
  
lemma fst_Pair_in_M:
  assumes "<\<sigma>,p>\<in>\<theta>" "\<theta> \<in> M"
  shows   "\<sigma>\<in>M"
  sorry
  
notepad begin
  fix \<tau> a
  assume 
    "\<tau> \<in> M" "val(G, \<tau>) = a"
  then have
    "a \<in> M[G]"
    using GenExtI by blast
  let
    ?Q="Pow(domain(\<tau>)\<times>P) \<inter> M"
  from \<open>\<tau>\<in>M\<close> have
    "domain(\<tau>)\<times>P \<in> M"
    using domain_closed cartprod_closed P_in_M   
    by simp
  then have
    "?Q \<in> M"
    sorry
  let
    ?\<pi>="?Q\<times>{one}"
  let
    ?b="val(G,?\<pi>)"
  from \<open>?Q\<in>M\<close> have
    "?\<pi>\<in>M"
    using one_in_P P_in_M Transset_intf transM  
    by (simp del:setclass_iff add:setclass_iff[symmetric])
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
    from \<open>?\<pi>\<in>M\<close> have
      "?b \<in> M[G]" 
      using GenExtI by simp
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
          using fst_Pair_in_M[of _ _ ?\<theta>]  by auto
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
          sorry
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
  from \<open>a\<in>M[G]\<close> have
    "{x\<in>?b . x\<subseteq>a}  = {x\<in>?b . sats(M[G],subset_fm(0,1),[x,a])}"
    using Transset_MG[of G] 
  
    also have
      "{x\<in>?b . x\<subseteq>a & x\<in>M[G]} \<in> M[G]"
      using separation_in_MG
end
  
end