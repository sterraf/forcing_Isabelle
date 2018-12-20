theory Pairing_Axiom imports Names Interface begin

context forcing_data
begin

lemma valsigma :
  "one \<in> G \<Longrightarrow> {\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>} \<in> M \<Longrightarrow>
   val(G,{\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>}) = {val(G,\<tau>),val(G,\<rho>)}"
  by (insert one_in_P, rule trans, subst def_val,auto simp add: Sep_and_Replace)
      
lemma pairing_in_MG : 
  assumes "M_generic(G)"
  shows "upair_ax(##M[G])"
proof - 
  {
    fix x y
    have "one\<in>G" using assms one_in_G by simp
    from assms have "G\<subseteq>P" 
      unfolding M_generic_def and filter_def by simp
    with \<open>one\<in>G\<close>have "one\<in>P" using subsetD by simp
    then have "one\<in>M" using Transset_intf[OF trans_M _ P_in_M] by simp
    assume "x \<in> M[G]" "y \<in> M[G]"
    then obtain \<tau> \<rho> where
      0 : "val(G,\<tau>) = x" "val(G,\<rho>) = y" "\<rho> \<in> M"  "\<tau> \<in> M"
      using GenExtD by blast
    with \<open>one\<in>M\<close> have "\<langle>\<tau>,one\<rangle> \<in> M" "\<langle>\<rho>,one\<rangle>\<in>M" 
      using pair_in_M_iff by auto
    then have 1: "{\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>} \<in> M" (is "?\<sigma> \<in> _")
      using upair_in_M_iff by simp
    then have "val(G,?\<sigma>) \<in> M[G]"
      using GenExtI by simp
    with 1 have "{val(G,\<tau>),val(G,\<rho>)} \<in> M[G]" 
      using valsigma assms one_in_G by simp
    with 0 have "{x,y} \<in> M[G]" by simp
    }
    then show ?thesis unfolding upair_ax_def upair_def by auto
qed

end
end
  
