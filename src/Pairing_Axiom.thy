section\<open>The Axiom of Pairing in $M[G]$\<close>

theory Pairing_Axiom
  imports
    Names
begin

context forcing_data1
begin

lemma val_Upair :
  "\<one> \<in> G \<Longrightarrow> val(P,G,{\<langle>\<tau>,\<one>\<rangle>,\<langle>\<rho>,\<one>\<rangle>}) = {val(P,G,\<tau>),val(P,G,\<rho>)}"
  by (insert one_in_P, rule trans, subst def_val,auto)

lemma pairing_in_MG :
  assumes "M_generic(G)"
  shows "upair_ax(##M[G])"
proof -
  {
    fix x y
    have "\<one>\<in>G" using assms one_in_G by simp
    from assms
    have "G\<subseteq>P" unfolding M_generic_def and filter_def by simp
    with \<open>\<one>\<in>G\<close>
    have "\<one>\<in>P" using subsetD by simp
    then
    have "\<one>\<in>M" using transitivity[OF _ P_in_M] by simp
    assume "x \<in> M[G]" "y \<in> M[G]"
    then
    obtain \<tau> \<rho> where
      0 : "val(P,G,\<tau>) = x" "val(P,G,\<rho>) = y" "\<rho> \<in> M"  "\<tau> \<in> M"
      using GenExtD by blast
    with \<open>\<one>\<in>M\<close>
    have "\<langle>\<tau>,\<one>\<rangle> \<in> M" "\<langle>\<rho>,\<one>\<rangle>\<in>M" using pair_in_M_iff by auto
    then
    have 1: "{\<langle>\<tau>,\<one>\<rangle>,\<langle>\<rho>,\<one>\<rangle>} \<in> M" (is "?\<sigma> \<in> _") using upair_in_M_iff by simp
    then
    have "val(P,G,?\<sigma>) \<in> M[G]" using GenExtI by simp
    with 1
    have "{val(P,G,\<tau>),val(P,G,\<rho>)} \<in> M[G]" using val_Upair assms one_in_G by simp
    with 0
    have "{x,y} \<in> M[G]" by simp
  }
  then show ?thesis unfolding upair_ax_def upair_def by auto
qed

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

end