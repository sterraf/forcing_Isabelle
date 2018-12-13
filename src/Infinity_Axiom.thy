theory Infinity_Axiom 
  imports Forces_locale 
begin

locale G_generic_extra = G_generic + M_extra_assms  
begin

lemma infinty_in_MG : "infinity_ax(##M[G])"
proof -
  from infinity_ax obtain I where
   Eq1: "I\<in>M" "0 \<in> I" "\<forall>y\<in>M. y \<in> I \<longrightarrow> succ(y) \<in> I"
   unfolding infinity_ax_def  by auto
  then have
    "check(I) \<in> M" 
    using check_in_M by simp
  then have 
    "I\<in> M[G]" 
    using valcheck generic one_in_G one_in_P GenExtI[of "check(I)" G] by simp
  have
    "y\<in>M[G] \<Longrightarrow>  y \<in> I \<Longrightarrow> succ(y) \<in> I \<inter> M[G]" for y
  proof
    assume 
      "y\<in>M[G]" "y \<in> I"
    with Eq1 have
      "y\<in>M" 
      using trans_M Transset_intf by blast
    with Eq1 \<open>y\<in>I\<close> show 
      "succ(y)\<in>I" by simp
    with \<open>y\<in>I\<close> \<open>I\<in>M\<close> have
      "succ(y)\<in>M" 
      using trans_M Transset_intf by blast
    then show
      "succ(y) \<in> M[G]"
      using valcheck generic one_in_G one_in_P 
        check_in_M GenExtI[of "check(succ(y))" G ] by simp
  qed     
  with Eq1 \<open>I\<in>M[G]\<close>  show ?thesis 
    unfolding infinity_ax_def using zero_in_MG by auto
qed

end   (* context: G_generic_extra *)
end