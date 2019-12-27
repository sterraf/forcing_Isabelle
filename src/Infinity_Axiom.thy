theory Infinity_Axiom 
  imports Pairing_Axiom Union_Axiom
begin  
  
locale G_generic = forcing_data +
    fixes G :: "i"
    assumes generic : "M_generic(G)" 
begin
  
lemma zero_in_MG : 
  "0 \<in> M[G]" 
proof -
  from zero_in_M and elem_of_val have 
    "0 = val(G,0)" 
    by auto
  also from GenExtI and zero_in_M have 
    "... \<in> M[G]" 
  by simp
  finally show ?thesis .
qed 
end

sublocale  G_generic \<subseteq> M_trans"##M[G]"
  using generic zero_in_MG Transset_intf Transset_MG
  unfolding M_trans_def 
  by (simp;blast)

sublocale G_generic \<subseteq> M_trivial"##M[G]"
  using generic Union_MG pairing_in_MG  zero_in_MG Transset_intf Transset_MG
  unfolding M_trivial_def M_trivial_axioms_def M_trans_def 
  by (simp;blast)
    
context G_generic
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
  with \<open>0\<in>I\<close> have "0\<in>M[G]" using Transset_MG Transset_intf by simp
  with \<open>I\<in>M\<close> have "y \<in> M" if "y \<in> I" for y
    using  Transset_intf[OF trans_M _ \<open>I\<in>M\<close>] that by simp
  with \<open>I\<in>M[G]\<close> have "succ(y) \<in> I \<inter> M[G]" if  "y \<in> I" for y
    using that Eq1 Transset_MG Transset_intf by blast
  with Eq1 \<open>I\<in>M[G]\<close> \<open>0\<in>M[G]\<close> show ?thesis 
    unfolding infinity_ax_def by auto
qed

end (* G_generic *)
end
