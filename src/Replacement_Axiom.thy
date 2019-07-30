theory Replacement_Axiom
  imports
    Relative_Univ Separation_Axiom

begin

context G_generic
begin

lemma pow_inter_M:
  assumes
    "x\<in>M" "y\<in>M"
  shows
    "powerset(##M,x,y) \<longleftrightarrow> y = Pow(x) \<inter> M"
  using assms by auto

lemma Vset_abs:  "\<lbrakk> i\<in>M; V\<in>M \<rbrakk> \<Longrightarrow> is_Vfrom(##M,0,i,V) \<longleftrightarrow> V = Vset(i) \<inter> M"
  using Vfrom_abs by (auto simp del:setclass_iff simp add: setclass_iff[symmetric])

lemma Replace_sats_in_MG:
  assumes
    "\<pi> \<in> M" "\<sigma> \<in> M" "val(G,\<pi>) = c" "val(G,\<sigma>) = w"
    "\<phi> \<in> formula" "arity(\<phi>) \<le> 3"
  shows
    "{v. x\<in>c, sats(M[G], \<phi>, [x,v,w])} \<in> M[G]"
  sorry

theorem strong_replacement_in_MG:
  assumes 
    "\<phi>\<in>formula" and "arity(\<phi>) = 1 \<or> arity(\<phi>)=2"
  shows  
    "(\<forall>a\<in>(M[G]). strong_replacement(##M[G],\<lambda>x v. sats(M[G],\<phi>,[x,v,a])))"
proof -
  { 
    fix c v w 
    assume "c\<in>M[G]" "w\<in>M[G]"
    then 
    obtain \<pi> \<sigma> where "val(G, \<pi>) = c" "val(G, \<sigma>) = w" "\<pi> \<in> M" "\<sigma> \<in> M" 
      using GenExt_def by auto
    with assms 
    have Eq1: "{v. x\<in>c, sats(M[G], \<phi>, [x,v,w])} \<in> M[G]"
      using Replace_sats_in_MG by auto
  }
  then
  show ?thesis 
    unfolding strong_replacement_def univalent_def
    apply (intro ballI rallI impI)
    apply (rule_tac x="{v . x \<in> A, sats(M[G], \<phi>, [x, v, a])}" in rexI)
     apply (auto simp add: Transset_intf Transset_MG)

    oops
    find_theorems name:ReplaceI

end (* context G_generic *)

end