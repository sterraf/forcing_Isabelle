theory Gen_Ext_Sep_test imports Forces_locale Separation_Lemmas begin

context forcing_thms begin  

lemmas transitivity = Transset_intf trans_M

lemma one_in_M: "one \<in> M"
  by (insert one_in_P P_in_M, simp add: transitivity)
    
lemma iff_impl_trans: "Q\<longleftrightarrow>R \<Longrightarrow> R\<longrightarrow>S \<Longrightarrow> Q \<longrightarrow>S"
                      "Q\<longrightarrow>R \<Longrightarrow> R\<longleftrightarrow>S \<Longrightarrow> Q \<longrightarrow>S"
                      "Q\<longrightarrow>R \<Longrightarrow> R\<longrightarrow> S \<Longrightarrow> Q\<longrightarrow> S"
  by simp_all  

    
lemma zero_in_Gen_Ext : 
  "0 \<in> M[G]" 
proof -
  from zero_in_M and def_val have 
    "0 = val(G,0)" 
    by auto
  also from def_GenExt2 and zero_in_M have 
    "... \<in> M[G]" 
  by simp
  finally show ?thesis .
qed
    
     
lemma Gen_Ext_mtriv :  
  "M_generic(G) \<Longrightarrow> Union_ax(##M[G]) \<Longrightarrow> M_trivial_no_repl(##M[G])"
  sorry
    
(* theorem separation_in_genext: *)    
theorem separation_preserv:
  assumes 
      "M_generic(G)" and "\<phi>\<in>formula"  and "arity(\<phi>) = 1 \<or> arity(\<phi>)=2" 
    shows  
      "(\<forall>a\<in>M. separation(##M[G],\<lambda>x. sats(M[G],\<phi>,[x,a])))"
proof -
  note 
      \<open>arity(\<phi>) = 1 \<or> arity(\<phi>)=2\<close>
  then consider (1) "arity(\<phi>) = 1" | (2) "arity(\<phi>) = 2" ..
  then show ?thesis
  proof cases
    case (1) 
    then show ?thesis sorry
  next
    case (2)
    then show ?thesis sorry
  qed
qed

    
end