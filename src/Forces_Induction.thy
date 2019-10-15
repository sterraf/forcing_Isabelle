theory Forces_Induction
imports
  Forcing_Theorems 
begin

context forcing_thms begin

lemma map_val_in_MG: "env\<in>list(M) \<Longrightarrow> map(val(G),env)\<in>list(M[G])" for G 
  sorry

lemma 
  assumes
    "p\<in>P" "\<phi>\<in>formula" "\<psi>\<in>formula" "env\<in>list(M)"
  shows
    "sats(M,forces(And(\<phi>,\<psi>)), [P,leq,one,p] @ env) \<longleftrightarrow>
    sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<and> sats(M,forces(\<psi>), [P,leq,one,p] @ env)"
proof -
  from assms have
    "sats(M,forces(And(\<phi>,\<psi>)), [P,leq,one,p] @ env) \<longleftrightarrow> 
     (\<forall>G. (M_generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],And(\<phi>,\<psi>),map(val(G),env)))"
    using definition_of_forces by simp
  also from assms have
    "... \<longleftrightarrow> (\<forall>G. (M_generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],\<phi>,map(val(G),env))) \<and> 
     (\<forall>G. (M_generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],\<psi>,map(val(G),env)))"
    using map_val_in_MG by auto
  also from assms have
    "... \<longleftrightarrow> sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<and> sats(M,forces(\<psi>), [P,leq,one,p] @ env)"
    using definition_of_forces by simp
  finally show ?thesis .
qed  
    
lemma 
  assumes
    "p\<in>P" "\<phi>\<in>formula" "env\<in>list(M)"
  shows
    "sats(M,forces(Neg(\<phi>)), [P,leq,one,p] @ env) \<longleftrightarrow>
    (\<forall>q\<in>P. (<q,p>\<in>leq \<longrightarrow> \<not> sats(M,forces(\<phi>), [P,leq,one,q] @ env)))"
proof (intro iffI ballI impI) 
  assume
    "sats(M,forces(Neg(\<phi>)), [P,leq,one,p] @ env)"
  with assms have
    "(\<forall>G. (M_generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],Neg(\<phi>),map(val(G),env)))"
    using definition_of_forces by simp
  with assms have
    1: "(\<forall>G. (M_generic(G)\<and> p\<in>G)\<longrightarrow>\<not>sats(M[G],\<phi>,map(val(G),env)))"
    using map_val_in_MG by simp
  fix q
  assume
    "q\<in>P" "<q,p>\<in>leq"
  then obtain G where
    "q\<in>G"  "M_generic(G)"
    using generic_filter_existence by auto
  moreover from calculation \<open>p\<in>P\<close> \<open><q,p>\<in>leq\<close> have
    "p\<in>G"
    unfolding M_generic_def using filter_leqD by simp
  moreover from calculation have
    "\<not>sats(M[G],\<phi>,map(val(G),env))" 
    using 1 by simp
  ultimately have
    "\<not> (\<forall>G. (M_generic(G)\<and> q\<in>G)\<longrightarrow>sats(M[G],\<phi>,map(val(G),env)))" 
    by blast
  with assms \<open>q\<in>P\<close> show
    "\<not> sats(M,forces(\<phi>), [P,leq,one,q] @ env)"
    using definition_of_forces by simp
next
  assume
    2: "(\<forall>q\<in>P. (<q,p>\<in>leq \<longrightarrow> \<not> sats(M,forces(\<phi>), [P,leq,one,q] @ env)))"
  with \<open>p\<in>P\<close> have
    "\<not> sats(M,forces(\<phi>), [P,leq,one,p] @ env)"
    using refl_leq by simp
  {
    fix G
    assume
      "p\<in>G" "M_generic(G)"
    then have
      "\<not> sats(M[G],\<phi>,map(val(G),env))"
    proof (intro notI)
      assume
        "sats(M[G],\<phi>,map(val(G),env))"
      with assms \<open>M_generic(G)\<close> obtain r where
        "r\<in>G" "sats(M,forces(\<phi>), [P,leq,one,r] @ env)" "r\<in>P"
        using truth_lemma unfolding M_generic_def using filterD by blast
      moreover from \<open>r\<in>G\<close>  \<open>M_generic(G)\<close> \<open>p\<in>G\<close> obtain q where
        "q\<in>G" "<q,p>\<in>leq" "<q,r>\<in>leq" "q\<in>P"
        unfolding M_generic_def using filterD low_bound_filter by blast
      moreover note assms
      ultimately have
        "sats(M,forces(\<phi>), [P,leq,one,q] @ env)"
        using strengthening by simp
      with 2 \<open><q,p>\<in>leq\<close> \<open>q\<in>P\<close> show
        False by simp
    qed
    with assms have
      "sats(M[G],Neg(\<phi>),map(val(G),env))"
      using map_val_in_MG by simp
  }
  with assms show
    "sats(M,forces(Neg(\<phi>)), [P,leq,one,p] @ env)"
    using definition_of_forces by simp
qed

end  (* forcing_thms *)
end