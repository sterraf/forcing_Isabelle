theory Forces_locale imports Interface2 Pairing_Axiom Union_Axiom begin
   
(* Prototyping Forcing relation and theorems as a locale*)
locale forcing_thms = M_extra_assms +
  fixes forces :: "i \<Rightarrow> i"
  assumes definition_of_forces: "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                  sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<longleftrightarrow>
                  (\<forall>G.(M_generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],\<phi>,map(val(G),env)))"
      and  definability[TC]: "\<phi>\<in>formula \<Longrightarrow> forces(\<phi>) \<in> formula"
      and  arity_forces:     "\<phi>\<in>formula \<Longrightarrow> arity(forces(\<phi>)) = arity(\<phi>) #+ 4"
      and   truth_lemma:     "\<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> M_generic(G) \<Longrightarrow>
                  (\<exists>p\<in>G.(sats(M,forces(\<phi>), [P,leq,one,p] @ env))) \<longleftrightarrow>
                  sats(M[G],\<phi>,map(val(G),env))"
      and  streghtening:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> q\<in>P \<Longrightarrow> <q,p>\<in>leq \<Longrightarrow>
                               sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<Longrightarrow>
                               sats(M,forces(\<phi>), [P,leq,one,q] @ env)"
      and density_lemma:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                    sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<longleftrightarrow> 
                    dense_below({q\<in>P. sats(M,forces(\<phi>), [P,leq,one,q] @ env)},p)"

begin (******************** CONTEXT: forcing_thms ******** *)
end (* forcing_thms *)
  
locale G_generic = forcing_thms + 
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

lemma G_nonempty: "G\<noteq>0"
proof -
  have "P\<subseteq>P" ..
  with P_in_M P_dense \<open>P\<subseteq>P\<close> show
    "G \<noteq> 0"
    using generic unfolding M_generic_def by auto
qed
    
interpretation MGtriv :  M_trivial_no_repl"##M[G]"
  using generic Union_MG pairing_in_MG zero_in_MG Transset_intf Transset_MG
  unfolding M_trivial_no_repl_def by simp    

end
end