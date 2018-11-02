theory Forces_locale imports Forcing_data Interface2 Names begin
   
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
end