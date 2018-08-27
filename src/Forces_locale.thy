theory Forces_locale imports Interface Forcing_data Names begin
   
lemma aux_VoN : "N\<in>M \<Longrightarrow>  domain(N) \<subseteq> trancl(Memrel(eclose(M)))-``{N}"
  apply clarify
  apply (rule vimageI [of _ N], simp_all)
   apply (rule_tac b="<x,y>" in rtrancl_into_trancl1, rule trancl_into_rtrancl)
   apply (rule_tac b="{x}" in rtrancl_into_trancl1, rule trancl_into_rtrancl)
    apply (rule MemrelI [THEN r_into_trancl], simp)
       prefer 3 apply (rule  MemrelI)
         prefer 6 apply (rule  MemrelI)
      apply (tactic {* distinct_subgoals_tac *})
       apply auto
      prefer 5  apply (rule_tac A="{x}" in ecloseD)
       apply (tactic {* distinct_subgoals_tac *})
       apply (rule_tac A="<x,y>" in ecloseD)
       apply (tactic {* distinct_subgoals_tac *})
     apply (rule_tac A="N" in ecloseD)
      apply (tactic {* distinct_subgoals_tac *})
     apply (rule arg_into_eclose)
     apply (simp_all add:Pair_def)
  done
  
lemma [trans] : "x=y \<Longrightarrow> y\<subseteq>z \<Longrightarrow> x\<subseteq>z"
                "x\<subseteq>y \<Longrightarrow> y=z \<Longrightarrow> x\<subseteq>z"
  by simp_all
 
    
(* Prototyping Forcing relation and theorems as a locale*)
locale forcing_thms = forcing_data +
  fixes forces :: "i \<Rightarrow> i"
  assumes definition_of_forces: "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                  sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<longleftrightarrow>
                  (\<forall>G.(M_generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],\<phi>,map(val(G),env)))"
      and  definability[TC]: "\<phi>\<in>formula \<Longrightarrow> forces(\<phi>) \<in> formula"
      and  arity_forces:     "\<phi>\<in>formula \<Longrightarrow> arity(forces(\<phi>)) = arity(\<phi>) #+ 4"
      and   truth_lemma:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                 \<forall>G.(M_generic(G) \<and> p\<in>G)\<longrightarrow>
                  ((\<exists>p\<in>P.(sats(M,forces(\<phi>), [P,leq,one,p] @ env))) \<longleftrightarrow>
                  (sats(M[G],\<phi>,map(val(G),env))))"
      and  streghtening:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> q\<in>P \<Longrightarrow> <q,p>\<in>leq \<Longrightarrow>
                               sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<Longrightarrow>
                               sats(M,forces(\<phi>), [P,leq,one,q] @ env)"
      and density_lemma:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                    sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<longleftrightarrow> 
                    dense_below({q\<in>P. sats(M,forces(\<phi>), [P,leq,one,q] @ env)},p)"

begin  (*************** CONTEXT: forcing_thms *****************)
  
lemma
  "a\<in>M \<Longrightarrow> b\<in>M \<Longrightarrow> env\<in>list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow>
  val(G,{x\<in>domain(\<pi>)\<times>P. \<exists>\<theta> p. x=<\<theta>,p> \<and> (\<forall>F. M_generic(F) \<and> p\<in>F \<longrightarrow>
         sats(M[F],\<phi>,[val(F,\<theta>),val(F,\<pi>),val(F,\<sigma>)]))})
 \<subseteq>
  {x\<in>val(G,\<pi>). sats(M[F],\<phi>,[val(F,\<theta>),val(F,\<pi>),val(F,\<sigma>)])} "
proof -
  have
              "val(G,{x\<in>domain(\<pi>)\<times>P. \<exists>\<theta> p. x=<\<theta>,p> \<and> (\<forall>F. M_generic(F) \<and> p\<in>F \<longrightarrow> 
               sats(M[F],\<phi>,[val(F,\<theta>),val(F,\<pi>),val(F,\<sigma>)]))}) = 
               {val(G,x) .. x\<in>domain(\<pi>)\<times>P, \<exists>\<theta> p. x=<\<theta>,p> \<and> (\<forall>F. M_generic(F) \<and> p\<in>F \<longrightarrow> 
               sats(M[F],\<phi>,[val(F,\<theta>),val(F,\<pi>),val(F,\<sigma>)]))}"  
              (is  "val(G,{x\<in>_. \<exists>\<theta> p. ?R(x,\<theta>,p) \<and> (\<forall>F. ?Q(F,p) \<longrightarrow> ?P(F,\<phi>,\<theta>,\<pi>,\<sigma>))}) = ?x")
  oops
end    (*************** CONTEXT: forcing_thms *****************)
  
end