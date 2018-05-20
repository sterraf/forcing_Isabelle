theory Forces_locale imports Interface Forcing_data begin

context forcing_data
begin
lemma to_M_basic_no_repl :
  "M_basic_no_repl(##M)"
  by (insert trans_M M_model_ZF zero_in_M,rule interface_M_basic)

interpretation M?: M_basic_no_repl "##M" by (rule to_M_basic_no_repl)
end
  
(* Prototyping Forcing relation and theorems as a locale*)
locale forcing_thms = forcing_data +
  fixes forces :: "i \<Rightarrow> i"
  assumes definition_of_forces: "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                  sats(M,forces(\<phi>), [P,leq,uno,p] @ env) \<longleftrightarrow>
                  (\<forall>G.(generic(G)\<and> p\<in>G)\<longrightarrow>sats(gen_ext(M,P,G),\<phi>,map(valR(M,P,G),env)))"
      and  definability:     "\<phi>\<in>formula \<Longrightarrow> forces(\<phi>) \<in> formula"
      and   truth_lemma:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                 \<forall>G.(generic(G) \<and> p\<in>G)\<longrightarrow>
                  ((\<exists>p\<in>P.(sats(M,forces(\<phi>), [P,leq,uno,p] @ env))) \<longleftrightarrow>
                  (sats(gen_ext(M,P,G),\<phi>,map(valR(M,P,G),env))))"
      and  streghtening:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> q\<in>P \<Longrightarrow> <q,p>\<in>leq \<Longrightarrow>
                               sats(M,forces(\<phi>), [P,leq,uno,p] @ env) \<Longrightarrow>
                               sats(M,forces(\<phi>), [P,leq,uno,q] @ env)"
      and density_lemma:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                 \<forall>env\<in>list(M).
                    sats(M,forces(\<phi>), [P,leq,uno,p] @ env) \<longleftrightarrow> 
                    dense_below({q\<in>P. sats(M,forces(\<phi>), [P,leq,uno,q] @ env)},p)"

begin  (*************** CONTEXT: forcing_thms *****************)
  
end
  
end