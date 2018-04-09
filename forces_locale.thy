theory forces_locale imports Formula val_check ZFCaxioms begin

locale forcing_poset =
  fixes P leq uno
  assumes uno_in_P:         "uno \<in> P"
      and leq_preord:       "preorder_on(P,leq)"
      and uno_max:          "\<forall>p\<in>P. <p,uno>\<in>leq"

definition (in forcing_poset)
  dense :: "i\<Rightarrow>o" where
  "dense(D) == \<forall>p\<in>P. \<exists>d\<in>D . <d,p>\<in>leq"
  
definition (in forcing_poset)
  generic :: "i\<Rightarrow>o" where
  "generic(G) == \<forall>D. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0"
  
locale M_ctm =
  fixes M enum
  assumes trans_M:          "Transset(M)"
      and M_model_ZF:       "satT(M,ZFTh,[])"
      and M_countable:      "enum\<in>bij(M,\<omega>)"
      
(* Prototyping Forcing relation and theorems as a locale*)
locale forcing_thms = forcing_poset + M_ctm +
  fixes forces
  assumes P_in_M:           "P \<in> M"
      and forces_type:      "forces(\<phi>,x,y,z,w) \<in> formula"
      and forces_example:   "\<forall>p\<in> P. forces(\<phi>,P,uno,leq,p)\<in>formula" (* only to fix types *)
      and truth_lemma:      "sats(M,forces(\<phi>,P,leq,uno,p),env') \<longleftrightarrow>
                 (\<forall>G.(G\<subseteq>P \<and> generic(G)\<and> p\<in>G)\<longrightarrow>sats(gen_ext(M,P,G),\<phi>,map(valR(M,P,G),env)))"
                 (* aquí hay que cambiar env' por env++[P,leq,uno,p] *)
      
theorem (in forcing_thms) separation_in_genext:
    "\<forall>p\<in>formula. sats(gen_ext(M,P,G),ZFSeparation(p),[])"
oops
end