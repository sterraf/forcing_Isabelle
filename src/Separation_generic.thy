theory Separation_generic imports Forces_locale begin

  locale forcing_thms = forcing_poset + forcing_data +
  fixes forces :: "i \<Rightarrow> i"
  assumes definition_of_forces: "\<forall>env\<in>list(M).
                  sats(M,forces(\<phi>), [P,leq,uno,p] @ env) \<longleftrightarrow>
                  (\<forall>G.(generic(G)\<and> p\<in>G)\<longrightarrow>sats(gen_ext(M,P,G),\<phi>,map(valR(M,P,G),env)))"
      and definability:      "forces(\<phi>) \<in> formula"
      and truth_lemma:      "\<forall>env\<in>list(M).\<forall>G.(generic(G) \<and> p\<in>G)\<longrightarrow>
                  ((\<exists>p\<in>P.(sats(M,forces(\<phi>), [P,leq,uno,p] @ env))) \<longleftrightarrow>
                  (sats(gen_ext(M,P,G),\<phi>,map(valR(M,P,G),env))))"

lemma (in forcing_thms)
  "\<phi>\<in>formula \<Longrightarrow> \<psi>\<in>formula \<Longrightarrow> 
    \<forall>u\<in>M. \<forall>l\<in>M. \<forall>Q\<in>M. \<forall>s\<in>M. \<forall>r\<in>M. \<forall>d\<in>M.
      sats(M,[d,r,s,Q,l,u],
        Exists(Exists(And(pair_fm(0,1,2),
          forces(And(Member(0,1),\<phi>))))))" 
  oops
   
lemma (in forcing_thms)
    "sats(M,forces(And(Member(0,1),\<phi>)),[P,leq,uno,p,\<theta>,\<pi>,\<sigma>])
      \<Longrightarrow> valR(M,P,G,{w\<in>domain(\<pi>)\<times>P. x=x}) =x"  (* Enunciado mal *)
  oops
    
      
lemma (in forcing_thms) bounded_separation_in_genext:
    "\<forall>p\<in>formula. arity(p) = 3 \<longrightarrow> sats(gen_ext(M,P,G),ZFSeparation(p),[])"
oops
  
end