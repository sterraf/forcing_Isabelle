theory Separation_generic imports   Formula Names ZFCAxioms_formula forcing_posets begin

locale forcing_data = forcing_poset +
  fixes M enum
  assumes trans_M:          "Transset(M)"
      and M_model_ZF:       "satT(M,ZFTh,[])"
      and M_countable:      "enum\<in>bij(nat,M)"
      and P_in_M:           "P \<in> M"
      (* TODO: Quitar estas assumptions cuando tengamos el Relative hacked *)
      and M_repl:           "\<And>P. replacement(##M,P)"
      and M_nat:            "nat \<in> M"
begin  
definition
  generic :: "i\<Rightarrow>o" where
  "generic(G) == filter(G) \<and> (\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"
  
lemma generic_filter_existence: 
  "p\<in>P \<Longrightarrow> \<exists>G. generic(G)"
  
  oops
  
end      
(* Prototyping Forcing relation and theorems as a locale*)
locale forcing_thms = forcing_poset + forcing_data +
  fixes forces :: "i \<Rightarrow> i"
  assumes definition_of_forces: "\<forall>env\<in>list(M).
                  sats(M,forces(\<phi>), [P,leq,uno,p] @ env) \<longleftrightarrow>
                  (\<forall>G.(generic(G)\<and> p\<in>G)\<longrightarrow>sats(gen_ext(M,P,G),\<phi>,map(valR(M,P,G),env)))"
      and definability:      "forces(\<phi>) \<in> formula"
      and truth_lemma:      "\<forall>env\<in>list(M).\<forall>G.(generic(G) \<and> p\<in>G)\<longrightarrow>
                  ((\<exists>p\<in>P.(sats(M,forces(\<phi>), [P,leq,uno,p] @ env))) \<longleftrightarrow>
                  (sats(gen_ext(M,P,G),\<phi>,map(valR(M,P,G),env))))"
begin
lemma
  "\<phi>\<in>formula \<Longrightarrow> \<psi>\<in>formula \<Longrightarrow> 
    \<forall>u\<in>M. \<forall>l\<in>M. \<forall>Q\<in>M. \<forall>s\<in>M. \<forall>r\<in>M. \<forall>d\<in>M.
      sats(M,[d,r,s,Q,l,u],
        Exists(Exists(And(pair_fm(0,1,2),
          forces(And(Member(0,1),\<phi>))))))" 
  oops
   
lemma
    "sats(M,forces(And(Member(0,1),\<phi>)),[P,leq,uno,p,\<theta>,\<pi>,\<sigma>])
      \<Longrightarrow> valR(M,P,G,{w\<in>domain(\<pi>)\<times>P. x=x}) =x"  (* Enunciado mal *)
  oops
    
      
theorem separation_in_genext:
    "\<forall>p\<in>formula. arity(p) = 3 \<longrightarrow> sats(gen_ext(M,P,G),separation_ax_fm(p),[])"
oops
end  
end