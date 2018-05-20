theory Separation_generic imports  Formula Names ZFCAxioms_formula forcing_posets begin

lemma lam_codomain: "\<forall>n\<in>N. (\<lambda>x\<in>N. b(x))`n \<in> B \<Longrightarrow>  (\<lambda>x\<in>N. b(x)) : N\<rightarrow>B"
  apply (rule fun_weaken_type)
   apply (subgoal_tac " (\<lambda>x\<in>N. b(x)) : N \<rightarrow> {b(x).x\<in>N}", assumption)
   apply (auto simp add:lam_funtype)
  done
    
locale forcing_data = forcing_poset +
  fixes M enum
  assumes trans_M:          "Transset(M)"
      and M_model_ZF:       "satT(M,ZFTh,[])"
      and M_countable:      "enum\<in>bij(nat,M)"
      and P_in_M:           "P \<in> M"
      (* TODO: Quitar estas assumptions cuando tengamos el Relative hacked *)
      and M_nonempty:       "0 \<in> M"

begin  (*************** CONTEXT: forcing_data *****************)
definition
  M_generic :: "i\<Rightarrow>o" where
  "M_generic(G) == filter(G) \<and> (\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"

declare iff_trans [trans]

lemma generic_filter_existence: 
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> M_generic(G)"
proof -
  assume
         Eq1: "p\<in>P"
  let
              ?D="\<lambda>n\<in>nat. (if (enum`n\<subseteq>P \<and> dense(enum`n))  then enum`n else P)"
  have 
         Eq2: "\<forall>n\<in>nat. ?D`n \<in> Pow(P)"
    by auto
  then have
         Eq3: "?D:nat\<rightarrow>Pow(P)"
    by (rule lam_codomain)
  have
         Eq4: "\<forall>n\<in>nat. dense(?D`n)"
  proof
    show
              "dense(?D`n)"    
    if   Eq5: "n\<in>nat"        for n
    proof -
      have
              "dense(?D`n) 
                \<longleftrightarrow>  dense(if enum ` n \<subseteq> P \<and> dense(enum ` n) then enum ` n else P)"
        using Eq5 by simp
      also have
              " ... \<longleftrightarrow>  (\<not>(enum ` n \<subseteq> P \<and> dense(enum ` n)) \<longrightarrow> dense(P)) "
        using split_if by simp
      finally show ?thesis
        using P_dense and Eq5 by auto
    qed
  qed
  from Eq3 and Eq4 interpret 
          cg: countable_generic P leq uno ?D 
    by (unfold_locales, auto)
  from cg.rasiowa_sikorski and Eq1 obtain G where 
         Eq6: "p\<in>G \<and> filter(G) \<and> (\<forall>n\<in>nat.(?D`n)\<inter>G\<noteq>0)"
    unfolding cg.D_generic_def by blast
  then have
         Eq7: "(\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"
  proof (intro ballI impI)
    show
              "D \<inter> G \<noteq> 0" 
    if   Eq8: "D\<in>M" and 
         Eq9: "D \<subseteq> P \<and> dense(D) " for D
    proof -
      from M_countable and  bij_is_surj have
              "\<forall>y\<in>M. \<exists>x\<in>nat. enum`x= y"
        unfolding surj_def  by (simp)
      with Eq8 obtain n where
        Eq10: "n\<in>nat \<and> enum`n = D" 
        by auto
      with Eq9 and if_P have
        Eq11: "?D`n = D"
        by (simp)
      with Eq6 and Eq10 show 
              "D\<inter>G\<noteq>0"
        by auto
    qed
    with Eq6 have
        Eq12: "\<exists>G. filter(G) \<and> (\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"
      by auto
  qed
  with Eq6 show ?thesis 
    unfolding M_generic_def by auto
qed     
end    (*************** CONTEXT: forcing_data *****************)      

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

begin  (*************** CONTEXT: forcing_thms *****************)
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
end    (*************** CONTEXT: forcing_thms *****************)
end