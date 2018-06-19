theory Forcing_data imports   Forcing_posets  begin

lemma lam_codomain: "\<forall>n\<in>N. (\<lambda>x\<in>N. b(x))`n \<in> B \<Longrightarrow>  (\<lambda>x\<in>N. b(x)) : N\<rightarrow>B"
  apply (rule fun_weaken_type)
   apply (subgoal_tac " (\<lambda>x\<in>N. b(x)) : N \<rightarrow> {b(x).x\<in>N}", assumption)
   apply (auto simp add:lam_funtype)
  done
    
locale forcing_data = forcing_notion +
  fixes M enum
  assumes M_countable:      "enum\<in>bij(nat,M)"
      and P_in_M:           "P \<in> M"
      and leq_in_M:         "leq \<in> M"

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
          cg: countable_generic P leq one ?D 
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

end