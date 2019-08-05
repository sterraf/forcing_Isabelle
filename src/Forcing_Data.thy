theory Forcing_Data 
  imports  
    Forcing_Notions 
    Relative 
    "~~/src/ZF/Constructible/Formula"

begin

lemma lam_codomain: "\<forall>n\<in>N. (\<lambda>x\<in>N. b(x))`n \<in> B \<Longrightarrow>  (\<lambda>x\<in>N. b(x)) : N\<rightarrow>B"
  apply (rule fun_weaken_type)
   apply (subgoal_tac " (\<lambda>x\<in>N. b(x)) : N \<rightarrow> {b(x).x\<in>N}", assumption)
   apply (auto simp add:lam_funtype)
  done

lemma Transset_M :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)  

definition 
  infinity_ax :: "(i \<Rightarrow> o) \<Rightarrow> o" where
  "infinity_ax(M) ==  
      (\<exists>I[M]. (\<exists>z[M]. empty(M,z) \<and> z\<in>I) \<and>  (\<forall>y[M]. y\<in>I \<longrightarrow> (\<exists>sy[M]. successor(M,y,sy) \<and> sy\<in>I)))"

locale M_ZF = 
  fixes M 
  assumes 
          upair_ax:         "upair_ax(##M)"
      and Union_ax:         "Union_ax(##M)"
      and power_ax:         "power_ax(##M)"
      and extensionality:   "extensionality(##M)"
      and foundation_ax:    "foundation_ax(##M)"
      and infinity_ax:      "infinity_ax(##M)"
      and separation_ax:    "\<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> arity(\<phi>) \<le> 1 #+ length(env) \<Longrightarrow>
                    separation(##M,\<lambda>x. sats(M,\<phi>,[x] @ env))" 
      and replacement_ax:   "\<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> arity(\<phi>) \<le> 2 #+ length(env) \<Longrightarrow> 
                    strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,[x,y] @ env))" 
      
locale forcing_data = forcing_notion + M_ZF +
  fixes enum
  assumes M_countable:      "enum\<in>bij(nat,M)"
      and P_in_M:           "P \<in> M"
      and leq_in_M:         "leq \<in> M"
      and trans_M:          "Transset(M)"
          
begin  (*************** CONTEXT: forcing_data *****************)
definition
  M_generic :: "i\<Rightarrow>o" where
  "M_generic(G) == filter(G) \<and> (\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"

lemma G_nonempty: "M_generic(G) \<Longrightarrow> G\<noteq>0"
proof -
  have "P\<subseteq>P" ..
  assume
    "M_generic(G)"
  with P_in_M P_dense \<open>P\<subseteq>P\<close> show
    "G \<noteq> 0"
    unfolding M_generic_def by auto
qed

lemma one_in_G : 
  assumes "M_generic(G)"
  shows  "one \<in> G" 
proof -
  from assms have "G\<subseteq>P" 
    unfolding M_generic_def and filter_def by simp
  from \<open>M_generic(G)\<close> have "increasing(G)" 
    unfolding M_generic_def and filter_def by simp
  with \<open>G\<subseteq>P\<close> and \<open>M_generic(G)\<close> 
  show ?thesis 
    using G_nonempty and one_in_P and one_max 
    unfolding increasing_def by blast
qed
  
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
