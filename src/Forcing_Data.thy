theory Forcing_Data 
  imports  
    Forcing_Notions 
    "../Constructible/Relative"
    "../Constructible/Formula"
    Interface

begin

lemma Transset_M :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)  


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

locale M_ctm = M_ZF +
  fixes enum
  assumes M_countable:      "enum\<in>bij(nat,M)"
      and trans_M:          "Transset(M)"

begin
interpretation intf: M_ZF_trans "M"
  apply (rule M_ZF_trans.intro)
          apply (simp_all add: trans_M upair_ax Union_ax power_ax extensionality
      foundation_ax infinity_ax separation_ax[simplified] 
      replacement_ax[simplified])
  done

lemmas transitivity = Transset_intf[OF trans_M]

lemma zero_in_M:  "0 \<in> M" 
  by (rule intf.zero_in_M)

lemma tuples_in_M: "A\<in>M \<Longrightarrow> B\<in>M \<Longrightarrow> <A,B>\<in>M" 
   by (simp del:setclass_iff add:setclass_iff[symmetric])

lemma nat_in_M : "nat \<in> M"
  by (rule intf.nat_in_M)

lemma n_in_M : "n\<in>nat \<Longrightarrow> n\<in>M"
  using nat_in_M trans_M Transset_intf[of M n nat] by simp

lemma mtriv: "M_trivial(##M)" 
  by (rule intf.mtriv)

lemma mtrans: "M_trans(##M)"
  by (rule intf.mtrans)

lemma mbasic: "M_basic(##M)"
  by (rule intf.mbasic)

lemma mtrancl: "M_trancl(##M)"
  by (rule intf.mtrancl)

lemma mdatatypes: "M_datatypes(##M)"
  by (rule intf.mdatatypes)

lemma meclose: "M_eclose(##M)"
  by (rule intf.meclose)

lemma meclose_pow: "M_eclose_pow(##M)"
  by (rule intf.meclose_pow)

end

(* M_ctm interface *)
sublocale M_ctm \<subseteq> M_trivial "##M"
  by  (rule mtriv)

sublocale M_ctm \<subseteq> M_trans "##M"
  by  (rule mtrans)

sublocale M_ctm \<subseteq> M_basic "##M"
  by  (rule mbasic)

sublocale M_ctm \<subseteq> M_trancl "##M"
  by  (rule mtrancl)

sublocale M_ctm \<subseteq> M_datatypes "##M"
  by  (rule mdatatypes)

sublocale M_ctm \<subseteq> M_eclose "##M"
  by  (rule meclose)

sublocale M_ctm \<subseteq> M_eclose_pow "##M"
  by  (rule meclose_pow)

(* end interface *)


locale forcing_data = forcing_notion + M_ctm +
  assumes P_in_M:           "P \<in> M"
      and leq_in_M:         "leq \<in> M"
          
begin

lemma transD : "Transset(M) \<Longrightarrow> y \<in> M \<Longrightarrow> y \<subseteq> M" 
  by (unfold Transset_def, blast) 
    
(* P \<subseteq> M *)
lemmas P_sub_M = transD[OF trans_M P_in_M]

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
    using lam_type by auto
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
  from Eq1 
  obtain G where Eq6: "p\<in>G \<and> filter(G) \<and> (\<forall>n\<in>nat.(?D`n)\<inter>G\<noteq>0)"
    using cg.countable_rasiowa_sikorski[where M="\<lambda>_. M"]  P_sub_M
      M_countable[THEN bij_is_fun] M_countable[THEN bij_is_surj, THEN surj_range] 
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



end (* forcing_data *)      
  
end
