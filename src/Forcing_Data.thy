section\<open>Transitive set models of ZF\<close>
text\<open>This theory defines the locale \<^term>\<open>M_ZF_trans\<close> for
transitive models of ZF, and the associated \<^term>\<open>forcing_data\<close>
 that adds a forcing notion\<close>
theory Forcing_Data
  imports  
    Forcing_Notions 
    Interface
begin

locale M_ctm = M_ZF_trans +
  fixes enum
  assumes M_countable:      "enum\<in>bij(nat,M)"

locale M_ctm_AC = M_ctm + M_ZFC_trans

subsection\<open>A forcing locale and generic filters\<close>
locale forcing_data = forcing_notion + M_ctm +
  assumes P_in_M:           "P \<in> M"
    and leq_in_M:         "leq \<in> M"

begin

(* P \<subseteq> M *)
lemma P_sub_M : "P\<subseteq>M"
  using transitivity[OF _ P_in_M] by auto

definition
  M_generic :: "i\<Rightarrow>o" where
  "M_generic(G) \<equiv> filter(G) \<and> (\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"

lemma M_genericD [dest]: "M_generic(G) \<Longrightarrow> x\<in>G \<Longrightarrow> x\<in>P"
  unfolding M_generic_def by (blast dest:filterD)

lemma M_generic_leqD [dest]: "M_generic(G) \<Longrightarrow> p\<in>G \<Longrightarrow> q\<in>P \<Longrightarrow> p\<preceq>q \<Longrightarrow> q\<in>G"
  unfolding M_generic_def by (blast dest:filter_leqD)

lemma M_generic_compatD [dest]: "M_generic(G) \<Longrightarrow> p\<in>G \<Longrightarrow> r\<in>G \<Longrightarrow> \<exists>q\<in>G. q\<preceq>p \<and> q\<preceq>r"
  unfolding M_generic_def by (blast dest:low_bound_filter)

lemma M_generic_denseD [dest]: "M_generic(G) \<Longrightarrow> dense(D) \<Longrightarrow> D\<subseteq>P \<Longrightarrow> D\<in>M \<Longrightarrow> \<exists>q\<in>G. q\<in>D"
  unfolding M_generic_def by blast

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

lemma G_subset_M: "M_generic(G) \<Longrightarrow> G \<subseteq> M"
  using transitivity[OF _ P_in_M] by auto

declare iff_trans [trans]

lemma generic_filter_existence: 
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> M_generic(G)"
proof -
  assume "p\<in>P"
  let ?D="\<lambda>n\<in>nat. (if (enum`n\<subseteq>P \<and> dense(enum`n))  then enum`n else P)"
  have "\<forall>n\<in>nat. ?D`n \<in> Pow(P)"
    by auto
  then 
  have "?D:nat\<rightarrow>Pow(P)"
    using lam_type by auto
  have Eq4: "\<forall>n\<in>nat. dense(?D`n)"
  proof(intro ballI)
    fix n
    assume "n\<in>nat"
    then
    have "dense(?D`n) \<longleftrightarrow> dense(if enum`n \<subseteq> P \<and> dense(enum`n) then enum`n else P)"
      by simp
    also 
    have "... \<longleftrightarrow>  (\<not>(enum`n \<subseteq> P \<and> dense(enum`n)) \<longrightarrow> dense(P)) "
      using split_if by simp
    finally
    show "dense(?D`n)"
      using P_dense \<open>n\<in>nat\<close> by auto
  qed
  from \<open>?D\<in>_\<close> and Eq4 
  interpret cg: countable_generic P leq one ?D 
    by (unfold_locales, auto)
  from \<open>p\<in>P\<close> 
  obtain G where Eq6: "p\<in>G \<and> filter(G) \<and> (\<forall>n\<in>nat.(?D`n)\<inter>G\<noteq>0)"
    using cg.countable_rasiowa_sikorski[where M="\<lambda>_. M"]  P_sub_M
      M_countable[THEN bij_is_fun] M_countable[THEN bij_is_surj, THEN surj_range] 
    unfolding cg.D_generic_def by blast
  then 
  have Eq7: "(\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"
  proof (intro ballI impI)
    fix D
    assume "D\<in>M" and Eq9: "D \<subseteq> P \<and> dense(D) " 
    have "\<forall>y\<in>M. \<exists>x\<in>nat. enum`x= y"
      using M_countable and  bij_is_surj unfolding surj_def by (simp)
    with \<open>D\<in>M\<close> obtain n where Eq10: "n\<in>nat \<and> enum`n = D" 
      by auto
    with Eq9 and if_P
    have "?D`n = D" by (simp)
    with Eq6 and Eq10 
    show "D\<inter>G\<noteq>0" by auto
  qed
  with Eq6 
  show ?thesis unfolding M_generic_def by auto
qed

lemma one_in_M: "one \<in> M"
  by (insert one_in_P P_in_M, simp add: transitivity)

end \<comment> \<open>\<^locale>\<open>forcing_data\<close>\<close>

(* Compatibility lemmas *)
context forcing_data begin

definition
  compat_in_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "compat_in_fm(A,r,p,q) \<equiv> 
    Exists(And(Member(0,succ(A)),Exists(And(pair_fm(1,p#+2,0),
                                        And(Member(0,r#+2),
                                 Exists(And(pair_fm(2,q#+3,0),Member(0,r#+3))))))))" 

lemma compat_in_fm_type[TC] : 
  "\<lbrakk> A\<in>nat;r\<in>nat;p\<in>nat;q\<in>nat\<rbrakk> \<Longrightarrow> compat_in_fm(A,r,p,q)\<in>formula" 
  unfolding compat_in_fm_def by simp

lemma sats_compat_in_fm:
  assumes
    "A\<in>nat" "r\<in>nat"  "p\<in>nat" "q\<in>nat" "env\<in>list(M)"  
  shows
    "sats(M,compat_in_fm(A,r,p,q),env) \<longleftrightarrow> 
            is_compat_in(##M,nth(A, env),nth(r, env),nth(p, env),nth(q, env))"
  unfolding compat_in_fm_def is_compat_in_def using assms by simp

end \<comment> \<open>\<^locale>\<open>forcing_data\<close>\<close>

end
