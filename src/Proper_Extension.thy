theory Proper_Extension
  imports
    Forcing_Thms 
    (* it actually depends on more basic stuff, plus a misplaced lemma in the former *)

begin

lemma (in forcing_notion) filter_imp_compat: "filter(G) \<Longrightarrow> p\<in>G \<Longrightarrow> q\<in>G \<Longrightarrow> compat(p,q)"  \<comment> \<open>put somewhere else\<close>
  unfolding filter_def compat_in_def compat_def by blast

locale separative_notion = forcing_notion +
  assumes separative: "p\<in>P \<Longrightarrow> \<exists>q\<in>P. \<exists>r\<in>P. q \<preceq> p \<and> r \<preceq> p \<and> q \<bottom> r"
begin

lemma filter_complement_dense:
  assumes "filter(G)" shows "dense(P - G)"
proof
  fix p
  assume "p\<in>P"
  show "\<exists>d\<in>P - G. d \<preceq> p"
  proof (cases "p\<in>G")
    case True
    note \<open>p\<in>P\<close> assms
    moreover
    obtain q r where "q \<preceq> p" "r \<preceq> p" "q \<bottom> r" "q\<in>P" "r\<in>P" 
      using separative[OF \<open>p\<in>P\<close>]
      by force
    with \<open>filter(G)\<close>
    obtain s where "s \<preceq> p" "s \<notin> G" "s \<in> P"
      using filter_imp_compat[of G q r]
      by auto
    then
    show ?thesis by blast
  next
    case False
    with \<open>p\<in>P\<close> 
    show ?thesis using leq_reflI unfolding Diff_def by auto
  qed
qed

end (* separative_notion *)

locale ctm_separative = forcing_data + separative_notion
begin

lemma generic_not_in_M: assumes "M_generic(G)"  shows "G \<notin> M"
proof
  assume "G\<in>M"
  then
  have "P - G \<in> M" 
    using P_in_M Diff_closed by simp
  moreover
  have "\<not>(\<exists>q\<in>G. q \<in> P - G)" "(P - G) \<subseteq> P"
    unfolding Diff_def by auto
  moreover
  note assms
  ultimately
  show "False"
    using filter_complement_dense[of G] M_generic_denseD[of G "P-G"] 
      M_generic_def by simp \<comment> \<open>need to put generic ==> filter in claset\<close>
qed

lemma G_subset_M: "M_generic(G) \<Longrightarrow> G \<subseteq> M" \<comment> \<open>put somewhere else\<close>
  using transitivity[OF _ P_in_M] by auto

theorem proper_extension: assumes "M_generic(G)" shows "M \<noteq> M[G]"
  using assms G_in_Gen_Ext[of G] one_in_G[of G] generic_not_in_M G_subset_M
  by force

end (* ctm_separative *)

end