theory Konig
  imports
    Cofinality
    Cardinal_Library

begin

subsection\<open>König's Lemma\<close>

lemma konigs_theorem:
  notes [dest] = InfCard_is_Card Card_is_Ord
    and [trans] = lt_trans1 lt_trans2
  assumes
    "InfCard(\<kappa>)" "InfCard(\<nu>)" "cf(\<kappa>) \<le> \<nu>"
  shows
    "\<kappa> < \<kappa>\<^bsup>\<up>\<nu>\<^esup>"
  using assms(1,2) Card_cexp
proof (intro not_le_iff_lt[THEN iffD1] notI)
  assume "\<kappa>\<^bsup>\<up>\<nu>\<^esup> \<le> \<kappa>"
  moreover
  note \<open>InfCard(\<kappa>)\<close>
  moreover from calculation
  have "\<nu> \<rightarrow> \<kappa> \<lesssim> \<kappa>"
    using Card_cardinal_eq[OF InfCard_is_Card, symmetric]
      Card_le_imp_lepoll
    unfolding cexp_def by simp
  ultimately
  obtain G where "G \<in> surj(\<kappa>, \<nu> \<rightarrow> \<kappa>)"
    using inj_imp_surj[OF _ function_space_nonempty,
        OF _ nat_into_InfCard] by blast
  from assms
  obtain f where "f:\<nu> \<rightarrow> \<kappa>" "cf_fun(f,\<kappa>)"
    using cf_le_cf_fun[OF _ InfCard_is_Limit] by blast
  define H where "H(\<alpha>) \<equiv> \<mu> x. x\<in>\<kappa> \<and> (\<forall>m<f`\<alpha>. G`m`\<alpha> \<noteq> x)"
    (is "_ \<equiv> \<mu> x. ?P(\<alpha>,x)") for \<alpha>
  have H_satisfies: "?P(\<alpha>,H(\<alpha>))" if "\<alpha> \<in> \<nu>" for \<alpha>
  proof -
    obtain h where "?P(\<alpha>,h)"
    proof -
      from \<open>\<alpha>\<in>\<nu>\<close> \<open>f:\<nu> \<rightarrow> \<kappa>\<close> \<open>InfCard(\<kappa>)\<close>
      have "f`\<alpha> < \<kappa>"
        using apply_type[of _ _ "\<lambda>_ . \<kappa>"] by (auto intro:ltI)
      have "|{G`m`\<alpha> . m \<in> {x\<in>\<kappa> . x < f`\<alpha>}}| \<le> |{x\<in>\<kappa> . x < f`\<alpha>}|"
        using cardinal_RepFun_le by simp
      also from \<open>f`\<alpha> < \<kappa>\<close> \<open>InfCard(\<kappa>)\<close>
      have "|{x\<in>\<kappa> . x < f`\<alpha>}| < |\<kappa>|"
        using Card_lt_iff[OF lt_Ord, THEN iffD2, of "f`\<alpha>" \<kappa> \<kappa>]
          Ord_eq_Collect_lt[of "f`\<alpha>" \<kappa>] Card_cardinal_eq
        by force
      finally
      have "|{G`m`\<alpha> . m \<in> {x\<in>\<kappa> . x < f`\<alpha>}}| < |\<kappa>|" .
      moreover from \<open>f`\<alpha> < \<kappa>\<close> \<open>InfCard(\<kappa>)\<close>
      have "m<f`\<alpha> \<Longrightarrow> m\<in>\<kappa>" for m
        using Ord_trans[of m "f`\<alpha>" \<kappa>]
        by (auto dest:ltD)
      ultimately
      have "\<exists>h. ?P(\<alpha>,h)"
        using lt_cardinal_imp_not_subset by blast
      with that
      show ?thesis by blast
    qed
    with assms
    show "?P(\<alpha>,H(\<alpha>))"
      using LeastI[of "?P(\<alpha>)" h] lt_Ord Ord_in_Ord
      unfolding H_def by fastforce
  qed
  then
  have "(\<lambda>\<alpha>\<in>\<nu>. H(\<alpha>)): \<nu> \<rightarrow> \<kappa>"
    using lam_type by auto
  with \<open>G \<in> surj(\<kappa>, \<nu> \<rightarrow> \<kappa>)\<close>
  obtain n where "n\<in>\<kappa>" "G`n = (\<lambda>\<alpha>\<in>\<nu>. H(\<alpha>))"
    unfolding surj_def by blast
  moreover
  note \<open>InfCard(\<kappa>)\<close> \<open>f: \<nu> \<rightarrow> \<kappa>\<close> \<open>cf_fun(f,_)\<close>
  ultimately
  obtain \<alpha> where "n < f`\<alpha>" "\<alpha>\<in>\<nu>"
    using Limit_cofinal_fun_lt[OF InfCard_is_Limit] by blast
  moreover from calculation and \<open>G`n = (\<lambda>\<alpha>\<in>\<nu>. H(\<alpha>))\<close>
  have "G`n`\<alpha> = H(\<alpha>)"
    using ltD by simp
  moreover from calculation and H_satisfies
  have "\<forall>m<f`\<alpha>. G`m`\<alpha> \<noteq> H(\<alpha>)" by simp
  ultimately
  show "False" by blast
qed blast+

lemma cf_cexp:
  assumes
    "Card(\<kappa>)" "InfCard(\<nu>)" "2 \<le> \<kappa>"
  shows
    "\<nu> < cf(\<kappa>\<^bsup>\<up>\<nu>\<^esup>)"
proof (rule ccontr)
  assume "\<not> \<nu> < cf(\<kappa>\<^bsup>\<up>\<nu>\<^esup>)"
  with \<open>InfCard(\<nu>)\<close>
  have "cf(\<kappa>\<^bsup>\<up>\<nu>\<^esup>) \<le> \<nu>" 
    using not_lt_iff_le Ord_cf InfCard_is_Card Card_is_Ord by simp
  moreover
  note assms
  moreover from calculation
  have "InfCard(\<kappa>\<^bsup>\<up>\<nu>\<^esup>)" using InfCard_cexp by simp
  moreover from calculation
  have "\<kappa>\<^bsup>\<up>\<nu>\<^esup> < (\<kappa>\<^bsup>\<up>\<nu>\<^esup>)\<^bsup>\<up>\<nu>\<^esup>" 
    using konigs_theorem by simp
  ultimately
  show "False" using cexp_cexp_cmult InfCard_csquare_eq by auto
qed

corollary cf_continuum: "\<aleph>\<^bsub>0\<^esub> < cf(2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^esup>)"
  using cf_cexp InfCard_Aleph nat_into_Card by simp

end