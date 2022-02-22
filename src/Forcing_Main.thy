section\<open>The main theorem\<close>

theory Forcing_Main
  imports
    Succession_Poset
    Internal_ZFC_Axioms
    Choice_Axiom
    Ordinals_In_MG

begin

subsection\<open>The generic extension is countable\<close>

lemma (in forcing_data1) surj_nat_MG :
  "\<exists>f. f \<in> surj(\<omega>,M[G])"
proof -
  let ?f="\<lambda>n\<in>\<omega>. val(P,G,enum`n)"
  have "x \<in> \<omega> \<Longrightarrow> val(P,G, enum ` x)\<in> M[G]" for x
    using GenExt_iff[THEN iffD2, of _ G] bij_is_fun[OF M_countable] by force
  then
  have "?f: \<omega> \<rightarrow> M[G]"
    using lam_type[of \<omega> "\<lambda>n. val(P,G,enum`n)" "\<lambda>_.M[G]"] by simp
  moreover
  have "\<exists>n\<in>\<omega>. ?f`n = x" if "x\<in>M[G]" for x
    using that GenExt_iff[of _ G] bij_is_surj[OF M_countable]
    unfolding surj_def by auto
  ultimately
  show ?thesis
    unfolding surj_def by blast
qed

lemma (in G_generic1) MG_eqpoll_nat: "M[G] \<approx> \<omega>"
proof -
  obtain f where "f \<in> surj(\<omega>,M[G])"
    using surj_nat_MG by blast
  then
  have "M[G] \<lesssim> \<omega>"
    using well_ord_surj_imp_lepoll well_ord_Memrel[of \<omega>]
    by simp
  moreover
  have "\<omega> \<lesssim> M[G]"
    using ext.nat_into_M subset_imp_lepoll by (auto del:lepollI)
  ultimately
  show ?thesis using eqpollI
    by simp
qed

subsection\<open>The main result\<close>

theorem extensions_of_ctms:
  assumes
    "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZF"
  shows
    "\<exists>N.
      M \<subseteq> N \<and> N \<approx> \<omega> \<and> Transset(N) \<and> N \<Turnstile> ZF \<and> M\<noteq>N \<and>
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)) \<and>
      ((M, []\<Turnstile> \<cdot>AC\<cdot>) \<longrightarrow> N \<Turnstile> ZFC)"
proof -
  from \<open>M \<Turnstile> ZF\<close>
  interpret M_ZF M
    using M_ZF_iff_M_satT
    by simp
  from \<open>Transset(M)\<close>
  interpret M_ZF_trans M
    using M_ZF_iff_M_satT
    by unfold_locales
  from \<open>M \<approx> \<omega>\<close>
  obtain enum where "enum \<in> bij(\<omega>,M)"
    using eqpoll_sym unfolding eqpoll_def by blast
  then
  interpret M_ctm M enum by unfold_locales
  interpret forcing_data "2\<^bsup><\<omega>\<^esup>" seqle 0 M enum
    using nat_into_M seqspace_closed seqle_in_M
    by unfold_locales simp
  obtain G where "M_generic(G)" "M \<noteq> M\<^bsup>2\<^bsup><\<omega>\<^esup>\<^esup>[G]" (is "M\<noteq>?N")
    using cohen_extension_is_proper
    by blast
  then
  interpret G_generic "2\<^bsup><\<omega>\<^esup>" seqle 0 _ enum G by unfold_locales
  interpret MG: M_ZF "?N"
    using generic pairing_in_MG
      Union_MG  extensionality_in_MG power_in_MG foundation_in_MG
      strong_replacement_in_MG[unfolded ground_replacement_assm_def, OF _ _ _ replacement_ax]
      separation_in_MG infinity_in_MG
    by unfold_locales (simp_all add:replacement_assm_def)
  have "?N \<Turnstile> ZF"
    using M_ZF_iff_M_satT[of ?N] MG.M_ZF_axioms by simp
  moreover
  have "M, []\<Turnstile> \<cdot>AC\<cdot> \<Longrightarrow> ?N \<Turnstile> ZFC"
  proof -
    assume "M, [] \<Turnstile> \<cdot>AC\<cdot>"
    then
    have "choice_ax(##M)"
      unfolding ZF_choice_fm_def using ZF_choice_auto by simp
    then
    have "choice_ax(##?N)" using choice_in_MG by simp
    with \<open>?N \<Turnstile> ZF\<close>
    show "?N \<Turnstile> ZFC"
      using ZF_choice_auto sats_ZFC_iff_sats_ZF_AC
      unfolding ZF_choice_fm_def by simp
  qed
  moreover
  note \<open>M \<noteq> ?N\<close>
  moreover
  have "Transset(?N)" using Transset_MG .
  moreover
  have "M \<subseteq> ?N" using M_subset_MG[OF one_in_G] generic by simp
  ultimately
  show ?thesis
    using Ord_MG_iff MG_eqpoll_nat
    by (rule_tac x="?N" in exI, simp)
qed

end