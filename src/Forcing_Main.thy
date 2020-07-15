section\<open>The main theorem\<close>
theory Forcing_Main
  imports
  Internal_ZFC_Axioms
  Choice_Axiom
  Ordinals_In_MG
  Succession_Poset

begin

subsection\<open>The generic extension is countable\<close>
(*
\<comment> \<open>Useful missing lemma\<close>
lemma surj_imp_well_ord:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "\<exists>s. well_ord(B,r)"
*)

definition
  minimum :: "i \<Rightarrow> i \<Rightarrow> i" where
  "minimum(r,B) \<equiv> THE b. first(b,B,r)"

lemma well_ord_surj_imp_lepoll:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "B \<lesssim> A"
proof -
  let ?f="\<lambda>b\<in>B. minimum(r, {a\<in>A. h`a=b})"
  have "minimum(r, {a \<in> A . h ` a = b}) \<in> {a\<in>A. h`a=b}" if "b\<in>B" for b
  proof -
    from \<open>h \<in> surj(A,B)\<close> that
    have "{a\<in>A. h`a=b} \<noteq> 0"
      unfolding surj_def by blast
    with \<open>well_ord(A,r)\<close>
    show "minimum(r,{a\<in>A. h`a=b}) \<in> {a\<in>A. h`a=b}"
      unfolding minimum_def using the_first_in by blast
  qed
  moreover from this
  have "?f : B \<rightarrow> A"
      using lam_type[of B _ "\<lambda>_.A"] by simp
  moreover
  have "?f ` w = ?f ` x \<Longrightarrow> w = x" if "w\<in>B" "x\<in>B" for w x
  proof -
    from calculation that
    have "w = h ` minimum(r,{a\<in>A. h`a=w})"
         "x = h ` minimum(r,{a\<in>A. h`a=x})"
      by simp_all
    moreover
    assume "?f ` w = ?f ` x"
    moreover from this and that
    have "minimum(r, {a \<in> A . h ` a = w}) = minimum(r, {a \<in> A . h ` a = x})"
      unfolding minimum_def by simp_all
    moreover from calculation(1,2,4)
    show "w=x" by simp
    qed
  ultimately
  show ?thesis
  unfolding lepoll_def inj_def by blast
qed

lemma (in forcing_data) surj_nat_MG :
  "\<exists>f. f \<in> surj(nat,M[G])"
proof -
  let ?f="\<lambda>n\<in>nat. val(G,enum`n)"
  have "x \<in> nat \<Longrightarrow> val(G, enum ` x)\<in> M[G]" for x
    using GenExtD[THEN iffD2, of _ G] bij_is_fun[OF M_countable] by force
  then
  have "?f: nat \<rightarrow> M[G]"
    using lam_type[of nat "\<lambda>n. val(G,enum`n)" "\<lambda>_.M[G]"] by simp
  moreover
  have "\<exists>n\<in>nat. ?f`n = x" if "x\<in>M[G]" for x
    using that GenExtD[of _ G] bij_is_surj[OF M_countable]
    unfolding surj_def by auto
  ultimately
  show ?thesis
    unfolding surj_def by blast
qed

lemma (in G_generic) MG_eqpoll_nat: "M[G] \<approx> nat"
proof -
  interpret MG: M_ZF_trans "M[G]"
    using Transset_MG generic pairing_in_MG
      Union_MG  extensionality_in_MG power_in_MG
      foundation_in_MG  strong_replacement_in_MG[simplified]
      separation_in_MG[simplified] infinity_in_MG
    by unfold_locales simp_all
  obtain f where "f \<in> surj(nat,M[G])"
    using surj_nat_MG by blast
  then
  have "M[G] \<lesssim> nat"
    using well_ord_surj_imp_lepoll well_ord_Memrel[of nat]
    by simp
  moreover
  have "nat \<lesssim> M[G]"
    using MG.nat_into_M subset_imp_lepoll by auto
  ultimately
  show ?thesis using eqpollI
    by simp
qed

subsection\<open>The main result\<close>

theorem extensions_of_ctms:
  assumes
    "M \<approx> nat" "Transset(M)" "M \<Turnstile> ZF"
  shows
    "\<exists>N.
      M \<subseteq> N \<and> N \<approx> nat \<and> Transset(N) \<and> N \<Turnstile> ZF \<and> M\<noteq>N \<and>
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)) \<and>
      (M, []\<Turnstile> AC \<longrightarrow> N \<Turnstile> ZFC)"
proof -
  from \<open>M \<approx> nat\<close>
  obtain enum where "enum \<in> bij(nat,M)"
    using eqpoll_sym unfolding eqpoll_def by blast
  with assms
  interpret M_ctm M enum
    using M_ZF_iff_M_satT
    by intro_locales (simp_all add:M_ctm_axioms_def)
  interpret ctm_separative "2^<\<omega>" seqle 0 M enum
  proof (unfold_locales)
    fix f
    let ?q="seq_upd(f,0)" and ?r="seq_upd(f,1)"
    assume "f \<in> 2^<\<omega>"
    then
    have "?q \<preceq>s f \<and> ?r \<preceq>s f \<and> ?q \<bottom>s ?r"
      using upd_leI seqspace_separative by auto
    moreover from calculation
    have "?q \<in> 2^<\<omega>"  "?r \<in> 2^<\<omega>"
      using seq_upd_type[of f 2] by auto
    ultimately
    show "\<exists>q\<in>2^<\<omega>.  \<exists>r\<in>2^<\<omega>. q \<preceq>s f \<and> r \<preceq>s f \<and> q \<bottom>s r"
      by (rule_tac bexI)+ \<comment> \<open>why the heck auto-tools don't solve this?\<close>
  next
    show "2^<\<omega> \<in> M" using nat_into_M seqspace_closed by simp
  next
    show "seqle \<in> M" using seqle_in_M .
  qed
  from cohen_extension_is_proper
  obtain G where "M_generic(G)"
    "M \<noteq> GenExt(G)" (is "M\<noteq>?N")
    by blast
  then
  interpret G_generic "2^<\<omega>" seqle 0 _ enum G by unfold_locales
  interpret MG: M_ZF "?N"
    using generic pairing_in_MG
      Union_MG  extensionality_in_MG power_in_MG
      foundation_in_MG  strong_replacement_in_MG[simplified]
      separation_in_MG[simplified] infinity_in_MG
    by unfold_locales simp_all
  have "?N \<Turnstile> ZF"
    using M_ZF_iff_M_satT[of ?N] MG.M_ZF_axioms by simp
  moreover
  have "M, []\<Turnstile> AC \<Longrightarrow> ?N \<Turnstile> ZFC"
  proof -
    assume "M, [] \<Turnstile> AC"
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