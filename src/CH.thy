theory CH
  imports
    Kappa_Closed_Notions
    Cardinal_Library_Relative2
begin

context M_ctm
begin

(* FIXME: Fake def *)
abbreviation
  Coll :: "i" where
  "Coll \<equiv> Fn(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)"

\<comment> \<open>Kunen IV.7.14, only for \<^term>\<open>\<aleph>\<^bsub>1\<^esub>\<close>\<close>
lemma kappa_closed_Aleph_rel1_Coll: "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>-closed\<^bsup>M\<^esup>(Coll,Fnle(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2))"
  sorry

end (* M_ctm *)

(* FIXME: Fake lemmas *)
lemma (in M_master) Fn_Aleph_rel1_closed[intro,simp]: "M(Fn(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2))" sorry
lemma (in M_master) Fnle_Aleph_rel1_closed[intro,simp]: "M(Fnle(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2))" sorry

locale collapse_generic = G_generic_AC "Fn(\<aleph>\<^bsub>1\<^esub>\<^bsup>##M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)" "Fnle(\<aleph>\<^bsub>1\<^esub>\<^bsup>##M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)" 0

sublocale collapse_generic \<subseteq> cohen_data "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2"
  using zero_lt_Aleph_rel1 by unfold_locales auto

context collapse_generic
begin

notation Leq (infixl "\<preceq>" 50)
notation Incompatible (infixl "\<bottom>" 50)
notation GenExt_at_P ("_[_]" [71,1])

abbreviation
  f_G :: "i" (\<open>f\<^bsub>G\<^esub>\<close>) where
  "f\<^bsub>G\<^esub> \<equiv> \<Union>G"

lemma f_G_in_MG[simp]:
  shows "f\<^bsub>G\<^esub> \<in> M[G]"
  using G_in_MG by simp

abbreviation
  dom_dense :: "i\<Rightarrow>i" where
  "dom_dense(x) \<equiv> { p\<in>Coll . x \<in> domain(p) }"

\<comment> \<open>FIXME: Should be more general, cf. @{thm add_generic.dense_dom_dense}\<close> 
lemma dense_dom_dense: "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> dense(dom_dense(x))"
proof
  fix p
  assume "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "p \<in> Coll"
  show "\<exists>d\<in>dom_dense(x). d \<preceq> p"
  proof (cases "x \<in> domain(p)")
    case True
    with \<open>x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close> \<open>p \<in> Coll\<close>
    show ?thesis using refl_leq by auto
  next
    case False
    note \<open>p \<in> Coll\<close>
    moreover from this and False and \<open>x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
    have "cons(\<langle>x,0\<rangle>, p) \<in> Coll"
      sorry
    moreover from \<open>p \<in> Coll\<close>
    have "x\<in>domain(cons(\<langle>x,0\<rangle>, p))" by simp
    ultimately
    show ?thesis
      by (fastforce del:FnD)
  qed
qed

(* FIXME: should be more general *)
lemma dom_dense_closed[intro,simp]: "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow>  dom_dense(x) \<in> M"
  using Fn_Aleph_rel1_closed Aleph_rel2_closed domain_separation[of x] nat_into_M
  by (rule_tac separation_closed[simplified], blast dest:transM) simp

lemma domain_f_G: assumes "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  shows "x \<in> domain(f\<^bsub>G\<^esub>)"
proof -
  from assms
  have "dense(dom_dense(x))" using dense_dom_dense by simp
  with assms
  obtain p where "p\<in>dom_dense(x)" "p\<in>G"
    using generic[THEN M_generic_denseD, of "dom_dense(x)"]
    by auto
  then
  show "x \<in> domain(f\<^bsub>G\<^esub>)" by blast
qed

lemma Fn_Aleph_rel1_subset_Pow: "Fn(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>,I,J) \<subseteq> Pow(I\<times>J)"
  sorry

lemma f_G_funtype:
  shows "f\<^bsub>G\<^esub> : \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightarrow> \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"
proof -
  have "x \<in> B \<Longrightarrow> B \<in> G \<Longrightarrow> x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<times> (\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2)" for B x
  proof -
    assume "x\<in>B" "B\<in>G"
    moreover from this
    have "x \<in> M[G]"
      by (auto dest!:generic_dests ext.transM)
        (intro generic_simps(2)[of Coll], simp add:Fn_Aleph_rel1_closed[simplified])
    moreover from calculation
    have "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<times> (\<omega> \<rightarrow> 2)"
      using Fn_Aleph_rel1_subset_Pow[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2"]
        function_space_rel_char by (auto dest!:generic_dests)
    moreover from this
    obtain z w where "x=\<langle>z,w\<rangle>" "z\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "w:\<omega> \<rightarrow> 2" by auto
    moreover from calculation
    have "w \<in> M[G]" by (auto dest:ext.transM)
    ultimately
    show ?thesis using ext.function_space_rel_char by auto
  qed
  moreover
  have "function(f\<^bsub>G\<^esub>)"
    using Un_filter_is_function generic
    unfolding M_generic_def by fast
  ultimately
  show ?thesis
  using generic domain_f_G unfolding Pi_def by auto
qed

abbreviation
  surj_dense :: "i\<Rightarrow>i" where
  "surj_dense(x) \<equiv> { p\<in>Coll . x \<in> range(p) }"

\<comment> \<open>FIXME write general versions of this for \<^term>\<open>Fn(\<omega>,I,J)\<close>
    in a context with a generic filter for it\<close>
lemma dense_surj_dense:
  assumes "x \<in> \<omega> \<rightarrow>\<^bsup>M\<^esup> 2"
  shows "dense(surj_dense(x))"
  sorry

lemma surj_dense_closed[intro,simp]:
  "x \<in> \<omega> \<rightarrow>\<^bsup>M\<^esup> 2 \<Longrightarrow> surj_dense(x) \<in> M"
  sorry

lemma reals_sub_image_f_G:
  assumes "x\<in>\<omega> \<rightarrow>\<^bsup>M\<^esup> 2" 
  shows "\<exists>\<alpha>\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>. f\<^bsub>G\<^esub> ` \<alpha> = x"
proof -
  from assms
  have "dense(surj_dense(x))" using dense_surj_dense by simp
  with \<open>x \<in> \<omega> \<rightarrow>\<^bsup>M\<^esup> 2\<close>
  obtain p where "p\<in>surj_dense(x)" "p\<in>G"
    using generic[THEN M_generic_denseD, of "surj_dense(x)"]
    by blast
  then
  show ?thesis
    using apply_rangeI[of "f\<^bsub>G\<^esub>" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<lambda>_. \<omega>\<rightarrow>2"]
      kappa_closed_Aleph_rel1_Coll
      f_G_funtype Aleph_1_closed_imp_no_new_reals[symmetric] apply auto
    sorry
qed

lemma f_G_surj_Aleph_rel1_reals: "f\<^bsub>G\<^esub> \<in> surj\<^bsup>M[G]\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2)"
  using Aleph_rel_sub_closed
proof (intro ext.mem_surj_abs[THEN iffD2])
  show "f\<^bsub>G\<^esub> \<in> surj(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2)"
    unfolding surj_def
  proof (intro ballI CollectI impI)
    show "f\<^bsub>G\<^esub> \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightarrow> \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"
      using f_G_funtype G_in_MG ext.nat_into_M f_G_in_MG by simp
    fix x
    assume "x \<in> \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"
    then
    show "\<exists>\<alpha>\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>. f\<^bsub>G\<^esub> ` \<alpha> = x"
      using reals_sub_image_f_G kappa_closed_Aleph_rel1_Coll
        f_G_funtype Aleph_1_closed_imp_no_new_reals by simp
  qed
qed simp_all

lemma continuum_rel_le_Aleph1_extension:
  includes G_generic_lemmas
  shows "2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup> \<le> \<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup>"
proof -
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<in> M[G]" "Ord(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)"
    using Card_rel_Aleph_rel[THEN Card_rel_is_Ord, of 1]
      Aleph_rel_closed
    by auto
  moreover from this
  have "\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2 \<lesssim>\<^bsup>M[G]\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using ext.surj_rel_implies_inj_rel[OF f_G_surj_Aleph_rel1_reals]
      f_G_in_MG unfolding lepoll_rel_def by auto
  with \<open>Ord(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)\<close>
  have "|\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2|\<^bsup>M[G]\<^esup> \<le> |\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>|\<^bsup>M[G]\<^esup>"
    using  M_subset_MG[OF one_in_G, OF generic] Aleph_rel_closed[of 1] 
    by (rule_tac ext.lepoll_rel_imp_cardinal_rel_le) simp_all
  ultimately
  have "2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup> \<le> |\<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup>|\<^bsup>M[G]\<^esup>"
    using ext.lepoll_rel_imp_cardinal_rel_le[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2",
        OF _ _ ext.function_space_rel_closed] ext.Aleph_rel_zero
      kappa_closed_Aleph_rel1_Coll Aleph_1_closed_imp_Aleph_1_preserved
    unfolding cexp_rel_def by simp
  then
  show "2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup> \<le> \<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup>" by simp
qed

theorem CH: "\<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup> = 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>"
  using continuum_rel_le_Aleph1_extension ext.Aleph_rel_succ[of 0]
  ext.Aleph_rel_zero ext.csucc_rel_le[of "2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>" \<omega>]
  ext.Card_rel_cexp_rel ext.cantor_cexp_rel[of \<omega>] ext.Card_rel_nat 
  ext.cexp_rel_closed[of 2 \<omega>] le_anti_sym
  by auto

end (* collapse_generic *)


theorem ctm_of_CH:
  assumes
    "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZFC"
  shows
    "\<exists>N.
      M \<subseteq> N \<and> N \<approx> \<omega> \<and> Transset(N) \<and> N \<Turnstile> ZFC \<union> {\<cdot>CH\<cdot>} \<and>
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N))"
proof -
  from \<open>M \<Turnstile> ZFC\<close>
  interpret M_ZFC M
    using M_ZFC_iff_M_satT
    by simp
  from \<open>Transset(M)\<close>
  interpret M_ZF_trans M
    using M_ZF_iff_M_satT
    by unfold_locales
  from \<open>M \<approx> \<omega>\<close>
  obtain enum where "enum \<in> bij(\<omega>,M)"
    using eqpoll_sym unfolding eqpoll_def by blast
  then
  interpret M_ctm_AC M enum by unfold_locales
  interpret forcing_data "Fn(\<aleph>\<^bsub>1\<^esub>\<^bsup>##M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)" "Fnle(\<aleph>\<^bsub>1\<^esub>\<^bsup>##M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)" 0 M enum
  proof -
    interpret cohen_data "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2" 
      using zero_lt_Aleph_rel1 by unfold_locales auto
    show "forcing_data(Fn(\<aleph>\<^bsub>1\<^esub>\<^bsup>##M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2), Fnle(\<aleph>\<^bsub>1\<^esub>\<^bsup>##M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2), 0, M, enum)"
      using Fn_Aleph_rel1_closed Fnle_Aleph_rel1_closed
      by (unfold_locales, simp_all)
  qed
  obtain G where "M_generic(G)"
    using generic_filter_existence[OF one_in_P]
    by auto
  moreover from this
  interpret collapse_generic M enum G by unfold_locales
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup> = 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>"
    using CH .
  then
  have "M[G], [] \<Turnstile> \<cdot>CH\<cdot>"
    using ext.is_ContHyp_iff
    by (simp add:ContHyp_rel_def)
  then
  have "M[G] \<Turnstile> ZFC \<union> {\<cdot>CH\<cdot>}"
    using M_ZFC_iff_M_satT[of "M[G]"] ext.M_ZFC_axioms by auto
  moreover
  have "Transset(M[G])" using Transset_MG .
  moreover
  have "M \<subseteq> M[G]" using M_subset_MG[OF one_in_G] generic by simp
  ultimately
  show ?thesis
    using Ord_MG_iff MG_eqpoll_nat
    by (rule_tac x="M[G]" in exI, simp)
qed

end