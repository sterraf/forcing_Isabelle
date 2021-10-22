theory CH
  imports
    Kappa_Closed_Notions
    Cardinal_Library_Relative2
begin

(* FIXME: Fake defs *)
definition
  Fn_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" (\<open>Fn\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "Fn_rel(M,\<kappa>,I,J) \<equiv> 0"

abbreviation
  Fn_r_set ::  "[i,i,i,i] \<Rightarrow> i" (\<open>Fn\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "Fn_r_set(M) \<equiv> Fn_rel(##M)"

definition
  Fnle_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" (\<open>Fnle\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "Fnle_rel(M,\<kappa>,I,J) \<equiv> Fnlerel(Fn\<^bsup>M\<^esup>(\<kappa>,I,J))"

abbreviation
  Fnle_r_set ::  "[i,i,i,i] \<Rightarrow> i" (\<open>Fnle\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "Fnle_r_set(M) \<equiv> Fnle_rel(##M)"

context M_master
begin
(* FIXME: The results in this context are to be obtain through porting
  Cohen_Posets.thy *)

lemma Fn_rel_closed[intro,simp]:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "M(Fn\<^bsup>M\<^esup>(\<kappa>,I,J))" sorry

lemma Fn_rel_subset_Pow:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "Fn\<^bsup>M\<^esup>(\<kappa>,I,J) \<subseteq> Pow(I\<times>J)"
  sorry

lemma Fnle_rel_closed[intro,simp]:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "M(Fnle\<^bsup>M\<^esup>(\<kappa>,I,J))" sorry

lemma Fnle_rel_Aleph_rel1_closed[intro,simp]: "M(Fnle\<^bsup>M\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2))"
  by simp

lemma Fnle_relI[intro]:
  assumes "p \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)" "q \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)" "p \<supseteq> q"
  shows "<p,q> \<in> Fnle\<^bsup>M\<^esup>(\<kappa>,I,J)"
  using assms unfolding Fnlerel_def Fnle_rel_def FnleR_def Rrel_def
  by auto

lemma FnleD[dest]:
  assumes "<p,q> \<in> Fnle\<^bsup>M\<^esup>(\<kappa>,I,J)"
  shows "p \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)" "q \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)" "p \<supseteq> q"
  using assms unfolding Fnlerel_def Fnle_rel_def FnleR_def Rrel_def
  by auto

lemma zero_in_Fn_rel: 
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "0 \<in> Fn\<^bsup>M\<^esup>(\<kappa>, I, J)"
  sorry

lemma zero_top_Fn_rel: 
  assumes "p\<in>Fn\<^bsup>M\<^esup>(\<kappa>, I, J)" "M(\<kappa>)" "M(I)" "M(J)"
  shows "\<langle>p, 0\<rangle> \<in> Fnle\<^bsup>M\<^esup>(\<kappa>, I, J)"
  using assms zero_in_Fn_rel unfolding preorder_on_def refl_def trans_on_def
  by auto

lemma preorder_on_Fnle_rel:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "preorder_on(Fn\<^bsup>M\<^esup>(\<kappa>, I, J), Fnle\<^bsup>M\<^esup>(\<kappa>, I, J))"
  unfolding preorder_on_def refl_def trans_on_def
  by blast

end (* M_master *)

context M_ctm_AC
begin

abbreviation
  Coll :: "i" where
  "Coll \<equiv> Fn\<^bsup>M\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)"

abbreviation
  Colleq :: "i" where
  "Colleq \<equiv> Fnle\<^bsup>M\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)"

\<comment> \<open>Kunen IV.7.14, only for \<^term>\<open>\<aleph>\<^bsub>1\<^esub>\<close>\<close>
lemma Aleph_rel1_closed_Coll: "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>-closed\<^bsup>M\<^esup>(Coll,Colleq)"
  sorry

lemma Coll_in_M[intro,simp]: "Coll \<in> M"
  using Fn_rel_closed[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2"] Aleph_rel_closed[of 1]
    M_nat nat_into_M function_space_rel_closed by simp

end (* M_ctm_AC *)

locale collapse_generic = G_generic_AC "Fn\<^bsup>M\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>##M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)" "Fnle\<^bsup>M\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>##M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)" 0

sublocale collapse_generic \<subseteq> forcing_notion "Coll" "Colleq" 0
  using zero_lt_Aleph_rel1 by unfold_locales

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

lemma (in M_master) Fn_relD[dest]:
  assumes "p \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)" "M(\<kappa>)" "M(I)" "M(J)"
  shows "\<exists>d[M]. p : d \<rightarrow>\<^bsup>M\<^esup> J \<and> d \<subseteq> I \<and> d \<prec>\<^bsup>M\<^esup> \<kappa>"
  sorry

lemma (in M_master) cons_in_Fn_rel:
  assumes "x \<notin> domain(p)" "p \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)" "x \<in> I" "j \<in> J" "InfCard\<^bsup>M\<^esup>(\<kappa>)"
    "M(x)" "M(\<kappa>)" "M(I)" "M(J)"
  shows "cons(\<langle>x,j\<rangle>, p) \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)"
  sorry

lemma Coll_into_countable_rel: "p \<in> Coll \<Longrightarrow> countable\<^bsup>M\<^esup>(p)"
  sorry

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
    have "cons(\<langle>x,\<lambda>n\<in>\<omega>. 0\<rangle>, p) \<in> Coll" "x\<in>M"
      using Aleph_rel_closed[of 1] function_space_rel_char
        function_space_rel_closed lam_replacement_constant
        lam_replacement_iff_lam_closed InfCard_rel_Aleph_rel
      by (auto intro!: cons_in_Fn_rel dest:transM intro:function_space_nonempty)
    ultimately
    show ?thesis
      using Fn_relD by blast
  qed
qed

(* FIXME: should be more general *)
lemma dom_dense_closed[intro,simp]: "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow>  dom_dense(x) \<in> M"
  using Coll_in_M domain_separation[of x]
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

(* FIXME: port (see Cohen_Posets.thy) *)
lemma Un_filter_is_function: "filter(G) \<Longrightarrow> function(\<Union>G)"
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
        (intro generic_simps(2)[of Coll], simp)
    moreover from calculation
    have "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<times> (\<omega> \<rightarrow> 2)"
      using Fn_rel_subset_Pow[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2",
          OF _ _ function_space_rel_closed]
        function_space_rel_char Aleph_rel_closed[of 1]
      by (auto dest!:generic_dests)
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

\<comment> \<open>FIXME write general versions of this for \<^term>\<open>Fn\<^bsup>M\<^esup>(\<kappa>,I,J)\<close>
    in a context with a generic filter for it\<close>
lemma dense_surj_dense:
  assumes "x \<in> \<omega> \<rightarrow>\<^bsup>M\<^esup> 2"
  shows "dense(surj_dense(x))"
proof
  fix p
  assume "p \<in> Coll"
  then
  have "countable\<^bsup>M\<^esup>(p)" using Coll_into_countable_rel by simp
  show "\<exists>d\<in>surj_dense(x). d \<preceq> p"
  proof -
    from \<open>countable\<^bsup>M\<^esup>(p)\<close>
    obtain \<alpha> where "\<alpha> \<notin> domain(p)" "\<alpha>\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
      sorry
    moreover note assms
    moreover from calculation and \<open>p \<in> Coll\<close>
    have "cons(\<langle>\<alpha>,x\<rangle>, p) \<in> Coll" "x\<in>M" "cons(\<langle>\<alpha>,x\<rangle>, p) \<preceq> p"
      using Aleph_rel_closed[of 1] InfCard_rel_Aleph_rel
      by (auto intro!: cons_in_Fn_rel Fnle_relI dest:transM)
    ultimately
    show ?thesis by blast
  qed
qed

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
    using Aleph_rel1_closed_Coll f_G_funtype function_apply_equality[of _ x f_G]
      Aleph_rel1_closed_imp_no_new_reals[symmetric]
     by (auto, rule_tac bexI) (auto simp:Pi_def)
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
      using reals_sub_image_f_G Aleph_rel1_closed_Coll
        f_G_funtype Aleph_rel1_closed_imp_no_new_reals by simp
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
      Aleph_rel1_closed_Coll Aleph_rel1_closed_imp_Aleph_1_preserved
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
  interpret forcing_data "Coll" "Colleq" 0 M enum
  proof -
    show "forcing_data(Coll, Colleq, 0, M, enum)"
      using Coll_in_M Fnle_rel_Aleph_rel1_closed
        zero_in_Fn_rel[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2"] zero_top_Fn_rel[of _ "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2"]
        preorder_on_Fnle_rel[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2"] Aleph_rel_closed[of 1]
        nat_into_M function_space_rel_closed[of \<omega> 2] M_nat
      by unfold_locales simp_all
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