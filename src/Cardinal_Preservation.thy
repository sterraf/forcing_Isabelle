theory Cardinal_Preservation
  imports
    Cardinal_AC_Relative
    Forcing_Main

begin

(* MOVE THIS to some appropriate place *)
declare (in M_trivial) compat_in_abs[absolut]

definition
  antichain_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "antichain_rel(M,P,leq,A) \<equiv> subset(M,A,P) \<and> (\<forall>p[M]. \<forall>q[M].
       p\<in>A \<longrightarrow> q\<in>A \<longrightarrow> \<not> is_compat_in(M,P,leq,p,q))"

context M_trivial
begin

abbreviation
  antichain_r :: "[i,i,i] \<Rightarrow> o" where
  "antichain_r(P,leq,A) \<equiv> antichain_rel(M,P,leq,A)"

lemma antichain_abs [absolut]:
  "\<lbrakk>M(X); M(A); M(r); M(P); M(leq)\<rbrakk> \<Longrightarrow> 
  antichain_r(P,leq,A) \<longleftrightarrow> antichain(P,leq,A)"
  unfolding antichain_rel_def antichain_def by (simp add:absolut)

end (* M_trivial *)

(******************************************************)
subsection\<open>Discipline for \<^term>\<open>ccc\<close>\<close>

definition (* completely relational *)
  ccc_rel   :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "ccc_rel(M,P,leq) \<equiv> \<forall>A[M]. antichain_rel(M,P,leq,A) \<longrightarrow> 
      (\<forall>\<kappa>[M]. is_cardinal(M,A,\<kappa>) \<longrightarrow> (\<exists>om[M]. omega(M,om) \<and> le_rel(M,\<kappa>,om)))"

context M_cardinals
begin

abbreviation
  ccc_r     :: "[i,i]\<Rightarrow>o"  where
  "ccc_r(P,leq) \<equiv> ccc_rel(M,P,leq)"

lemma def_ccc_rel:
  assumes
    "M(i)"
  shows
    "ccc_r(P,leq) \<longleftrightarrow> (\<forall>A[M]. antichain_r(P,leq,A) \<longrightarrow> |A|r \<le> nat)"
  using assms cardinal_rel_iff
  unfolding ccc_rel_def by (simp add:absolut)

end (* M_cardinals *)

(******************  end Discipline  ******************)

sublocale M_ZF_trans \<subseteq> M_cardinal_AC "##M"
  sorry

context G_generic begin

notation cardinal_rel (\<open>|_|\<^sup>M\<close>)
notation ccc_r (\<open>ccc\<^sup>M\<close>)
notation check (\<open>_\<^sup>v\<close> [101] 100)
notation function_space_rel (infix \<open>\<rightarrow>\<^sup>M\<close> 60)
notation inj_rel (\<open>inj\<^sup>M\<close>)

\<comment> \<open>NOTE: The following bundled additions to the simpset might be of
    use later on, perhaps add them globally to some appropriate
    locale.\<close>
lemmas generic_simps = generic[THEN one_in_G, THEN valcheck, OF one_in_P]
  generic[THEN one_in_G, THEN M_subset_MG, THEN subsetD]
  check_in_M GenExtI P_in_M
lemmas generic_dests = M_genericD[OF generic] M_generic_compatD[OF generic]

bundle G_generic_lemmas = generic_simps[simp] generic_dests[dest]

text\<open>The following interpretation makes the simplifications from the
locales \<open>M_trans\<close>, \<open>M_trivial\<close>, etc., available for \<^term>\<open>M[G]\<close> \<close>
interpretation mgzf: M_ZF_trans "M[G]"
  using Transset_MG generic pairing_in_MG Union_MG
    extensionality_in_MG power_in_MG foundation_in_MG
    strong_replacement_in_MG separation_in_MG infinity_in_MG
  by unfold_locales simp_all

context
  includes G_generic_lemmas
begin

\<comment> \<open>Simplifying simp rules (because of the occurrence of "##")\<close>
lemmas sharp_simps = Card_Union Card_rel_cardinal_rel Collect_abs
  Cons_abs Cons_in_M_iff Diff_closed Equal_abs Equal_in_M_iff Finite_abs
  Forall_abs Forall_in_M_iff Inl_abs Inl_in_M_iff Inr_abs Inr_in_M_iff
  Int_closed Inter_abs Inter_closed M_nat Member_abs Member_in_M_iff
  Memrel_closed Nand_abs Nand_in_M_iff Nil_abs Nil_in_M Ord_cardinal_rel
  Pow_rel_closed Un_closed Union_abs Union_closed and_abs and_closed
  apply_abs apply_closed bij_rel_closed bijection_abs bool_of_o_abs
  bool_of_o_closed cadd_rel_0 cadd_rel_closed cardinal_rel_0_iff_0
  cardinal_rel_closed cardinal_rel_idem cartprod_abs cartprod_closed
  cmult_rel_0 cmult_rel_1 cmult_rel_closed comp_closed composition_abs
  cons_abs cons_closed converse_abs converse_closed csquare_lam_closed
  csquare_rel_closed depth_closed domain_abs domain_closed eclose_abs
  eclose_closed empty_abs field_abs field_closed finite_funspace_closed
  finite_ordinal_abs formula_N_abs formula_N_closed formula_abs
  formula_case_abs formula_case_closed formula_closed
  formula_functor_abs fst_closed function_abs function_space_rel_closed
  hd_abs image_abs image_closed inj_rel_closed injection_abs inter_abs
  irreflexive_abs is_depth_apply_abs is_eclose_n_abs is_funspace_abs
  iterates_closed le_abs length_abs length_closed lepoll_rel_refl
  limit_ordinal_abs linear_rel_abs list_N_abs list_N_closed list_abs
  list_case'_closed list_case_abs list_closed list_functor_abs lt_abs
  mem_bij_abs mem_eclose_abs mem_inj_abs mem_list_abs membership_abs
  minimum_closed nat_case_abs nat_case_closed nonempty not_abs
  not_closed nth_abs number1_abs number2_abs number3_abs omega_abs
  or_abs or_closed order_isomorphism_abs ordermap_closed
  ordertype_closed ordinal_abs pair_abs pair_in_M_iff powerset_abs
  pred_closed pred_set_abs quasilist_abs quasinat_abs radd_closed
  rall_abs range_abs range_closed relation_abs restrict_closed
  restriction_abs rex_abs rmult_closed rtrancl_abs rtrancl_closed
  rvimage_closed separation_closed setdiff_abs singleton_abs
  singleton_in_M_iff snd_closed strong_replacement_closed subset_abs
  succ_in_M_iff successor_abs successor_ordinal_abs sum_abs sum_closed
  surj_rel_closed surjection_abs tl_abs trancl_abs trancl_closed
  transitive_rel_abs transitive_set_abs typed_function_abs union_abs
  upair_abs upair_in_M_iff vimage_abs vimage_closed well_ord_abs
  mem_formula_abs fst_abs snd_abs nth_closed

\<comment> \<open>NOTE: there is a theorem missing from those above\<close>
lemmas mg_sharp_simps = mgzf.Card_Union mgzf.Card_rel_cardinal_rel
  mgzf.Collect_abs mgzf.Cons_abs mgzf.Cons_in_M_iff mgzf.Diff_closed
  mgzf.Equal_abs mgzf.Equal_in_M_iff mgzf.Finite_abs mgzf.Forall_abs
  mgzf.Forall_in_M_iff mgzf.Inl_abs mgzf.Inl_in_M_iff mgzf.Inr_abs
  mgzf.Inr_in_M_iff mgzf.Int_closed mgzf.Inter_abs mgzf.Inter_closed
  mgzf.M_nat mgzf.Member_abs mgzf.Member_in_M_iff mgzf.Memrel_closed
  mgzf.Nand_abs mgzf.Nand_in_M_iff mgzf.Nil_abs mgzf.Nil_in_M
  mgzf.Ord_cardinal_rel mgzf.Pow_rel_closed mgzf.Un_closed
  mgzf.Union_abs mgzf.Union_closed mgzf.and_abs mgzf.and_closed
  mgzf.apply_abs mgzf.apply_closed mgzf.bij_rel_closed
  mgzf.bijection_abs mgzf.bool_of_o_abs mgzf.bool_of_o_closed
  mgzf.cadd_rel_0 mgzf.cadd_rel_closed mgzf.cardinal_rel_0_iff_0
  mgzf.cardinal_rel_closed mgzf.cardinal_rel_idem mgzf.cartprod_abs
  mgzf.cartprod_closed mgzf.cmult_rel_0 mgzf.cmult_rel_1
  mgzf.cmult_rel_closed mgzf.comp_closed mgzf.composition_abs
  mgzf.cons_abs mgzf.cons_closed mgzf.converse_abs mgzf.converse_closed
  mgzf.csquare_lam_closed mgzf.csquare_rel_closed mgzf.depth_closed
  mgzf.domain_abs mgzf.domain_closed mgzf.eclose_abs mgzf.eclose_closed
  mgzf.empty_abs mgzf.field_abs mgzf.field_closed
  mgzf.finite_funspace_closed mgzf.finite_ordinal_abs mgzf.formula_N_abs
  mgzf.formula_N_closed mgzf.formula_abs mgzf.formula_case_abs
  mgzf.formula_case_closed mgzf.formula_closed mgzf.formula_functor_abs
  mgzf.fst_closed mgzf.function_abs mgzf.function_space_rel_closed
  mgzf.hd_abs mgzf.image_abs mgzf.image_closed mgzf.inj_rel_closed
  mgzf.injection_abs mgzf.inter_abs mgzf.irreflexive_abs
  mgzf.is_depth_apply_abs mgzf.is_eclose_n_abs mgzf.is_funspace_abs
  mgzf.iterates_closed mgzf.le_abs mgzf.length_abs mgzf.length_closed
  mgzf.lepoll_rel_refl mgzf.limit_ordinal_abs mgzf.linear_rel_abs
  mgzf.list_N_abs mgzf.list_N_closed mgzf.list_abs
  mgzf.list_case'_closed mgzf.list_case_abs mgzf.list_closed
  mgzf.list_functor_abs mgzf.lt_abs mgzf.mem_bij_abs mgzf.mem_eclose_abs
  mgzf.mem_inj_abs mgzf.mem_list_abs mgzf.membership_abs
  mgzf.minimum_closed mgzf.nat_case_abs mgzf.nat_case_closed
  mgzf.nonempty mgzf.not_abs mgzf.not_closed mgzf.nth_abs
  mgzf.number1_abs mgzf.number2_abs mgzf.number3_abs mgzf.omega_abs
  mgzf.or_abs mgzf.or_closed mgzf.order_isomorphism_abs
  mgzf.ordermap_closed mgzf.ordertype_closed mgzf.ordinal_abs
  mgzf.pair_abs mgzf.pair_in_M_iff mgzf.powerset_abs mgzf.pred_closed
  mgzf.pred_set_abs mgzf.quasilist_abs mgzf.quasinat_abs
  mgzf.radd_closed mgzf.rall_abs mgzf.range_abs mgzf.range_closed
  mgzf.relation_abs mgzf.restrict_closed mgzf.restriction_abs
  mgzf.rex_abs mgzf.rmult_closed mgzf.rtrancl_abs mgzf.rtrancl_closed
  mgzf.rvimage_closed mgzf.separation_closed mgzf.setdiff_abs
  mgzf.singleton_abs mgzf.singleton_in_M_iff mgzf.snd_closed
  mgzf.strong_replacement_closed mgzf.subset_abs mgzf.succ_in_M_iff
  mgzf.successor_abs mgzf.successor_ordinal_abs mgzf.sum_abs
  mgzf.sum_closed mgzf.surj_rel_closed mgzf.surjection_abs mgzf.tl_abs
  mgzf.trancl_abs mgzf.trancl_closed mgzf.transitive_rel_abs
  mgzf.transitive_set_abs mgzf.typed_function_abs mgzf.union_abs
  mgzf.upair_abs mgzf.upair_in_M_iff mgzf.vimage_abs mgzf.vimage_closed
  mgzf.well_ord_abs mgzf.mem_formula_abs mgzf.nth_closed

declare sharp_simps[simp del, simplified, simp]
\<comment> \<open>The following was motivated by the fact that
    @{thm mgzf.apply_closed} did not simplify appropriately

    NOTE: @{thm fst_abs} and @{thm snd_abs} not in mgzf
    interpretation.\<close>
declare mg_sharp_simps[simp del, simplified, simp]

\<comment> \<open>Kunen IV.3.5\<close>
lemma ccc_fun_approximation_lemma:
  assumes "ccc\<^sup>M(P,leq)" "A\<in>M" "B\<in>M" "f\<in>M[G]" "f : A \<rightarrow> B"
  shows 
    "\<exists>F\<in>M. F : A \<rightarrow> Pow(B) \<and> (\<forall>a\<in>A. f`a \<in> F`a \<and> |F`a|\<^sup>M \<le> nat)"
proof -
  let ?\<phi>="typed_function_fm(1,2,0)"\<comment> \<open>formula for \<^term>\<open>f : A\<rightarrow> B\<close>\<close>
  from \<open>f\<in>M[G]\<close>
  obtain f_dot where "f = val(G,f_dot)" "f_dot\<in>M" using GenExtD by force
  with assms
  obtain p where "p \<tturnstile> ?\<phi> [f_dot, A\<^sup>v, B\<^sup>v]" "p\<in>G"
    using generic truth_lemma[of ?\<phi> G "[f_dot, A\<^sup>v, B\<^sup>v]"]
    by (auto simp add:nat_simp_union arity_typed_function_fm
        \<comment> \<open>NOTE: type-checking is not performed here by the Simplifier\<close>
        typed_function_type)
  let ?app_fm="fun_apply_fm(0,1,2)"\<comment> \<open>formula for \<open>f`x=z\<close>\<close>
  define F where "F\<equiv>\<lambda>a\<in>A. {b\<in>B. \<exists>q\<in>P. q \<preceq> p \<and> (q \<tturnstile> ?app_fm [f_dot, a\<^sup>v, b\<^sup>v])}"
  have "F \<in> M" sorry
  moreover
  have "f`a \<in> F`a" if "a \<in> A" for a
  proof -
    note \<open>f: A \<rightarrow> B\<close> \<open>a \<in> A\<close>
    moreover from this
    have "f ` a \<in> B" by simp
    moreover
    note \<open>f\<in>M[G]\<close> \<open>a\<in>A\<close> \<open>A\<in>M\<close>
    moreover from calculation
    have "M[G], [f, a, f`a] \<Turnstile> ?app_fm"
      by (auto dest:transM)
    moreover
    note \<open>B\<in>M\<close> \<open>f`a\<in>B\<close> \<open>f = val(G,f_dot)\<close>
    moreover from calculation
    have "a\<in>M[G]" "a\<in>M" "val(G, f_dot)`a\<in>M"
      by (auto dest:transM)
    moreover
    note \<open>f_dot\<in>M\<close>
    moreover from calculation
    obtain r where "r \<tturnstile> ?app_fm [f_dot, a\<^sup>v, (f`a)\<^sup>v]" "r\<in>G"
      using generic truth_lemma[of ?app_fm G "[f_dot, a\<^sup>v, (f`a)\<^sup>v]"]
      by (auto simp add: nat_simp_union arity_fun_apply_fm
          fun_apply_type)
    moreover from this and \<open>p\<in>G\<close>
    obtain q where "q \<preceq> p" "q \<preceq> r" "q \<in> G" by auto
    ultimately
    have "q \<tturnstile> ?app_fm [f_dot, a\<^sup>v, (f`a)\<^sup>v]" "q\<in>G"
      using strengthening_lemma[of r ?app_fm _ "[f_dot, a\<^sup>v, (f`a)\<^sup>v]"]
      by (auto simp add: nat_simp_union arity_fun_apply_fm
          fun_apply_type)
    with \<open>f`a \<in> B\<close> \<open>q \<preceq> p\<close>
    have "f`a \<in> {b\<in>B . \<exists>q\<in>P. q \<preceq> p \<and> q \<tturnstile> ?app_fm [f_dot, a\<^sup>v, b\<^sup>v]}"
      by blast
    with \<open>a\<in>A\<close>
    show ?thesis unfolding F_def by simp
  qed
  moreover
  have "|F`a|\<^sup>M \<le> nat" if "a \<in> A" for a
  proof -
    let ?Q="\<lambda>b. {q\<in>P. q \<preceq> p \<and> (q \<tturnstile> ?app_fm [f_dot, a\<^sup>v, b\<^sup>v])}"
    interpret M_Pi_assumptions_choice "##M" "F`a" ?Q sorry
    have "\<exists>y. y \<in> ?Q(b)" if "b \<in> F`a" for b sorry
    then
    obtain q where "q \<in> Pi_rel(F`a,?Q)" "q\<in>M" using AC_Pi_rel by auto
    moreover from \<open>F \<in> M\<close>
    have "F`a \<in> M" sorry
    moreover from calculation
    have "q : F`a \<rightarrow>\<^sup>M P" sorry
    moreover
    have "q`b \<bottom> q`c" if "b \<noteq> c" "b \<in> F`a" "c \<in> F`a" for b c sorry
    moreover from this
    have "q`b \<noteq> q`c" if "b \<noteq> c" "b \<in> F`a" "c \<in> F`a" for b c sorry
    ultimately
    have "q \<in> inj_rel(F`a,P)" using def_inj_rel by auto
    with \<open>F`a \<in> M\<close> \<open>q \<in> M\<close>
    show ?thesis sorry
  qed
  moreover
  have "F : A \<rightarrow> Pow(B)"
    unfolding F_def by (rule_tac lam_type) blast
  ultimately
  show ?thesis by auto
qed

end (* includes G_generic_lemmas *)

end (* forcing_data *)


end