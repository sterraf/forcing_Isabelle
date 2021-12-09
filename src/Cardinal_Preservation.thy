theory Cardinal_Preservation
  imports
    Cohen_Posets_Relative
    Forcing_Main
    ZF_Trans_Interpretations
begin

context forcing_notion
begin

definition
  antichain :: "i\<Rightarrow>o" where
  "antichain(A) \<equiv> A\<subseteq>P \<and> (\<forall>p\<in>A. \<forall>q\<in>A. p \<noteq> q \<longrightarrow> p \<bottom> q)"

definition
  ccc :: "o" where
  "ccc \<equiv> \<forall>A. antichain(A) \<longrightarrow> |A| \<le> \<omega>"

end (* forcing_notion *)

locale M_trivial_notion = M_trivial + forcing_notion
begin

abbreviation
  antichain_r' :: "i \<Rightarrow> o" where
  "antichain_r'(A) \<equiv> antichain_rel(M,P,leq,A)"

lemma antichain_abs' [absolut]:
  "\<lbrakk> M(A); M(P); M(leq) \<rbrakk> \<Longrightarrow> antichain_r'(A) \<longleftrightarrow> antichain(A)"
  unfolding antichain_rel_def antichain_def compat_def
  by (simp add:absolut)

end (* M_trivial_notion *)

\<comment> \<open>MOVE THIS to an appropriate place\<close>
text\<open>The following interpretation makes the simplifications from the
locales \<open>M_trans\<close>, \<open>M_trivial\<close>, etc., available for \<open>M[G]\<close>\<close>
sublocale forcing_data \<subseteq> M_trivial_notion "##M" ..

context forcing_data
begin

lemma antichain_abs'' [absolut]: "A\<in>M \<Longrightarrow> antichain_r'(A) \<longleftrightarrow> antichain(A)"
  using P_in_M leq_in_M
  unfolding antichain_rel_def antichain_def compat_def
  by (auto simp add:absolut transitivity)

end (* M_trivial_notion *)

lemma (in forcing_notion) Incompatible_imp_not_eq: "\<lbrakk> p \<bottom> q; p\<in>P; q\<in>P \<rbrakk>\<Longrightarrow> p \<noteq> q"
  using refl_leq by blast

lemma (in forcing_data) inconsistent_imp_incompatible:
  assumes "p \<tturnstile> \<phi> env" "q \<tturnstile> Neg(\<phi>) env" "p\<in>P" "q\<in>P"
    "arity(\<phi>) \<le> length(env)" "\<phi> \<in> formula" "env \<in> list(M)"
  shows "p \<bottom> q"
proof
  assume "compat(p,q)"
  then
  obtain d where "d \<preceq> p" "d \<preceq> q" "d \<in> P" by blast
  moreover
  note assms
  moreover from calculation
  have "d \<tturnstile> \<phi> env" "d \<tturnstile> Neg(\<phi>) env"
    using strengthening_lemma by simp_all
  ultimately
  show "False"
    using Forces_Neg[of d env \<phi>] refl_leq P_in_M
    by (auto dest:transM; drule_tac bspec; auto dest:transM)
qed

notation (in forcing_data) check (\<open>_\<^sup>v\<close> [101] 100)

context G_generic begin

\<comment> \<open>NOTE: The following bundled additions to the simpset might be of
    use later on, perhaps add them globally to some appropriate
    locale.\<close>
lemmas generic_simps = generic[THEN one_in_G, THEN valcheck, OF one_in_P]
  generic[THEN one_in_G, THEN M_subset_MG, THEN subsetD]
  check_in_M GenExtI P_in_M
lemmas generic_dests = M_genericD[OF generic] M_generic_compatD[OF generic]

bundle G_generic_lemmas = generic_simps[simp] generic_dests[dest]

end (* G_generic *)

sublocale G_generic \<subseteq> ext:M_ZF_trans "M[G]"
  using Transset_MG generic pairing_in_MG Union_MG
    extensionality_in_MG power_in_MG foundation_in_MG
    strong_replacement_in_MG separation_in_MG infinity_in_MG
  by unfold_locales simp_all

sublocale G_generic_AC \<subseteq> ext:M_ZFC_trans "M[G]"
  using choice_ax choice_in_MG
  by unfold_locales

lemma (in forcing_data) forces_neq_apply_imp_incompatible:
  assumes
    "p \<tturnstile> \<cdot>0`1 is 2\<cdot> [f,a,b\<^sup>v]"
    "q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f,a,b'\<^sup>v]"
    "b \<noteq> b'"
    \<comment> \<open>More general version: taking general names
       \<^term>\<open>b\<^sup>v\<close> and \<^term>\<open>b'\<^sup>v\<close>, satisfying
       \<^term>\<open>p \<tturnstile> \<cdot>\<not>\<cdot>0 = 1\<cdot>\<cdot> [b\<^sup>v, b'\<^sup>v]\<close> and
       \<^term>\<open>q \<tturnstile> \<cdot>\<not>\<cdot>0 = 1\<cdot>\<cdot> [b\<^sup>v, b'\<^sup>v]\<close>.\<close>
    and
    types:"f\<in>M" "a\<in>M" "b\<in>M" "b'\<in>M" "p\<in>P" "q\<in>P"
  shows
    "p \<bottom> q"
proof -
  {
    fix G
    assume "M_generic(G)"
    then
    interpret G_generic _ _ _ _ _ G by unfold_locales
    include G_generic_lemmas
      \<comment> \<open>FIXME: make a locale containg two \<open>M_ZF_trans\<close> instances, one
          for \<^term>\<open>M\<close> and one for \<^term>\<open>M[G]\<close>\<close>
    assume "q\<in>G"
    with assms \<open>M_generic(G)\<close>
    have "M[G], map(val(P,G),[f,a,b'\<^sup>v]) \<Turnstile> \<cdot>0`1 is 2\<cdot>"
      using truth_lemma[of "\<cdot>0`1 is 2\<cdot>" G "[f,a,b'\<^sup>v]"]
      by (auto simp add:ord_simp_union arity_fun_apply_fm
          fun_apply_type)
    with \<open>b \<noteq> b'\<close> types
    have "M[G], map(val(P,G),[f,a,b\<^sup>v]) \<Turnstile> \<cdot>\<not>\<cdot>0`1 is 2\<cdot>\<cdot>"
      using GenExtI by auto
  }
  with types
  have "q \<tturnstile> \<cdot>\<not>\<cdot>0`1 is 2\<cdot>\<cdot> [f,a,b\<^sup>v]"
    using definition_of_forcing[where \<phi>="\<cdot>\<not>\<cdot>0`1 is 2\<cdot>\<cdot>" ] check_in_M
    by (auto simp add:ord_simp_union arity_fun_apply_fm)
  with \<open>p \<tturnstile> \<cdot>0`1 is 2\<cdot> [f,a,b\<^sup>v]\<close> and types
  show "p \<bottom> q"
    using check_in_M inconsistent_imp_incompatible
    by (simp add:ord_simp_union arity_fun_apply_fm fun_apply_type)
qed

context M_ctm_AC
begin

\<comment> \<open>Simplifying simp rules (because of the occurrence of "\#\#")\<close>
lemmas sharp_simps = Card_rel_Union Card_rel_cardinal_rel Collect_abs
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
  mem_formula_abs fst_abs snd_abs nth_closed Aleph_rel_closed csucc_rel_closed
  Card_rel_Aleph_rel

declare sharp_simps[simp del, simplified setclass_iff, simp]

lemmas sharp_intros = nat_into_M Aleph_rel_closed Card_rel_Aleph_rel

declare sharp_intros[rule del, simplified setclass_iff, intro]

end (* M_ctm_AC *)

context G_generic_AC begin

context
  includes G_generic_lemmas
begin
\<comment> \<open>NOTE: there is a theorem missing from those above\<close>
lemmas mg_sharp_simps = ext.Card_rel_Union ext.Card_rel_cardinal_rel
  ext.Collect_abs ext.Cons_abs ext.Cons_in_M_iff ext.Diff_closed
  ext.Equal_abs ext.Equal_in_M_iff ext.Finite_abs ext.Forall_abs
  ext.Forall_in_M_iff ext.Inl_abs ext.Inl_in_M_iff ext.Inr_abs
  ext.Inr_in_M_iff ext.Int_closed ext.Inter_abs ext.Inter_closed
  ext.M_nat ext.Member_abs ext.Member_in_M_iff ext.Memrel_closed
  ext.Nand_abs ext.Nand_in_M_iff ext.Nil_abs ext.Nil_in_M
  ext.Ord_cardinal_rel ext.Pow_rel_closed ext.Un_closed
  ext.Union_abs ext.Union_closed ext.and_abs ext.and_closed
  ext.apply_abs ext.apply_closed ext.bij_rel_closed
  ext.bijection_abs ext.bool_of_o_abs ext.bool_of_o_closed
  ext.cadd_rel_0 ext.cadd_rel_closed ext.cardinal_rel_0_iff_0
  ext.cardinal_rel_closed ext.cardinal_rel_idem ext.cartprod_abs
  ext.cartprod_closed ext.cmult_rel_0 ext.cmult_rel_1
  ext.cmult_rel_closed ext.comp_closed ext.composition_abs
  ext.cons_abs ext.cons_closed ext.converse_abs ext.converse_closed
  ext.csquare_lam_closed ext.csquare_rel_closed ext.depth_closed
  ext.domain_abs ext.domain_closed ext.eclose_abs ext.eclose_closed
  ext.empty_abs ext.field_abs ext.field_closed
  ext.finite_funspace_closed ext.finite_ordinal_abs ext.formula_N_abs
  ext.formula_N_closed ext.formula_abs ext.formula_case_abs
  ext.formula_case_closed ext.formula_closed ext.formula_functor_abs
  ext.fst_closed ext.function_abs ext.function_space_rel_closed
  ext.hd_abs ext.image_abs ext.image_closed ext.inj_rel_closed
  ext.injection_abs ext.inter_abs ext.irreflexive_abs
  ext.is_depth_apply_abs ext.is_eclose_n_abs ext.is_funspace_abs
  ext.iterates_closed ext.le_abs ext.length_abs ext.length_closed
  ext.lepoll_rel_refl ext.limit_ordinal_abs ext.linear_rel_abs
  ext.list_N_abs ext.list_N_closed ext.list_abs
  ext.list_case'_closed ext.list_case_abs ext.list_closed
  ext.list_functor_abs ext.lt_abs ext.mem_bij_abs ext.mem_eclose_abs
  ext.mem_inj_abs ext.mem_list_abs ext.membership_abs
  ext.minimum_closed ext.nat_case_abs ext.nat_case_closed
  ext.nonempty ext.not_abs ext.not_closed ext.nth_abs
  ext.number1_abs ext.number2_abs ext.number3_abs ext.omega_abs
  ext.or_abs ext.or_closed ext.order_isomorphism_abs
  ext.ordermap_closed ext.ordertype_closed ext.ordinal_abs
  ext.pair_abs ext.pair_in_M_iff ext.powerset_abs ext.pred_closed
  ext.pred_set_abs ext.quasilist_abs ext.quasinat_abs
  ext.radd_closed ext.rall_abs ext.range_abs ext.range_closed
  ext.relation_abs ext.restrict_closed ext.restriction_abs
  ext.rex_abs ext.rmult_closed ext.rtrancl_abs ext.rtrancl_closed
  ext.rvimage_closed ext.separation_closed ext.setdiff_abs
  ext.singleton_abs ext.singleton_in_M_iff ext.snd_closed
  ext.strong_replacement_closed ext.subset_abs ext.succ_in_M_iff
  ext.successor_abs ext.successor_ordinal_abs ext.sum_abs
  ext.sum_closed ext.surj_rel_closed ext.surjection_abs ext.tl_abs
  ext.trancl_abs ext.trancl_closed ext.transitive_rel_abs
  ext.transitive_set_abs ext.typed_function_abs ext.union_abs
  ext.upair_abs ext.upair_in_M_iff ext.vimage_abs ext.vimage_closed
  ext.well_ord_abs ext.mem_formula_abs ext.nth_closed ext.Aleph_rel_closed
  ext.csucc_rel_closed ext.Card_rel_Aleph_rel

  \<comment> \<open>The following was motivated by the fact that
    @{thm ext.apply_closed} did not simplify appropriately

    NOTE: @{thm fst_abs} and @{thm snd_abs} not in mgzf
    interpretation.\<close>
declare mg_sharp_simps[simp del, simplified setclass_iff, simp]

lemmas mg_sharp_intros = ext.nat_into_M ext.Aleph_rel_closed
  ext.Card_rel_Aleph_rel

declare mg_sharp_intros[rule del, simplified setclass_iff, intro]

\<comment> \<open>Kunen IV.2.31\<close>
lemma forces_below_filter:
  assumes "M[G], map(val(P,G),env) \<Turnstile> \<phi>" "p \<in> G"
    "arity(\<phi>) \<le> length(env)" "\<phi> \<in> formula" "env \<in> list(M)"
  shows "\<exists>q\<in>G. q \<preceq> p \<and> q \<tturnstile> \<phi> env"
proof -
  note assms
  moreover from this
  obtain r where "r \<tturnstile> \<phi> env" "r\<in>G"
    using generic truth_lemma[of  \<phi> _ env]
    by blast
  moreover from this and \<open>p\<in>G\<close>
  obtain q where "q \<preceq> p" "q \<preceq> r" "q \<in> G" by auto
  ultimately
  show ?thesis
    using strengthening_lemma[of r \<phi> _ env] by blast
qed

abbreviation
  fm_leq :: "[i,i,i] \<Rightarrow> i" (\<open>\<cdot>_\<preceq>\<^bsup>_\<^esup>_\<cdot>\<close>) where
  "fm_leq(A,l,B) \<equiv> leq_fm(l,A,B)"

simple_rename "ren_U" src "[z1,x_P, x_leq, x_o, x_t, z2_c]"
  tgt "[z2_c,z1,z,x_P, x_leq, x_o, x_t]"

definition check_fm' where "check_fm'(ofm,arg,res) \<equiv> check_fm(arg,ofm,res)"

lemma separation_forces' :
  assumes "\<tau>\<in>M" "\<chi>\<in>formula" "arity(\<chi>) \<le> 6"
  shows "separation(##M, \<lambda>z. M, [fst(z), P, leq, one, \<tau>, snd(z)\<^sup>v] \<Turnstile> \<chi>)"
proof -
  note types = assms leq_in_M P_in_M one_in_M
  let ?\<phi>="\<chi>"

  let ?\<psi>="ren(?\<phi>)`6`7`ren_U_fn"
  let ?\<psi>''="Exists(And(fst_fm(1,0),Exists(And(hcomp_fm(check_fm'(6),snd_fm,2,0),?\<psi>))))"
  let ?\<rho>="\<lambda>z.[fst(z), P, leq, one, \<tau>, snd(z)\<^sup>v]"
  let ?env="[P, leq, one, \<tau>]"
  let ?\<eta>="\<lambda>z.[snd(z)\<^sup>v,fst(z),z]@?env"
  note types
  moreover from this
  have "?\<phi>\<in>formula" by simp
  moreover from calculation
  have "arity(?\<phi>) \<le> 6" "?\<psi>\<in>formula"
    using ord_simp_union arity_forces[of "\<cdot>0 = 1\<cdot> "] ren_tc ren_U_thm(2)[folded ren_U_fn_def]
      by simp_all
  moreover from calculation
  have "arity(?\<psi>) \<le> 7" "?\<psi>''\<in>formula"
    using arity_ren ren_U_thm(2)[folded ren_U_fn_def]
    unfolding check_fm'_def hcomp_fm_def by simp_all
  moreover from calculation
  have "arity(?\<psi>'') \<le> 5"
    using arity_fst_fm arity_snd_fm arity_check_fm ord_simp_union pred_le arity_type
    unfolding check_fm'_def hcomp_fm_def by (simp add:arity)
  moreover from assms calculation
  have 0:"(M, ?\<rho>(z) \<Turnstile> ?\<phi>) \<longleftrightarrow> (M,?\<eta>(z)\<Turnstile> ?\<psi>)" if "(##M)(z)" for z
    using sats_iff_sats_ren[of ?\<phi> 6 7 "?\<rho>(z)" _ "?\<eta>(z)"]
      ren_U_thm(1)[where A=M,folded ren_U_fn_def] ren_U_thm(2)[folded ren_U_fn_def] that
    by simp
  moreover from calculation
  have 1:"(M,?\<eta>(z)\<Turnstile> ?\<psi>) \<longleftrightarrow> M,[z]@?env\<Turnstile>?\<psi>''" if "(##M)(z)" for z
    using that sats_check_fm check_abs
    unfolding check_fm'_def hcomp_fm_def
    by simp
  moreover from calculation
  have 2:"separation(##M, \<lambda>z. (M,[z]@?env \<Turnstile> ?\<psi>''))"
    using separation_ax
      by simp_all
  ultimately
  show ?thesis
    by(rule_tac separation_cong[THEN iffD2,OF iff_trans[OF 0 1]],clarify,force)
qed

simple_rename "ren_V" src "[fz,x_P, x_leq, x_o,x_f, x_t, gz]"
  tgt "[gz,fz,z,x_P, x_leq, x_o,x_f, x_t]"

lemma pred_nat_closed : "a\<in>M \<Longrightarrow> pred(a)\<in>M"
    using nat_case_closed
    unfolding pred_def
    by auto

simple_rename "ren_V3" src "[fz,x_P, x_leq, x_o,x_f, gz, hz]"
  tgt "[hz,gz,fz,z,x_P, x_leq, x_o,x_f]"


lemma separation_sat_after_function3:
  assumes "f_dot\<in>M" and  "\<chi>\<in>formula" and "arity(\<chi>) \<le> 7"
  and
    f_fm:  "f_fm \<in> formula" and
    f_ar:  "arity(f_fm) \<le> 6" and
    fsats: "\<And> fx x. fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[fx,x]@[P, leq, one,f_dot] \<Turnstile> f_fm) \<longleftrightarrow> fx=f(x)" and
    fclosed: "\<And>x . x\<in>M \<Longrightarrow> f(x) \<in> M" and
    g_fm:  "g_fm \<in> formula" and
    g_ar:  "arity(g_fm) \<le> 7" and
    gsats: "\<And> gx fx x. gx\<in>M \<Longrightarrow>  fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[gx,fx,x]@[P, leq, one,f_dot] \<Turnstile> g_fm) \<longleftrightarrow> gx=g(x)" and
    gclosed: "\<And>x . x\<in>M \<Longrightarrow> g(x) \<in> M" and
    h_fm:  "h_fm \<in> formula" and
    h_ar:  "arity(h_fm) \<le> 8" and
    hsats: "\<And> hx gx fx x. hx\<in>M \<Longrightarrow> gx\<in>M \<Longrightarrow> fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[hx,gx,fx,x]@[P, leq, one,f_dot] \<Turnstile> h_fm) \<longleftrightarrow> hx=h(x)" and
    hclosed: "\<And>x . x\<in>M \<Longrightarrow> h(x) \<in> M"
shows  "separation(##M, \<lambda>r. M, [f(r), P, leq, one, f_dot, g(r), h(r)] \<Turnstile> \<chi>)"
proof -
  note types = assms(1-4) leq_in_M P_in_M one_in_M
  let ?\<phi>="\<chi>"
  let ?\<psi>="ren(?\<phi>)`7`8`ren_V3_fn"
  let ?\<psi>'="Exists(And(f_fm,Exists(And(g_fm,Exists(And(h_fm,?\<psi>))))))"
  let ?\<rho>="\<lambda>z.[f(z), P, leq, one,f_dot,g(z), h(z)]"
  let ?env="[P, leq, one,f_dot]"
  let ?\<eta>="\<lambda>z.[h(z),g(z),f(z),z]@?env"
  note types
  moreover from this
  have "?\<phi>\<in>formula" by simp
  moreover from calculation
  have "arity(?\<phi>) \<le> 9" "?\<psi>\<in>formula"
    using ord_simp_union ren_tc ren_V3_thm(2)[folded ren_V3_fn_def] le_trans[of "arity(\<chi>)" 7]
      by simp_all
  moreover from calculation
  have "arity(?\<psi>) \<le> 8" "?\<psi>'\<in>formula"
    using arity_ren ren_V3_thm(2)[folded ren_V3_fn_def] f_fm g_fm h_fm
    by (simp_all)
  moreover from this f_ar g_ar f_fm g_fm h_fm h_ar \<open>?\<psi>'\<in>_\<close>
  have "arity(?\<psi>') \<le> 5"
    using ord_simp_union arity_type nat_into_Ord
    by (simp add:arity,(rule_tac pred_le,simp,rule_tac Un_le,simp)+,simp_all add: \<open>?\<psi>\<in>_\<close>)
  moreover from calculation fclosed gclosed hclosed
  have 0:"(M, ?\<rho>(z) \<Turnstile> ?\<phi>) \<longleftrightarrow> (M,?\<eta>(z)\<Turnstile> ?\<psi>)" if "(##M)(z)" for z
    using sats_iff_sats_ren[of ?\<phi> 7 8 "?\<rho>(z)" M "?\<eta>(z)"]
      ren_V3_thm(1)[where A=M,folded ren_V3_fn_def,simplified] ren_V3_thm(2)[folded ren_V3_fn_def] that
    by simp
  moreover from calculation
  have 1:"(M,?\<eta>(z)\<Turnstile> ?\<psi>) \<longleftrightarrow> M,[z]@?env\<Turnstile>?\<psi>'" if "(##M)(z)" for z
    using that fsats[OF fclosed[of z],of z] gsats[of "g(z)" "f(z)" z]
      hsats[of "h(z)" "g(z)" "f(z)" z]
      fclosed gclosed hclosed f_fm g_fm h_fm
    apply(rule_tac iffI,simp,rule_tac rev_bexI[where x="f(z)"],simp)
     apply(rule_tac conjI,simp,rule_tac rev_bexI[where x="g(z)"],simp)
    apply(rule_tac conjI,simp,rule_tac rev_bexI[where x="h(z)"],simp,rule_tac conjI,simp,simp)
  proof -
    assume "M, [z] @ [P, leq, one, f_dot] \<Turnstile> (\<cdot>\<exists>\<cdot>f_fm \<and> (\<cdot>\<exists>\<cdot>g_fm \<and> (\<cdot>\<exists>\<cdot>h_fm \<and> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn\<cdot>\<cdot>)\<cdot>\<cdot>)\<cdot>\<cdot>)"
    with calculation that
    have "\<exists>x\<in>M. (M, [x, z, P, leq, one, f_dot] \<Turnstile> f_fm) \<and>
           (\<exists>xa\<in>M. (M, [xa, x, z, P, leq, one, f_dot] \<Turnstile> g_fm) \<and> (\<exists>xb\<in>M. (M, [xb, xa, x, z, P, leq, one, f_dot] \<Turnstile> h_fm) \<and> (M, [xb, xa, x, z, P, leq, one, f_dot] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn)))"
      by auto
    with calculation
    obtain x where "x\<in>M" "(M, [x, z, P, leq, one, f_dot] \<Turnstile> f_fm)"
        "(\<exists>xa\<in>M. (M, [xa, x, z, P, leq, one, f_dot] \<Turnstile> g_fm) \<and> (\<exists>xb\<in>M. (M, [xb, xa, x, z, P, leq, one, f_dot] \<Turnstile> h_fm) \<and> (M, [xb, xa, x, z, P, leq, one, f_dot] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn)))"
      by force
    moreover from this
    have "x=f(z)" using fsats[of x] that by simp
    moreover from calculation
    obtain xa where "xa\<in>M" "(M, [xa, x, z, P, leq, one, f_dot] \<Turnstile> g_fm)"
      "(\<exists>xb\<in>M. (M, [xb, xa, x, z, P, leq, one, f_dot] \<Turnstile> h_fm) \<and> (M, [xb, xa, x, z, P, leq, one, f_dot] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn))"
      by auto
    moreover from calculation
    have "xa=g(z)" using gsats[of xa x] that by simp
    moreover from calculation
    obtain xb where "xb\<in>M" "(M, [xb, xa, x, z, P, leq, one, f_dot] \<Turnstile> h_fm)"
      "(M, [xb, xa, x, z, P, leq, one, f_dot] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn)"
      by auto
    moreover from calculation
    have "xb=h(z)" using hsats[of xb xa x] that by simp
    ultimately
    show "M, [h(z), g(z), f(z), z] @ [P, leq, one, f_dot] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn"
      by auto
  qed
  moreover from calculation \<open>?\<psi>'\<in>_\<close>
  have 2:"separation(##M, \<lambda>z. (M,[z]@?env \<Turnstile> ?\<psi>'))"
    using separation_ax
    by simp
  ultimately
  show ?thesis
    by(rule_tac separation_cong[THEN iffD2,OF iff_trans[OF 0 1]],clarify,force)
qed

lemma separation_sat_after_function:
  assumes "f_dot\<in>M"and "\<tau>\<in>M" and  "\<chi>\<in>formula" and "arity(\<chi>) \<le> 7"
  and
    f_fm:  "f_fm \<in> formula" and
    f_ar:  "arity(f_fm) \<le> 7" and
    fsats: "\<And> fx x. fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[fx,x]@[P, leq, one,f_dot, \<tau>] \<Turnstile> f_fm) \<longleftrightarrow> fx=f(x)" and
    fclosed: "\<And>x . x\<in>M \<Longrightarrow> f(x) \<in> M" and
    g_fm:  "g_fm \<in> formula" and
    g_ar:  "arity(g_fm) \<le> 8" and
    gsats: "\<And> gx fx x. gx\<in>M \<Longrightarrow>  fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[gx,fx,x]@[P, leq, one,f_dot, \<tau>] \<Turnstile> g_fm) \<longleftrightarrow> gx=g(x)" and
    gclosed: "\<And>x . x\<in>M \<Longrightarrow> g(x) \<in> M"
  shows  "separation(##M, \<lambda>r. M, [f(r), P, leq, one, f_dot, \<tau>, g(r)] \<Turnstile> \<chi>)"
proof -
  note types = assms(1-4) leq_in_M P_in_M one_in_M
  let ?\<phi>="\<chi>"
  let ?\<psi>="ren(?\<phi>)`7`8`ren_V_fn"
  let ?\<psi>'="Exists(And(f_fm,Exists(And(g_fm,?\<psi>))))"
  let ?\<rho>="\<lambda>z.[f(z), P, leq, one,f_dot, \<tau>, g(z)]"
  let ?env="[P, leq, one,f_dot, \<tau>]"
  let ?\<eta>="\<lambda>z.[g(z),f(z),z]@?env"
  note types
  moreover from this
  have "?\<phi>\<in>formula" by simp
  moreover from calculation
  have "arity(?\<phi>) \<le> 8" "?\<psi>\<in>formula"
    using ord_simp_union ren_tc ren_V_thm(2)[folded ren_V_fn_def] le_trans[of "arity(\<chi>)" 7]
      by simp_all
  moreover from calculation
  have "arity(?\<psi>) \<le> 8" "?\<psi>'\<in>formula"
    using arity_ren ren_V_thm(2)[folded ren_V_fn_def] f_fm g_fm
     by (simp_all)
  moreover from calculation f_ar g_ar f_fm g_fm
  have "arity(?\<psi>') \<le> 6"
    using ord_simp_union pred_le arity_type
    by (simp add:arity)
  moreover from calculation fclosed gclosed
  have 0:"(M, ?\<rho>(z) \<Turnstile> ?\<phi>) \<longleftrightarrow> (M,?\<eta>(z)\<Turnstile> ?\<psi>)" if "(##M)(z)" for z
    using sats_iff_sats_ren[of ?\<phi> 7 8 "?\<rho>(z)" _ "?\<eta>(z)"]
      ren_V_thm(1)[where A=M,folded ren_V_fn_def] ren_V_thm(2)[folded ren_V_fn_def] that
    by simp
  moreover from calculation
  have 1:"(M,?\<eta>(z)\<Turnstile> ?\<psi>) \<longleftrightarrow> M,[z]@?env\<Turnstile>?\<psi>'" if "(##M)(z)" for z
    using that fsats[OF fclosed[of z],of z]  gsats[of "g(z)" "f(z)" z]
      fclosed gclosed f_fm g_fm
    apply(rule_tac iffI,simp,rule_tac rev_bexI[where x="f(z)"],simp)
    apply(auto)[1]
  proof -
    assume "M, [z] @ [P, leq, one, f_dot, \<tau>] \<Turnstile> (\<cdot>\<exists>\<cdot>f_fm \<and> (\<cdot>\<exists>\<cdot>g_fm \<and> ren(\<chi>) ` 7 ` 8 ` ren_V_fn\<cdot>\<cdot>)\<cdot>\<cdot>)"
    then have "\<exists>xa\<in>M. (M, [xa, z, P, leq, one, f_dot, \<tau>] \<Turnstile> f_fm) \<and>
       (\<exists>x\<in>M. (M, [x, xa, z, P, leq, one, f_dot, \<tau>] \<Turnstile> g_fm) \<and> (M, [x, xa, z, P, leq, one, f_dot, \<tau>] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V_fn))"
      using that calculation by auto
    then
    obtain xa where "xa\<in>M" "M, [xa, z, P, leq, one, f_dot, \<tau>] \<Turnstile> f_fm"
        "(\<exists>x\<in>M. (M, [x, xa, z, P, leq, one, f_dot, \<tau>] \<Turnstile> g_fm) \<and> (M, [x, xa, z, P, leq, one, f_dot, \<tau>] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V_fn))"
      by auto
    moreover from this
    have "xa=f(z)" using fsats[of xa] that by simp
    moreover from calculation
    obtain x where "x\<in>M" "M, [x, xa, z, P, leq, one, f_dot, \<tau>] \<Turnstile> g_fm" "M, [x, xa, z, P, leq, one, f_dot, \<tau>] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V_fn"
      by auto
    moreover from calculation
    have "x=g(z)" using gsats[of x xa] that by simp
    ultimately
    show "M, [g(z), f(z), z] @ [P, leq, one, f_dot, \<tau>] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V_fn"
      by auto
  qed
  moreover from calculation
  have 2:"separation(##M, \<lambda>z. (M,[z]@?env \<Turnstile> ?\<psi>'))"
    using separation_ax
      by simp_all
  ultimately
  show ?thesis
    by(rule_tac separation_cong[THEN iffD2,OF iff_trans[OF 0 1]],clarify,force)
qed

lemma ccc_fun_closed_lemma_aux:
  assumes "f_dot\<in>M" "p\<in>M" "a\<in>M" "b\<in>M"
  shows "{q \<in> P . q \<preceq> p \<and> (M, [q, P, leq, one, f_dot, a\<^sup>v, b\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))} \<in> M"
proof -
  have "\<cdot>0`1 is 2\<cdot> \<in> formula" "arity(\<cdot>0`1 is 2\<cdot> ) = 3"
    using arity_fun_apply_fm union_abs1
    by simp_all
  then
  have "arity(forces(\<cdot>0`1 is 2\<cdot> )) \<le> 7"
    using arity_forces[of "\<cdot>0`1 is 2\<cdot> "] by simp
  then
  show ?thesis
  using assms G_subset_M[THEN subsetD] generic one_in_M P_in_M
    separation_in lam_replacement_constant lam_replacement_identity
    lam_replacement_Pair[THEN[5] lam_replacement_hcomp2] leq_in_M check_in_M
    separation_conj separation_ax[simplified]
  by simp_all
qed

lemma aux_ccc :  
  assumes "x \<in> M" "a\<in>M" "f_dot\<in>M"
  shows "separation(##M, \<lambda>z. M, [z, P, leq, one, f_dot, a,x] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))"
proof -
  have "\<cdot>0`1 is 2\<cdot> \<in> formula" "arity(\<cdot>0`1 is 2\<cdot> ) = 3"
    using arity_fun_apply_fm union_abs1
    by simp_all
  then
  have "arity(forces(\<cdot>0`1 is 2\<cdot> )) \<le> 7"
    using arity_forces[of "\<cdot>0`1 is 2\<cdot> "] by simp
  then
  show ?thesis
    using leq_in_M one_in_M assms separation_ax[simplified]
    by simp
qed

lemma ccc_fun_closed_lemma_aux_sep :
  assumes "\<tau>\<in>M" "f_dot\<in>M"
  shows "separation(##M, \<lambda>z. M, [snd(z), P, leq, one, f_dot, \<tau>, fst(fst(z))\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))"
proof -
  let ?f_fm="snd_fm(1,0)"
  let ?g_fm="hcomp_fm(check_fm'(6),hcomp_fm(fst_fm,fst_fm),2,0)"
  note types = assms leq_in_M P_in_M one_in_M
  have "\<cdot>0`1 is 2\<cdot> \<in> formula" "arity(\<cdot>0`1 is 2\<cdot> ) = 3"
    using arity_fun_apply_fm union_abs1
    by simp_all
  then
  have "arity(forces(\<cdot>0`1 is 2\<cdot> )) \<le> 7"
    using arity_forces[of "\<cdot>0`1 is 2\<cdot> "] by simp
  moreover
  have 1: "?f_fm \<in> formula" "arity(?f_fm) \<le> 7"
    using ord_simp_union
    by (simp_all add:arity)
  moreover
  have 2:"\<And> fx x. fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[fx,x]@[P, leq, one,f_dot, \<tau>] \<Turnstile> ?f_fm) \<longleftrightarrow> fx=snd(x)"
    using types sats_fst_fm 
    by simp
  moreover
  have 3:"?g_fm \<in> formula" "arity(?g_fm) \<le> 8"
    using ord_simp_union
    unfolding hcomp_fm_def check_fm'_def
    by (simp_all add:arity)
  moreover
  have 4:"\<And> gx fx x. gx\<in>M \<Longrightarrow> fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[gx,fx,x]@[P, leq, one,f_dot, \<tau>] \<Turnstile> ?g_fm) \<longleftrightarrow> gx=fst(fst(x))\<^sup>v"
    using snd_abs types sats_snd_fm sats_check_fm check_abs check_in_M
    unfolding hcomp_fm_def check_fm'_def
    by simp
  ultimately
  show ?thesis
    using separation_sat_after_function assms
    by simp
qed

lemma ccc_fun_closed_lemma_aux_sep' :
  assumes "\<tau>\<in>M" "f_dot\<in>M"
  shows "separation(##M, \<lambda>z. M, [snd(z), P, leq, one, f_dot, \<tau>, fst(z)\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))"
proof -
  let ?f_fm="snd_fm(1,0)"
  let ?g_fm="hcomp_fm(check_fm'(6),fst_fm,2,0)"
  note types = assms leq_in_M P_in_M one_in_M
  have "\<cdot>0`1 is 2\<cdot> \<in> formula" "arity(\<cdot>0`1 is 2\<cdot> ) = 3"
    using arity_fun_apply_fm union_abs1
    by simp_all
  then
  have "arity(forces(\<cdot>0`1 is 2\<cdot> )) \<le> 7"
    using arity_forces[of "\<cdot>0`1 is 2\<cdot> "] by simp
  moreover
  have 1: "?f_fm \<in> formula" "arity(?f_fm) \<le> 7"
    using ord_simp_union
    by (simp_all add:arity)
  moreover
  have 2:"\<And> fx x. fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[fx,x]@[P, leq, one,f_dot, \<tau>] \<Turnstile> ?f_fm) \<longleftrightarrow> fx=snd(x)"
    using types sats_fst_fm 
    by simp
  moreover
  have 3:"?g_fm \<in> formula" "arity(?g_fm) \<le> 8"
    using ord_simp_union
    unfolding hcomp_fm_def check_fm'_def
    by (simp_all add:arity)
  moreover
  have 4:"\<And> gx fx x. gx\<in>M \<Longrightarrow> fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[gx,fx,x]@[P, leq, one,f_dot, \<tau>] \<Turnstile> ?g_fm) \<longleftrightarrow> gx=fst(x)\<^sup>v"
    using snd_abs types sats_snd_fm sats_check_fm check_abs check_in_M
    unfolding hcomp_fm_def check_fm'_def
    by simp
  ultimately
  show ?thesis
    using separation_sat_after_function assms
    by simp
qed

lemma ccc_fun_closed_lemma_aux2:
  assumes "B\<in>M" "f_dot\<in>M" "p\<in>M" "a\<in>M"
  shows "(##M)(\<lambda>b\<in>B. {q \<in> P . q \<preceq> p \<and> (M, [q, P, leq, one, f_dot, a\<^sup>v, b\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))})"
  using lam_replacement_imp_lam_closed lam_replacement_Collect assms separation_conj
    separation_in lam_replacement_constant leq_in_M
    lam_replacement_Pair[THEN [5] lam_replacement_hcomp2] lam_replacement_identity 
    aux_ccc separation_ball  separation_iff' lam_replacement_snd lam_replacement_fst lam_replacement_hcomp
    ccc_fun_closed_lemma_aux transitivity[of _ B] ccc_fun_closed_lemma_aux_sep
  by simp

lemma ccc_fun_closed_lemma:
  assumes "A\<in>M" "B\<in>M" "f_dot\<in>M" "p\<in>M"
  shows "(\<lambda>a\<in>A. {b\<in>B. \<exists>q\<in>P. q \<preceq> p \<and> (q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v])}) \<in> M"
proof -
  have "separation(##M, \<lambda>z. M, [snd(z), P, leq, one, f_dot, fst(fst(fst(z)))\<^sup>v, snd(fst(z))\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))"
  proof -
    note types = assms leq_in_M P_in_M one_in_M
    let ?f_fm="snd_fm(1,0)"
    let ?g="\<lambda>z . fst(fst(fst(z)))\<^sup>v"
    let ?g_fm="hcomp_fm(check_fm'(6),hcomp_fm(fst_fm,hcomp_fm(fst_fm,fst_fm)),2,0)"
    let ?h_fm="hcomp_fm(check_fm'(7),hcomp_fm(snd_fm,fst_fm),3,0)"
    have "\<cdot>0`1 is 2\<cdot> \<in> formula" "arity(\<cdot>0`1 is 2\<cdot> ) = 3"
      using arity_fun_apply_fm union_abs1
      by simp_all
    then
    have "arity(forces(\<cdot>0`1 is 2\<cdot> )) \<le> 7"
      using arity_forces[of "\<cdot>0`1 is 2\<cdot> "] by simp
    moreover
    have 0:"?f_fm \<in> formula" "arity(?f_fm) \<le> 6"
      using ord_simp_union
      unfolding hcomp_fm_def
      by (simp_all add:arity)
    moreover from types
    have 1:"\<And> fx x. fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[fx,x]@[P, leq, one,f_dot] \<Turnstile> ?f_fm) \<longleftrightarrow> fx=snd(x)"
      unfolding hcomp_fm_def
      by simp
    have 2:"?g_fm \<in> formula" "arity(?g_fm) \<le> 7"
      using ord_simp_union
      unfolding hcomp_fm_def check_fm'_def
      by (simp_all add:arity)
    moreover from types
    have 3:"\<And> gx fx x. gx\<in>M \<Longrightarrow> fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[gx,fx,x]@[P, leq, one,f_dot] \<Turnstile> ?g_fm) \<longleftrightarrow> gx=?g(x)"
      "\<And>x . x\<in>M \<Longrightarrow> ?g(x)\<in>M"
      using types sats_check_fm check_abs check_in_M
      unfolding hcomp_fm_def check_fm'_def
      by auto
    moreover
    have 4:"?h_fm \<in> formula" "arity(?h_fm) \<le> 8"
      using ord_simp_union
      unfolding hcomp_fm_def check_fm'_def
      by (simp_all add:arity)
    moreover
    have 5:"\<And> hx gx fx x. hx\<in>M \<Longrightarrow> gx\<in>M \<Longrightarrow> fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[hx,gx,fx,x]@[P, leq, one,f_dot] \<Turnstile> ?h_fm) \<longleftrightarrow> hx=snd(fst(x))\<^sup>v"
      "\<And>x . x\<in>M \<Longrightarrow> snd(x)\<^sup>v\<in>M"
      using snd_abs types sats_snd_fm sats_check_fm check_abs check_in_M
      unfolding hcomp_fm_def check_fm'_def
      by simp_all
    ultimately
    show ?thesis
      using separation_sat_after_function3[OF _ _ _ 0 1 _ 2 3 4 5] assms
      by simp
  qed
  then show ?thesis
  using lam_replacement_imp_lam_closed lam_replacement_Collect
    lam_replacement_constant lam_replacement_identity lam_replacement_snd lam_replacement_fst
    lam_replacement_hcomp lam_replacement_Pair[THEN [5] lam_replacement_hcomp2]
    separation_conj separation_in  separation_ball separation_bex separation_iff'
    ccc_fun_closed_lemma_aux_sep' transitivity[of _ A] leq_in_M assms
  by simp
qed

\<comment> \<open>Kunen IV.3.5\<close>
lemma ccc_fun_approximation_lemma:
  notes le_trans[trans]
  assumes "ccc\<^bsup>M\<^esup>(P,leq)" "A\<in>M" "B\<in>M" "f\<in>M[G]" "f : A \<rightarrow> B"
  shows
    "\<exists>F\<in>M. F : A \<rightarrow> Pow\<^bsup>M\<^esup>(B) \<and> (\<forall>a\<in>A. f`a \<in> F`a \<and> |F`a|\<^bsup>M\<^esup> \<le> \<omega>)"
proof -
  from \<open>f\<in>M[G]\<close>
  obtain f_dot where "f = val(P,G,f_dot)" "f_dot\<in>M" using GenExtD by force
  with assms
  obtain p where "p \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, A\<^sup>v, B\<^sup>v]" "p\<in>G" "p\<in>M"
    using transitivity[OF M_genericD P_in_M]
      generic truth_lemma[of "\<cdot>0:1\<rightarrow>2\<cdot>" G "[f_dot, A\<^sup>v, B\<^sup>v]"]
    by (auto simp add:ord_simp_union arity_typed_function_fm
        \<comment> \<open>NOTE: type-checking is not performed here by the Simplifier\<close>
        typed_function_type)
  define F where "F\<equiv>\<lambda>a\<in>A. {b\<in>B. \<exists>q\<in>P. q \<preceq> p \<and> (q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v])}"
  from assms \<open>f_dot\<in>_\<close> \<open>p\<in>M\<close>
  have "F \<in> M"
    unfolding F_def using ccc_fun_closed_lemma by simp
  moreover from calculation
  have "f`a \<in> F`a" if "a \<in> A" for a
  proof -
    note \<open>f: A \<rightarrow> B\<close> \<open>a \<in> A\<close>
    moreover from this
    have "f ` a \<in> B" by simp
    moreover
    note \<open>f\<in>M[G]\<close> \<open>A\<in>M\<close>
    moreover from calculation
    have "M[G], [f, a, f`a] \<Turnstile> \<cdot>0`1 is 2\<cdot>"
      by (auto dest:transM)
    moreover
    note \<open>B\<in>M\<close> \<open>f = val(P,G,f_dot)\<close>
    moreover from calculation
    have "a\<in>M" "val(P,G, f_dot)`a\<in>M"
      by (auto dest:transM)
    moreover
    note \<open>f_dot\<in>M\<close> \<open>p\<in>G\<close>
    ultimately
    obtain q where "q \<preceq> p" "q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, (f`a)\<^sup>v]" "q\<in>G"
      using forces_below_filter[of "\<cdot>0`1 is 2\<cdot>" "[f_dot, a\<^sup>v, (f`a)\<^sup>v]" p]
      by (auto simp add: ord_simp_union arity_fun_apply_fm
          fun_apply_type)
    with \<open>f`a \<in> B\<close>
    have "f`a \<in> {b\<in>B . \<exists>q\<in>P. q \<preceq> p \<and> q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v]}"
      by blast
    with \<open>a\<in>A\<close>
    show ?thesis unfolding F_def by simp
  qed
  moreover
  have "|F`a|\<^bsup>M\<^esup> \<le> \<omega> \<and> F`a\<in>M" if "a \<in> A" for a
  proof -
    let ?Q="\<lambda>b. {q\<in>P. q \<preceq> p \<and> (q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v])}"
    from \<open>F \<in> M\<close> \<open>a\<in>A\<close> \<open>A\<in>M\<close>
    have "F`a \<in> M" "a\<in>M"
      using transitivity[OF _ \<open>A\<in>M\<close>] by simp_all
    moreover
    have 2:"\<And>x. x\<in>F`a \<Longrightarrow> x\<in>M"
      using transitivity[OF _ \<open>F`a\<in>M\<close>] by simp
    moreover
    have 3:"\<And>x. x\<in>F`a \<Longrightarrow> (##M)(?Q(x))"
      using ccc_fun_closed_lemma_aux[OF \<open>f_dot\<in>M\<close> \<open>p\<in>M\<close> \<open>a\<in>M\<close> 2] transitivity[of _ "F`a"]
      by simp
    moreover
    have 4:"lam_replacement(##M,\<lambda>b. {q \<in> P . q \<preceq> p \<and> (M, [q, P, leq, one, f_dot, a\<^sup>v, b\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))})"
      using ccc_fun_closed_lemma_aux2[OF _ \<open>f_dot\<in>M\<close> \<open>p\<in>M\<close> \<open>a\<in>M\<close>]
        lam_replacement_iff_lam_closed[THEN iffD2]
        ccc_fun_closed_lemma_aux[OF  \<open>f_dot\<in>M\<close> \<open>p\<in>M\<close> \<open>a\<in>M\<close>]
      by simp
    ultimately
    interpret M_Pi_assumptions_choice "##M" "F`a" ?Q
      using Pi_replacement1[OF _ 3] lam_replacement_Sigfun[OF 4]
        lam_replacement_imp_strong_replacement
          ccc_fun_closed_lemma_aux[OF \<open>f_dot\<in>M\<close> \<open>p\<in>M\<close> \<open>a\<in>M\<close>]
          lam_replacement_product
          lam_replacement_hcomp2[OF lam_replacement_constant 4 _ _ lam_replacement_minimum,unfolded lam_replacement_def]
        by unfold_locales simp_all
    from \<open>F`a \<in> M\<close>
    interpret M_Pi_assumptions2 "##M" "F`a" ?Q "\<lambda>_ . P"
      using P_in_M lam_replacement_imp_strong_replacement[OF
          lam_replacement_Sigfun[OF lam_replacement_constant]]
        Pi_replacement1 transM[of _ "F`a"]
      by unfold_locales simp_all
    from \<open>p \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, A\<^sup>v, B\<^sup>v]\<close> \<open>a\<in>A\<close>
    have "\<exists>y. y \<in> ?Q(b)" if "b \<in> F`a" for b
      using that unfolding F_def by auto
    then
    obtain q where "q \<in> Pi\<^bsup>M\<^esup>(F`a,?Q)" "q\<in>M" using AC_Pi_rel by auto
    moreover
    note \<open>F`a \<in> M\<close>
    moreover from calculation
    have "q : F`a \<rightarrow>\<^bsup>M\<^esup> P"
      using Pi_rel_weaken_type def_function_space_rel by auto
    moreover from calculation
    have "q : F`a \<rightarrow> range(q)" "q : F`a \<rightarrow> P" "q : F`a \<rightarrow>\<^bsup>M\<^esup> range(q)"
      using mem_function_space_rel_abs range_of_fun by simp_all
    moreover
    have "q`b \<bottom> q`c" if "b \<in> F`a" "c \<in> F`a" "b \<noteq> c"
      \<comment> \<open>For the next step, if the premise \<^term>\<open>b \<noteq> c\<close> is first,
        the proof breaks down badly\<close>
      for b c
    proof -
      from \<open>b \<in> F`a\<close> \<open>c \<in> F`a\<close> \<open>q \<in> Pi\<^bsup>M\<^esup>(F`a,?Q)\<close> \<open>q\<in>M\<close>
      have "q`b \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v]"
        "q`c \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, c\<^sup>v]"
        using mem_Pi_rel_abs[of q] apply_type[of _ _  ?Q]
        by simp_all
      with \<open>b \<noteq> c\<close> \<open>q : F`a \<rightarrow> P\<close> \<open>a\<in>A\<close> \<open>b\<in>_\<close> \<open>c\<in>_\<close>
        \<open>A\<in>M\<close> \<open>f_dot\<in>M\<close> \<open>F`a\<in>M\<close>
      show ?thesis
        using forces_neq_apply_imp_incompatible
          transitivity[of _ A] transitivity[of _ "F`a"]
        by auto
    qed
    moreover from calculation
    have "antichain(range(q))"
      using Pi_range_eq[of _  _ "\<lambda>_ . P"]
      unfolding antichain_def by auto
    moreover from this and \<open>q\<in>M\<close>
    have "antichain_r'(range(q))"
      by (simp add:absolut)
    moreover from calculation
    have "q`b \<noteq> q`c" if "b \<noteq> c" "b \<in> F`a" "c \<in> F`a" for b c
      using that Incompatible_imp_not_eq apply_type
        mem_function_space_rel_abs by simp
    ultimately
    have "q \<in> inj\<^bsup>M\<^esup>(F`a,range(q))"
      using def_inj_rel by auto
    with \<open>F`a \<in> M\<close> \<open>q\<in>M\<close>
    have "|F`a|\<^bsup>M\<^esup> \<le> |range(q)|\<^bsup>M\<^esup>"
      using def_lepoll_rel
      by (rule_tac lepoll_rel_imp_cardinal_rel_le) auto
    also from \<open>antichain_r'(range(q))\<close> \<open>ccc\<^bsup>M\<^esup>(P,leq)\<close> \<open>q\<in>M\<close>
    have "|range(q)|\<^bsup>M\<^esup> \<le> \<omega>"
      using def_ccc_rel by simp
    finally
    show ?thesis using \<open>F`a\<in>M\<close> by auto
  qed
  moreover from this
  have "F`a\<in>M" if "a\<in>A" for a
    using that by simp
  moreover from this \<open>B\<in>M\<close>
  have "F : A \<rightarrow> Pow\<^bsup>M\<^esup>(B)"
    using Pow_rel_char
    unfolding F_def by (rule_tac lam_type) auto
  ultimately
  show ?thesis by auto
qed

end (* includes G_generic_lemmas *)

end (* G_generic *)

end