section\<open>From M to V\<close>

theory Absolute_Versions
  imports
    Cardinal_AC_Relative

begin

subsection\<open>Locales of a class "M" hold in V\<close>

interpretation (* mtriv_V: *) M_trivial "\<lambda>_. True"
proof
  show "Union_ax(\<lambda>_. True)"
    unfolding Union_ax_def big_union_def
    by (auto intro:rexI[of _ "\<Union>_"])
qed (unfold upair_ax_def upair_def, auto)

lemmas bad_simps = nonempty Forall_in_M_iff Inl_in_M_iff Inr_in_M_iff 
  succ_in_M_iff singleton_in_M_iff Equal_in_M_iff Member_in_M_iff Nand_in_M_iff 
  Cons_in_M_iff pair_in_M_iff upair_in_M_iff

lemmas bad_M_trivial_simps[simp del] = Forall_in_M_iff Equal_in_M_iff
  nonempty

lemmas bad_M_trivial_rules[rule del] =  pair_in_MI singleton_in_MI pair_in_MD nat_into_M
  depth_closed length_closed nat_case_closed separation_closed
  Un_closed strong_replacement_closed nonempty

lemma separation_absolute: "separation(\<lambda>_. True, P)"
  unfolding separation_def
  by (rule rallI, rule_tac x="{x\<in>_ . P(x)}" in rexI) auto

lemma univalent_absolute: 
  assumes "univalent(\<lambda>_. True, A, P)"
    "P(x, b)"  "x \<in> A" 
  shows "P(x, y) \<Longrightarrow> y = b"
  using assms
  unfolding univalent_def by force

lemma replacement_absolute: "strong_replacement(\<lambda>_. True, P)"
  unfolding strong_replacement_def
proof (intro rallI impI)
  fix A
  assume "univalent(\<lambda>_. True, A, P)"
  then
  show "\<exists>Y[\<lambda>_. True]. \<forall>b[\<lambda>_. True]. b \<in> Y \<longleftrightarrow> (\<exists>x[\<lambda>_. True]. x \<in> A \<and> P(x, b))"
    by (rule_tac x="{y. x\<in>A , P(x,y)}" in rexI)
      (auto dest:univalent_absolute[of _ P])
qed

interpretation M_basic "\<lambda>_. True"
proof
  {
    fix x
    have "\<forall>y[\<lambda>_. True]. y \<in> Pow(x) \<longleftrightarrow> (\<forall>z[\<lambda>_. True]. z \<in> y \<longrightarrow> z \<in> x)"
      by auto
  }
  then
  show "power_ax(\<lambda>_. True)"
    unfolding power_ax_def powerset_def subset_def by blast
qed (auto simp add: upair_ax_def upair_def 
    intro:separation_absolute replacement_absolute)

lemmas bad_M_basic_rules[simp del, rule del] = 
  cartprod_closed finite_funspace_closed converse_closed 
  list_case'_closed pred_closed

interpretation M_cardinal_arith "\<lambda>_. True"
  by unfold_locales 
    (auto intro:separation_absolute replacement_absolute)

lemmas bad_M_cardinals_rules[simp del, rule del] =
  iterates_closed M_nat trancl_closed rvimage_closed

named_theorems V_simps

lemma eqpoll_rel_absolute[V_simps]: "eqpoll_rel(\<lambda>_. True,x,y) \<longleftrightarrow> eqpoll(x,y)"
  unfolding eqpoll_def using def_eqpoll_rel by auto

lemma cardinal_rel_absolute[V_simps]: "cardinal_rel(x) = cardinal(x)"
  unfolding cardinal_def using def_cardinal_rel eqpoll_rel_absolute
  by simp

\<comment> \<open>Example of an absolute lemma obtained from the relative version\<close>
lemma Ord_cardinal_idem': "Ord(A) \<Longrightarrow> ||A|| = |A|"
  using Ord_cardinal_rel_idem by (simp add:V_simps)

\<comment> \<open>Example of a transfer result between a transitive model and $V$\<close>
lemma (in M_Perm) assumes "M(A)" "M(B)" "A \<approx>r B"
  shows "A \<approx> B"
proof -
  interpret M_N_Perm M "\<lambda>_. True"
    by (unfold_locales, simp)
  from assms
  show ?thesis using eqpoll_rel_transfer 
    by (simp add:V_simps)
qed

end