(* FIXME: To be incorporated to Cardinal_Library_Relative *)
theory Cardinal_Library_Relative2
  imports
    Cardinal_Library_Relative
    ZF_Library_Relative2
begin

context M_library
begin

subsection\<open>Results on cardinal exponentiation\<close>

lemma cexp_rel_eqpoll_rel_cong:
  assumes
    "A \<approx>\<^bsup>M\<^esup> A'" "B \<approx>\<^bsup>M\<^esup> B'" "M(A)" "M(A')" "M(B)" "M(B')"
  shows
    "A\<^bsup>\<up>B,M\<^esup> = A'\<^bsup>\<up>B',M\<^esup>"
  unfolding cexp_rel_def using cardinal_rel_eqpoll_rel_iff
    function_space_rel_eqpoll_rel_cong assms
  by simp

lemma cexp_rel_cexp_rel_cmult: 
  assumes "M(\<kappa>)" "M(\<nu>1)" "M(\<nu>2)"
  shows "(\<kappa>\<^bsup>\<up>\<nu>1,M\<^esup>)\<^bsup>\<up>\<nu>2,M\<^esup> = \<kappa>\<^bsup>\<up>\<nu>2 \<otimes>\<^bsup>M\<^esup> \<nu>1,M\<^esup>"
proof -
  have "(\<kappa>\<^bsup>\<up>\<nu>1,M\<^esup>)\<^bsup>\<up>\<nu>2,M\<^esup> = (\<nu>1 \<rightarrow>\<^bsup>M\<^esup> \<kappa>)\<^bsup>\<up>\<nu>2,M\<^esup>"
    using cardinal_rel_eqpoll_rel
    by (intro cexp_rel_eqpoll_rel_cong) (simp_all add:assms cexp_rel_def)
  also from assms
  have " \<dots> = \<kappa>\<^bsup>\<up>\<nu>2 \<times> \<nu>1,M\<^esup>"
    unfolding cexp_rel_def using curry_eqpoll_rel[THEN cardinal_rel_cong] by blast
  also
  have " \<dots> = \<kappa>\<^bsup>\<up>\<nu>2 \<otimes>\<^bsup>M\<^esup> \<nu>1,M\<^esup>"
    using cardinal_rel_eqpoll_rel[THEN eqpoll_rel_sym]
    unfolding cmult_rel_def by (intro cexp_rel_eqpoll_rel_cong) (auto simp add:assms)
  finally
  show ?thesis .
qed

lemma cardinal_rel_Pow_rel: "M(X) \<Longrightarrow> |Pow_rel(M,X)|\<^bsup>M\<^esup> = 2\<^bsup>\<up>X,M\<^esup>" \<comment> \<open>Perhaps it's better with |X|\<close>
  using cardinal_rel_eqpoll_rel_iff[THEN iffD2,
      OF _ _ Pow_rel_eqpoll_rel_function_space_rel]
  unfolding cexp_rel_def by simp

lemma cantor_cexp_rel:
  assumes "Card_rel(M,\<nu>)" "M(\<nu>)"
  shows "\<nu> < 2\<^bsup>\<up>\<nu>,M\<^esup>"
  using assms Card_rel_is_Ord Card_rel_cexp_rel
proof (intro not_le_iff_lt[THEN iffD1] notI)
  assume "2\<^bsup>\<up>\<nu>,M\<^esup> \<le> \<nu>"
  with assms
  have "|Pow_rel(M,\<nu>)|\<^bsup>M\<^esup> \<le> \<nu>"
    using cardinal_rel_Pow_rel[of \<nu>] by simp
  with assms
  have "Pow_rel(M,\<nu>) \<lesssim>\<^bsup>M\<^esup> \<nu>"
    using cardinal_rel_eqpoll_rel_iff Card_rel_le_imp_lepoll_rel Card_rel_cardinal_rel_eq
    by auto
  then
  obtain g where "g \<in> inj_rel(M,Pow_rel(M,\<nu>), \<nu>)"
    by blast
  moreover
  note \<open>M(\<nu>)\<close>
  moreover from calculation
  have "M(g)" by (auto dest:transM)
  ultimately
  show "False"
    using cantor_inj_rel by simp
qed simp

lemma countable_iff_le_rel_Aleph_rel_one:
  notes iff_trans[trans]
  assumes "M(C)"
  shows "countable\<^bsup>M\<^esup>(C) \<longleftrightarrow> |C|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
proof -
  have "countable\<^bsup>M\<^esup>(C) \<longleftrightarrow> C \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using assms lesspoll_rel_csucc_rel[of \<omega> C] Aleph_rel_succ Aleph_rel_zero
    unfolding countable_rel_def by simp
  also from assms
  have "\<dots> \<longleftrightarrow> |C|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using cardinal_rel_eqpoll_rel[THEN eqpoll_rel_sym, THEN eq_lesspoll_rel_trans]
    by (auto intro:cardinal_rel_eqpoll_rel[THEN eq_lesspoll_rel_trans])
  finally
  show ?thesis .
qed

end (* M_library *)

(* FIXME: This can be generalized. *)
lemma (in M_cardinal_library) countable_fun_imp_countable_image:
  assumes "f:C \<rightarrow>\<^bsup>M\<^esup> B" "countable\<^bsup>M\<^esup>(C)" "\<And>c. c\<in>C \<Longrightarrow> countable\<^bsup>M\<^esup>(f`c)"
    "M(C)" "M(B)"
  shows "countable\<^bsup>M\<^esup>(\<Union>(f``C))"
  using assms function_space_rel_char image_fun[of f]
    cardinal_rel_RepFun_apply_le[of f C B]
    countable_rel_iff_cardinal_rel_le_nat[THEN iffD1, THEN [2] le_trans, of _ ]
    countable_rel_iff_cardinal_rel_le_nat
  by (rule_tac countable_rel_union_countable_rel)
    (auto dest:transM del:imageE)

end