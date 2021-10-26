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
  shows "(\<kappa>\<^bsup>\<up>\<nu>1,M\<^esup>)\<^bsup>\<up>\<nu>2,M\<^esup> = \<kappa>\<^bsup>\<up>\<nu>2 \<otimes> \<nu>1,M\<^esup>"
proof -
  have "(\<kappa>\<^bsup>\<up>\<nu>1\<^esup>)\<^bsup>\<up>\<nu>2\<^esup> = (\<nu>1 \<rightarrow> \<kappa>)\<^bsup>\<up>\<nu>2\<^esup>"
    using cardinal_rel_eqpoll_rel
    by (intro cexp_rel_eqpoll_rel_cong) (simp_all add:cexp_rel_def)
  also
  have " \<dots> = \<kappa>\<^bsup>\<up>\<nu>2 \<times> \<nu>1\<^esup>"
    unfolding cexp_rel_def using curry_eqpoll_rel cardinal_rel_cong by blast*
  also
  have " \<dots> = \<kappa>\<^bsup>\<up>\<nu>2 \<otimes> \<nu>1\<^esup>"
    using cardinal_rel_eqpoll_rel[THEN eqpoll_rel_sym]
    unfolding cmult_def by (intro cexp_rel_eqpoll_rel_cong) (simp)
  finally
  show ?thesis  .
qed

lemma cardinal_rel_Pow_rel: "M(X) \<Longrightarrow> |Pow_rel(M,X)|\<^bsup>M\<^esup> = 2\<^bsup>\<up>X,M\<^esup>" \<comment> \<open>Perhaps it's better with |X|\<close>
  using cardinal_rel_eqpoll_rel_iff[THEN iffD2, OF Pow_rel_eqpoll_rel_function_space_rel]
  unfolding cexp_rel_def by simp

lemma cantor_cexp_rel:
  assumes "Card_rel(M,\<nu>)" "M(\<nu>)"
  shows "\<nu> < 2\<^bsup>\<up>\<nu>,M\<^esup>"
  using assms Card_rel_is_Ord Card_rel_cexp_rel
  sorry
(*
proof (intro not_le_iff_lt[THEN iffD1] notI)
  assume "2\<^bsup>\<up>\<nu>,M\<^esup> \<le> \<nu>"
  then
  have "|Pow_rel(M,\<nu>)| \<le> \<nu>"
    using cardinal_rel_Pow_rel by simp
  with assms
  have "Pow_rel(M,\<nu>) \<lesssim>\<^bsup>M\<^esup> \<nu>"
    using cardinal_rel_eqpoll_rel_iff Card_rel_le_imp_lepoll_rel Card_rel_cardinal_rel_eq
    by auto
  then
  obtain g where "g \<in> inj_rel(M,Pow_rel(M,\<nu>), \<nu>)"
    by blast
  then
  show "False"
    using cantor_inj_rel by simp
qed simp
*)

end (* M_cardinal_library *)

end