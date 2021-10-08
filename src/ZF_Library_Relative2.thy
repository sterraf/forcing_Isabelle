(* FIXME: To be incorporated to ZF_Library_Relative *)
theory ZF_Library_Relative2
  imports
    ZF_Library_Relative
begin

context M_ZF_library
begin

lemma function_space_rel_eqpoll_rel_cong:
  assumes
    "A \<approx>\<^bsup>M\<^esup> A'" "B \<approx>\<^bsup>M\<^esup> B'" "M(A)" "M(A')" "M(B)" "M(B')"
  shows
    "A \<rightarrow>\<^bsup>M\<^esup> B \<approx>\<^bsup>M\<^esup> A' \<rightarrow>\<^bsup>M\<^esup> B'"
  sorry
(* proof -
  from assms(1)[THEN eqpoll_sym] assms(2)
  obtain f g where "f \<in> bij(A',A)" "g \<in> bij(B,B')"
    by blast
  then
  have "converse(g) : B' \<rightarrow> B" "converse(f): A \<rightarrow> A'"
    using bij_converse_bij bij_is_fun by auto
  show ?thesis
    unfolding eqpoll_def
  proof (intro exI fg_imp_bijective, rule_tac [1-2] lam_type)
    fix F
    assume "F: A \<rightarrow> B"
    with \<open>f \<in> bij(A',A)\<close> \<open>g \<in> bij(B,B')\<close>
    show "g O F O f : A' \<rightarrow> B'"
      using bij_is_fun comp_fun by blast
  next
    fix F
    assume "F: A' \<rightarrow> B'"
    with \<open>converse(g) : B' \<rightarrow> B\<close> \<open>converse(f): A \<rightarrow> A'\<close>
    show "converse(g) O F O converse(f) : A \<rightarrow> B"
      using comp_fun by blast
  next
    from \<open>f\<in>_\<close> \<open>g\<in>_\<close> \<open>converse(f)\<in>_\<close> \<open>converse(g)\<in>_\<close>
    have "(\<And>x. x \<in> A' \<rightarrow> B' \<Longrightarrow> converse(g) O x O converse(f) \<in> A \<rightarrow> B)"
      using bij_is_fun comp_fun by blast
    then
    have "(\<lambda>x\<in>A \<rightarrow> B. g O x O f) O (\<lambda>x\<in>A' \<rightarrow> B'. converse(g) O x O converse(f))
          =  (\<lambda>x\<in>A' \<rightarrow> B' . (g O converse(g)) O x O (converse(f) O f))"
      using lam_cong comp_assoc comp_lam[of "A' \<rightarrow> B'" ] by auto
    also
    have "... = (\<lambda>x\<in>A' \<rightarrow> B' . id(B') O x O (id(A')))"
      using left_comp_inverse[OF bij_is_inj[OF \<open>f\<in>_\<close>]]
        right_comp_inverse[OF bij_is_surj[OF \<open>g\<in>_\<close>]]
      by auto
    also
    have "... = (\<lambda>x\<in>A' \<rightarrow> B' . x)"
      using left_comp_id[OF fun_is_rel] right_comp_id[OF fun_is_rel]  lam_cong by auto
    also
    have "... = id(A'\<rightarrow>B')" unfolding id_def by simp
    finally
    show "(\<lambda>x\<in>A -> B. g O x O f) O (\<lambda>x\<in>A' -> B'. converse(g) O x O converse(f)) = id(A' -> B')" .
  next
    from \<open>f\<in>_\<close> \<open>g\<in>_\<close>
    have "(\<And>x. x \<in> A \<rightarrow> B \<Longrightarrow> g O x O f \<in> A' \<rightarrow> B')"
      using bij_is_fun comp_fun by blast
    then
    have "(\<lambda>x\<in>A' -> B'. converse(g) O x O converse(f)) O (\<lambda>x\<in>A -> B. g O x O f)
          = (\<lambda>x\<in>A \<rightarrow> B . (converse(g) O g) O x O (f O converse(f)))"
      using comp_lam comp_assoc by auto
    also
    have "... = (\<lambda>x\<in>A \<rightarrow> B . id(B) O x O (id(A)))"
      using
        right_comp_inverse[OF bij_is_surj[OF \<open>f\<in>_\<close>]]
        left_comp_inverse[OF bij_is_inj[OF \<open>g\<in>_\<close>]] lam_cong
      by auto
    also
    have "... = (\<lambda>x\<in>A \<rightarrow> B . x)"
      using left_comp_id[OF fun_is_rel] right_comp_id[OF fun_is_rel] lam_cong by auto
    also
    have "... = id(A\<rightarrow>B)" unfolding id_def by simp
    finally
    show "(\<lambda>x\<in>A' \<rightarrow> B'. converse(g) O x O converse(f)) O (\<lambda>x\<in>A -> B. g O x O f) = id(A -> B)" .
  qed
qed
*)

lemma curry_eqpoll_rel:
  fixes \<nu>1 \<nu>2  \<kappa>
  assumes  "M(\<nu>1)" "M(\<nu>2)" "M(\<kappa>)"
  shows "\<nu>1 \<rightarrow>\<^bsup>M\<^esup> (\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>) \<approx>\<^bsup>M\<^esup> \<nu>1 \<times> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>"
  unfolding eqpoll_def
  sorry
(* proof (intro exI, rule lam_bijective,
    rule_tac [1-2] lam_type, rule_tac [2] lam_type)
  fix f z
  assume "f : \<nu>1 \<rightarrow> \<nu>2 \<rightarrow> \<kappa>" "z \<in> \<nu>1 \<times> \<nu>2"
  then
  show "f`fst(z)`snd(z) \<in> \<kappa>"
    by simp
next
  fix f x y
  assume "f : \<nu>1 \<times> \<nu>2 \<rightarrow> \<kappa>" "x\<in>\<nu>1" "y\<in>\<nu>2"
  then
  show "f`\<langle>x,y\<rangle> \<in> \<kappa>" by simp
next \<comment> \<open>one composition is the identity:\<close>
  fix f
  assume "f : \<nu>1 \<times> \<nu>2 \<rightarrow> \<kappa>"
  then
  show "(\<lambda>x\<in>\<nu>1 \<times> \<nu>2. (\<lambda>x\<in>\<nu>1. \<lambda>xa\<in>\<nu>2. f ` \<langle>x, xa\<rangle>) ` fst(x) ` snd(x)) = f"
    by (auto intro:fun_extension)
qed simp \<comment> \<open>the other composition follows automatically\<close>
 *)

lemma Pow_eqpoll_function_space:
  fixes d X
  notes bool_of_o_def [simp]
  defines [simp]:"d(A) \<equiv> (\<lambda>x\<in>X. bool_of_o(x\<in>A))"
    \<comment> \<open>the witnessing map for the thesis:\<close>
  shows "Pow(X) \<approx> X \<rightarrow> 2"
  unfolding eqpoll_def
proof (intro exI, rule lam_bijective)
  \<comment> \<open>We give explicit mutual inverses\<close>
  fix A
  assume "A\<in>Pow(X)"
  then
  show "d(A) : X \<rightarrow> 2"
    using lam_type[of _ "\<lambda>x. bool_of_o(x\<in>A)" "\<lambda>_. 2"]
    by force
  from \<open>A\<in>Pow(X)\<close>
  show "{y\<in>X. d(A)`y = 1} = A"
    by (auto)
next
  fix f
  assume "f: X\<rightarrow>2"
  then
  show "d({y \<in> X . f ` y = 1}) = f"
    using apply_type[OF \<open>f: X\<rightarrow>2\<close>]
    by (force intro:fun_extension)
qed blast

lemma cantor_inj: "f \<notin> inj(Pow(A),A)"
  using inj_imp_surj[OF _ Pow_bottom] cantor_surj by blast

end (* M_ZF_library *)

end