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

lemma f_imp_injective_rel:
  assumes "f \<in> A \<rightarrow>\<^bsup>M\<^esup> B" "\<forall>x\<in>A. d(f ` x) = x" "M(A)" "M(B)"
  shows "f \<in> inj\<^bsup>M\<^esup>(A, B)"
  using assms
  apply (simp (no_asm_simp) add: def_inj_rel)
  apply (auto intro: subst_context [THEN box_equals])
  done

lemma lam_injective_rel:
  assumes "\<And>x. x \<in> A \<Longrightarrow> c(x) \<in> B"
    "\<And>x. x \<in> A \<Longrightarrow> d(c(x)) = x"
    "M(A)" "M(B)"
  shows "(\<lambda>x\<in>A. c(x)) \<in> inj\<^bsup>M\<^esup>(A, B)"
  using assms
  apply (rule_tac d = d in f_imp_injective_rel)
     apply (simp_all add: lam_type)
  sorry

lemma f_imp_surjective_rel:
  assumes "f \<in> A \<rightarrow>\<^bsup>M\<^esup> B" "\<And>y. y \<in> B \<Longrightarrow> d(y) \<in> A" "\<And>y. y \<in> B \<Longrightarrow> f ` d(y) = y"
    "M(A)" "M(B)"
  shows "f \<in> surj\<^bsup>M\<^esup>(A, B)"
  using assms
  by (simp add: def_surj_rel, blast)

lemma lam_surjective_rel:
  assumes "\<And>x. x \<in> A \<Longrightarrow> c(x) \<in> B"
    "\<And>y. y \<in> B \<Longrightarrow> d(y) \<in> A"
    "\<And>y. y \<in> B \<Longrightarrow> c(d(y)) = y"
    "M(A)" "M(B)"
  shows "(\<lambda>x\<in>A. c(x)) \<in> surj\<^bsup>M\<^esup>(A, B)"
  using assms
  apply (rule_tac d = d in f_imp_surjective_rel)
      apply (simp_all add: lam_type)
  sorry

lemma lam_bijective_rel:
  assumes "\<And>x. x \<in> A \<Longrightarrow> c(x) \<in> B"
    "\<And>y. y \<in> B \<Longrightarrow> d(y) \<in> A"
    "\<And>x. x \<in> A \<Longrightarrow> d(c(x)) = x"
    "\<And>y. y \<in> B \<Longrightarrow> c(d(y)) = y"
    "M(A)" "M(B)"
  shows "(\<lambda>x\<in>A. c(x)) \<in> bij\<^bsup>M\<^esup>(A, B)"
  using assms
  apply (unfold bij_rel_def)
  apply (blast intro!: lam_injective_rel lam_surjective_rel)
  done

lemma Pow_rel_eqpoll_rel_function_space_rel:
  fixes d X
  notes bool_of_o_def [simp]
  defines [simp]:"d(A) \<equiv> (\<lambda>x\<in>X. bool_of_o(x\<in>A))"
    \<comment> \<open>the witnessing map for the thesis:\<close>
  assumes "M(X)"
  shows "Pow\<^bsup>M\<^esup>(X) \<approx>\<^bsup>M\<^esup> X \<rightarrow>\<^bsup>M\<^esup> 2"
  unfolding eqpoll_rel_def
proof (intro rexI, rule lam_bijective_rel)
  from assms
  interpret M_Pi_assumptions M X "\<lambda>_. 2"
    using Pi_replacement Pi_separation lam_replacement_identity
      lam_replacement_Sigfun[THEN lam_replacement_imp_strong_replacement]
    apply unfold_locales apply auto
    sorry
  \<comment> \<open>We give explicit mutual inverses\<close>
  fix A
  assume "A\<in>Pow\<^bsup>M\<^esup>(X)"
  moreover
  note \<open>M(X)\<close>
  moreover from calculation
  have "M(A)" by (auto dest:transM)
  ultimately
  show "d(A) : X \<rightarrow>\<^bsup>M\<^esup> 2"
    using lam_type_M[of "\<lambda>x. bool_of_o(x\<in>A)"] function_space_rel_char
      lam_type[of _ "\<lambda>x. bool_of_o(x\<in>A)" "\<lambda>_. 2"]
    apply (auto)
    sorry
  from \<open>A\<in>Pow\<^bsup>M\<^esup>(X)\<close> \<open>M(X)\<close>
  show "{y\<in>X. d(A)`y = 1} = A"
    using Pow_rel_char by auto
next
  fix f
  assume "f: X\<rightarrow>\<^bsup>M\<^esup> 2"
  with assms
  have "f: X\<rightarrow> 2" using function_space_rel_char by simp
  then
  show "d({y \<in> X . f ` y = 1}) = f"
    using apply_type[OF \<open>f: X\<rightarrow>2\<close>] by (force intro:fun_extension)
  show "{ya \<in> X . f ` ya = 1} \<in> Pow\<^bsup>M\<^esup>(X)"
    sorry
next
  show "M(\<lambda>x\<in>Pow\<^bsup>M\<^esup>(X). d(x))" sorry
qed (auto simp:\<open>M(X)\<close>)

lemma Pow_rel_bottom: "M(B) \<Longrightarrow> 0 \<in> Pow\<^bsup>M\<^esup>(B)"
  using Pow_rel_char by simp

(* FIXME: missing assms on \<^term>\<open>b\<close> being definable on M *)
lemma cantor_rel: "M(A) \<Longrightarrow> \<exists>S \<in> Pow\<^bsup>M\<^esup>(A). \<forall>x\<in>A. b(x) \<noteq> S"
  sorry

lemma cantor_surj_rel: "M(f) \<Longrightarrow> M(A) \<Longrightarrow> f \<notin> surj\<^bsup>M\<^esup>(A,Pow\<^bsup>M\<^esup>(A))"
  apply (simp add: def_surj_rel, safe)
  apply (cut_tac cantor_rel)
  sorry

lemma cantor_inj_rel: "M(f) \<Longrightarrow> M(A) \<Longrightarrow> f \<notin> inj\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A),A)"
  using inj_rel_imp_surj_rel[OF _ Pow_rel_bottom, of f A A]
    cantor_surj_rel[of "\<lambda>x\<in>A. if x \<in> range(f) then converse(f) ` x else 0" A]
    lam_replacement_if separation_in[of "range(f)"]
    lam_replacement_converse_app[THEN [5] lam_replacement_hcomp2]
    lam_replacement_identity lam_replacement_constant
    lam_replacement_iff_lam_closed by auto

end (* M_ZF_library *)

end