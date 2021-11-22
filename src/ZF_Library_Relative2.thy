(* FIXME: To be incorporated to ZF_Library_Relative *)
theory ZF_Library_Relative2
  imports
    ZF_Library_Relative
begin

context M_ZF_library
begin

lemma lam_replacement_twist: "lam_replacement(M,\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>. \<langle>x,y,z\<rangle>)"
    using lam_replacement_fst lam_replacement_snd
      lam_replacement_Pair[THEN [5] lam_replacement_hcomp2,
        of "\<lambda>x. snd(fst(x))" "\<lambda>x. snd(x)", THEN [2] lam_replacement_Pair[
          THEN [5] lam_replacement_hcomp2, of "\<lambda>x. fst(fst(x))"]]
      lam_replacement_hcomp unfolding split_def by simp

lemma twist_closed[intro,simp]: "M(x) \<Longrightarrow> M((\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>. \<langle>x,y,z\<rangle>)(x))"
  unfolding split_def by simp

lemma lam_replacement_Lambda:
  assumes "lam_replacement(M, \<lambda>y. b(fst(y), snd(y)))"
    "\<forall>w[M]. \<forall>y[M]. M(b(w, y))" "M(W)"
  shows "lam_replacement(M, \<lambda>x. \<lambda>w\<in>W. b(x, w))"
proof (intro lam_replacement_iff_lam_closed[THEN iffD2]; clarify)
  from assms
  show lbc:"M(x) \<Longrightarrow> M(\<lambda>w\<in>W. b(x, w))" for x
    using lam_replacement_constant lam_replacement_identity
      lam_replacement_hcomp2[where h=b]
    by (intro lam_replacement_iff_lam_closed[THEN iffD1, rule_format])
      simp_all
  fix A
  assume "M(A)"
  moreover from this assms
  have "M({b(fst(x),snd(x)). x \<in> A\<times>W})" (is "M(?RFb)")\<comment> \<open>\<^term>\<open>RepFun\<close> \<^term>\<open>b\<close>\<close>
    using lam_replacement_imp_strong_replacement transM[of _ "A\<times>W"]
    by (rule_tac RepFun_closed) auto
  moreover
  have "{\<langle>\<langle>x,y\<rangle>,z\<rangle> \<in> (A\<times>W)\<times>?RFb. z = b(x,y)} = (\<lambda>\<langle>x,y\<rangle>\<in>A\<times>W. b(x,y)) \<inter> (A\<times>W)\<times>?RFb"
    (is "{\<langle>\<langle>x,y\<rangle>,z\<rangle> \<in> (A\<times>W)\<times>?B. _ } = ?lam")
    unfolding lam_def by auto
  moreover from calculation and assms
  have "M(?lam)"
    using lam_replacement_iff_lam_closed unfolding split_def by simp
  moreover
  have "{\<langle>\<langle>x,y\<rangle>,z\<rangle> \<in> (X \<times> Y) \<times> Z . P(x, y, z)} \<subseteq> (X \<times> Y) \<times> Z" for X Y Z P
    by auto
  then
  have "{\<langle>x,y,z\<rangle> \<in> X\<times>Y\<times>Z. P(x,y,z) }= (\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>\<in>(X\<times>Y)\<times>Z. \<langle>x,y,z\<rangle>) ``
        {\<langle>\<langle>x,y\<rangle>,z\<rangle> \<in> (X\<times>Y)\<times>Z. P(x,y,z) }" (is "?C' = Lambda(?A,?f) `` ?C")
      for X Y Z P
    using image_lam[of ?C ?A ?f]
    by (intro equalityI) (auto)
  with calculation
  have "{\<langle>x,y,z\<rangle> \<in> A\<times>W\<times>?RFb. z = b(x,y) } =
        (\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>\<in>(A\<times>W)\<times>?RFb. \<langle>x,y,z\<rangle>) `` ?lam" (is "?H = ?G ")
    by simp
  with \<open>M(A)\<close> \<open>M(W)\<close> \<open>M(?lam)\<close> \<open>M(?RFb)\<close>
  have "M(?H)"
    using lam_replacement_iff_lam_closed[THEN iffD1, rule_format, OF _ lam_replacement_twist]
    by simp
  with \<open>M(A)\<close>
  have "(\<lambda>x\<in>A. \<lambda>w\<in>W. b(x, w)) =
    {\<langle>x,Z\<rangle> \<in> A \<times> Pow\<^bsup>M\<^esup>(range(?H)). Z = {y \<in> W\<times>?RFb . \<langle>x, y\<rangle> \<in> ?H}}"
    unfolding lam_def
    by (intro equalityI; subst Pow_rel_char[of "range(?H)"])
      (auto dest:transM simp: lbc[unfolded lam_def], force+)
  ultimately
  show "M(\<lambda>x\<in>A. \<lambda>w\<in>W. b(x, w))"
    unfolding lam_def
    sorry
qed

lemma lam_replacement_apply_Pair:
  assumes "M(y)"
  shows "lam_replacement(M, \<lambda>x. y ` \<langle>fst(x), snd(x)\<rangle>)"
  using assms lam_replacement_constant lam_replacement_Pair
    lam_replacement_apply2[THEN [5] lam_replacement_hcomp2]
  by auto

lemma lam_replacement_apply_fst_snd:
  shows "lam_replacement(M, \<lambda>w. fst(w) ` fst(snd(w)) ` snd(snd(w)))"
  using lam_replacement_fst lam_replacement_snd lam_replacement_hcomp
    lam_replacement_apply2[THEN [5] lam_replacement_hcomp2]
  by auto

lemma separation_snd_in_fst: "separation(M, \<lambda>x. snd(x) \<in> fst(x))"
  using separation_in lam_replacement_fst lam_replacement_snd
  by auto

lemma lam_replacement_if_mem:
  "lam_replacement(M, \<lambda>x. if snd(x) \<in> fst(x) then 1 else 0)"
  using separation_snd_in_fst
    lam_replacement_constant lam_replacement_if
  by auto

(*FIXME: move this to Lambda_Replacement and prove it. *)
lemma lam_replacement_comp: "lam_replacement(M, \<lambda>x. fst(x) O snd(x))"
  sorry

lemma lam_replacement_Lambda_apply_fst_snd:
  assumes "M(X)"
  shows "lam_replacement(M, \<lambda>x. \<lambda>w\<in>X. x ` fst(w) ` snd(w))"
  using assms lam_replacement_apply_fst_snd lam_replacement_Lambda
  by simp

lemma lam_replacement_Lambda_apply_Pair:
  assumes "M(X)" "M(y)"
  shows "lam_replacement(M, \<lambda>x. \<lambda>w\<in>X. y ` \<langle>x, w\<rangle>)"
  using assms lam_replacement_apply_Pair lam_replacement_Lambda
  by simp

lemma lam_replacement_Lambda_if_mem:
  assumes "M(X)"
  shows "lam_replacement(M, \<lambda>x. \<lambda>xa\<in>X. if xa \<in> x then 1 else 0)"
  using assms lam_replacement_if_mem lam_replacement_Lambda
  by simp

lemma lam_replacement_comp':
  "M(f) \<Longrightarrow> M(g) \<Longrightarrow> lam_replacement(M, \<lambda>x . f O x O g)"
  using lam_replacement_comp[THEN [5] lam_replacement_hcomp2,
      OF lam_replacement_constant lam_replacement_comp,
      THEN [5] lam_replacement_hcomp2] lam_replacement_constant
    lam_replacement_identity by simp

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
    "\<forall>x[M]. M(c(x))" "lam_replacement(M,c)"
    "M(A)" "M(B)"
  shows "(\<lambda>x\<in>A. c(x)) \<in> inj\<^bsup>M\<^esup>(A, B)"
  using assms function_space_rel_char lam_replacement_iff_lam_closed
  by (rule_tac d = d in f_imp_injective_rel)
    (auto simp add: lam_type)

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
    "\<forall>x[M]. M(c(x))" "lam_replacement(M,c)"
    "M(A)" "M(B)"
  shows "(\<lambda>x\<in>A. c(x)) \<in> surj\<^bsup>M\<^esup>(A, B)"
  using assms function_space_rel_char lam_replacement_iff_lam_closed
  by (rule_tac d = d in f_imp_surjective_rel)
    (auto simp add: lam_type)

lemma lam_bijective_rel:
  assumes "\<And>x. x \<in> A \<Longrightarrow> c(x) \<in> B"
    "\<And>y. y \<in> B \<Longrightarrow> d(y) \<in> A"
    "\<And>x. x \<in> A \<Longrightarrow> d(c(x)) = x"
    "\<And>y. y \<in> B \<Longrightarrow> c(d(y)) = y"
    "\<forall>x[M]. M(c(x))" "lam_replacement(M,c)"
    "M(A)" "M(B)"
  shows "(\<lambda>x\<in>A. c(x)) \<in> bij\<^bsup>M\<^esup>(A, B)"
  using assms
  apply (unfold bij_rel_def)
  apply (blast intro!: lam_injective_rel lam_surjective_rel)
  done

lemma function_space_rel_eqpoll_rel_cong:
  assumes
    "A \<approx>\<^bsup>M\<^esup> A'" "B \<approx>\<^bsup>M\<^esup> B'" "M(A)" "M(A')" "M(B)" "M(B')"
  shows
    "A \<rightarrow>\<^bsup>M\<^esup> B \<approx>\<^bsup>M\<^esup> A' \<rightarrow>\<^bsup>M\<^esup> B'"
proof -
  from assms(1)[THEN eqpoll_rel_sym] assms(2) assms lam_type
  obtain f g where "f \<in> bij\<^bsup>M\<^esup>(A',A)" "g \<in> bij\<^bsup>M\<^esup>(B,B')"
    by blast
  with assms
  have "converse(g) : bij\<^bsup>M\<^esup>(B', B)" "converse(f): bij\<^bsup>M\<^esup>(A, A')"
    using bij_converse_bij by auto
  let ?H="\<lambda> h \<in> A \<rightarrow>\<^bsup>M\<^esup> B . g O h O f"
  let ?I="\<lambda> h \<in> A' \<rightarrow>\<^bsup>M\<^esup> B' . converse(g) O h O converse(f)"
  have go:"g O F O f : A' \<rightarrow>\<^bsup>M\<^esup> B'" if "F: A \<rightarrow>\<^bsup>M\<^esup> B" for F
    proof -
    note assms \<open>f\<in>_\<close> \<open>g\<in>_\<close> that
    moreover from this
    have "g O F O f : A' \<rightarrow> B'"
      using bij_rel_is_fun[OF \<open>g\<in>_\<close>] bij_rel_is_fun[OF \<open>f\<in>_\<close>] comp_fun
        mem_function_space_rel[OF \<open>F\<in>_\<close>]
      by blast
    ultimately
    show "g O F O f : A' \<rightarrow>\<^bsup>M\<^esup> B'"
      using comp_closed function_space_rel_char bij_rel_char
      by auto
  qed
  have og:"converse(g) O F O converse(f) : A \<rightarrow>\<^bsup>M\<^esup> B" if "F: A' \<rightarrow>\<^bsup>M\<^esup> B'" for F
  proof -
    note assms that \<open>converse(f) \<in> _\<close> \<open>converse(g) \<in> _\<close>
    moreover from this
    have "converse(g) O F O converse(f) : A \<rightarrow> B"
      using bij_rel_is_fun[OF \<open>converse(g)\<in>_\<close>] bij_rel_is_fun[OF \<open>converse(f)\<in>_\<close>] comp_fun
        mem_function_space_rel[OF \<open>F\<in>_\<close>]
      by blast
    ultimately
    show "converse(g) O F O converse(f) : A \<rightarrow>\<^bsup>M\<^esup> B" (is "?G\<in>_") 
      using comp_closed function_space_rel_char bij_rel_char
      by auto
  qed
  with go
  have tc:"?H \<in> (A \<rightarrow>\<^bsup>M\<^esup> B) \<rightarrow> (A'\<rightarrow>\<^bsup>M\<^esup> B')" "?I \<in> (A' \<rightarrow>\<^bsup>M\<^esup> B') \<rightarrow> (A\<rightarrow>\<^bsup>M\<^esup> B)"
    using lam_type by auto
  with assms \<open>f\<in>_\<close> \<open>g\<in>_\<close>
  have "M(g O x O f)" and "M(converse(g) O x O converse(f))" if "M(x)" for x 
    using bij_rel_char comp_closed that by auto
  with assms \<open>f\<in>_\<close> \<open>g\<in>_\<close>
  have "M(?H)" "M(?I)" 
    using lam_replacement_iff_lam_closed[THEN iffD1,OF _ lam_replacement_comp']
      bij_rel_char by auto
  show ?thesis
    unfolding eqpoll_rel_def
  proof (intro rexI[of _ ?H] fg_imp_bijective_rel)
  from og go
  have "(\<And>x. x \<in> A' \<rightarrow>\<^bsup>M\<^esup> B' \<Longrightarrow> converse(g) O x O converse(f) \<in> A \<rightarrow>\<^bsup>M\<^esup> B)"
    by simp
  next
    show "M(A \<rightarrow>\<^bsup>M\<^esup> B)" using assms by simp
  next    
    show "M(A' \<rightarrow>\<^bsup>M\<^esup> B')" using assms by simp
  next
    from og assms
    have "?H O ?I = (\<lambda>x\<in>A' \<rightarrow>\<^bsup>M\<^esup> B' . (g O converse(g)) O x O (converse(f) O f))"
      using lam_cong[OF refl[of "A' \<rightarrow>\<^bsup>M\<^esup> B'"]] comp_assoc comp_lam
      by auto
    also
    have "... = (\<lambda>x\<in>A' \<rightarrow>\<^bsup>M\<^esup> B' . id(B') O x O (id(A')))"
      using left_comp_inverse[OF mem_inj_rel[OF bij_rel_is_inj_rel]] \<open>f\<in>_\<close>
        right_comp_inverse[OF bij_is_surj[OF mem_bij_rel]] \<open>g\<in>_\<close> assms
      by auto
    also
    have "... = (\<lambda>x\<in>A' \<rightarrow>\<^bsup>M\<^esup> B' . x)"
      using left_comp_id[OF fun_is_rel[OF mem_function_space_rel]] 
        right_comp_id[OF fun_is_rel[OF mem_function_space_rel]] assms
      by auto
    also
    have "... = id(A'\<rightarrow>\<^bsup>M\<^esup>B')" unfolding id_def by simp
    finally
    show "?H O ?I = id(A' \<rightarrow>\<^bsup>M\<^esup> B')" .
  next
    from go assms
    have "?I O ?H = (\<lambda>x\<in>A \<rightarrow>\<^bsup>M\<^esup> B . (converse(g) O g) O x O (f O converse(f)))"
      using lam_cong[OF refl[of "A \<rightarrow>\<^bsup>M\<^esup> B"]] comp_assoc comp_lam by auto
    also
    have "... = (\<lambda>x\<in>A \<rightarrow>\<^bsup>M\<^esup> B . id(B) O x O (id(A)))"
      using
        left_comp_inverse[OF mem_inj_rel[OF bij_rel_is_inj_rel[OF \<open>g\<in>_\<close>]]]
        right_comp_inverse[OF bij_is_surj[OF mem_bij_rel[OF \<open>f\<in>_\<close>]]] assms
      by auto
    also
    have "... = (\<lambda>x\<in>A \<rightarrow>\<^bsup>M\<^esup> B . x)"
      using left_comp_id[OF fun_is_rel[OF mem_function_space_rel]] 
        right_comp_id[OF fun_is_rel[OF mem_function_space_rel]]
         assms
      by auto
    also
    have "... = id(A\<rightarrow>\<^bsup>M\<^esup>B)" unfolding id_def by simp
    finally
    show "?I O ?H = id(A \<rightarrow>\<^bsup>M\<^esup> B)" .
  next 
    from assms tc \<open>M(?H)\<close> \<open>M(?I)\<close>
    show "?H \<in> (A\<rightarrow>\<^bsup>M\<^esup> B) \<rightarrow>\<^bsup>M\<^esup> (A'\<rightarrow>\<^bsup>M\<^esup> B')" "M(?H)"
       "?I \<in> (A'\<rightarrow>\<^bsup>M\<^esup> B') \<rightarrow>\<^bsup>M\<^esup> (A\<rightarrow>\<^bsup>M\<^esup> B)"
      using mem_function_space_rel_abs by auto
  qed
qed

lemma curry_eqpoll_rel:
  fixes \<nu>1 \<nu>2  \<kappa>
  assumes  "M(\<nu>1)" "M(\<nu>2)" "M(\<kappa>)"
  shows "\<nu>1 \<rightarrow>\<^bsup>M\<^esup> (\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>) \<approx>\<^bsup>M\<^esup> \<nu>1 \<times> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>"
  unfolding eqpoll_rel_def
proof (intro rexI, rule lam_bijective_rel,
    rule_tac [1-2] mem_function_space_rel_abs[THEN iffD2],
    rule_tac [4] lam_type, rule_tac [8] lam_type,
    rule_tac [8] mem_function_space_rel_abs[THEN iffD2],
    rule_tac [11] lam_type, simp_all add:assms)
  let ?cur="\<lambda>x. \<lambda>w\<in>\<nu>1 \<times> \<nu>2. x ` fst(w) ` snd(w)"
  fix f z
  assume "f : \<nu>1 \<rightarrow>\<^bsup>M\<^esup> (\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>)"
  moreover
  note assms
  moreover from calculation
  have "M(\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>)"
    using function_space_rel_closed by simp
  moreover from calculation
  have "M(f)" "f : \<nu>1 \<rightarrow> (\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>)"
    using function_space_rel_char by (auto dest:transM)
  moreover from calculation
  have "x \<in> \<nu>1 \<Longrightarrow> f`x : \<nu>2 \<rightarrow> \<kappa>" for x
    by (auto dest:transM intro!:mem_function_space_rel_abs[THEN iffD1])
  moreover from this
  show "(\<lambda>a\<in>\<nu>1. \<lambda>b\<in>\<nu>2. ?cur(f) ` \<langle>a, b\<rangle>) = f"
    using Pi_type[OF \<open>f \<in> \<nu>1 \<rightarrow> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>\<close>, of "\<lambda>_.\<nu>2 \<rightarrow> \<kappa>"] by simp
  moreover
  assume "z \<in> \<nu>1 \<times> \<nu>2"
  moreover from calculation
  have "f`fst(z): \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>" by simp
  ultimately
  show "f`fst(z)`snd(z) \<in> \<kappa>"
    using mem_function_space_rel_abs by (auto dest:transM)
next \<comment> \<open>one composition is the identity:\<close>
  let ?cur="\<lambda>x. \<lambda>w\<in>\<nu>1 \<times> \<nu>2. x ` fst(w) ` snd(w)"
  fix f
  assume "f : \<nu>1 \<times> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>"
  with assms
  show "?cur(\<lambda>x\<in>\<nu>1. \<lambda>xa\<in>\<nu>2. f ` \<langle>x, xa\<rangle>) = f"
    using function_space_rel_char mem_function_space_rel_abs
    by (auto dest:transM intro:fun_extension)
  fix x y
  assume "x\<in>\<nu>1" "y\<in>\<nu>2"
  with assms \<open>f : \<nu>1 \<times> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>\<close>
  show "f`\<langle>x,y\<rangle> \<in> \<kappa>"
    using function_space_rel_char mem_function_space_rel_abs
    by (auto dest:transM) \<comment> \<open>slow\<close>
next
  let ?cur="\<lambda>x. \<lambda>w\<in>\<nu>1 \<times> \<nu>2. x ` fst(w) ` snd(w)"
  note assms
  moreover from this
  show "\<forall>x[M]. M(?cur(x))"
    using  lam_replacement_fst lam_replacement_snd
      lam_replacement_apply2[THEN [5] lam_replacement_hcomp2,
        THEN [1] lam_replacement_hcomp2, where h="(`)", OF
        lam_replacement_constant] lam_replacement_apply2
    by (auto intro: lam_replacement_iff_lam_closed[THEN iffD1, rule_format])
  moreover from calculation
  show "x \<in> \<nu>1 \<rightarrow>\<^bsup>M\<^esup> (\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>) \<Longrightarrow> M(?cur(x))" for x
    by (auto dest:transM)
  moreover from assms
  show "lam_replacement(M, ?cur)"
    using lam_replacement_Lambda_apply_fst_snd by simp
  ultimately
  show "M(\<lambda>x\<in>\<nu>1 \<rightarrow>\<^bsup>M\<^esup> (\<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa>). ?cur(x))"
    using lam_replacement_iff_lam_closed
    by (auto dest:transM)
  from assms
  show "y \<in> \<nu>1 \<times> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa> \<Longrightarrow> x \<in> \<nu>1 \<Longrightarrow> M(\<lambda>xa\<in>\<nu>2. y ` \<langle>x, xa\<rangle>)" for x y
    using lam_replacement_apply_const_id
    by (rule_tac lam_replacement_iff_lam_closed[THEN iffD1, rule_format])
      (auto dest:transM)
  from assms
  show "y \<in> \<nu>1 \<times> \<nu>2 \<rightarrow>\<^bsup>M\<^esup> \<kappa> \<Longrightarrow> M(\<lambda>x\<in>\<nu>1. \<lambda>xa\<in>\<nu>2. y ` \<langle>x, xa\<rangle>)" for y
    using lam_replacement_apply2[THEN [5] lam_replacement_hcomp2,
        OF lam_replacement_constant lam_replacement_const_id]
      lam_replacement_Lambda_apply_Pair[of \<nu>2]
    by (auto dest:transM
        intro!: lam_replacement_iff_lam_closed[THEN iffD1, rule_format])
qed

lemma Pow_rel_eqpoll_rel_function_space_rel:
  fixes d X
  notes bool_of_o_def [simp]
  defines [simp]:"d(A) \<equiv> (\<lambda>x\<in>X. bool_of_o(x\<in>A))"
    \<comment> \<open>the witnessing map for the thesis:\<close>
  assumes "M(X)"
  shows "Pow\<^bsup>M\<^esup>(X) \<approx>\<^bsup>M\<^esup> X \<rightarrow>\<^bsup>M\<^esup> 2"
proof -
  from assms
  interpret M_Pi_assumptions M X "\<lambda>_. 2"
    using Pi_replacement Pi_separation lam_replacement_identity
      lam_replacement_Sigfun[THEN lam_replacement_imp_strong_replacement]
      Pi_replacement1[of _ 2] transM[of _ X] lam_replacement_constant
    by unfold_locales auto
  have "lam_replacement(M, \<lambda>x. bool_of_o(x\<in>A))" if "M(A)" for A
    using that lam_replacement_if lam_replacement_constant
      separation_in_constant by simp
  with assms
  have "lam_replacement(M, \<lambda>x. d(x))"
    using separation_in_constant[THEN [3] lam_replacement_if, of "\<lambda>_.1" "\<lambda>_.0"]
        lam_replacement_identity lam_replacement_constant lam_replacement_Lambda_if_mem
    by simp
  show ?thesis
    unfolding eqpoll_rel_def
  proof (intro rexI, rule lam_bijective_rel)
    \<comment> \<open>We give explicit mutual inverses\<close>
    fix A
    assume "A\<in>Pow\<^bsup>M\<^esup>(X)"
    moreover
    note \<open>M(X)\<close>
    moreover from calculation
    have "M(A)" by (auto dest:transM)
    moreover
    note \<open>_ \<Longrightarrow> lam_replacement(M, \<lambda>x. bool_of_o(x\<in>A))\<close>
    ultimately
    show "d(A) : X \<rightarrow>\<^bsup>M\<^esup> 2"
      using function_space_rel_char lam_replacement_iff_lam_closed[THEN iffD1]
      by (simp, rule_tac lam_type[of X "\<lambda>x. bool_of_o(x\<in>A)" "\<lambda>_. 2", simplified])
        auto
    from \<open>A\<in>Pow\<^bsup>M\<^esup>(X)\<close> \<open>M(X)\<close>
    show "{y\<in>X. d(A)`y = 1} = A"
      using Pow_rel_char by auto
  next
    fix f
    assume "f: X\<rightarrow>\<^bsup>M\<^esup> 2"
    with assms
    have "f: X\<rightarrow> 2" "M(f)" using function_space_rel_char by simp_all
    then
    show "d({y \<in> X . f ` y = 1}) = f"
      using apply_type[OF \<open>f: X\<rightarrow>2\<close>] by (force intro:fun_extension)
    from \<open>M(X)\<close> \<open>M(f)\<close>
    show "{ya \<in> X . f ` ya = 1} \<in> Pow\<^bsup>M\<^esup>(X)"
      using Pow_rel_char separation_equal_apply by auto
  next
    from assms \<open>lam_replacement(M, \<lambda>x. d(x))\<close>
      \<open>\<And>A. _ \<Longrightarrow> lam_replacement(M, \<lambda>x. bool_of_o(x\<in>A))\<close>
    show "M(\<lambda>x\<in>Pow\<^bsup>M\<^esup>(X). d(x))" "lam_replacement(M, \<lambda>x. d(x))"
      "\<forall>x[M]. M(d(x))"
      using lam_replacement_iff_lam_closed[THEN iffD1] by auto
  qed (auto simp:\<open>M(X)\<close>)
qed

lemma Pow_rel_bottom: "M(B) \<Longrightarrow> 0 \<in> Pow\<^bsup>M\<^esup>(B)"
  using Pow_rel_char by simp

lemma cantor_surj_rel:
  assumes "M(f)" "M(A)"
  shows "f \<notin> surj\<^bsup>M\<^esup>(A,Pow\<^bsup>M\<^esup>(A))"
proof
  assume "f \<in> surj\<^bsup>M\<^esup>(A,Pow\<^bsup>M\<^esup>(A))"
  with assms
  have "f \<in> surj(A,Pow\<^bsup>M\<^esup>(A))" using surj_rel_char by simp
  moreover
  note assms
  moreover from this
  have "M({x \<in> A . x \<in> f ` x})" "{x \<in> A . x \<notin> f ` x} = A - {x \<in> A . x \<in> f ` x}"
    using lam_replacement_apply[THEN [4] separation_in, of  "\<lambda>x. x"]
      lam_replacement_identity lam_replacement_constant by auto
  with \<open>M(A)\<close>
  have "{x\<in>A . x \<notin> f`x} \<in> Pow\<^bsup>M\<^esup>(A)"
    by (intro mem_Pow_rel_abs[THEN iffD2]) auto
  ultimately
  obtain d where "d\<in>A" "f`d = {x\<in>A . x \<notin> f`x}"
    unfolding surj_def by blast
  show False
  proof (cases "d \<in> f`d")
    case True
    note \<open>d \<in> f`d\<close>
    also
    note \<open>f`d = {x\<in>A . x \<notin> f`x}\<close>
    finally
    have "d \<notin> f`d" using \<open>d\<in>A\<close> by simp
    then
    show False using \<open>d \<in> f ` d\<close> by simp
  next
    case False
    with \<open>d\<in>A\<close>
    have "d \<in> {x\<in>A . x \<notin> f`x}" by simp
    also from \<open>f`d = \<dots>\<close>
    have "\<dots> = f`d" by simp
    finally
    show False using \<open>d \<notin> f`d\<close> by simp
  qed
qed

lemma cantor_inj_rel: "M(f) \<Longrightarrow> M(A) \<Longrightarrow> f \<notin> inj\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A),A)"
  using inj_rel_imp_surj_rel[OF _ Pow_rel_bottom, of f A A]
    cantor_surj_rel[of "\<lambda>x\<in>A. if x \<in> range(f) then converse(f) ` x else 0" A]
    lam_replacement_if separation_in_constant[of "range(f)"]
    lam_replacement_converse_app[THEN [5] lam_replacement_hcomp2]
    lam_replacement_identity lam_replacement_constant
    lam_replacement_iff_lam_closed by auto

end (* M_ZF_library *)

end