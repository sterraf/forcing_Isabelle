section\<open>Library of basic $\ZF$ results\label{sec:zf-lib}\<close>

theory ZF_Library_Relative
  imports
    "../Delta_System_Lemma/ZF_Library"
    "ZF-Constructible.Normal"
    Aleph_Relative
    Cardinal_AC_Relative
    "../Tools/Try0"
begin

(*
lemma Least_antitone:
  assumes
    "Ord(j)" "P(j)" "\<And>i. P(i) \<Longrightarrow> Q(i)"
  shows
    "(\<mu> i. Q(i)) \<le> (\<mu> i. P(i))"
  using assms LeastI2[of P j Q] Least_le by simp

lemma Least_set_antitone:
  "Ord(j) \<Longrightarrow> j\<in>A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<mu> i. i\<in>B) \<le> (\<mu> i. i\<in>A)"
  using subset_iff by (auto intro:Least_antitone)

lemma le_neq_imp_lt:
  "x\<le>y \<Longrightarrow> x\<noteq>y \<Longrightarrow> x<y"
  using ltD ltI[of x y] le_Ord2
  unfolding succ_def by auto

text\<open>The next two lemmas are handy when one is constructing
some object recursively. The first handles injectivity (of recursively
constructed sequences of sets), while the second is helpful for
establishing a symmetry argument.\<close>
lemma Int_eq_zero_imp_not_eq:
  assumes
    "\<And>x y. x\<in>D \<Longrightarrow> y \<in> D \<Longrightarrow> x \<noteq> y \<Longrightarrow> A(x) \<inter> A(y) = 0"
    "\<And>x. x\<in>D \<Longrightarrow> A(x) \<noteq> 0" "a\<in>D" "b\<in>D" "a\<noteq>b"
  shows
    "A(a) \<noteq> A(b)"
  using assms by fastforce

lemma lt_neq_symmetry:
  assumes
    "\<And>\<alpha> \<beta>. \<alpha> \<in> \<gamma> \<Longrightarrow> \<beta> \<in> \<gamma> \<Longrightarrow> \<alpha> < \<beta> \<Longrightarrow> Q(\<alpha>,\<beta>)"
    "\<And>\<alpha> \<beta>. Q(\<alpha>,\<beta>) \<Longrightarrow> Q(\<beta>,\<alpha>)"
    "\<alpha> \<in> \<gamma>" "\<beta> \<in> \<gamma>" "\<alpha> \<noteq> \<beta>"
    "Ord(\<gamma>)"
  shows
    "Q(\<alpha>,\<beta>)"
proof -
  from assms
  consider "\<alpha><\<beta>" | "\<beta><\<alpha>"
    using Ord_linear_lt[of \<alpha> \<beta> thesis] Ord_in_Ord[of \<gamma>]
    by auto
  then
  show ?thesis by cases (auto simp add:assms)
qed

*)

lemma (in M_cardinal_AC) cardinal_rel_succ_not_0:   "|A|\<^bsup>M\<^esup> = succ(n) \<Longrightarrow> M(A) \<Longrightarrow> M(n) \<Longrightarrow> A \<noteq> 0"
  by auto


(* "Finite_to_one(X,Y) \<equiv> {f:X\<rightarrow>Y. \<forall>y\<in>Y. Finite({x\<in>X . f`x = y})}" *)

reldb_add functional "Finite" "Finite" \<comment> \<open>wrongly done? Finite is absolute\<close>
relativize functional "Finite_to_one" "Finite_to_one_rel" external
(* reldb_add relational "Finite" "is_Finite" \<comment> \<open>don't have is_Finite yet\<close>
relationalize "Finite_to_one_rel" "is_Finite_to_one" *)

notation Finite_to_one_rel (\<open>Finite'_to'_one\<^bsup>_\<^esup>'(_,_')\<close>)

abbreviation
  Finite_to_one_r_set :: "[i,i,i] \<Rightarrow> i" (\<open>Finite'_to'_one\<^bsup>_\<^esup>'(_,_')\<close>) where
  "Finite_to_one\<^bsup>M\<^esup>(X,Y) \<equiv> Finite_to_one_rel(##M,X,Y)"

locale M_library =  M_cardinal_AC + M_aleph +
  assumes
  Pair_diff_replacement: "M(X) \<Longrightarrow> strong_replacement(M, \<lambda>A y. y = \<langle>A, A - X\<rangle>)"
  and
  diff_replacement: "M(X) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = x - X)"
  and
  tag_replacement: "M(b) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, b\<rangle>)"
  and
  ifx_replacement: "M(f) \<Longrightarrow> M(b) \<Longrightarrow> 
    strong_replacement(M, \<lambda>x y. y = \<langle>x, if x \<in> range(f) then converse(f) ` x else b\<rangle>)"
begin

lemma Finite_Collect_imp: "Finite({x\<in>X . Q(x)}) \<Longrightarrow> Finite({x\<in>X . M(x) \<and> Q(x)})"
  (is "Finite(?A) \<Longrightarrow> Finite(?B)")
  using subset_Finite[of ?B ?A] by auto 

lemma Finite_to_one_relI[intro]:
  assumes "f:X\<rightarrow>\<^bsup>M\<^esup>Y" "\<And>y. y\<in>Y \<Longrightarrow> Finite({x\<in>X . f`x = y})"
    and types:"M(f)" "M(X)" "M(Y)"
  shows "f \<in> Finite_to_one\<^bsup>M\<^esup>(X,Y)"
  using assms Finite_Collect_imp unfolding Finite_to_one_rel_def
  by (simp)

lemma Finite_to_one_relI'[intro]:
  assumes "f:X\<rightarrow>\<^bsup>M\<^esup>Y" "\<And>y. y\<in>Y \<Longrightarrow> Finite({x\<in>X . M(x) \<and> f`x = y})"
    and types:"M(f)" "M(X)" "M(Y)"
  shows "f \<in> Finite_to_one\<^bsup>M\<^esup>(X,Y)"
  using assms unfolding Finite_to_one_rel_def
  by (simp)

lemma Finite_to_one_relD[dest]:
  "f \<in> Finite_to_one\<^bsup>M\<^esup>(X,Y) \<Longrightarrow>f:X\<rightarrow>\<^bsup>M\<^esup>Y"
  "f \<in> Finite_to_one\<^bsup>M\<^esup>(X,Y) \<Longrightarrow> y\<in>Y \<Longrightarrow> M(Y) \<Longrightarrow> Finite({x\<in>X . M(x) \<and> f`x = y})"
  unfolding Finite_to_one_rel_def by simp_all

lemma Diff_bij_rel:
  assumes "\<forall>A\<in>F. X \<subseteq> A" 
    and types: "M(F)" "M(X)" shows "(\<lambda>A\<in>F. A-X) \<in> bij\<^bsup>M\<^esup>(F, {A-X. A\<in>F})"
  using assms  def_inj_rel def_surj_rel unfolding bij_rel_def
  apply (auto)
   apply (subgoal_tac "M(\<lambda>A\<in>F. A - X)" "M({A - X . A \<in> F})")
     apply (auto simp add:mem_function_space_rel_abs)
      apply (rule_tac lam_type, auto)
     prefer 4
     apply (subgoal_tac "M(\<lambda>A\<in>F. A - X)" "M({A - X . A \<in> F})")
       apply(tactic \<open>distinct_subgoals_tac\<close>)
     apply (auto simp add:mem_function_space_rel_abs)
     apply (rule_tac lam_type, auto) prefer 3
    apply (subst subset_Diff_Un[of X])
     apply auto
proof -
  from types 
  show "M({A - X . A \<in> F})"
    using diff_replacement
    by (rule_tac RepFun_closed) (auto dest:transM[of _ F])
  from types
  show "M(\<lambda>A\<in>F. A - X)"
    using Pair_diff_replacement
    by (rule_tac lam_closed, auto dest:transM)
qed

lemma function_space_rel_nonempty:
  assumes "b\<in>B"  and types: "M(B)" "M(A)"
  shows "(\<lambda>x\<in>A. b) : A \<rightarrow>\<^bsup>M\<^esup> B"
proof -
  note assms
  moreover from this
  have "M(\<lambda>x\<in>A. b)" 
    using tag_replacement by (rule_tac lam_closed, auto dest:transM)
  ultimately
  show ?thesis
    by (simp add:mem_function_space_rel_abs)
qed

lemma mem_function_space_rel:
  assumes "f \<in> A \<rightarrow>\<^bsup>M\<^esup> y" "M(A)" "M(y)"
  shows  "f \<in> A \<rightarrow> y"
  using assms function_space_rel_char by simp

lemmas range_fun_rel_subset_codomain = range_fun_subset_codomain[OF mem_function_space_rel]

end (* M_library *)

context M_Pi_assumptions
begin

lemma mem_Pi_rel: "f \<in> Pi\<^bsup>M\<^esup>(A,B) \<Longrightarrow> f \<in> Pi(A, B)"
  using trans_closed mem_Pi_rel_abs
  by force

lemmas Pi_rel_rangeD = Pi_rangeD[OF mem_Pi_rel]

lemmas rel_apply_Pair = apply_Pair[OF mem_Pi_rel]

lemmas rel_apply_rangeI = apply_rangeI[OF mem_Pi_rel]

lemmas Pi_rel_range_eq = Pi_range_eq[OF mem_Pi_rel]

lemmas Pi_rel_vimage_subset = Pi_vimage_subset[OF mem_Pi_rel]

end (* M_Pi_assumptions *)

context M_library
begin

lemma mem_bij_rel: "\<lbrakk>f \<in> bij\<^bsup>M\<^esup>(A,B); M(A); M(B)\<rbrakk> \<Longrightarrow> f\<in>bij(A,B)"
  using bij_rel_char by simp

lemma mem_inj_rel: "\<lbrakk>f \<in> inj\<^bsup>M\<^esup>(A,B); M(A); M(B)\<rbrakk> \<Longrightarrow> f\<in>inj(A,B)"
  using inj_rel_char by simp

lemma mem_surj_rel: "\<lbrakk>f \<in> surj\<^bsup>M\<^esup>(A,B); M(A); M(B)\<rbrakk> \<Longrightarrow> f\<in>surj(A,B)"
  using surj_rel_char by simp

lemmas rel_apply_in_range = apply_in_range[OF _ _ mem_function_space_rel]

lemmas rel_range_eq_image = ZF_Library.range_eq_image[OF mem_function_space_rel]

lemmas rel_Image_sub_codomain = Image_sub_codomain[OF mem_function_space_rel]

lemma rel_inj_to_Image: "\<lbrakk>f:A\<rightarrow>\<^bsup>M\<^esup>B; f \<in> inj\<^bsup>M\<^esup>(A,B); M(A); M(B)\<rbrakk> \<Longrightarrow> f \<in> inj\<^bsup>M\<^esup>(A,f``A)"
  using inj_to_Image[OF mem_function_space_rel mem_inj_rel]
    transM[OF _ function_space_rel_closed] by simp

lemma inj_rel_imp_surj_rel:
  fixes f b
  defines [simp]: "ifx(x) \<equiv> if x\<in>range(f) then converse(f)`x else b"
  assumes "f \<in> inj\<^bsup>M\<^esup>(B,A)" "b\<in>B" and types: "M(f)" "M(B)" "M(A)"
  shows "(\<lambda>x\<in>A. ifx(x)) \<in> surj\<^bsup>M\<^esup>(A,B)"
proof -
  from types and \<open>b\<in>B\<close>
  have "M(\<lambda>x\<in>A. ifx(x))"
    using ifx_replacement by (rule_tac lam_closed) (auto dest:transM)
  with assms(2-)
  show ?thesis
    using inj_imp_surj mem_surj_abs by simp
qed

lemma function_space_rel_disjoint_Un:
  assumes "f \<in> A\<rightarrow>\<^bsup>M\<^esup>B" "g \<in> C\<rightarrow>\<^bsup>M\<^esup>D"  "A \<inter> C = 0"
    and types:"M(A)" "M(B)" "M(C)" "M(D)"
  shows "f \<union> g \<in> (A \<union> C)\<rightarrow>\<^bsup>M\<^esup> (B \<union> D)"
  using assms fun_Pi_disjoint_Un[OF mem_function_space_rel
      mem_function_space_rel, OF assms(1) _ _ assms(2)]
    function_space_rel_char by auto

lemma restrict_eq_imp_Un_into_function_space_rel:
  assumes "f \<in> A\<rightarrow>\<^bsup>M\<^esup>B" "g \<in> C\<rightarrow>\<^bsup>M\<^esup>D"  "restrict(f, A \<inter> C) = restrict(g, A \<inter> C)"
    and types:"M(A)" "M(B)" "M(C)" "M(D)"
  shows "f \<union> g \<in> (A \<union> C)\<rightarrow>\<^bsup>M\<^esup> (B \<union> D)"
  using assms restrict_eq_imp_Un_into_Pi[OF mem_function_space_rel
      mem_function_space_rel, OF assms(1) _ _ assms(2)]
    function_space_rel_char by auto

lemma lepoll_relD[dest]: "A \<lesssim>\<^bsup>M\<^esup> B \<Longrightarrow> \<exists>f[M]. f \<in> inj\<^bsup>M\<^esup>(A, B)"
  unfolding lepoll_rel_def .

\<comment> \<open>Should the assumptions be on \<^term>\<open>f\<close> or on \<^term>\<open>A\<close> and \<^term>\<open>B\<close>?
    Should BOTH be intro rules?\<close>
lemma lepoll_relI[intro]: "f \<in> inj\<^bsup>M\<^esup>(A, B) \<Longrightarrow> M(f) \<Longrightarrow> A \<lesssim>\<^bsup>M\<^esup> B"
  unfolding lepoll_rel_def by blast

lemma eqpollD[dest]: "A \<approx>\<^bsup>M\<^esup> B \<Longrightarrow> \<exists>f[M]. f \<in> bij\<^bsup>M\<^esup>(A, B)"
  unfolding eqpoll_rel_def .

\<comment> \<open>Same as @{thm lepoll_relI}}\<close>
lemma bij_rel_imp_eqpoll_rel[intro]: "f \<in> bij\<^bsup>M\<^esup>(A,B) \<Longrightarrow> M(f) \<Longrightarrow> A \<approx>\<^bsup>M\<^esup> B"
  unfolding eqpoll_rel_def by blast

lemma restrict_bij_rel:\<comment> \<open>Unused\<close>
  assumes "f \<in> inj\<^bsup>M\<^esup>(A,B)"  "C\<subseteq>A"
    and types:"M(A)" "M(B)" "M(C)"
  shows "restrict(f,C)\<in> bij\<^bsup>M\<^esup>(C, f``C)"
  using assms restrict_bij inj_rel_char bij_rel_char by auto

lemma range_of_subset_eqpoll_rel:
  assumes "f \<in> inj\<^bsup>M\<^esup>(X,Y)" "S \<subseteq> X"
    and types:"M(X)" "M(Y)" "M(S)"
  shows "S \<approx>\<^bsup>M\<^esup> f `` S"
  using assms restrict_bij bij_rel_char
    trans_inj_rel_closed[OF \<open>f \<in> inj\<^bsup>M\<^esup>(X,Y)\<close>]
  unfolding eqpoll_rel_def
  by (rule_tac x="restrict(f,S)" in rexI) auto

text\<open>I thank Miguel Pagano for this proof.\<close>
lemma function_space_eqpoll_cong: (* FIXME: not ported yet *)
  assumes
    "A \<approx> A'" "B \<approx> B'"
  shows
    "A \<rightarrow> B \<approx> A' \<rightarrow> B'"
proof -
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

lemma curry_eqpoll: (* FIXME: not ported yet *)
  fixes d \<nu>1 \<nu>2  \<kappa>
  shows "\<nu>1 \<rightarrow> \<nu>2 \<rightarrow> \<kappa> \<approx> \<nu>1 \<times> \<nu>2 \<rightarrow> \<kappa>"
  unfolding eqpoll_def
proof (intro exI, rule lam_bijective,
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

end (* M_library *)

relativize functional "cexp" "cexp_rel" external
(*
relationalize "cexp" "is_cexp"
\<comment> \<open>fails with "Constant ZF_Base.Pi is not present in the db"\<close>
*)

abbreviation
  cexp_r :: "[i,i,i\<Rightarrow>o] \<Rightarrow> i"  (\<open>'(_\<^bsup>\<up>_\<^esup>')\<^bsup>_\<^esup>\<close>) where
  "cexp_r(x,y,M) \<equiv> cexp_rel(M,x,y)"

abbreviation
  cexp_r_set :: "[i,i,i] \<Rightarrow> i"  (\<open>'(_\<^bsup>\<up>_\<^esup>')\<^bsup>_\<^esup>\<close>) where
  "cexp_r_set(x,y,M) \<equiv> cexp_rel(##M,x,y)"

context M_library
begin

lemma Card_cexp: "M(\<kappa>) \<Longrightarrow> M(\<nu>) \<Longrightarrow> Card\<^bsup>M\<^esup>((\<kappa>\<^bsup>\<up>\<nu>\<^esup>)\<^bsup>M\<^esup>)"
  unfolding cexp_rel_def by simp

\<comment> \<open>Restoring congruence rule, but NOTE: beware\<close>
declare conj_cong[cong]

lemma eq_csucc_rel_ord:
  "Ord(i) \<Longrightarrow> M(i) \<Longrightarrow> (i\<^sup>+)\<^bsup>M\<^esup> = (|i|\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup>"
  using Card_rel_lt_iff Least_cong unfolding csucc_rel_def by auto

text\<open>I thank Miguel Pagano for this proof.\<close>
lemma lesspoll_csucc: (* FIXME: not ported yet *)
  assumes "Ord(\<kappa>)"
  shows "d \<prec> \<kappa>\<^sup>+ \<longleftrightarrow> d \<lesssim> \<kappa>"
proof
  assume "d \<prec> \<kappa>\<^sup>+"
  moreover
  note Card_is_Ord \<open>Ord(\<kappa>)\<close>
  moreover from calculation
  have "\<kappa> < \<kappa>\<^sup>+" "Card(\<kappa>\<^sup>+)"
    using Ord_cardinal_eqpoll csucc_basic by simp_all
  moreover from calculation
  have "d \<prec> |\<kappa>|\<^sup>+" "Card(|\<kappa>|)" "d \<approx> |d|"
    using eq_csucc_ord[of \<kappa>] lesspoll_imp_eqpoll eqpoll_sym by simp_all
  moreover from calculation
  have "|d| < |\<kappa>|\<^sup>+"
    using lesspoll_cardinal_lt csucc_basic by simp
  moreover from calculation
  have "|d| \<lesssim> |\<kappa>|"
    using Card_lt_csucc_iff le_imp_lepoll by simp
  moreover from calculation
  have "|d| \<lesssim> \<kappa>"
    using lepoll_eq_trans Ord_cardinal_eqpoll by simp
  ultimately
  show "d \<lesssim> \<kappa>"
    using eq_lepoll_trans by simp
next
  from \<open>Ord(\<kappa>)\<close>
  have "\<kappa> < \<kappa>\<^sup>+" "Card(\<kappa>\<^sup>+)"
    using csucc_basic by simp_all
  moreover
  assume "d \<lesssim> \<kappa>"
  ultimately
  have "d \<lesssim> \<kappa>\<^sup>+"
    using le_imp_lepoll leI lepoll_trans by simp
  moreover
  from \<open>d \<lesssim> \<kappa>\<close> \<open>Ord(\<kappa>)\<close>
  have "\<kappa>\<^sup>+ \<lesssim> \<kappa>" if "d \<approx> \<kappa>\<^sup>+"
    using eqpoll_sym[OF that] eq_lepoll_trans[OF _ \<open>d\<lesssim>\<kappa>\<close>] by simp
  moreover from calculation \<open>Card(_)\<close>
  have "\<not> d \<approx> \<kappa>\<^sup>+"
    using lesspoll_irrefl lesspoll_trans1 lt_Card_imp_lesspoll[OF _ \<open>\<kappa> <_\<close>]
    by auto
  ultimately
  show "d \<prec> \<kappa>\<^sup>+"
    unfolding lesspoll_def by simp
qed

lemma Infinite_imp_nats_lepoll: (* FIXME: not ported yet *)
  assumes "Infinite(X)" "n \<in> \<omega>"
  shows "n \<lesssim> X"
  using \<open>n \<in> \<omega>\<close>
proof (induct)
  case 0
  then
  show ?case using empty_lepollI by simp
next
  case (succ x)
  show ?case
  proof -
    from \<open>Infinite(X)\<close> and \<open>x \<in> \<omega>\<close>
    have "\<not> (x \<approx> X)"
      using eqpoll_sym unfolding Finite_def by auto
    with \<open>x \<lesssim> X\<close>
    obtain f where "f \<in> inj(x,X)" "f \<notin> surj(x,X)"
      unfolding bij_def eqpoll_def by auto
    moreover from this
    obtain b where "b \<in> X" "\<forall>a\<in>x. f`a \<noteq> b"
      using inj_is_fun unfolding surj_def by auto
    ultimately
    have "f \<in> inj(x,X-{b})"
      unfolding inj_def by (auto intro:Pi_type)
    then
    have "cons(\<langle>x, b\<rangle>, f) \<in> inj(succ(x), cons(b, X - {b}))"
      using inj_extend[of f x "X-{b}" x b] unfolding succ_def
      by (auto dest:mem_irrefl)
    moreover from \<open>b\<in>X\<close>
    have "cons(b, X - {b}) = X" by auto
    ultimately
    show "succ(x) \<lesssim> X" by auto
  qed
qed

(* \<comment> \<open>Unused?\<close>
lemma zero_lesspoll: assumes "0<\<kappa>" shows "0 \<prec> \<kappa>"
  using assms eqpoll_0_iff[THEN iffD1, of \<kappa>] eqpoll_sym
  unfolding lesspoll_def lepoll_def
  by (auto simp add:inj_def)
*)

lemma lepoll_rel_imp_lepoll: "A \<lesssim>\<^bsup>M\<^esup> B \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> A \<lesssim> B"
  unfolding lepoll_rel_def by auto

lemma lepoll_rel_nat_imp_Infinite: "\<omega> \<lesssim>\<^bsup>M\<^esup> X \<Longrightarrow> M(X) \<Longrightarrow> Infinite(X)"
  using  lepoll_nat_imp_Infinite lepoll_rel_imp_lepoll by simp

lemma InfCard_rel_imp_Infinite: "InfCard\<^bsup>M\<^esup>(\<kappa>) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> Infinite(\<kappa>)"
  using le_imp_lepoll_rel[THEN lepoll_rel_nat_imp_Infinite, of \<kappa>]
  unfolding InfCard_rel_def by simp

lemma lt_surj_rel_empty_imp_Card_rel:
  assumes "Ord(\<kappa>)" "\<And>\<alpha>. \<alpha> < \<kappa> \<Longrightarrow> surj\<^bsup>M\<^esup>(\<alpha>,\<kappa>) = 0"
    and types:"M(\<kappa>)"
  shows "Card\<^bsup>M\<^esup>(\<kappa>)"
proof -
  {
    define min where "min\<equiv>\<mu> x. \<exists>f[M]. f \<in> bij\<^bsup>M\<^esup>(x,\<kappa>)"
    moreover
    note \<open>Ord(\<kappa>)\<close> \<open>M(\<kappa>)\<close>
    moreover
    assume "|\<kappa>|\<^bsup>M\<^esup> < \<kappa>"
    moreover from calculation 
    have "\<exists>f. f \<in> bij\<^bsup>M\<^esup>(min,\<kappa>)"
      using LeastI[of "\<lambda>i. i \<approx>\<^bsup>M\<^esup> \<kappa>" \<kappa>, OF eqpoll_rel_refl]
      unfolding Card_rel_def cardinal_rel_def eqpoll_rel_def
      by (auto)
    moreover from calculation
    have "min < \<kappa>"
      using LeastI[of "\<lambda>i. i \<approx>\<^bsup>M\<^esup> \<kappa>" \<kappa>, OF eqpoll_rel_refl]
        Least_le[of "\<lambda>i. i \<approx>\<^bsup>M\<^esup> \<kappa>" "|\<kappa>|\<^bsup>M\<^esup>", OF Ord_cardinal_rel_eqpoll_rel]
        lt_trans1[of min "\<mu> i. M(i) \<and> (\<exists>f[M]. f \<in> bij\<^bsup>M\<^esup>(i, \<kappa>))" \<kappa>]
      unfolding Card_rel_def cardinal_rel_def eqpoll_rel_def
      by (simp)
    moreover
    note \<open>min < \<kappa> \<Longrightarrow> surj\<^bsup>M\<^esup>(min,\<kappa>) = 0\<close>
    ultimately
    have "False"
      unfolding bij_rel_def by simp
  }
  with assms
  show ?thesis
    using Ord_cardinal_rel_le[of \<kappa>] not_lt_imp_le[of "|\<kappa>|\<^bsup>M\<^esup>" \<kappa>] le_anti_sym
    unfolding Card_rel_def by auto
qed


subsection\<open>Morphisms of binary relations\<close>

text\<open>The main case of interest is in the case of partial orders.\<close>

lemma mono_map_mono:
  assumes
    "f \<in> mono_map(A,r,B,s)" "B \<subseteq> C"
  shows
    "f \<in> mono_map(A,r,C,s)"
  unfolding mono_map_def
proof (intro CollectI ballI impI)
  from \<open>f \<in> mono_map(A,_,B,_)\<close>
  have "f: A \<rightarrow> B"
    using mono_map_is_fun by simp
  with \<open>B\<subseteq>C\<close>
  show "f: A \<rightarrow> C"
    using fun_weaken_type by simp
  fix x y
  assume "x\<in>A" "y\<in>A" "\<langle>x,y\<rangle> \<in> r"
  moreover from this and \<open>f: A \<rightarrow> B\<close>
  have "f`x \<in> B" "f`y \<in> B"
    using apply_type by simp_all
  moreover
  note \<open>f \<in> mono_map(_,r,_,s)\<close>
  ultimately
  show "\<langle>f ` x, f ` y\<rangle> \<in> s"
    unfolding mono_map_def by blast
qed

lemma ordertype_zero_imp_zero: "ordertype(A,r) = 0 \<Longrightarrow> A = 0"
  using ordermap_type[of A r]
  by (cases "A=0") auto

lemma mono_map_increasing:
  "j\<in>mono_map(A,r,B,s) \<Longrightarrow> a\<in>A \<Longrightarrow> c\<in>A \<Longrightarrow> \<langle>a,c\<rangle>\<in>r \<Longrightarrow> \<langle>j`a,j`c\<rangle>\<in>s"
  unfolding mono_map_def by simp

lemma linear_mono_map_reflects:
  assumes
    "linear(\<alpha>,r)" "trans[\<beta>](s)" "irrefl(\<beta>,s)" "f\<in>mono_map(\<alpha>,r,\<beta>,s)"
    "x\<in>\<alpha>" "y\<in>\<alpha>" "\<langle>f`x,f`y\<rangle>\<in>s"
  shows
    "\<langle>x,y\<rangle>\<in>r"
proof -
  from \<open>f\<in>mono_map(_,_,_,_)\<close>
  have preserves:"x\<in>\<alpha> \<Longrightarrow> y\<in>\<alpha> \<Longrightarrow> \<langle>x,y\<rangle>\<in>r \<Longrightarrow> \<langle>f`x,f`y\<rangle>\<in>s" for x y
    unfolding mono_map_def by blast
  {
    assume "\<langle>x, y\<rangle> \<notin> r" "x\<in>\<alpha>" "y\<in>\<alpha>"
    moreover
    note \<open>\<langle>f`x,f`y\<rangle>\<in>s\<close> and \<open>linear(\<alpha>,r)\<close>
    moreover from calculation
    have "y = x \<or> \<langle>y,x\<rangle>\<in>r"
      unfolding linear_def by blast
    moreover
    note preserves [of y x]
    ultimately
    have "y = x \<or> \<langle>f`y, f`x\<rangle>\<in> s" by blast
    moreover from \<open>f\<in>mono_map(_,_,\<beta>,_)\<close> \<open>x\<in>\<alpha>\<close> \<open>y\<in>\<alpha>\<close>
    have "f`x\<in>\<beta>" "f`y\<in>\<beta>"
      using apply_type[OF mono_map_is_fun] by simp_all
    moreover
    note \<open>\<langle>f`x,f`y\<rangle>\<in>s\<close>  \<open>trans[\<beta>](s)\<close> \<open>irrefl(\<beta>,s)\<close>
    ultimately
    have "False"
      using trans_onD[of \<beta> s "f`x" "f`y" "f`x"] irreflE by blast
  }
  with assms
  show "\<langle>x,y\<rangle>\<in>r" by blast
qed

lemma irrefl_Memrel: "irrefl(x, Memrel(x))"
  unfolding irrefl_def using mem_irrefl by auto

lemmas Memrel_mono_map_reflects = linear_mono_map_reflects
  [OF well_ord_is_linear[OF well_ord_Memrel] well_ord_is_trans_on[OF well_ord_Memrel]
    irrefl_Memrel]

\<comment> \<open>Same proof as Paulson's @{thm mono_map_is_inj}\<close>
lemma mono_map_is_inj':
  "\<lbrakk> linear(A,r);  irrefl(B,s);  f \<in> mono_map(A,r,B,s) \<rbrakk> \<Longrightarrow> f \<in> inj(A,B)"
  unfolding irrefl_def mono_map_def inj_def using linearE
  by (clarify, rename_tac x w)
    (erule_tac x=w and y=x in linearE, assumption+, (force intro: apply_type)+)

lemma mono_map_imp_ord_iso_image:
  assumes
    "linear(\<alpha>,r)" "trans[\<beta>](s)"  "irrefl(\<beta>,s)" "f\<in>mono_map(\<alpha>,r,\<beta>,s)"
  shows
    "f \<in> ord_iso(\<alpha>,r,f``\<alpha>,s)"
  unfolding ord_iso_def
proof (intro CollectI ballI iffI)
  \<comment> \<open>Enough to show it's bijective and preserves both ways\<close>
  from assms
  have "f \<in> inj(\<alpha>,\<beta>)"
    using mono_map_is_inj' by blast
  moreover from \<open>f \<in> mono_map(_,_,_,_)\<close>
  have "f \<in> surj(\<alpha>, f``\<alpha>)"
    unfolding mono_map_def using surj_image by auto
  ultimately
  show "f \<in> bij(\<alpha>, f``\<alpha>)"
    unfolding bij_def using inj_is_fun inj_to_Image by simp
  from \<open>f\<in>mono_map(_,_,_,_)\<close>
  show "x\<in>\<alpha> \<Longrightarrow> y\<in>\<alpha> \<Longrightarrow> \<langle>x,y\<rangle>\<in>r \<Longrightarrow> \<langle>f`x,f`y\<rangle>\<in>s" for x y
    unfolding mono_map_def by blast
  with assms
  show "\<langle>f`x,f`y\<rangle>\<in>s \<Longrightarrow> x\<in>\<alpha> \<Longrightarrow> y\<in>\<alpha> \<Longrightarrow> \<langle>x,y\<rangle>\<in>r" for x y
    using linear_mono_map_reflects
    by blast
qed

lemma mono_map_imp_ord_iso_Memrel:
  assumes
    "Ord(\<alpha>)" "Ord(\<beta>)" "f:\<alpha> \<rightarrow>\<^sub>< \<beta>"
  shows
    "f \<in> ord_iso(\<alpha>,Memrel(\<alpha>),f``\<alpha>,Memrel(\<beta>))"
  using assms mono_map_imp_ord_iso_image[OF well_ord_is_linear[OF well_ord_Memrel]
      well_ord_is_trans_on[OF well_ord_Memrel] irrefl_Memrel] by blast

lemma mono_map_ordertype_image':
  assumes
    "X\<subseteq>\<alpha>" "Ord(\<alpha>)" "Ord(\<beta>)" "f \<in> mono_map(X,Memrel(\<alpha>),\<beta>,Memrel(\<beta>))"
  shows
    "ordertype(f``X,Memrel(\<beta>)) = ordertype(X,Memrel(\<alpha>))"
  using assms mono_map_is_fun[of f X _ \<beta>]  ordertype_eq
    mono_map_imp_ord_iso_image[OF well_ord_is_linear[OF well_ord_Memrel, THEN linear_subset]
      well_ord_is_trans_on[OF well_ord_Memrel] irrefl_Memrel, of \<alpha> X \<beta> f]
    well_ord_subset[OF well_ord_Memrel]  Image_sub_codomain[of f X \<beta> X] by auto

lemma mono_map_ordertype_image:
  assumes
    "Ord(\<alpha>)" "Ord(\<beta>)" "f:\<alpha> \<rightarrow>\<^sub>< \<beta>"
  shows
    "ordertype(f``\<alpha>,Memrel(\<beta>)) = \<alpha>"
  using assms mono_map_is_fun ordertype_Memrel ordertype_eq[of f \<alpha> "Memrel(\<alpha>)"]
    mono_map_imp_ord_iso_Memrel well_ord_subset[OF well_ord_Memrel] Image_sub_codomain[of _ \<alpha>]
  by auto

lemma Image_subset_Ord_imp_lt:
  assumes
    "Ord(\<alpha>)" "h``A \<subseteq> \<alpha>" "x\<in>domain(h)" "x\<in>A" "function(h)"
  shows
    "h`x < \<alpha>"
  using assms
  unfolding domain_def using imageI ltI function_apply_equality by auto

lemma ordermap_le_arg:
  assumes
    "X\<subseteq>\<beta>" "x\<in>X" "Ord(\<beta>)"
  shows
    "x\<in>X \<Longrightarrow> ordermap(X,Memrel(\<beta>))`x\<le>x"
proof (induct rule:Ord_induct[OF subsetD, OF assms])
  case (1 x)
  have "wf[X](Memrel(\<beta>))"
    using wf_imp_wf_on[OF wf_Memrel] .
  with 1
  have "ordermap(X,Memrel(\<beta>))`x = {ordermap(X,Memrel(\<beta>))`y . y\<in>{y\<in>X . y\<in>x \<and> y\<in>\<beta>}}"
    using ordermap_unfold Ord_trans[of _ x \<beta>] by auto
  also from assms
  have "... = {ordermap(X,Memrel(\<beta>))`y . y\<in>{y\<in>X . y\<in>x}}"
    using Ord_trans[of _ x \<beta>] Ord_in_Ord by blast
  finally
  have ordm:"ordermap(X,Memrel(\<beta>))`x = {ordermap(X,Memrel(\<beta>))`y . y\<in>{y\<in>X . y\<in>x}}" .
  from 1
  have "y\<in>x \<Longrightarrow> y\<in>X \<Longrightarrow> ordermap(X,Memrel(\<beta>))`y \<le> y" for y by simp
  with \<open>x\<in>\<beta>\<close> and \<open>Ord(\<beta>)\<close>
  have "y\<in>x \<Longrightarrow> y\<in>X \<Longrightarrow> ordermap(X,Memrel(\<beta>))`y \<in> x" for y
    using ltI[OF _ Ord_in_Ord[of \<beta> x]] lt_trans1 ltD by blast
  with ordm
  have "ordermap(X,Memrel(\<beta>))`x \<subseteq> x" by auto
  with \<open>x\<in>X\<close> assms
  show ?case
    using subset_imp_le Ord_in_Ord[of \<beta> x] Ord_ordermap
      well_ord_subset[OF well_ord_Memrel, of \<beta>] by force
qed

lemma subset_imp_ordertype_le:
  assumes
    "X\<subseteq>\<beta>" "Ord(\<beta>)"
  shows
    "ordertype(X,Memrel(\<beta>))\<le>\<beta>"
proof -
  {
    fix x
    assume "x\<in>X"
    with assms
    have "ordermap(X,Memrel(\<beta>))`x \<le> x"
      using ordermap_le_arg by simp
    with \<open>x\<in>X\<close> and assms
    have "ordermap(X,Memrel(\<beta>))`x \<in> \<beta>" (is "?y \<in> _")
      using ltD[of ?y "succ(x)"] Ord_trans[of  ?y x \<beta>] by auto
  }
  then
  have "ordertype(X, Memrel(\<beta>)) \<subseteq> \<beta>"
    using ordertype_unfold[of X] by auto
  with assms
  show ?thesis
    using subset_imp_le Ord_ordertype[OF well_ord_subset, OF well_ord_Memrel] by simp
qed

lemma mono_map_imp_le:
  assumes
    "f\<in>mono_map(\<alpha>, Memrel(\<alpha>),\<beta>, Memrel(\<beta>))" "Ord(\<alpha>)" "Ord(\<beta>)"
  shows
    "\<alpha>\<le>\<beta>"
proof -
  from assms
  have "f \<in> \<langle>\<alpha>, Memrel(\<alpha>)\<rangle> \<cong> \<langle>f``\<alpha>, Memrel(\<beta>)\<rangle>"
    using mono_map_imp_ord_iso_Memrel by simp
  then
  have "converse(f) \<in> \<langle>f``\<alpha>, Memrel(\<beta>)\<rangle> \<cong> \<langle>\<alpha>, Memrel(\<alpha>)\<rangle>"
    using ord_iso_sym by simp
  with \<open>Ord(\<alpha>)\<close>
  have "\<alpha> = ordertype(f``\<alpha>,Memrel(\<beta>))"
    using ordertype_eq well_ord_Memrel ordertype_Memrel by auto
  also from assms
  have "ordertype(f``\<alpha>,Memrel(\<beta>)) \<le> \<beta>"
    using subset_imp_ordertype_le mono_map_is_fun[of f] Image_sub_codomain[of f] by force
  finally
  show ?thesis .
qed

\<comment> \<open>\<^term>\<open>Ord(A) \<Longrightarrow> f \<in> mono_map(A, Memrel(A), B, Memrel(Aa)) \<Longrightarrow> f \<in> inj(A, B)\<close>\<close> 
lemmas Memrel_mono_map_is_inj = mono_map_is_inj
  [OF well_ord_is_linear[OF well_ord_Memrel]
    wf_imp_wf_on[OF wf_Memrel]]

lemma mono_mapI:
  assumes "f: A\<rightarrow>B" "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> \<langle>x,y\<rangle>\<in>r \<Longrightarrow> \<langle>f`x,f`y\<rangle>\<in>s"
  shows   "f \<in> mono_map(A,r,B,s)"
  unfolding mono_map_def using assms by simp

lemmas mono_mapD = mono_map_is_fun mono_map_increasing

bundle mono_map_rules =  mono_mapI[intro!] mono_map_is_fun[dest] mono_mapD[dest]

lemma nats_le_InfCard:
  assumes "n \<in> \<omega>" "InfCard(\<kappa>)"
  shows "n \<le> \<kappa>"
  using assms Ord_is_Transset
    le_trans[of n \<omega> \<kappa>, OF le_subset_iff[THEN iffD2]]
  unfolding InfCard_def Transset_def by simp

lemma nat_into_InfCard:
  assumes "n \<in> \<omega>" "InfCard(\<kappa>)"
  shows "n \<in> \<kappa>"
  using assms  le_imp_subset[of \<omega> \<kappa>]
  unfolding InfCard_def by auto


subsection\<open>Alephs are infinite cardinals\<close>\<comment> \<open>This requires porting \<^term>\<open>Aleph\<close>\<close>

lemma Aleph_zero_eq_nat: "\<aleph>\<^bsub>0\<^esub> = \<omega>"
  unfolding Aleph_def by simp

lemma InfCard_Aleph:
  notes Aleph_zero_eq_nat[simp]
  assumes "Ord(\<alpha>)"
  shows "InfCard(\<aleph>\<^bsub>\<alpha>\<^esub>)"
proof -
  have "\<not> (\<aleph>\<^bsub>\<alpha>\<^esub> \<in> \<omega>)"
  proof (cases "\<alpha>=0")
    case True
    then show ?thesis using mem_irrefl by auto
  next
    case False
    with \<open>Ord(\<alpha>)\<close>
    have "\<omega> \<in> \<aleph>\<^bsub>\<alpha>\<^esub>" using Ord_0_lt[of \<alpha>] ltD  by (auto dest:Aleph_increasing)
    then show ?thesis using foundation by blast
  qed
  with \<open>Ord(\<alpha>)\<close>
  have "\<not> (|\<aleph>\<^bsub>\<alpha>\<^esub>| \<in> \<omega>)"
    using Card_cardinal_eq by auto
  then
  have "\<not> Finite(\<aleph>\<^bsub>\<alpha>\<^esub>)" by auto
  with \<open>Ord(\<alpha>)\<close>
  show ?thesis
    using Inf_Card_is_InfCard by simp
qed

lemmas Limit_Aleph = InfCard_Aleph[THEN InfCard_is_Limit]

(* Already ported:  *)
bundle Ord_dests = Limit_is_Ord[dest] Card_rel_is_Ord[dest]
bundle Aleph_rel_dests = Aleph_rel_cont[dest]
bundle Aleph_rel_intros = Aleph_rel_increasing[intro!]
bundle Aleph_rel_mem_dests = Aleph_rel_increasing[OF ltI, THEN ltD, dest]


end (* M_library *)

end