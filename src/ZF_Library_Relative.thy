section\<open>Library of basic $\ZF$ results\label{sec:zf-lib}\<close>

theory ZF_Library_Relative
  imports
    "../Delta_System_Lemma/ZF_Library"
    "ZF-Constructible.Normal"
    Aleph_Relative\<comment> \<open>must be before Cardinal_AC_Relative!\<close>
    Cardinal_AC_Relative
    FiniteFun_Relative
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

locale M_library =  M_cardinal_AC + M_aleph + M_FiniteFun +
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

end (* M_library *)

relativize functional "cexp" "cexp_rel" external
(*
relationalize "cexp" "is_cexp"
\<comment> \<open>fails with "Constant ZF_Base.Pi is not present in the db"\<close>
*)

abbreviation
  cexp_r :: "[i,i,i\<Rightarrow>o] \<Rightarrow> i"  (\<open>_\<^bsup>\<up>_,_\<^esup>\<close>) where
  "cexp_r(x,y,M) \<equiv> cexp_rel(M,x,y)"

abbreviation
  cexp_r_set :: "[i,i,i] \<Rightarrow> i"  (\<open>_\<^bsup>\<up>_,_\<^esup>\<close>) where
  "cexp_r_set(x,y,M) \<equiv> cexp_rel(##M,x,y)"

context M_library
begin

lemma Card_cexp: "M(\<kappa>) \<Longrightarrow> M(\<nu>) \<Longrightarrow> Card\<^bsup>M\<^esup>(\<kappa>\<^bsup>\<up>\<nu>,M\<^esup>)"
  unfolding cexp_rel_def by simp

\<comment> \<open>Restoring congruence rule, but NOTE: beware\<close>
declare conj_cong[cong]

lemma eq_csucc_rel_ord:
  "Ord(i) \<Longrightarrow> M(i) \<Longrightarrow> (i\<^sup>+)\<^bsup>M\<^esup> = (|i|\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup>"
  using Card_rel_lt_iff Least_cong unfolding csucc_rel_def by auto

lemma lesspoll_succ_rel:
  assumes "Ord(\<kappa>)" "M(\<kappa>)"
  shows "\<kappa> \<lesssim>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
  using csucc_rel_basic assms lt_Card_rel_imp_lesspoll_rel
    Card_rel_csucc_rel lepoll_rel_iff_leqpoll_rel
  by auto

lemma lesspoll_rel_csucc_rel:
  assumes "Ord(\<kappa>)"
    and types:"M(\<kappa>)" "M(d)"
  shows "d \<prec>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup> \<longleftrightarrow> d \<lesssim>\<^bsup>M\<^esup> \<kappa>"
proof
  assume "d \<prec>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
  moreover
  note Card_rel_csucc_rel assms Card_rel_is_Ord
  moreover from calculation
  have "Card\<^bsup>M\<^esup>((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)" "M((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)" "Ord((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)"
    using Card_rel_is_Ord by simp_all
  moreover from calculation
  have "d \<prec>\<^bsup>M\<^esup> (|\<kappa>|\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup>" "d \<approx>\<^bsup>M\<^esup> |d|\<^bsup>M\<^esup>"
    using eq_csucc_rel_ord[OF _ \<open>M(\<kappa>)\<close>]
      lesspoll_rel_imp_eqpoll_rel eqpoll_rel_sym by simp_all
  moreover from calculation
  have "|d|\<^bsup>M\<^esup> < (|\<kappa>|\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup>"
    using lesspoll_cardinal_lt_rel by simp
  moreover from calculation
  have "|d|\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^esup> |\<kappa>|\<^bsup>M\<^esup>"
    using lt_csucc_rel_iff le_imp_lepoll_rel by simp
  moreover from calculation
  have "|d|\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^esup> \<kappa>"
    using Ord_cardinal_rel_eqpoll_rel lepoll_rel_eq_trans
    by simp
  ultimately
  show "d \<lesssim>\<^bsup>M\<^esup> \<kappa>"
    using eq_lepoll_rel_trans by simp
next
  from \<open>Ord(\<kappa>)\<close>
  have "\<kappa> < (\<kappa>\<^sup>+)\<^bsup>M\<^esup>" "Card\<^bsup>M\<^esup>((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)" "M((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)"
    using Card_rel_csucc_rel lt_csucc_rel_iff types eq_csucc_rel_ord[OF _ \<open>M(\<kappa>)\<close>]
    by simp_all
  then
  have "\<kappa> \<prec>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
  using lt_Card_rel_imp_lesspoll_rel[OF _ \<open>\<kappa> <_\<close>] types by simp
  moreover
  assume "d \<lesssim>\<^bsup>M\<^esup> \<kappa>"
  ultimately
  have "d \<lesssim>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
    using Card_rel_csucc_rel types lesspoll_succ_rel lepoll_rel_trans \<open>Ord(\<kappa>)\<close>
    by simp
  moreover
  from \<open>d \<lesssim>\<^bsup>M\<^esup> \<kappa>\<close> \<open>Ord(\<kappa>)\<close>
  have "(\<kappa>\<^sup>+)\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^esup> \<kappa>" if "d \<approx>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
    using eqpoll_rel_sym[OF that] types eq_lepoll_rel_trans[OF _ \<open>d\<lesssim>\<^bsup>M\<^esup>\<kappa>\<close>]
    by simp
  moreover from calculation \<open>\<kappa> \<prec>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>\<close>
  have False if "d \<approx>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
    using lesspoll_rel_irrefl[OF _ \<open>M((\<kappa>\<^sup>+)\<^bsup>M\<^esup>)\<close>] lesspoll_rel_trans1 types that
    by auto
  ultimately
  show "d \<prec>\<^bsup>M\<^esup> (\<kappa>\<^sup>+)\<^bsup>M\<^esup>"
    unfolding lesspoll_rel_def by auto
qed

lemma Infinite_imp_nats_lepoll:
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

lemma nepoll_imp_nepoll_rel :
  assumes "\<not> x \<approx> X" "M(x)" "M(X)"
  shows "\<not> (x \<approx>\<^bsup>M\<^esup> X)"
  using assms unfolding eqpoll_def eqpoll_rel_def by simp

lemma Infinite_imp_nats_lepoll_rel:
  assumes "Infinite(X)" "n \<in> \<omega>"
    and types: "M(X)"
  shows "n \<lesssim>\<^bsup>M\<^esup> X"
  using \<open>n \<in> \<omega>\<close>
proof (induct)
  case 0
  then
  show ?case using empty_lepoll_relI types by simp
next
  case (succ x)
  show ?case
  proof -
    from \<open>Infinite(X)\<close> and \<open>x \<in> \<omega>\<close>
    have "\<not> (x \<approx> X)" "M(x)" "M(succ(x))"
      using eqpoll_sym unfolding Finite_def by auto
    then
    have "\<not> (x \<approx>\<^bsup>M\<^esup> X)"
      using nepoll_imp_nepoll_rel types by simp
    with \<open>x \<lesssim>\<^bsup>M\<^esup> X\<close>
    obtain f where "f \<in> inj\<^bsup>M\<^esup>(x,X)" "f \<notin> surj\<^bsup>M\<^esup>(x,X)" "M(f)"
      unfolding bij_rel_def eqpoll_rel_def by auto
    with \<open>M(X)\<close> \<open>M(x)\<close>
    have "f\<notin>surj(x,X)" "f\<in>inj(x,X)"
      using surj_rel_char by simp_all
    moreover
    from this
    obtain b where "b \<in> X" "\<forall>a\<in>x. f`a \<noteq> b"
      using inj_is_fun unfolding surj_def by auto
    moreover
    from this calculation \<open>M(x)\<close>
    have "f \<in> inj(x,X-{b})" "M(<x,b>)"
      unfolding inj_def using transM[OF _ \<open>M(X)\<close>]
      by (auto intro:Pi_type)
    moreover
    from this
    have "cons(\<langle>x, b\<rangle>, f) \<in> inj(succ(x), cons(b, X - {b}))" (is "?g\<in>_")
      using inj_extend[of f x "X-{b}" x b] unfolding succ_def
      by (auto dest:mem_irrefl)
    moreover
    note \<open>M(<x,b>)\<close> \<open>M(f)\<close> \<open>b\<in>X\<close> \<open>M(X)\<close> \<open>M(succ(x))\<close>
    moreover from this
    have "M(?g)" "cons(b, X - {b}) = X" by auto
    moreover from calculation
    have "?g\<in>inj_rel(M,succ(x),X)"
      using mem_inj_abs by simp
    with \<open>M(?g)\<close>
    show "succ(x) \<lesssim>\<^bsup>M\<^esup> X" using lepoll_relI by simp
  qed
qed

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
      using lt_trans1[of min "\<mu> i. M(i) \<and> (\<exists>f[M]. f \<in> bij\<^bsup>M\<^esup>(i, \<kappa>))" \<kappa>]
       Least_le[of "\<lambda>i. i \<approx>\<^bsup>M\<^esup> \<kappa>" "|\<kappa>|\<^bsup>M\<^esup>", OF Ord_cardinal_rel_eqpoll_rel]
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

end (* M_library *)

relativize functional "mono_map" "mono_map_rel" external
relationalize "mono_map_rel" "is_mono_map"

notation mono_map_rel (\<open>mono'_map\<^bsup>_\<^esup>'(_,_,_,_')\<close>)

abbreviation
  mono_map_r_set  :: "[i,i,i,i,i]\<Rightarrow>i"  (\<open>mono'_map\<^bsup>_\<^esup>'(_,_,_,_')\<close>) where
  "mono_map\<^bsup>M\<^esup>(a,r,b,s) \<equiv> mono_map_rel(##M,a,r,b,s)"

context M_library
begin

lemma mono_map_rel_char:
  assumes "M(a)" "M(b)"
  shows "mono_map\<^bsup>M\<^esup>(a,r,b,s) = {f\<in>mono_map(a,r,b,s) . M(f)}"
  using assms function_space_rel_char unfolding mono_map_rel_def mono_map_def
  by auto

text\<open>Just a sample of porting results on \<^term>\<open>mono_map\<close>\<close>
lemma mono_map_rel_mono:
  assumes
    "f \<in> mono_map\<^bsup>M\<^esup>(A,r,B,s)" "B \<subseteq> C"
    and types:"M(A)" "M(B)" "M(C)"
  shows
    "f \<in> mono_map\<^bsup>M\<^esup>(A,r,C,s)"
  using assms mono_map_mono mono_map_rel_char by auto

lemma nats_le_InfCard_rel:
  assumes "n \<in> \<omega>" "InfCard\<^bsup>M\<^esup>(\<kappa>)"
  shows "n \<le> \<kappa>"
  using assms Ord_is_Transset
    le_trans[of n \<omega> \<kappa>, OF le_subset_iff[THEN iffD2]]
  unfolding InfCard_rel_def Transset_def by simp

lemma nat_into_InfCard_rel:
  assumes "n \<in> \<omega>" "InfCard\<^bsup>M\<^esup>(\<kappa>)"
  shows "n \<in> \<kappa>"
  using assms  le_imp_subset[of \<omega> \<kappa>]
  unfolding InfCard_rel_def by auto

lemma Finite_cardinal_rel_in_nat [simp]:
  assumes "Finite(A)" "M(A)" shows "|A|\<^bsup>M\<^esup> \<in> \<omega>"
proof -
  note assms
  moreover from this
  obtain n where "n \<in> \<omega>" "M(n)" "A \<approx> n"
    unfolding Finite_def by auto
  moreover from calculation
  obtain f where "f \<in> bij(A,n)" "f: A-||>n"
    using Finite_Fin[THEN fun_FiniteFunI, OF _ subset_refl] bij_is_fun
    unfolding eqpoll_def by auto
  ultimately
  have "A \<approx>\<^bsup>M\<^esup> n" unfolding eqpoll_rel_def by (auto dest:transM)
  with assms and \<open>M(n)\<close>
  have "n \<approx>\<^bsup>M\<^esup> A" using eqpoll_rel_sym by simp
  moreover
  note \<open>n\<in>\<omega>\<close> \<open>M(n)\<close>
  ultimately
  show ?thesis
    using assms Least_le[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A" n]
      lt_trans1[of _ n \<omega>, THEN ltD]
    unfolding cardinal_rel_def Finite_def
    by (auto dest!:naturals_lt_nat)
qed

lemma InfCard_rel_Aleph_rel:
  notes Aleph_rel_zero[simp]
  assumes "Ord(\<alpha>)"
    and types: "M(\<alpha>)"
  shows "InfCard\<^bsup>M\<^esup>(\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>)"
proof -
  have "\<not> (\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup> \<in> \<omega>)"
  proof (cases "\<alpha>=0")
    case True
    then show ?thesis using mem_irrefl by auto
  next
    case False
    with assms
    have "\<omega> \<in> \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>" using Ord_0_lt[of \<alpha>] ltD by (auto dest:Aleph_rel_increasing)
    then show ?thesis using foundation by blast
  qed
  with assms
  have "\<not> (|\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>|\<^bsup>M\<^esup> \<in> \<omega>)"
    using Card_rel_cardinal_rel_eq by auto
  with assms
  have "Infinite(\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>)" using Ord_Aleph_rel by clarsimp
  with assms
  show ?thesis
    using Inf_Card_rel_is_InfCard_rel by simp
qed

lemmas Limit_Aleph_rel = InfCard_rel_Aleph_rel[THEN InfCard_rel_is_Limit]

bundle Ord_dests = Limit_is_Ord[dest] Card_rel_is_Ord[dest]
bundle Aleph_rel_dests = Aleph_rel_cont[dest]
bundle Aleph_rel_intros = Aleph_rel_increasing[intro!]
bundle Aleph_rel_mem_dests = Aleph_rel_increasing[OF ltI, THEN ltD, dest]


end (* M_library *)

end