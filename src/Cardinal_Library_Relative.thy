section\<open>Cardinal Arithmetic under Choice\label{sec:cardinal-lib-rel}\<close>

theory Cardinal_Library_Relative
  imports
    ZF_Library_Relative
    "../Delta_System_Lemma/Cardinal_Library"
    "../Tools/Try0"
begin

context M_library
begin

declare eqpoll_rel_refl [simp]

subsection\<open>Miscellaneous\<close>

lemma cardinal_rel_RepFun_le:
  assumes "S \<in> A\<rightarrow>B" "M(S)" "M(A)" "M(B)"
  shows "|{S`a . a\<in>A}|\<^bsup>M\<^esup> \<le> |A|\<^bsup>M\<^esup>"
proof -
  note assms
  moreover from this
  have "{S ` a . a \<in> A} = S``A"
    using image_eq_UN RepFun_def UN_iff by force
  moreover from calculation
  have "M(\<lambda>x\<in>A. S ` x)" "M({S ` a . a \<in> A})"
    using lam_closed[of "\<lambda> x. S`x"] apply_type[OF \<open>S\<in>_\<close>]
      transM[OF _ \<open>M(B)\<close>] image_closed
     by auto
  moreover from assms this
  have "(\<lambda>x\<in>A. S`x) \<in> surj_rel(M,A, {S`a . a\<in>A})"
    using mem_surj_abs lam_funtype[of A "\<lambda>x . S`x"]
    unfolding surj_def by auto
  ultimately
  show ?thesis
    using surj_rel_char surj_rel_implies_cardinal_rel_le by simp
qed

lemma subset_imp_le_cardinal_rel: "A \<subseteq> B \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> |A|\<^bsup>M\<^esup> \<le> |B|\<^bsup>M\<^esup>"
  using subset_imp_lepoll_rel[THEN lepoll_rel_imp_cardinal_rel_le] .

lemma lt_cardinal_rel_imp_not_subset: "|A|\<^bsup>M\<^esup> < |B|\<^bsup>M\<^esup> \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> \<not> B \<subseteq> A"
  using subset_imp_le_cardinal_rel le_imp_not_lt  by blast

lemma cardinal_rel_lt_csucc_rel_iff: 
"Card_rel(M,K) \<Longrightarrow> M(K) \<Longrightarrow> M(K') \<Longrightarrow> |K'|\<^bsup>M\<^esup> < (K\<^sup>+)\<^bsup>M\<^esup> \<longleftrightarrow> |K'|\<^bsup>M\<^esup> \<le> K"
  by (simp add: Card_rel_lt_csucc_rel_iff)

lemma fun_rel_is_fun: "f \<in> A\<rightarrow>\<^bsup>M\<^esup>B \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> f \<in> A\<rightarrow>B"
  using function_space_rel_char by simp

lemmas inj_rel_is_fun = inj_is_fun[OF mem_inj_abs[THEN iffD1]]

lemma inj_rel_bij_rel_range: "f \<in> inj\<^bsup>M\<^esup>(A,B) \<Longrightarrow>M(A) \<Longrightarrow> M(B) \<Longrightarrow> f \<in> bij\<^bsup>M\<^esup>(A,range(f))"
  using bij_rel_char inj_rel_char inj_bij_range by force

lemma bij_rel_is_inj_rel: "f \<in> bij\<^bsup>M\<^esup>(A,B) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> f \<in> inj\<^bsup>M\<^esup>(A,B)"
  unfolding bij_rel_def by simp

lemma inj_rel_weaken_type: "[| f \<in> inj\<^bsup>M\<^esup>(A,B);  B\<subseteq>D; M(A); M(B); M(D) |] ==> f \<in> inj\<^bsup>M\<^esup>(A,D)"
  using inj_rel_char inj_rel_is_fun inj_weaken_type by auto

lemma bij_rel_converse_bij_rel [TC]: "f \<in> bij\<^bsup>M\<^esup>(A,B)  \<Longrightarrow> M(A) \<Longrightarrow> M(B) ==> converse(f): bij\<^bsup>M\<^esup>(B,A)"
  using bij_rel_char by force

lemma bij_rel_is_fun_rel: "f \<in> bij\<^bsup>M\<^esup>(A,B) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow>  f \<in> A\<rightarrow>\<^bsup>M\<^esup>B"
  using bij_rel_char mem_function_space_rel_abs bij_is_fun by simp

lemmas bij_rel_is_fun = bij_rel_is_fun_rel[THEN fun_rel_is_fun]

lemma comp_bij_rel:
    "g \<in> bij\<^bsup>M\<^esup>(A,B) \<Longrightarrow> f \<in> bij\<^bsup>M\<^esup>(B,C) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> M(C) \<Longrightarrow> (f O g) \<in> bij\<^bsup>M\<^esup>(A,C)"
  using bij_rel_char comp_bij by force

lemma inj_rel_converse_fun: "f \<in> inj\<^bsup>M\<^esup>(A,B) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> converse(f) \<in> range(f)\<rightarrow>\<^bsup>M\<^esup>A"
proof -
  assume "f \<in> inj\<^bsup>M\<^esup>(A,B)" "M(A)" "M(B)"
  then
  have "M(f)" "M(converse(f))" "M(range(f))" "f\<in>inj(A,B)"
    using inj_rel_char converse_closed range_closed
    by auto
  then
  show ?thesis
    using inj_converse_inj function_space_rel_char inj_is_fun \<open>M(A)\<close> by auto
qed

end (* M_library *)

locale M_cardinal_UN_nat = M_cardinal_UN _ \<omega> X for X
begin
lemma cardinal_rel_UN_le_nat:
  assumes "\<And>i. i\<in>\<omega> \<Longrightarrow> |X(i)|\<^bsup>M\<^esup> \<le> \<omega>"
  shows "|\<Union>i\<in>\<omega>. X(i)|\<^bsup>M\<^esup> \<le> \<omega>"
proof -
  from assms
  show ?thesis
  by (simp add: cardinal_rel_UN_le InfCard_rel_nat)
qed

end (* M_cardinal_UN_nat *)

locale M_cardinal_UN_inj = M_library +
  j:M_cardinal_UN _ J +
  y:M_cardinal_UN _ K "\<lambda>k. if k\<in>range(f) then X(converse(f)`k) else 0" for J K f +
assumes
  f_inj: "f \<in> inj_rel(M,J,K)"
begin

lemma inj_rel_imp_cardinal_rel_UN_le:
  notes [dest] = InfCard_is_Card Card_is_Ord
  fixes Y
  defines "Y(k) \<equiv> if k\<in>range(f) then X(converse(f)`k) else 0"
  assumes "InfCard\<^bsup>M\<^esup>(K)" "\<And>i. i\<in>J \<Longrightarrow> |X(i)|\<^bsup>M\<^esup> \<le> K"
  shows "|\<Union>i\<in>J. X(i)|\<^bsup>M\<^esup> \<le> K"
proof -
  have "M(K)" "M(J)" "\<And>w x. w \<in> X(x) \<Longrightarrow> M(x)"
    using y.Pi_assumptions j.Pi_assumptions j.X_witness_in_M by simp_all
  then
  have "M(f)"
    using inj_rel_char f_inj by simp
  note inM = \<open>M(f)\<close> \<open>M(K)\<close> \<open>M(J)\<close> \<open>\<And>w x. w \<in> X(x) \<Longrightarrow> M(x)\<close>
  have "i\<in>J \<Longrightarrow> f`i \<in> K" for i
    using inj_rel_is_fun[OF _ _ _ f_inj] apply_type
      function_space_rel_char by (auto simp add:inM)
  have "(\<Union>i\<in>J. X(i)) \<subseteq> (\<Union>i\<in>K. Y(i))"
  proof (standard, elim UN_E)
    fix x i
    assume "i\<in>J" "x\<in>X(i)"
    with \<open>i\<in>J \<Longrightarrow> f`i \<in> K\<close>
    have "x \<in> Y(f`i)" "f`i \<in> K"
      unfolding Y_def
      using inj_is_fun right_inverse f_inj
      by (auto simp add:inM Y_def intro: apply_rangeI)
    then
    show "x \<in> (\<Union>i\<in>K. Y(i))" by auto
  qed
  then
  have "|\<Union>i\<in>J. X(i)|\<^bsup>M\<^esup> \<le> |\<Union>i\<in>K. Y(i)|\<^bsup>M\<^esup>"
    using subset_imp_le_cardinal_rel j.UN_closed y.UN_closed
    unfolding Y_def by (simp add:inM)
  moreover
  note assms \<open>\<And>i. i\<in>J \<Longrightarrow> f`i \<in> K\<close> inM
  moreover from this
  have "k\<in>range(f) \<Longrightarrow> converse(f)`k \<in> J" for k
    using inj_rel_converse_fun[OF f_inj]
      range_fun_subset_codomain function_space_rel_char by simp
  ultimately
  show "|\<Union>i\<in>J. X(i)|\<^bsup>M\<^esup> \<le> K"
    using InfCard_rel_is_Card_rel[THEN Card_rel_is_Ord,THEN Ord_0_le, of K]
    by (rule_tac le_trans[OF _ y.cardinal_rel_UN_le])
      (auto intro:Ord_0_le simp:Y_def)+
qed

end (* M_cardinal_UN_inj *)

locale M_cardinal_UN_lepoll = M_library +
  j:M_cardinal_UN _ J for J +
assumes
  lepoll_assumptions:
  "M(f) \<Longrightarrow> strong_replacement(M,
    \<lambda>x z. z = Sigfun(x, \<lambda>k. if k \<in> range(f) then X(converse(f) ` k) else 0))"
  "M(f) \<Longrightarrow> strong_replacement(M,
    \<lambda>x y. y = (if x \<in> range(f) then X(converse(f) ` x) else 0))"
  "M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> M(fa) \<Longrightarrow> M(x) \<Longrightarrow> strong_replacement(M, \<lambda>y z. y \<in> X(converse(f) ` x) \<and> z = {\<langle>x, y\<rangle>})"
  "M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> strong_replacement(M,
    \<lambda>x y. y = \<langle>x, minimum(r, if x \<in> range(f) then X(converse(f) ` x) else 0)\<rangle>)"
  "M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> M(fa) \<Longrightarrow> strong_replacement(M,
    \<lambda>x y. y = \<langle>x, \<mu> i. x \<in> (if i \<in> range(f) then X(converse(f) ` i) else 0),
		fa ` (\<mu> i. x \<in> (if i \<in> range(f) then X(converse(f) ` i) else 0)) ` x\<rangle>)"
	"M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> M(fa) \<Longrightarrow> M(x) \<Longrightarrow> strong_replacement(M,
    \<lambda>y z. y \<in> inj\<^bsup>M\<^esup>(if x \<in> range(f) then X(converse(f) ` x) else 0,K) \<and> z = {\<langle>x, y\<rangle>})"
  "M(f) \<Longrightarrow> M(K) \<Longrightarrow> strong_replacement(M,
    \<lambda>x y. y = inj\<^bsup>M\<^esup>(if x \<in> range(f) then X(converse(f) ` x) else 0,K))"
  "M(f) \<Longrightarrow> M(K) \<Longrightarrow> strong_replacement(M,
    \<lambda>x z. z = Sigfun(x, \<lambda>i. inj\<^bsup>M\<^esup>(if i \<in> range(f) then X(converse(f) ` i) else 0,K)))"
  "M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> strong_replacement(M,
    \<lambda>x y. y = \<langle>x, minimum(r, inj\<^bsup>M\<^esup>(if x \<in> range(f) then X(converse(f) ` x) else 0,K))\<rangle>)"
begin

\<comment>\<open>FIXME: this "LEQpoll" should be "LEPOLL"; same correction in Delta System\<close>
lemma leqpoll_rel_imp_cardinal_rel_UN_le:
  notes [dest] = InfCard_is_Card Card_is_Ord
  assumes "InfCard\<^bsup>M\<^esup>(K)" "J \<lesssim>\<^bsup>M\<^esup> K" "\<And>i. i\<in>J \<Longrightarrow> |X(i)|\<^bsup>M\<^esup> \<le> K"
    "M(K)"
  shows "|\<Union>i\<in>J. X(i)|\<^bsup>M\<^esup> \<le> K"
proof -
  from \<open>J \<lesssim>\<^bsup>M\<^esup> K\<close>
  obtain f where "f \<in> inj_rel(M,J,K)" "M(f)" by blast
  moreover
  let ?Y="\<lambda>k. if k\<in>range(f) then X(converse(f)`k) else 0"
  note \<open>M(K)\<close>
  moreover from calculation
  have "k \<in> range(f) \<Longrightarrow> converse(f)`k \<in> J" for k
    using mem_inj_rel[THEN inj_converse_fun, THEN apply_type]
      j.Pi_assumptions by blast
  moreover from \<open>M(f)\<close>
  have "w \<in> ?Y(x) \<Longrightarrow> M(x)" for w x
    by (cases "x\<in>range(f)") (auto dest:transM)
  moreover from calculation
  interpret M_Pi_assumptions_choice _ K ?Y
    using j.Pi_assumptions lepoll_assumptions(1-3)[of f] lepoll_assumptions(4-)[of f K]
  proof (unfold_locales, auto dest:transM)
    show "strong_replacement(M, \<lambda>y z. False)"
      unfolding strong_replacement_def by auto
  qed
  from calculation
  interpret M_cardinal_UN_inj _ _ _ _ f
    using lepoll_assumptions(5-)[of f K]
    by unfold_locales auto
  from assms
  show ?thesis using inj_rel_imp_cardinal_rel_UN_le by simp
qed

end (* M_cardinal_UN_lepoll *)

context M_library
begin

lemma cardinal_rel_lt_csucc_rel_iff':
  includes Ord_dests
  assumes "Card_rel(M,\<kappa>)"
    and types:"M(\<kappa>)" "M(X)"
  shows "\<kappa> < |X|\<^bsup>M\<^esup> \<longleftrightarrow> (\<kappa>\<^sup>+)\<^bsup>M\<^esup> \<le> |X|\<^bsup>M\<^esup>"
  using assms cardinal_rel_lt_csucc_rel_iff[of \<kappa> X] Card_rel_csucc_rel[of \<kappa>]
    not_le_iff_lt[of "(\<kappa>\<^sup>+)\<^bsup>M\<^esup>" "|X|\<^bsup>M\<^esup>"] not_le_iff_lt[of "|X|\<^bsup>M\<^esup>" \<kappa>]
  by blast

lemma lepoll_rel_imp_subset_bij_rel: 
  assumes "M(X)" "M(Y)"
  shows "X \<lesssim>\<^bsup>M\<^esup> Y \<longleftrightarrow> (\<exists>Z[M]. Z \<subseteq> Y \<and> Z \<approx>\<^bsup>M\<^esup> X)"
proof
  assume "X \<lesssim>\<^bsup>M\<^esup> Y"
  then
  obtain j where  "j \<in> inj_rel(M,X,Y)"
    by blast
  with assms
  have "range(j) \<subseteq> Y" "j \<in> bij_rel(M,X,range(j))" "M(range(j))" "M(j)"
    using inj_rel_bij_rel_range inj_rel_char
      inj_rel_is_fun[THEN range_fun_subset_codomain]
    by auto
  with assms
  have "range(j) \<subseteq> Y" "X \<approx>\<^bsup>M\<^esup> range(j)"
    unfolding eqpoll_rel_def by auto
  with assms \<open>M(j)\<close>
  show "\<exists>Z[M]. Z \<subseteq> Y \<and> Z \<approx>\<^bsup>M\<^esup> X"
    using eqpoll_rel_sym[OF \<open>X \<approx>\<^bsup>M\<^esup> range(j)\<close>]
    by auto
next
  assume "\<exists>Z[M]. Z \<subseteq> Y \<and> Z \<approx>\<^bsup>M\<^esup> X"
  then
  obtain Z f where "f \<in> bij_rel(M,Z,X)" "Z \<subseteq> Y" "M(Z)" "M(f)"
    unfolding eqpoll_rel_def by blast
  with assms
  have "converse(f) \<in> inj_rel(M,X,Y)" "M(converse(f))"
    using inj_rel_weaken_type[OF bij_rel_converse_bij_rel[THEN bij_rel_is_inj_rel],of f Z X Y]
    by auto
  then
  show "X \<lesssim>\<^bsup>M\<^esup> Y"
    unfolding lepoll_rel_def by auto
qed

text\<open>The following result proves to be very useful when combining
     \<^term>\<open>cardinal_rel\<close> and \<^term>\<open>eqpoll_rel\<close> in a calculation.\<close>

lemma cardinal_rel_Card_rel_eqpoll_rel_iff: 
  "M(\<kappa>) \<Longrightarrow> M(X) \<Longrightarrow> Card_rel(M,\<kappa>) \<Longrightarrow> |X|\<^bsup>M\<^esup> = \<kappa> \<longleftrightarrow> X \<approx>\<^bsup>M\<^esup> \<kappa>"
  using Card_rel_cardinal_rel_eq[of \<kappa>] cardinal_rel_eqpoll_rel_iff[of X \<kappa>] by auto

lemma lepoll_rel_imp_lepoll_rel_cardinal_rel: 
  assumes "M(X)" "M(Y)" "X \<lesssim>\<^bsup>M\<^esup> Y" 
  shows "X \<lesssim>\<^bsup>M\<^esup> |Y|\<^bsup>M\<^esup>"
  using assms cardinal_rel_Card_rel_eqpoll_rel_iff[of "|Y|\<^bsup>M\<^esup>" Y]
  Card_rel_cardinal_rel
    lepoll_rel_eq_trans[of _ _ "|Y|\<^bsup>M\<^esup>"] by simp

lemma lepoll_rel_Un:
  assumes "InfCard_rel(M,\<kappa>)" "M(A)" "M(B)" "M(\<kappa>)"  "A \<lesssim>\<^bsup>M\<^esup> \<kappa>" "B \<lesssim>\<^bsup>M\<^esup> \<kappa>"
  shows "A \<union> B \<lesssim>\<^bsup>M\<^esup> \<kappa>"
proof -
  from assms
  have "A \<union> B \<lesssim>\<^bsup>M\<^esup> sum(A,B)"
    using Un_lepoll_rel_sum by simp
  moreover
  note assms
  moreover from this
  have "|sum(A,B)|\<^bsup>M\<^esup> \<le> \<kappa> \<oplus>\<^bsup>M\<^esup> \<kappa>"
    using sum_lepoll_rel_mono[of A \<kappa> B \<kappa>] lepoll_rel_imp_cardinal_rel_le
    unfolding cadd_rel_def by auto
  ultimately
  show ?thesis
    using InfCard_rel_cdouble_eq Card_rel_cardinal_rel_eq
      InfCard_rel_is_Card_rel Card_rel_le_imp_lepoll_rel[of "sum(A,B)" \<kappa>]
      lepoll_rel_trans[of "A\<union>B"]
    by auto
qed

lemma cardinal_rel_Un_le:
  assumes "M(A)" "M(B)" "M(\<kappa>)" "InfCard_rel(M,\<kappa>)" "|A|\<^bsup>M\<^esup> \<le> \<kappa>" "|B|\<^bsup>M\<^esup> \<le> \<kappa>"
  shows "|A \<union> B|\<^bsup>M\<^esup> \<le> \<kappa>"
  using assms lepoll_rel_Un le_Card_rel_iff InfCard_rel_is_Card_rel by auto

lemma eqpoll_rel_imp_Finite: "A \<approx>\<^bsup>M\<^esup> B \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> Finite(A) \<Longrightarrow> Finite(B)" 
proof -
  assume "A \<approx>\<^bsup>M\<^esup> B" "Finite(A)" "M(A)" "M(B)"
  then obtain f n g where "f\<in>bij(A,B)" "n\<in>\<omega>" "g\<in>bij(A,n)"
    unfolding Finite_def eqpoll_def eqpoll_rel_def
    using bij_rel_char
    by auto
  then
  have "g O converse(f) \<in> bij(B,n)"
    using bij_converse_bij comp_bij by simp
  with \<open>n\<in>_\<close>
  show"Finite(B)"
    unfolding Finite_def eqpoll_def by auto
qed

lemma eqpoll_rel_imp_Finite_iff: "A \<approx>\<^bsup>M\<^esup> B \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> Finite(A) \<longleftrightarrow> Finite(B)"
  using eqpoll_rel_imp_Finite eqpoll_rel_sym by force

lemma Finite_cardinal_rel_iff': "M(i) \<Longrightarrow> Finite(|i|\<^bsup>M\<^esup>) \<longleftrightarrow> Finite(i)"
  using eqpoll_rel_imp_Finite_iff[OF cardinal_rel_eqpoll_rel]
  by auto

lemma cardinal_rel_subset_of_Card_rel:
  assumes "Card_rel(M,\<gamma>)" "a \<subseteq> \<gamma>" "M(a)" "M(\<gamma>)"
  shows "|a|\<^bsup>M\<^esup> < \<gamma> \<or> |a|\<^bsup>M\<^esup> = \<gamma>"
proof -
  from assms
  have "|a|\<^bsup>M\<^esup> < |\<gamma>|\<^bsup>M\<^esup> \<or> |a|\<^bsup>M\<^esup> = |\<gamma>|\<^bsup>M\<^esup>"
    using subset_imp_le_cardinal_rel[THEN le_iff[THEN iffD1]] by simp
  with assms
  show ?thesis
    using Card_rel_cardinal_rel_eq by auto
qed

lemma cardinal_rel_cases:
  includes Ord_dests
  assumes "M(\<gamma>)" "M(X)"
  shows "Card_rel(M,\<gamma>) \<Longrightarrow> |X|\<^bsup>M\<^esup> < \<gamma> \<longleftrightarrow> \<not> |X|\<^bsup>M\<^esup> \<ge> \<gamma>"
  using assms not_le_iff_lt Card_rel_is_Ord Ord_cardinal_rel
  by auto

end (* M_library *)

subsection\<open>Countable and uncountable sets\<close>

relativize functional "countable" "countable_rel" external
relationalize "countable_rel" "is_countable"

context M_library
begin

lemma countableI[intro]: "X \<lesssim>\<^bsup>M\<^esup> \<omega> \<Longrightarrow> countable_rel(M,X)"
  unfolding countable_rel_def by simp

lemma countableD[dest]: "countable_rel(M,X) \<Longrightarrow> X \<lesssim>\<^bsup>M\<^esup> \<omega>"
  unfolding countable_rel_def by simp

lemma countable_rel_iff_cardinal_rel_le_nat: "M(X) \<Longrightarrow> countable_rel(M,X) \<longleftrightarrow> |X|\<^bsup>M\<^esup> \<le> \<omega>"
  using le_Card_rel_iff[of \<omega> X] Card_rel_nat
  unfolding countable_rel_def by simp

lemma lepoll_rel_countable_rel: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<lesssim>\<^bsup>M\<^esup> Y \<Longrightarrow> countable_rel(M,Y) \<Longrightarrow> countable_rel(M,X)"
  using lepoll_rel_trans[of X Y] by blast

\<comment> \<open>Next lemma can be proved without using AC\<close>
lemma surj_rel_countable_rel:
  "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> M(f) \<Longrightarrow> countable_rel(M,X) \<Longrightarrow> f \<in> surj_rel(M,X,Y) \<Longrightarrow> countable_rel(M,Y)"
  using surj_rel_implies_cardinal_rel_le[of f X Y, THEN le_trans]
    countable_rel_iff_cardinal_rel_le_nat by simp

lemma Finite_imp_countable_rel: "M(X) \<Longrightarrow> Finite_rel(M,X) \<Longrightarrow> countable_rel(M,X)"
  unfolding Finite_rel_def
  by (auto intro:InfCard_rel_nat nats_le_InfCard_rel[of _ \<omega>,
        THEN le_imp_lepoll_rel] dest!:eq_lepoll_rel_trans[of X _ \<omega>] )

end (* M_library *)

lemma (in M_cardinal_UN_lepoll) countable_rel_imp_countable_rel_UN:
  assumes "countable_rel(M,J)" "\<And>i. i\<in>J \<Longrightarrow> countable_rel(M,X(i))"
  shows "countable_rel(M,\<Union>i\<in>J. X(i))"
  using assms leqpoll_rel_imp_cardinal_rel_UN_le[of \<omega>] InfCard_rel_nat
    InfCard_rel_is_Card_rel j.UN_closed
    countable_rel_iff_cardinal_rel_le_nat j.Pi_assumptions
    Card_rel_le_imp_lepoll_rel[of J \<omega>] Card_rel_cardinal_rel_eq[of \<omega>]
  by auto
 
locale M_cardinal_library = M_library +
  assumes
    cardinal_lib_assms1:"M(C) \<Longrightarrow> \<forall>x\<in>C. strong_replacement(M, \<lambda>y z. y \<in> (if M(x) then x else 0) \<and> z = {\<langle>x, y\<rangle>})"
    "M(C) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = Sigfun(x, \<lambda>n. if M(n) then n else 0))"
    "M(C) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = (if M(x) then x else 0))"
    "M(C) \<Longrightarrow> M(r) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, minimum(r, if M(x) then x else 0)\<rangle>)"
    "M(C) \<Longrightarrow>
         M(f) \<Longrightarrow>
         strong_replacement
          (M, \<lambda>x y. y = \<langle>x, \<mu> i. x \<in> (if M(i) then i else 0),
                         f ` (\<mu> i. x \<in> (if M(i) then i else 0)) ` x\<rangle>)"
    "M(C) \<Longrightarrow>
         M(x) \<Longrightarrow> strong_replacement(M, \<lambda>y z. y \<in> inj\<^bsup>M\<^esup>(if M(x) then x else 0,C) \<and> z = {\<langle>x, y\<rangle>})"
    "M(C) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = inj\<^bsup>M\<^esup>(if M(x) then x else 0,C))"
    "M(C) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = Sigfun(x, \<lambda>i. inj\<^bsup>M\<^esup>(if M(i) then i else 0,C)))"
    "M(C) \<Longrightarrow>
         M(r) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, minimum(r, inj\<^bsup>M\<^esup>(if M(x) then x else 0,C))\<rangle>)"
    "M(C) \<Longrightarrow>
          M(f) \<Longrightarrow>
          strong_replacement
           (M, \<lambda>x z. z = Sigfun
                           (x, \<lambda>k. if k \<in> range(f)
                                    then if M(converse(f) ` k) then (converse(f) ` k) else 0 else 0))"
    "M(C) \<Longrightarrow>
          M(f) \<Longrightarrow>
          strong_replacement
           (M, \<lambda>x y. y = (if x \<in> range(f) then if M(converse(f) ` x) then (converse(f) ` x) else 0
                           else 0))"
    "M(C) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        M(fa) \<Longrightarrow>
        M(x) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>y z. y \<in> (if M(converse(f) ` x) then (converse(f) ` x) else 0) \<and> z = {\<langle>x, y\<rangle>})"
    "M(C) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>x y. y = \<langle>x, minimum
                            (r, if x \<in> range(f)
                                then if M(converse(f) ` x) then (converse(f) ` x) else 0 else 0)\<rangle>)"
    "M(C) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        M(fa) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>x y. y = \<langle>x, \<mu> i. x \<in>
                                (if i \<in> range(f)
                                 then if M(converse(f) ` i) then (converse(f) ` i) else 0 else 0),
                        fa `
                        (\<mu> i. x \<in> (if i \<in> range(f)
                                    then if M(converse(f) ` i) then (converse(f) ` i) else 0
                                    else 0)) `
                        x\<rangle>)"
    "M(C) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        M(fa) \<Longrightarrow>
        M(x) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>y z. y \<in> inj\<^bsup>M\<^esup>(if x \<in> range(f)
                               then if M(converse(f) ` x) then (converse(f) ` x) else 0 else 0,K) \<and>
                    z = {\<langle>x, y\<rangle>})"
    "M(C) \<Longrightarrow>
            M(f) \<Longrightarrow>
            M(K) \<Longrightarrow>
            strong_replacement
             (M, \<lambda>x y. y = inj\<^bsup>M\<^esup>(if x \<in> range(f)
                                   then if M(converse(f) ` x) then (converse(f) ` x) else 0
                                   else 0,K))"
    "M(C) \<Longrightarrow>
            M(f) \<Longrightarrow>
            M(K) \<Longrightarrow>
            strong_replacement
             (M, \<lambda>x z. z = Sigfun
                             (x, \<lambda>i. inj\<^bsup>M\<^esup>(if i \<in> range(f)
                                             then if M(converse(f) ` i) then (converse(f) ` i) else 0
                                             else 0,K)))"
    "M(C) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>x y. y = \<langle>x, minimum
                            (r, inj\<^bsup>M\<^esup>(if x \<in> range(f)
                                       then if M(converse(f) ` x) then (converse(f) ` x) else 0
                                       else 0,K))\<rangle>)"

  and

    cardinal_lib_assms2:
    "M(G) \<Longrightarrow> \<forall>x\<in>domain(G). strong_replacement(M, \<lambda>y z. y \<in> (if M(x) then G ` x else 0) \<and> z = {\<langle>x, y\<rangle>})"
    "M(G) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = Sigfun(x, \<lambda>n. if M(n) then G ` n else 0))"
    "M(G) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = (if M(x) then G ` x else 0))"
    "M(G) \<Longrightarrow> M(r) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, minimum(r, if M(x) then G ` x else 0)\<rangle>)"
    "M(G) \<Longrightarrow>
         M(f) \<Longrightarrow>
         strong_replacement
          (M, \<lambda>x y. y = \<langle>x, \<mu> i. x \<in> (if M(i) then G ` i else 0),
                         f ` (\<mu> i. x \<in> (if M(i) then G ` i else 0)) ` x\<rangle>)"
    "M(G) \<Longrightarrow>
         M(x) \<Longrightarrow>
         strong_replacement(M, \<lambda>y z. y \<in> inj\<^bsup>M\<^esup>(if M(x) then G ` x else 0,domain(G)) \<and> z = {\<langle>x, y\<rangle>})"
    "M(G) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = inj\<^bsup>M\<^esup>(if M(x) then G ` x else 0,domain(G)))"
    "M(G) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = Sigfun(x, \<lambda>i. inj\<^bsup>M\<^esup>(if M(i) then G ` i else 0,domain(G))))"
    "M(G) \<Longrightarrow>
          M(r) \<Longrightarrow>
          strong_replacement(M, \<lambda>x y. y = \<langle>x, minimum(r, inj\<^bsup>M\<^esup>(if M(x) then G ` x else 0,domain(G)))\<rangle>)"
    "M(G) \<Longrightarrow>
          M(f) \<Longrightarrow>
          strong_replacement
           (M, \<lambda>x z. z = Sigfun
                           (x, \<lambda>k. if k \<in> range(f)
                                    then if M(converse(f) ` k) then G ` (converse(f) ` k) else 0 else 0))"
    "M(G) \<Longrightarrow>
          M(f) \<Longrightarrow>
          strong_replacement
           (M, \<lambda>x y. y = (if x \<in> range(f) then if M(converse(f) ` x) then G ` (converse(f) ` x) else 0
                           else 0))"
    "M(G) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        M(fa) \<Longrightarrow>
        M(x) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>y z. y \<in> (if M(converse(f) ` x) then G ` (converse(f) ` x) else 0) \<and> z = {\<langle>x, y\<rangle>})"
    "M(G) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>x y. y = \<langle>x, minimum
                            (r, if x \<in> range(f)
                                then if M(converse(f) ` x) then G ` (converse(f) ` x) else 0 else 0)\<rangle>)"
    "M(G) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        M(fa) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>x y. y = \<langle>x, \<mu> i. x \<in>
                                (if i \<in> range(f)
                                 then if M(converse(f) ` i) then G ` (converse(f) ` i) else 0 else 0),
                        fa `
                        (\<mu> i. x \<in> (if i \<in> range(f)
                                    then if M(converse(f) ` i) then G ` (converse(f) ` i) else 0
                                    else 0)) `
                        x\<rangle>)"
    "M(G) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        M(fa) \<Longrightarrow>
        M(x) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>y z. y \<in> inj\<^bsup>M\<^esup>(if x \<in> range(f)
                               then if M(converse(f) ` x) then G ` (converse(f) ` x) else 0 else 0,K) \<and>
                    z = {\<langle>x, y\<rangle>})"
    "M(G) \<Longrightarrow>
            M(f) \<Longrightarrow>
            M(K) \<Longrightarrow>
            strong_replacement
             (M, \<lambda>x y. y = inj\<^bsup>M\<^esup>(if x \<in> range(f)
                                   then if M(converse(f) ` x) then G ` (converse(f) ` x) else 0
                                   else 0,K))"
    "M(G) \<Longrightarrow>
            M(f) \<Longrightarrow>
            M(K) \<Longrightarrow>
            strong_replacement
             (M, \<lambda>x z. z = Sigfun
                             (x, \<lambda>i. inj\<^bsup>M\<^esup>(if i \<in> range(f)
                                             then if M(converse(f) ` i) then G ` (converse(f) ` i) else 0
                                             else 0,K)))"
    "M(G) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>x y. y = \<langle>x, minimum
                            (r, inj\<^bsup>M\<^esup>(if x \<in> range(f)
                                       then if M(converse(f) ` x) then G ` (converse(f) ` x) else 0
                                       else 0,K))\<rangle>)"

and

cardinal_lib_assms3:"M(Z) \<Longrightarrow> M(F) \<Longrightarrow> \<forall>x\<in>Y. strong_replacement(M, \<lambda>y z. y \<in> (if M(x) then {xa \<in> Z . F ` xa = x} else 0) \<and> z = {\<langle>x, y\<rangle>})"
"M(Z) \<Longrightarrow> M(F) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = Sigfun(x, \<lambda>y. if M(y) then {x \<in> Z . F ` x = y} else 0))"
"M(Z) \<Longrightarrow> M(F) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = (if M(x) then {xa \<in> Z . F ` xa = x} else 0))"
"M(Z) \<Longrightarrow>
         M(F) \<Longrightarrow> M(r) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, minimum(r, if M(x) then {xa \<in> Z . F ` xa = x} else 0)\<rangle>)"
"M(Z) \<Longrightarrow>
         M(F) \<Longrightarrow>
         M(f) \<Longrightarrow>
         strong_replacement
          (M, \<lambda>x y. y = \<langle>x, \<mu> i. x \<in> (if M(i) then {x \<in> Z . F ` x = i} else 0),
                         f ` (\<mu> i. x \<in> (if M(i) then {x \<in> Z . F ` x = i} else 0)) ` x\<rangle>)"
"M(Z) \<Longrightarrow>
         M(F) \<Longrightarrow>
         M(x) \<Longrightarrow> strong_replacement(M, \<lambda>y z. y \<in> inj\<^bsup>M\<^esup>(if M(x) then {xa \<in> Z . F ` xa = x} else 0,Y) \<and> z = {\<langle>x, y\<rangle>})"
"M(Z) \<Longrightarrow> M(F) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = inj\<^bsup>M\<^esup>(if M(x) then {xa \<in> Z . F ` xa = x} else 0,Y))"
"M(Z) \<Longrightarrow> M(F) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = Sigfun(x, \<lambda>i. inj\<^bsup>M\<^esup>(if M(i) then {x \<in> Z . F ` x = i} else 0,Y)))"
"M(Z) \<Longrightarrow>
         M(F) \<Longrightarrow>
         M(r) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, minimum(r, inj\<^bsup>M\<^esup>(if M(x) then {xa \<in> Z . F ` xa = x} else 0,Y))\<rangle>)"
"M(Z) \<Longrightarrow>
          M(F) \<Longrightarrow>
          M(f) \<Longrightarrow>
          strong_replacement
           (M, \<lambda>x z. z = Sigfun
                           (x, \<lambda>k. if k \<in> range(f)
                                    then if M(converse(f) ` k) then {x \<in> Z . F ` x = converse(f) ` k} else 0 else 0))"
"M(Z) \<Longrightarrow>
          M(F) \<Longrightarrow>
          M(f) \<Longrightarrow>
          strong_replacement
           (M, \<lambda>x y. y = (if x \<in> range(f) then if M(converse(f) ` x) then {xa \<in> Z . F ` xa = converse(f) ` x} else 0
                           else 0))"
"M(Z) \<Longrightarrow>
        M(F) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        M(fa) \<Longrightarrow>
        M(x) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>y z. y \<in> (if M(converse(f) ` x) then {xa \<in> Z . F ` xa = converse(f) ` x} else 0) \<and> z = {\<langle>x, y\<rangle>})"
"M(Z) \<Longrightarrow>
        M(F) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>x y. y = \<langle>x, minimum
                            (r, if x \<in> range(f)
                                then if M(converse(f) ` x) then {xa \<in> Z . F ` xa = converse(f) ` x} else 0 else 0)\<rangle>)"
"M(Z) \<Longrightarrow>
        M(F) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        M(fa) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>x y. y = \<langle>x, \<mu> i. x \<in>
                                (if i \<in> range(f) then if M(converse(f) ` i) then {x \<in> Z . F ` x = converse(f) ` i} else 0
                                 else 0),
                        fa `
                        (\<mu> i. x \<in> (if i \<in> range(f)
                                    then if M(converse(f) ` i) then {x \<in> Z . F ` x = converse(f) ` i} else 0 else 0)) `
                        x\<rangle>)"
"M(Z) \<Longrightarrow>
        M(F) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        M(fa) \<Longrightarrow>
        M(x) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>y z. y \<in> inj\<^bsup>M\<^esup>(if x \<in> range(f) then if M(converse(f) ` x) then {xa \<in> Z . F ` xa = converse(f) ` x} else 0
                               else 0,K) \<and>
                    z = {\<langle>x, y\<rangle>})"
"M(Z) \<Longrightarrow>
            M(F) \<Longrightarrow>
            M(f) \<Longrightarrow>
            M(K) \<Longrightarrow>
            strong_replacement
             (M, \<lambda>x y. y = inj\<^bsup>M\<^esup>(if x \<in> range(f)
                                   then if M(converse(f) ` x) then {xa \<in> Z . F ` xa = converse(f) ` x} else 0 else 0,K))"
"M(Z) \<Longrightarrow>
            M(F) \<Longrightarrow>
            M(f) \<Longrightarrow>
            M(K) \<Longrightarrow>
            strong_replacement
             (M, \<lambda>x z. z = Sigfun
                             (x, \<lambda>i. inj\<^bsup>M\<^esup>(if i \<in> range(f)
                                             then if M(converse(f) ` i) then {x \<in> Z . F ` x = converse(f) ` i} else 0
                                             else 0,K)))"
"M(Z) \<Longrightarrow>
        M(F) \<Longrightarrow>
        M(f) \<Longrightarrow>
        M(K) \<Longrightarrow>
        M(r) \<Longrightarrow>
        strong_replacement
         (M, \<lambda>x y. y = \<langle>x, minimum
                            (r, inj\<^bsup>M\<^esup>(if x \<in> range(f)
                                       then if M(converse(f) ` x) then {xa \<in> Z . F ` xa = converse(f) ` x} else 0
                                       else 0,K))\<rangle>)"
and cardinal_lib_assms4: "M(f) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, f -`` {x}\<rangle>)"

begin

lemma countable_rel_union_countable_rel:
  assumes "\<And>x. x \<in> C \<Longrightarrow> countable_rel(M,x)" "countable_rel(M,C)" "M(C)"
  shows "countable_rel(M,\<Union>C)"
proof -
  \<comment> \<open>These few lines repeat below mutatis mutandis\<close>
  note \<open>M(C)\<close>
  moreover
  have  "w \<in> (if M(x) then x else 0) \<Longrightarrow> M(x)" for w x
    by (cases "M(x)") auto
  ultimately
  interpret M_cardinal_UN_lepoll _ "\<lambda>c. if M(c) then c else 0" C
    using cardinal_lib_assms1
    by unfold_locales simp_all
  have "(if M(i) then i else 0) = i" if "i\<in>C" for i 
    using transM[OF _ \<open>M(C)\<close>] that by simp
  then
  show ?thesis
    using assms countable_rel_imp_countable_rel_UN by simp
qed

end (* M_library *)

abbreviation
  uncountable_rel :: "[i\<Rightarrow>o,i]\<Rightarrow>o" where
  "uncountable_rel(M,X) \<equiv> \<not> countable_rel(M,X)"

context M_cardinal_library
begin

lemma uncountable_rel_iff_nat_lt_cardinal_rel:
  "M(X) \<Longrightarrow> uncountable_rel(M,X) \<longleftrightarrow> \<omega> < |X|\<^bsup>M\<^esup>"
  using countable_rel_iff_cardinal_rel_le_nat not_le_iff_lt by simp

lemma uncountable_rel_not_empty: "uncountable_rel(M,X) \<Longrightarrow> X \<noteq> 0"
  using empty_lepoll_relI by auto

lemma uncountable_rel_imp_Infinite: "uncountable_rel(M,X) \<Longrightarrow> M(X) \<Longrightarrow> Infinite(X)"
  using uncountable_rel_iff_nat_lt_cardinal_rel[of X] lepoll_rel_nat_imp_Infinite[of X]
    cardinal_rel_le_imp_lepoll_rel[of \<omega> X] leI
  by simp

lemma uncountable_rel_not_subset_countable_rel:
  assumes "M(X)" "M(Y)" "countable_rel(M,X)" "uncountable_rel(M,Y)"
  shows "\<not> (Y \<subseteq> X)"
  using assms lepoll_rel_trans subset_imp_lepoll_rel[of Y X]
  by blast


subsection\<open>Results on Aleph_rels\<close>

lemma nat_lt_Aleph_rel1: "\<omega> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  by (simp add: Aleph_rel_succ Aleph_rel_zero lt_csucc_rel)

lemma zero_lt_Aleph_rel1: "0 < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  by (rule lt_trans[of _ "\<omega>"], auto simp add: ltI nat_lt_Aleph_rel1)

lemma le_Aleph_rel1_nat: "M(k) \<Longrightarrow> Card_rel(M,k) \<Longrightarrow> k<\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> k \<le> \<omega>"
  by (simp add: Aleph_rel_succ Aleph_rel_zero Card_rel_lt_csucc_rel_iff Card_rel_nat)
 
lemma lesspoll_rel_Aleph_rel_plus_one:
  assumes "Ord(\<alpha>)"
    and types:"M(\<alpha>)" "M(d)"
  shows "d \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>succ(\<alpha>)\<^esub>\<^bsup>M\<^esup> \<longleftrightarrow> d \<lesssim>\<^bsup>M\<^esup> \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>"
  using assms Aleph_rel_succ Card_rel_is_Ord Ord_Aleph_rel lesspoll_rel_csucc_rel 
  by simp

lemma cardinal_rel_Aleph_rel [simp]: "Ord(\<alpha>) \<Longrightarrow> M(\<alpha>) \<Longrightarrow> |\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>|\<^bsup>M\<^esup> = \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>"
  using Card_rel_cardinal_rel_eq by simp

\<comment> \<open>Could be proved without using AC\<close>
lemma Aleph_rel_lesspoll_rel_increasing:
  includes Aleph_rel_intros
  assumes "M(b)" "M(a)"
  shows "a < b \<Longrightarrow> \<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>"
  using assms 
    cardinal_rel_lt_iff_lesspoll_rel[of "\<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>"]
    Aleph_rel_increasing[of a b] Card_rel_cardinal_rel_eq[of "\<aleph>\<^bsub>b\<^esub>"]
    lt_Ord lt_Ord2 Card_rel_Aleph_rel[THEN Card_rel_is_Ord] 
  by auto 

lemma uncountable_rel_iff_subset_eqpoll_rel_Aleph_rel1:
  includes Ord_dests
  assumes "M(X)"
  notes Aleph_rel_zero[simp] Card_rel_nat[simp] Aleph_rel_succ[simp]
  shows "uncountable_rel(M,X) \<longleftrightarrow> (\<exists>S[M]. S \<subseteq> X \<and> S \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)"
proof
  assume "uncountable_rel(M,X)"
  with \<open>M(X)\<close>
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^esup> X"
    using uncountable_rel_iff_nat_lt_cardinal_rel cardinal_rel_lt_csucc_rel_iff'
      cardinal_rel_le_imp_lepoll_rel by auto
  with \<open>M(X)\<close>
  obtain S where "M(S)" "S \<subseteq> X" "S \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using lepoll_rel_imp_subset_bij_rel by auto
  then
  show "\<exists>S[M]. S \<subseteq> X \<and> S \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using cardinal_rel_cong Card_rel_csucc_rel[of \<omega>] Card_rel_cardinal_rel_eq by auto
next
  note Aleph_rel_lesspoll_rel_increasing[of 1 0,simplified]
  assume "\<exists>S[M]. S \<subseteq> X \<and> S \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  moreover
  have eq:"\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> = (\<omega>\<^sup>+)\<^bsup>M\<^esup>" by auto
  moreover from calculation \<open>M(X)\<close>
  have A:"(\<omega>\<^sup>+)\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^esup> X" 
    using subset_imp_lepoll_rel[THEN [2] eq_lepoll_rel_trans, of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" _ X,
        OF eqpoll_rel_sym] by auto
  with \<open>M(X)\<close>
  show "uncountable_rel(M,X)"
    using Aleph_rel_closed
      lesspoll_rel_trans1[OF lepoll_rel_trans[OF A _] \<open>\<omega> \<prec>\<^bsup>M\<^esup> (\<omega>\<^sup>+)\<^bsup>M\<^esup>\<close>]
      lesspoll_rel_not_refl
    by auto
qed

lemma UN_if_zero: "M(K) \<Longrightarrow> (\<Union>x\<in>K. if M(x) then G ` x else 0) =(\<Union>x\<in>K. G ` x)"
  using transM[of _ K] by auto

lemma lt_Aleph_rel_imp_cardinal_rel_UN_le_nat: "function(G) \<Longrightarrow> domain(G) \<lesssim>\<^bsup>M\<^esup> \<omega> \<Longrightarrow>
   \<forall>n\<in>domain(G). |G`n|\<^bsup>M\<^esup><\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> M(G) \<Longrightarrow> |\<Union>n\<in>domain(G). G`n|\<^bsup>M\<^esup>\<le>\<omega>"
proof -
  assume "M(G)"
  moreover
  have  "w \<in> (if M(x) then G ` x else 0) \<Longrightarrow> M(x)" for w x
    by (cases "M(x)") auto
  ultimately
  interpret M_cardinal_UN_lepoll _  "\<lambda>n. if M(n) then G`n else 0" "domain(G)"
    using cardinal_lib_assms2
    by unfold_locales simp_all
  assume "function(G)"
  let ?N="domain(G)" and ?R="\<Union>n\<in>domain(G). G`n"
  assume "?N \<lesssim>\<^bsup>M\<^esup> \<omega>"
  assume Eq1: "\<forall>n\<in>?N. |G`n|\<^bsup>M\<^esup><\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  {
    fix n
    assume "n\<in>?N"
    with Eq1 \<open>M(G)\<close>
    have "|G`n|\<^bsup>M\<^esup> \<le> \<omega>"
      using le_Aleph_rel1_nat[of "|G ` n|\<^bsup>M\<^esup>"] leqpoll_rel_imp_cardinal_rel_UN_le
        UN_if_zero[of "domain(G)" G]
      by (auto dest:transM)
  }
  then
  have "n\<in>?N \<Longrightarrow> |G`n|\<^bsup>M\<^esup> \<le> \<omega>" for n .
  moreover
  note \<open>?N \<lesssim>\<^bsup>M\<^esup> \<omega>\<close> \<open>M(G)\<close>
  moreover
  have "(if M(i) then G ` i else 0) \<subseteq> G ` i" for i
    by auto
  with \<open>M(G)\<close>
  have "|if M(i) then G ` i else 0|\<^bsup>M\<^esup> \<le> |G ` i|\<^bsup>M\<^esup>" for i
  proof(cases "M(i)")
    case True
    with \<open>M(G)\<close> show ?thesis using Ord_cardinal_rel[OF apply_closed]
      by simp
  next
    case False
    then
    have "i\<notin>domain(G)"
      using transM[OF _ domain_closed[OF \<open>M(G)\<close>]] by auto
    then
    show ?thesis
      using Ord_cardinal_rel[OF apply_closed] apply_0 by simp
  qed
  ultimately
  show ?thesis
    using InfCard_rel_nat leqpoll_rel_imp_cardinal_rel_UN_le[of \<omega>]
      UN_if_zero[of "domain(G)" G]
      le_trans[of "|if M(_) then G ` _ else 0|\<^bsup>M\<^esup>" "|G ` _|\<^bsup>M\<^esup>" \<omega>]
    by auto blast
qed

lemma Aleph_rel1_eq_cardinal_rel_vimage: "f:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<^bsup>M\<^esup>\<omega> \<Longrightarrow> \<exists>n\<in>\<omega>. |f-``{n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
proof -
  assume "f:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<^bsup>M\<^esup>\<omega>"
  then
  have "function(f)" "domain(f) = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "range(f)\<subseteq>\<omega>" "f\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<omega>" "M(f)"
    using fun_rel_is_fun[OF \<open>f\<in>_\<close>] domain_of_fun fun_is_function range_fun_subset_codomain
      Aleph_rel_closed function_space_rel_char 
    by auto
  let ?G="\<lambda>n\<in>range(f). f-``{n}"
  from \<open>f:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<omega>\<close>
  have "range(f) \<subseteq> \<omega>" "domain(?G) = range(f)"
    using range_fun_subset_codomain 
    by simp_all
  from \<open>f:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<omega>\<close> \<open>M(f)\<close> \<open>range(f) \<subseteq> \<omega>\<close>
  have "M(f-``{n})" if "n \<in> range(f)" for n
    using vimage_closed that singleton_closed transM[of _ \<omega>] by auto
  with \<open>M(f)\<close> \<open>range(f) \<subseteq> \<omega>\<close>
  have "domain(?G) \<lesssim>\<^bsup>M\<^esup> \<omega>" "M(?G)"
    using subset_imp_lepoll_rel range_closed lam_closed[of "\<lambda>x . f-``{x}"] cardinal_lib_assms4
    by simp_all
  have "function(?G)" by (simp add:function_lam)
  from \<open>f:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<omega>\<close>
  have "n\<in>\<omega> \<Longrightarrow> f-``{n} \<subseteq> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" for n
    using Pi_vimage_subset by simp
  with \<open>range(f) \<subseteq> \<omega>\<close>
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> = (\<Union>n\<in>range(f). f-``{n})"
  proof (intro equalityI, intro subsetI)
    fix x
    assume "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    with \<open>f:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>\<omega>\<close> \<open>function(f)\<close> \<open>domain(f) = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
    have "x \<in> f-``{f`x}" "f`x \<in> range(f)"
      using function_apply_Pair vimage_iff apply_rangeI by simp_all
    then
    show "x \<in> (\<Union>n\<in>range(f). f-``{n})" by auto
  qed auto
  {
    assume "\<forall>n\<in>range(f). |f-``{n}|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    then
    have "\<forall>n\<in>domain(?G). |?G`n|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
      using zero_lt_Aleph_rel1 by (auto)
    with \<open>function(?G)\<close> \<open>domain(?G) \<lesssim>\<^bsup>M\<^esup> \<omega>\<close> \<open>M(?G)\<close>
    have "|\<Union>n\<in>domain(?G). ?G`n|\<^bsup>M\<^esup>\<le>\<omega>"
      using lt_Aleph_rel_imp_cardinal_rel_UN_le_nat[of ?G]
      by auto
    then
    have "|\<Union>n\<in>range(f). f-``{n}|\<^bsup>M\<^esup>\<le>\<omega>" by simp
    with \<open>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> = _\<close>
    have "|\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>|\<^bsup>M\<^esup> \<le> \<omega>" by auto
    then
    have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<le> \<omega>"
      using Card_rel_Aleph_rel Card_rel_cardinal_rel_eq
      by auto
    then
    have "False"
      using nat_lt_Aleph_rel1 by (blast dest:lt_trans2)
  }
  with \<open>range(f)\<subseteq>\<omega>\<close> \<open>M(f)\<close> 
  obtain n where "n\<in>\<omega>" "\<not>(|f -`` {n}|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)" "M(f -`` {n})"
    using vimage_closed singleton_closed nat_into_M by auto
  moreover from this
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<le> |f-``{n}|\<^bsup>M\<^esup>"
    using not_lt_iff_le Card_rel_is_Ord by simp 
  moreover
  note \<open>n\<in>\<omega> \<Longrightarrow> f-``{n} \<subseteq> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
  ultimately
  show ?thesis
    using subset_imp_le_cardinal_rel[THEN le_anti_sym, of _ "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"]
      Card_rel_Aleph_rel Card_rel_cardinal_rel_eq 
    by auto
qed

\<comment> \<open>There is some asymmetry between assumptions and conclusion
    (\<^term>\<open>eqpoll_rel\<close> versus \<^term>\<open>cardinal_rel\<close>)\<close>

lemma eqpoll_rel_Aleph_rel1_cardinal_rel_vimage:
  assumes "Z \<approx>\<^bsup>M\<^esup> (\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)" "f \<in> Z \<rightarrow>\<^bsup>M\<^esup> \<omega>" "M(Z)"
  shows "\<exists>n\<in>\<omega>. |f-``{n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
proof -
  have "M(1)" "M(\<omega>)" by simp_all
  then
  have "M(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)" using Aleph_rel_closed[of 1] by simp
  with assms \<open>M(1)\<close>
  obtain g where A:"g\<in>bij_rel(M,\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>,Z)" "M(g)"
    using eqpoll_rel_sym unfolding eqpoll_rel_def by blast
  with \<open>f : Z \<rightarrow>\<^bsup>M\<^esup> \<omega>\<close> assms
  have "M(f)" "converse(g) \<in> bij_rel(M,Z, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)" "f\<in>Z\<rightarrow>\<omega>" "g\<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>Z"
    using bij_rel_is_fun_rel bij_rel_converse_bij_rel bij_rel_char function_space_rel_char
    by simp_all
  with \<open>g\<in>bij_rel(M,\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>,Z)\<close> \<open>M(g)\<close> 
  have "f O g : \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightarrow>\<^bsup>M\<^esup> \<omega>" "M(converse(g))"
    using comp_fun[OF _ \<open>f\<in> Z\<rightarrow>_\<close>,of g] comp_closed function_space_rel_char
      converse_closed
    by simp_all
  then
  obtain n where "n\<in>\<omega>" "|(f O g)-``{n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using Aleph_rel1_eq_cardinal_rel_vimage
    by auto
  with \<open>M(f)\<close> \<open>M(converse(g))\<close>
  have "M(converse(g) `` (f -`` {n}))" "f -`` {n} \<subseteq> Z" 
    using image_comp converse_comp Pi_iff[THEN iffD1,OF \<open>f\<in>Z\<rightarrow>\<omega>\<close>] vimage_subset
    unfolding vimage_def
    using image_closed singleton_closed transM[OF \<open>n\<in>\<omega>\<close>]
    by auto
  from \<open>n\<in>\<omega>\<close> \<open>|(f O g)-``{n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> = |converse(g) `` (f -``{n})|\<^bsup>M\<^esup>"
    using image_comp converse_comp unfolding vimage_def
    by auto
  also from \<open>converse(g) \<in> bij_rel(M,Z, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)\<close> \<open>f: Z\<rightarrow>\<^bsup>M\<^esup> \<omega>\<close> \<open>M(Z)\<close> \<open>M(f)\<close> \<open>M(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)\<close>
    \<open>M(converse(g) `` (f -`` {n}))\<close>
  have "\<dots> = |f -``{n}|\<^bsup>M\<^esup>"
    using range_of_subset_eqpoll_rel[of "converse(g)" Z  _ "f -``{n}",
        OF bij_rel_is_inj_rel[OF \<open>converse(g)\<in>_\<close>] \<open>f -`` {n} \<subseteq> Z\<close>]
      cardinal_rel_cong vimage_closed[OF singleton_closed[OF transM[OF \<open>n\<in>\<omega>\<close>]],of f]
    by auto
  finally
  show ?thesis using \<open>n\<in>_\<close> by auto 
qed


subsection\<open>Applications of transfinite recursive constructions\<close>

definition
  rec_constr :: "[i,i] \<Rightarrow> i" where
  "rec_constr(f,\<alpha>) \<equiv> transrec(\<alpha>,\<lambda>a g. f`(g``a))"

text\<open>The function \<^term>\<open>rec_constr\<close> allows to perform \<^emph>\<open>recursive
     constructions\<close>: given a choice function on the powerset of some
     set, a transfinite sequence is created by successively choosing
     some new element.

     The next result explains its use.\<close>

lemma rec_constr_unfold: "rec_constr(f,\<alpha>) = f`({rec_constr(f,\<beta>). \<beta>\<in>\<alpha>})"
  using def_transrec[OF rec_constr_def, of f \<alpha>] image_lam by simp

lemma rec_constr_type: assumes "f:Pow_rel(M,G)\<rightarrow>\<^bsup>M\<^esup> G" "Ord(\<alpha>)" "M(G)" "M(\<alpha>)"
   shows "rec_constr(f,\<alpha>) \<in> G"
  using assms(2)
proof(induct rule:trans_induct)
  case (step \<beta>)
  then
  have "{rec_constr(f, x) . x \<in> \<beta>} \<in> Pow(G)" (is "?X\<in>_") by auto
  moreover
  have "M(?X)"
    sorry
  moreover from calculation \<open>M(G)\<close>
  have "?X\<in>Pow_rel(M,G)"
    using Pow_rel_char by simp
  ultimately
  have "f`?X \<in> G"
    using assms apply_type[OF fun_rel_is_fun[of f],of "Pow_rel(M,G)" G ?X]
    by auto
  then
  show ?case
    by (subst rec_constr_unfold,simp)
qed

lemma rec_constr_closed :
  assumes "f:Pow_rel(M,G)\<rightarrow>\<^bsup>M\<^esup> G" "Ord(\<alpha>)" "M(G)" "M(\<alpha>)"
  shows "M(rec_constr(f,\<alpha>))"
  using transM[OF rec_constr_type \<open>M(G)\<close>] assms by auto

text\<open>The next lemma is an application of recursive constructions.
     It works under the assumption that whenever the already constructed
     subsequence is small enough, another element can be added.\<close>

\<comment>\<open>FIXME: this should be postulated in some locale.\<close>
lemma aux : "separation(M, \<lambda>Z . cardinal_rel(M,Z)<\<gamma>)" sorry

lemma ble: "S\<in>A\<rightarrow>B \<Longrightarrow> C\<subseteq>A\<Longrightarrow> {S ` x . x\<in> C} = S``C"
  using image_function[symmetric,of S C] domain_of_fun Pi_iff by auto

lemma bounded_cardinal_rel_selection:
  includes Ord_dests
  assumes
    "\<And>Z. |Z|\<^bsup>M\<^esup> < \<gamma> \<Longrightarrow> Z \<subseteq> G \<Longrightarrow> \<exists>a\<in>G. \<forall>s\<in>Z. Q(s,a)" "b\<in>G" "Card_rel(M,\<gamma>)" "M(G)" "M(\<gamma>)"
  shows
    "\<exists>S[M]. S : \<gamma> \<rightarrow>\<^bsup>M\<^esup> G \<and> (\<forall>\<alpha> \<in> \<gamma>. \<forall>\<beta> \<in> \<gamma>.  \<alpha><\<beta> \<longrightarrow> Q(S`\<alpha>,S`\<beta>))"
proof -
  let ?cdlt\<gamma>="{Z\<in>Pow_rel(M,G) . |Z|\<^bsup>M\<^esup><\<gamma>}" \<comment> \<open>“cardinal_rel less than \<^term>\<open>\<gamma>\<close>”\<close>
    and ?inQ="\<lambda>Y.{a\<in>G. \<forall>s\<in>Y. Q(s,a)}"
  from \<open>M(G)\<close>
  have "M(?cdlt\<gamma>)" using Pow_rel_closed separation_closed aux by simp
  from assms
  have H:"\<exists>a. a \<in> ?inQ(Y)" if "Y\<in>?cdlt\<gamma>" for Y
  proof -
    {
      fix Y
      assume "Y\<in>?cdlt\<gamma>"
      then
      have A:"Y\<in>Pow_rel(M,G)" "|Y|\<^bsup>M\<^esup><\<gamma>" by simp_all
      then
      have "Y\<subseteq>G" using Pow_rel_char[OF \<open>M(G)\<close>] by simp
      with A
      obtain a where "a\<in>G" "\<forall>s\<in>Y. Q(s,a)"
        using assms(1) by force
      with \<open>M(G)\<close>
      have "\<exists>a. a \<in> ?inQ(Y)" by auto
    }
    then show ?thesis using that by simp
  qed
  then
  have "\<exists>f[M]. f \<in> Pi_rel(M,?cdlt\<gamma>,?inQ) \<and> f \<in> Pi(?cdlt\<gamma>,?inQ)" 
  proof - 
    interpret M_Pi_assumptions_choice M  ?cdlt\<gamma> ?inQ
      using \<open>M(?cdlt\<gamma>)\<close>
      apply (unfold_locales,simp_all)
      sorry
    show ?thesis using AC_Pi_rel Pi_rel_char H by auto
    qed
  then
  obtain f where f_type:"f \<in> Pi_rel(M,?cdlt\<gamma>,?inQ)" "f \<in> Pi(?cdlt\<gamma>,?inQ)" and "M(f)"
    by auto
  moreover
  define Cb where "Cb \<equiv> \<lambda>_\<in>Pow_rel(M,G)-?cdlt\<gamma>. b"
  moreover from \<open>b\<in>G\<close> \<open>M(?cdlt\<gamma>)\<close> \<open>M(G)\<close>
  have "Cb \<in> Pow_rel(M,G)-?cdlt\<gamma> \<rightarrow> G" "M(Cb)"
    using lam_closed[of "\<lambda>_.b" "Pow_rel(M,G)-?cdlt\<gamma>"]
      tag_replacement transM[OF \<open>b\<in>G\<close>]
      Diff_closed Pow_rel_closed 
    unfolding Cb_def by auto
  moreover
  note \<open>Card_rel(M,\<gamma>)\<close>
  ultimately
  have "f \<union> Cb : (\<Prod>x\<in>Pow_rel(M,G). ?inQ(x) \<union> G)" using
      fun_Pi_disjoint_Un[ of f ?cdlt\<gamma>  ?inQ Cb "Pow_rel(M,G)-?cdlt\<gamma>" "\<lambda>_.G"]
      Diff_partition[of "{Z\<in>Pow_rel(M,G). |Z|\<^bsup>M\<^esup><\<gamma>}" "Pow_rel(M,G)", OF Collect_subset]
    by auto
  moreover
  have "?inQ(x) \<union> G = G" for x by auto
  moreover from calculation 
  have "f \<union> Cb : Pow_rel(M,G) \<rightarrow> G" 
    using function_space_rel_char by simp
  ultimately
  have "f \<union> Cb : Pow_rel(M,G) \<rightarrow>\<^bsup>M\<^esup> G"
    using function_space_rel_char \<open>M(f)\<close> \<open>M(Cb)\<close> Pow_rel_closed \<open>M(G)\<close>
    by auto
  define S where "S\<equiv>\<lambda>\<alpha>\<in>\<gamma>. rec_constr(f \<union> Cb, \<alpha>)"
  from \<open>f \<union> Cb: Pow_rel(M,G) \<rightarrow>\<^bsup>M\<^esup> G\<close> \<open>Card_rel(M,\<gamma>)\<close> \<open>M(\<gamma>)\<close>
  have "S : \<gamma> \<rightarrow> G" "M(S)"
    using Ord_in_Ord Card_rel_is_Ord
    unfolding S_def
    sorry
  moreover
  have "\<forall>\<alpha>\<in>\<gamma>. \<forall>\<beta>\<in>\<gamma>. \<alpha> < \<beta> \<longrightarrow> Q(S ` \<alpha>, S ` \<beta>)"
  proof (intro ballI impI)
    fix \<alpha> \<beta>
    assume "\<beta>\<in>\<gamma>"
    with \<open>Card_rel(M,\<gamma>)\<close> \<open>M(S)\<close>
    have "\<beta>\<subseteq>\<gamma>" "M(S``\<beta>)" 
      using transM[OF \<open>\<beta>\<in>\<gamma>\<close> \<open>M(\<gamma>)\<close>] image_closed 
      sorry
    with \<open>\<beta>\<in>_\<close> \<open>Card_rel(M,\<gamma>)\<close> \<open>M(\<gamma>)\<close>
    have "{rec_constr(f \<union> Cb, x) . x\<in>\<beta>} = {S`x . x \<in> \<beta>}"
      using Ord_trans[OF _ _ Card_rel_is_Ord, of _ \<beta> \<gamma>]
      unfolding S_def
      by auto
    moreover from \<open>\<beta>\<in>\<gamma>\<close> \<open>S : \<gamma> \<rightarrow> G\<close> \<open>Card_rel(M,\<gamma>)\<close> \<open>M(\<gamma>)\<close> \<open>M(S``\<beta>)\<close>
    have "{S`x . x \<in> \<beta>} \<subseteq> G" "M({S`x . x \<in> \<beta>})"
      using Ord_trans[OF _ _ Card_rel_is_Ord, of _ \<beta> \<gamma>]
        apply_type[of S \<gamma> "\<lambda>_. G"] ble[OF \<open>S\<in>_\<close> \<open>\<beta>\<subseteq>_\<close>]
      sorry
    moreover from \<open>Card_rel(M,\<gamma>)\<close> \<open>\<beta>\<in>\<gamma>\<close> \<open>S\<in>_\<close>
    have "|{S`x . x \<in> \<beta>}|\<^bsup>M\<^esup> < \<gamma>"
      using cardinal_rel_RepFun_le[of \<beta>]  Ord_in_Ord Ord_cardinal_rel
        lt_trans1[of "|{S`x . x \<in> \<beta>}|\<^bsup>M\<^esup>" "|\<beta>|\<^bsup>M\<^esup>" \<gamma>]
        Card_rel_lt_iff[THEN iffD2, of \<beta> \<gamma>, OF _ _ _ _ ltI]
        Card_rel_is_Ord 
      sorry
    moreover
    have "\<forall>x\<in>\<beta>. Q(S`x, f ` {S`x . x \<in> \<beta>})"
    proof -
      from calculation and f_type
      have "f ` {S`x . x \<in> \<beta>} \<in> {a\<in>G. \<forall>x\<in>\<beta>. Q(S`x,a)}"
        using apply_type[of f ?cdlt\<gamma> ?inQ "{S`x . x \<in> \<beta>}"]
         Pow_rel_char[OF \<open>M(G)\<close>]
        by auto
      then
      show ?thesis by simp
    qed
    moreover
    assume "\<alpha>\<in>\<gamma>" "\<alpha> < \<beta>"
    moreover from this
    have "\<alpha>\<in>\<beta>" using ltD by simp
    moreover
    note \<open>\<beta>\<in>\<gamma>\<close> \<open>Cb \<in> Pow_rel(M,G)-?cdlt\<gamma> \<rightarrow> G\<close>
    ultimately
    show "Q(S ` \<alpha>, S ` \<beta>)"
      using fun_disjoint_apply1[of "{S`x . x \<in> \<beta>}" Cb f]
        domain_of_fun[of Cb] ltD[of \<alpha> \<beta>]
       by (subst (2) S_def, auto) (subst rec_constr_unfold, auto)
   qed
   moreover
   note \<open>M(G)\<close> \<open>M(\<gamma>)\<close>
   ultimately
  show ?thesis using function_space_rel_char by auto
qed

text\<open>The following basic result can, in turn, be proved by a
     bounded-cardinal_rel selection.\<close>
lemma Infinite_iff_lepoll_rel_nat: "M(Z) \<Longrightarrow> Infinite(Z) \<longleftrightarrow> \<omega> \<lesssim>\<^bsup>M\<^esup> Z"
proof
  assume "Infinite(Z)" "M(Z)"
  then
  obtain b where "b\<in>Z"
    using Infinite_not_empty by auto
  {
    fix Y
    assume "|Y|\<^bsup>M\<^esup> < \<omega>" "M(Y)"
    then
    have "Finite(Y)"
      using Finite_cardinal_rel_iff' ltD nat_into_Finite by auto
    with \<open>Infinite(Z)\<close>
    have "Z \<noteq> Y" by auto
  }
  moreover
  have A: "(\<And>W. |W|\<^bsup>M\<^esup> < \<omega> \<Longrightarrow> W \<subseteq> Z \<Longrightarrow> \<exists>a\<in>Z. \<forall>s\<in>W. s \<noteq> a)"
    sorry
  moreover from \<open>b\<in>Z\<close> \<open>M(Z)\<close>
  obtain S where "S : \<omega> \<rightarrow>\<^bsup>M\<^esup> Z" "M(S)" "\<forall>\<alpha>\<in>\<omega>. \<forall>\<beta>\<in>\<omega>. \<alpha> < \<beta> \<longrightarrow> S`\<alpha> \<noteq> S`\<beta>"
    using bounded_cardinal_rel_selection[OF A \<open>b\<in>Z\<close> Card_rel_nat]
    by blast
  moreover from this
  have "\<alpha> \<in> \<omega> \<Longrightarrow> \<beta> \<in> \<omega> \<Longrightarrow> \<alpha>\<noteq>\<beta> \<Longrightarrow> S`\<alpha> \<noteq> S`\<beta>" for \<alpha> \<beta>
    by (rule_tac lt_neq_symmetry[of "\<omega>" "\<lambda>\<alpha> \<beta>. S`\<alpha> \<noteq> S`\<beta>"])
      auto
  moreover from this \<open>S\<in>_\<close> \<open>M(Z)\<close>
  have "S\<in>inj(\<omega>,Z)" using function_space_rel_char unfolding inj_def by auto
  ultimately
  show "\<omega> \<lesssim>\<^bsup>M\<^esup> Z"
    unfolding lepoll_rel_def using inj_rel_char \<open>M(Z)\<close> by auto
next
  assume "\<omega> \<lesssim>\<^bsup>M\<^esup> Z" "M(Z)"
  then
  show "Infinite(Z)" using lepoll_rel_nat_imp_Infinite by simp
qed

lemma Infinite_InfCard_rel_cardinal_rel: "M(Z) \<Longrightarrow> Infinite(Z) \<Longrightarrow> InfCard_rel(M,|Z|\<^bsup>M\<^esup>)"
  using lepoll_rel_eq_trans eqpoll_rel_sym lepoll_rel_nat_imp_Infinite
    Infinite_iff_lepoll_rel_nat Inf_Card_rel_is_InfCard_rel cardinal_rel_eqpoll_rel
  by simp

lemma Finite_to_one_rel_surj_rel_imp_cardinal_rel_eq:
  assumes "F \<in> Finite_to_one_rel(M,Z,Y) \<inter> surj_rel(M,Z,Y)" "Infinite(Z)" "M(Z)" "M(Y)"
  shows "|Y|\<^bsup>M\<^esup> = |Z|\<^bsup>M\<^esup>"
proof -
  note \<open>M(Z)\<close> \<open>M(Y)\<close>
  moreover from this assms
  have "M(F)" "F \<in> Z \<rightarrow> Y"
    unfolding Finite_to_one_rel_def
    using function_space_rel_char by simp_all
  moreover
  have "M(y) \<Longrightarrow> M({x\<in>Z . F`x = y})" for y
  proof(cases "y\<in>Y")
    case True
    with \<open>M(Y)\<close> \<open>M(F)\<close>
    show ?thesis
      using vimage_fun_sing[OF \<open>F\<in>Z\<rightarrow>Y\<close> \<open>y\<in>Y\<close>] vimage_closed transM[OF _ \<open>M(Y)\<close>]
      by auto
  next
    case False
    then
    have "{x \<in> Z . F ` x = y} = 0"
      using apply_type[OF \<open>F\<in>Z\<rightarrow>Y\<close>] by auto
    then
    show ?thesis by simp
  qed
  moreover
  have "w \<in> (if M(y) then {x\<in>Z . F`x = y} else 0) \<Longrightarrow> M(y)" for w y
    by (cases "M(y)") auto
  ultimately
  interpret M_cardinal_UN_lepoll _ "\<lambda>y. if M(y) then {x\<in>Z . F`x = y} else 0" Y
    using cardinal_lib_assms3
    by unfold_locales (auto dest:transM simp del:mem_inj_abs)
  from \<open>F\<in>Z\<rightarrow>Y\<close>
  have "Z = (\<Union>y\<in>Y. {x\<in>Z . F`x = y})"
    using apply_type by auto
  then
  show ?thesis
  proof (cases "Finite(Y)")
    case True
    with \<open>Z = (\<Union>y\<in>Y. {x\<in>Z . F`x = y})\<close> and assms and \<open>F\<in>Z\<rightarrow>Y\<close>
    show ?thesis
      using Finite_RepFun[THEN [2] Finite_Union, of Y "\<lambda>y. {x\<in>Z . F`x = y}"]
      sorry
  next
    case False
    moreover from this \<open>M(Y)\<close>
    have "Y \<lesssim>\<^bsup>M\<^esup> |Y|\<^bsup>M\<^esup>"
      using cardinal_rel_eqpoll_rel eqpoll_rel_sym eqpoll_rel_imp_lepoll_rel by auto
    moreover
    note assms
    moreover from calculation 
    have "y \<in> Y \<Longrightarrow> |{x\<in>Z . F`x = y}|\<^bsup>M\<^esup> \<le> |Y|\<^bsup>M\<^esup>" for y
      using Infinite_imp_nats_lepoll_rel[THEN lepoll_rel_imp_cardinal_rel_le, of Y
          "|{x\<in>Z . F`x = y}|\<^bsup>M\<^esup>"] cardinal_rel_idem sorry
    ultimately
    have "|\<Union>y\<in>Y. {x\<in>Z . F`x = y}|\<^bsup>M\<^esup> \<le> |Y|\<^bsup>M\<^esup>"
      using leqpoll_rel_imp_cardinal_rel_UN_le
        Infinite_InfCard_rel_cardinal_rel[of Y] sorry
    moreover from \<open>F \<in> Finite_to_one_rel(M,Z,Y) \<inter> surj_rel(M,Z,Y)\<close> \<open>M(Z)\<close> \<open>M(F)\<close> \<open>M(Y)\<close>
    have "|Y|\<^bsup>M\<^esup> \<le> |Z|\<^bsup>M\<^esup>"
      using surj_rel_implies_cardinal_rel_le by auto
    moreover
    note \<open>Z = (\<Union>y\<in>Y. {x\<in>Z . F`x = y})\<close>
    ultimately
    show ?thesis
      using le_anti_sym by auto
  qed
qed

lemma cardinal_rel_map_Un:
  assumes "Infinite(X)" "Finite(b)" "M(X)" "M(b)"
  shows "|{a \<union> b . a \<in> X}|\<^bsup>M\<^esup> = |X|\<^bsup>M\<^esup>"
proof -
  have "(\<lambda>a\<in>X. a \<union> b) \<in> Finite_to_one_rel(M,X,{a \<union> b . a \<in> X})"
    "(\<lambda>a\<in>X. a \<union> b) \<in>  surj_rel(M,X,{a \<union> b . a \<in> X})"
    "M({a \<union> b . a \<in> X})"
    unfolding def_surj_rel
  proof
    fix d
    have "Finite({a \<in> X . a \<union> b = d})" (is "Finite(?Y(b,d))")
      using \<open>Finite(b)\<close>
    proof (induct arbitrary:d)
      case 0
      have "{a \<in> X . a \<union> 0 = d} = (if d\<in>X then {d} else 0)"
        by auto
      then
      show ?case by simp
    next
      case (cons c b)
      from \<open>c \<notin> b\<close>
      have "?Y(cons(c,b),d) \<subseteq> (if c\<in>d then ?Y(b,d) \<union> ?Y(b,d-{c}) else 0)"
        by auto
      with cons
      show ?case
        using subset_Finite
        by simp
    qed
    moreover
    assume "d \<in> {x \<union> b . x \<in> X}"
    ultimately
    show "Finite({a \<in> X . M(a) \<and> (\<lambda>x\<in>X. x \<union> b) ` a = d})"
      using subset_Finite[of "{a \<in> X . M(a) \<and> (\<lambda>x\<in>X. x \<union> b) ` a = d}"
          "{a \<in> X . (\<lambda>x\<in>X. x \<union> b) ` a = d}"] by auto
  next
    note \<open>M(X)\<close> \<open>M(b)\<close>
    moreover
    show "M(\<lambda>a\<in>X. a \<union> b)" 
      using lam_closed[of "\<lambda> x . x\<union>b",OF _ \<open>M(X)\<close>] Un_closed[OF transM[OF _ \<open>M(X)\<close>] \<open>M(b)\<close>]
        tag_union_replacement[OF \<open>M(b)\<close>]
      by simp
    moreover from this
    have "{a \<union> b . a \<in> X} = (\<lambda>x\<in>X. x \<union> b) `` X"
      using image_lam by simp
    with calculation
    show "M({a \<union> b . a \<in> X})" by auto
    moreover from calculation
    show "(\<lambda>a\<in>X. a \<union> b) \<in> X \<rightarrow>\<^bsup>M\<^esup> {a \<union> b . a \<in> X}"
      using function_space_rel_char by (auto intro:lam_funtype)
    ultimately
    show "(\<lambda>a\<in>X. a \<union> b) \<in> surj\<^bsup>M\<^esup>(X,{a \<union> b . a \<in> X})" "M({a \<union> b . a \<in> X})"
      using surj_rel_char function_space_rel_char
      unfolding surj_def by auto
  next
  qed (simp add:\<open>M(X)\<close>)
  moreover from assms this
  show ?thesis
    using Finite_to_one_rel_surj_rel_imp_cardinal_rel_eq by simp
qed

end (* M_cardinal_library *)

end