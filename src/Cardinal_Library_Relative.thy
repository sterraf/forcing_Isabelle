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
  assumes "M(S)" "M(A)"
  shows "|{S`a . a\<in>A}|\<^bsup>M\<^esup> \<le> |A|\<^bsup>M\<^esup>"
proof -
  note assms
  moreover from this
  have "(\<lambda>x\<in>A. S`x) \<in> surj_rel(M,A, {S`a . a\<in>A})"
    using def_surj_rel lam_funtype  sorry (* by auto *)
  moreover from assms
  have "M(\<lambda>x\<in>A. S ` x)" "M({S ` a . a \<in> A})" sorry
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

lemmas inj_rel_is_fun = inj_is_fun[OF mem_inj_abs[THEN iffD1]]

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

\<comment> \<open>This is not the correct version, since we'll gonna closure under
    \<^term>\<open>\<Union>x\<in>A. B(x)\<close> for several \<^term>\<open>A\<close> and \<^term>\<open>B\<close>.\<close>
locale M_cardinal_UN_lepoll = M_library +
  k:M_cardinal_UN _ K +
  j:M_cardinal_UN _ J for J K
begin

\<comment>\<open>FIXME: this "LEQpoll" should be "LEPOLL"; same correction in Delta System\<close>
lemma leqpoll_rel_imp_cardinal_rel_UN_le:
  notes [dest] = InfCard_is_Card Card_is_Ord
  assumes "InfCard\<^bsup>M\<^esup>(K)" "J \<lesssim>\<^bsup>M\<^esup> K" "\<And>i. i\<in>J \<Longrightarrow> |X(i)|\<^bsup>M\<^esup> \<le> K"
  shows "|\<Union>i\<in>J. X(i)|\<^bsup>M\<^esup> \<le> K"
proof -
  from \<open>J \<lesssim>\<^bsup>M\<^esup> K\<close>
  obtain f where "f \<in> inj_rel(M,J,K)" "M(f)" by blast
  have "M(K)" "M(J)" "\<And>w x. w \<in> X(x) \<Longrightarrow> M(x)"
    using k.Pi_assumptions j.Pi_assumptions j.X_witness_in_M by simp_all
  note inM = \<open>M(f)\<close> this
  define Y where "Y(k) \<equiv> if k\<in>range(f) then X(converse(f)`k) else 0" for k
  have "i\<in>J \<Longrightarrow> f`i \<in> K" for i
    using inj_rel_is_fun[OF _ _ _ \<open>f \<in> inj\<^bsup>M\<^esup>(J,K)\<close>] apply_type
      function_space_rel_char by (auto simp add:inM)
  from inM
  interpret y:M_Pi_assumptions _ K Y
    sorry
  from inM
  interpret y:M_Pi_assumptions_choice _ K Y
    sorry
  interpret y:M_cardinal_UN _ K Y
    using k.lam_m_replacement k.inj_replacement
    apply unfold_locales
(*   proof -
    fix w x
    assume "w\<in>Y(x)"
    then
    have "x\<in>range(f)"
      unfolding Y_def by (cases "x\<in>range(f)", auto)
    with \<open>M(f)\<close>
    show "M(x)" by (auto dest:transM)
  qed
 *) sorry
  have "(\<Union>i\<in>J. X(i)) \<subseteq> (\<Union>i\<in>K. Y(i))"
  proof (standard, elim UN_E)
    fix x i
    assume "i\<in>J" "x\<in>X(i)"
    with \<open>f \<in> inj_rel(M,J,K)\<close> \<open>i\<in>J \<Longrightarrow> f`i \<in> K\<close>
    have "x \<in> Y(f`i)" "f`i \<in> K"
      unfolding Y_def
      using inj_is_fun right_inverse
      by (auto simp add:inM intro: apply_rangeI)
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
    using inj_rel_converse_fun[OF \<open>f \<in> inj_rel(M,J,K)\<close>]
      range_fun_subset_codomain function_space_rel_char by simp
  ultimately
  show "|\<Union>i\<in>J. X(i)|\<^bsup>M\<^esup> \<le> K"
    using InfCard_rel_is_Card_rel[THEN Card_rel_is_Ord,THEN Ord_0_le, of K]
    by (rule_tac le_trans[OF _ y.cardinal_rel_UN_le])
      (auto intro:Ord_0_le simp:Y_def)+
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

lemma inj_rel_bij_rel_range: "f \<in> inj\<^bsup>M\<^esup>(A,B) \<Longrightarrow>M(A) \<Longrightarrow> M(B) \<Longrightarrow> f \<in> bij\<^bsup>M\<^esup>(A,range(f))"
  using bij_rel_char inj_rel_char inj_bij_range by force

lemma bij_rel_is_inj_rel: "f \<in> bij\<^bsup>M\<^esup>(A,B) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> f \<in> inj\<^bsup>M\<^esup>(A,B)"
  unfolding bij_rel_def by simp

lemma inj_rel_weaken_type: "[| f \<in> inj\<^bsup>M\<^esup>(A,B);  B\<subseteq>D; M(A); M(B); M(D) |] ==> f \<in> inj\<^bsup>M\<^esup>(A,D)"
  using inj_rel_char inj_rel_is_fun inj_weaken_type by auto

lemma bij_rel_converse_bij_rel [TC]: "f \<in> bij\<^bsup>M\<^esup>(A,B)  \<Longrightarrow> M(A) \<Longrightarrow> M(B) ==> converse(f): bij\<^bsup>M\<^esup>(B,A)"
  using bij_rel_char by force

lemma bij_rel_is_fun: "f \<in> bij\<^bsup>M\<^esup>(A,B) \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow>  f \<in> A\<rightarrow>\<^bsup>M\<^esup>B"
  using bij_rel_char mem_function_space_rel_abs bij_is_fun by simp

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

lemma lepoll_rel_countable: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<lesssim>\<^bsup>M\<^esup> Y \<Longrightarrow> countable_rel(M,Y) \<Longrightarrow> countable_rel(M,X)"
  using lepoll_rel_trans[of X Y] by blast

\<comment> \<open>Next lemma can be proved without using AC\<close>
lemma surj_rel_countable: 
  "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> M(f) \<Longrightarrow> countable_rel(M,X) \<Longrightarrow> f \<in> surj_rel(M,X,Y) \<Longrightarrow> countable_rel(M,Y)"
  using surj_rel_implies_cardinal_rel_le[of f X Y, THEN le_trans]
    countable_rel_iff_cardinal_rel_le_nat by simp

lemma Finite_imp_countable: "M(X) \<Longrightarrow> Finite_rel(M,X) \<Longrightarrow> countable_rel(M,X)"
  unfolding Finite_rel_def
  by (auto intro:InfCard_rel_nat nats_le_InfCard_rel[of _ \<omega>,
        THEN le_imp_lepoll_rel] dest!:eq_lepoll_rel_trans[of X _ \<omega>] )

lemma countable_rel_imp_countable_rel_UN:
  assumes "M(J)" "countable_rel(M,J)" "\<And>i. i\<in>J \<Longrightarrow> countable_rel(M,X(i))"
  shows "countable_rel(M,\<Union>i\<in>J. X(i))"
using assms M_cardinal_UN_lepoll.leqpoll_rel_imp_cardinal_rel_UN_le[where X="\<lambda>c . c"] InfCard_rel_nat
    countable_rel_iff_cardinal_rel_le_nat 
  sorry
 
lemma countable_rel_union_countable:
  assumes "M(C)" "\<And>x. x \<in> C \<Longrightarrow> countable_rel(M,x)" "countable_rel(M,C)"
  shows "countable_rel(M,\<Union>C)"
  using assms countable_rel_imp_countable_rel_UN[where X="\<lambda>c . c"] by simp

end (* M_library *)

abbreviation
  uncountable_rel :: "[i\<Rightarrow>o,i]\<Rightarrow>o" where
  "uncountable_rel(M,X) \<equiv> \<not> countable_rel(M,X)"

context M_library
begin

lemma uncountable_rel_iff_nat_lt_cardinal_rel:
  "M(X) \<Longrightarrow> uncountable_rel(M,X) \<longleftrightarrow> \<omega> < |X|\<^bsup>M\<^esup>"
  using countable_rel_iff_cardinal_rel_le_nat not_le_iff_lt by simp

lemma uncountable_rel_not_empty: "uncountable_rel(M,X) \<Longrightarrow> X \<noteq> 0"
  using empty_lepoll_relI by auto

lemma uncountable_rel_imp_Infinite: "M(X) \<Longrightarrow> uncountable_rel(M,X) \<Longrightarrow> Infinite(X)"
  using uncountable_rel_iff_nat_lt_cardinal_rel[of X] lepoll_rel_nat_imp_Infinite[of X]
    cardinal_rel_le_imp_lepoll_rel[of \<omega> X] leI
  by simp

lemma uncountable_rel_not_subset_countable:
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
  shows "a < b \<Longrightarrow> \<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup> \<prec> \<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>"
  using cardinal_rel_lt_iff_lesspoll_rel[of "\<aleph>\<^bsub>a\<^esub>" "\<aleph>\<^bsub>b\<^esub>"] Card_rel_cardinal_rel_eq[of "\<aleph>\<^bsub>b\<^esub>"]
    lt_Ord lt_Ord2 Card_rel_Aleph_rel[THEN Card_rel_is_Ord] sorry

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
  assume "\<exists>S[M]. S \<subseteq> X \<and> S \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  with \<open>M(X)\<close>
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^esup> X"
    using subset_imp_lepoll_rel[THEN [2] eq_lepoll_rel_trans, of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" _ X,
        OF eqpoll_rel_sym] by auto
  with \<open>M(X)\<close>
  show "uncountable_rel(M,X)"
    using Aleph_rel_lesspoll_rel_increasing[of 1 0,simplified] Aleph_rel_closed[of 1]
      lesspoll_rel_trans1[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" X "(\<omega>\<^sup>+)\<^bsup>M\<^esup>" ,simplified] 
      lepoll_rel_trans[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" X \<omega>,simplified]
    unfolding countable_rel_def sorry
qed

lemma lt_Aleph_rel_imp_cardinal_rel_UN_le_nat: "function(G) \<Longrightarrow> domain(G) \<lesssim>\<^bsup>M\<^esup> \<omega> \<Longrightarrow>
   \<forall>n\<in>domain(G). |G`n|<\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> |\<Union>n\<in>domain(G). G`n|\<le>\<omega>"
proof -
  assume "function(G)"
  let ?N="domain(G)" and ?R="\<Union>n\<in>domain(G). G`n"
  assume "?N \<lesssim>\<^bsup>M\<^esup> \<omega>"
  assume Eq1: "\<forall>n\<in>?N. |G`n|<\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  {
    fix n
    assume "n\<in>?N"
    with Eq1 have "|G`n|\<^bsup>M\<^esup> \<le> \<omega>"
      using le_Aleph_rel1_nat leqpoll_imp_cardinal_UN_le
      sorry
  }
  then
  have "n\<in>?N \<Longrightarrow> |G`n|\<^bsup>M\<^esup> \<le> \<omega>" for n .
  with \<open>?N \<lesssim>\<^bsup>M\<^esup> \<omega>\<close>
  show ?thesis
    using InfCard_rel_nat leqpoll_rel_imp_cardinal_rel_UN_le sorry
qed

lemma Aleph_rel1_eq_cardinal_rel_vimage: "f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>\<omega> \<Longrightarrow> \<exists>n\<in>\<omega>. |f-``{n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>"
proof -
  assume "f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>\<omega>"
  then
  have "function(f)" "domain(f) = \<aleph>\<^bsub>1\<^esub>" "range(f)\<subseteq>\<omega>"
    by (simp_all add: domain_of_fun fun_is_function range_fun_subset_codomain)
  let ?G="\<lambda>n\<in>range(f). f-``{n}"
  from \<open>f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>\<omega>\<close>
  have "range(f) \<subseteq> \<omega>" by (simp add: range_fun_subset_codomain)
  then
  have "domain(?G) \<lesssim>\<^bsup>M\<^esup> \<omega>"
    using subset_imp_lepoll_rel sorry
  have "function(?G)" by (simp add:function_lam)
  from \<open>f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>\<omega>\<close>
  have "n\<in>\<omega> \<Longrightarrow> f-``{n} \<subseteq> \<aleph>\<^bsub>1\<^esub>" for n
    using Pi_vimage_subset by simp
  with \<open>range(f) \<subseteq> \<omega>\<close>
  have "\<aleph>\<^bsub>1\<^esub> = (\<Union>n\<in>range(f). f-``{n})"
  proof (intro equalityI, intro subsetI)
    fix x
    assume "x \<in> \<aleph>\<^bsub>1\<^esub>"
    with \<open>f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>\<omega>\<close> \<open>function(f)\<close> \<open>domain(f) = \<aleph>\<^bsub>1\<^esub>\<close>
    have "x \<in> f-``{f`x}" "f`x \<in> range(f)"
      using function_apply_Pair vimage_iff apply_rangeI by simp_all
    then
    show "x \<in> (\<Union>n\<in>range(f). f-``{n})" by auto
  qed auto
  {
    assume "\<forall>n\<in>range(f). |f-``{n}|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>"
    then
    have "\<forall>n\<in>domain(?G). |?G`n|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>"
      using zero_lt_Aleph_rel1 by (auto)
    with \<open>function(?G)\<close> \<open>domain(?G) \<lesssim>\<^bsup>M\<^esup> \<omega>\<close>
    have "|\<Union>n\<in>domain(?G). ?G`n|\<le>\<omega>"
      using lt_Aleph_rel_imp_cardinal_rel_UN_le_nat sorry
    then
    have "|\<Union>n\<in>range(f). f-``{n}|\<le>\<omega>" by simp
    with \<open>\<aleph>\<^bsub>1\<^esub> = _\<close>
    have "|\<aleph>\<^bsub>1\<^esub>|\<^bsup>M\<^esup> \<le> \<omega>" sorry
    then
    have "\<aleph>\<^bsub>1\<^esub> \<le> \<omega>"
      using Card_rel_Aleph_rel Card_rel_cardinal_rel_eq
      sorry
    then
    have "False"
      using nat_lt_Aleph_rel1 (* by (blast dest:lt_trans2) *)
      sorry
  }
  with \<open>range(f)\<subseteq>\<omega>\<close>
  obtain n where "n\<in>\<omega>" "\<not>(|f -`` {n}|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>)"
    by blast
  moreover from this
  have "\<aleph>\<^bsub>1\<^esub> \<le> |f-``{n}|"
    using not_lt_iff_le Card_rel_is_Ord sorry
  moreover
  note \<open>n\<in>\<omega> \<Longrightarrow> f-``{n} \<subseteq> \<aleph>\<^bsub>1\<^esub>\<close>
  ultimately
  show ?thesis
    using subset_imp_le_cardinal_rel[THEN le_anti_sym, of _ "\<aleph>\<^bsub>1\<^esub>"]
      Card_rel_Aleph_rel Card_rel_cardinal_rel_eq sorry
qed

\<comment> \<open>There is some asymmetry between assumptions and conclusion
    (\<^term>\<open>eqpoll_rel\<close> versus \<^term>\<open>cardinal_rel\<close>)\<close>

lemma eqpoll_rel_Aleph_rel1_cardinal_rel_vimage:
  assumes "Z \<approx>\<^bsup>M\<^esup> (\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)" "f \<in> Z \<rightarrow> \<omega>" "M(Z)"
  shows "\<exists>n\<in>\<omega>. |f-``{n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
proof -
  have "M(1)" by simp
  note Aleph_rel_closed[of 1] 
  with assms \<open>M(1)\<close>
  obtain g where "g\<in>bij_rel(M,\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>,Z)" "M(g)"
    using eqpoll_rel_sym unfolding eqpoll_rel_def by blast
  with \<open>f : Z \<rightarrow> \<omega>\<close> assms
  have "f O g : \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightarrow> \<omega>" "converse(g) \<in> bij_rel(M,Z, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)"
    using bij_rel_is_fun comp_fun bij_rel_converse_bij_rel 
    sorry
  then
  obtain n where "n\<in>\<omega>" "|(f O g)-``{n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using Aleph_rel1_eq_cardinal_rel_vimage 
    sorry
  then
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> = |converse(g) `` (f -``{n})|"
    using image_comp converse_comp
    unfolding vimage_def 
    sorry
  also from \<open>converse(g) \<in> bij_rel(M,Z, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)\<close> \<open>f: Z\<rightarrow> \<omega>\<close>
  have "\<dots> = |f -``{n}|"
    using range_of_subset_eqpoll_rel[of "converse(g)" Z  _ "f -``{n}"]
      bij_rel_is_inj_rel cardinal_rel_cong bij_rel_is_fun eqpoll_rel_sym Pi_vimage_subset
    sorry
  finally
  show ?thesis using \<open>n\<in>\<omega>\<close> sorry
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

lemma rec_constr_type: assumes "f:Pow_rel(M,G)\<rightarrow> G" "Ord(\<alpha>)"
  shows "rec_constr(f,\<alpha>) \<in> G"
  using assms(2,1)
(*   by (induct rule:trans_induct)
    (subst rec_constr_unfold, rule apply_type[of f "Pow_rel(M,G)" "\<lambda>_. G"], auto)
 *)
  sorry

text\<open>The next lemma is an application of recursive constructions.
     It works under the assumption that whenever the already constructed
     subsequence is small enough, another element can be added.\<close>

lemma bounded_cardinal_rel_selection:
  includes Ord_dests
  assumes
    "\<And>Z. |Z|\<^bsup>M\<^esup> < \<gamma> \<Longrightarrow> Z \<subseteq> G \<Longrightarrow> \<exists>a\<in>G. \<forall>s\<in>Z. Q(s,a)" "b\<in>G" "Card_rel(M,\<gamma>)"
  shows
    "\<exists>S. S : \<gamma> \<rightarrow> G \<and> (\<forall>\<alpha> \<in> \<gamma>. \<forall>\<beta> \<in> \<gamma>.  \<alpha><\<beta> \<longrightarrow> Q(S`\<alpha>,S`\<beta>))"
proof -
  let ?cdlt\<gamma>="{Z\<in>Pow_rel(M,G) . |Z|<\<gamma>}" \<comment> \<open>“cardinal_rel less than \<^term>\<open>\<gamma>\<close>”\<close>
    and ?inQ="\<lambda>Y.{a\<in>G. \<forall>s\<in>Y. Q(s,a)}"
  from assms
  have "\<forall>Y \<in> ?cdlt\<gamma>. \<exists>a. a \<in> ?inQ(Y)"
(*     by blast *)
  sorry
  then
  have "\<exists>f. f \<in> Pi(?cdlt\<gamma>,?inQ)"
    using AC_ball_Pi[of ?cdlt\<gamma> ?inQ] by simp
  then
  obtain f where f_type:"f \<in> Pi(?cdlt\<gamma>,?inQ)"
    by auto
  moreover
  define Cb where "Cb \<equiv> \<lambda>_\<in>Pow_rel(M,G)-?cdlt\<gamma>. b"
  moreover from \<open>b\<in>G\<close>
  have "Cb \<in> Pow_rel(M,G)-?cdlt\<gamma> \<rightarrow> G"
    unfolding Cb_def by simp
  moreover
  note \<open>Card_rel(M,\<gamma>)\<close>
  ultimately
  have "f \<union> Cb : (\<Prod>x\<in>Pow_rel(M,G). ?inQ(x) \<union> G)" using
      fun_Pi_disjoint_Un[ of f ?cdlt\<gamma>  ?inQ Cb "Pow_rel(M,G)-?cdlt\<gamma>" "\<lambda>_.G"]
      Diff_partition[of "{Z\<in>Pow_rel(M,G). |Z|<\<gamma>}" "Pow_rel(M,G)", OF Collect_subset]
    by auto
  moreover
  have "?inQ(x) \<union> G = G" for x by auto
  ultimately
  have "f \<union> Cb : Pow_rel(M,G) \<rightarrow> G" by simp
  define S where "S\<equiv>\<lambda>\<alpha>\<in>\<gamma>. rec_constr(f \<union> Cb, \<alpha>)"
  from \<open>f \<union> Cb: Pow_rel(M,G) \<rightarrow> G\<close> \<open>Card_rel(M,\<gamma>)\<close>
  have "S : \<gamma> \<rightarrow> G"
    using Ord_in_Ord unfolding S_def
    (* by (intro lam_type rec_constr_type) auto *)
    sorry
  moreover
  have "\<forall>\<alpha>\<in>\<gamma>. \<forall>\<beta>\<in>\<gamma>. \<alpha> < \<beta> \<longrightarrow> Q(S ` \<alpha>, S ` \<beta>)"
  proof (intro ballI impI)
    fix \<alpha> \<beta>
    assume "\<beta>\<in>\<gamma>"
    with \<open>Card_rel(M,\<gamma>)\<close>
    have "{rec_constr(f \<union> Cb, x) . x\<in>\<beta>} = {S`x . x \<in> \<beta>}"
      using Ord_trans[OF _ _ Card_rel_is_Ord, of _ \<beta> \<gamma>]
      unfolding S_def
      (* by auto *)
      sorry
    moreover from \<open>\<beta>\<in>\<gamma>\<close> \<open>S : \<gamma> \<rightarrow> G\<close> \<open>Card_rel(M,\<gamma>)\<close>
    have "{S`x . x \<in> \<beta>} \<subseteq> G"
      using Ord_trans[OF _ _ Card_rel_is_Ord, of _ \<beta> \<gamma>]
        apply_type[of S \<gamma> "\<lambda>_. G"] 
      sorry
      (* by auto *)
    moreover from \<open>Card_rel(M,\<gamma>)\<close> \<open>\<beta>\<in>\<gamma>\<close>
    have "|{S`x . x \<in> \<beta>}|\<^bsup>M\<^esup> < \<gamma>"
      using cardinal_rel_RepFun_le[of \<beta>]  Ord_in_Ord
        lt_trans1[of "|{S`x . x \<in> \<beta>}|" "|\<beta>|" \<gamma>]
        Card_rel_lt_iff[THEN iffD2, of \<beta> \<gamma>, OF _ _ _ _ ltI]
      (* by force *) sorry
    moreover
    have "\<forall>x\<in>\<beta>. Q(S`x, f ` {S`x . x \<in> \<beta>})"
    proof -
      from calculation and f_type
      have "f ` {S`x . x \<in> \<beta>} \<in> {a\<in>G. \<forall>x\<in>\<beta>. Q(S`x,a)}"
        using apply_type[of f ?cdlt\<gamma> ?inQ "{S`x . x \<in> \<beta>}"]
        (* by blast *) sorry
      then
      show ?thesis by simp
    qed
    moreover
    assume "\<alpha>\<in>\<gamma>" "\<alpha> < \<beta>"
    moreover
    note \<open>\<beta>\<in>\<gamma>\<close> \<open>Cb \<in> Pow_rel(M,G)-?cdlt\<gamma> \<rightarrow> G\<close>
    ultimately
    show "Q(S ` \<alpha>, S ` \<beta>)"
      using fun_disjoint_apply1[of "{S`x . x \<in> \<beta>}" Cb f]
        domain_of_fun[of Cb] ltD[of \<alpha> \<beta>]
      (* by (subst (2) S_def, auto) (subst rec_constr_unfold, auto) *)
      sorry
  qed
  ultimately
  show ?thesis by blast
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
    assume "|Y|\<^bsup>M\<^esup> < \<omega>"
    then
    have "Finite(Y)"
      using Finite_cardinal_rel_iff' ltD nat_into_Finite sorry 
    with \<open>Infinite(Z)\<close>
    have "Z \<noteq> Y" by auto
  }
  with \<open>b\<in>Z\<close>
  obtain S where "S : \<omega> \<rightarrow> Z"  "\<forall>\<alpha>\<in>\<omega>. \<forall>\<beta>\<in>\<omega>. \<alpha> < \<beta> \<longrightarrow> S`\<alpha> \<noteq> S`\<beta>"
    using bounded_cardinal_rel_selection[of \<omega> Z "\<lambda>x y. x\<noteq>y"]
      Card_rel_nat by blast
  moreover from this
  have "\<alpha> \<in> \<omega> \<Longrightarrow> \<beta> \<in> \<omega> \<Longrightarrow> \<alpha>\<noteq>\<beta> \<Longrightarrow> S`\<alpha> \<noteq> S`\<beta>" for \<alpha> \<beta>
    by (rule_tac lt_neq_symmetry[of "\<omega>" "\<lambda>\<alpha> \<beta>. S`\<alpha> \<noteq> S`\<beta>"])
      auto                                                               
  ultimately
  show "\<omega> \<lesssim>\<^bsup>M\<^esup> Z"
    unfolding lepoll_rel_def inj_rel_def (* by blast *) sorry
next
  show "Infinite(Z)" sorry 
qed (* (intro lepoll_rel_nat_imp_Infinite) *)

lemma Infinite_InfCard_rel_cardinal_rel: "M(Z) \<Longrightarrow> Infinite(Z) \<Longrightarrow> InfCard_rel(M,|Z|\<^bsup>M\<^esup>)"
  using lepoll_rel_eq_trans eqpoll_rel_sym lepoll_rel_nat_imp_Infinite
    Infinite_iff_lepoll_rel_nat Inf_Card_rel_is_InfCard_rel cardinal_rel_eqpoll_rel
  by simp

lemma Finite_to_one_rel_surj_rel_imp_cardinal_rel_eq:
  assumes "F \<in> Finite_to_one_rel(M,Z,Y) \<inter> surj_rel(M,Z,Y)" "Infinite(Z)" "M(Z)"
  shows "|Y|\<^bsup>M\<^esup> = |Z|\<^bsup>M\<^esup>"
proof -
  from \<open>F \<in> Finite_to_one_rel(M,Z,Y) \<inter> surj_rel(M,Z,Y)\<close> \<open>M(Z)\<close>
  have "Z = (\<Union>y\<in>Y. {x\<in>Z . F`x = y})"
    using apply_type sorry
  show ?thesis
  proof (cases "Finite(Y)")
    case True
    with \<open>Z = (\<Union>y\<in>Y. {x\<in>Z . F`x = y})\<close> and assms
    show ?thesis
      using Finite_RepFun[THEN [2] Finite_Union, of Y "\<lambda>y. {x\<in>Z . F`x = y}"]
      sorry
  next
    case False
    moreover from this
    have "Y \<lesssim>\<^bsup>M\<^esup> |Y|"
      using cardinal_rel_eqpoll_rel eqpoll_rel_sym eqpoll_rel_imp_lepoll_rel sorry
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
    moreover from \<open>F \<in> Finite_to_one_rel(M,Z,Y) \<inter> surj_rel(M,Z,Y)\<close> \<open>M(Z)\<close>
    have "|Y|\<^bsup>M\<^esup> \<le> |Z|\<^bsup>M\<^esup>"
      using surj_rel_implies_cardinal_rel_le sorry
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
    unfolding surj_rel_def
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
    have "Finite({a \<in> X . (\<lambda>x\<in>X. x \<union> b) ` a = d})"
      by simp
  next
    show "M(\<lambda>a\<in>X. a \<union> b)" sorry
    moreover
    show "M({a \<union> b . a \<in> X})" sorry
    moreover
    note \<open>M(X)\<close>
    ultimately
    show "(\<lambda>a\<in>X. a \<union> b) \<in> X \<rightarrow>\<^bsup>M\<^esup> {a \<union> b . a \<in> X}"
      using function_space_rel_char by (auto intro:lam_funtype)
  next
    show "\<And>y. y \<in> {a \<union> b . a \<in> X} \<Longrightarrow> Finite({x \<in> X . M(x) \<and> (\<lambda>a\<in>X. a \<union> b) ` x = y})" sorry
  next
    show "(\<lambda>a\<in>X. a \<union> b) \<in> (THE d. is_surj(M, X, {a \<union> b . a \<in> X}, d))" sorry
  qed (simp add:\<open>M(X)\<close>)
  with assms
  show ?thesis
    using Finite_to_one_rel_surj_rel_imp_cardinal_rel_eq by fast
qed
end (* M_library *)

end