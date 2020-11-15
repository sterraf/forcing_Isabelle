section\<open>Cohen forcing notions\<close>

theory Cohen_Posets
  imports
    Forcing_Notions
    Names \<comment> \<open>only for \<^term>\<open>SepReplace\<close>\<close>
    Recursion_Thms \<comment> \<open>only for the definition of \<^term>\<open>Rrel\<close>\<close>
    Renaming_Auto \<comment> \<open>only for @{thm app_fun}\<close>
    "../Delta_System_Lemma/Delta_System"
begin

definition
  Fn :: "[i,i,i] \<Rightarrow> i" where
  "Fn(\<kappa>,I,J) \<equiv> \<Union>{(d\<rightarrow>J) .. d \<in> Pow(I),  d\<prec>\<kappa>}"

lemma FnI[intro]:
  assumes "p : d \<rightarrow> J" "d \<subseteq> I" "d \<prec> \<kappa>"
  shows "p \<in> Fn(\<kappa>,I,J)"
  using assms Sep_and_Replace
  unfolding Fn_def by auto

lemma FnD[dest]:
  assumes "p \<in> Fn(\<kappa>,I,J)"
  shows "\<exists>d. p : d \<rightarrow> J \<and> d \<subseteq> I \<and> d \<prec> \<kappa>"
  using assms Sep_and_Replace
  unfolding Fn_def by auto

lemma Fn_is_function: "p \<in> Fn(\<kappa>,I,J) \<Longrightarrow> function(p)"
  unfolding Fn_def using Sep_and_Replace fun_is_function by auto

lemma lesspoll_csucc:
  assumes "Ord(\<kappa>)"
  shows "d \<prec> csucc(\<kappa>) \<longleftrightarrow> d \<lesssim> \<kappa>"
proof
  assume "d \<prec> csucc(\<kappa>)"
  moreover
  note Card_is_Ord \<open>Ord(\<kappa>)\<close>
  moreover from calculation
  have "\<kappa> < csucc(\<kappa>)" "Card(csucc(\<kappa>))"
    using Ord_cardinal_eqpoll csucc_basic by simp_all
  moreover from calculation
  have "d \<prec> csucc(|\<kappa>|)" "Card(|\<kappa>|)" "d \<approx> |d|"
    using eq_csucc_ord[of \<kappa>] lesspoll_imp_eqpoll eqpoll_sym by simp_all
  moreover from calculation
  have "|d| < csucc(|\<kappa>|)"
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
  have "\<kappa> < csucc(\<kappa>)" "Card(csucc(\<kappa>))"
    using csucc_basic by simp_all
  moreover
  assume "d \<lesssim> \<kappa>"
  ultimately
  have "d \<lesssim> csucc(\<kappa>)"
    using le_imp_lepoll leI lepoll_trans by simp
  moreover
  from \<open>d \<lesssim> \<kappa>\<close> \<open>Ord(\<kappa>)\<close>
  have "csucc(\<kappa>) \<lesssim> \<kappa>" if "d \<approx> csucc(\<kappa>)"
    using eqpoll_sym[OF that] eq_lepoll_trans[OF _ \<open>d\<lesssim>\<kappa>\<close>] by simp
  moreover from calculation \<open>Card(_)\<close>
  have "\<not> d \<approx> csucc(\<kappa>)"
    using lesspoll_irrefl lesspoll_trans1 lt_Card_imp_lesspoll[OF _ \<open>\<kappa> <_\<close>]
    by auto
  ultimately
  show "d \<prec> csucc(\<kappa>)"
    unfolding lesspoll_def by simp
qed

lemma Fn_csucc:
  assumes "Ord(\<kappa>)"
  shows "Fn(csucc(\<kappa>),I,J) = \<Union>{(d\<rightarrow>J) .. d \<in> Pow(I), d\<lesssim>\<kappa>}"
  using assms
  unfolding Fn_def using lesspoll_csucc by (simp)

lemma Finite_imp_lesspoll_nat:
  assumes "Finite(A)"
  shows "A \<prec> nat"
  using assms subset_imp_lepoll[OF naturals_subset_nat] eq_lepoll_trans
    n_lesspoll_nat eq_lesspoll_trans
  unfolding Finite_def lesspoll_def by auto

lemma Fn_nat_eq_FiniteFun: "Fn(nat,I,J) = I -||> J"
  unfolding Fn_def
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> I -||> J"
  then
  show "x \<in> \<Union>{(d\<rightarrow>J) .. d \<in> Pow(I), d\<prec>nat}"
  proof (induct)
    case emptyI
    have "0: 0\<rightarrow>J" by simp
    moreover
    have "|0|<nat" using ltI by simp
    ultimately
    show ?case using lt_Card_imp_lesspoll Card_nat
      by (simp,rule_tac x="0\<rightarrow>J" in bexI)
        (auto | rule_tac x="0" in bexI)+
  next
    case (consI a b h)
    then
    obtain d where "h:d\<rightarrow>J" "d\<prec>nat" "d\<subseteq>I" by auto
    moreover from this
    have "Finite(d)"
      using lesspoll_nat_is_Finite by simp
    ultimately
    have "h : d -||> J"
      using fun_FiniteFunI Finite_into_Fin by blast
    note \<open>h:d\<rightarrow>J\<close>
    moreover from this
    have "domain(cons(\<langle>a, b\<rangle>, h)) = cons(a,d)" (is "domain(?h) = ?d")
      and "domain(h) = d"
      using domain_of_fun by simp_all
    moreover
    note consI
    moreover from calculation
    have "cons(\<langle>a, b\<rangle>, h) \<in> cons(a,d) \<rightarrow> J"
      using fun_extend3 by simp
    moreover from \<open>Finite(d)\<close>
    have "Finite(cons(a,d))" by simp
    moreover from this
    have "cons(a,d) \<prec> nat" using Finite_imp_lesspoll_nat by simp
    ultimately
    show ?case by (simp,rule_tac x="?d\<rightarrow>J" in bexI)
        (force dest:app_fun)+
  qed
next
  fix x
  assume "x \<in> \<Union>{(d\<rightarrow>J) .. d \<in> Pow(I),  d\<prec>nat}"
  then
  obtain d where "x:d\<rightarrow>J" "d \<in> Pow(I)" "d\<prec>nat" by auto
  moreover from this
  have "Finite(d)"
    using lesspoll_nat_is_Finite by simp
  moreover from calculation
  have "d \<in> Fin(I)"
    using Finite_into_Fin[of d] Fin_mono by auto
  ultimately
  show "x \<in> I -||> J" using fun_FiniteFunI FiniteFun_mono by blast
qed

definition
  FnleR :: "i \<Rightarrow> i \<Rightarrow> o" (infixl \<open>\<supseteq>\<close> 50) where
  "f \<supseteq> g \<equiv> g \<subseteq> f"

lemma FnleR_iff_subset [iff]: "f \<supseteq> g \<longleftrightarrow> g \<subseteq> f"
  unfolding FnleR_def ..

definition
  Fnlerel :: "i \<Rightarrow> i" where
  "Fnlerel(A) \<equiv> Rrel(\<lambda>x y. x \<supseteq> y,A)"

definition
  Fnle :: "[i,i,i] \<Rightarrow> i" where
  "Fnle(\<kappa>,I,J) \<equiv> Fnlerel(Fn(\<kappa>,I,J))"

lemma FnleI[intro]:
  assumes "p \<in> Fn(\<kappa>,I,J)" "q \<in> Fn(\<kappa>,I,J)" "p \<supseteq> q"
  shows "<p,q> \<in> Fnle(\<kappa>,I,J)"
  using assms unfolding Fnlerel_def Fnle_def FnleR_def Rrel_def
  by auto

lemma FnleD[dest]:
  assumes "<p,q> \<in> Fnle(\<kappa>,I,J)"
  shows "p \<in> Fn(\<kappa>,I,J)" "q \<in> Fn(\<kappa>,I,J)" "p \<supseteq> q"
  using assms unfolding Fnlerel_def Fnle_def FnleR_def Rrel_def
  by auto

lemma zero_lesspoll: assumes "0<\<kappa>" shows "0 \<prec> \<kappa>"
  using assms eqpoll_0_iff[THEN iffD1, of \<kappa>] eqpoll_sym
  unfolding lesspoll_def lepoll_def
  by (auto simp add:inj_def)

locale cohen_data =
  fixes \<kappa> I J::i
  assumes zero_lt_kappa: "0<\<kappa>"
begin

lemmas zero_lesspoll_kappa = zero_lesspoll[OF zero_lt_kappa]

end (* cohen_data *)

sublocale cohen_data \<subseteq> forcing_notion "Fn(\<kappa>,I,J)" "Fnle(\<kappa>,I,J)" 0
proof
  show "0 \<in> Fn(\<kappa>, I, J)"
    unfolding Fn_def
    by (simp,rule_tac x="0 \<rightarrow> J" in bexI, auto)
      (rule_tac x=0 in bexI, auto intro:zero_lesspoll_kappa)
  then
  show "\<forall>p\<in>Fn(\<kappa>, I, J). \<langle>p, 0\<rangle> \<in> Fnle(\<kappa>, I, J)"
    unfolding preorder_on_def refl_def trans_on_def
    by auto
next
  show "preorder_on(Fn(\<kappa>, I, J), Fnle(\<kappa>, I, J))"
    unfolding preorder_on_def refl_def trans_on_def
    by blast
qed

lemma restrict_eq_imp_Un_into_Pi:
  assumes "f \<in> Pi(A,B)" "g \<in> Pi(C,D)" "restrict(f, A \<inter> C) = restrict(g, A \<inter> C)"
  shows "f \<union> g \<in> Pi(A \<union> C, \<lambda>x. B(x) \<union> D(x))"
  sorry

lemma restrict_eq_imp_Un_into_Pi':
  assumes "f \<in> Pi(A,B)" "g \<in> Pi(C,D)" "restrict(f, domain(f) \<inter> domain(g)) = restrict(g, domain(f) \<inter> domain(g))"
  shows "f \<union> g \<in> Pi(A \<union> C, \<lambda>x. B(x) \<union> D(x))"
  using  assms domain_of_fun restrict_eq_imp_Un_into_Pi by simp

lemma InfCard_lesspoll_Un:
  assumes "InfCard(\<kappa>)" "A \<prec> \<kappa>" "B \<prec> \<kappa>"
  shows "A \<union> B \<prec> \<kappa>"
  sorry

subsection\<open>MOVE THIS to an appropriate place\<close>

definition
  antichain :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "antichain(P,leq,A) \<equiv> A\<subseteq>P \<and> (\<forall>p\<in>A. \<forall>q\<in>A.
                p\<noteq>q \<longrightarrow> \<not>compat_in(P,leq,p,q))"
definition
  ccc :: "i \<Rightarrow> i \<Rightarrow> o" where
  "ccc(P,leq) \<equiv> \<forall>A. antichain(P,leq,A) \<longrightarrow> |A| \<le> nat"

lemma Replace_sing1:
    "\<lbrakk> (\<exists>a. P(d,a)) \<and> (\<forall>y y'. P(d,y) \<longrightarrow> P(d,y') \<longrightarrow> y=y') \<rbrakk> \<Longrightarrow> \<exists>a. {y . x \<in> {d}, P(x,y)} = {a}"
  by blast

\<comment> \<open>Not really necessary\<close>
lemma Replace_sing2:
  assumes "\<forall>a. \<not> P(d,a)"
  shows "{y . x \<in> {d}, P(x,y)} = 0"
  using assms by auto

lemma Replace_sing3:
  assumes "\<exists>c e. c \<noteq> e \<and> P(d,c) \<and> P(d,e)"
  shows "{y . x \<in> {d}, P(x,y)} = 0"
proof -
  {
    fix z
    {
      assume "\<forall>y. P(d, y) \<longrightarrow> y = z"
      with assms
      have "False" by auto
    }
    then
    have "z \<notin> {y . x \<in> {d}, P(x,y)}"
      using Replace_iff by auto
  }
  then
  show ?thesis
    by (intro equalityI subsetI) simp_all
qed

lemma Replace_Un: "{b . a \<in> A \<union> B, Q(a, b)} =
        {b . a \<in> A, Q(a, b)} \<union> {b . a \<in> B, Q(a, b)}"
  by (intro equalityI subsetI) (auto simp add:Replace_iff)

lemma Replace_subset_sing: "\<exists>z. {y . x \<in> {d}, P(x,y)} \<subseteq> {z}"
proof -
  consider
    (1) "(\<exists>a. P(d,a)) \<and> (\<forall>y y'. P(d,y) \<longrightarrow> P(d,y') \<longrightarrow> y=y')" |
    (2) "\<forall>a. \<not> P(d,a)" | (3) "\<exists>c e. c \<noteq> e \<and> P(d,c) \<and> P(d,e)" by auto
  then
  show "\<exists>z. {y . x \<in> {d}, P(x,y)} \<subseteq> {z}"
  proof (cases)
    case 1
    then show ?thesis using Replace_sing1[of P d] by auto
  next
    case 2
    then show ?thesis by auto
  next
    case 3
    then show ?thesis using Replace_sing3[of P d] by auto
  qed
qed

lemma Finite_Replace: "Finite(A) \<Longrightarrow> Finite(Replace(A,Q))"
proof (induct rule:Finite_induct)
  case 0
  then
  show ?case by simp
next
  case (cons x B)
  moreover
  have "{b . a \<in> cons(x, B), Q(a, b)} =
        {b . a \<in> B, Q(a, b)} \<union> {b . a \<in> {x}, Q(a, b)}"
    using Replace_Un unfolding cons_def by auto
  moreover
  obtain d where "{b . a \<in> {x}, Q(a, b)} \<subseteq> {d}"
    using Replace_subset_sing[of _ Q] by blast
  moreover from this
  have "Finite({b . a \<in> {x}, Q(a, b)})"
    using subset_Finite by simp
  ultimately
  show ?case using subset_Finite by simp
qed

lemma Finite_domain: "Finite(A) \<Longrightarrow> Finite(domain(A))"
  using Finite_Replace unfolding domain_def
  by auto

lemma Finite_converse: "Finite(A) \<Longrightarrow> Finite(converse(A))"
  using Finite_Replace unfolding converse_def
  by auto

lemma Finite_range: "Finite(A) \<Longrightarrow> Finite(range(A))"
  using Finite_domain Finite_converse unfolding range_def
  by blast

lemma Finite_Sigma: "Finite(A) \<Longrightarrow> \<forall>x. Finite(B(x)) \<Longrightarrow> Finite(Sigma(A,B))"
  unfolding Sigma_def using Finite_RepFun Finite_Union
  by simp

lemma Finite_Pi: "Finite(A) \<Longrightarrow> \<forall>x. Finite(B(x)) \<Longrightarrow> Finite(Pi(A,B))"
  using Finite_Sigma
    Finite_Pow subset_Finite[of "Pi(A,B)" "Pow(Sigma(A,B))"]
  unfolding Pi_def
  by auto

subsection\<open>Combinatorial results on Cohen posets\<close>

context cohen_data
begin
notation Leq (infixl "\<preceq>" 50)

lemma restrict_eq_imp_compat:
  assumes "f \<in> Fn(\<kappa>, I, J)" "g \<in> Fn(\<kappa>, I, J)" "InfCard(\<kappa>)"
    "restrict(f, domain(f) \<inter> domain(g)) = restrict(g, domain(f) \<inter> domain(g))"
  shows "f \<union> g \<in> Fn(\<kappa>, I, J)"
proof -
  from assms
  obtain d1 d2 where "f : d1 \<rightarrow> J" "d1 \<in> Pow(I)" "d1 \<prec> \<kappa>"
    "g : d2 \<rightarrow> J" "d2 \<in> Pow(I)" "d2 \<prec> \<kappa>"
    by blast
  with assms
  show ?thesis
    using domain_of_fun InfCard_lesspoll_Un[of \<kappa> d1 d2]
      restrict_eq_imp_Un_into_Pi[of f d1 "\<lambda>_. J" g d2 "\<lambda>_. J"]
    by auto
qed

lemma compat_imp_Un_is_function:
  assumes "G \<subseteq> Fn(\<kappa>, I, J)" "\<And>p q. p \<in> G \<Longrightarrow> q \<in> G \<Longrightarrow> compat(p,q)"
  shows "function(\<Union>G)"
  unfolding function_def
proof (intro allI ballI impI)
  fix x y y'
  assume "\<langle>x, y\<rangle> \<in> \<Union>G" "\<langle>x, y'\<rangle> \<in> \<Union>G"
  then
  obtain p q where "\<langle>x, y\<rangle> \<in> p" "\<langle>x, y'\<rangle> \<in> q" "p \<in> G" "q \<in> G"
    by auto
  moreover from this and assms
  obtain r where "r \<in> Fn(\<kappa>, I, J)" "r \<supseteq> p" "r \<supseteq> q"
    using compatD[of p q] by force
  moreover from this
  have "function(r)"
    using Fn_is_function by simp
  ultimately
  show "y = y'"
    unfolding function_def by fastforce
qed

lemma filter_subset_notion: "filter(G) \<Longrightarrow> G \<subseteq> Fn(\<kappa>, I, J)"
  unfolding filter_def by simp

lemma Un_filter_is_function: "filter(G) \<Longrightarrow> function(\<Union>G)"
  using compat_imp_Un_is_function filter_imp_compat[of G]
    filter_subset_notion by simp

end (* cohen_data *)

locale add_reals = cohen_data nat _ 2
begin

lemma ccc_Fn_nat: "ccc(Fn(nat,I,2), Fnle(nat,I,2))"
proof -
  {
    fix A
    assume "\<not> |A| \<le> nat" "A \<subseteq> Fn(nat, I, 2)"
    moreover from this
    have "uncountable({domain(p) . p \<in> A})" sorry
    moreover from \<open>A \<subseteq> Fn(nat, I, 2)\<close>
    have "p \<in> A \<Longrightarrow> Finite(domain(p))" for p
      using lesspoll_nat_is_Finite[of "domain(p)"]
        domain_of_fun[of p _ "\<lambda>_. 2"] by auto
    ultimately
    obtain D where "delta_system(D)" "D \<subseteq> {domain(p) . p \<in> A}" "D \<approx> \<aleph>\<^bsub>1\<^esub>"
      using delta_system_uncountable[of "{domain(p) . p \<in> A}"] by auto
    moreover from this
    have "uncountable(D)"
      using uncountable_iff_subset_eqpoll_aleph1 by auto
    ultimately
    have delta:"\<forall>d1\<in>D. \<forall>d2\<in>D. d1 \<noteq> d2 \<longrightarrow> d1 \<inter> d2 = \<Inter>D"
      using uncountable_imp_Infinite[THEN Infinite_delta_system_root_eq_Inter]
      by simp
    moreover from \<open>D \<subseteq> {domain(p) . p \<in> A}\<close> \<open>D \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
    obtain p1 where "p1 \<in> A" "domain(p1) \<in> D"
      using uncountable_iff_subset_eqpoll_aleph1[of D]
        uncountable_not_empty[of D] by blast
    moreover from this and \<open>p1 \<in> A \<Longrightarrow> Finite(domain(p1))\<close>
    have "Finite(domain(p1))" using Finite_domain by simp
    moreover
    define r where "r \<equiv> \<Inter>D"
    ultimately
    have "Finite(r)" using subset_Finite[of "r" "domain(p1)"] by auto
    then
    have "Finite((r) \<rightarrow> 2)"
      using Finite_Pi by auto
    with \<open>D \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
    obtain p q where "domain(p) \<noteq> domain(q)" "p \<in> A" "q \<in> A"
      "domain(p) \<in> D" "q1 \<in> A" "domain(q) \<in> D"
      "restrict(p,r) = restrict(q,r)" sorry
    moreover from this and delta
    have "domain(p) \<inter> domain(q) = r" unfolding r_def by simp
    moreover
    note \<open>A \<subseteq> Fn(nat, I, 2)\<close>
    moreover from calculation
    have "p \<union> q \<in> Fn(nat, I, 2)"
      using restrict_eq_imp_compat InfCard_nat by blast
    ultimately
    have "\<exists>p\<in>A. \<exists>q\<in>A. p \<noteq> q \<and> compat_in(Fn(nat, I, 2), Fnle(nat, I, 2), p, q)"
      unfolding compat_in_def
      by (rule_tac bexI[of _ p], rule_tac bexI[of _ q]) blast
  }
  then
  show ?thesis unfolding ccc_def antichain_def by auto
qed

end (* add_reals *)

end