section\<open>Cohen forcing notions\<close>

theory Cohen_Posets
  imports
    Forcing_Notions
    Names \<comment> \<open>only for \<^term>\<open>SepReplace\<close>\<close>
    Recursion_Thms \<comment> \<open>only for the definition of \<^term>\<open>Rrel\<close>\<close>
    Renaming_Auto \<comment> \<open>only for @{thm app_fun}\<close>
    "../Tools/Try0"
begin

lemma eq_csucc_ord:
  "Ord(i) \<Longrightarrow> csucc(i) = csucc(|i|)"
  using Card_lt_iff Least_cong unfolding csucc_def by auto

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

lemma FnleR_iff_subset [simp]: "f \<supseteq> g \<longleftrightarrow> g \<subseteq> f"
  unfolding FnleR_def ..

definition
  Fnlerel :: "i \<Rightarrow> i" where
  "Fnlerel(A) \<equiv> Rrel(\<lambda>x y. x \<supseteq> y,A)"

definition
  Fnle :: "[i,i,i] \<Rightarrow> i" where
  "Fnle(\<kappa>,I,J) \<equiv> Fnlerel(Fn(\<kappa>,I,J))"

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
      Fnle_def Fnlerel_def Rrel_def by simp
next
  show "preorder_on(Fn(\<kappa>, I, J), Fnle(\<kappa>, I, J))"
    unfolding preorder_on_def refl_def trans_on_def
      Fnle_def Fnlerel_def Rrel_def by auto
qed

context cohen_data
begin
notation Leq (infixl "\<preceq>" 50)

\<comment> \<open>Really necessary?\<close>
lemma fun_compat_Un:
  assumes "f \<in> A\<rightarrow>B" "g \<in> C\<rightarrow>D" "restrict(f, A \<inter> C) = restrict(g, A \<inter> C)"
  shows "(f \<union> g) \<in> (A \<union> C) \<rightarrow> (B \<union> D)"
  oops

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
    using compatD[of p q]
    unfolding Fnlerel_def Fnle_def FnleR_def Rrel_def
    by auto
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

end