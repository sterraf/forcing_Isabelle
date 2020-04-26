section\<open>Cohen forcing notions\<close>

theory Cohen_Posets
  imports
    Least "../Tools/Try0"
begin

definition
  Fn :: "[i,i,i] \<Rightarrow> i" where
  "Fn(\<kappa>,I,J) \<equiv> \<Union>{(d\<rightarrow>J) .. d \<in> Pow(I),  d\<prec>\<kappa>}"

lemma lesspoll_csucc: assumes "Ord(\<kappa>)" shows "d \<prec> csucc(\<kappa>) \<longleftrightarrow> d \<lesssim> \<kappa>"
  unfolding lesspoll_def
proof (intro iffI conjI, elim conjE)
  assume "d \<lesssim> \<kappa>"
  show "d \<lesssim> csucc(\<kappa>)"
    sorry
  show "\<not> d \<approx> csucc(\<kappa>)"
    sorry
next
  assume "d \<lesssim> csucc(\<kappa>)" "\<not> d \<approx> csucc(\<kappa>)"
  show "d \<lesssim> \<kappa>"
    sorry
qed

lemma Fn_csucc:
  assumes "Ord(\<kappa>)"
  shows "Fn(csucc(\<kappa>),I,J) = \<Union>{(d\<rightarrow>J) .. d \<in> Pow(I), d\<lesssim>\<kappa>}"
  using assms
  unfolding Fn_def using lesspoll_csucc by (simp)

lemma Finite_imp_lesspoll_nat: "Finite(A) \<Longrightarrow> A \<prec> nat"
  sorry

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

end (* cohen_data *)

end