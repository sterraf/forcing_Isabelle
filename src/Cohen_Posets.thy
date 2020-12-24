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

lemma InfCard_lesspoll_Un:
  includes Ord_dests
  assumes "InfCard(\<kappa>)" "A \<prec> \<kappa>" "B \<prec> \<kappa>"
  shows "A \<union> B \<prec> \<kappa>"
proof -
  from assms
  have "|A| < \<kappa>" "|B| < \<kappa>"
    using lesspoll_cardinal_lt InfCard_is_Card by auto
  show ?thesis
  proof (cases "Finite(A) \<and> Finite(B)")
    case True
    with assms
    show ?thesis
      using lesspoll_trans2[OF _ le_imp_lepoll, of _ nat \<kappa>]
        Finite_imp_lesspoll_nat[OF Finite_Un]
      unfolding InfCard_def by simp
  next
    case False
    then
    have "InfCard(max(|A|,|B|))"
      using Infinite_InfCard_cardinal InfCard_is_Card
        le_trans[of nat] not_le_iff_lt[THEN iffD1, THEN leI, of "|A|" "|B|"]
      unfolding max_def InfCard_def
      by (auto)
    then
    have "|A \<union> B| \<le> max(|A|,|B|)"
      using cardinal_Un_le[of "max(|A|,|B|)"]
        not_le_iff_lt[THEN iffD1, THEN leI, of "|A|" "|B|" ]
      unfolding max_def
      by auto
    moreover from \<open>|A| < \<kappa>\<close> \<open>|B| < \<kappa>\<close>
    have "max(|A|,|B|) < \<kappa>"
      unfolding max_def by simp
    ultimately
    have "|A \<union> B| <  \<kappa>"
      using lt_trans1 by blast
    moreover
    note \<open>InfCard(\<kappa>)\<close>
    moreover from calculation
    have "|A \<union> B| \<prec> \<kappa>"
      using lt_Card_imp_lesspoll InfCard_is_Card by simp
    ultimately
    show ?thesis
      using  cardinal_eqpoll eq_lesspoll_trans eqpoll_sym by blast
  qed
qed

subsection\<open>MOVE THIS to an appropriate place\<close>

definition
  antichain :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "antichain(P,leq,A) \<equiv> A\<subseteq>P \<and> (\<forall>p\<in>A. \<forall>q\<in>A.
                p\<noteq>q \<longrightarrow> \<not>compat_in(P,leq,p,q))"
definition
  ccc :: "i \<Rightarrow> i \<Rightarrow> o" where
  "ccc(P,leq) \<equiv> \<forall>A. antichain(P,leq,A) \<longrightarrow> |A| \<le> nat"

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

(* MOVE THIS to an appropriate place *)
lemma filter_subset_notion: "filter(G) \<Longrightarrow> G \<subseteq> Fn(\<kappa>, I, J)"
  unfolding filter_def by simp

lemma Un_filter_is_function: "filter(G) \<Longrightarrow> function(\<Union>G)"
  using compat_imp_Un_is_function filter_imp_compat[of G]
    filter_subset_notion by simp

end (* cohen_data *)

locale add_reals = cohen_data nat _ 2
begin

lemma ccc_Fn_nat:
  notes Sep_and_Replace [simp]\<comment> \<open>FIXME with all \<^term>\<open>SepReplace\<close> instances\<close>
  shows "ccc(Fn(nat,I,2), Fnle(nat,I,2))"
proof -
  {
    fix A
    assume "\<not> |A| \<le> nat"
    assume "A \<subseteq> Fn(nat, I, 2)"
    moreover from this
    have "countable({p\<in>A. domain(p) = d})" for d
    proof (cases "d\<prec>nat \<and> d \<subseteq> I")
      case True
      with \<open>A \<subseteq> Fn(nat, I, 2)\<close>
      have "{p \<in> A . domain(p) = d} \<subseteq> d \<rightarrow> 2"
        using domain_of_fun by fastforce
      moreover from True
      have "Finite(d \<rightarrow> 2)"
        using Finite_Pi lesspoll_nat_is_Finite by auto
      ultimately
      show ?thesis using subset_Finite[of _ "d\<rightarrow>2" ] Finite_imp_countable
        by auto
    next
      case False
      with \<open>A \<subseteq> Fn(nat, I, 2)\<close>
      have "{p \<in> A . domain(p) = d} = 0"
        by (intro equalityI) (auto dest!: domain_of_fun)
      then
      show ?thesis using empty_lepollI by auto
    qed
    moreover
    have "uncountable({domain(p) . p \<in> A})"
    proof
      from \<open>A \<subseteq> Fn(nat, I, 2)\<close>
      have "A = (\<Union>d\<in>{domain(p) . p \<in> A}. {p\<in>A. domain(p) = d})"
        by auto
      moreover
      assume "countable({domain(p) . p \<in> A})"
      moreover
      note \<open>\<And>d. countable({p\<in>A. domain(p) = d})\<close>
      ultimately
      have "countable(A)"
        using countable_imp_countable_UN[of "{domain(p). p\<in>A}"
            "\<lambda>d. {p \<in> A. domain(p) = d }"]
        by simp
      with \<open>\<not> |A| \<le> nat\<close>
      show False
        using countable_iff_cardinal_le_nat by simp
    qed
    moreover from \<open>A \<subseteq> Fn(nat, I, 2)\<close>
    have "p \<in> A \<Longrightarrow> Finite(domain(p))" for p
      using lesspoll_nat_is_Finite[of "domain(p)"]
        domain_of_fun[of p _ "\<lambda>_. 2"] by auto
    ultimately
    obtain D where "delta_system(D)" "D \<subseteq> {domain(p) . p \<in> A}" "D \<approx> \<aleph>\<^bsub>1\<^esub>"
      using delta_system_uncountable[of "{domain(p) . p \<in> A}"] by auto
    moreover from this
    have "uncountable(D)"
      using uncountable_iff_subset_eqpoll_Aleph1 by auto
    ultimately
    have delta:"\<forall>d1\<in>D. \<forall>d2\<in>D. d1 \<noteq> d2 \<longrightarrow> d1 \<inter> d2 = \<Inter>D"
      using uncountable_imp_Infinite[THEN Infinite_delta_system_root_eq_Inter]
      by simp
    moreover from \<open>D \<subseteq> {domain(p) . p \<in> A}\<close> \<open>uncountable(D)\<close>
    obtain p1 where "p1 \<in> A" "domain(p1) \<in> D"
      using uncountable_not_empty[of D] by blast
    moreover from this and \<open>p1 \<in> A \<Longrightarrow> Finite(domain(p1))\<close>
    have "Finite(domain(p1))" using Finite_domain by simp
    moreover
    define r where "r \<equiv> \<Inter>D"
    ultimately
    have "Finite(r)" using subset_Finite[of "r" "domain(p1)"] by auto
    have "countable({restrict(p,r) . p\<in>A})"
    proof -
      have "f\<in>Fn(nat, I, 2) \<Longrightarrow> restrict(f,r) \<in> Pow(r \<times> 2)" for f
        using restrict_subset_Sigma[of f _ "\<lambda>_. 2" r]
        by (auto dest!:FnD simp: Pi_def) auto
      with \<open>A \<subseteq> Fn(nat, I, 2)\<close>
      have "{restrict(f,r) . f \<in> A } \<subseteq> Pow(r \<times> 2)"
        by fast
      with \<open>Finite(r)\<close>
      show ?thesis
        using Finite_Sigma[THEN Finite_Pow, of r "\<lambda>_. 2"]
        by (intro Finite_imp_countable) (auto intro:subset_Finite)
    qed
    moreover
    have "uncountable({p\<in>A. domain(p) \<in> D})" (is "uncountable(?X)")
    proof
      from \<open>D \<subseteq> {domain(p) . p \<in> A}\<close>
      have "(\<lambda>p\<in>?X. domain(p)) \<in> surj(?X, D)"
        using lam_type unfolding surj_def by auto
      moreover
      assume "countable(?X)"
      moreover
      note \<open>uncountable(D)\<close>
      ultimately
      show False
        using surj_countable by auto
    qed
    moreover
    have "D = (\<Union>f\<in>Pow(r\<times>2) . {domain(p) .. p\<in>A, restrict(p,r) = f \<and> domain(p) \<in> D})"
    proof -
      {
        fix z
        assume "z \<in> D"
        with \<open>D \<subseteq> _\<close>
        obtain p  where "domain(p) = z" "p \<in> A"
          by auto
        moreover from \<open>A \<subseteq> Fn(nat, I, 2)\<close> and this
        have "p : z \<rightarrow> 2"
          using domain_of_fun by (auto dest!:FnD)
        moreover from this
        have "restrict(p,r) \<subseteq> r \<times> 2"
          using function_restrictI[of p r] fun_is_function[of p z "\<lambda>_. 2"]
            restrict_subset_Sigma[of p z "\<lambda>_. 2" r]
          by (auto simp:Pi_def)
        ultimately
        have "\<exists>p\<in>A.  restrict(p,r) \<in> Pow(r\<times>2) \<and> domain(p) = z" by auto
      }
      then
      show ?thesis
        by (intro equalityI) (force)+
    qed
    obtain f where "uncountable({domain(p) .. p\<in>A, restrict(p,r) = f \<and> domain(p) \<in> D})"
      (is "uncountable(?Y(f))")
    proof -
      {
        from \<open>Finite(r)\<close>
        have "countable(Pow(r\<times>2))"
          using Finite_Sigma[THEN Finite_Pow, THEN Finite_imp_countable]
          by simp
        moreover
        assume "countable(?Y(f))" for f
        moreover
        note \<open>D = (\<Union>f\<in>Pow(r\<times>2) .?Y(f))\<close>
        moreover
        note \<open>uncountable(D)\<close>
        ultimately
        have "False"
          using countable_imp_countable_UN[of "Pow(r\<times>2)" ?Y] by auto
      }
      with that
      show ?thesis by auto
    qed
    then
    obtain j where "j \<in> inj(nat, ?Y(f))"
      using uncountable_iff_nat_lt_cardinal[THEN iffD1, THEN leI,
          THEN cardinal_le_imp_lepoll, THEN lepollD]
      by auto
    then
    have "j`0 \<noteq> j`1" "j`0 \<in> ?Y(f)" "j`1 \<in> ?Y(f)"
      using inj_is_fun[THEN apply_type, of j nat "?Y(f)"]
      unfolding inj_def by auto
    then
    obtain p q where "domain(p) \<noteq> domain(q)" "p \<in> A" "q \<in> A"
      "domain(p) \<in> D" "domain(q) \<in> D"
      "restrict(p,r) = restrict(q,r)" by auto
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