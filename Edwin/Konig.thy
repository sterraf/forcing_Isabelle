theory Konig
  imports
    ZF.Cardinal_AC
    Cofinality

begin

definition
  cexp :: "[i,i] \<Rightarrow> i" (infixr "\<up>" 75) where
  "\<kappa> \<up> \<nu> \<equiv> |\<nu> \<rightarrow> \<kappa>|"

lemma Card_cexp: "Card(\<kappa> \<up> \<nu>)"
  unfolding cexp_def Card_cardinal by simp

(* 
lemma cexp_cardinal: "X \<up> Y = |X| \<up> |Y|"
  oops
*)

(*
lemma cardinal_eqpollI:
  "X \<approx> Y \<Longrightarrow>  X  \<approx> |Y|"
  "X \<approx> Y \<Longrightarrow> |X| \<approx>  Y"
  using cardinal_eqpoll eqpoll_trans[of "|X|" X Y] 
    eqpoll_trans[OF _ eqpoll_sym, of X Y "|Y|" ]
  by simp_all 
*)

lemma function_space_eqpoll_cong:
  assumes 
    "A \<approx> A'" "B \<approx> B'"
  shows
    "A \<rightarrow> B \<approx> A' \<rightarrow> B'"
  sorry
(*
proof -
  from assms(1)[THEN eqpoll_sym] assms(2)
  obtain f g where "f \<in> bij(A',A)" "g \<in> bij(B,B')"
    unfolding eqpoll_def by blast
  then
  have "converse(g) : B' \<rightarrow> B" "converse(f): A \<rightarrow> A'"
    sorry
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
    show "(\<lambda>x\<in>A \<rightarrow> B. g O x O f) O (\<lambda>x\<in>A' \<rightarrow> B'. converse(g) O x O converse(f)) = id(A' -> B')"
      unfolding id_def 
      apply (rule_tac A="A'\<rightarrow>B'" and B="\<lambda>_.A'\<rightarrow>B'" in fun_extension)
      using comp_fun_apply[OF lam_funtype]
        apply (simp_all)
      sorry
  next
    show "(\<lambda>x\<in>A' \<rightarrow> B'. converse(g) O x O converse(f)) O (\<lambda>x\<in>A -> B. g O x O f) = id(A -> B)"
      sorry
  qed
qed
*)

lemma cexp_eqpoll_cong:
  assumes 
    "A \<approx> A'" "B \<approx> B'"
  shows
    "A \<up> B = A' \<up> B'"
  unfolding cexp_def using cardinal_eqpoll_iff 
    function_space_eqpoll_cong assms
  by simp

(*
definition 
  curry :: "[i,i,i]\<Rightarrow>i" where
  "curry(X,Y,f) \<equiv> \<lambda>x\<in>X. \<lambda>y\<in>Y. f`\<langle>x,y\<rangle>"

definition 
  uncurry :: "[i,i,i]\<Rightarrow>i" where
  "uncurry(X,Y,f) \<equiv> \<lambda>\<langle>x,y\<rangle>\<in>X\<times>Y. f`x`y"
*)

lemma curry_eqpoll:
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

lemma cexp_cexp_cmult: "(\<kappa> \<up> \<nu>1) \<up> \<nu>2 = \<kappa> \<up> (\<nu>2 \<otimes> \<nu>1)"
proof -
  have "(\<kappa> \<up> \<nu>1) \<up> \<nu>2 = (\<nu>1 \<rightarrow> \<kappa>) \<up> \<nu>2"
    using cardinal_eqpoll
    by (intro cexp_eqpoll_cong) (simp_all add:cexp_def)
  also
  have " \<dots> = \<kappa> \<up> (\<nu>2 \<times> \<nu>1)"
    unfolding cexp_def using curry_eqpoll cardinal_cong by blast
  also
  have " \<dots> = \<kappa> \<up> (\<nu>2 \<otimes> \<nu>1)" 
    using cardinal_eqpoll[THEN eqpoll_sym]
    unfolding cmult_def by (intro cexp_eqpoll_cong) (simp)
  finally
  show ?thesis  .
qed

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

lemma cardinal_Pow: "|Pow(X)| = 2 \<up> X" \<comment> \<open>Perhaps it's better with |X|\<close>
  using cardinal_eqpoll_iff[THEN iffD2, OF Pow_eqpoll_function_space]
  unfolding cexp_def by simp

lemma cantor_inj : "f \<notin> inj(Pow(A),A)"
  using inj_imp_surj[OF _ Pow_bottom] cantor_surj by blast

lemma cantor_cexp:
  assumes "Card(\<nu>)"
  shows "\<nu> < 2 \<up> \<nu>"
  using assms Card_is_Ord Card_cexp
proof (intro not_le_iff_lt[THEN iffD1] notI)
  assume "2 \<up> \<nu> \<le> \<nu>"
  then
  have "|Pow(\<nu>)| \<le> \<nu>"
    using cardinal_Pow by simp
  with assms
  have "Pow(\<nu>) \<lesssim> \<nu>"
    using cardinal_eqpoll_iff Card_le_imp_lepoll Card_cardinal_eq
    by auto
  then
  obtain g where "g \<in> inj(Pow(\<nu>), \<nu>)"
    by blast
  then
  show "False"
    using cantor_inj by simp
qed simp

lemma cexp_left_mono:
  assumes "\<kappa>1 \<le> \<kappa>2" 
  shows "\<kappa>1 \<up> \<nu> \<le> \<kappa>2 \<up> \<nu>"
(* \<comment> \<open>short, unreadable proof: \<close>  
  unfolding cexp_def 
  using subset_imp_lepoll[THEN lepoll_imp_Card_le]
    assms le_subset_iff[THEN iffD1, OF assms]
    Pi_weaken_type[of _ _ "\<lambda>_. \<kappa>1" "\<lambda>_. \<kappa>2"] by auto *)
proof -
  from assms
  have "\<kappa>1 \<subseteq> \<kappa>2"
    using le_subset_iff by simp
  then
  have "\<nu> \<rightarrow> \<kappa>1  \<subseteq> \<nu> \<rightarrow> \<kappa>2"
    using Pi_weaken_type by auto
  then
  show ?thesis unfolding cexp_def
    using lepoll_imp_Card_le subset_imp_lepoll by simp
qed

lemma cantor_cexp':
  assumes "2 \<le> \<kappa>" "Card(\<nu>)"
  shows "\<nu> < \<kappa> \<up> \<nu>"
 using cexp_left_mono assms cantor_cexp lt_trans2 by blast

lemma InfCard_cexp:
  assumes "2 \<le> \<kappa>" "InfCard(\<nu>)"
  shows "InfCard(\<kappa> \<up> \<nu>)"
  using assms cantor_cexp'[THEN leI] le_trans Card_cexp
  unfolding InfCard_def by auto

lemma nats_le_InfCard:
  assumes "n\<in>nat" "InfCard(\<kappa>)"
  shows "n \<le> \<kappa>"
  using assms Ord_is_Transset
    le_trans[of n nat \<kappa>, OF le_subset_iff[THEN iffD2]]
  unfolding InfCard_def Transset_def by simp

lemmas InfCard_cexp' = InfCard_cexp[OF nats_le_InfCard, simplified]
  \<comment> \<open>\<^term>\<open>InfCard(\<kappa>) \<Longrightarrow> InfCard(\<nu>) \<Longrightarrow> InfCard(\<kappa> \<up> \<nu>)\<close>\<close>

lemma nat_into_InfCard:
  assumes "n\<in>nat" "InfCard(\<kappa>)"
  shows "n \<in> \<kappa>"
  using assms  le_imp_subset[of nat \<kappa>]
  unfolding InfCard_def by auto

subsection\<open>Alephs are infinite cardinals\<close>

lemmas Aleph_mono = Normal_imp_mono[OF _ Normal_Aleph]

lemma Aleph_zero_eq_nat: "\<aleph>0 = nat"
  unfolding Aleph_def by simp

lemma InfCard_Aleph: 
  notes Aleph_zero_eq_nat[simp]
  assumes "Ord(\<alpha>)" 
  shows "InfCard(\<aleph>\<alpha>)"
proof -
  have "\<not> (\<aleph>\<alpha> \<in> nat)" 
  proof (cases "\<alpha>=0")
    case True
    then show ?thesis using mem_irrefl by auto
  next
    case False
    with \<open>Ord(\<alpha>)\<close>
    have "nat \<in> \<aleph>\<alpha>" using Ord_0_lt[of \<alpha>] ltD  by (auto dest:Aleph_mono)
    then show ?thesis using foundation by blast 
  qed
  with \<open>Ord(\<alpha>)\<close>
  have "\<not> (|\<aleph>\<alpha>| \<in> nat)" 
    using Card_cardinal_eq by auto
  then
  have "\<not> Finite(\<aleph>\<alpha>)" by auto
  with \<open>Ord(\<alpha>)\<close>
  show ?thesis
    using Inf_Card_is_InfCard by simp
qed 

lemmas Limit_Aleph = InfCard_Aleph[THEN InfCard_is_Limit] 

subsection\<open>König's Lemma\<close>

lemma function_space_nonempty:
  assumes "b\<in>B"
  shows "(\<lambda>x\<in>A. b) : A \<rightarrow> B"
  using assms lam_type by force

definition
  str_bound :: "i\<Rightarrow>i" where
  "str_bound(A) \<equiv> \<Union>a\<in>A. succ(a)"

lemma str_bound_type [TC]: "\<forall>a\<in>A. Ord(a) \<Longrightarrow> Ord(str_bound(A))"
  unfolding str_bound_def by auto

lemma str_bound_lt: "\<forall>a\<in>A. Ord(a) \<Longrightarrow> \<forall>a\<in>A. a < str_bound(A)"
  unfolding str_bound_def using str_bound_type  
  by (blast intro:ltI)

lemma cardinal_RepFun_le: "|{f(a) . a\<in>A}| \<le> |A|"
proof -
  have "(\<lambda>x\<in>A. f(x)) \<in> surj(A, {f(a) . a\<in>A})"
    unfolding surj_def using lam_funtype by auto
  then
  show ?thesis
    using  surj_implies_cardinal_le by blast
qed

lemma subset_imp_le_cardinal: "A \<subseteq> B \<Longrightarrow> |A| \<le> |B|"
  using subset_imp_lepoll[THEN lepoll_imp_Card_le] .

lemma lt_cardinal_imp_not_subset: "|A| < |B| \<Longrightarrow> \<not> B \<subseteq> A"
  using subset_imp_le_cardinal le_imp_not_lt by blast

lemma Ord_eq_Collect_lt: "i<\<alpha> \<Longrightarrow> {j\<in>\<alpha>. j<i} = i"
  \<comment> \<open>almost the same proof as @{thm nat_eq_Collect_lt}\<close>
  apply (rule equalityI)
   apply (blast dest: ltD)
  apply (auto simp add: Ord_mem_iff_lt)
   apply (rule Ord_trans ltI[OF _ lt_Ord]; auto simp add:lt_def dest:ltD)+
  done

lemma konigs_lemma:
  notes [dest] = InfCard_is_Card Card_is_Ord
    and [trans] = lt_trans1 lt_trans2
  assumes
    "InfCard(\<kappa>)" "InfCard(\<nu>)" "cf(\<kappa>) \<le> \<nu>"
  shows
    "\<kappa> < \<kappa> \<up> \<nu>"
  using assms(1,2) Card_cexp
proof (intro not_le_iff_lt[THEN iffD1] notI)
  assume "\<kappa> \<up> \<nu> \<le> \<kappa>"
  moreover
  note \<open>InfCard(\<kappa>)\<close>
  moreover from calculation
  have "\<nu> \<rightarrow> \<kappa> \<lesssim> \<kappa>"
    using Card_cardinal_eq[OF InfCard_is_Card, symmetric]
      Card_le_imp_lepoll
    unfolding cexp_def by simp
  ultimately
  obtain G where "G \<in> surj(\<kappa>, \<nu> \<rightarrow> \<kappa>)"
    using inj_imp_surj[OF _ function_space_nonempty,
        OF _ nat_into_InfCard] by blast
  from assms
  obtain f where "f:\<nu> \<rightarrow> \<kappa>" "cf_fun(f,\<kappa>)"
    using cf_le_cf_fun[OF _ InfCard_is_Limit] by blast
  define H where "H(\<alpha>) \<equiv> \<mu> x. x\<in>\<kappa> \<and> (\<forall>m<f`\<alpha>. G`m`\<alpha> \<noteq> x)"
    (is "_ \<equiv> \<mu> x. ?P(\<alpha>,x)") for \<alpha>
  have H_satisfies: "?P(\<alpha>,H(\<alpha>))" if "\<alpha> \<in> \<nu>" for \<alpha>
  proof -
    obtain h where "?P(\<alpha>,h)"
    proof -
      from \<open>\<alpha>\<in>\<nu>\<close> \<open>f:\<nu> \<rightarrow> \<kappa>\<close> \<open>InfCard(\<kappa>)\<close>
      have "f`\<alpha> < \<kappa>"
        using apply_type[of _ _ "\<lambda>_ . \<kappa>"] by (auto intro:ltI)
      have "|{G`m`\<alpha> . m \<in> {x\<in>\<kappa> . x < f`\<alpha>}}| \<le> |{x\<in>\<kappa> . x < f`\<alpha>}|"
        using cardinal_RepFun_le by simp
      also from \<open>f`\<alpha> < \<kappa>\<close> \<open>InfCard(\<kappa>)\<close>
      have "|{x\<in>\<kappa> . x < f`\<alpha>}| < |\<kappa>|"
        using Card_lt_iff[OF lt_Ord, THEN iffD2, of "f`\<alpha>" \<kappa> \<kappa>]
          Ord_eq_Collect_lt[of "f`\<alpha>" \<kappa>] Card_cardinal_eq
        by force
      finally
      have "|{G`m`\<alpha> . m \<in> {x\<in>\<kappa> . x < f`\<alpha>}}| < |\<kappa>|" .
      moreover from \<open>f`\<alpha> < \<kappa>\<close> \<open>InfCard(\<kappa>)\<close>
      have "m<f`\<alpha> \<Longrightarrow> m\<in>\<kappa>" for m
        using Ord_trans[of m "f`\<alpha>" \<kappa>]
        by (auto dest:ltD)
      ultimately
      have "\<exists>h. ?P(\<alpha>,h)"
        using lt_cardinal_imp_not_subset by blast
      with that
      show ?thesis by blast
    qed
    with assms
    show "?P(\<alpha>,H(\<alpha>))"
      using LeastI[of "?P(\<alpha>)" h] lt_Ord Ord_in_Ord
      unfolding H_def by fastforce
  qed
  then
  have "(\<lambda>\<alpha>\<in>\<nu>. H(\<alpha>)): \<nu> \<rightarrow> \<kappa>"
    using lam_type by auto
  with \<open>G \<in> surj(\<kappa>, \<nu> \<rightarrow> \<kappa>)\<close>
  obtain n where "n\<in>\<kappa>" "G`n = (\<lambda>\<alpha>\<in>\<nu>. H(\<alpha>))"
    unfolding surj_def by blast
  moreover
  note \<open>InfCard(\<kappa>)\<close> \<open>f: \<nu> \<rightarrow> \<kappa>\<close> \<open>cf_fun(f,_)\<close>
  ultimately
  obtain \<alpha> where "n < f`\<alpha>" "\<alpha>\<in>\<nu>"
    using Limit_cofinal_fun_lt[OF InfCard_is_Limit] by blast
  moreover from calculation and \<open>G`n = (\<lambda>\<alpha>\<in>\<nu>. H(\<alpha>))\<close>
  have "G`n`\<alpha> = H(\<alpha>)"
    using ltD by simp
  moreover from calculation and H_satisfies
  have "\<forall>m<f`\<alpha>. G`m`\<alpha> \<noteq> H(\<alpha>)" by simp
  ultimately
  show "False" by blast
qed blast+

lemma cf_cexp:
  assumes
    "Card(\<kappa>)" "InfCard(\<nu>)" "2 \<le> \<kappa>"
  shows
    "\<nu> < cf(\<kappa> \<up> \<nu>)"
proof (rule ccontr)
  assume "\<not> \<nu> < cf(\<kappa> \<up> \<nu>)"
  with \<open>InfCard(\<nu>)\<close>
  have "cf(\<kappa> \<up> \<nu>) \<le> \<nu>" 
    using not_lt_iff_le Ord_cf InfCard_is_Card Card_is_Ord by simp
  moreover
  note assms
  moreover from calculation
  have "InfCard(\<kappa> \<up> \<nu>)" using InfCard_cexp by simp
  moreover from calculation
  have "\<kappa> \<up> \<nu> < (\<kappa> \<up> \<nu>) \<up> \<nu>" 
    using konigs_lemma by simp
  ultimately
  show "False" using cexp_cexp_cmult InfCard_csquare_eq by auto
qed

corollary cf_continuum: "\<aleph>0 < cf(2 \<up> \<aleph>0)"
  using cf_cexp InfCard_Aleph nat_into_Card by simp

end