theory Konig
  imports
    ZF.Cardinal_AC Delta_System \<comment> \<open>The last one only for @{thm InfCard_Aleph}\<close>
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
      find_theorems "( _ O _)`_"
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
next \<comment> \<open>one composition is the identity\<dots>\<close>
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

lemma cantor_cexp:
  assumes "Card(\<nu>)"
  shows "\<nu> < 2 \<up> \<nu>"
proof (rule le_neq_imp_lt)
  show "\<nu> \<le> 2 \<up> \<nu>"
    sorry
  show "\<nu> \<noteq> 2 \<up> \<nu>"
  proof
    assume "\<nu> = 2 \<up> \<nu>"
    then
    have "\<nu> = |Pow(\<nu>)|"
      using cardinal_Pow by simp
    with assms
    have "\<nu> \<approx> Pow(\<nu>)"
      using cardinal_eqpoll_iff Card_cardinal_eq
      by force
    then
    obtain g where "g \<in> surj(\<nu>, Pow(\<nu>))"
      unfolding eqpoll_def using bij_is_surj by blast
    then
    show "False"
      using cantor_surj by simp
  qed
qed

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

subsection\<open>König's Lemma\<close>

lemma konigs_lemma:
  assumes
    "InfCard(\<kappa>)" "Card(\<nu>)" "cf(\<kappa>) \<le> \<nu>"
  shows
    "\<kappa> < \<kappa> \<up> \<nu>"
  sorry

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
    using konigs_lemma InfCard_is_Card Card_is_Ord by simp
  ultimately
  show "False" using cexp_cexp_cmult InfCard_csquare_eq by auto
qed

corollary cf_continuum: "\<aleph>0 < cf(2 \<up> \<aleph>0)"
  using cf_cexp InfCard_Aleph nat_into_Card by simp

end