section\<open>Cohen forcing notions\<close>

theory Cohen_Posets_Relative
  imports
    Cohen_Posets\<comment> \<open>FIXME: This theory is going obsolete\<close>
    Delta_System_Relative
begin

lemma (in M_delta) Fnle_nat_closed[intro,simp]:
  assumes "M(I)" "M(J)"
  shows "M(Fnle(\<omega>,I,J))"
  sorry

definition
  \<comment> \<open>"domain collect F"\<close>
  dC_F :: "i \<Rightarrow> i \<Rightarrow> i" where
  "dC_F(A,d) \<equiv> {p \<in> A. domain(p) = d }"

definition
  \<comment> \<open>"domain restrict SepReplace Y\<close>
  drSR_Y :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "drSR_Y(r',D,A,x) \<equiv> {domain(p) .. p\<in>A, restrict(p,r') = x \<and> domain(p) \<in> D}"

locale M_cohen = M_delta +
  assumes
    countable_lepoll_assms2:
    "M(A) \<Longrightarrow> lepoll_assumptions1(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> lepoll_assumptions2(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> lepoll_assumptions3(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(r) \<Longrightarrow> lepoll_assumptions4(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> lepoll_assumptions5(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(x) \<Longrightarrow> lepoll_assumptions6(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> lepoll_assumptions7(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> lepoll_assumptions8(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(r) \<Longrightarrow> lepoll_assumptions9(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> lepoll_assumptions10(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> lepoll_assumptions11(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> M(fa) \<Longrightarrow> M(x) \<Longrightarrow> lepoll_assumptions12(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow>  M(K) \<Longrightarrow> M(r) \<Longrightarrow> lepoll_assumptions13(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> M(fa) \<Longrightarrow> lepoll_assumptions14(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> M(fa) \<Longrightarrow> M(x) \<Longrightarrow> lepoll_assumptions15(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow>  M(K) \<Longrightarrow> lepoll_assumptions16(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow>  M(K) \<Longrightarrow> lepoll_assumptions17(M,A,dC_F,S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> lepoll_assumptions18(M,A,dC_F,S,fa,K,x,f,r)"
    and
    countable_lepoll_assms3:
    "M(A) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions1(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions2(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions3(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(r) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions4(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions5(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(x) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions6(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions7(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions8(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(r) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions9(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions10(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions11(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> M(fa) \<Longrightarrow> M(x) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions12(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow>  M(K) \<Longrightarrow> M(r) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions13(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> M(fa) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions14(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> M(fa) \<Longrightarrow> M(x) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions15(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow>  M(K) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions16(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow>  M(K) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions17(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(K) \<Longrightarrow> M(r) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lepoll_assumptions18(M,A,drSR_Y(r',D),S,fa,K,x,f,r)"
    and
    domain_mem_separation: "M(A) \<Longrightarrow> separation(M, \<lambda>x . domain(x)\<in>A)"
    and
    domain_eq_separation: "M(p) \<Longrightarrow> separation(M, \<lambda>x . domain(x) = p)"
    and
    domain_replacement: "strong_replacement(M, \<lambda>x y . y=<x,domain(x)>)"
    and
    domain_replacement_simp: "strong_replacement(M, \<lambda>x y. y=domain(x))"
    and
    restrict_eq_separation: "M(r) \<Longrightarrow> M(p) \<Longrightarrow> separation(M, \<lambda>x . restrict(x,r) = p)"
    and
    restrict_strong_replacement: "M(r) \<Longrightarrow> strong_replacement(M, \<lambda>x y . y=restrict(x,r))"

context M_cardinal_library
begin

lemma lesspoll_nat_imp_lesspoll_rel: 
  assumes "A \<prec> \<omega>" "M(A)"
  shows "A \<prec>\<^bsup>M\<^esup> \<omega>"
proof -
  note assms
  moreover from this
  obtain f n where "f\<in>bij\<^bsup>M\<^esup>(A,n)" "n\<in>\<omega>" "A \<approx>\<^bsup>M\<^esup> n"
    using lesspoll_nat_is_Finite using Finite_rel_def[of M A] by auto
  moreover from calculation
  have "A \<lesssim>\<^bsup>M\<^esup> \<omega>"
    using lesspoll_nat_is_Finite Infinite_imp_nats_lepoll_rel[of \<omega> n]
    nat_not_Finite eq_lepoll_rel_trans[of A n \<omega>]
    by auto
  moreover from calculation
  have "\<not> g \<in> bij\<^bsup>M\<^esup>(A,\<omega>)" for g 
    using mem_bij_rel unfolding lesspoll_def by auto
  ultimately
  show ?thesis unfolding lesspoll_rel_def eqpoll_rel_def bij_rel_is_inj_rel rex_def
    by auto
qed

lemma Finite_imp_lesspoll_rel_nat:
  assumes "Finite(A)" "M(A)"
  shows "A \<prec>\<^bsup>M\<^esup> \<omega>"
  using Finite_imp_lesspoll_nat assms lesspoll_nat_imp_lesspoll_rel by auto

lemma InfCard_rel_lesspoll_rel_Un:
  includes Ord_dests
  assumes "InfCard_rel(M,\<kappa>)" "A \<prec>\<^bsup>M\<^esup> \<kappa>" "B \<prec>\<^bsup>M\<^esup> \<kappa>"
    and types: "M(\<kappa>)" "M(A)" "M(B)"
  shows "A \<union> B \<prec>\<^bsup>M\<^esup> \<kappa>"
proof -
  from assms
  have "|A|\<^bsup>M\<^esup> < \<kappa>" "|B|\<^bsup>M\<^esup> < \<kappa>"
    using lesspoll_rel_cardinal_rel_lt InfCard_rel_is_Card_rel by auto
  show ?thesis
  proof (cases "Finite(A) \<and> Finite(B)")
    case True
    with assms
    show ?thesis
      using lesspoll_rel_trans2[OF _ le_imp_lepoll_rel, of _ nat \<kappa>]
        Finite_imp_lesspoll_rel_nat[OF Finite_Un]
      unfolding InfCard_rel_def by simp
  next
    case False
    with types
    have "InfCard_rel(M,max(|A|\<^bsup>M\<^esup>,|B|\<^bsup>M\<^esup>))"
      using Infinite_InfCard_rel_cardinal_rel InfCard_rel_is_Card_rel
        le_trans[of nat] not_le_iff_lt[THEN iffD1, THEN leI, of "|A|\<^bsup>M\<^esup>" "|B|\<^bsup>M\<^esup>"]
      unfolding max_def InfCard_rel_def
      by (auto)
    with \<open>M(A)\<close> \<open>M(B)\<close>
    have "|A \<union> B|\<^bsup>M\<^esup> \<le> max(|A|\<^bsup>M\<^esup>,|B|\<^bsup>M\<^esup>)"
      using cardinal_rel_Un_le[of "max(|A|\<^bsup>M\<^esup>,|B|\<^bsup>M\<^esup>)" A B]
        not_le_iff_lt[THEN iffD1, THEN leI, of "|A|\<^bsup>M\<^esup>" "|B|\<^bsup>M\<^esup>" ]
      unfolding max_def by simp
    moreover from \<open>|A|\<^bsup>M\<^esup> < \<kappa>\<close> \<open>|B|\<^bsup>M\<^esup> < \<kappa>\<close>
    have "max(|A|\<^bsup>M\<^esup>,|B|\<^bsup>M\<^esup>) < \<kappa>"
      unfolding max_def by simp
    ultimately
    have "|A \<union> B|\<^bsup>M\<^esup> <  \<kappa>"
      using lt_trans1 by blast
    moreover
    note \<open>InfCard_rel(M,\<kappa>)\<close>
    moreover from calculation types
    have "|A \<union> B|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<kappa>"
      using lt_Card_rel_imp_lesspoll_rel InfCard_rel_is_Card_rel by simp
    ultimately
    show ?thesis
      using cardinal_rel_eqpoll_rel eq_lesspoll_rel_trans[of "A \<union> B" "|A \<union> B|\<^bsup>M\<^esup>" \<kappa>]
        eqpoll_rel_sym types by simp
  qed
qed

end (* M_cardinal_library *)

locale M_add_reals = M_cohen + add_reals
begin

lemmas zero_lesspoll_rel_kappa = zero_lesspoll_rel[OF zero_lt_kappa]

end (* M_add_reals *)

(* FIXME This is old-style discipline *)
(* MOVE THIS to some appropriate place *)
declare (in M_trivial) compat_in_abs[absolut]

definition
  antichain_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" (\<open>antichain\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "antichain_rel(M,P,leq,A) \<equiv> subset(M,A,P) \<and> (\<forall>p[M]. \<forall>q[M].
       p\<in>A \<longrightarrow> q\<in>A \<longrightarrow> p \<noteq> q\<longrightarrow> \<not> is_compat_in(M,P,leq,p,q))"

abbreviation
  antichain_r_set :: "[i,i,i,i] \<Rightarrow> o" (\<open>antichain\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "antichain\<^bsup>M\<^esup>(P,leq,A) \<equiv> antichain_rel(##M,P,leq,A)"

context M_trivial
begin

lemma antichain_abs [absolut]:
  "\<lbrakk> M(A); M(P); M(leq) \<rbrakk> \<Longrightarrow> antichain\<^bsup>M\<^esup>(P,leq,A) \<longleftrightarrow> antichain(P,leq,A)"
  unfolding antichain_rel_def antichain_def by (simp add:absolut)

end (* M_trivial *)

(******************************************************)
(* FIXME This is old-style discipline *)

definition (* completely relational *)
  ccc_rel   :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" (\<open>ccc\<^bsup>_\<^esup>'(_,_')\<close>) where
  "ccc_rel(M,P,leq) \<equiv> \<forall>A[M]. antichain_rel(M,P,leq,A) \<longrightarrow> 
      (\<forall>\<kappa>[M]. is_cardinal(M,A,\<kappa>) \<longrightarrow> (\<exists>om[M]. omega(M,om) \<and> le_rel(M,\<kappa>,om)))"

abbreviation
  ccc_r_set :: "[i,i,i]\<Rightarrow>o" (\<open>ccc\<^bsup>_\<^esup>'(_,_')\<close>) where
  "ccc_r_set(M) \<equiv> ccc_rel(##M)"

context M_cardinals
begin

lemma def_ccc_rel:
  shows
    "ccc\<^bsup>M\<^esup>(P,leq) \<longleftrightarrow> (\<forall>A[M]. antichain\<^bsup>M\<^esup>(P,leq,A) \<longrightarrow> |A|\<^bsup>M\<^esup> \<le> \<omega>)"
  using is_cardinal_iff
  unfolding ccc_rel_def by (simp add:absolut)

end (* M_cardinals *)

(******************  end Discipline  ******************)

context M_add_reals
begin

lemma ccc_Fn_nat:
  notes Sep_and_Replace [simp]\<comment> \<open>FIXME with all \<^term>\<open>SepReplace\<close> instances\<close>
  assumes "M(I)"
  shows "ccc\<^bsup>M\<^esup>(Fn(nat,I,2), Fnle(nat,I,2))"
proof -
  from assms
  have "M(Fn(nat,I,2))" using Fn_nat_eq_FiniteFun by simp
  {
    fix A
    assume "\<not> |A|\<^bsup>M\<^esup> \<le> nat" "M(A)"
    then
    have "M({domain(p) . p \<in> A})"
      using RepFun_closed domain_replacement_simp transM[OF _ \<open>M(A)\<close>]
      by auto
    assume "A \<subseteq> Fn(nat, I, 2)"
    moreover from this
    have "countable_rel(M,{p\<in>A. domain(p) = d})" if "M(d)" for d
    proof (cases "d\<prec>\<^bsup>M\<^esup>nat \<and> d \<subseteq> I")
      case True
      with \<open>A \<subseteq> Fn(nat, I, 2)\<close> \<open>M(A)\<close>
      have "{p \<in> A . domain(p) = d} \<subseteq> d \<rightarrow>\<^bsup>M\<^esup> 2"
        using domain_of_fun function_space_rel_char[of _ 2]
        by (auto,subgoal_tac "M(domain(x))") (force dest: transM)+\<comment> \<open>slow\<close>
      moreover from True \<open>M(d)\<close>
      have "Finite(d \<rightarrow>\<^bsup>M\<^esup> 2)"
        using Finite_Pi[THEN [2] subset_Finite, of _ d "\<lambda>_. 2"]
          lesspoll_rel_nat_is_Finite_rel function_space_rel_char[of _ 2] by auto
      moreover from \<open>M(d)\<close>
      have "M(d \<rightarrow>\<^bsup>M\<^esup> 2)" by simp
      moreover from \<open>M(A)\<close>
      have "M({p \<in> A . domain(p) = d})"
        using separation_closed domain_eq_separation[OF \<open>M(d)\<close>] by simp
      ultimately
      show ?thesis using subset_Finite[of _ "d\<rightarrow>\<^bsup>M\<^esup>2" ]
        by (auto intro!:Finite_imp_countable_rel)
    next
      case False
      with \<open>A \<subseteq> Fn(nat, I, 2)\<close> \<open>M(A)\<close>
      have "{p \<in> A . domain(p) = d} = 0"
        using function_space_rel_char[of _ 2, OF transM, of _ A]
        apply (intro equalityI)
         apply (clarsimp)
         apply (rule lesspoll_nat_imp_lesspoll_rel[of "domain(_)", THEN [2] swap])
           apply (auto dest!: domain_of_fun[ of _ _ "\<lambda>_. 2"] dest:transM)
        done
      then
      show ?thesis using empty_lepoll_relI by auto
    qed
    moreover
    have "uncountable_rel(M,{domain(p) . p \<in> A})"
    proof
      note \<open>M({domain(p). p\<in>A})\<close> \<open>M(A)\<close>
      moreover from this
      have "x \<in> A \<Longrightarrow> M({p \<in> A . domain(p) = domain(x)})" for x
        using separation_closed domain_eq_separation transM[OF _ \<open>M(A)\<close>] by simp
      ultimately
      interpret M_cardinal_UN_lepoll _ "\<lambda>d. {p \<in> A. domain(p) = d }" "{domain(p). p\<in>A}"
        using countable_lepoll_assms2 unfolding dC_F_def
        by unfold_locales (auto dest: transM)
      from \<open>A \<subseteq> Fn(nat, I, 2)\<close>
      have x:"(\<Union>d\<in>{domain(p) . p \<in> A}. {p\<in>A. domain(p) = d}) = A"
        by auto
      moreover
      assume "countable_rel(M,{domain(p) . p \<in> A})"
      moreover
      note \<open>\<And>d. M(d) \<Longrightarrow> countable_rel(M,{p\<in>A. domain(p) = d})\<close>
      moreover from \<open>M(A)\<close>
      have "p\<in>A \<Longrightarrow> M(domain(p))" for p by (auto dest: transM)
      ultimately
      have "countable_rel(M,A)"
        using countable_rel_imp_countable_rel_UN
        by auto
      with \<open>\<not> |A|\<^bsup>M\<^esup> \<le> nat\<close> \<open>M(A)\<close>
      show False
        using countable_rel_iff_cardinal_rel_le_nat by simp
    qed
    moreover from \<open>A \<subseteq> Fn(nat, I, 2)\<close> \<open>M(A)\<close>
    have "p \<in> A \<Longrightarrow> Finite(domain(p))" for p
      using lesspoll_rel_nat_is_Finite_rel[of "domain(p)"]
        lesspoll_nat_imp_lesspoll_rel[of "domain(p)"]
        domain_of_fun[of p _ "\<lambda>_. 2"] by (auto dest:transM)
    moreover
    note \<open>M({domain(p). p\<in>A})\<close>
    ultimately
    obtain D where "delta_system(D)" "D \<subseteq> {domain(p) . p \<in> A}" "D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "M(D)"
      using delta_system_uncountable_rel[of "{domain(p) . p \<in> A}"] by auto
    then
    have delta:"\<forall>d1\<in>D. \<forall>d2\<in>D. d1 \<noteq> d2 \<longrightarrow> d1 \<inter> d2 = \<Inter>D"
      using delta_system_root_eq_Inter
      by simp
    moreover from \<open>D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close> \<open>M(D)\<close>
    have "uncountable_rel(M,D)"
      using uncountable_rel_iff_subset_eqpoll_rel_Aleph_rel1 by auto
    moreover from this and \<open>D \<subseteq> {domain(p) . p \<in> A}\<close>
    obtain p1 where "p1 \<in> A" "domain(p1) \<in> D"
      using uncountable_rel_not_empty[of D] by blast
    moreover from this and \<open>p1 \<in> A \<Longrightarrow> Finite(domain(p1))\<close>
    have "Finite(domain(p1))" using Finite_domain by simp
    moreover
    define r where "r \<equiv> \<Inter>D"
    moreover from \<open>M(D)\<close>
    have "M(r)" "M(r\<times>2)" unfolding r_def by simp_all
    ultimately
    have "Finite(r)" using subset_Finite[of "r" "domain(p1)"] by auto
    have "countable_rel(M,{restrict(p,r) . p\<in>A})"
    proof -
      note \<open>M(Fn(nat, I, 2))\<close> \<open>M(r)\<close>
      moreover from this
      have "f\<in>Fn(nat, I, 2) \<Longrightarrow> M(restrict(f,r))" for f
        by (blast dest: transM)
      ultimately
      have "f\<in>Fn(nat, I, 2) \<Longrightarrow> restrict(f,r) \<in> Pow_rel(M,r \<times> 2)" for f
        using restrict_subset_Sigma[of f _ "\<lambda>_. 2" r] Pow_rel_char
        by (auto dest!:FnD simp: Pi_def) (auto dest:transM)
      with \<open>A \<subseteq> Fn(nat, I, 2)\<close>
      have "{restrict(f,r) . f \<in> A } \<subseteq> Pow_rel(M,r \<times> 2)"
        by fast
      moreover from \<open>M(A)\<close> \<open>M(r)\<close>
      have "M({restrict(f,r) . f \<in> A })"
        using RepFun_closed restrict_strong_replacement transM[OF _ \<open>M(A)\<close>] by auto
      moreover
      note \<open>Finite(r)\<close> \<open>M(r)\<close>
      ultimately
      show ?thesis
        using Finite_Sigma[THEN Finite_Pow_rel, of r "\<lambda>_. 2"]
        by (intro Finite_imp_countable_rel) (auto intro:subset_Finite)
    qed
    moreover from \<open>M(A)\<close> \<open>M(D)\<close>
    have "M({p\<in>A. domain(p) \<in> D})"
      using domain_mem_separation by simp
    have "uncountable_rel(M,{p\<in>A. domain(p) \<in> D})" (is "uncountable_rel(M,?X)")
    proof
      from \<open>D \<subseteq> {domain(p) . p \<in> A}\<close>
      have "(\<lambda>p\<in>?X. domain(p)) \<in> surj(?X, D)"
        using lam_type unfolding surj_def by auto
      moreover from \<open>M(A)\<close> \<open>M(?X)\<close>
      have "M(\<lambda>p\<in>?X. domain(p))"
        using lam_closed[OF domain_replacement \<open>M(?X)\<close>] transM[OF _ \<open>M(?X)\<close>] by simp
      moreover
      note \<open>M(?X)\<close> \<open>M(D)\<close>
      moreover from calculation
      have surjection:"(\<lambda>p\<in>?X. domain(p)) \<in> surj\<^bsup>M\<^esup>(?X, D)"
        using surj_rel_char by simp
      moreover
      assume "countable_rel(M,?X)"
      moreover
      note \<open>uncountable_rel(M,D)\<close>
      ultimately
      show False
        using surj_rel_countable_rel[OF _ surjection] by auto
    qed
    moreover
    have "D = (\<Union>f\<in>Pow_rel(M,r\<times>2) . {domain(p) .. p\<in>A, restrict(p,r) = f \<and> domain(p) \<in> D})"
    proof -
      {
        fix z
        assume "z \<in> D"
        with \<open>M(D)\<close>
        have \<open>M(z)\<close> by (auto dest:transM)
        from \<open>z\<in>D\<close> \<open>D \<subseteq> _\<close> \<open>M(A)\<close>
        obtain p  where "domain(p) = z" "p \<in> A" "M(p)"
          by (auto dest:transM)
        moreover from \<open>A \<subseteq> Fn(nat, I, 2)\<close> \<open>M(z)\<close> and this
        have "p : z \<rightarrow>\<^bsup>M\<^esup> 2"
          using domain_of_fun function_space_rel_char by (auto dest!:FnD)
        moreover from this \<open>M(z)\<close>
        have "p : z \<rightarrow> 2"
          using domain_of_fun function_space_rel_char by (auto)
        moreover from this \<open>M(r)\<close>
        have "restrict(p,r) \<subseteq> r \<times> 2"
          using function_restrictI[of p r] fun_is_function[of p z "\<lambda>_. 2"]
            restrict_subset_Sigma[of p z "\<lambda>_. 2" r] function_space_rel_char
          by (auto simp:Pi_def)
        moreover from \<open>M(p)\<close> \<open>M(r)\<close>
        have "M(restrict(p,r))" by simp
        moreover
        note \<open>M(r)\<close>
        ultimately
        have "\<exists>p\<in>A.  restrict(p,r) \<in> Pow_rel(M,r\<times>2) \<and> domain(p) = z"
          using Pow_rel_char by auto
      }
      then
      show ?thesis
        by (intro equalityI) (force)+
    qed
    from \<open>M(D)\<close> \<open>M(A)\<close> \<open>M(r)\<close>
    have "M({domain(p) .. p\<in>A, restrict(p,r) = f \<and> domain(p) \<in> D})" (is "M(?Y(f))")
      if "M(f)" for f
      using RepFun_closed domain_replacement_simp
        separation_conj[OF restrict_eq_separation[OF \<open>M(r)\<close> \<open>M(f)\<close>]
                           domain_mem_separation[OF \<open>M(D)\<close>]]
        transM[OF _ \<open>M(D)\<close>]
      by simp
    obtain f where "uncountable_rel(M,?Y(f))" "M(f)"
    proof -
      note \<open>M(r)\<close>
      moreover from this
      have "M(Pow\<^bsup>M\<^esup>(r \<times> 2))" by simp
      moreover
      note \<open>M(A)\<close> \<open>\<And>f. M(f) \<Longrightarrow> M(?Y(f))\<close> \<open>M(D)\<close>
      ultimately
      interpret M_cardinal_UN_lepoll _ ?Y "Pow_rel(M,r\<times>2)"
        using countable_lepoll_assms3[where S="Pow_rel(M,r\<times>2)" and A=A and D=D and r'=r]
        unfolding lepoll_assumptions_defs drSR_Y_def
        apply unfold_locales defer defer prefer 6 apply (blast dest: transM)
        by (unfold lepoll_assumptions_defs, fast) (auto dest:transM)\<comment> \<open>NOTE VERY SLOW: 25s\<close>
      {
        from \<open>Finite(r)\<close> \<open>M(r)\<close>
        have "countable_rel(M,Pow_rel(M,r\<times>2))"
          using Finite_Sigma[THEN Finite_Pow_rel] Finite_imp_countable_rel
          by simp
        moreover
        assume "M(f) \<Longrightarrow> countable_rel(M,?Y(f))" for f
        moreover
        note \<open>D = (\<Union>f\<in>Pow_rel(M,r\<times>2) .?Y(f))\<close> \<open>M(r)\<close>
        moreover
        note \<open>uncountable_rel(M,D)\<close>
        ultimately
        have "False"
          using countable_rel_imp_countable_rel_UN by (auto dest: transM)
      }
      with that
      show ?thesis by auto
    qed
    moreover from this and \<open>M(f) \<Longrightarrow> M(?Y(f))\<close>
    have "M(?Y(f))" by blast
    ultimately
    obtain j where "j \<in> inj_rel(M,nat, ?Y(f))" "M(j)"
      using uncountable_rel_iff_nat_lt_cardinal_rel[THEN iffD1, THEN leI,
          THEN cardinal_rel_le_imp_lepoll_rel, THEN lepoll_relD]
      by auto
    with \<open>M(?Y(f))\<close>
    have "j`0 \<noteq> j`1" "j`0 \<in> ?Y(f)" "j`1 \<in> ?Y(f)"
      using inj_is_fun[THEN apply_type, of j nat "?Y(f)"]
        inj_rel_char
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
  moreover from assms
  have "M(Fnle(\<omega>,I,2))" by simp
  moreover note \<open>M(Fn(\<omega>,I,2))\<close>
  ultimately
  show ?thesis using def_ccc_rel by (auto simp:absolut antichain_def) fastforce
qed

end (* M_add_reals *)

end