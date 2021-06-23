section\<open>The Delta System Lemma, Relativized\label{sec:dsl-rel}\<close>

theory Delta_System_Relative
  imports 
    Cardinal_Library_Relative
    "../Delta_System_Lemma/Delta_System"
begin

relativize functional "delta_system" "delta_system_rel" external

context M_cardinal_library
begin

lemma Finite_imp_succ_cardinal_rel_Diff:
     "[| Finite(A);  a \<in> A; M(A) ; M(a) |] ==> succ(|A-{a}|\<^bsup>M\<^esup>) = |A|\<^bsup>M\<^esup>"
(* apply (rule_tac b = A in cons_Diff [THEN subst], assumption)
apply (simp add: Finite_imp_cardinal_cons Diff_subset [THEN subset_Finite])
apply (simp add: cons_Diff)
done
 *) sorry

lemma delta_system_Aleph_rel1:
  assumes "\<forall>A\<in>F. Finite(A)" "F \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "M(F)"
  shows "\<exists>D[M]. D \<subseteq> F \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
proof -
  text\<open>Since all members are finite,\<close>
  from \<open>\<forall>A\<in>F. Finite(A)\<close>
  have "(\<lambda>A\<in>F. |A|\<^bsup>M\<^esup>) : F \<rightarrow>\<^bsup>M\<^esup> \<omega>" (is "?cards : _")
    by (rule_tac lam_type) simp
  moreover from this
  have a:"?cards -`` {n} = { A\<in>F . |A|\<^bsup>M\<^esup> = n }" for n
    using vimage_lam by auto
  moreover
  note \<open>F \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
  moreover from calculation
  text\<open>there are uncountably many have the same cardinal:\<close>
  obtain n where "n\<in>\<omega>" "|?cards -`` {n}|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using eqpoll_rel_Aleph_rel1_cardinal_rel_vimage[of F ?cards] by auto
  moreover
  define G where "G \<equiv> ?cards -`` {n}"
  moreover from calculation
  have "G \<subseteq> F" by auto
  ultimately
  text\<open>Therefore, without loss of generality, we can assume that all
  elements of the family have cardinality \<^term>\<open>n\<in>\<omega>\<close>.\<close>
  have "A\<in>G \<Longrightarrow> |A|\<^bsup>M\<^esup> = n" and "G \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" and "M(G)" for A
    using cardinal_rel_Card_rel_eqpoll_rel_iff by auto
  with \<open>n\<in>\<omega>\<close>
  text\<open>So we prove the result by induction on this \<^term>\<open>n\<close> and
  generalizing \<^term>\<open>G\<close>, since the argument requires changing the
  family in order to apply the inductive hypothesis.\<close>
  have "\<exists>D[M]. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  proof (induct arbitrary:G)
    case 0 \<comment> \<open>This case is impossible\<close>
    then
    have "G \<subseteq> {0}"
      using cardinal_rel_0_iff_0 by (blast dest:transM)
    with \<open>G \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close> \<open>M(G)\<close>
    show ?case
      using nat_lt_Aleph_rel1 subset_imp_le_cardinal[of G "{0}"]
        lt_trans2 cardinal_rel_Card_rel_eqpoll_rel_iff by auto
  next
    case (succ n)
    then
    have "\<forall>a\<in>G. Finite(a)"
      using Finite_cardinal_rel_iff' nat_into_Finite[of "succ(n)"]
      by fastforce*
    show "\<exists>D[M]. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    proof (cases "\<exists>p[M]. {A\<in>G . p \<in> A} \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>")
      case True \<comment> \<open>the positive case, uncountably many sets with a
                    common element\<close>
      then
      obtain p where "{A\<in>G . p \<in> A} \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" by blast
      moreover from this
      have "{A-{p} . A\<in>{X\<in>G. p\<in>X}} \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" (is "?F \<approx>\<^bsup>M\<^esup> _")
        using Diff_bij_rel[of "{A\<in>G . p \<in> A}" "{p}"]
          comp_bij_rel[OF bij_rel_converse_bij_rel, where C="\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"] by fast
      text\<open>Now using the hypothesis of the successor case,\<close>
      moreover from \<open>\<And>A. A\<in>G \<Longrightarrow> |A|\<^bsup>M\<^esup>=succ(n)\<close> \<open>\<forall>a\<in>G. Finite(a)\<close>
        and this
      have "p\<in>A \<Longrightarrow> A\<in>G \<Longrightarrow> |A - {p}|\<^bsup>M\<^esup> = n" for A
        using Finite_imp_succ_cardinal_rel_Diff[of _ p] by force*
      moreover from this and \<open>n\<in>\<omega>\<close>
      have "\<forall>a\<in>?F. Finite(a)"
        using Finite_cardinal_rel_iff' nat_into_Finite by auto*
      moreover
      text\<open>we may apply the inductive hypothesis to the new family \<^term>\<open>?F\<close>:\<close>
      note \<open>(\<And>A. A \<in> ?F \<Longrightarrow> |A|\<^bsup>M\<^esup> = n) \<Longrightarrow> ?F \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> M(?F) \<Longrightarrow>
             \<exists>D[M]. D \<subseteq> ?F \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
      moreover
      have "M(?F)" sorry
      ultimately
      obtain D where "D\<subseteq>{A-{p} . A\<in>{X\<in>G. p\<in>X}}" "delta_system(D)" "D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
             "M(D)"
        by auto
      moreover from this
      obtain r where "\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
        by fastforce
      then
      have "\<forall>A\<in>D.\<forall>B\<in>D. A\<union>{p} \<noteq> B\<union>{p}\<longrightarrow>(A \<union> {p}) \<inter> (B \<union> {p}) = r\<union>{p}"
        by blast
      ultimately
      have "delta_system({B \<union> {p} . B\<in>D})" (is "delta_system(?D)")
        by fastforce
      moreover
      have "M(?D)" sorry
      moreover from \<open>D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
      have "|D|\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "Infinite(D)"
        using cardinal_rel_eqpoll_rel_iff
        by (auto intro!: uncountable_rel_iff_subset_eqpoll_rel_Aleph_rel1[THEN iffD2]
            uncountable_rel_imp_Infinite) (force*)
      moreover from this
      have "?D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
        using cardinal_rel_map_Un[of D "{p}"] naturals_lt_nat
          cardinal_rel_eqpoll_rel_iff[THEN iffD1] by simp
      moreover
      note \<open>D \<subseteq> {A-{p} . A\<in>{X\<in>G. p\<in>X}}\<close>
      have "?D \<subseteq> G"
      proof -
        {
          fix A
          assume "A\<in>G" "p\<in>A"
          moreover from this
          have "A = A - {p} \<union> {p}"
            by blast
          ultimately
          have "A -{p} \<union> {p} \<in> G"
            by auto
        }
        with \<open>D \<subseteq> {A-{p} . A\<in>{X\<in>G. p\<in>X}}\<close>
        show ?thesis
          by blast
      qed
      moreover
      note \<open>M(?D)\<close>
      ultimately
      show "\<exists>D[M]. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" by auto
    next
      case False
      note \<open>\<not> (\<exists>p[M]. {A \<in> G . p \<in> A} \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)\<close> \<comment> \<open>the other case\<close>
      moreover from \<open>G \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
      have "{A \<in> G . p \<in> A} \<lesssim> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" (is "?G(p) \<lesssim> _") for p
        (* by (blast intro:lepoll_rel_eq_trans[OF subset_imp_lepoll_rel]) *) sorry
      ultimately
      have "?G(p) \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" for p
        unfolding lesspoll_rel_def by simp
      then (* may omit the previous step if unfolding here: *)
      have "?G(p) \<lesssim>\<^bsup>M\<^esup> \<omega>" for p
        using lesspoll_rel_Aleph_rel_plus_one[of 0] Aleph_rel_zero by auto
      moreover
      have "{A \<in> G . S \<inter> A \<noteq> 0} = (\<Union>p\<in>S. ?G(p))" for S
        by auto
      ultimately
      have "countable_rel(M,S) \<Longrightarrow> countable_rel(M,{A \<in> G . S \<inter> A \<noteq> 0})" for S
        using InfCard_rel_nat Card_rel_nat
         le_Card_rel_iff[THEN iffD2, THEN [3] leqpoll_rel_imp_cardinal_rel_UN_le,
           THEN [2] le_Card_rel_iff[THEN iffD1], of \<omega> S]
        unfolding countable_rel_def by simp
      text\<open>For every countable_rel subfamily of \<^term>\<open>G\<close> there is another some
      element disjoint from all of them:\<close>
      have "\<exists>A\<in>G. \<forall>S\<in>X. S \<inter> A = 0" if "|X|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "X \<subseteq> G" for X
      proof -
        from \<open>n\<in>\<omega>\<close> \<open>\<And>A. A\<in>G \<Longrightarrow> |A|\<^bsup>M\<^esup> = succ(n)\<close>
        have "A\<in>G \<Longrightarrow> Finite(A)" for A
          using cardinal_rel_Card_rel_eqpoll_rel_iff
          unfolding Finite_def by fastforce*
        with \<open>X\<subseteq>G\<close>
        have "A\<in>X \<Longrightarrow> countable_rel(M,A)" for A
          using Finite_imp_countable\<comment> \<open>FIXME: bad name\<close> by auto
        with \<open>|X|\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
        have "countable_rel(M,\<Union>X)"
          using Card_rel_nat[THEN cardinal_rel_lt_csucc_rel_iff, of X]
            countable_rel_union_countable \<comment> \<open>FIXME: bad name\<close>
            countable_rel_iff_cardinal_rel_le_nat
          unfolding Aleph_rel_def by simp
        with \<open>countable_rel(M,_) \<Longrightarrow> countable_rel(M,{A \<in> G . _  \<inter> A \<noteq> 0})\<close>
        have "countable_rel(M,{A \<in> G . (\<Union>X) \<inter> A \<noteq> 0})" .
        with \<open>G \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
        obtain B where "B\<in>G" "B \<notin> {A \<in> G . (\<Union>X) \<inter> A \<noteq> 0}" 
          using nat_lt_Aleph_rel1 cardinal_rel_Card_rel_eqpoll_rel_iff[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" G]
            uncountable_rel_not_subset_countable\<comment> \<open>FIXME: bad name\<close>
            [of "{A \<in> G . (\<Union>X) \<inter> A \<noteq> 0}" G]
            uncountable_rel_iff_nat_lt_cardinal_rel
          by auto
        then
        show "\<exists>A\<in>G. \<forall>S\<in>X. S \<inter> A = 0" by auto
      qed
      moreover from \<open>G \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
      obtain b where "b\<in>G"
        using uncountable_rel_iff_subset_eqpoll_rel_Aleph_rel1
          uncountable_rel_not_empty by blast*
      ultimately
      text\<open>Hence, the hypotheses to perform a bounded-cardinal selection
      are satisfied,\<close>
      obtain S where "S:\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<rightarrow>G" "\<alpha>\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> \<beta>\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> \<alpha><\<beta> \<Longrightarrow> S`\<alpha> \<inter> S`\<beta> = 0"
        for \<alpha> \<beta>
        using bounded_cardinal_rel_selection[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" G "\<lambda>s a. s \<inter> a = 0" b]
        by force*
      then
      have "\<alpha> \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> \<beta> \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> \<alpha>\<noteq>\<beta> \<Longrightarrow> S`\<alpha> \<inter> S`\<beta> = 0" for \<alpha> \<beta>
        using lt_neq_symmetry[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<lambda>\<alpha> \<beta>. S`\<alpha> \<inter> S`\<beta> = 0"] Card_rel_is_Ord
        by auto (blast*)
      text\<open>and a symmetry argument shows that obtained \<^term>\<open>S\<close> is
      an injective  \<^term>\<open>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>-sequence of disjoint elements of \<^term>\<open>G\<close>.\<close>
      moreover from this and \<open>\<And>A. A\<in>G \<Longrightarrow> |A|\<^bsup>M\<^esup> = succ(n)\<close> \<open>S : \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightarrow> G\<close>
      have "S \<in> inj_rel(M,\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, G)"
        using cardinal_rel_succ_not_0 Int_eq_zero_imp_not_eq[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<lambda>x. S`x"]
        unfolding inj_rel_def by fastforce*
      moreover from calculation
      have "range(S) \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
        using inj_rel_bij_rel_range eqpoll_rel_sym unfolding eqpoll_rel_def by fast*
      moreover from calculation
      have "range(S) \<subseteq> G"
        using inj_rel_is_fun range_fun_subset_codomain by fast*
      ultimately
      show "\<exists>D[M]. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
        using inj_rel_is_fun ZF_Library.range_eq_image[of S "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" G]
          image_function[OF fun_is_function, OF inj_rel_is_fun, of S "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" G]
          domain_of_fun[OF inj_rel_is_fun, of S "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" G]
        by (rule_tac x="S``\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" in rexI) auto
      text\<open>This finishes the successor case and hence the proof.\<close>
    qed
  qed
  with \<open>G \<subseteq> F\<close>
  show ?thesis by blast
qed

lemma delta_system_uncountable_rel:
  assumes "\<forall>A\<in>F. Finite(A)" "uncountable_rel(M,F)" "M(F)"
  shows "\<exists>D[M]. D \<subseteq> F \<and> delta_system(D) \<and> D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
proof -
  from assms
  obtain S where "S \<subseteq> F" "S \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "M(S)"
    using uncountable_rel_iff_subset_eqpoll_rel_Aleph_rel1[of F] by auto
  moreover from \<open>\<forall>A\<in>F. Finite(A)\<close> and this
  have "\<forall>A\<in>S. Finite(A)" by auto
  ultimately
  show ?thesis using delta_system_Aleph_rel1[of S]
    by (auto dest:transM)
qed

end (* M_cardinal_rel_library *)

end