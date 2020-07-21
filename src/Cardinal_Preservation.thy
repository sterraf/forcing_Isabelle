theory Cardinal_Preservation
  imports
    Cardinal_AC_Relative
    Forcing_Main

begin

(* MOVE THIS to some appropriate place *)
declare (in M_trivial) compat_in_abs[absolut]

definition
  antichain_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "antichain_rel(M,P,leq,A) \<equiv> subset(M,A,P) \<and> (\<forall>p[M]. \<forall>q[M].
       p\<in>A \<longrightarrow> q\<in>A \<longrightarrow> \<not> is_compat_in(M,P,leq,p,q))"

lemma (in M_trivial) antichain_abs [absolut]: 
  "\<lbrakk>M(X); M(A); M(r); M(P); M(leq)\<rbrakk> \<Longrightarrow> 
  antichain_rel(M,P,leq,A) \<longleftrightarrow> antichain(P,leq,A)"
  unfolding antichain_rel_def antichain_def by (simp add:absolut)


(******************************************************)
subsection\<open>Discipline for \<^term>\<open>ccc\<close>\<close>

definition (* completely relational *)
  ccc_rel   :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "ccc_rel(M,P,leq) \<equiv> \<forall>A[M]. antichain_rel(M,P,leq,A) \<longrightarrow> 
      (\<forall>\<kappa>[M]. is_cardinal(M,A,\<kappa>) \<longrightarrow> (\<exists>om[M]. omega(M,om) \<and> le_rel(M,\<kappa>,om)))"

context M_cardinals
begin

lemma def_ccc_rel:
  assumes
    "M(i)"
  shows
    "ccc_rel(M,P,leq) \<longleftrightarrow> (\<forall>A[M]. antichain_rel(M,P,leq,A) \<longrightarrow> |A|r \<le> nat)"
  using assms cardinal_rel_iff
  unfolding ccc_rel_def by (simp add:absolut)

end (* M_cardinals *)

(******************  end Discipline  ******************)

sublocale M_ZF_trans \<subseteq> M_cardinal_AC "##M"
  sorry

context G_generic begin

notation cardinal_rel (\<open>|_|\<^sup>M\<close>)
notation ccc_rel (\<open>ccc\<^sup>M\<close>)
notation check (\<open>_\<^sup>v\<close> [101] 100)
notation function_space_rel (infix \<open>\<rightarrow>\<^sup>M\<close> 60)
notation inj_rel (\<open>inj\<^sup>M\<close>)

\<comment> \<open>NOTE: The following bundled additions to the simpset might be of
    use later on, perhaps add them globally to some appropriate
    locale.\<close>
lemmas generic_simps = generic[THEN one_in_G, THEN valcheck, OF one_in_P]
  generic[THEN one_in_G, THEN M_subset_MG, THEN subsetD]
  check_in_M GenExtI P_in_M
lemmas generic_dests = M_genericD[OF generic] M_generic_compatD[OF generic]

bundle G_generic_lemmas = generic_simps[simp] generic_dests[dest]

text\<open>The following interpretation makes the simplifications from the
locales \<open>M_trans\<close>, \<open>M_trivial\<close>, etc., available for \<^term>\<open>M[G]\<close> \<close>
interpretation mgzf: M_ZF_trans "M[G]"
  using Transset_MG generic pairing_in_MG Union_MG
    extensionality_in_MG power_in_MG foundation_in_MG
    strong_replacement_in_MG separation_in_MG infinity_in_MG
  by unfold_locales simp_all

context
  includes G_generic_lemmas
begin

\<comment> \<open>@{thm mgzf.apply_closed} does not simplifies appropriately\<close>
lemmas apply_closed_in_MG = mgzf.apply_closed[simplified, simp]
lemmas apply_closed_in_M = apply_closed[simplified, simp]
lemmas nonempty_ctm = nonempty[simplified, simp]

\<comment> \<open>Kunen IV.3.5\<close>
lemma ccc_fun_approximation_lemma:
  assumes "ccc\<^sup>M(##M,P,leq)" "A\<in>M" "B\<in>M" "f\<in>M[G]" "f : A \<rightarrow> B"
  shows 
    "\<exists>F\<in>M. F : A \<rightarrow> Pow(B) \<and> (\<forall>a\<in>A. f`a \<in> F`a \<and> |F`a|\<^sup>M \<le> nat)"
proof -
  let ?\<phi>="typed_function_fm(1,2,0)"\<comment> \<open>formula for \<^term>\<open>f : A\<rightarrow> B\<close>\<close>
  from \<open>f\<in>M[G]\<close>
  obtain f_dot where "f = val(G,f_dot)" "f_dot\<in>M" using GenExtD by force
  with assms
  obtain p where "p \<tturnstile> ?\<phi> [f_dot, A\<^sup>v, B\<^sup>v]" "p\<in>G"
    using generic truth_lemma[of ?\<phi> G "[f_dot, A\<^sup>v, B\<^sup>v]"]
    by (auto simp add:nat_simp_union arity_typed_function_fm
        \<comment> \<open>NOTE: type-checking is not performed here by the Simplifier\<close>
        typed_function_type)
  define F where "F\<equiv>\<lambda>a\<in>A. {b\<in>B. \<exists>q\<in>P. q \<preceq> p \<and> (q \<tturnstile> fun_apply_fm(0,1,2) [f_dot, a\<^sup>v, b\<^sup>v])}"
  let ?app_fm="fun_apply_fm(0,1,2)"\<comment> \<open>formula for \<open>f`x=z\<close>\<close>
  have "F \<in> M" sorry
  moreover
  have "f`a \<in> F`a" if "a \<in> A" for a
  proof -
    note \<open>f: A \<rightarrow> B\<close> \<open>a \<in> A\<close>
    moreover from this
    have "f ` a \<in> B" by simp
    moreover
    note \<open>f\<in>M[G]\<close> \<open>a\<in>A\<close> \<open>A\<in>M\<close>
    moreover from calculation
    have "M[G], [f, a, f`a] \<Turnstile> ?app_fm"
      by (auto dest:transM)
    moreover
    note \<open>B\<in>M\<close> \<open>f`a\<in>B\<close> \<open>f = val(G,f_dot)\<close>
    moreover from calculation
    have "a\<in>M[G]" "a\<in>M" "val(G, f_dot)`a\<in>M"
      by (auto dest:transM)
    moreover
    note \<open>f_dot\<in>M\<close>
    moreover from calculation
    obtain r where "r \<tturnstile> ?app_fm [f_dot, a\<^sup>v, (f`a)\<^sup>v]" "r\<in>G"
      using generic truth_lemma[of ?app_fm G "[f_dot, a\<^sup>v, (f`a)\<^sup>v]"]
      by (auto simp add: nat_simp_union arity_fun_apply_fm
          fun_apply_type)
    moreover from this and \<open>p\<in>G\<close>
    obtain q where "q \<preceq> p" "q \<preceq> r" "q \<in> G" by auto
    ultimately
    have "q \<tturnstile> ?app_fm [f_dot, a\<^sup>v, (f`a)\<^sup>v]" "q\<in>G"
      using strengthening_lemma[of r ?app_fm _ "[f_dot, a\<^sup>v, (f`a)\<^sup>v]"]
      by (auto simp add: nat_simp_union arity_fun_apply_fm
          fun_apply_type)
    with \<open>f`a \<in> B\<close> \<open>q \<preceq> p\<close>
    have "f`a \<in> {b\<in>B . \<exists>q\<in>P. q \<preceq> p \<and> q \<tturnstile> ?app_fm [f_dot, a\<^sup>v, b\<^sup>v]}"
      by blast
    with \<open>a\<in>A\<close>
    show ?thesis unfolding F_def by simp
  qed
  moreover
  have "|F`a|\<^sup>M \<le> nat" if "a \<in> A" for a
  proof -
    let ?Q="\<lambda>b. {q\<in>P. q \<preceq> p \<and> (q \<tturnstile> ?app_fm [f_dot, a\<^sup>v, b\<^sup>v])}"
    interpret M_Pi_assumptions_choice "##M" "F`a" ?Q sorry
    have "\<exists>y. y \<in> ?Q(b)" if "b \<in> F`a" for b sorry
    then
    obtain q where "q \<in> Pi_rel(F`a,?Q)" "q\<in>M" using AC_Pi_rel by auto
    moreover from \<open>F \<in> M\<close>
    have "F`a \<in> M" sorry
    moreover from calculation
    have "q : F`a \<rightarrow>\<^sup>M P" sorry
    moreover
    have "q`b \<bottom> q`c" if "b \<noteq> c" "b \<in> F`a" "c \<in> F`a" for b c sorry
    moreover from this
    have "q`b \<noteq> q`c" if "b \<noteq> c" "b \<in> F`a" "c \<in> F`a" for b c sorry
    ultimately
    have "q \<in> inj_rel(F`a,P)" using def_inj_rel by auto
    with \<open>F`a \<in> M\<close> \<open>q \<in> M\<close>
    show ?thesis sorry
  qed
  moreover
  have "F : A \<rightarrow> Pow(B)"
    unfolding F_def by (rule_tac lam_type) blast
  ultimately
  show ?thesis by auto
qed

end (* includes generic_simps *)

end (* forcing_data *)


end