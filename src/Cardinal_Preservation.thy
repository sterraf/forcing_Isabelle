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

sublocale forcing_data \<subseteq> M_cardinal_AC "##M"
  sorry

context G_generic begin

notation cardinal_rel (\<open>|_|\<^sup>M\<close>)
notation ccc_rel (\<open>ccc\<^sup>M\<close>)
notation check (\<open>_\<^sup>v\<close> [101] 100)

\<comment> \<open>NOTE: The following bundled additions to the simpset might be of
    use later on, perhaps add them globally to some appropriate
    locale.\<close>
bundle generic_simps = generic[THEN one_in_G, THEN valcheck, OF one_in_P, simp] GenExtI[simp]
  generic[THEN one_in_G, THEN M_subset_MG, THEN subsetD, simp] check_in_M[simp]

text\<open>The following interpretation makes the simplifications from the
locales \<open>M_trans\<close>, \<open>M_trivial\<close>, etc., available for \<^term>\<open>M[G]\<close> \<close>
interpretation mgzf: M_ZF_trans "M[G]"
  using Transset_MG generic pairing_in_MG Union_MG
    extensionality_in_MG power_in_MG foundation_in_MG
    strong_replacement_in_MG separation_in_MG infinity_in_MG
  by unfold_locales simp_all

context
  includes generic_simps
begin

\<comment> \<open>@{thm mgzf.apply_closed} does not simplifies appropriately\<close>
lemmas apply_closed_in_MG = mgzf.apply_closed[simplified, simp]
lemmas apply_closed_in_M = apply_closed[simplified, simp]

\<comment> \<open>Kunen IV.3.35\<close>
lemma 
  assumes "ccc\<^sup>M(##M,P,leq)" "A\<in>M" "B\<in>M" "f\<in>M[G]" "f : A\<rightarrow> B"
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
  let ?F="\<lambda>a\<in>A. {b\<in>B. \<exists>q\<in>P. q \<preceq> p \<and> (q \<tturnstile> fun_apply_fm(0,1,2) [f_dot, a\<^sup>v, b\<^sup>v])}"
  have "?F \<in> M" sorry
  have "f`a \<in> ?F`a" if "a \<in> A" for a
  proof -
    let ?app_fm="fun_apply_fm(0,1,2)"\<comment> \<open>formula for \<open>f`x=z\<close>\<close>
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
    then
    have "\<exists>q\<in>P. q \<preceq> p \<and> q \<tturnstile> ?app_fm [f_dot, a\<^sup>v, (f`a)\<^sup>v]"
      sorry
    with \<open>f`a \<in> B\<close>
    have "f`a \<in> {b\<in>B . \<exists>q\<in>P. q \<preceq> p \<and> q \<tturnstile> ?app_fm [f_dot, a\<^sup>v, b\<^sup>v]}"
      by simp
    with \<open>a\<in>A\<close>
    show ?thesis by simp
  qed
  oops

end (* includes generic_simps *)

end (* forcing_data *)


end