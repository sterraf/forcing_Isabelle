theory Toplevel_Draft
  imports
    Cardinal_Preservation
    "../Delta_System_Lemma/Delta_System"
    Cohen_Posets

begin

definition
  Add_subs :: "[i,i] \<Rightarrow> i" where
  "Add_subs(\<kappa>,\<alpha>) \<equiv> Fn(\<omega>,\<kappa>\<times>\<alpha>,2)"

definition (* fake def *)
  Aleph_rel :: "[i\<Rightarrow>o,i] \<Rightarrow> i" where
  "Aleph_rel(M,a) \<equiv> Aleph(a)"

abbreviation
  Aleph_r :: "[i,i\<Rightarrow>o] \<Rightarrow> i" (\<open>\<aleph>\<^bsub>_\<^esub>\<^bsup>_\<^esup>\<close>) where
  "Aleph_r(a,M) \<equiv> Aleph_rel(M,a)"

abbreviation
  Aleph_r_set :: "[i,i] \<Rightarrow> i" (\<open>\<aleph>\<^bsub>_\<^esub>\<^bsup>_\<^esup>\<close>) where
  "Aleph_r_set(a,M) \<equiv> Aleph_rel(##M,a)"

definition
  cexp_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" where
  def_cexp_rel:"cexp_rel(M,x,y) \<equiv> |y\<rightarrow>\<^bsup>M\<^esup> x|\<^bsup>M\<^esup>"

abbreviation
  cexp_r :: "[i,i,i\<Rightarrow>o] \<Rightarrow> i"  (\<open>'(_\<^bsup>\<up>_\<^esup>')\<^bsup>_\<^esup>\<close>) where
  "cexp_r(x,y,M) \<equiv> cexp_rel(M,x,y)"

abbreviation
  cexp_r_set :: "[i,i,i] \<Rightarrow> i"  (\<open>'(_\<^bsup>\<up>_\<^esup>')\<^bsup>_\<^esup>\<close>) where
  "cexp_r_set(x,y,M) \<equiv> cexp_rel(##M,x,y)"

abbreviation
  csucc_r :: "[i,i\<Rightarrow>o] \<Rightarrow> i"  (\<open>'(_\<^sup>+')\<^bsup>_\<^esup>\<close>) where
  "csucc_r(x,M) \<equiv> csucc_rel(M,x)"

abbreviation
  csucc_r_set :: "[i,i] \<Rightarrow> i"  (\<open>'(_\<^sup>+')\<^bsup>_\<^esup>\<close>) where
  "csucc_r_set(x,M) \<equiv> csucc_rel(##M,x)"

locale M_cardinal_UN_lepoll = M_cardinal_UN _ J for J
begin

lemma leqpoll_rel_imp_cardinal_rel_UN_le:
  notes [dest] = InfCard_is_Card Card_is_Ord
  assumes "InfCard\<^bsup>M\<^esup>(K)" "J \<lesssim>\<^bsup>M\<^esup> K" "\<And>i. i\<in>J \<Longrightarrow> |X(i)|\<^bsup>M\<^esup> \<le> K"
    and types:"M(K)"
  shows "|\<Union>i\<in>J. X(i)|\<^bsup>M\<^esup> \<le> K"
  sorry

end (* M_cardinal_UN_lepoll *)


locale M_master = M_cardinal_AC +
  assumes
  domain_separation: "M(x) \<Longrightarrow> separation(M, \<lambda>z. x \<in> domain(z))"
  and
  inj_dense_separation: "M(x) \<Longrightarrow> M(w) \<Longrightarrow>
    separation(M, \<lambda>z. \<exists>n\<in>\<omega>.    \<langle>\<langle>w, n\<rangle>, 1\<rangle> \<in> z \<and> \<langle>\<langle>x, n\<rangle>, 0\<rangle> \<in> z)"
  and
  apply_replacement1: "M(x) \<Longrightarrow> M(f) \<Longrightarrow>
      strong_replacement(M, \<lambda>z y. y = \<langle>z, f ` \<langle>x,z\<rangle>\<rangle>)"
  and
  apply_replacement2: "M(x) \<Longrightarrow> M(f) \<Longrightarrow> M(z) \<Longrightarrow>
      strong_replacement(M, \<lambda>x y. y = \<langle>x, f ` \<langle>z, x\<rangle>\<rangle>)"
  and
  lam_apply_replacement: "M(A) \<Longrightarrow> M(f) \<Longrightarrow>
      strong_replacement(M, \<lambda>x y. y = \<langle>x, \<lambda>n\<in>A. f ` \<langle>x, n\<rangle>\<rangle>)"
begin

lemma FiniteFun_closed[intro,simp]:
  assumes "M(A)" "M(B)" shows "M(A-||>B)"
  sorry

lemma Fn_nat_closed[intro,simp]:
  assumes "M(A)" "M(B)" shows "M(Fn(\<omega>,A,B))"
  using assms Fn_nat_eq_FiniteFun
  by simp

lemma lepoll_rel_imp_lepoll_rel_cardinal_rel:
  assumes "X \<lesssim>\<^bsup>M\<^esup> Y"  "M(X)" "M(Y)"
  shows "X \<lesssim>\<^bsup>M\<^esup> |Y|\<^bsup>M\<^esup>"
  sorry

lemma subset_imp_le_cardinal_rel: "A \<subseteq> B \<Longrightarrow> M(A) \<Longrightarrow> M(B) \<Longrightarrow> |A|\<^bsup>M\<^esup> \<le> |B|\<^bsup>M\<^esup>"
  sorry

lemma cardinal_rel_subset_of_Card_rel:
  assumes "Card\<^bsup>M\<^esup>(\<gamma>)" "a \<subseteq> \<gamma>"
    and types: "M(\<gamma>)" "M(a)"
  shows "|a|\<^bsup>M\<^esup> < \<gamma> \<or> |a|\<^bsup>M\<^esup> = \<gamma>"
  sorry

lemma lt_surj_rel_empty_imp_Card:
  assumes "\<And>\<alpha>. \<alpha> < \<kappa> \<Longrightarrow> surj\<^bsup>M\<^esup>(\<alpha>,\<kappa>) = 0"
  shows "Card\<^bsup>M\<^esup>(\<kappa>)"
  sorry

lemma Card_rel_csucc_rel: "Ord(K) \<Longrightarrow> M(K) \<Longrightarrow> Card\<^bsup>M\<^esup>((K\<^sup>+)\<^bsup>M\<^esup>)"
  sorry

lemma csucc_rel_le: "Card\<^bsup>M\<^esup>(l) \<Longrightarrow> K < l \<Longrightarrow> M(l) \<Longrightarrow> M(K) \<Longrightarrow> (K\<^sup>+)\<^bsup>M\<^esup> \<le> l"
  sorry

lemma cardinal_rel_lt_csucc_rel_iff: "Card\<^bsup>M\<^esup>(K) \<Longrightarrow> M(K) \<Longrightarrow> M(K') \<Longrightarrow>
  |K'|\<^bsup>M\<^esup> < (K\<^sup>+)\<^bsup>M\<^esup> \<longleftrightarrow> |K'|\<^bsup>M\<^esup> \<le> K"
  sorry

lemma InfCard_rel_Aleph_rel:
  assumes "Ord(\<alpha>)" "M(\<alpha>)"
  shows "InfCard\<^bsup>M\<^esup>(\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>)"
  sorry

lemma cardinal_rel_Aleph_rel [simp]: "Ord(\<alpha>) \<Longrightarrow> M(\<alpha>) \<Longrightarrow> |\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>|\<^bsup>M\<^esup> = \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>"
  sorry

lemma nat_lt_Aleph_rel1: "\<omega> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  sorry

lemma Aleph_rel_closed[intro,simp]: "M(a) \<Longrightarrow> M(\<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup>)"
  sorry

lemma Aleph_rel2_closed[intro,simp]: "M(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>)"
  using  nat_into_M[of 2, THEN Aleph_rel_closed] by simp

lemma Card_rel_Aleph_rel[simp]: "Ord(\<alpha>) \<Longrightarrow> Card\<^bsup>M\<^esup>(\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>)"
  sorry

lemma Aleph_rel_zero_eq_nat: "\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^esup> = \<omega>"
  sorry

lemma Aleph_rel_succ: "\<aleph>\<^bsub>succ(\<alpha>)\<^esub>\<^bsup>M\<^esup> = (\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup>"
  sorry

lemma Aleph_rel_increasing: "a < b  \<Longrightarrow> M(a) \<Longrightarrow> M(b) \<Longrightarrow> \<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup> < \<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>"
  sorry

lemma Fnle_nat_closed[intro,simp]:
  assumes "M(I)" "M(J)"
  shows "M(Fnle(\<omega>,I,J))"
  sorry

end (* M_master *)

locale M_master_sub = M_master + N:M_master N for N +
  assumes
    M_imp_N: "M(x) \<Longrightarrow> N(x)" and
    Ord_iff: "Ord(x) \<Longrightarrow> M(x) \<longleftrightarrow> N(x)"
begin

lemma Card_rel_imp_Card_rel: "M(\<kappa>) \<Longrightarrow> Card\<^bsup>N\<^esup>(\<kappa>) \<Longrightarrow> Card\<^bsup>M\<^esup>(\<kappa>)"
  sorry

lemma Aleph_rel_le_Aleph_rel: "Ord(\<alpha>) \<Longrightarrow> M(\<alpha>) \<Longrightarrow> \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>N\<^esup>"
  sorry

lemma cardinal_rel_le_cardinal_rel: "M(X) \<Longrightarrow> |X|\<^bsup>N\<^esup> \<le> |X|\<^bsup>M\<^esup>"
  sorry

lemma Aleph_rel_sub_closed: "Ord(\<alpha>) \<Longrightarrow> M(\<alpha>) \<Longrightarrow> N(\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>)"
  using Aleph_rel2_closed Ord_iff[THEN iffD1,
      OF Card_rel_Aleph_rel[THEN Card_rel_is_Ord]]
  by simp

end (* M_master_sub *)

sublocale M_master_sub \<subseteq> M_N_Perm
  using M_imp_N by unfold_locales

sublocale M_ZF_trans \<subseteq> M_master "##M"
  sorry

context M_ctm
begin

\<comment> \<open>FIXME: using notation as if \<^term>\<open>Add_subs\<close> were used\<close>
lemma ccc_Add_subs_Aleph_2: "ccc\<^bsup>M\<^esup>(Fn(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>,2),Fnle(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>,2))"
  sorry

end (* M_ctm *)

sublocale G_generic \<subseteq> M_master_sub "##M" "##(M[G])"
  using M_subset_MG[OF one_in_G] generic Ord_MG_iff
  by unfold_locales auto

context G_generic begin

context
  includes G_generic_lemmas
begin

lemma G_in_MG: "G \<in> M[G]"
  using G_in_Gen_Ext[ OF _ one_in_G, OF _ generic]
  by blast

lemma ccc_preserves_Aleph_succ:
  assumes "ccc\<^bsup>M\<^esup>(P,leq)" "Ord(z)" "z \<in> M"
  shows "Card\<^bsup>M[G]\<^esup>(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)"
proof (rule ccontr)
  assume "\<not> Card\<^bsup>M[G]\<^esup>(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)"
  then
  obtain \<alpha> f where "\<alpha> < \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>" "f \<in> surj\<^bsup>M[G]\<^esup>(\<alpha>, \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)"
    using ext.lt_surj_rel_empty_imp_Card by blast
  moreover from this and \<open>z\<in>M\<close>
  have "\<alpha> \<in> M" "f \<in> M[G]"
    using Aleph_rel_closed[of "succ(z)"] ext.trans_surj_rel_closed
    by (auto dest:transM ext.transM dest!:ltD)
  moreover
  note \<open>ccc\<^bsup>M\<^esup>(P,leq)\<close> \<open>z\<in>M\<close>
  ultimately
  obtain F where "F:\<alpha>\<rightarrow>Pow(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)" "\<forall>\<beta>\<in>\<alpha>. f`\<beta> \<in> F`\<beta>" "\<forall>\<beta>\<in>\<alpha>. |F`\<beta>|\<^bsup>M\<^esup> \<le> \<omega>"
    "F \<in> M"
    using ccc_fun_approximation_lemma[of \<alpha> "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>" f]
      ext.mem_surj_abs[of f \<alpha> "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>"]
      Aleph_rel_closed[of "succ(z)"] surj_is_fun[of f \<alpha> "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>"] by auto
  then
  have "\<beta> \<in> \<alpha> \<Longrightarrow> |F`\<beta>|\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^esup>" for \<beta>
    using Aleph_rel_zero_eq_nat by simp
  from \<open>\<alpha> \<in> M\<close> \<open>F:\<alpha>\<rightarrow>Pow(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)\<close> \<open>F\<in>M\<close>
  interpret M_cardinal_UN_lepoll "##M" "\<lambda>\<beta>. F`\<beta>" \<alpha>
    using Aleph_rel_closed[of 0]
  proof (unfold_locales, auto dest:transM)
    show "w \<in> F ` x \<Longrightarrow> x \<in> M" for w x
    proof -
      fix w x
      assume "w \<in> F`x"
      then
      have "x \<in> domain(F)"
        using apply_0 by auto
      with \<open>F:\<alpha>\<rightarrow>Pow(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)\<close>
      have "x \<in> \<alpha>"
        using domain_of_fun by simp
      with \<open>\<alpha> \<in> M\<close>
      show "x \<in> M" by (auto dest:transM)
    qed
    show "strong_replacement(##M, \<lambda>y z. y \<in> F ` x \<and> z = {\<langle>x, y\<rangle>})"
      "strong_replacement(##M, \<lambda>x z. z = Sigfun(x, (`)(F)))"
      "strong_replacement(##M, \<lambda>x y. y = F ` x)"
      "strong_replacement(##M, \<lambda>x y. y = \<langle>x, Cardinal_AC_Relative.minimum(r, F ` x)\<rangle>)"
      "strong_replacement(##M, \<lambda>y z. y \<in> inj(F ` x, \<alpha>) \<and> z = {\<langle>x, y\<rangle>})"
      "strong_replacement(##M, \<lambda>x y. y = inj\<^bsup>M\<^esup>(F ` x,\<alpha>))"
      "strong_replacement(##M, \<lambda>x z. z = Sigfun(x, \<lambda>i. inj\<^bsup>M\<^esup>(F ` i,\<alpha>)))"
      "strong_replacement(##M, \<lambda>x y. y = \<langle>x, Cardinal_AC_Relative.minimum(r, inj\<^bsup>M\<^esup>(F ` x,\<alpha>))\<rangle>)"
      "strong_replacement(##M, \<lambda>x y. y = \<langle>x, \<mu> i. x \<in> F ` i, f ` (\<mu> i. x \<in> F ` i) ` x\<rangle>)" for x r f
      sorry
  qed
  from \<open>\<alpha> < \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>\<close> \<open>\<alpha> \<in> M\<close> assms
  have "\<alpha> \<lesssim>\<^bsup>M\<^esup> \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"
    using
      Aleph_rel_zero_eq_nat
      cardinal_rel_lt_csucc_rel_iff[of "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>" \<alpha>]
      le_Card_rel_iff[of "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>" \<alpha>]
      Aleph_rel_succ[of z] Card_rel_lt_iff[of \<alpha> "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>"]
      lt_Ord[of \<alpha> "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>"]
      csucc_rel_closed[of "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"] Card_rel_csucc_rel[of "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"]
      Aleph_rel_closed[of z]
      Card_rel_Aleph_rel[THEN Card_rel_is_Ord, OF _ Aleph_rel_closed]
    by simp
  with \<open>\<alpha> < \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>\<close> \<open>\<forall>\<beta>\<in>\<alpha>. |F`\<beta>|\<^bsup>M\<^esup> \<le> \<omega>\<close> \<open>\<alpha> \<in> M\<close> assms
  have "|\<Union>\<beta>\<in>\<alpha>. F`\<beta>|\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"
    using InfCard_rel_Aleph_rel[of z] Aleph_rel_zero_eq_nat
      subset_imp_lepoll_rel[THEN lepoll_rel_imp_cardinal_rel_le,
        of "\<Union>\<beta>\<in>\<alpha>. F`\<beta>" "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"]
      Aleph_rel_closed[of z] Aleph_rel_succ
      Aleph_rel_increasing[THEN leI, THEN [2] le_trans, of _ 0 z]
      Ord_0_lt_iff[THEN iffD1, of z]
    by (cases "0<z"; rule_tac leqpoll_rel_imp_cardinal_rel_UN_le) (auto, force)
  moreover
  note \<open>z\<in>M\<close> \<open>Ord(z)\<close>
  moreover from \<open>\<forall>\<beta>\<in>\<alpha>. f`\<beta> \<in> F`\<beta>\<close> \<open>f \<in> surj\<^bsup>M[G]\<^esup>(\<alpha>, \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)\<close>
    \<open>\<alpha> \<in> M\<close> \<open>f \<in> M[G]\<close> and this
  have "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup> \<subseteq> (\<Union>\<beta>\<in>\<alpha>. F`\<beta>)"
    using Aleph_rel_closed[of "succ(z)"] ext.mem_surj_abs
    by (force simp add:surj_def)
  moreover from \<open>F \<in> M\<close> \<open>\<alpha> \<in> M\<close>
  have "(\<Union>x\<in>\<alpha>. F ` x) \<in> M"
    using B_replacement
    by (intro Union_closed[simplified] RepFun_closed[simplified])
      (auto dest:transM)
  ultimately
  have "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"
    using subset_imp_le_cardinal_rel[of "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>" "\<Union>\<beta>\<in>\<alpha>. F`\<beta>"]
      Aleph_rel_closed[of "succ(z)"] le_trans
    by auto
  with assms
  show "False"
    using Aleph_rel_increasing not_le_iff_lt[of "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"]
      Card_rel_Aleph_rel[THEN Card_rel_is_Ord, OF _ Aleph_rel_closed]
    by auto
qed

end (* G_generic_lemmas *)

end (* G_generic *)

context M_ctm
begin

abbreviation
  Add :: "i" where
  "Add \<equiv> Fn(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>, 2)"

end (* M_ctm *)

locale add_generic = G_generic "Fn(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>##M\<^esup> \<times> \<omega>, 2)" "Fnle(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>##M\<^esup> \<times> \<omega>, 2)" 0

sublocale add_generic \<subseteq> cohen_data \<omega> "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 2 by unfold_locales auto

context add_generic
begin

notation Leq (infixl "\<preceq>" 50)
notation Incompatible (infixl "\<bottom>" 50)
notation GenExt_at_P ("_[_]" [71,1])

lemma Add_subs_preserves_Aleph_succ: "Ord(z) \<Longrightarrow> z\<in>M \<Longrightarrow> Card\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)"
  using ccc_preserves_Aleph_succ ccc_Add_subs_Aleph_2
  by auto

lemma Aleph_rel_nats_MG_eq_Aleph_rel_nats_M:
  includes G_generic_lemmas
  assumes "z \<in> \<omega>"
  shows "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> = \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"
  using assms
proof (induct)
  case 0
  have "\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> = \<omega>"
    using ext.Aleph_rel_zero_eq_nat .
  also
  have "\<omega> = \<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^esup>"
    using Aleph_rel_zero_eq_nat by simp
  finally
  show ?case .
next
  case (succ z)
  then
  have "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
    using Aleph_rel_le_Aleph_rel nat_into_M by simp
  moreover from \<open>z \<in> \<omega>\<close>
  have "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup> \<in> M[G]" "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup> \<in> M[G]"
    using Aleph_rel_closed nat_into_M by simp_all
  moreover from this and \<open>\<aleph>\<^bsub>z\<^esub>\<^bsup>M[G]\<^esup> = \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>\<close> \<open>z \<in> \<omega>\<close>
  have "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> \<le> \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>"
    using ext.Aleph_rel_succ nat_into_M
      Add_subs_preserves_Aleph_succ[THEN ext.csucc_rel_le, of z]
      Aleph_rel_increasing[of z "succ(z)"]
    by simp
  ultimately
  show ?case using le_anti_sym by blast
qed

abbreviation
  f_G :: "i" (\<open>f\<^bsub>G\<^esub>\<close>) where
  "f\<^bsub>G\<^esub> \<equiv> \<Union>G"

abbreviation
  dom_dense :: "i\<Rightarrow>i" where
  "dom_dense(x) \<equiv> { p\<in>Add . x \<in> domain(p) }"

\<comment> \<open>FIXME write general versions of this for \<^term>\<open>Fn(\<omega>,I,J)\<close>
    in a context with a generic filter for it\<close>
lemma dense_dom_dense: "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega> \<Longrightarrow> dense(dom_dense(x))"
proof
  fix p
  assume "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" "p \<in> Add"
  show "\<exists>d\<in>dom_dense(x). d \<preceq> p"
  proof (cases "x \<in> domain(p)")
    case True
    with \<open>x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>\<close> \<open>p \<in> Add\<close>
    show ?thesis using refl_leq by auto
  next
    case False
    note \<open>p \<in> Add\<close>
    moreover from this and False and \<open>x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>\<close>
    have "cons(\<langle>x,0\<rangle>, p) \<in> Add"
      using FiniteFun.consI[of x "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 0 2 p]
        Fn_nat_eq_FiniteFun by auto
    moreover from \<open>p \<in> Add\<close>
    have "x\<in>domain(cons(\<langle>x,0\<rangle>, p))" by simp
    ultimately
    show ?thesis
      \<comment> \<open>FIXME: Too many unfoldings following\<close>
      unfolding Fnle_def Fnlerel_def Rrel_def
      by (fastforce del:FnD)
  qed
qed

(*
NOTE Class model version?
lemma dom_dense_closed[intro,simp]: "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega> \<Longrightarrow> M(dom_dense(x))" *)
lemma dom_dense_closed[intro,simp]: "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega> \<Longrightarrow> dom_dense(x) \<in> M"
  using Fn_nat_closed Aleph_rel2_closed domain_separation[of x] nat_into_M
  by (rule_tac separation_closed[simplified], blast dest:transM) simp

lemma domain_f_G: assumes "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "y \<in> \<omega>"
  shows "\<langle>x, y\<rangle> \<in> domain(f\<^bsub>G\<^esub>)"
proof -
  from assms
  have "dense(dom_dense(\<langle>x, y\<rangle>))" using dense_dom_dense by simp
  with assms
  obtain p where "p\<in>dom_dense(\<langle>x, y\<rangle>)" "p\<in>G"
    using generic[THEN M_generic_denseD, of "dom_dense(\<langle>x, y\<rangle>)"]
    by auto
  then
  show "\<langle>x, y\<rangle> \<in> domain(f\<^bsub>G\<^esub>)" by blast
qed

\<comment> \<open>MOVE THIS to \<^file>\<open>Cohen_Posets.thy\<close>\<close>
lemma Fn_nat_subset_Pow: "Fn(\<omega>,I,J) \<subseteq> Pow(I\<times>J)"
  using subset_trans[OF FiniteFun.dom_subset Fin.dom_subset]
    Fn_nat_eq_FiniteFun by simp

lemma f_G_funtype:
  includes G_generic_lemmas
  shows "f\<^bsub>G\<^esub> : \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega> \<rightarrow> 2"
  using generic domain_f_G
  unfolding Pi_def
proof (auto)
  show "x \<in> B \<Longrightarrow> B \<in> G \<Longrightarrow> x \<in> (\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>) \<times> 2" for B x
    using Fn_nat_subset_Pow by blast
  show "function(f\<^bsub>G\<^esub>)"
    using Un_filter_is_function generic
    unfolding M_generic_def by fast
qed

abbreviation
  inj_dense :: "i\<Rightarrow>i\<Rightarrow>i" where
  "inj_dense(w,x) \<equiv>
    { p\<in>Add . (\<exists>n\<in>\<omega>. <<w,n>,1> \<in> p \<and> <<x,n>,0> \<in> p) }"

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
  sorry

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

\<comment> \<open>FIXME write general versions of this for \<^term>\<open>Fn(\<omega>,I,J)\<close>
    in a context with a generic filter for it\<close>
lemma dense_inj_dense:
  assumes "w \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "w \<noteq> x"
  shows "dense(inj_dense(w,x))"
proof
  fix p
  assume "p \<in> Add"
  then
  obtain n where "<w,n> \<notin> domain(p)" "<x,n> \<notin> domain(p)" "n \<in> \<omega>"
  proof -
    {
      assume "<w,n> \<in> domain(p) \<or> <x,n> \<in> domain(p)" if "n \<in> \<omega>" for n
      then
      have "\<omega> \<subseteq> range(domain(p))" by blast
      then
      have "\<not> Finite(p)"
        using Finite_range Finite_domain subset_Finite nat_not_Finite
        by auto
      with \<open>p \<in> Add\<close>
      have False
        using Fn_nat_eq_FiniteFun FiniteFun.dom_subset[of "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 2]
          Fin_into_Finite by auto
    }
    with that\<comment> \<open>the shape of the goal puts assumptions in this variable\<close>
    show ?thesis by auto
  qed
  moreover
  note \<open>p \<in> Add\<close> assms
  moreover from calculation
  have "cons(\<langle>\<langle>x,n\<rangle>,0\<rangle>, p) \<in> Add"
    using FiniteFun.consI[of "\<langle>x,n\<rangle>" "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 0 2 p]
      Fn_nat_eq_FiniteFun by auto
  ultimately
  have "cons(\<langle>\<langle>w,n\<rangle>,1\<rangle>, cons(\<langle>\<langle>x,n\<rangle>,0\<rangle>, p) ) \<in> Add"
    using FiniteFun.consI[of "\<langle>w,n\<rangle>" "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 1 2 "cons(\<langle>\<langle>x,n\<rangle>,0\<rangle>, p)"]
      Fn_nat_eq_FiniteFun by auto
  with \<open>n \<in> \<omega>\<close>
  show "\<exists>d\<in>inj_dense(w,x). d \<preceq> p"
    using \<open>p \<in> Add\<close> unfolding Fnle_def Fnlerel_def Rrel_def
    by (intro bexI) auto
qed

lemma inj_dense_closed[intro,simp]:
  "w \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> inj_dense(w,x) \<in> M"
  using Fn_nat_closed Aleph_rel2_closed domain_separation[of x] nat_into_M
    inj_dense_separation transM[OF _ Aleph_rel2_closed]
  by (rule_tac separation_closed[simplified]; simp_all)

lemma Aleph_rel2_new_reals:
  assumes "w \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "w \<noteq> x"
  shows "(\<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub> ` \<langle>w, n\<rangle>) \<noteq> (\<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub> ` \<langle>x, n\<rangle>)"
proof -
  from assms
  have "dense(inj_dense(w,x))" using dense_inj_dense by simp
  with assms
  obtain p where "p\<in>inj_dense(w,x)" "p\<in>G"
    using generic[THEN M_generic_denseD, of "inj_dense(w,x)"]
    by blast
  then
  obtain n where "n \<in> \<omega>" "\<langle>\<langle>w, n\<rangle>, 1\<rangle> \<in> p" "\<langle>\<langle>x, n\<rangle>, 0\<rangle> \<in> p"
    by blast
  moreover from this and \<open>p\<in>G\<close>
  have "\<langle>\<langle>w, n\<rangle>, 1\<rangle> \<in> f\<^bsub>G\<^esub>" "\<langle>\<langle>x, n\<rangle>, 0\<rangle> \<in> f\<^bsub>G\<^esub>" by auto
  moreover from calculation
  have "f\<^bsub>G\<^esub> ` \<langle>w, n\<rangle> = 1" "f\<^bsub>G\<^esub> ` \<langle>x, n\<rangle> = 0"
    using f_G_funtype apply_equality
    by auto
  ultimately
  have "(\<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub> ` \<langle>w, n\<rangle>) ` n \<noteq> (\<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub> ` \<langle>x, n\<rangle>) ` n"
    by simp
  then
  show ?thesis by fastforce
qed

definition
  h_G :: "i" (\<open>h\<^bsub>G\<^esub>\<close>) where
  "h\<^bsub>G\<^esub> \<equiv> \<lambda>\<alpha>\<in>\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>. \<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub>`<\<alpha>,n>"

lemma h_G_in_MG[simp]:
  includes G_generic_lemmas
  shows "h\<^bsub>G\<^esub> \<in> M\<^bsup>Add\<^esup>[G]"
  using Aleph_rel2_closed
    ext.lam_apply_replacement ext.apply_replacement1
    ext.Union_closed[simplified, OF G_in_MG]
    \<comment> \<open>The "simplified" here is because of
        the \<^term>\<open>setclass\<close> ocurrences\<close>
    ext.nat_in_M Aleph_rel2_closed ext.nat_into_M
  unfolding h_G_def
  by (rule_tac ext.lam_closed[simplified] | auto dest:transM)+

lemma h_G_inj_Aleph_rel2_reals: "h\<^bsub>G\<^esub> \<in> inj\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> 2)"
  using Aleph_rel_sub_closed
proof (intro ext.mem_inj_abs[THEN iffD2])
  show "h\<^bsub>G\<^esub> \<in> inj(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2)"
    unfolding inj_def
  proof (intro ballI CollectI impI)
    show "h\<^bsub>G\<^esub> \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<rightarrow> \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"
      using f_G_funtype G_in_MG ext.nat_into_M unfolding h_G_def
      apply (intro lam_type ext.mem_function_space_rel_abs[THEN iffD2], simp_all)
      apply (rule_tac ext.lam_closed[simplified], simp_all)
       apply (rule ext.apply_replacement2)
         apply (auto dest:ext.transM[OF _ Aleph_rel_sub_closed])
      done
    fix w x
    assume "w \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "h\<^bsub>G\<^esub> ` w = h\<^bsub>G\<^esub> ` x"
    then
    show "w = x"
      unfolding h_G_def using Aleph_rel2_new_reals by auto
  qed
qed simp_all

lemma Aleph2_submodel_le_continuum_rel:
  includes G_generic_lemmas
  shows "\<aleph>\<^bsub>2\<^esub>\<^bsup>M[G]\<^esup> \<le> (2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>\<^esup>)\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
proof -
  have "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<in> M\<^bsup>Add\<^esup>[G]" "Ord(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>)"
    using Card_rel_Aleph_rel[THEN Card_rel_is_Ord, of 2]
      Aleph_rel2_closed
    by auto
  moreover from this
  have "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> \<omega> \<rightarrow>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> 2"
    using ext.def_lepoll_rel[of "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> 2",
        OF _ ext.function_space_rel_closed]
      h_G_inj_Aleph_rel2_reals h_G_in_MG ext.nat_into_M ext.M_nat
    by auto
  moreover from calculation
  have "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<lesssim>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> |\<omega> \<rightarrow>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> 2|\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
    using ext.lepoll_rel_imp_lepoll_rel_cardinal_rel by simp
  ultimately
  have "|\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>|\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> \<le> (2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>\<^esup>)\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
    using ext.lepoll_rel_imp_cardinal_rel_le[of "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> 2",
        OF _ _ ext.function_space_rel_closed] ext.nat_into_M ext.M_nat
      ext.Aleph_rel_zero_eq_nat Aleph_rel_nats_MG_eq_Aleph_rel_nats_M
    unfolding def_cexp_rel by simp
  then
  show "\<aleph>\<^bsub>2\<^esub>\<^bsup>M[G]\<^esup> \<le> (2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>\<^esup>)\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
    using Aleph_rel_nats_MG_eq_Aleph_rel_nats_M
      ext.Card_rel_Aleph_rel[of 2, THEN ext.Card_rel_cardinal_rel_eq]
      ext.Aleph_rel2_closed
    by simp
qed

lemma Aleph_rel_lt_continuum_rel: "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> < (2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>\<^esup>)\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
  using Aleph2_submodel_le_continuum_rel
    ext.Aleph_rel_increasing[of 1 2] le_trans by auto

corollary not_CH: "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> \<noteq> (2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>\<^esup>)\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
  using Aleph_rel_lt_continuum_rel by auto

end (* add_generic *)

notepad
begin
  fix M
  assume
    "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZF"
  from \<open>M \<Turnstile> ZF\<close>
  interpret M_ZF M
    using M_ZF_iff_M_satT
    by simp
  from \<open>Transset(M)\<close>
  interpret M_ZF_trans M
    using M_ZF_iff_M_satT
    by unfold_locales
  from \<open>M \<approx> \<omega>\<close>
  obtain enum where "enum \<in> bij(\<omega>,M)"
    using eqpoll_sym unfolding eqpoll_def by blast
  then
  interpret M_ctm M enum by unfold_locales
  interpret forcing_data "Fn(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>,2)" "Fnle(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>,2)" 0 M enum
  proof -
    interpret cohen_data \<omega> "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 2 by unfold_locales auto
    show "forcing_data(Fn(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>, 2), Fnle(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>, 2), 0, M, enum)"
      using nat_into_M[of 2] M_nat
        Fn_nat_closed[OF cartprod_closed, OF Aleph_rel_closed, of 2 \<omega> 2]
        Fnle_nat_closed[OF cartprod_closed, OF Aleph_rel_closed, of 2 \<omega> 2]
      by (unfold_locales, simp_all)
  qed
  obtain G where "M_generic(G)"
    using generic_filter_existence[OF one_in_P]
    by auto
  then
  interpret add_generic M enum G by unfold_locales
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> \<noteq> (2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>\<^esup>)\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
    using not_CH .

end (* notepad *)

end