theory Non_Constructible
  imports
    Forcing_Thms 
    (* it actually depends on more basic stuff, plus a misplaced lemma in the former *)

begin

lemma (in forcing_notion) filter_imp_compat: "filter(G) \<Longrightarrow> p\<in>G \<Longrightarrow> q\<in>G \<Longrightarrow> compat(p,q)"  \<comment> \<open>put somewhere else\<close>
  unfolding filter_def compat_in_def compat_def by blast

definition
  chleR :: "i \<Rightarrow> i \<Rightarrow> o" where
  "chleR(xs,ys) \<equiv> \<exists>zs. xs = ys @ zs"

definition
  chlerel :: "i \<Rightarrow> i" where
  "chlerel(A) \<equiv> Rrel(chleR,A)"

definition
  chle :: "i" where
  "chle \<equiv> chlerel(list(2))"

lemma chleI[intro!]: 
  "\<langle>x,y\<rangle> \<in> list(2)\<times>list(2) \<Longrightarrow> \<exists>zs. x = y @ zs \<Longrightarrow> \<langle>x,y\<rangle> \<in> chle"
  unfolding preorder_on_def refl_def trans_on_def 
  chle_def chlerel_def Rrel_def chleR_def 
  by blast

lemma chleD[dest!]: 
  "z \<in> chle \<Longrightarrow> \<exists>x y. \<langle>x,y\<rangle> \<in> list(2)\<times>list(2) \<and> (\<exists>zs. x = y @ zs) \<and> z = \<langle>x,y\<rangle>"
  unfolding preorder_on_def refl_def trans_on_def 
  chle_def chlerel_def Rrel_def chleR_def 
  by blast

lemma preorder_on_chle: "preorder_on(list(2),chle)"
  unfolding preorder_on_def refl_def trans_on_def 
  using app_assoc by auto

lemma Nil_chle_max: "x\<in>list(2) \<Longrightarrow> \<langle>x,[]\<rangle> \<in> chle"
  by auto

interpretation ch: forcing_notion "list(2)" "chle" "[]"
  unfolding forcing_notion_def using preorder_on_chle Nil_chle_max by simp

abbreviation Chle :: "[i, i] \<Rightarrow> o"  (infixl "\<preceq>" 50)
  where "x \<preceq> y \<equiv> ch.Leq(x,y)"

abbreviation Incompatible :: "[i, i] \<Rightarrow> o"  (infixl "\<bottom>" 50)
  where "p \<bottom> q \<equiv> ch.Incompatible(p,q)"

lemma incompatible_extensions:
  assumes "p\<in>list(2)"
  shows "(p @ [0]) \<bottom> (p @ [1])"
proof
  assume "ch.compat(p @ [0], p @ [1])"
  then
  obtain q where "q\<in>list(2)" "q \<preceq> p@[0]" "q \<preceq> p@[1]" 
    by blast
  with assms
  obtain xs ys where "q = (p @ [0]) @ xs" "q = (p @ [1]) @ ys"  
    by blast
  with assms
  show "False" using app_assoc by simp
qed

lemma filter_complement_dense:
  assumes "ch.filter(G)" shows "ch.dense(list(2) - G)"
proof
  fix p
  assume "p\<in>list(2)"
  show "\<exists>d\<in>list(2) - G. ch.Leq(d, p)"
  proof (cases "p\<in>G")
    case True
    note assms \<open>p\<in>list(2)\<close>
    moreover from this
    obtain j where "j\<in>2" "p @ [j] \<notin> G"
      using incompatible_extensions[of p] ch.filter_imp_compat[of G "p @ [0]" "p @ [1]"] 
      by auto
    moreover from calculation
    have "p @ [k] \<in> list(2)" if "k\<in>2" for k using that by simp
    moreover from calculation
    have "p @ [j] \<preceq> p" by auto
    ultimately 
    show ?thesis by auto
  next
    case False
    with \<open>p\<in>list(2)\<close> 
    show ?thesis using ch.leq_reflI unfolding Diff_def by auto
  qed
qed

context M_ctm
begin

lemma poset_in_M: "list(2)\<in>M" 
  using list_closed transitivity[OF _ nat_in_M] by simp

lemma chle_in_M: "chle \<in> M"
  unfolding chle_def chlerel_def Rrel_def chleR_def
  sorry

end (* M_ctm *)

sublocale M_ctm \<subseteq> forcing_data "list(2)" "chle" "[]"
  using poset_in_M chle_in_M by (unfold_locales)

context M_ctm
begin

lemma generic_not_in_M: assumes "M_generic(G)"  shows "G \<notin> M"
proof
  assume "G\<in>M"
  then
  have "list(2) - G \<in> M" 
    using P_in_M Diff_closed by simp
  moreover
  have "\<not>(\<exists>q\<in>G. q \<in> list(2) - G)" "(list(2) - G) \<subseteq> list(2)"
    unfolding Diff_def by auto
  moreover
  note assms
  ultimately
  show "False"
    using filter_complement_dense[of G] M_generic_denseD[of G "list(2)-G"] 
      M_generic_def by simp \<comment> \<open>need to put generic ==> filter in claset\<close>
qed

lemma G_subset_M: "M_generic(G) \<Longrightarrow> G \<subseteq> M" \<comment> \<open>put somewhere else\<close>
  using transitivity[OF _ P_in_M] by auto

(* For some reason, "M[G]" doesn't work here *)
theorem proper_extension: assumes "M_generic(G)" shows "M \<noteq> GenExt(G)"
  using assms G_in_Gen_Ext[of G] one_in_G[of G] generic_not_in_M G_subset_M
  by force

end (* M_ctm *)

end