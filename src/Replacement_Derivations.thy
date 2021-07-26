section\<open>Main definitions of the development\<close>

theory Replacement_Derivations
  imports
    "ZF-Constructible.Relative"
    Toplevel_Draft
    "../Tools/Try0"
begin

definition
  lam_replacement :: "[i\<Rightarrow>o,i\<Rightarrow>i] \<Rightarrow> o" where
  "lam_replacement(M,b) \<equiv> strong_replacement(M, \<lambda>x y. y = \<langle>x, b(x)\<rangle>)"

locale M_replacement = M_basic +
  assumes
    lam_replacement_fst: "lam_replacement(M,fst)"
    and
    lam_replacement_snd: "lam_replacement(M,snd)"
    and
    id_separation:"M(A) \<Longrightarrow> separation(M, \<lambda>z. \<exists>x[M]. z = \<langle>x, x\<rangle>)"
    and
    middle_separation: "separation(M, \<lambda>x. snd(fst(x))=fst(snd(x)))"
    and
    middle_del_replacement: "strong_replacement(M, \<lambda>x y. y=\<langle>fst(fst(x)),snd(snd(x))\<rangle>)"
    and
    pullback_separation: "separation(M, \<lambda>x. fst(fst(x))=fst(snd(x)))"
    and
    pullback_replacement:
    "strong_replacement(M, \<lambda>x y. y=\<langle>fst(fst(x)),\<langle>snd(fst(x)),snd(snd(x))\<rangle>\<rangle>)"
begin

lemma lam_replacement_iff_lam_closed:
  assumes "\<forall>x[M]. M(b(x))"
  shows "lam_replacement(M, b) \<longleftrightarrow>  (\<forall>A[M]. M(\<lambda>x\<in>A. b(x)))"
  using assms lam_closed lam_funtype[of _ b, THEN Pi_memberD]
  unfolding lam_replacement_def strong_replacement_def
  by (auto intro:lamI dest:transM)
    (rule lam_closed, auto simp add:strong_replacement_def dest:transM)

lemma lam_replacement_imp_strong_replacement:
  assumes "lam_replacement(M, b)" "\<forall>x[M]. M(b(x))"
  shows "strong_replacement(M, \<lambda>x y. y = b(x))"
proof -
  {
    fix A
    note assms
    moreover
    assume "M(A)"
    moreover from calculation
    have "M(\<lambda>x\<in>A. b(x))" using lam_replacement_iff_lam_closed by auto
    ultimately
    have "M((\<lambda>x\<in>A. b(x))``A)" "\<forall>z[M]. z \<in> (\<lambda>x\<in>A. b(x))``A \<longleftrightarrow> (\<exists>x\<in>A. z = b(x))"
      by (auto simp:lam_def)
  }
  then
  show ?thesis unfolding strong_replacement_def 
    by clarsimp (rule_tac x="(\<lambda>x\<in>A. b(x))``A" in rexI, auto)
qed

lemma Collect_middle: "{p \<in> (\<lambda>x\<in>A. f(x)) \<times> (\<lambda>x\<in>{f(x) . x\<in>A}. g(x)) . snd(fst(p))=fst(snd(p))}
     = { \<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> . x\<in>A }"
  by (intro equalityI; auto simp:lam_def)

lemma RepFun_middle_del: "{ \<langle>fst(fst(p)),snd(snd(p))\<rangle> . p \<in> { \<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> . x\<in>A }}
        =  { \<langle>x,g(f(x))\<rangle> . x\<in>A }"
  by auto

lemma lam_replacement_hcomp:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
          "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "lam_replacement(M, \<lambda>x. g(f(x)))"
proof -
  {
    fix A
    note assms
    moreover
    assume "M(A)"
    moreover from calculation
    have "M({f(x) . x\<in>A})"
      using RepFun_closed[of f A] lam_replacement_imp_strong_replacement by (auto dest:transM)
    moreover from calculation
    have "M((\<lambda>x\<in>A. f(x)) \<times> (\<lambda>x\<in>{f(x) . x\<in>A}. g(x)))"
      using lam_replacement_iff_lam_closed by simp
    moreover from this
    have "M({p \<in> (\<lambda>x\<in>A. f(x)) \<times> (\<lambda>x\<in>{f(x) . x\<in>A}. g(x)) . snd(fst(p))=fst(snd(p))})"
      using middle_separation by simp
    then
    have "M({ \<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> . x\<in>A })"
      using Collect_middle by simp
    ultimately
    have "M({ \<langle>fst(fst(p)),snd(snd(p))\<rangle> . p \<in> { \<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> . x\<in>A }})"
      using middle_del_replacement by (rule_tac RepFun_closed, auto dest:transM)
    then
    have "M({ \<langle>x,g(f(x))\<rangle> . x\<in>A })"
      using RepFun_middle_del by simp
    then
    have "M(\<lambda>x\<in>A. g(f(x)))"
      unfolding lam_def .
    }
  with assms
  show ?thesis using lam_replacement_iff_lam_closed by simp
qed

lemma Collect_pullback: "{p \<in> (\<lambda>x\<in>A. f(x)) \<times> (\<lambda>x\<in>A. g(x)) . fst(fst(p))=fst(snd(p))}
     = { \<langle>\<langle>x,f(x)\<rangle>,\<langle>x,g(x)\<rangle>\<rangle> . x\<in>A }"
  by (intro equalityI; auto simp:lam_def)

lemma RepFun_pullback:
  "{ \<langle>fst(fst(p)),\<langle>snd(fst(p)),snd(snd(p))\<rangle>\<rangle> . p \<in> { \<langle>\<langle>x,f(x)\<rangle>,\<langle>x,g(x)\<rangle>\<rangle> . x\<in>A }}
    =  { \<langle>x,\<langle>f(x),g(x)\<rangle>\<rangle> . x\<in>A }"
  by auto

lemma lam_replacement_pullback:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
          "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "lam_replacement(M, \<lambda>x. \<langle>f(x),g(x)\<rangle>)"
proof -
  {
    fix A
    note assms
    moreover
    assume "M(A)"
    moreover from calculation
    have "M({f(x) . x\<in>A})" "M({g(x) . x\<in>A})"
      using RepFun_closed[of f A] RepFun_closed[of g A]
        lam_replacement_imp_strong_replacement by (auto dest:transM)
    moreover from calculation
    have "M((\<lambda>x\<in>A. f(x)) \<times> (\<lambda>x\<in>A. g(x)))"
      using lam_replacement_iff_lam_closed by simp
    moreover from this
    have "M({p \<in> (\<lambda>x\<in>A. f(x)) \<times> (\<lambda>x\<in>A. g(x)) . fst(fst(p))=fst(snd(p))})"
      using pullback_separation by simp
    then
    have "M({ \<langle>\<langle>x,f(x)\<rangle>,\<langle>x,g(x)\<rangle>\<rangle> . x\<in>A })"
      using Collect_pullback by simp
    ultimately
    have "M({ \<langle>fst(fst(p)),\<langle>snd(fst(p)),snd(snd(p))\<rangle>\<rangle> . p \<in> { \<langle>\<langle>x,f(x)\<rangle>,\<langle>x,g(x)\<rangle>\<rangle> . x\<in>A }})"
      using pullback_replacement by (rule_tac RepFun_closed, auto dest:transM)
    then
    have "M({ \<langle>x,\<langle>f(x),g(x)\<rangle>\<rangle> . x\<in>A })"
      using RepFun_pullback by simp
    then
    have "M(\<lambda>x\<in>A. \<langle>f(x),g(x)\<rangle>)"
      unfolding lam_def .
    }
  with assms
  show ?thesis using lam_replacement_iff_lam_closed by simp
qed

lemma lam_replacement_hcomp2:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
    "lam_replacement(M, \<lambda>p. h(fst(p),snd(p)))"
    "\<forall>x[M]. \<forall>y[M]. M(h(x,y))"
  shows "lam_replacement(M, \<lambda>x. h(f(x),g(x)))"
  using assms lam_replacement_pullback[of f g]
    lam_replacement_hcomp[of "\<lambda>x. \<langle>f(x), g(x)\<rangle>" "\<lambda>\<langle>x,y\<rangle>. h(x,y)"]
  unfolding split_def by simp

lemma lam_replacement_identity: "lam_replacement(M,\<lambda>x. x)"
proof -
  {
    fix A
      \<comment> \<open>From here on, modified proof of @{thm M_cardinals.id_closed},
          the modified locale assumption @{thm id_separation}\<close>
    assume "M(A)"
    moreover from this
    have "id(A) = {z\<in> A\<times>A. \<exists>x[M]. z=<x,x>}"
      unfolding id_def lam_def by (auto dest:transM)
    moreover from calculation
    have "M({z\<in> A\<times>A. \<exists>x[M]. z=<x,x>})"
      using id_separation by simp
    ultimately
    have "M(id(A))" by simp
  }
  then
  show ?thesis using lam_replacement_iff_lam_closed
    unfolding id_def by simp
qed

lemma lam_replacement_constant: "M(b) \<Longrightarrow> lam_replacement(M,\<lambda>_. b)"
  unfolding lam_replacement_def strong_replacement_def
  by safe (rule_tac x="_\<times>{b}" in rexI; blast)

lemmas tag_replacement = lam_replacement_constant[unfolded lam_replacement_def]

lemma lam_replacement_id2: "lam_replacement(M, \<lambda>x. \<langle>x, x\<rangle>)"
  using lam_replacement_identity lam_replacement_pullback[of "\<lambda>x. x" "\<lambda>x. x"]
  by simp

lemmas id_replacement = lam_replacement_id2[unfolded lam_replacement_def]

lemma lam_replacement_apply:"M(S) \<Longrightarrow> lam_replacement(M, \<lambda>x.  S ` x)"
  sorry

lemma apply_replacement:"M(S) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = S ` x)"
  using lam_replacement_apply lam_replacement_imp_strong_replacement by simp

lemma lam_replacement_id_const: "M(b) \<Longrightarrow> lam_replacement(M, \<lambda>x. \<langle>x, b\<rangle>)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_pullback[of "\<lambda>x. x" "\<lambda>x. b"] by simp

lemmas pospend_replacement = lam_replacement_id_const[unfolded lam_replacement_def]

lemma lam_replacement_const_id: "M(b) \<Longrightarrow> lam_replacement(M, \<lambda>z. \<langle>b, z\<rangle>)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_pullback[of "\<lambda>x. b" "\<lambda>x. x"] by simp

lemmas prepend_replacement = lam_replacement_const_id[unfolded lam_replacement_def]

lemma lam_replacement_apply_const_id: "M(f) \<Longrightarrow> M(z) \<Longrightarrow>
      lam_replacement(M, \<lambda>x. f ` \<langle>z, x\<rangle>)"
  using lam_replacement_const_id[of z] lam_replacement_apply[of f]
    lam_replacement_hcomp[of "\<lambda>x. \<langle>z, x\<rangle>" "\<lambda>x. f`x"] by simp

lemmas apply_replacement2' = lam_replacement_apply_const_id[unfolded lam_replacement_def]

\<comment> \<open>Exactly the same as the one before\<close>
lemma apply_replacement1: "M(x) \<Longrightarrow> M(f) \<Longrightarrow>
      strong_replacement(M, \<lambda>z y. y = \<langle>z, f ` \<langle>x,z\<rangle>\<rangle>)"
  oops

\<comment> \<open>\<^term>\<open>M(x)\<close> redundant\<close>
lemma apply_replacement2: "M(x) \<Longrightarrow> M(f) \<Longrightarrow> M(z) \<Longrightarrow>
      strong_replacement(M, \<lambda>x y. y = \<langle>x, f ` \<langle>z, x\<rangle>\<rangle>)"
  oops

lemma lam_replacement_Inl: "lam_replacement(M, Inl)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_pullback[of "\<lambda>x. 0" "\<lambda>x. x"]
  unfolding Inl_def by simp

lemmas Inl_replacement1 = lam_replacement_Inl[unfolded lam_replacement_def]

lemma lam_replacement_Diff: "M(X) \<Longrightarrow> lam_replacement(M, \<lambda>x. x - X)"
  sorry

lemmas Pair_diff_replacement = lam_replacement_Diff[unfolded lam_replacement_def]

lemma diff_Pair_replacement: "M(p) \<Longrightarrow> strong_replacement(M, \<lambda>x y . y=\<langle>x,x-{p}\<rangle>)"
  using Pair_diff_replacement by simp

lemma lam_replacement_swap: "lam_replacement(M, \<lambda>x. \<langle>snd(x),fst(x)\<rangle>)"
    using lam_replacement_fst lam_replacement_snd
    lam_replacement_pullback[of "snd" "fst"] by simp

lemma swap_replacement:"strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,y\<rangle>. \<langle>y, x\<rangle>)(x)\<rangle>)"
  using lam_replacement_swap unfolding lam_replacement_def split_def by simp

lemma lam_replacement_Un:"lam_replacement(M, \<lambda>p. fst(p) \<union> snd(p))"
  unfolding lam_replacement_def strong_replacement_def apply simp
  sorry

lemma lam_replacement_Un_const:"M(b) \<Longrightarrow> lam_replacement(M, \<lambda>x. x \<union> b)"
  using lam_replacement_Un lam_replacement_hcomp2[of _ _ "(\<union>)"]
    lam_replacement_constant[of b] lam_replacement_identity by simp

lemmas tag_union_replacement = lam_replacement_Un_const[unfolded lam_replacement_def]

lemma lam_replacement_csquare: "lam_replacement(M,\<lambda>p. \<langle>fst(p) \<union> snd(p), fst(p), snd(p)\<rangle>)"
  using lam_replacement_Un lam_replacement_fst lam_replacement_snd
  by (fast intro: lam_replacement_pullback lam_replacement_hcomp2)

lemma csquare_lam_replacement:"strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,y\<rangle>. \<langle>x \<union> y, x, y\<rangle>)(x)\<rangle>)"
  using lam_replacement_csquare unfolding split_def lam_replacement_def .

lemma lam_replacement_assoc:"lam_replacement(M,\<lambda>x. \<langle>fst(fst(x)), snd(fst(x)), snd(x)\<rangle>)"
  using lam_replacement_fst lam_replacement_snd
  by (force intro: lam_replacement_pullback lam_replacement_hcomp)

lemma assoc_replacement:"strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>. \<langle>x, y, z\<rangle>)(x)\<rangle>)"
  using lam_replacement_assoc unfolding split_def lam_replacement_def .

end (* M_replacement *)

find_theorems "strong_replacement(_,\<lambda>x y. y = <x,_>)"
-"strong_replacement(_,\<lambda>x y. y = <x,_>) \<Longrightarrow> _"
-name:"_def" -name:intro -name:assumptions -name:closed -name: Derivations -name:transrec_equal_on_M
-name:Pair_diff_replacement
-name:id_replacement -name:tag_replacement -name:pospend_replacement -name:prepend_replacement
-name:Inl_replacement1 -name:apply_replacement1 -name:apply_replacement2 -name:diff_Pair_replacement
-name:swap_replacement -name:tag_union_replacement -name:csquare_lam_replacement
-name:assoc_replacement

end