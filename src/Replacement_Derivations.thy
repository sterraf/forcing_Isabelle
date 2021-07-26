section\<open>Main definitions of the development\<close>

theory Replacement_Derivations
  imports
    "ZF-Constructible.Relative"
    CardinalArith_Relative
    "../Tools/Try0"
begin

definition
  lam_replacement :: "[i\<Rightarrow>o,i\<Rightarrow>i] \<Rightarrow> o" where
  "lam_replacement(M,b) \<equiv> strong_replacement(M, \<lambda>x y. y = \<langle>x, b(x)\<rangle>)"

locale M_replacement = M_basic +
  assumes
    fst_lam_replacement: "lam_replacement(M,fst)"
    and
    snd_lam_replacement: "lam_replacement(M,snd)"
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

lemma id_replacement: "strong_replacement(M, \<lambda>x y. y = \<langle>x, x, x\<rangle>)"
  using lam_replacement_identity lam_replacement_pullback[of "\<lambda>x. x" "\<lambda>x. x"]
  unfolding lam_replacement_def by simp

lemma pospend_replacement: "M(b) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, x, b\<rangle>)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_pullback[of "\<lambda>x. x" "\<lambda>x. b"]
  unfolding lam_replacement_def by simp

lemma prepend_replacement: "M(b) \<Longrightarrow> strong_replacement(M, \<lambda>z y. y = \<langle>z, b, z\<rangle>)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_pullback[of "\<lambda>x. b" "\<lambda>x. x"]
  unfolding lam_replacement_def by simp

lemma Inl_replacement1: "strong_replacement(M, \<lambda>x y. y = \<langle>x, Inl(x)\<rangle>)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_pullback[of "\<lambda>x. 0" "\<lambda>x. x"]
  unfolding lam_replacement_def Inl_def by simp

end (* M_replacement *)

find_theorems "strong_replacement(_,\<lambda>x y. y = <x,_>)" -name: Derivations
-"strong_replacement(_,\<lambda>x y. y = <x,_>) \<Longrightarrow> _" -name:"_def" -name:intro

end