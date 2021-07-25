section\<open>Main definitions of the development\<close>

theory Replacement_Derivations
  imports
    "ZF-Constructible.Relative"
    "../Tools/Try0"
begin

definition
  lam_replacement :: "[i\<Rightarrow>o,i\<Rightarrow>i] \<Rightarrow> o" where
  "lam_replacement(M,b) \<equiv> strong_replacement(M, \<lambda>x y. y = \<langle>x, b(x)\<rangle>)"

locale M_replacement = M_basic +
  assumes
    fst_replacement: "strong_replacement(M, \<lambda>x y. y=fst(x))"
    and
    snd_replacement: "strong_replacement(M, \<lambda>x y. y=snd(x))"
    and
    middle_separation: "separation(M, \<lambda>x. snd(fst(x))=fst(snd(x)))"
    and
    middle_del_replacement: "strong_replacement(M, \<lambda>x y. y=\<langle>fst(fst(x)),snd(snd(x))\<rangle>)"
begin

lemma lam_replacement_iff_lam_closed:
  assumes "\<forall>x. M(b(x))"
  shows "lam_replacement(M, b) \<longleftrightarrow>  (\<forall>A[M]. M(\<lambda>x\<in>A. b(x)))"
  using assms lam_closed lam_funtype[of _ b, THEN Pi_memberD]
  unfolding lam_replacement_def strong_replacement_def by (auto intro:lamI)

lemma lam_replacement_imp_strong_replacement:
  assumes "lam_replacement(M, b)" "\<forall>x. M(b(x))"
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
          "\<forall>x. M(f(x))" "\<forall>x. M(g(x))"
  shows "lam_replacement(M, \<lambda>x. g(f(x)))"
proof -
  {
    fix A
    note assms
    moreover
    assume "M(A)"
    moreover from calculation
    have "M({f(x) . x\<in>A})"
      using RepFun_closed[of f] lam_replacement_imp_strong_replacement by auto
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

end (* M_replacement *)

end