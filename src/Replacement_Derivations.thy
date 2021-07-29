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
    lam_replacement_domain: "lam_replacement(M,domain)"
    and
    lam_replacement_converse: "lam_replacement(M,converse)"
    and
    lam_replacement_fst: "lam_replacement(M,fst)"
    and
    lam_replacement_snd: "lam_replacement(M,snd)"
    and
    lam_replacement_Union: "lam_replacement(M,Union)"
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
    and
    lam_replacement_Un:"lam_replacement(M, \<lambda>p. fst(p) \<union> snd(p))"
    and
    lam_replacement_cons:"lam_replacement(M, \<lambda>p. cons(fst(p),snd(p)))"
    and
    lam_replacement_Diff:"lam_replacement(M, \<lambda>p. fst(p) - snd(p))"
    and
    lam_replacement_Image:"lam_replacement(M, \<lambda>p. fst(p) `` snd(p))"
    and
    lam_replacement_minimum:"lam_replacement(M, \<lambda>p. minimum(fst(p),snd(p)))"
    and
    lam_replacement_RepFun_cons:"lam_replacement(M, \<lambda>p. RepFun(fst(p), \<lambda>x. {\<langle>snd(p),x\<rangle>}))"
    \<comment> \<open>This one is too particular: It is for \<^term>\<open>Sigfun\<close>.
        I would like greater modularity here.\<close>
    and
    separation_fst_equal : "M(a) \<Longrightarrow> separation(M,\<lambda>x . fst(x)=a)"
    and
    separation_equal_fst2 : "M(a) \<Longrightarrow> separation(M,\<lambda>x . fst(fst(x))=a)"
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

\<comment> \<open>This result doesn't depend on any other replacement instance.\<close>
lemma lam_replacement_if:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)" "separation(M,b)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "lam_replacement(M, \<lambda>x. if b(x) then f(x) else g(x))"
proof -
  let ?G="\<lambda>x. if b(x) then f(x) else g(x)"
  let ?b="\<lambda>A . {x\<in>A. b(x)}" and ?b'="\<lambda>A . {x\<in>A. \<not>b(x)}"
  have eq:"(\<lambda>x\<in>A . ?G(x)) = (\<lambda>x\<in>?b(A) . f(x)) \<union> (\<lambda>x\<in>?b'(A).g(x))" for A
    unfolding lam_def by auto
  have "?b'(A) = A - ?b(A)" for A by auto
  moreover
  have "M(?b(A))" if "M(A)" for A using assms that by simp
  moreover from calculation
  have "M(?b'(A))" if "M(A)" for A using that by simp
  moreover from calculation assms
  have "M(\<lambda>x\<in>?b(A). f(x))" "M(\<lambda>x\<in>?b'(A) . g(x))" if "M(A)" for A
    using lam_replacement_iff_lam_closed that
    by simp_all
  moreover from this
  have "M((\<lambda>x\<in>?b(A) . f(x)) \<union> (\<lambda>x\<in>?b'(A).g(x)))" if "M(A)" for A
    using that by simp
  ultimately
  have "M(\<lambda>x\<in>A. if b(x) then f(x) else g(x))" if "M(A)" for A
    using that eq by simp
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

lemmas tag_replacement = lam_replacement_constant[unfolded lam_replacement_def]

lemma lam_replacement_id2: "lam_replacement(M, \<lambda>x. \<langle>x, x\<rangle>)"
  using lam_replacement_identity lam_replacement_pullback[of "\<lambda>x. x" "\<lambda>x. x"]
  by simp

lemmas id_replacement = lam_replacement_id2[unfolded lam_replacement_def]

lemma lam_replacement_apply:"M(S) \<Longrightarrow> lam_replacement(M, \<lambda>x.  S ` x)"
  using lam_replacement_Union lam_replacement_constant lam_replacement_identity
    lam_replacement_Image lam_replacement_cons
    lam_replacement_hcomp2[of _ _ Image] lam_replacement_hcomp2[of "\<lambda>x. x" "\<lambda>_. 0" cons]
  unfolding apply_def
  by (rule_tac lam_replacement_hcomp[of _ Union]) (force intro:lam_replacement_hcomp)+

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

lemma lam_replacement_Inr: "lam_replacement(M, Inr)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_pullback[of "\<lambda>x. 1" "\<lambda>x. x"]
  unfolding Inr_def by simp

lemmas Inl_replacement1 = lam_replacement_Inl[unfolded lam_replacement_def]

lemma lam_replacement_Diff': "M(X) \<Longrightarrow> lam_replacement(M, \<lambda>x. x - X)"
  using lam_replacement_Diff
  by (force intro: lam_replacement_hcomp2 lam_replacement_constant
      lam_replacement_identity)+

lemmas Pair_diff_replacement = lam_replacement_Diff'[unfolded lam_replacement_def]

lemma diff_Pair_replacement: "M(p) \<Longrightarrow> strong_replacement(M, \<lambda>x y . y=\<langle>x,x-{p}\<rangle>)"
  using Pair_diff_replacement by simp

lemma lam_replacement_swap: "lam_replacement(M, \<lambda>x. \<langle>snd(x),fst(x)\<rangle>)"
    using lam_replacement_fst lam_replacement_snd
    lam_replacement_pullback[of "snd" "fst"] by simp

lemma swap_replacement:"strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,y\<rangle>. \<langle>y, x\<rangle>)(x)\<rangle>)"
  using lam_replacement_swap unfolding lam_replacement_def split_def by simp

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

lemma lam_replacement_prod_fun: "M(f) \<Longrightarrow> M(g) \<Longrightarrow> lam_replacement(M,\<lambda>x. \<langle>f ` fst(x), g ` snd(x)\<rangle>)"
  using lam_replacement_fst lam_replacement_snd
  by (force intro: lam_replacement_pullback lam_replacement_hcomp lam_replacement_apply)

lemma prod_fun_replacement:"M(f) \<Longrightarrow> M(g) \<Longrightarrow>
  strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>w,y\<rangle>. \<langle>f ` w, g ` y\<rangle>)(x)\<rangle>)"
  using lam_replacement_prod_fun unfolding split_def lam_replacement_def .

\<comment> \<open>Exactly the same as the previous one.\<close>
lemma prod_bij_rel_replacement:"M(f) \<Longrightarrow> M(g) \<Longrightarrow>
     strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,y\<rangle>. \<langle>f ` x, g ` y\<rangle>)(x)\<rangle>)"
  oops

lemma lam_replacement_vimage:"lam_replacement(M, \<lambda>p. fst(p) -`` snd(p))"
  using lam_replacement_Image lam_replacement_converse lam_replacement_fst
    lam_replacement_snd unfolding vimage_def
  by (force intro: lam_replacement_pullback lam_replacement_hcomp2 lam_replacement_hcomp)+

lemma lam_replacement_vimage_sing: "M(f) \<Longrightarrow> lam_replacement(M, \<lambda>x. f -`` {x})"
  using lam_replacement_vimage lam_replacement_constant lam_replacement_cons
    lam_replacement_hcomp2[of _ _ vimage] lam_replacement_hcomp2[of "\<lambda>x. x" "\<lambda>_. 0" cons]
  by (force intro: lam_replacement_identity)

lemmas cardinal_lib_assms4 = lam_replacement_vimage_sing[unfolded lam_replacement_def]

lemma lam_replacement_surj_imp_inj1:
  "M(x) \<Longrightarrow> lam_replacement(M, \<lambda>y. {\<langle>x, y\<rangle>})"
  using lam_replacement_cons lam_replacement_constant
  by (rule_tac lam_replacement_hcomp2[of _ _ cons], simp_all)
    (fast intro: lam_replacement_hcomp lam_replacement_pullback lam_replacement_identity)

\<comment> \<open>The following instance is unnecessarily complicated, since it follows from
@{thm lam_replacement_surj_imp_inj1}\<close>
lemma surj_imp_inj_replacement1:
  "M(f) \<Longrightarrow> M(x) \<Longrightarrow> strong_replacement(M, \<lambda>y z. y \<in> f -`` {x} \<and> z = {\<langle>x, y\<rangle>})"
  using lam_replacement_surj_imp_inj1[THEN lam_replacement_imp_strong_replacement, of x]
  unfolding strong_replacement_def
  by (simp, safe, drule_tac x="A \<inter> f -`` {x}" in rspec,
      simp, erule_tac rexE, rule_tac x=Y in rexI) auto

lemma lam_replacement_Sigfun: "M(f) \<Longrightarrow> lam_replacement(M, \<lambda>x. \<Union>y\<in>f -`` {x}. {\<langle>x, y\<rangle>})"
  using lam_replacement_Union lam_replacement_identity lam_replacement_vimage_sing
    lam_replacement_surj_imp_inj1[THEN lam_replacement_imp_strong_replacement]
    lam_replacement_hcomp2[of "\<lambda>x. \<langle>_,x\<rangle>" "\<lambda>_. 0" cons,
      THEN lam_replacement_imp_strong_replacement] unfolding apply_def
  apply (rule_tac lam_replacement_hcomp[of _ Union])
     apply (auto intro:RepFun_closed dest:transM)
  by (rule lam_replacement_RepFun_cons[THEN [5] lam_replacement_hcomp2])
    (auto intro:RepFun_closed dest:transM)

lemma surj_imp_inj_replacement2:
  "M(f) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = Sigfun(x, \<lambda>y. f -`` {y}))"
  using lam_replacement_surj_imp_inj1[THEN lam_replacement_imp_strong_replacement]
  unfolding Sigfun_def
  by (rule_tac lam_replacement_Sigfun[THEN lam_replacement_imp_strong_replacement, of f])
    (auto intro:RepFun_closed dest:transM)

lemma surj_imp_inj_replacement3:
  "M(f) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = f -`` {x})"
  using lam_replacement_vimage_sing lam_replacement_imp_strong_replacement by simp

lemma lam_replacement_minimum_vimage:
  "M(f) \<Longrightarrow> M(r) \<Longrightarrow> lam_replacement(M, \<lambda>x. minimum(r, f -`` {x}))"
  using lam_replacement_minimum lam_replacement_vimage_sing lam_replacement_constant
  by (rule_tac lam_replacement_hcomp2[of _ _ minimum])
    (force intro: lam_replacement_identity)+

lemmas surj_imp_inj_replacement4 = lam_replacement_minimum_vimage[unfolded lam_replacement_def]

lemmas domain_replacement =  lam_replacement_domain[unfolded lam_replacement_def]

lemma domain_replacement_simp: "strong_replacement(M, \<lambda>x y. y=domain(x))"
  using lam_replacement_domain lam_replacement_imp_strong_replacement by simp

\<comment> \<open>Redundant\<close>
lemma image_replacement:
    "M(f) \<Longrightarrow> M(a) \<Longrightarrow> strong_replacement(M, \<lambda> x y . y = f`x)"
  oops

\<comment> \<open>Redundant, it has another name to avoid a clash in Absolute Versions.\<close>
lemma image_replacement':
    "M(f) \<Longrightarrow> strong_replacement(M, \<lambda> x y . y = f`x)"
  oops

lemma un_Pair_replacement: "M(p) \<Longrightarrow> strong_replacement(M, \<lambda>x y . y = x\<union>{p})"
  using lam_replacement_Un_const[THEN lam_replacement_imp_strong_replacement] by simp

lemma restrict_strong_replacement: "M(r) \<Longrightarrow> strong_replacement(M, \<lambda>x y . y=restrict(x,r))"
  sorry

lemma diff_replacement: "M(X) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = x - X)"
  using lam_replacement_Diff'[THEN lam_replacement_imp_strong_replacement] by simp

\<comment> \<open>The following instance is unnecessarily complicated, since it follows from
@{thm lam_replacement_surj_imp_inj1}\<close>
lemma Pi_replacement1: "M(x) \<Longrightarrow> M(y) \<Longrightarrow>  strong_replacement(M, \<lambda>ya z. ya \<in> y \<and> z = {\<langle>x, ya\<rangle>})"
  using lam_replacement_surj_imp_inj1[THEN lam_replacement_imp_strong_replacement, of x]
  unfolding strong_replacement_def
  by (simp, safe, drule_tac x="A \<inter> y" in rspec,
      simp, erule_tac rexE, rule_tac x=Y in rexI) auto

lemma lam_replacement_Pi: "M(y) \<Longrightarrow> lam_replacement(M, \<lambda>x. \<Union>xa\<in>y. {\<langle>x, xa\<rangle>})"
  using lam_replacement_Union lam_replacement_identity lam_replacement_constant
    lam_replacement_surj_imp_inj1[THEN lam_replacement_imp_strong_replacement]
    lam_replacement_hcomp2[of "\<lambda>x. \<langle>_,x\<rangle>" "\<lambda>_. 0" cons,
      THEN lam_replacement_imp_strong_replacement] unfolding apply_def
  apply (rule_tac lam_replacement_hcomp[of _ Union])
     apply (auto intro:RepFun_closed dest:transM)
  by (rule lam_replacement_RepFun_cons[THEN [5] lam_replacement_hcomp2])
    (auto intro:RepFun_closed dest:transM)

lemma Pi_replacement2: "M(y) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = (\<Union>xa\<in>y. {\<langle>x, xa\<rangle>}))"
  using lam_replacement_Pi[THEN lam_replacement_imp_strong_replacement, of y]
proof -
  assume "M(y)"
  then
  have "M(x) \<Longrightarrow> M(\<Union>xa\<in>y. {\<langle>x, xa\<rangle>})" for x
    using lam_replacement_surj_imp_inj1[THEN lam_replacement_imp_strong_replacement]
    by (rule_tac Union_closed RepFun_closed, simp_all | safe)+
      (force dest: transM) \<comment> \<open>a bit slow\<close>
  with \<open>M(y)\<close>
  show ?thesis
    using lam_replacement_Pi[THEN lam_replacement_imp_strong_replacement, of y]
    by blast
qed

lemma separation_in :
  assumes "M(a)"
  shows "separation(M,\<lambda>x . x\<in>a)"
proof -
  have "M({x\<in>A . x\<in>a})" if "M(A)" for A
  proof -
    have "{x\<in>A . x\<in>a} = A \<inter> a" by auto
    with assms \<open>M(A)\<close>
    show ?thesis by simp
  qed
  then
  show ?thesis using separation_iff Collect_abs
    by simp
qed

lemma separation_equal :
  shows "separation(M,\<lambda>x . x=a)"
proof -
  have "M({x\<in>A . x=a})" if "M(A)" for A
  proof -
    have "{x\<in>A . x=a} = (if a\<in>A then {a} else 0)" by auto
    with transM[OF _ \<open>M(A)\<close>]
    show ?thesis by simp
  qed
  then
  show ?thesis using separation_iff Collect_abs
    by simp
qed

lemma if_then_Inj_replacement:
  shows "M(A) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, if x \<in> A then Inl(x) else Inr(x)\<rangle>)"
  using lam_replacement_if lam_replacement_Inl lam_replacement_Inr separation_in
  unfolding lam_replacement_def
  by simp

lemma lam_if_then_replacement:
    "M(b) \<Longrightarrow>
    M(a) \<Longrightarrow> M(f) \<Longrightarrow> strong_replacement(M, \<lambda>y ya. ya = \<langle>y, if y = a then b else f ` y\<rangle>)"
  using lam_replacement_if lam_replacement_apply lam_replacement_constant
    separation_equal
  unfolding lam_replacement_def
  by simp

lemma if_then_replacement:
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(g) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, if x \<in> A then f ` x else g ` x\<rangle>)"
  using lam_replacement_if lam_replacement_apply[of f] lam_replacement_apply[of g]
    separation_in
  unfolding lam_replacement_def
  by simp

lemma ifx_replacement:
    "M(f) \<Longrightarrow>
    M(b) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, if x \<in> range(f) then converse(f) ` x else b\<rangle>)"
  using lam_replacement_if lam_replacement_apply lam_replacement_constant
    separation_in
  unfolding lam_replacement_def
  by simp

lemma if_then_range_replacement2:
    "M(A) \<Longrightarrow> M(C) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, if x = Inl(A) then C else x\<rangle>)"
  using lam_replacement_if lam_replacement_constant lam_replacement_identity
    separation_equal
  unfolding lam_replacement_def
  by simp

lemma lam_replacement_succ:
  "M(f) \<Longrightarrow> lam_replacement(M,\<lambda>z . succ(z))"
  unfolding succ_def
  using lam_replacement_hcomp2[of "\<lambda>x. x" "\<lambda>x. x" cons]
    lam_replacement_cons lam_replacement_identity
  by simp

lemma if_then_range_replacement:
    "M(u) \<Longrightarrow>
    M(f) \<Longrightarrow>
    strong_replacement
     (M,
      \<lambda>z y. y = \<langle>z, if z = u then f ` 0 else if z \<in> range(f) then f ` succ(converse(f) ` z) else z\<rangle>)"
  using lam_replacement_if separation_equal separation_in
    lam_replacement_constant lam_replacement_identity
    lam_replacement_succ lam_replacement_apply
    lam_replacement_hcomp[of "\<lambda>x. converse(f)`x" "succ"]
    lam_replacement_hcomp[of "\<lambda>x. succ(converse(f)`x)" "\<lambda>x . f`x"]
  unfolding lam_replacement_def
  by simp

lemma Inl_replacement2:
    "M(A) \<Longrightarrow>
    strong_replacement(M, \<lambda>x y. y = \<langle>x, if fst(x) = A then Inl(snd(x)) else Inr(x)\<rangle>)"
  using lam_replacement_if separation_fst_equal
        lam_replacement_hcomp[of "snd" "Inl"]
        lam_replacement_Inl lam_replacement_Inr lam_replacement_snd
  unfolding lam_replacement_def
  by simp

lemma case_closed :
  assumes "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "\<forall>x[M]. M(case(f,g,x))"
  unfolding case_def split_def cond_def
  using assms by simp

lemma lam_replacement_case :
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "lam_replacement(M, \<lambda>x . case(f,g,x))"
  unfolding case_def split_def cond_def
  using lam_replacement_if separation_fst_equal
        lam_replacement_hcomp[of "snd" g]
        lam_replacement_hcomp[of "snd" f]
        lam_replacement_snd assms
  by simp

lemma case_replacement1:
    "strong_replacement(M, \<lambda>z y. y = \<langle>z, case(Inr, Inl, z)\<rangle>)"
  using lam_replacement_case lam_replacement_Inl lam_replacement_Inr
  unfolding lam_replacement_def
  by simp

lemma case_replacement2:
    "strong_replacement(M, \<lambda>z y. y = \<langle>z, case(case(Inl, \<lambda>y. Inr(Inl(y))), \<lambda>y. Inr(Inr(y)), z)\<rangle>)"
  using lam_replacement_case lam_replacement_hcomp
        case_closed[of Inl "\<lambda>x. Inr(Inl(x))"]
       lam_replacement_Inl lam_replacement_Inr
  unfolding lam_replacement_def
  by simp

lemma case_replacement4:
    "M(f) \<Longrightarrow> M(g) \<Longrightarrow> strong_replacement(M, \<lambda>z y. y = \<langle>z, case(\<lambda>w. Inl(f ` w), \<lambda>y. Inr(g ` y), z)\<rangle>)"
  using lam_replacement_case lam_replacement_hcomp
       lam_replacement_Inl lam_replacement_Inr lam_replacement_apply
  unfolding lam_replacement_def
  by simp

\<comment> \<open>Exactly as the previous one.\<close>
lemma sum_bij_rel_replacement:
    "M(f) \<Longrightarrow> M(g) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, case(\<lambda>u. Inl(f ` u), \<lambda>z. Inr(g ` z), x)\<rangle>)"
  oops

lemma case_replacement5:
    "strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,z\<rangle>. case(\<lambda>y. Inl(\<langle>y, z\<rangle>), \<lambda>y. Inr(\<langle>y, z\<rangle>), x))(x)\<rangle>)"
  unfolding split_def case_def cond_def
  using lam_replacement_if separation_equal_fst2
     lam_replacement_snd lam_replacement_Inl lam_replacement_Inr
     lam_replacement_hcomp[OF
       lam_replacement_pullback[OF
         lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd]]]
  unfolding lam_replacement_def
  by simp

end (* M_replacement *)

locale M_replacement_lepoll = M_replacement + M_inj +
  fixes A F S fa K x f r
  assumes
    types[simp]:"M(A)" "\<forall>x[M]. M(F(A,x))" "M(S)" "M(fa)" "M(K)" "M(x)" "M(f)" "M(r)"
    and
    lam_lepoll_assumption_F:"lam_replacement(M,F(A))"
    and
    lam_replacement_inj_rel:"lam_replacement(M, \<lambda>p. inj\<^bsup>M\<^esup>(fst(p),snd(p)))"
begin

lemma lepoll_assumptions1:
  shows "lepoll_assumptions1(M,A,F,S,fa,K,x,f,r)"
proof -
  {
    fix z C
    assume "z\<in>S" "M(C)"
    moreover from this
    have "M(z)" "\<forall>y[M]. M({\<langle>z, y\<rangle>})" by (auto dest:transM)
    moreover
    have "\<forall>C[M]. univalent(M, C, \<lambda>t y. y = {\<langle>z, t\<rangle>})" by simp
    ultimately
    have "M(Z) \<Longrightarrow> \<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>xa[M]. xa \<in> Z \<and> b = {\<langle>z, xa\<rangle>})" for Z
      using lam_replacement_surj_imp_inj1[THEN
          lam_replacement_imp_strong_replacement]
      unfolding strong_replacement_def by simp
    moreover from \<open>M(C)\<close> \<open>M(z)\<close>
    have "M(C \<inter> F(A,z))" by simp
    ultimately
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>xa[M]. xa \<in> C \<inter> F(A, z) \<and> b = {\<langle>z, xa\<rangle>})"
      by blast
  }
  then
  show ?thesis
    unfolding strong_replacement_def lepoll_assumptions_defs
    by (simp)
qed

lemma lepoll_assumptions3:"lepoll_assumptions3(M,A,F,S,fa,K,x,f,r)"
  using lam_lepoll_assumption_F[THEN lam_replacement_imp_strong_replacement]
  unfolding lepoll_assumptions_defs by simp

lemma lepoll_assumptions4:"lepoll_assumptions4(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_minimum lam_replacement_constant lam_lepoll_assumption_F
  unfolding lepoll_assumptions_defs
    lam_replacement_def[symmetric]
  by (rule_tac lam_replacement_hcomp2[of _ _ minimum])
    (force intro: lam_replacement_identity)+

lemma lepoll_assumptions6:\<comment> \<open>almost copy-paste\<close>
  shows "lepoll_assumptions6(M,A,F,S,fa,K,x,f,r)"
proof -
  {
    fix C
    assume "M(C)"
    moreover from this
    have "\<forall>y[M]. M({\<langle>x, y\<rangle>})" by (auto dest:transM)
    moreover
    have "\<forall>C[M]. univalent(M, C, \<lambda>t y. y = {\<langle>x, t\<rangle>})" by simp
    ultimately
    have "M(Z) \<Longrightarrow> \<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>xa[M]. xa \<in> Z \<and> b = {\<langle>x, xa\<rangle>})" for Z
      using lam_replacement_surj_imp_inj1[THEN
          lam_replacement_imp_strong_replacement]
      unfolding strong_replacement_def by simp
    moreover from \<open>M(C)\<close>
    have "M(C \<inter> inj\<^bsup>M\<^esup>(F(A, x),S))" by simp
    ultimately
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>xa[M]. xa \<in> C \<inter> inj\<^bsup>M\<^esup>(F(A, x),S) \<and> b = {\<langle>x, xa\<rangle>})"
      by blast
  }
  then
  show ?thesis
    unfolding strong_replacement_def lepoll_assumptions_defs
    by simp
qed

lemma lepoll_assumptions9:"lepoll_assumptions9(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_minimum lam_replacement_constant lam_lepoll_assumption_F
    lam_replacement_hcomp2[of _ _ "inj_rel(M)"] lam_replacement_inj_rel lepoll_assumptions4
  unfolding lepoll_assumptions_defs lam_replacement_def[symmetric]
  by (rule_tac lam_replacement_hcomp2[of _ _ minimum])
    (force intro: lam_replacement_identity)+

find_theorems name:lepoll_assumptions name:def -name:defs
-name:"assumptions1_" -name:assumptions6 -name:assumptions3 -name:assumptions4 -name:assumptions9

end (* M_replacement_lepoll *)

find_theorems
"strong_replacement(_,\<lambda>x y. y = <x,_>)" -"strong_replacement(_,\<lambda>x y. y = <x,_>) \<Longrightarrow> _"
(* "strong_replacement" -"strong_replacement(_,_) \<Longrightarrow> _" -"strong_replacement(_,\<lambda>x y. y = <x,_>)" *)
-name:"_def" -name:intro -name:assumptions -name:closed -name: Derivations -name:transrec_equal_on_M
-name:M_cardinal_UN -name:"absolute" -name:Separation -name:"Rank." -name:"Interface."
-name:"WFrec." -name:"Relative.strong_" -name:"L_axioms" -name:"Names" -name:"Relative.M_b"
-name:"Relative.M_t" -name:"Internal_ZFC"
-name:Pair_diff_replacement
-name:id_replacement -name:tag_replacement -name:pospend_replacement -name:prepend_replacement
-name:Inl_replacement1 -name:apply_replacement1 -name:apply_replacement2 -name:diff_Pair_replacement
-name:swap_replacement -name:tag_union_replacement -name:csquare_lam_replacement
-name:assoc_replacement -name:prod_fun_replacement -name:prod_bij_rel_replacement
-name:cardinal_lib_assms4 -name:surj_imp_inj_replacement -name:domain_replacement
-name:apply_replacement -name:image_replacement
-name:un_Pair_replacement -name:restrict_strong_replacement -name:diff_replacement
-name:Pi_replacement -name:snd_replacement
-name:if_then_Inj_replacement -name:lam_if_then_replacement -name:if_then_replacement
-name:ifx_replacement -name:if_then_range_replacement2 -name:if_then_range_replacement
-name:Inl_replacement2
-name:case_replacement1 -name:case_replacement2 -name:case_replacement4 -name:case_replacement5
-name:sum_bij_rel_replacement

end