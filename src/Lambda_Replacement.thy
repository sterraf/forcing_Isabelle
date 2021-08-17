section\<open>Replacements using Lambdas\<close>

theory Lambda_Replacement
  imports
    "ZF-Constructible.Relative"
    ZF_Miscellanea\<comment> \<open>for \<^term>\<open>SepReplace\<close>\<close>
    Discipline_Function
    (* "../Tools/Try0" *)
begin

definition
  lam_replacement :: "[i\<Rightarrow>o,i\<Rightarrow>i] \<Rightarrow> o" where
  "lam_replacement(M,b) \<equiv> strong_replacement(M, \<lambda>x y. y = \<langle>x, b(x)\<rangle>)"

context M_basic
begin

lemma separation_univ :
  shows "separation(M,M)"
  unfolding separation_def by auto

lemma separation_in :
  assumes "M(a)"
  shows "separation(M,\<lambda>x . x\<in>a)"
proof -
  have "{x\<in>A . x\<in>a} = A \<inter> a" for A by auto
  with \<open>M(a)\<close>
  show ?thesis using separation_iff Collect_abs
    by simp
qed

lemma separation_equal :
  shows "separation(M,\<lambda>x . x=a)"
proof -
  have "{x\<in>A . x=a} = (if a\<in>A then {a} else 0)" for A
    by auto
  then
  have "M({x\<in>A . x=a})" if "M(A)" for A
    using transM[OF _ \<open>M(A)\<close>] by simp
  then
  show ?thesis using separation_iff Collect_abs
    by simp
qed

lemma lam_replacement_iff_lam_closed:
  assumes "\<forall>x[M]. M(b(x))"
  shows "lam_replacement(M, b) \<longleftrightarrow>  (\<forall>A[M]. M(\<lambda>x\<in>A. b(x)))"
  using assms lam_closed lam_funtype[of _ b, THEN Pi_memberD]
  unfolding lam_replacement_def strong_replacement_def
  by (auto intro:lamI dest:transM)
    (rule lam_closed, auto simp add:strong_replacement_def dest:transM)

lemma lam_replacement_cong:
  assumes "lam_replacement(M,f)" "\<forall>x[M]. f(x) = g(x)" "\<forall>x[M]. M(f(x))"
  shows "lam_replacement(M,g)"
proof -
  note assms
  moreover from this
  have "\<forall>A[M]. M(\<lambda>x\<in>A. f(x))"
    using lam_replacement_iff_lam_closed
    by simp
  moreover from calculation
  have "(\<lambda>x\<in>A . f(x)) = (\<lambda>x\<in>A . g(x))" if "M(A)" for A
    using lam_cong[OF refl,of A f g] transM[OF _ that]
    by simp
  ultimately
  show ?thesis
        using lam_replacement_iff_lam_closed
    by simp
qed

lemma lam_replacement_imp_strong_replacement_aux:
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

lemma lam_replacement_imp_RepFun_Lam:
  assumes "lam_replacement(M, f)" "M(A)"
  shows "M({y . x\<in>A , M(y) \<and> y=\<langle>x,f(x)\<rangle>})"
proof -
  from assms
  obtain Y where 1:"M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,f(x)\<rangle>)"
    unfolding lam_replacement_def strong_replacement_def
    by auto
  moreover from calculation
  have "Y = {y . x\<in>A , M(y) \<and> y = \<langle>x,f(x)\<rangle>}" (is "Y=?R")
  proof(intro equalityI subsetI)
    fix y
    assume "y\<in>Y"
    moreover from this 1
    obtain x where "x\<in>A" "y=\<langle>x,f(x)\<rangle>" "M(y)"
      using transM[OF _ \<open>M(Y)\<close>] by auto
    ultimately
    show "y\<in>?R"
      by auto
  next
    fix z
    assume "z\<in>?R"
    moreover from this
    obtain a where "a\<in>A" "z=\<langle>a,f(a)\<rangle>" "M(a)" "M(f(a))"
      using transM[OF _ \<open>M(A)\<close>]
      by auto
    ultimately
    show "z\<in>Y" using 1 by simp
  qed
  ultimately
  show ?thesis by auto
qed

lemma lam_closed_imp_closed:
  assumes "\<forall>A[M]. M(\<lambda>x\<in>A. f(x))"
  shows "\<forall>x[M]. M(f(x))"
proof
  fix x
  assume "M(x)"
  moreover from this and assms
  have "M(\<lambda>x\<in>{x}. f(x))" by simp
  ultimately
  show "M(f(x))"
    using image_lam[of "{x}" "{x}" f]
      image_closed[of "{x}" "(\<lambda>x\<in>{x}. f(x))"] by (auto dest:transM)
qed

subsection\<open>Replacement instances obtained through Powerset\<close>

txt\<open>The next few lemmas provide bounds for certain constructions.\<close>

lemma not_functional_Replace_0:
  assumes "\<not>(\<forall>y y'. P(y) \<and> P(y') \<longrightarrow> y=y')"
  shows "{y . x \<in> A, P(y)} = 0"
  using assms by (blast elim!: ReplaceE)

lemma Replace_in_Pow_rel:
  assumes "\<And>x b. x \<in> A \<Longrightarrow> P(x,b) \<Longrightarrow> b \<in> U" "\<forall>x\<in>A. \<forall>y y'. P(x,y) \<and> P(x,y') \<longrightarrow> y=y'"
    "separation(M, \<lambda>y. \<exists>x[M]. x \<in> A \<and> P(x, y))"
    "M(U)" "M(A)"
  shows "{y . x \<in> A, P(x, y)} \<in> Pow\<^bsup>M\<^esup>(U)"
proof -
  from assms
  have "{y . x \<in> A, P(x, y)} \<subseteq> U"
    "z \<in> {y . x \<in> A, P(x, y)} \<Longrightarrow> M(z)" for z
    by (auto dest:transM)
  with assms
  have "{y . x \<in> A, P(x, y)} = {y\<in>U . \<exists>x[M]. x\<in>A \<and> P(x,y)}"
    by (intro equalityI) (auto, blast)
  with assms
  have "M({y . x \<in> A, P(x, y)})"
    by simp
  with assms
  show ?thesis
    using mem_Pow_rel_abs by auto
qed

lemma Replace_sing_0_in_Pow_rel:
  assumes "\<And>b. P(b) \<Longrightarrow> b \<in> U"
    "separation(M, \<lambda>y. P(y))" "M(U)"
  shows "{y . x \<in> {0}, P(y)} \<in> Pow\<^bsup>M\<^esup>(U)"
proof (cases "\<forall>y y'. P(y) \<and> P(y') \<longrightarrow> y=y'")
  case True
  with assms
  show ?thesis by (rule_tac Replace_in_Pow_rel) auto
next
  case False
  with assms
  show ?thesis
    using nonempty not_functional_Replace_0[of P "{0}"] Pow_rel_char by auto
qed

lemma The_in_Pow_rel_Union:
  assumes "\<And>b. P(b) \<Longrightarrow> b \<in> U" "separation(M, \<lambda>y. P(y))" "M(U)"
  shows "(THE i. P(i)) \<in> Pow\<^bsup>M\<^esup>(\<Union>U)"
proof -
  note assms
  moreover from this
  have "(THE i. P(i)) \<in> Pow(\<Union>U)"
    unfolding the_def by auto
  moreover from assms
  have "M(THE i. P(i))"
    using Replace_sing_0_in_Pow_rel[of P U] unfolding the_def
    by (auto dest:transM)
  ultimately
  show ?thesis
    using Pow_rel_char by auto
qed

lemma separation_least: "separation(M, \<lambda>y. Ord(y) \<and> P(y) \<and> (\<forall>j. j < y \<longrightarrow> \<not> P(j)))"
  unfolding separation_def
proof
  fix z
  assume "M(z)"
  have "M({x \<in> z . x \<in> z \<and> Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))})"
    (is "M(?y)")
  proof (cases "\<exists>x\<in>z. Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))")
    case True
    with \<open>M(z)\<close>
    have "\<exists>x[M]. ?y = {x}"
      by (safe, rename_tac x, rule_tac x=x in rexI)
        (auto dest:transM, intro equalityI, auto elim:Ord_linear_lt)
    then
    show ?thesis
      by auto
  next
    case False
    then
    have "{x \<in> z . x \<in> z \<and> Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))} = 0"
      by auto
    then
    show ?thesis by auto
  qed
  moreover from this
  have "\<forall>x[M]. x \<in> ?y \<longleftrightarrow> x \<in> z \<and> Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))" by simp
  ultimately
  show "\<exists>y[M]. \<forall>x[M]. x \<in> y \<longleftrightarrow> x \<in> z \<and> Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))"
    by blast
qed

lemma Least_in_Pow_rel_Union:
  assumes "\<And>b. P(b) \<Longrightarrow> b \<in> U"
    "M(U)"
  shows "(\<mu> i. P(i)) \<in> Pow\<^bsup>M\<^esup>(\<Union>U)"
  using assms separation_least unfolding Least_def
  by (rule_tac The_in_Pow_rel_Union) simp

lemma bounded_lam_replacement:
  fixes U
  assumes "\<forall>X[M]. \<forall>x\<in>X. f(x) \<in> U(X)"
    and separation_f:"\<forall>A[M]. separation(M,\<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, f(x)\<rangle>)"
    and U_closed [intro,simp]: "\<And>X. M(X) \<Longrightarrow> M(U(X))"
  shows "lam_replacement(M, f)"
proof -
  have "M(\<lambda>x\<in>A. f(x))" if "M(A)" for A
  proof -
    have "(\<lambda>x\<in>A. f(x)) = {y\<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A \<union> U(A))). \<exists>x[M]. x\<in>A \<and> y = \<langle>x, f(x)\<rangle>}"
      using \<open>M(A)\<close> unfolding lam_def
    proof (intro equalityI, auto)
      fix x
      assume "x\<in>A"
      moreover
      note \<open>M(A)\<close>
      moreover from calculation assms
      have "f(x) \<in> U(A)" by simp
      moreover from calculation
      have "{x, f(x)} \<in> Pow\<^bsup>M\<^esup>(A \<union> U(A))" "{x,x} \<in> Pow\<^bsup>M\<^esup>(A \<union> U(A))"
        using Pow_rel_char[of "A \<union> U(A)"] by (auto dest:transM)
      ultimately
      show "\<langle>x, f(x)\<rangle> \<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A \<union> U(A)))"
        using Pow_rel_char[of "Pow\<^bsup>M\<^esup>(A \<union> U(A))"] unfolding Pair_def
        by (auto dest:transM)
    qed
    moreover from \<open>M(A)\<close>
    have "M({y\<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A \<union> U(A))). \<exists>x[M]. x\<in>A \<and> y = \<langle>x, f(x)\<rangle>})"
      using separation_f
      by (rule_tac separation_closed) simp_all
    ultimately
    show ?thesis
      by simp
  qed
  moreover from this
  have "\<forall>x[M]. M(f(x))"
    using lam_closed_imp_closed by simp
  ultimately
  show ?thesis
    using assms
    by (rule_tac lam_replacement_iff_lam_closed[THEN iffD2]) simp_all
qed

lemma lam_replacement_domain':
  assumes "\<forall>A[M]. separation(M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, domain(x)\<rangle>)"
  shows "lam_replacement(M,domain)"
proof -
  have "\<forall>x\<in>X. domain(x) \<in> Pow\<^bsup>M\<^esup>(\<Union>\<Union>\<Union>X)" if "M(X)" for X
  proof
    fix x
    assume "x\<in>X"
    moreover
    note \<open>M(X)\<close>
    moreover from calculation
    have "M(x)" by (auto dest:transM)
    ultimately
    show "domain(x) \<in> Pow\<^bsup>M\<^esup>(\<Union>\<Union>\<Union>X)"
      using mem_Pow_rel_abs[of "domain(x)" "\<Union>\<Union>\<Union>X"]
        (* FIXME: bad taste procedural proof ahead *)
      apply (auto simp:Pair_def)
      apply (rule_tac x=x in bexI)
       apply (rule_tac x="{{xaa}, {xaa, ya}}" in bexI)
        apply (rule_tac x="{xaa}" in bexI)
      by simp_all
  qed
  with assms
  show ?thesis
    using bounded_lam_replacement[of domain "\<lambda>X. Pow\<^bsup>M\<^esup>(\<Union>\<Union>\<Union>X)"] by simp
qed

lemma lam_replacement_fst':
  assumes "\<forall>A[M]. separation(M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, fst(x)\<rangle>)"
  shows "lam_replacement(M,fst)"
proof -
  have "\<forall>x\<in>X. fst(x) \<in> {0} \<union> \<Union>\<Union>X" if "M(X)" for X
  proof
    fix x
    assume "x\<in>X"
    moreover
    note \<open>M(X)\<close>
    moreover from calculation
    have "M(x)" by (auto dest:transM)
    ultimately
    show "fst(x) \<in> {0} \<union> \<Union>\<Union>X" unfolding fst_def Pair_def
      by (auto, rule_tac [1] the_0) force\<comment> \<open>tricky! And slow. It doesn't work for \<^term>\<open>snd\<close>\<close>
  qed
  with assms
  show ?thesis
    using bounded_lam_replacement[of fst "\<lambda>X. {0} \<union> \<Union>\<Union>X"] by simp
qed

lemma lam_replacement_restrict:
assumes "\<forall>A[M]. separation(M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, restrict(x,B)\<rangle>)"  "M(B)"
shows "lam_replacement(M, \<lambda>r . restrict(r,B))"
proof -
  have "\<forall>r\<in>R. restrict(r,B)\<in>Pow\<^bsup>M\<^esup>(\<Union>R)" if "M(R)" for R
  proof -
    {
      fix r
      assume "r\<in>R"
      with \<open>M(B)\<close>
      have "restrict(r,B)\<in>Pow(\<Union>R)" "M(restrict(r,B))"
        using Union_upper subset_Pow_Union subset_trans[OF restrict_subset]
          transM[OF _ \<open>M(R)\<close>]
        by simp_all
    } then show ?thesis
      using Pow_rel_char that by simp
  qed
  with assms
  show ?thesis
    using bounded_lam_replacement[of "\<lambda>r . restrict(r,B)" "\<lambda>X. Pow\<^bsup>M\<^esup>(\<Union>X)"]
    by simp
qed

end (* M_basic *)

locale M_replacement = M_basic +
  assumes
    lam_replacement_domain: "lam_replacement(M,domain)"
    and
    lam_replacement_vimage: "lam_replacement(M, \<lambda>p. fst(p) -`` snd(p))"
    and
    lam_replacement_fst: "lam_replacement(M,fst)"
    and
    lam_replacement_snd: "lam_replacement(M,snd)"
    and
    lam_replacement_Union: "lam_replacement(M,Union)"
    and
    id_separation:"separation(M, \<lambda>z. \<exists>x[M]. z = \<langle>x, x\<rangle>)"
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
    lam_replacement_Upair:"lam_replacement(M, \<lambda>p. Upair(fst(p),snd(p)))"
    and
    lam_replacement_Diff:"lam_replacement(M, \<lambda>p. fst(p) - snd(p))"
    and
    lam_replacement_Image:"lam_replacement(M, \<lambda>p. fst(p) `` snd(p))"
    and
    separation_fst_equal : "M(a) \<Longrightarrow> separation(M,\<lambda>x . fst(x)=a)"
    and
    separation_equal_fst2 : "M(a) \<Longrightarrow> separation(M,\<lambda>x . fst(fst(x))=a)"
    and
    separation_equal_apply: "M(f) \<Longrightarrow> M(a) \<Longrightarrow> separation(M,\<lambda>x. f`x=a)"
    and
    separation_restrict: "M(B) \<Longrightarrow> \<forall>A[M]. separation(M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, restrict(x, B)\<rangle>)"
begin

lemma lam_replacement_imp_strong_replacement:
  assumes "lam_replacement(M, f)"
  shows "strong_replacement(M, \<lambda>x y. y = f(x))"
proof -
  {
    fix A
    assume "M(A)"
    moreover
    from assms
    have "univalent(M,A,\<lambda>x y. y=\<langle>x,f(x)\<rangle>)" by simp
    moreover from calculation assms
    obtain Y where 1:"M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,f(x)\<rangle>)"
      unfolding lam_replacement_def strong_replacement_def
      by auto
    moreover from this
    have "M({snd(b) . b \<in> Y})"
      using transM[OF _ \<open>M(Y)\<close>] lam_replacement_snd lam_replacement_imp_strong_replacement_aux
        RepFun_closed by simp
    moreover
    have "{snd(b) . b \<in> Y} = {y . x\<in>A , M(f(x)) \<and> y=f(x)}" (is "?L=?R")
    proof(intro equalityI subsetI)
      fix x
      assume "x\<in>?L"
      moreover from this
      obtain b where "b\<in>Y" "x=snd(b)" "M(b)"
        using transM[OF _ \<open>M(Y)\<close>] by auto
      moreover from this 1
      obtain a where "a\<in>A" "b=\<langle>a,f(a)\<rangle>" by auto
      moreover from calculation
      have "x=f(a)" by simp
      ultimately show "x\<in>?R"
        by auto
    next
      fix z
      assume "z\<in>?R"
      moreover from this
      obtain a where "a\<in>A" "z=f(a)" "M(a)" "M(f(a))"
        using transM[OF _ \<open>M(A)\<close>]
        by auto
      moreover from calculation this 1
      have "z=snd(\<langle>a,f(a)\<rangle>)" "\<langle>a,f(a)\<rangle> \<in> Y" by auto
      ultimately
      show "z\<in>?L" by force
    qed
    ultimately
    have "\<exists>Z[M]. \<forall>z[M]. z\<in>Z \<longleftrightarrow> (\<exists>a[M]. a\<in>A \<and> z=f(a))"
      by (rule_tac rexI[where x="{snd(b) . b \<in> Y}"],auto)
  }
  then
  show ?thesis unfolding strong_replacement_def by simp
qed

lemma Collect_middle: "{p \<in> (\<lambda>x\<in>A. f(x)) \<times> (\<lambda>x\<in>{f(x) . x\<in>A}. g(x)) . snd(fst(p))=fst(snd(p))}
     = { \<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> . x\<in>A }"
  by (intro equalityI; auto simp:lam_def)

lemma RepFun_middle_del: "{ \<langle>fst(fst(p)),snd(snd(p))\<rangle> . p \<in> { \<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> . x\<in>A }}
        =  { \<langle>x,g(f(x))\<rangle> . x\<in>A }"
  by auto

lemma lam_replacement_imp_RepFun:
  assumes "lam_replacement(M, f)" "M(A)"
  shows "M({y . x\<in>A , M(y) \<and> y=f(x)})"
proof -
  from assms
  have "univalent(M,A,\<lambda>x y. y=\<langle>x,f(x)\<rangle>)" by simp
  moreover from calculation assms
  obtain Y where 1:"M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,f(x)\<rangle>)"
    unfolding lam_replacement_def strong_replacement_def
    by auto
  moreover from this
  have "M({snd(b) . b \<in> Y})"
    using transM[OF _ \<open>M(Y)\<close>] lam_replacement_snd lam_replacement_imp_strong_replacement_aux
      RepFun_closed by simp
  moreover
  have "{snd(b) . b \<in> Y} = {y . x\<in>A , M(y) \<and> y=f(x)}" (is "?L=?R")
  proof(intro equalityI subsetI)
    fix x
    assume "x\<in>?L"
    moreover from this
    obtain b where "b\<in>Y" "x=snd(b)" "M(b)"
      using transM[OF _ \<open>M(Y)\<close>] by auto
    moreover from this 1
    obtain a where "a\<in>A" "b=\<langle>a,f(a)\<rangle>" by auto
    moreover from calculation
    have "x=f(a)" by simp
    ultimately show "x\<in>?R"
      by auto
  next
    fix z
    assume "z\<in>?R"
    moreover from this
    obtain a where "a\<in>A" "z=f(a)" "M(a)" "M(f(a))"
      using transM[OF _ \<open>M(A)\<close>]
      by auto
    moreover from calculation this 1
    have "z=snd(\<langle>a,f(a)\<rangle>)" "\<langle>a,f(a)\<rangle> \<in> Y" by auto
    ultimately
    show "z\<in>?L" by force
  qed
  ultimately
  show ?thesis by simp
qed

lemma lam_replacement_pullback:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
  shows "lam_replacement(M, \<lambda>x. \<langle>f(x),g(x)\<rangle>)"
proof -
  {
    fix A
    let ?Y="{y . x\<in>A , M(y) \<and> y=f(x)}"
    let ?Y'="{y . x\<in>A ,M(y) \<and>  y=\<langle>x,f(x)\<rangle>}"
    let ?Z="{y . x\<in>A , M(y) \<and> y=g(x)}"
    let ?Z'="{y . x\<in>A ,M(y) \<and>  y=\<langle>x,g(x)\<rangle>}"
    have "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> fst(x) = fst(y) \<longrightarrow> M(fst(y)) \<and> M(snd(x)) \<and> M(snd(y))" if "M(C)" for C y x
      using transM[OF _ that] by auto
    moreover
    note assms
    moreover
    assume "M(A)"
    moreover from \<open>M(A)\<close> assms(1)
    have "M(?Y')" "M(?Y)"
      using lam_replacement_imp_RepFun_Lam lam_replacement_imp_RepFun by auto
    moreover from calculation
    have "M(?Z)" "M(?Z')"
      using lam_replacement_imp_RepFun_Lam lam_replacement_imp_RepFun by auto
    moreover from calculation
    have "M(?Y'\<times>?Z')"
      by simp
    moreover from this
    have "M({p \<in> ?Y'\<times>?Z' . fst(fst(p))=fst(snd(p))})" (is "M(?P)")
      using pullback_separation by simp
    moreover from calculation
    have "M({ \<langle>fst(fst(p)),\<langle>snd(fst(p)),snd(snd(p))\<rangle>\<rangle> . p\<in>?P })" (is "M(?R)")
      using RepFun_closed[OF pullback_replacement \<open>M(?P)\<close> ] by simp
    ultimately
    have "b \<in> ?R \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,\<langle>f(x),g(x)\<rangle>\<rangle>)" if "M(b)" for b
      using that
      apply(intro iffI)apply(auto)[1]
    proof -
      assume " \<exists>x[M]. x \<in> A \<and> b = \<langle>x, f(x), g(x)\<rangle>"
      moreover from this
      obtain x where "M(x)" "x\<in>A" "b= \<langle>x, \<langle>f(x), g(x)\<rangle>\<rangle>"
        by auto
      moreover from calculation that
      have "M(\<langle>x,f(x)\<rangle>)" "M(\<langle>x,g(x)\<rangle>)" by auto
      moreover from calculation
      have "\<langle>x,f(x)\<rangle> \<in> ?Y'" "\<langle>x,g(x)\<rangle> \<in> ?Z'" by auto
      moreover from calculation
      have "\<langle>\<langle>x,f(x)\<rangle>,\<langle>x,g(x)\<rangle>\<rangle>\<in>?Y'\<times>?Z'" by auto
      moreover from calculation
      have "\<langle>\<langle>x,f(x)\<rangle>,\<langle>x,g(x)\<rangle>\<rangle> \<in> ?P"
        (is "?p\<in>?P")
        by auto
      moreover from calculation
      have "b = \<langle>fst(fst(?p)),\<langle>snd(fst(?p)),snd(snd(?p))\<rangle>\<rangle>" by auto
      moreover from calculation
      have "\<langle>fst(fst(?p)),\<langle>snd(fst(?p)),snd(snd(?p))\<rangle>\<rangle>\<in>?R"
        by(rule_tac RepFunI[of ?p ?P], simp)
      ultimately show "b\<in>?R" by simp
    qed
    with \<open>M(?R)\<close>
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,\<langle>f(x),g(x)\<rangle>\<rangle>)"
      by (rule_tac rexI[where x="?R"],simp_all)
  }
  with assms
  show ?thesis using lam_replacement_def strong_replacement_def by simp
qed

lemma lam_replacement_hcomp:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)" "\<forall>x[M]. M(f(x))"
  shows "lam_replacement(M, \<lambda>x. g(f(x)))"
proof -
  {
    fix A
    let ?Y="{y . x\<in>A , y=f(x)}"
    let ?Y'="{y . x\<in>A , y=\<langle>x,f(x)\<rangle>}"
    have "\<forall>x\<in>C. M(\<langle>fst(fst(x)),snd(snd(x))\<rangle>)" if "M(C)" for C
      using transM[OF _ that] by auto
    moreover
    note assms
    moreover
    assume "M(A)"
    moreover from assms
    have eq:"?Y = {y . x\<in>A ,M(y) \<and> y=f(x)}"  "?Y' = {y . x\<in>A ,M(y) \<and> y=\<langle>x,f(x)\<rangle>}"
      using transM[OF _ \<open>M(A)\<close>] by auto
    moreover from \<open>M(A)\<close> assms(1)
    have "M(?Y')" "M(?Y)"
      using lam_replacement_imp_RepFun_Lam lam_replacement_imp_RepFun eq by auto
    moreover from calculation
    have "M({z . y\<in>?Y , M(z) \<and> z=\<langle>y,g(y)\<rangle>})" (is "M(?Z)")
      using lam_replacement_imp_RepFun_Lam by auto
    moreover from calculation
    have "M(?Y'\<times>?Z)"
      by simp
    moreover from this
    have "M({p \<in> ?Y'\<times>?Z . snd(fst(p))=fst(snd(p))})" (is "M(?P)")
      using middle_separation by simp
    moreover from calculation
    have "M({ \<langle>fst(fst(p)),snd(snd(p))\<rangle> . p\<in>?P })" (is "M(?R)")
      using RepFun_closed[OF middle_del_replacement \<open>M(?P)\<close>] by simp
    ultimately
    have "b \<in> ?R \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,g(f(x))\<rangle>)" if "M(b)" for b
      using that assms(3)
      apply(intro iffI) apply(auto)[1]
    proof -
      assume "\<exists>x[M]. x \<in> A \<and> b = \<langle>x, g(f(x))\<rangle>"
      moreover from this
      obtain x where "M(x)" "x\<in>A" "b= \<langle>x, g(f(x))\<rangle>"
        by auto
      moreover from calculation that assms(3)
      have "M(f(x))" "M(g(f(x)))" by auto
      moreover from calculation
      have "\<langle>x,f(x)\<rangle> \<in> ?Y'" by auto
      moreover from calculation
      have "\<langle>f(x),g(f(x))\<rangle>\<in>?Z" by auto
      moreover from calculation
      have "\<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> \<in> ?P"
        (is "?p\<in>?P")
        by auto
      moreover from calculation
      have "b = \<langle>fst(fst(?p)),snd(snd(?p))\<rangle>" by auto
      moreover from calculation
      have "\<langle>fst(fst(?p)),snd(snd(?p))\<rangle>\<in>?R"
        by(rule_tac RepFunI[of ?p ?P], simp)
      ultimately show "b\<in>?R" by simp
    qed
    with \<open>M(?R)\<close>
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,g(f(x))\<rangle>)"
      by (rule_tac rexI[where x="?R"],simp_all)
  }
  with assms
  show ?thesis using lam_replacement_def strong_replacement_def by simp
qed

lemma lam_replacement_Collect :
  assumes "M(A)" "\<forall>x[M]. separation(M,F(x))"
    "separation(M,\<lambda>p . \<forall>x\<in>A. x\<in>snd(p) \<longleftrightarrow> F(fst(p),x))"
  shows "lam_replacement(M,\<lambda>x. {y\<in>A . F(x,y)})"
proof -
  {
    fix Z
    let ?Y="\<lambda>z.{x\<in>A . F(z,x)}"
    assume "M(Z)"
    moreover from this
    have "M(?Y(z))" if "z\<in>Z" for z
      using assms that transM[of _ Z] by simp
    moreover from this
    have "?Y(z)\<in>Pow\<^bsup>M\<^esup>(A)" if "z\<in>Z" for z
      using Pow_rel_char that assms by auto
    moreover from calculation \<open>M(A)\<close>
    have "M(Z\<times>Pow\<^bsup>M\<^esup>(A))" by simp
    moreover from this
    have "M({p \<in> Z\<times>Pow\<^bsup>M\<^esup>(A) . \<forall>x\<in>A. x\<in>snd(p) \<longleftrightarrow> F(fst(p),x)})" (is "M(?P)")
      using assms by simp
    ultimately
    have "b \<in> ?P \<longleftrightarrow> (\<exists>z[M]. z\<in>Z \<and> b=\<langle>z,?Y(z)\<rangle>)" if "M(b)" for b
      using  assms(1) Pow_rel_char[OF \<open>M(A)\<close>] that
      by(intro iffI,auto,intro equalityI,auto)
    with \<open>M(?P)\<close>
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>z[M]. z \<in> Z \<and> b = \<langle>z,?Y(z)\<rangle>)"
      by (rule_tac rexI[where x="?P"],simp_all)
  }
  then
  show ?thesis
    unfolding lam_replacement_def strong_replacement_def
    by simp
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

lemma strong_replacement_separation_aux :
  assumes "strong_replacement(M,\<lambda> x y . y=f(x))" "separation(M,P)"
  shows "strong_replacement(M, \<lambda>x y . P(x) \<and> y=f(x))"
proof -
  {
    fix A
    let ?Q="\<lambda>X. \<forall>b[M]. b \<in> X \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> P(x) \<and> b = f(x))"
    assume "M(A)"
    moreover from this
    have "M({x\<in>A . P(x)})" (is "M(?B)") using assms by simp
    moreover from calculation assms
    obtain Y where "M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> ?B \<and> b = f(x))"
      unfolding strong_replacement_def by auto
    then
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> P(x) \<and> b = f(x))"
      using rexI[of ?Q _ M] by simp
  }
  then
  show ?thesis
    unfolding strong_replacement_def by simp
qed

lemma lam_replacement_separation :
  assumes "lam_replacement(M,f)" "separation(M,P)"
  shows "strong_replacement(M, \<lambda>x y . P(x) \<and> y=\<langle>x,f(x)\<rangle>)"
  using strong_replacement_separation_aux assms
  unfolding lam_replacement_def
  by simp

lemmas strong_replacement_separation =
  strong_replacement_separation_aux[OF lam_replacement_imp_strong_replacement]

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
    assume "M(A)"
    moreover from this
    have "id(A) = {z\<in> A\<times>A. \<exists>x[M]. z=\<langle>x,x\<rangle>}"
      unfolding id_def lam_def by (auto dest:transM)
    moreover from calculation
    have "M({z\<in> A\<times>A. \<exists>x[M]. z=\<langle>x,x\<rangle>})"
      using id_separation by simp
    ultimately
    have "M(id(A))" by simp
  }
  then
  show ?thesis using lam_replacement_iff_lam_closed
    unfolding id_def by simp
qed

lemma lam_replacement_Un: "lam_replacement(M, \<lambda>p. fst(p) \<union> snd(p))"
  using lam_replacement_Upair lam_replacement_Union
    lam_replacement_hcomp[where g=Union and f="\<lambda>p. Upair(fst(p),snd(p))"]
  unfolding Un_def by simp

lemma lam_replacement_cons: "lam_replacement(M, \<lambda>p. cons(fst(p),snd(p)))"
  using  lam_replacement_Upair
    lam_replacement_hcomp2[of _ _ "(\<union>)"]
    lam_replacement_hcomp2[of fst fst "Upair"]
    lam_replacement_Un lam_replacement_fst lam_replacement_snd
   unfolding cons_def
  by auto

lemma lam_replacement_constant: "M(b) \<Longrightarrow> lam_replacement(M,\<lambda>_. b)"
  unfolding lam_replacement_def strong_replacement_def
  by safe (rule_tac x="_\<times>{b}" in rexI; blast)

lemma lam_replacement_sing: "lam_replacement(M, \<lambda>x. {x})"
  using lam_replacement_constant lam_replacement_cons
    lam_replacement_hcomp2[of "\<lambda>x. x" "\<lambda>_. 0" cons]
  by (force intro: lam_replacement_identity)

lemmas tag_replacement = lam_replacement_constant[unfolded lam_replacement_def]

lemma lam_replacement_id2: "lam_replacement(M, \<lambda>x. \<langle>x, x\<rangle>)"
  using lam_replacement_identity lam_replacement_pullback[of "\<lambda>x. x" "\<lambda>x. x"]
  by simp

lemmas id_replacement = lam_replacement_id2[unfolded lam_replacement_def]

lemma lam_replacement_apply2:"lam_replacement(M, \<lambda>p. fst(p) ` snd(p))"
  using lam_replacement_sing lam_replacement_fst lam_replacement_snd
    lam_replacement_Image lam_replacement_Union
  unfolding apply_def
  by (rule_tac lam_replacement_hcomp[of _ Union],
      rule_tac lam_replacement_hcomp2[of _ _ "(``)"])
         (force intro:lam_replacement_hcomp)+

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

lemmas apply_replacement2 = lam_replacement_apply_const_id[unfolded lam_replacement_def]

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

lemma lam_replacement_vimage_sing: "lam_replacement(M, \<lambda>p. fst(p) -`` {snd(p)})"
  using lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_sing]
    lam_replacement_hcomp2[OF lam_replacement_fst  _ _ _ lam_replacement_vimage]
  by simp

lemma lam_replacement_vimage_sing_fun: "M(f) \<Longrightarrow> lam_replacement(M, \<lambda>x. f -`` {x})"
  using lam_replacement_hcomp2[OF lam_replacement_constant[of f]
          lam_replacement_identity _ _ lam_replacement_vimage_sing]
  by simp

lemma converse_apply_projs: "\<forall>x[M]. \<Union> (fst(x) -`` {snd(x)}) = converse(fst(x)) ` (snd(x))"
  using converse_apply_eq by auto

lemma lam_replacement_converse_app: "lam_replacement(M, \<lambda>p. converse(fst(p)) ` snd(p))"
  using lam_replacement_cong[OF _ converse_apply_projs]
    lam_replacement_hcomp[OF lam_replacement_vimage_sing lam_replacement_Union]
  by simp

lemmas cardinal_lib_assms4 = lam_replacement_vimage_sing_fun[unfolded lam_replacement_def]

lemma lam_replacement_surj_imp_inj1:
  "M(x) \<Longrightarrow> lam_replacement(M, \<lambda>y. {\<langle>x, y\<rangle>})"
  using lam_replacement_cons lam_replacement_constant
  by (rule_tac lam_replacement_hcomp2[of _ _ cons], simp_all)
    (fast intro: lam_replacement_hcomp lam_replacement_pullback lam_replacement_identity)

lemma tag_singleton_closed: "M(x) \<Longrightarrow> M(z) \<Longrightarrow> M({{\<langle>z, y\<rangle>} . y \<in> x})"
  using RepFun_closed[where A=x and f="\<lambda> u. {\<langle>z,u\<rangle>}"]
    lam_replacement_imp_strong_replacement
    lam_replacement_hcomp[OF lam_replacement_const_id lam_replacement_sing]
    transM[of _ x]
  by simp
end (* M_replacement *)

locale M_replacement_extra = M_replacement +
  assumes
    lam_replacement_minimum:"lam_replacement(M, \<lambda>p. minimum(fst(p),snd(p)))"
    and
    lam_replacement_RepFun_cons:"lam_replacement(M, \<lambda>p. RepFun(fst(p), \<lambda>x. {\<langle>snd(p),x\<rangle>}))"
    \<comment> \<open>This one is too particular: It is for \<^term>\<open>Sigfun\<close>.
        I would like greater modularity here.\<close>

begin
lemma lam_replacement_Sigfun:
  assumes "lam_replacement(M,f)" "\<forall>y[M]. M(f(y))"
  shows "lam_replacement(M, \<lambda>x. Sigfun(x,f))"
  using lam_replacement_Union lam_replacement_identity
    lam_replacement_sing[THEN lam_replacement_imp_strong_replacement]
  unfolding Sigfun_def
  apply (rule_tac lam_replacement_hcomp[of _ Union],simp_all)
   apply (rule lam_replacement_RepFun_cons[THEN [5] lam_replacement_hcomp2])
       apply(simp_all add:assms)
  using assms tag_singleton_closed
  by (simp_all)

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

subsection\<open>Particular instances\<close>

\<comment> \<open>The following instance is unnecessarily complicated, since it follows from
@{thm lam_replacement_surj_imp_inj1}\<close>
lemma surj_imp_inj_replacement1:
  "M(f) \<Longrightarrow> M(x) \<Longrightarrow> strong_replacement(M, \<lambda>y z. y \<in> f -`` {x} \<and> z = {\<langle>x, y\<rangle>})"
  using lam_replacement_imp_strong_replacement
  using lam_replacement_surj_imp_inj1[THEN lam_replacement_imp_strong_replacement, of x]
  unfolding strong_replacement_def
  by (simp, safe, drule_tac x="A \<inter> f -`` {x}" in rspec,
      simp, erule_tac rexE, rule_tac x=Y in rexI) auto

lemma surj_imp_inj_replacement2:
  "M(f) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = Sigfun(x, \<lambda>y. f -`` {y}))"
  using lam_replacement_imp_strong_replacement lam_replacement_Sigfun
    lam_replacement_vimage_sing_fun
  by simp

lemma lam_replacement_minimum_vimage:
  "M(f) \<Longrightarrow> M(r) \<Longrightarrow> lam_replacement(M, \<lambda>x. minimum(r, f -`` {x}))"
  using lam_replacement_minimum lam_replacement_vimage_sing_fun lam_replacement_constant
  by (rule_tac lam_replacement_hcomp2[of _ _ minimum])
    (force intro: lam_replacement_identity)+

lemmas surj_imp_inj_replacement4 = lam_replacement_minimum_vimage[unfolded lam_replacement_def]

lemmas domain_replacement =  lam_replacement_domain[unfolded lam_replacement_def]

lemma domain_replacement_simp: "strong_replacement(M, \<lambda>x y. y=domain(x))"
  using lam_replacement_domain lam_replacement_imp_strong_replacement by simp

lemma un_Pair_replacement: "M(p) \<Longrightarrow> strong_replacement(M, \<lambda>x y . y = x\<union>{p})"
  using lam_replacement_Un_const[THEN lam_replacement_imp_strong_replacement] by simp

lemma restrict_strong_replacement: "M(A) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y=restrict(x,A))"
  using lam_replacement_restrict separation_restrict
    lam_replacement_imp_strong_replacement
  by simp

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

lemma lam_replacement_hcomp_Least:
  assumes "lam_replacement(M, g)" "lam_replacement(M,\<lambda>x. \<mu> i. x\<in>F(i,x))"
    "\<forall>x[M]. M(g(x))" "\<And>x i. M(x) \<Longrightarrow> i \<in> F(i, x) \<Longrightarrow> M(i)"
  shows "lam_replacement(M,\<lambda>x. \<mu> i. g(x)\<in>F(i,g(x)))"
  using assms
  by (rule_tac lam_replacement_hcomp[of _ "\<lambda>x. \<mu> i. x\<in>F(i,x)"])
      (auto intro:Least_closed')

end (* M_replacement *)

\<comment> \<open>To be used in the relativized treatment of Cohen posets\<close>
definition
  \<comment> \<open>"domain collect F"\<close>
  dC_F :: "i \<Rightarrow> i \<Rightarrow> i" where
  "dC_F(A,d) \<equiv> {p \<in> A. domain(p) = d }"

definition
  \<comment> \<open>"domain restrict SepReplace Y"\<close>
  drSR_Y :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "drSR_Y(r',D,A,x) \<equiv> {domain(p) .. p\<in>A, restrict(p,r') = x \<and> domain(p) \<in> D}"


context M_replacement_extra
begin

lemma lam_if_then_apply_replacement: "M(f) \<Longrightarrow> M(v) \<Longrightarrow> M(u) \<Longrightarrow>
     lam_replacement(M, \<lambda>x. if f ` x = v then f ` u else f ` x)"
  using lam_replacement_if separation_equal_apply lam_replacement_constant lam_replacement_apply
  by simp

lemma  lam_if_then_apply_replacement2: "M(f) \<Longrightarrow> M(m) \<Longrightarrow> M(y) \<Longrightarrow>
     lam_replacement(M, \<lambda>z . if f ` z = m then y else f ` z)"
  using lam_replacement_if separation_equal_apply lam_replacement_constant lam_replacement_apply
  by simp

lemma lam_if_then_replacement2: "M(A) \<Longrightarrow> M(f) \<Longrightarrow>
     lam_replacement(M, \<lambda>x . if x \<in> A then f ` x else x)"
  using lam_replacement_if separation_in lam_replacement_identity lam_replacement_apply
  by simp

lemma lam_if_then_replacement_apply: "M(G) \<Longrightarrow> lam_replacement(M, \<lambda>x. if M(x) then G ` x else 0)"
  using lam_replacement_if separation_in lam_replacement_identity lam_replacement_apply
    lam_replacement_constant[of 0] separation_univ
  by simp

lemma lam_replacement_dC_F:
  assumes "M(A)"
    "\<And>d . M(d) \<Longrightarrow> separation(M, \<lambda>x . domain(x) = d)"
    "\<And> A . M(A) \<Longrightarrow> separation(M, \<lambda>p. \<forall>x\<in>A. x \<in> snd(p) \<longleftrightarrow> domain(x) = fst(p))"
  shows "lam_replacement(M, dC_F(A))"
  unfolding dC_F_def
  using assms lam_replacement_Collect[of A "\<lambda> d x . domain(x) = d"]
  by simp

lemmas replacements = Pair_diff_replacement id_replacement tag_replacement
  pospend_replacement prepend_replacement
  Inl_replacement1  diff_Pair_replacement
  swap_replacement tag_union_replacement csquare_lam_replacement
  assoc_replacement prod_fun_replacement
  cardinal_lib_assms4  domain_replacement
  apply_replacement
  un_Pair_replacement restrict_strong_replacement diff_replacement
  if_then_Inj_replacement lam_if_then_replacement if_then_replacement
  ifx_replacement if_then_range_replacement2 if_then_range_replacement
  Inl_replacement2
  case_replacement1 case_replacement2 case_replacement4 case_replacement5

end (* M_replacement_extra *)

(*find_theorems
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
  -name:sum_bij_rel_replacement -name:replacements
*)

end