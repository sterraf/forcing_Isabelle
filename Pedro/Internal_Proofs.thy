theory Internal_Proofs
  imports
    "../src/Relativization"
    "../Tools/Try0"
begin
\<comment> \<open>NOTE: This theory is a playground.\<close>
(* setup "Config.put_global Blast.trace true" *)

(* MOVE THIS. absoluteness of higher-order composition *)
definition
  Comp :: "[i\<Rightarrow>i,i\<Rightarrow>i] \<Rightarrow> i \<Rightarrow> i" (infixr \<open>\<circ>\<close> 60)  where
  "(g \<circ> f)(x) \<equiv> g(f(x))"

definition
  is_hcomp :: "[i\<Rightarrow>o,(i\<Rightarrow>o) \<Rightarrow>i\<Rightarrow>i\<Rightarrow>o,(i\<Rightarrow>o) \<Rightarrow>i\<Rightarrow>i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_hcomp(M,is_f,is_g,a,w) \<equiv> \<exists>z[M]. is_g(M,a,z) \<and> is_f(M,z,w)"

lemma (in M_trivial) hcomp_abs:
  assumes
    is_f_abs:"\<And>a z. M(a) \<Longrightarrow> M(z) \<Longrightarrow> is_f(M,a,z) \<longleftrightarrow> z = f(a)" and
    is_g_abs:"\<And>a z. M(a) \<Longrightarrow> M(z) \<Longrightarrow> is_g(M,a,z) \<longleftrightarrow> z = g(a)" and
    g_closed:"\<And>a. M(a) \<Longrightarrow> M(f(a))"
    "M(a)" "M(w)"
  shows
    "is_hcomp(M,is_g,is_f,a,w) \<longleftrightarrow> w = (g \<circ> f)(a)"
  unfolding is_hcomp_def Comp_def  using assms by simp
definition
  hcomp_fm :: "[i\<Rightarrow>i\<Rightarrow>i,i\<Rightarrow>i\<Rightarrow>i,i,i] \<Rightarrow> i" where
  "hcomp_fm(pf,pg,a,w) \<equiv> Exists(And(pg(succ(a),0),pf(0,succ(w))))"

lemma sats_hcomp_fm:
  assumes
    f_iff_sats:"\<And>a b z. a\<in>nat \<Longrightarrow> b\<in>nat \<Longrightarrow> z\<in>M \<Longrightarrow>
                 is_f(##M,nth(a,Cons(z,env)),nth(b,Cons(z,env))) \<longleftrightarrow> sats(M,pf(a,b),Cons(z,env))"
    and
    g_iff_sats:"\<And>a b z. a\<in>nat \<Longrightarrow> b\<in>nat \<Longrightarrow> z\<in>M \<Longrightarrow>
                is_g(##M,nth(a,Cons(z,env)),nth(b,Cons(z,env))) \<longleftrightarrow> sats(M,pg(a,b),Cons(z,env))"
    and
    "a\<in>nat" "w\<in>nat" "env\<in>list(M)"
  shows
    "sats(M,hcomp_fm(pf,pg,a,w),env) \<longleftrightarrow> is_hcomp(##M,is_f,is_g,nth(a,env),nth(w,env))"
proof -
  have "sats(M, pf(0, succ(w)), Cons(x, env)) \<longleftrightarrow> is_f(##M,x,nth(w,env))" if "x\<in>M" "w\<in>nat" for x w
    using f_iff_sats[of 0 "succ(w)" x] that by simp
  moreover
  have "sats(M, pg(succ(a), 0), Cons(x, env)) \<longleftrightarrow> is_g(##M,nth(a,env),x)" if "x\<in>M" "a\<in>nat" for x a
    using g_iff_sats[of "succ(a)" 0 x] that by simp
  ultimately
  show ?thesis unfolding hcomp_fm_def is_hcomp_def using assms by simp
qed


context M_basic
begin

definition
  is_Pow :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_Pow(N,A,z) \<equiv> \<forall>x[N]. x \<in> z \<longleftrightarrow> subset(N,x,A)"

reldb_add "Pow" "is_Pow"

definition Pow2 :: "i \<Rightarrow> i" where
  "Pow2(x) \<equiv> Pow(Pow(x))"

relativize "Pow2" "is_Pow2"


(****************************************************************)
subsection\<open>"Discipline" for \<^term>\<open>Pow\<close>\<close>

lemma extensionality_trans: \<comment> \<open>General preliminary result\<close>
  assumes
    "M(d)" "M(d')"
    "\<forall>x[M]. x\<in>d  \<longleftrightarrow> P(x)"
    "\<forall>x[M]. x\<in>d' \<longleftrightarrow> P(x)"
  shows
    "d=d'"
proof -
  from assms
  have "\<forall>x. x\<in>d \<longleftrightarrow> P(x) \<and> M(x)"
    using transM[of _ d, OF _ \<open>M(d)\<close>] by auto
  moreover from assms
  have  "\<forall>x. x\<in>d' \<longleftrightarrow> P(x) \<and> M(x)"
    using transM[of _ d', OF _ \<open>M(d')\<close>] by auto
  ultimately
  show ?thesis by auto
qed

lemma is_Pow_uniqueness:
  assumes
    "M(r)" "M(d)" "M(d')"
    "is_Pow(M,r,d)" "is_Pow(M,r,d')"
  shows
    "d=d'"
  using assms
    extensionality_trans[where P="\<lambda>x. subset(M, x, r)"]
  unfolding is_Pow_def
  by force

lemma is_Pow_witness: "M(r) \<Longrightarrow> \<exists>d[M]. is_Pow(M,r,d)"
  using power_ax unfolding power_ax_def powerset_def is_Pow_def
  by simp \<comment> \<open>We have to do this by hand, using axioms\<close>

definition
  Pow_rel :: "i \<Rightarrow> i" where
  "Pow_rel(r) \<equiv> THE d. M(d) \<and> is_Pow(M,r,d)"

lemma Pow_rel_closed: "M(r) \<Longrightarrow> M(Pow_rel(r))"
  unfolding Pow_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Pow(M,r,d)"], OF _ is_Pow_uniqueness[of r]]
    is_Pow_witness by auto

lemma Pow_rel_iff:
  assumes "M(r)"  "M(d)"
  shows "is_Pow(M,r,d) \<longleftrightarrow> d = Pow_rel(r)"
proof (intro iffI)
  assume "d = Pow_rel(r)"
  with assms
  show "is_Pow(M, r, d)"
    using is_Pow_uniqueness[of r] is_Pow_witness
    theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Pow(M,r,d)"], OF _ is_Pow_uniqueness[of r]]
    unfolding Pow_rel_def
    by auto
next
  assume "is_Pow(M, r, d)"
  with assms
  show "d = Pow_rel(r)"
    using is_Pow_uniqueness unfolding Pow_rel_def
    by (auto del:the_equality intro:the_equality[symmetric])
qed


(****************************************************************)

section\<open>Discipline for \<^term>\<open>Pow2\<close>\<close>

lemma hcomp_uniqueness: \<comment> \<open>General preliminary result\<close>
  assumes
    uniq_is_f: "\<And>r d d'. M(r) \<Longrightarrow> M(d) \<Longrightarrow> M(d') \<Longrightarrow> is_f(M, r, d) \<Longrightarrow> is_f(M, r, d') \<Longrightarrow> d = d'" and
    uniq_is_g: "\<And>r d d'. M(r) \<Longrightarrow> M(d) \<Longrightarrow> M(d') \<Longrightarrow> is_g(M, r, d) \<Longrightarrow> is_g(M, r, d') \<Longrightarrow> d = d'" and
    "M(a)" "M(w)" "M(w')"
    "is_hcomp(M,is_f,is_g,a,w)"
    "is_hcomp(M,is_f,is_g,a,w')"
  shows
    "w=w'"
proof -
  from assms
  obtain z z' where "is_g(M, a, z)" "is_g(M, a, z')"
    "is_f(M,z,w)" "is_f(M,z',w')"
    "M(z)" "M(z')"
    unfolding is_hcomp_def by blast
  moreover from this and uniq_is_g and \<open>M(a)\<close>
  have "z=z'" by blast
  moreover note uniq_is_f and \<open>M(w)\<close> \<open>M(w')\<close>
  ultimately
  show ?thesis by blast
qed

lemma hcomp_witness: \<comment> \<open>General preliminary result\<close>
  assumes
    wit_is_f: "\<And>r. M(r) \<Longrightarrow> \<exists>d[M]. is_f(M,r,d)" and
    wit_is_g: "\<And>r. M(r) \<Longrightarrow> \<exists>d[M]. is_g(M,r,d)" and
    "M(a)"
  shows
    "\<exists>w[M]. is_hcomp(M,is_f,is_g,a,w)"
proof -
  from \<open>M(a)\<close> and wit_is_g
  obtain z where "is_g(M,a,z)" "M(z)" by blast
  moreover from this and wit_is_f
  obtain w where "is_f(M,z,w)" "M(w)" by blast
  ultimately
  show ?thesis
    using assms unfolding is_hcomp_def by auto
qed

lemma is_Pow2_uniqueness:
  assumes
    "M(r)" "M(d)" "M(d')"
    "is_Pow2(M,r,d)" "is_Pow2(M,r,d')"
  shows
    "d=d'"
  using assms hcomp_uniqueness[where is_f=is_Pow and is_g=is_Pow]
    is_Pow_uniqueness
  unfolding is_Pow2_def is_hcomp_def
  by blast

lemma is_Pow2_witness: "M(r) \<Longrightarrow> \<exists>d[M]. is_Pow2(M,r,d)"
  using hcomp_witness[where is_f=is_Pow and is_g=is_Pow]
    is_Pow_witness
  unfolding is_Pow2_def is_hcomp_def by blast

definition
  Pow2_rel :: "i \<Rightarrow> i" where
  "Pow2_rel(r) \<equiv> THE d. M(d) \<and> is_Pow2(M,r,d)"

lemma Pow2_rel_closed: "M(r) \<Longrightarrow> M(Pow2_rel(r))"
  unfolding Pow2_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Pow2(M,r,d)"], OF _ is_Pow2_uniqueness[of r]]
    is_Pow2_witness by auto

lemma Pow2_rel_iff:
  assumes "M(r)"  "M(d)"
  shows "is_Pow2(M,r,d) \<longleftrightarrow> d = Pow2_rel(r)"
proof (intro iffI)
  assume "d = Pow2_rel(r)"
  with assms
  show "is_Pow2(M, r, d)"
    using is_Pow2_uniqueness[of r] is_Pow2_witness
    theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Pow2(M,r,d)"], OF _ is_Pow2_uniqueness[of r]]
    unfolding Pow2_rel_def
    by auto
next
  assume "is_Pow2(M, r, d)"
  with assms
  show "d = Pow2_rel(r)"
    using is_Pow2_uniqueness unfolding Pow2_rel_def
    by (auto del:the_equality intro:the_equality[symmetric])
qed

lemma def_Pow2_rel:
  assumes "M(x)"
  shows "Pow2_rel(x) = (Pow_rel \<circ> Pow_rel)(x)"
  using assms Pow2_rel_iff Pow_rel_closed Pow2_rel_closed
    hcomp_abs[of "is_Pow" Pow_rel "is_Pow" Pow_rel]
    Pow_rel_iff 
  unfolding is_Pow2_def Comp_def is_hcomp_def by auto

(****************************************************************)

declare
  pair_abs[simp del] pair_in_M_iff[simp del]
  pair_in_MD[rule del] pair_in_MI[rule del]
  domain_abs[simp del] domain_closed[simp del, rule del]
  converse_abs[simp del] converse_closed[simp del, rule del]
  range_abs[simp del] range_closed[simp del, rule del]

lemma univalent_is_domain:
  assumes
    "M(r)" "M(d)" "M(d')"
    "is_domain(M,r,d)" "is_domain(M,r,d')"
  shows
    "d=d'"
  using assms
    extensionality_trans[where P="\<lambda>x. \<exists>w[M]. w \<in> r \<and> (\<exists>y[M]. pair(M, x, y, w))"]
  unfolding is_domain_def
  by force

lemma is_domain_witness: "M(r) \<Longrightarrow> \<exists>d[M]. is_domain(M,r,d)"
  by (simp add: domain_abs domain_closed) \<comment> \<open>not the proof we want\<close>

definition
  domain_rel :: "i \<Rightarrow> i" where
  "domain_rel(r) \<equiv> THE d. M(d) \<and> is_domain(M,r,d)"

lemma domain_rel_iff:
  assumes "M(r)"  "M(d)"
  shows "is_domain(M,r,d) \<longleftrightarrow> d = domain_rel(r)"
proof (intro iffI)
  assume "d = domain_rel(r)"
  with assms
  show "is_domain(M, r, d)"
    using univalent_is_domain[of r] is_domain_witness
    theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_domain(M,r,d)"], OF _ univalent_is_domain[of r]]
    unfolding domain_rel_def
    by auto
next
  assume "is_domain(M, r, d)"
  with assms
  show "d = domain_rel(r)"
    using univalent_is_domain unfolding domain_rel_def
    by (auto del:the_equality intro:the_equality[symmetric])
qed

lemma domain_rel_closed: "M(r) \<Longrightarrow> M(domain_rel(r))"
  sorry

definition \<comment> \<open>not the one we want\<close>
  pair_rel :: "i\<Rightarrow>i\<Rightarrow>i" where
  "pair_rel(a,b) \<equiv> \<langle>a,b\<rangle>"

lemma pair_rel_closed: "M(a) \<Longrightarrow> M(b) \<Longrightarrow> M(pair_rel(a,b))"
  unfolding pair_rel_def
  by (simp add:pair_in_M_iff) \<comment> \<open>not the proof we want\<close>

lemma pair_rel_iff: "M(a) \<Longrightarrow> M(b) \<Longrightarrow> M(ab) \<Longrightarrow> pair(M,a,b,ab) \<longleftrightarrow> ab = pair_rel(a,b)"
  unfolding pair_rel_def
  by (simp add:pair_abs) \<comment> \<open>not the proof we want\<close>

definition \<comment> \<open>not the one we want\<close>
  converse_rel :: "i\<Rightarrow>i" where
  "converse_rel(a) \<equiv> converse(a)"

lemma converse_rel_closed: "M(a) \<Longrightarrow> M(converse_rel(a))"
  unfolding converse_rel_def
  by (simp add:converse_closed) \<comment> \<open>not the proof we want\<close>

lemma converse_rel_iff: "M(a) \<Longrightarrow> M(ab) \<Longrightarrow> is_converse(M,a,ab) \<longleftrightarrow> ab = converse_rel(a)"
  unfolding converse_rel_def
  by (simp add:converse_abs) \<comment> \<open>not the proof we want\<close>

(* \<langle>?a, ?b\<rangle> \<in> ?r \<Longrightarrow> ?a \<in> domain(?r) *)
lemma domain_relI [intro]:
  assumes  "pair_rel(a,b) \<in> r" "M(a)" "M(b)" "M(r)"
    \<comment> \<open>New typing assumptions go last\<close>
  shows "a \<in> domain_rel(r)"
  sorry \<comment> \<open>It won't work, \<^term>\<open>domain\<close> is a \<^term>\<open>Replace\<close>\<close>

definition \<comment> \<open>Is it the one we want?\<close>
  range_rel :: "i\<Rightarrow>i" where
  "range_rel(r) \<equiv> domain_rel(converse_rel(r))"

lemma range_rel_closed: "M(a) \<Longrightarrow> M(range_rel(a))"
  unfolding range_rel_def
  sorry

lemma range_rel_iff: "M(a) \<Longrightarrow> M(ab) \<Longrightarrow> is_range(M,a,ab) \<longleftrightarrow> ab = range_rel(a)"
  unfolding range_rel_def
  sorry

lemma converse_relI [intro!]:
  assumes "M(a)" "M(b)" "M(r)"
  shows  "pair_rel(a,b) \<in> r \<Longrightarrow> pair_rel(b,a) \<in> converse_rel(r)"
  sorry

(* \<langle>?a, ?b\<rangle> \<in> ?r \<Longrightarrow> ?b \<in> range(?r) *)
lemma range_relI [intro]:
  assumes "M(a)" "M(b)" "M(r)"
  shows  "pair_rel(a,b) \<in> r \<Longrightarrow> b \<in> range_rel(r)"
  using assms converse_rel_closed
(*  unfolding  range_rel_def
  using converse_relI  domain_relI
  by blast *)
  apply (unfold range_rel_def)
  apply (erule converse_relI [THEN domain_relI])
       apply (simp_all add:assms) \<comment> \<open>some assms were lost\<close>
  done

(*
lemma nth_closed' :
  assumes "0\<in>A" "env\<in>list(A)"
  shows "nth(n,env)\<in>A"
  using assms(2,1) unfolding nth_def by (induct env; simp)

lemma domain_fmI:
(* now domain_fm is in the antecedent, it can't be an intro rule *)
  notes
    Relative.M_trans.pair_abs[simp] nth_closed'[simp]
    Relative.M_basic.domain_closed[simp]
  assumes
    "M_trans(##A)" "M_basic(##A)"
    "0\<in>A"
    "env\<in>list(A)" "a\<in>nat" "b\<in>nat" "ab\<in>nat" "d\<in>nat" "r\<in>nat"
    "A, env \<Turnstile> pair_fm(a,b,ab)"  "A, env \<Turnstile> Member(ab,r)"
    "A, env \<Turnstile> domain_fm(r,d)"
  shows
    "A, env \<Turnstile> Member(a,d)"
  using assms  unfolding domain_fm_def
  apply (simp del:sats_domain_fm)
  oops
*)

end (* M_basic *)
end