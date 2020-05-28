theory Internal_Proofs
  imports
    FrecR
    Relativization
    "../Tools/Try0"
begin

definition
  is_range' :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_range'(M,r,c) \<equiv> is_hcomp(M,is_domain(M),is_converse(M),r,c)"

(* setup "Config.put_global Blast.trace true" *)

context M_ctm
begin

declare [[show_question_marks=false]]

thm strong_replacement_closed
(*  strong_replacement(##M, P) \<Longrightarrow> (##M)(A) \<Longrightarrow> univalent(##M, A, P) \<Longrightarrow>
    (\<And>x y. x \<in> A \<Longrightarrow> P(x, y) \<Longrightarrow> (##M)(y)) \<Longrightarrow> (##M)(Replace(A, P)) *)

thm replacement_ax
(* \<phi> \<in> formula \<Longrightarrow> env \<in> list(M) \<Longrightarrow> arity(\<phi>) \<le> 2 #+ length(env) \<Longrightarrow>
  strong_replacement(##M, \<lambda>x y. M, [x, y] @ env \<Turnstile> \<phi>) *)

thm ReplaceI
(* P(x, b) \<Longrightarrow> x \<in> A \<Longrightarrow> (\<And>y. P(x, y) \<Longrightarrow> y = b) \<Longrightarrow> b \<in> {y . x \<in> A, P(x, y)} *)

thm replacement_ax[THEN strong_replacement_closed]

thm Replace_abs[simplified]

end

context M_basic
begin

declare 
  pair_abs[simp del] pair_in_M_iff[simp del]
  pair_in_MD[rule del] pair_in_MI[rule del]
  domain_abs[simp del] domain_closed[simp del, rule del]
  converse_abs[simp del] converse_closed[simp del, rule del]
  range_abs[simp del] range_closed[simp del, rule del]

lemma extensionality_trans:
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
  sorry
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