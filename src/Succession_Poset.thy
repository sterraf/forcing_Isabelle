section\<open>A poset of successions\<close>

theory Succession_Poset
  imports
    Replacement_Instances
    Proper_Extension
begin

sublocale M_ZF2_trans \<subseteq> M_seqspace "##M"
  by (unfold_locales, simp add:replacement_omega_funspace)

definition seq_upd :: "i \<Rightarrow> i \<Rightarrow> i" where
  "seq_upd(f,a) \<equiv> \<lambda> j \<in> succ(domain(f)) . if j < domain(f) then f`j else a"

lemma seq_upd_succ_type :
  assumes "n\<in>nat" "f\<in>n\<rightarrow>A" "a\<in>A"
  shows "seq_upd(f,a)\<in> succ(n) \<rightarrow> A"
proof -
  from assms
  have equ: "domain(f) = n" using domain_of_fun by simp
  {
    fix j
    assume "j\<in>succ(domain(f))"
    with equ \<open>n\<in>_\<close>
    have "j\<le>n" using ltI by auto
    with \<open>n\<in>_\<close>
    consider (lt) "j<n" | (eq) "j=n" using leD by auto
    then
    have "(if j < n then f`j else a) \<in> A"
    proof cases
      case lt
      with \<open>f\<in>_\<close>
      show ?thesis using apply_type ltD[OF lt] by simp
    next
      case eq
      with \<open>a\<in>_\<close>
      show ?thesis by auto
    qed
  }
  with equ
  show ?thesis
    unfolding seq_upd_def
    using lam_type[of "succ(domain(f))"]
    by auto
qed

lemma seq_upd_type :
  assumes "f\<in>A\<^bsup><\<omega>\<^esup>" "a\<in>A"
  shows "seq_upd(f,a) \<in> A\<^bsup><\<omega>\<^esup>"
proof -
  from \<open>f\<in>_\<close>
  obtain y where "y\<in>nat" "f\<in>y\<rightarrow>A"
    unfolding seqspace_def by blast
  with \<open>a\<in>A\<close>
  have "seq_upd(f,a)\<in>succ(y)\<rightarrow>A"
    using seq_upd_succ_type by simp
  with \<open>y\<in>_\<close>
  show ?thesis
    unfolding seqspace_def by auto
qed

lemma seq_upd_apply_domain [simp]:
  assumes "f:n\<rightarrow>A" "n\<in>nat"
  shows "seq_upd(f,a)`n = a"
  unfolding seq_upd_def using assms domain_of_fun by auto

lemma zero_in_seqspace :
  shows "0 \<in> A\<^bsup><\<omega>\<^esup>"
  unfolding seqspace_def
  by force

definition
  seqleR :: "i \<Rightarrow> i \<Rightarrow> o" where
  "seqleR(f,g) \<equiv> g \<subseteq> f"

definition
  seqlerel :: "i \<Rightarrow> i" where
  "seqlerel(A) \<equiv> Rrel(\<lambda>x y. y \<subseteq> x,A\<^bsup><\<omega>\<^esup>)"

definition
  seqle :: "i" where
  "seqle \<equiv> seqlerel(2)"

lemma seqleI[intro!]:
  "\<langle>f,g\<rangle> \<in> 2\<^bsup><\<omega>\<^esup>\<times>2\<^bsup><\<omega>\<^esup> \<Longrightarrow> g \<subseteq> f  \<Longrightarrow> \<langle>f,g\<rangle> \<in> seqle"
  unfolding  seqspace_def seqle_def seqlerel_def Rrel_def
  by blast

lemma seqleD[dest!]:
  "z \<in> seqle \<Longrightarrow> \<exists>x y. \<langle>x,y\<rangle> \<in> 2\<^bsup><\<omega>\<^esup>\<times>2\<^bsup><\<omega>\<^esup> \<and> y \<subseteq> x \<and> z = \<langle>x,y\<rangle>"
  unfolding seqle_def seqlerel_def Rrel_def
  by blast

lemma upd_leI :
  assumes "f\<in>2\<^bsup><\<omega>\<^esup>" "a\<in>2"
  shows "\<langle>seq_upd(f,a),f\<rangle>\<in>seqle"  (is "\<langle>?f,_\<rangle>\<in>_")
proof
  show " \<langle>?f, f\<rangle> \<in> 2\<^bsup><\<omega>\<^esup> \<times> 2\<^bsup><\<omega>\<^esup>"
    using assms seq_upd_type by auto
next
  show  "f \<subseteq> seq_upd(f,a)"
  proof
    fix x
    assume "x \<in> f"
    moreover from \<open>f \<in> 2\<^bsup><\<omega>\<^esup>\<close>
    obtain n where  "n\<in>nat" "f : n \<rightarrow> 2"
      by blast
    moreover from calculation
    obtain y where "y\<in>n" "x=\<langle>y,f`y\<rangle>" using Pi_memberD[of f n "\<lambda>_ . 2"]
      by blast
    moreover from \<open>f:n\<rightarrow>2\<close>
    have "domain(f) = n" using domain_of_fun by simp
    ultimately
    show "x \<in> seq_upd(f,a)"
      unfolding seq_upd_def lam_def
      by (auto intro:ltI)
  qed
qed

lemma preorder_on_seqle: "preorder_on(2\<^bsup><\<omega>\<^esup>,seqle)"
  unfolding preorder_on_def refl_def trans_on_def by blast

lemma zero_seqle_max: "x\<in>2\<^bsup><\<omega>\<^esup> \<Longrightarrow> \<langle>x,0\<rangle> \<in> seqle"
  using zero_in_seqspace
  by auto

interpretation sp:forcing_notion "2\<^bsup><\<omega>\<^esup>" "seqle" "0"
  using preorder_on_seqle zero_seqle_max zero_in_seqspace
  by unfold_locales simp_all

notation sp.Leq (infixl "\<preceq>s" 50)
notation sp.Incompatible (infixl "\<bottom>s" 50)

lemma seqspace_separative:
  assumes "f\<in>2\<^bsup><\<omega>\<^esup>"
  shows "seq_upd(f,0) \<bottom>s seq_upd(f,1)" (is "?f \<bottom>s ?g")
proof
  assume "sp.compat(?f, ?g)"
  then
  obtain h where "h \<in> 2\<^bsup><\<omega>\<^esup>" "?f \<subseteq> h" "?g \<subseteq> h"
    by blast
  moreover from \<open>f\<in>_\<close>
  obtain y where "y\<in>nat" "f:y\<rightarrow>2" by blast
  moreover from this
  have "?f: succ(y) \<rightarrow> 2" "?g: succ(y) \<rightarrow> 2"
    using seq_upd_succ_type by blast+
  moreover from this
  have "\<langle>y,?f`y\<rangle> \<in> ?f" "\<langle>y,?g`y\<rangle> \<in> ?g" using apply_Pair by auto
  ultimately
  have "\<langle>y,0\<rangle> \<in> h" "\<langle>y,1\<rangle> \<in> h" by auto
  moreover from \<open>h \<in> 2\<^bsup><\<omega>\<^esup>\<close>
  obtain n where "n\<in>nat" "h:n\<rightarrow>2" by blast
  ultimately
  show "False"
    using fun_is_function[of h n "\<lambda>_. 2"]
    unfolding seqspace_def function_def by auto
qed

definition is_seqleR :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_seqleR(Q,f,g) \<equiv> g \<subseteq> f"

definition seqleR_fm :: "i \<Rightarrow> i" where
  "seqleR_fm(fg) \<equiv> Exists(Exists(And(pair_fm(0,1,fg#+2),subset_fm(1,0))))"

lemma type_seqleR_fm :
  "fg \<in> nat \<Longrightarrow> seqleR_fm(fg) \<in> formula"
  unfolding seqleR_fm_def
  by simp

lemma arity_seqleR_fm :
  "fg \<in> nat \<Longrightarrow> arity(seqleR_fm(fg)) = succ(fg)"
  unfolding seqleR_fm_def
  using arity_pair_fm arity_subset_fm ord_simp_union FOL_arities by simp

lemma (in M_basic) seqleR_abs:
  assumes "M(f)" "M(g)"
  shows "seqleR(f,g) \<longleftrightarrow> is_seqleR(M,f,g)"
  unfolding seqleR_def is_seqleR_def
  using assms apply_abs domain_abs domain_closed[OF \<open>M(f)\<close>]  domain_closed[OF \<open>M(g)\<close>]
  by auto

definition
  relP :: "[i\<Rightarrow>o,[i\<Rightarrow>o,i,i]\<Rightarrow>o,i] \<Rightarrow> o" where
  "relP(M,r,xy) \<equiv> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,xy) \<and> r(M,x,y))"

lemma (in M_ctm1) seqleR_fm_sats :
  assumes "fg\<in>nat" "env\<in>list(M)"
  shows "sats(M,seqleR_fm(fg),env) \<longleftrightarrow> relP(##M,is_seqleR,nth(fg, env))"
  unfolding seqleR_fm_def is_seqleR_def relP_def
  using assms trans_M sats_subset_fm pair_iff_sats
  by auto


lemma (in M_basic) is_related_abs :
  assumes "\<And> f g . M(f) \<Longrightarrow> M(g) \<Longrightarrow> rel(f,g) \<longleftrightarrow> is_rel(M,f,g)"
  shows "\<And>z . M(z) \<Longrightarrow> relP(M,is_rel,z) \<longleftrightarrow> (\<exists>x y. z = \<langle>x,y\<rangle> \<and> rel(x,y))"
  unfolding relP_def using pair_in_M_iff assms by auto

definition
  is_RRel :: "[i\<Rightarrow>o,[i\<Rightarrow>o,i,i]\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_RRel(M,is_r,A,r) \<equiv> \<exists>A2[M]. cartprod(M,A,A,A2) \<and> is_Collect(M,A2, relP(M,is_r),r)"

lemma (in M_basic) is_Rrel_abs :
  assumes "M(A)"  "M(r)"
    "\<And> f g . M(f) \<Longrightarrow> M(g) \<Longrightarrow> rel(f,g) \<longleftrightarrow> is_rel(M,f,g)"
  shows "is_RRel(M,is_rel,A,r) \<longleftrightarrow>  r = Rrel(rel,A)"
proof -
  from \<open>M(A)\<close>
  have "M(z)" if "z\<in>A\<times>A" for z
    using cartprod_closed transM[of z "A\<times>A"] that by simp
  then
  have A:"relP(M, is_rel, z) \<longleftrightarrow> (\<exists>x y. z = \<langle>x, y\<rangle> \<and> rel(x, y))" "M(z)" if "z\<in>A\<times>A" for z
    using that is_related_abs[of rel is_rel,OF assms(3)] by auto
  then
  have "Collect(A\<times>A,relP(M,is_rel)) = Collect(A\<times>A,\<lambda>z. (\<exists>x y. z = \<langle>x,y\<rangle> \<and> rel(x,y)))"
    using Collect_cong[of "A\<times>A" "A\<times>A" "relP(M,is_rel)",OF _ A(1)] assms(1) assms(2)
    by auto
  with assms
  show ?thesis unfolding is_RRel_def Rrel_def using cartprod_closed
    by auto
qed

definition
  is_seqlerel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_seqlerel(M,A,r) \<equiv> is_RRel(M,is_seqleR,A,r)"

lemma (in M_basic) seqlerel_abs :
  assumes "M(A)"  "M(r)"
  shows "is_seqlerel(M,A,r) \<longleftrightarrow> r = Rrel(seqleR,A)"
  unfolding is_seqlerel_def
  using is_Rrel_abs[OF \<open>M(A)\<close> \<open>M(r)\<close>,of seqleR is_seqleR] seqleR_abs
  by auto

definition RrelP :: "[i\<Rightarrow>i\<Rightarrow>o,i] \<Rightarrow> i" where
  "RrelP(R,A) \<equiv> {z\<in>A\<times>A. \<exists>x y. z = \<langle>x, y\<rangle> \<and> R(x,y)}"

lemma Rrel_eq : "RrelP(R,A) = Rrel(R,A)"
  unfolding Rrel_def RrelP_def by auto

locale M_ctm2 = M_ctm1 + M_ZF2_trans

locale M_ctm2_AC = M_ctm2 + M_ZFC2_trans

locale forcing_data2 = forcing_data1 + M_ctm2

(* FIXME: perhaps then obsolete *)
sublocale M_ctm \<subseteq> M_ctm2 ..
sublocale M_ctm_AC \<subseteq> M_ctm2_AC ..
sublocale forcing_data \<subseteq> forcing_data2 ..

context M_ctm2
begin

lemma Rrel_closed:
  assumes "A\<in>M"
    "\<And> a. a \<in> nat \<Longrightarrow> rel_fm(a)\<in>formula"
    "\<And> f g . (##M)(f) \<Longrightarrow> (##M)(g) \<Longrightarrow> rel(f,g) \<longleftrightarrow> is_rel(##M,f,g)"
    "arity(rel_fm(0)) = 1"
    "\<And> a . a \<in> M \<Longrightarrow> sats(M,rel_fm(0),[a]) \<longleftrightarrow> relP(##M,is_rel,a)"
  shows "(##M)(Rrel(rel,A))"
proof -
  have "z\<in> M \<Longrightarrow> relP(##M, is_rel, z) \<longleftrightarrow> (\<exists>x y. z = \<langle>x, y\<rangle> \<and> rel(x, y))" for z
    using assms(3) is_related_abs[of rel is_rel]
    by auto
  with assms
  have "Collect(A\<times>A,\<lambda>z. (\<exists>x y. z = \<langle>x,y\<rangle> \<and> rel(x,y))) \<in> M"
    using Collect_in_M[OF assms(2),of 0 "[]"] cartprod_closed
    by simp
  then show ?thesis
  unfolding Rrel_def by simp
qed

lemma seqle_in_M: "seqle \<in> M"
  using Rrel_closed seqspace_closed
    transitivity[OF _ nat_in_M] type_seqleR_fm[of 0] arity_seqleR_fm[of 0]
    seqleR_fm_sats[of 0] seqleR_abs seqlerel_abs
  unfolding seqle_def seqlerel_def seqleR_def
  by auto

subsection\<open>Cohen extension is proper\<close>

interpretation ctm_separative "2\<^bsup><\<omega>\<^esup>" seqle 0
proof (unfold_locales)
  fix f
  let ?q="seq_upd(f,0)" and ?r="seq_upd(f,1)"
  assume "f \<in> 2\<^bsup><\<omega>\<^esup>"
  then
  have "?q \<preceq>s f \<and> ?r \<preceq>s f \<and> ?q \<bottom>s ?r"
    using upd_leI seqspace_separative by auto
  moreover from calculation
  have "?q \<in> 2\<^bsup><\<omega>\<^esup>"  "?r \<in> 2\<^bsup><\<omega>\<^esup>"
    using seq_upd_type[of f 2] by auto
  ultimately
  show "\<exists>q\<in>2\<^bsup><\<omega>\<^esup>. \<exists>r\<in>2\<^bsup><\<omega>\<^esup>. q \<preceq>s f \<and> r \<preceq>s f \<and> q \<bottom>s r"
    by (rule_tac bexI)+ \<comment> \<open>why the heck auto-tools don't solve this?\<close>
next
  show "2\<^bsup><\<omega>\<^esup> \<in> M" using nat_into_M seqspace_closed by simp
next
  show "seqle \<in> M" using seqle_in_M .
qed

lemma cohen_extension_is_proper: "\<exists>G. M_generic(G) \<and> M \<noteq> M\<^bsup>2\<^bsup><\<omega>\<^esup>\<^esup>[G]"
  using proper_extension generic_filter_existence zero_in_seqspace
  by force

end \<comment> \<open>\<^locale>\<open>M_ctm2\<close>\<close>

end