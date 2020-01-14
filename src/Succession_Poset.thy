theory Succession_Poset
  imports
    Arities Proper_Extension Synthetic_Definition
    Names
begin

definition 
  seqspace :: "i \<Rightarrow> i" ("_^<\<omega>" [100]100) where
  "seqspace(B) \<equiv> \<Union>n\<in>nat. (n\<rightarrow>B)"

lemma seqspaceI[intro]: "n\<in>nat \<Longrightarrow> f:n\<rightarrow>B \<Longrightarrow> f\<in>seqspace(B)"
  unfolding seqspace_def by blast

lemma seqspaceD[dest]: "f\<in>seqspace(B) \<Longrightarrow> \<exists>n\<in>nat. f:n\<rightarrow>B"
  unfolding seqspace_def by blast

lemma seqspace_type: 
  "f \<in> B^<\<omega> \<Longrightarrow> \<exists>n\<in>nat. f:n\<rightarrow>B" 
  unfolding seqspace_def by auto

schematic_goal seqspace_fm_auto:
  assumes 
    "nth(i,env) = n" "nth(j,env) = z"  "nth(h,env) = B" 
    "i \<in> nat" "j \<in> nat" "h\<in>nat" "env \<in> list(A)"
  shows 
    "(\<exists>om\<in>A. omega(##A,om) \<and> n \<in> om \<and> is_funspace(##A, n, B, z)) \<longleftrightarrow> (A, env \<Turnstile> (?sqsprp(i,j,h)))"
  unfolding is_funspace_def 
  by (insert assms ; (rule sep_rules | simp)+)

synthesize "seqspace_rep_fm" from_schematic "seqspace_fm_auto"
 
locale M_seqspace =  M_trancl +
  assumes 
    seqspace_replacement: "M(B) \<Longrightarrow> strong_replacement(M,\<lambda>n z. n\<in>nat \<and> is_funspace(M,n,B,z))"

begin


lemma seqspace_closed:
  "M(B) \<Longrightarrow> M(B^<\<omega>)"
  unfolding seqspace_def using seqspace_replacement[of B] RepFun_closed2 
  by simp

end (* M_seqspace *)


sublocale M_ctm \<subseteq> M_seqspace "##M"
proof (unfold_locales, simp)
  fix B
  have "arity(seqspace_rep_fm(0,1,2)) \<le> 3" "seqspace_rep_fm(0,1,2)\<in>formula" 
    unfolding seqspace_rep_fm_def 
    using pair_fm_arity omega_fm_arity typed_function_fm_arity nat_simp_union 
    by auto
  moreover
  assume "B\<in>M"
  ultimately
  have "strong_replacement(##M, \<lambda>x y. M, [x, y, B] \<Turnstile> seqspace_rep_fm(0, 1, 2))"
    using replacement_ax[of "seqspace_rep_fm(0,1,2)"]
    by simp
  moreover 
  note \<open>B\<in>M\<close>
  moreover from this
  have "univalent(##M, A, \<lambda>x y. M, [x, y, B] \<Turnstile> seqspace_rep_fm(0, 1, 2))" 
    if "A\<in>M" for A 
    using that unfolding univalent_def seqspace_rep_fm_def  
    by (auto, blast dest:transitivity)
  ultimately
  have "strong_replacement(##M, \<lambda>n z. \<exists>om[##M]. omega(##M,om) \<and> n \<in> om \<and> is_funspace(##M, n, B, z))"
    using seqspace_fm_auto[of 0 "[_,_,B]" _ 1 _ 2 B M] unfolding seqspace_rep_fm_def strong_replacement_def
    by simp
  with \<open>B\<in>M\<close> 
  show "strong_replacement(##M, \<lambda>n z. n \<in> nat \<and> is_funspace(##M, n, B, z))"
    using M_nat by simp
qed

definition fun_upd :: "i \<Rightarrow> i \<Rightarrow> i" where
  "fun_upd(f,a) \<equiv> \<lambda> j \<in> succ(domain(f)) . if j < domain(f) then f`j else a"

lemma fun_upd_succ_type : 
  assumes "n\<in>nat" "f\<in>n\<rightarrow>A" "a\<in>A"
  shows "fun_upd(f,a)\<in> succ(n) \<rightarrow> A"
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
    unfolding fun_upd_def
    using lam_type[of "succ(domain(f))"]
    by auto
qed

lemma fun_upd_type : 
  assumes "f\<in>A^<\<omega>" "a\<in>A"
  shows "fun_upd(f,a) \<in> A^<\<omega>"
proof -
  from \<open>f\<in>_\<close>
  obtain y where "y\<in>nat" "f\<in>y\<rightarrow>A"
    unfolding seqspace_def by blast
  with \<open>a\<in>A\<close>
  have "fun_upd(f,a)\<in>succ(y)\<rightarrow>A" 
    using fun_upd_succ_type by simp
  with \<open>y\<in>_\<close>
  show ?thesis
    unfolding seqspace_def by auto
qed

lemma fun_upd_apply_domain [simp]: 
  assumes "f:n\<rightarrow>A" "n\<in>nat"
  shows "fun_upd(f,a)`n = a"
  unfolding fun_upd_def using assms domain_of_fun by auto

lemma zero_in_seqspace : 
  shows "0 \<in> A^<\<omega>"
  unfolding seqspace_def
  by force

definition
  funleR :: "i \<Rightarrow> i \<Rightarrow> o" where
  "funleR(f,g) \<equiv> g \<subseteq> f"

definition
  funlerel :: "i \<Rightarrow> i" where
  "funlerel(A) \<equiv> Rrel(\<lambda>x y. y \<subseteq> x,A^<\<omega>)"

definition
  funle :: "i" where
  "funle \<equiv> funlerel(2)"

lemma funleI[intro!]: 
  "\<langle>f,g\<rangle> \<in> 2^<\<omega>\<times>2^<\<omega> \<Longrightarrow> g \<subseteq> f  \<Longrightarrow> \<langle>f,g\<rangle> \<in> funle"
  unfolding  seqspace_def funle_def funlerel_def Rrel_def 
  by blast

lemma funleD[dest!]: 
  "z \<in> funle \<Longrightarrow> \<exists>x y. \<langle>x,y\<rangle> \<in> 2^<\<omega>\<times>2^<\<omega> \<and> y \<subseteq> x \<and> z = \<langle>x,y\<rangle>"
  unfolding funle_def funlerel_def Rrel_def 
  by blast

lemma upd_leI : 
  assumes "f\<in>2^<\<omega>" "a\<in>2"
  shows "<fun_upd(f,a),f>\<in>funle"  (is "<?f,_>\<in>_")
proof
  show " \<langle>?f, f\<rangle> \<in> 2^<\<omega> \<times> 2^<\<omega>" 
    using assms fun_upd_type by auto
next
  show  "f \<subseteq> fun_upd(f,a)" 
  proof 
    fix x
    assume "x \<in> f"
    moreover from \<open>f \<in> 2^<\<omega>\<close>
    obtain n where  "n\<in>nat" "f : n \<rightarrow> 2"
      using seqspace_type by blast
    moreover from calculation
    obtain y where "y\<in>n" "x=<y,f`y>" using Pi_memberD[of f n "\<lambda>_ . 2"] 
      by blast
    moreover from \<open>f:n\<rightarrow>2\<close>
    have "domain(f) = n" using domain_of_fun by simp
    ultimately
    show "x \<in> fun_upd(f,a)"
      unfolding fun_upd_def lam_def  
      by (auto intro:ltI)
  qed
qed

lemma preorder_on_funle: "preorder_on(2^<\<omega>,funle)"
  unfolding preorder_on_def refl_def trans_on_def by blast

lemma zero_funle_max: "x\<in>2^<\<omega> \<Longrightarrow> \<langle>x,0\<rangle> \<in> funle"
  using zero_in_seqspace 
  by auto

interpretation forcing_notion "2^<\<omega>" "funle" "0"
  using preorder_on_funle zero_funle_max zero_in_seqspace 
  by unfold_locales simp_all

abbreviation FUNle :: "[i, i] \<Rightarrow> o"  (infixl "\<preceq>f" 50)
  where "x \<preceq>f y \<equiv> Leq(x,y)"

abbreviation FUNIncompatible :: "[i, i] \<Rightarrow> o"  (infixl "\<bottom>f" 50)
  where "x \<bottom>f y \<equiv> Incompatible(x,y)"

lemma seqspace_separative:
  assumes "f\<in>2^<\<omega>"
  shows "fun_upd(f,0) \<bottom>f fun_upd(f,1)" (is "?f \<bottom>f ?g")
proof 
  assume "compat(?f, ?g)"
  then 
  obtain h where "h \<in> 2^<\<omega>" "?f \<subseteq> h" "?g \<subseteq> h"
    by blast
  moreover from \<open>f\<in>_\<close>
  obtain y where "y\<in>nat" "f:y\<rightarrow>2" by blast
  moreover from this
  have "?f: succ(y) \<rightarrow> 2" "?g: succ(y) \<rightarrow> 2" 
    using fun_upd_succ_type by blast+
  moreover from this
  have "<y,?f`y> \<in> ?f" "<y,?g`y> \<in> ?g" using apply_Pair by auto
  ultimately
  have "<y,0> \<in> h" "<y,1> \<in> h" by auto
  moreover from \<open>h \<in> 2^<\<omega>\<close>
  obtain n where "n\<in>nat" "h:n\<rightarrow>2" by blast
  ultimately
  show "False"
    using fun_is_function[of h n "\<lambda>_. 2"] 
    unfolding seqspace_def function_def by auto
qed

definition is_funleR :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_funleR(Q,f,g) \<equiv> g \<subseteq> f"

definition funleR_fm :: "i \<Rightarrow> i" where
  "funleR_fm(fg) \<equiv> Exists(Exists(And(pair_fm(0,1,fg#+2),subset_fm(1,0))))"

lemma type_funleR_fm :
  "fg \<in> nat \<Longrightarrow> funleR_fm(fg) \<in> formula"
  unfolding funleR_fm_def 
  by simp

lemma arity_funleR_fm :
  "fg \<in> nat \<Longrightarrow> arity(funleR_fm(fg)) = succ(fg)"
  unfolding funleR_fm_def 
  using pair_fm_arity subset_fm_arity nat_simp_union by simp

lemma (in M_basic) funleR_abs: 
  assumes "M(f)" "M(g)"
  shows "funleR(f,g) \<longleftrightarrow> is_funleR(M,f,g)"
  unfolding funleR_def is_funleR_def 
  using assms apply_abs domain_abs domain_closed[OF \<open>M(f)\<close>]  domain_closed[OF \<open>M(g)\<close>]
  by auto

definition
  relP :: "[i\<Rightarrow>o,[i\<Rightarrow>o,i,i]\<Rightarrow>o,i] \<Rightarrow> o" where
  "relP(M,r,xy) \<equiv> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,xy) \<and> r(M,x,y))"

lemma (in M_ctm) funleR_fm_sats : 
  assumes "fg\<in>nat" "env\<in>list(M)" 
  shows "sats(M,funleR_fm(fg),env) \<longleftrightarrow> relP(##M,is_funleR,nth(fg, env))"
  unfolding funleR_fm_def is_funleR_def relP_def
  using assms trans_M sats_subset_fm pair_iff_sats
  by auto


lemma (in M_basic) is_related_abs :
  assumes "\<And> f g . M(f) \<Longrightarrow> M(g) \<Longrightarrow> rel(f,g) \<longleftrightarrow> is_rel(M,f,g)"
  shows "\<And>z . M(z) \<Longrightarrow> relP(M,is_rel,z) \<longleftrightarrow> (\<exists>x y. z = <x,y> \<and> rel(x,y))"
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
  have "Collect(A\<times>A,relP(M,is_rel)) = Collect(A\<times>A,\<lambda>z. (\<exists>x y. z = <x,y> \<and> rel(x,y)))"
    using Collect_cong[of "A\<times>A" "A\<times>A" "relP(M,is_rel)",OF _ A(1)] assms(1) assms(2)
    by auto
  with assms
  show ?thesis unfolding is_RRel_def Rrel_def using cartprod_closed
    by auto
qed

definition
  is_funlerel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_funlerel(M,A,r) \<equiv> is_RRel(M,is_funleR,A,r)"

lemma (in M_basic) funlerel_abs :
  assumes "M(A)"  "M(r)"
  shows "is_funlerel(M,A,r) \<longleftrightarrow> r = Rrel(funleR,A)"
  unfolding is_funlerel_def
  using is_Rrel_abs[OF \<open>M(A)\<close> \<open>M(r)\<close>,of funleR is_funleR] funleR_abs
  by auto

definition RrelP :: "[i\<Rightarrow>i\<Rightarrow>o,i] \<Rightarrow> i" where
  "RrelP(R,A) \<equiv> {z\<in>A\<times>A. \<exists>x y. z = \<langle>x, y\<rangle> \<and> R(x,y)}"
  
lemma Rrel_eq : "RrelP(R,A) = Rrel(R,A)"
  unfolding Rrel_def RrelP_def by auto

context M_ctm
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
  have "Collect(A\<times>A,\<lambda>z. (\<exists>x y. z = <x,y> \<and> rel(x,y))) \<in> M"
    using Collect_in_M_0p[of "rel_fm(0)" "\<lambda> A z . relP(A,is_rel,z)" "\<lambda> z.\<exists>x y. z = \<langle>x, y\<rangle> \<and> rel(x, y)" ]
        cartprod_closed
    by simp
  then show ?thesis
  unfolding Rrel_def by simp
qed

lemma funle_in_M: "funle \<in> M"
  using Rrel_closed seqspace_closed 
    transitivity[OF _ nat_in_M] type_funleR_fm[of 0] arity_funleR_fm[of 0]
    funleR_fm_sats[of 0] funleR_abs funlerel_abs 
  unfolding funle_def funlerel_def funleR_def
  by auto

interpretation ctm_separative "2^<\<omega>" funle 0
proof (unfold_locales)
  fix f
  let ?q="fun_upd(f,0)" and ?r="fun_upd(f,1)"
  assume "f \<in> 2^<\<omega>"
  then
  have "?q \<preceq>f f \<and> ?r \<preceq>f f \<and> ?q \<bottom>f ?r" 
    using upd_leI seqspace_separative by auto
  moreover from calculation
  have "?q \<in> 2^<\<omega>"  "?r \<in> 2^<\<omega>"
    using fun_upd_type[of f 2] by auto
  ultimately
  show "\<exists>q\<in>2^<\<omega>. \<exists>r\<in>2^<\<omega>. q \<preceq>f f \<and> r \<preceq>f f \<and> q \<bottom>f r"
    by (rule_tac bexI)+ \<comment> \<open>why the heck auto-tools don't solve this?\<close>
next
  show "2^<\<omega> \<in> M" using nat_into_M seqspace_closed by simp
next
  show "funle \<in> M" using funle_in_M .
qed

lemma cohen_extension_is_proper: "\<exists>G. M_generic(G) \<and> M \<noteq> GenExt(G)"
  using proper_extension generic_filter_existence zero_in_seqspace
  by force

end (* M_ctm *)

end