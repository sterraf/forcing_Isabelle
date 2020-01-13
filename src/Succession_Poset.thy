theory Succession_Poset
  imports
    Proper_Extension Synthetic_Definition

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
    "nth(i,env) = n" "nth(j,env) = B" "nth(h,env) = z"
    "i \<in> nat" "j \<in> nat" "h \<in> nat" "env \<in> list(A)"
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
  have "arity(seqspace_rep_fm(0,1,2)) = 3" "seqspace_rep_fm(0,1,2)\<in>formula" sorry
  moreover
  assume "B\<in>M"
  ultimately
  have "strong_replacement(##M, \<lambda>n z. \<exists>om[##M]. omega(##M,om) \<and> n \<in> om \<and> is_funspace(##M, n, B, z))"
    using replacement_ax[of "seqspace_rep_fm(0,1,2)"] unfolding seqspace_rep_fm_def
    apply simp
    sorry
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

interpretation fun: forcing_notion "2^<\<omega>" "funle" "0"
  unfolding forcing_notion_def 
  using preorder_on_funle zero_funle_max zero_in_seqspace by simp

abbreviation FUNle :: "[i, i] \<Rightarrow> o"  (infixl "\<preceq>f" 50)
  where "x \<preceq>f y \<equiv> fun.Leq(x,y)"

lemma seqspace_separative:
  assumes "f\<in>2^<\<omega>"
  shows "fun.Incompatible(fun_upd(f,0),fun_upd(f,1))" (is "fun.Incompatible(?f,?g)")
proof 
  assume "fun.compat(?f, ?g)"
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

sublocale M_ctm \<subseteq> ctm_separative "2^<\<omega>" funle 0
proof (unfold_locales)
  fix f
  let ?q="fun_upd(f,0)" and ?r="fun_upd(f,1)"
  assume "f \<in> 2^<\<omega>"
  then
  have "?q \<preceq>f f \<and> ?r \<preceq>f f \<and> fun.Incompatible(?q, ?r)" 
    using upd_leI seqspace_separative by auto
  moreover from calculation
  have "?q \<in> 2^<\<omega>"  "?r \<in> 2^<\<omega>"
    using fun_upd_type[of f 2] by auto
  ultimately
  show "\<exists>q\<in>2^<\<omega>. \<exists>r\<in>2^<\<omega>. q \<preceq>f f \<and> r \<preceq>f f \<and> fun.Incompatible(q, r)"
    by (rule_tac bexI)+ \<comment> \<open>why the heck auto-tools don't solve this?\<close>
next
  show "2^<\<omega> \<in> M" using nat_into_M seqspace_closed by simp
next
  show "funle \<in> M"  sorry
qed

lemmas (in M_ctm) cohen_extension_is_proper = proper_extension

end