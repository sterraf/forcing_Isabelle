theory Non_Constructible
  imports
    Names

begin

lemma (in forcing_notion) filter_imp_compat: "filter(G) \<Longrightarrow> p\<in>G \<Longrightarrow> q\<in>G \<Longrightarrow> compat(p,q)"  \<comment> \<open>put somewhere else\<close>
  unfolding filter_def compat_in_def compat_def by blast

definition
  chleR :: "i \<Rightarrow> i \<Rightarrow> o" where
  "chleR(xs,ys) \<equiv> \<exists>zs. xs = ys @ zs"

definition
  chlerel :: "i \<Rightarrow> i" where
  "chlerel(A) \<equiv> Rrel(chleR,A)"

definition
  chle :: "i" where
  "chle \<equiv> chlerel(list(2))"

lemma chleI[intro!]: 
  "\<langle>x,y\<rangle> \<in> list(2)\<times>list(2) \<Longrightarrow> \<exists>zs. x = y @ zs \<Longrightarrow> \<langle>x,y\<rangle> \<in> chle"
  unfolding preorder_on_def refl_def trans_on_def 
  chle_def chlerel_def Rrel_def chleR_def 
  by blast

lemma chleD[dest!]: 
  "z \<in> chle \<Longrightarrow> \<exists>x y. \<langle>x,y\<rangle> \<in> list(2)\<times>list(2) \<and> (\<exists>zs. x = y @ zs) \<and> z = \<langle>x,y\<rangle>"
  unfolding preorder_on_def refl_def trans_on_def 
  chle_def chlerel_def Rrel_def chleR_def 
  by blast

lemma preorder_on_chle: "preorder_on(list(2),chle)"
  unfolding preorder_on_def refl_def trans_on_def 
  using app_assoc by auto

lemma Nil_chle_max: "x\<in>list(2) \<Longrightarrow> \<langle>x,[]\<rangle> \<in> chle"
  by auto

interpretation ch: forcing_notion "list(2)" "chle" "[]"
  unfolding forcing_notion_def using preorder_on_chle Nil_chle_max by simp

abbreviation Chle :: "[i, i] \<Rightarrow> o"  (infixl "\<preceq>" 50)
  where "x \<preceq> y \<equiv> ch.Leq(x,y)"

abbreviation Incompatible :: "[i, i] \<Rightarrow> o"  (infixl "\<bottom>" 50)
  where "p \<bottom> q \<equiv> ch.Incompatible(p,q)"

lemma incompatible_extensions:
  assumes "p\<in>list(2)"
  shows "(p @ [0]) \<bottom> (p @ [1])"
proof
  assume "ch.compat(p @ [0], p @ [1])"
  then
  obtain q where "q\<in>list(2)" "q \<preceq> p@[0]" "q \<preceq> p@[1]" 
    by blast
  with assms
  obtain xs ys where "q = (p @ [0]) @ xs" "q = (p @ [1]) @ ys"  
    by blast
  with assms
  show "False" using app_assoc by simp
qed

lemma filter_complement_dense:
  assumes "ch.filter(G)" shows "ch.dense(list(2) - G)"
proof
  fix p
  assume "p\<in>list(2)"
  show "\<exists>d\<in>list(2) - G. ch.Leq(d, p)"
  proof (cases "p\<in>G")
    case True
    note assms \<open>p\<in>list(2)\<close>
    moreover from this
    obtain j where "j\<in>2" "p @ [j] \<notin> G"
      using incompatible_extensions[of p] ch.filter_imp_compat[of G "p @ [0]" "p @ [1]"] 
      by auto
    moreover from calculation
    have "p @ [k] \<in> list(2)" if "k\<in>2" for k using that by simp
    moreover from calculation
    have "p @ [j] \<preceq> p" by auto
    ultimately 
    show ?thesis by auto
  next
    case False
    with \<open>p\<in>list(2)\<close> 
    show ?thesis using ch.leq_reflI unfolding Diff_def by auto
  qed
qed

context M_ctm
begin

lemma poset_in_M: "list(2)\<in>M" 
  using list_closed transitivity[OF _ nat_in_M] by simp

lemma chle_in_M: "chle \<in> M"
  unfolding chle_def chlerel_def Rrel_def chleR_def
  sorry

end (* M_ctm *)


sublocale M_ctm \<subseteq> forcing_data "list(2)" "chle" "[]"
  using poset_in_M chle_in_M by (unfold_locales)


context M_ctm
begin

lemma generic_not_in_M: assumes "M_generic(G)"  shows "G \<notin> M"
proof
  assume "G\<in>M"
  then
  have "list(2) - G \<in> M" 
    using P_in_M Diff_closed by simp
  moreover
  have "\<not>(\<exists>q\<in>G. q \<in> list(2) - G)" "(list(2) - G) \<subseteq> list(2)"
    unfolding Diff_def by auto
  moreover
  note assms
  ultimately
  show "False"
    using filter_complement_dense[of G] M_generic_denseD[of G "list(2)-G"] 
      M_generic_def by simp \<comment> \<open>need to put generic ==> filter in claset\<close>
qed

lemma G_subset_M: "M_generic(G) \<Longrightarrow> G \<subseteq> M" \<comment> \<open>put somewhere else\<close>
  using transitivity[OF _ P_in_M] by auto

(* For some reason, "M[G]" doesn't work here *)
theorem proper_extension: assumes "M_generic(G)" shows "M \<noteq> GenExt(G)"
  using assms G_in_Gen_Ext[of G] one_in_G[of G] generic_not_in_M G_subset_M
  by force

end (* M_ctm *)

(* Versión con n \<rightarrow> 2 *)
(* f \<le> n g sii \<forall>j\<in>n. g`j=f`j *)
definition 
  seqspace :: "i \<Rightarrow> i" ("_^<\<omega>" [100]100) where
  "B^<\<omega> \<equiv> \<Union>n\<in>nat. (n\<rightarrow>B)"

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

lemma zero_in_seqspace : 
  shows "0 \<in> A^<\<omega>"
  unfolding seqspace_def
 by force


definition
  funleR :: "i \<Rightarrow> i \<Rightarrow> o" where
  "funleR(f,g) \<equiv> domain(g) \<subseteq> domain(f) \<and> (\<forall> j\<in>domain(g). g`j = f`j)"

definition
  funlerel :: "i \<Rightarrow> i" where
  "funlerel(A) \<equiv> Rrel(funleR,A^<\<omega>)"

definition
  funle :: "i" where
  "funle \<equiv> funlerel(2)"

lemma funleI[intro!]: 
  "\<langle>f,g\<rangle> \<in> 2^<\<omega>\<times>2^<\<omega> \<Longrightarrow> domain(g) \<subseteq> domain(f) \<and> (\<forall>i\<in>domain(g). g`i = f`i)  \<Longrightarrow> \<langle>f,g\<rangle> \<in> funle"
  unfolding preorder_on_def refl_def trans_on_def 
  seqspace_def funleR_def funle_def funlerel_def Rrel_def 
  by auto

lemma funleD[dest!]: 
  "z \<in> funle \<Longrightarrow> \<exists>x y. \<langle>x,y\<rangle> \<in> 2^<\<omega>\<times>2^<\<omega> \<and> funleR(x,y) \<and> z = \<langle>x,y\<rangle>"
  unfolding funle_def funlerel_def Rrel_def 
  by blast

lemma dom_funleD : 
  assumes "<f,g> \<in> funle"
  shows "domain(g)\<subseteq>domain(f)" 
  using assms unfolding funle_def funlerel_def Rrel_def  funleR_def
  by simp

lemma app_funleD : 
  assumes "<f,g> \<in> funle" "i\<in>domain(g)"
  shows "g`i=f`i" 
  using assms unfolding funle_def funlerel_def Rrel_def funleR_def
  by simp

lemma upd_leI : 
  assumes "f\<in>2^<\<omega>" "a\<in>2"
  shows "<fun_upd(f,a),f>\<in>funle" 
  sorry

lemma preorder_on_funle: "preorder_on(2^<\<omega>,funle)"
  unfolding preorder_on_def  
proof auto
  show "refl(2^<\<omega>, funle)"
    unfolding refl_def by blast
next
  show "trans[2^<\<omega>](funle)"
    unfolding trans_on_def 
  proof (rule ballI,rule ballI,rule ballI,rule,rule)
    {
    fix f g h 
    assume 1:"f\<in>2^<\<omega>" "g\<in>2^<\<omega>" "h\<in>2^<\<omega>"
          "<f,g> \<in> funle" "<g,h> \<in> funle"
    then
    have 2:"domain(h) \<subseteq> domain(f)" "domain(h) \<subseteq> domain(g)" 
      using subset_trans[OF _ dom_funleD[OF \<open><f,g>\<in>_\<close>]] dom_funleD by auto
    {fix i
      assume "i\<in>domain(h)"
      then
      have "i\<in>domain(g)"  "h`i = g`i" 
        using app_funleD[OF \<open><g,h>\<in>_\<close>] subsetD[OF \<open>domain(h)\<subseteq>domain(g)\<close>] by simp_all
      then
      have "h`i = f`i" 
        using app_funleD[OF \<open><f,g>\<in>_\<close>] by simp
    }
    then 
    have "h`i = f`i" if "i\<in>domain(h)" for i
      using that by auto
    with 2 1
    show "\<langle>f, h\<rangle> \<in> funle" by blast
  }
qed
qed

lemma zero_funle_max: "x\<in>2^<\<omega> \<Longrightarrow> \<langle>x,0\<rangle> \<in> funle"
  using zero_in_seqspace 
  by auto

interpretation fun: forcing_notion "2^<\<omega>" "funle" "0"
  unfolding forcing_notion_def 
  using preorder_on_funle zero_funle_max zero_in_seqspace by simp

abbreviation FUNle :: "[i, i] \<Rightarrow> o"  (infixl "\<preceq>f" 50)
  where "x \<preceq>f y \<equiv> fun.Leq(x,y)"

abbreviation FUNIncompatible :: "[i, i] \<Rightarrow> o"  (infixl "\<bottom>f" 50)
  where "p \<bottom>f q \<equiv> fun.Incompatible(p,q)"

lemma FUNincompatible_extensions:
  assumes "f\<in>2^<\<omega>"
  shows "(fun_upd(f,0)) \<bottom>f (fun_upd(f,1))" (is "?f \<bottom>f ?g")
proof 
  {
  assume "fun.compat(?f, ?g)"
  then
  have 1:"\<exists>h\<in>2^<\<omega> . h \<preceq>f ?f \<and> h \<preceq>f ?g" 
    unfolding fun.compat_def compat_in_def by simp
  {fix h
    assume "h\<in>2^<\<omega>" "h \<preceq>f ?f \<and> h \<preceq>f ?g"
    then have "h \<preceq>f ?f" "h \<preceq>f ?g" by simp_all
  from \<open>f\<in>_\<close>
  obtain y where "y\<in>nat" "f\<in>y\<rightarrow>2" 
    unfolding seqspace_def by blast
  then
  have "y\<in>succ(y)" "y=domain(f)" 
    using domain_of_fun by simp_all
  then
  have equ: "?f`y = 0" "?g`y = 1" "y\<in>domain(?f)" "y\<in>domain(?g)"
    unfolding fun_upd_def by auto
  then 
  have "0 = 1"
    using app_funleD[OF \<open>h \<preceq>f ?f\<close>]app_funleD[OF \<open>h \<preceq>f ?g\<close>]
    by auto
  with equ
  have False by blast
} then
  show "fun.compat(fun_upd(f, 0), fun_upd(f, 1)) \<Longrightarrow> False"
    using bexE[OF 1,of False] by auto
}
qed

lemma FUNfilter_complement_dense:
  assumes "fun.filter(G)" shows "fun.dense(2^<\<omega> - G)"
proof
  fix p
  assume "p\<in>2^<\<omega>"
  show "\<exists>d\<in>2^<\<omega> - G. fun.Leq(d, p)"
  proof (cases "p\<in>G")
    case True
    note assms \<open>p\<in>2^<\<omega>\<close>
    moreover from this
    obtain j where "j\<in>2" "fun_upd(p,j) \<notin> G"
      using FUNincompatible_extensions[of p] fun.filter_imp_compat[of G "fun_upd(p,0)" "fun_upd(p, 1)"] 
      by auto
    moreover from calculation 
    have "fun_upd(p,j) \<in> 2^<\<omega> - G" using fun_upd_type by simp
    moreover from calculation 
    have "fun_upd(p,j) \<preceq>f p" using upd_leI[OF \<open>p\<in>2^<\<omega>\<close> \<open>j\<in>2\<close>] by simp
    ultimately 
    show ?thesis using rev_bexI[OF \<open>fun_upd(p,j) \<in> 2^<\<omega> - G\<close>] by auto
  next
    case False
    with \<open>p\<in>2^<\<omega>\<close> 
    show ?thesis using fun.leq_reflI unfolding Diff_def by auto
  qed
qed

lemma (in M_datatypes) poset_in_M: "M(2^<\<omega>)" 
proof - 
  have "M(2)" "M(nat)" by auto
  then
  have "M(n \<rightarrow> 2)" if "n\<in>nat" for n
    using that finite_funspace_closed by simp
  with \<open>M(nat)\<close>
  have "M({ n\<rightarrow>2 . n\<in>nat})" sorry
  then 
  show ?thesis
    unfolding seqspace_def using Union_closed by simp
qed


end