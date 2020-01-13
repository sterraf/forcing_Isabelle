theory Non_Constructible
  imports
    Names

begin

lemmas sep_rules' = nth_0 nth_ConsI FOL_iff_sats function_iff_sats
                   fun_plus_iff_sats 
                    omega_iff_sats FOL_sats_iff 

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

lemma funlerelI[intro!]: 
  "\<langle>f,g\<rangle> \<in> A^<\<omega>\<times>A^<\<omega> \<Longrightarrow> domain(g) \<subseteq> domain(f) \<and> (\<forall>i\<in>domain(g). g`i = f`i)  \<Longrightarrow> \<langle>f,g\<rangle> \<in> funlerel(A)"
  unfolding preorder_on_def refl_def trans_on_def 
  seqspace_def funleR_def funle_def funlerel_def Rrel_def 
  by auto

lemma funlerelD[dest!]: 
  "z \<in> funlerel(A) \<Longrightarrow> \<exists>x y. \<langle>x,y\<rangle> \<in> A^<\<omega>\<times>A^<\<omega> \<and> funleR(x,y) \<and> z = \<langle>x,y\<rangle>"
  unfolding funle_def funlerel_def Rrel_def 
  by blast

lemma dom_funleD : 
  assumes "<f,g> \<in> funlerel(2)"
  shows "domain(g)\<subseteq>domain(f)" 
  using assms unfolding funle_def funlerel_def Rrel_def  funleR_def
  by simp

lemma app_funleD : 
  assumes "<f,g> \<in> funlerel(2)" "i\<in>domain(g)"
  shows "g`i=f`i" 
  using assms unfolding funlerel_def Rrel_def funleR_def
  by simp

lemma upd_leI : 
  assumes "f\<in>A^<\<omega>" "a\<in>A"
  shows "<fun_upd(f,a),f>\<in>funlerel(A)" (is "<?f,_>\<in>_")
proof
  show " \<langle>?f, f\<rangle> \<in> A^<\<omega> \<times> A^<\<omega>" 
    using assms fun_upd_type by auto
next
  show  "domain(f) \<subseteq> domain(?f) \<and> (\<forall>i\<in>domain(f). f ` i = ?f ` i)"
  proof -
    from assms 
    obtain y where "y\<in>nat" "f\<in>y\<rightarrow>A" 
      unfolding seqspace_def  by blast 
    then
    have "domain(f) = y" "domain(?f) = succ(y)"
      using domain_of_fun fun_upd_succ_type [OF _ \<open>f\<in>y\<rightarrow>A\<close> \<open>a\<in>A\<close>] by auto
    with \<open>y\<in>_\<close>
    have "domain(f) \<subseteq> domain(?f)"
      using le_imp_subset[of y "succ(y)"] by simp  
    have "\<forall>i\<in>domain(f). f ` i = fun_upd(f, a) ` i"
    proof
      fix i 
      assume "i\<in>domain(f)"
      with \<open>domain(f) = y\<close> \<open>y\<in>nat\<close>
      have "i<domain(f)" "i\<in>succ(domain(f))"
        using ltI succI2 by simp_all
      then 
      show "f`i = ?f`i" 
        unfolding fun_upd_def by auto
    qed
    with \<open>domain(f) \<subseteq> domain(?f)\<close>
    show ?thesis ..
  qed
qed

lemma preorder_on_funle: "preorder_on(2^<\<omega>,funlerel(2))"
  unfolding preorder_on_def  
proof auto
  show "refl(2^<\<omega>, funlerel(2))"
    unfolding refl_def by blast
next
  show "trans[2^<\<omega>](funlerel(2))"
    unfolding trans_on_def 
  proof (rule ballI,rule ballI,rule ballI,rule,rule)
    {
    fix f g h 
    assume 1:"f\<in>2^<\<omega>" "g\<in>2^<\<omega>" "h\<in>2^<\<omega>"
          "<f,g> \<in> funlerel(2)" "<g,h> \<in> funlerel(2)"
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
    show "\<langle>f, h\<rangle> \<in> funlerel(2)" by blast
  }
qed
qed

lemma zero_funle_max: "x\<in>2^<\<omega> \<Longrightarrow> \<langle>x,0\<rangle> \<in> funlerel(2)"
  using zero_in_seqspace
  by auto

interpretation fun: forcing_notion "2^<\<omega>" "funlerel(2)" "0"
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
    assume "fun.compat(?f, ?g)"
    then
    have 1:"\<exists>h\<in>2^<\<omega> . h \<preceq>f ?f \<and> h \<preceq>f ?g" 
      unfolding fun.compat_def compat_in_def by simp
    {
      fix h
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
    } 
    then
    show "fun.compat(fun_upd(f, 0), fun_upd(f, 1)) \<Longrightarrow> False"
      using bexE[OF 1,of False] by auto
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

definition is_funleR :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_funleR(Q,f,g) \<equiv> \<exists>df[Q]. \<exists>dg[Q]. is_domain(Q,f,df) \<and> is_domain(Q,g,dg) \<and> dg \<subseteq> df \<and>
                        (\<forall>j[Q]. j\<in>dg \<longrightarrow> f`j = g`j)"

lemma (in M_basic) funleR_abs: 
  assumes "M(f)" "M(g)"
  shows "funleR(f,g) \<longleftrightarrow> is_funleR(M,f,g)"
  unfolding funleR_def is_funleR_def 
  using assms domain_abs domain_closed[OF \<open>M(f)\<close>]  domain_closed[OF \<open>M(g)\<close>]
  by auto

definition
  relP :: "[i\<Rightarrow>o,[i\<Rightarrow>o,i,i]\<Rightarrow>o,i] \<Rightarrow> o" where
  "relP(M,r,xy) \<equiv> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,xy) \<and> r(M,x,y))"

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

lemma (in M_ctm) Rrel_closed:
  assumes "A\<in>M" 
    "\<And> a. a \<in> nat \<Longrightarrow> rel_fm(a)\<in>formula"
    "\<And> f g . (##M)(f) \<Longrightarrow> (##M)(g) \<Longrightarrow> rel(f,g) \<longleftrightarrow> is_rel(##M,f,g)"
    "\<And> a . a \<in> nat \<Longrightarrow> arity(rel_fm(a)) =succ(a)" 
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


context M_ctm
begin

(* domain(g) \<subseteq> domain(f) \<and> (\<forall> j\<in>domain(g). g`j = f`j) *)
lemma funlerel_in_M: 
  assumes "A\<in>M" 
  shows "funlerel(A) \<in> M"
  unfolding  funlerel_def Rrel_def chleR_def
  sorry

end 


end