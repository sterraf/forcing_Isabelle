section\<open>Relativization of Finite Functiions\<close>
theory FiniteFun_Relative
  imports
    Arities
    Proper_Extension
    Synthetic_Definition
    Names
    FrecR
begin

subsection\<open>The set of finite binary sequences\<close>

notation nat (\<open>\<omega>\<close>) \<comment> \<open>TODO: already in ZF Library\<close>

text\<open>We implement the poset for adding one Cohen real, the set 
$2^{<\omega}$ of finite binary sequences.\<close>

definition
  seqspace :: "[i,i] \<Rightarrow> i" (\<open>_\<^bsup><_\<^esup>\<close> [100,1]100) where
  "B\<^bsup><\<alpha>\<^esup> \<equiv> \<Union>n\<in>\<alpha>. (n\<rightarrow>B)"

lemma seqspaceI[intro]: "n\<in>\<alpha> \<Longrightarrow> f:n\<rightarrow>B \<Longrightarrow> f\<in>B\<^bsup><\<alpha>\<^esup>"
  unfolding seqspace_def by blast

lemma seqspaceD[dest]: "f\<in>B\<^bsup><\<alpha>\<^esup> \<Longrightarrow> \<exists>n\<in>\<alpha>. f:n\<rightarrow>B"
  unfolding seqspace_def by blast

\<comment> \<open>FIXME: Now this is too particular (only for \<^term>\<open>\<omega>\<close>-sequences.
  A relative definition for \<^term>\<open>seqspace\<close> would be appropriate.\<close>

schematic_goal seqspace_fm_auto:
  assumes 
    "i \<in> nat" "j \<in> nat" "h\<in>nat" "env \<in> list(A)"
  shows 
    "(\<exists>om\<in>A. omega(##A,om) \<and> nth(i,env) \<in> om \<and> is_funspace(##A, nth(i,env), nth(h,env), nth(j,env))) \<longleftrightarrow> (A, env \<Turnstile> (?sqsprp(i,j,h)))"
  unfolding is_funspace_def 
  by (insert assms ; (rule iff_sats | simp)+)

synthesize "seqspace_rep" from_schematic seqspace_fm_auto

locale M_seqspace =  M_trancl +
  assumes 
    seqspace_replacement: "M(B) \<Longrightarrow> strong_replacement(M,\<lambda>n z. n\<in>nat \<and> is_funspace(M,n,B,z))"
begin

lemma seqspace_closed:
  "M(B) \<Longrightarrow> M(B\<^bsup><\<omega>\<^esup>)"
  unfolding seqspace_def using seqspace_replacement[of B] RepFun_closed2 
  by simp

lemma FiniteFun_fst_type:
  assumes "h\<in>A-||>B" "p\<in>h"
  shows  "fst(p)\<in>domain(h)"
  using assms by(induct h, auto)


lemma FinFun_closed:
  "M(A) \<Longrightarrow> M(B) \<Longrightarrow> M(\<Union>{n\<rightarrow>A\<times>B . n\<in>\<omega>})"
  using cartprod_closed seqspace_closed 
  unfolding seqspace_def by simp

definition cons_like :: "i \<Rightarrow> i \<Rightarrow> o" where
  "cons_like(n,f) \<equiv> \<forall> i \<in> n. \<forall> j. j\<in>i \<longrightarrow> fst(f`i) \<noteq> fst(f`j)"


lemma cons_like_lt : 
  assumes "n\<in>\<omega>" "f\<in>succ(n)\<rightarrow>A\<times>B" "cons_like(succ(n),f)"
  shows "restrict(f,n)\<in>n\<rightarrow>A\<times>B" "cons_like(n,restrict(f,n))"
  using assms
proof (auto simp add: le_imp_subset restrict_type2)
  { 
    fix i j
    assume "i\<in>n" "j\<in>i" 
    with \<open>n\<in>_\<close>
    have "j\<in>n" using Ord_trans[of j] by simp
    with \<open>cons_like(succ(n),f)\<close>  \<open>j\<in>n\<close> \<open>i\<in>n\<close> \<open>j\<in>i\<close>
    have "fst(restrict(f,n)`i) \<noteq> fst(restrict(f,n)`j)"
      using restrict_if unfolding cons_like_def by auto
  }
  then show "cons_like(n,restrict(f,n))" 
    unfolding cons_like_def by auto
qed


definition iso_FinFun :: "[i,i,i,i,i] \<Rightarrow> o" where
  "iso_FinFun(A,B,n,f,g) \<equiv> 
    (\<forall> i \<in> n . f`i \<in> g) \<and> (\<forall> ab \<in> g. (\<exists> i\<in>n. f`i=ab))"

lemma iso_consD : 
  assumes"n\<in>\<omega>" "f\<in>A-||> B" "ab\<in>A\<times>B"  "g\<in>n\<rightarrow>A\<times>B"  "iso_FinFun(A,B,n,g,cons(ab,f))"
  shows "\<exists> x\<in>nat. n=succ(x)"
  using assms unfolding iso_FinFun_def by(induct n, auto)


lemma Iso_intro1:
  assumes "f \<in> (A -||> B)"
  shows "\<exists>n\<in>\<omega> . \<exists>g\<in>n\<rightarrow>A\<times>B. iso_FinFun(A,B,n,g,f) \<and> cons_like(n,g)"
  using assms
proof(induct f,force simp add:emptyI iso_FinFun_def cons_like_def)
  case (consI a b h)
  then obtain n g where
    HI: "n\<in>\<omega>" "g\<in>n\<rightarrow>A\<times>B" "iso_FinFun(A,B,n,g,h)" "cons_like(n,g)" by auto
  let ?G="\<lambda> i \<in> succ(n) . if i=n then <a,b> else g`i"
  from HI \<open>a\<in>_\<close> \<open>b\<in>_\<close>
  have G: "?G \<in> succ(n)\<rightarrow>A\<times>B" 
    by (auto intro:lam_type) 
  have "iso_FinFun(A,B,succ(n),?G,cons(<a,b>,h))"
    unfolding iso_FinFun_def 
  proof(intro conjI)
    {
      fix i
      assume "i\<in>succ(n)" 
      then consider "i=n" | "i\<in>n\<and>i\<noteq>n" by auto
      then have "?G ` i \<in> cons(<a,b>,h)"
        using HI
        by(cases,simp;auto simp add:HI iso_FinFun_def)
    }
    then show "\<forall>i\<in>succ(n). ?G ` i \<in> cons(\<langle>a, b\<rangle>, h)" ..
  next
    { fix ab'
      assume "ab' \<in> cons(<a,b>,h)"
      then
      consider  "ab' = <a,b>" | "ab' \<in> h" using cons_iff by auto
      then
      have "\<exists>i \<in> succ(n) . ?G`i = ab'" unfolding iso_FinFun_def 
      proof(cases,simp)
        case 2
        with HI obtain i
          where "i\<in>n" "g`i=ab'" unfolding iso_FinFun_def by auto
        with HI show ?thesis using  ltI[OF \<open>i\<in>_\<close>] by auto
      qed
    }
    then
    show "\<forall>ab\<in>cons(\<langle>a, b\<rangle>, h). \<exists>i\<in>succ(n). ?G`i = ab"  ..
  qed
  with HI G
  have 1: "?G\<in>succ(n)\<rightarrow>A\<times>B" "iso_FinFun(A,B,succ(n),?G,cons(<a,b>,h))" "succ(n)\<in>\<omega>" by simp_all
  have "cons_like(succ(n),?G)" 
  proof -
    {
      fix i j
      assume "i\<in>succ(n)" "j\<in>i"
      with \<open>n\<in>_\<close>
      have "j\<in>n" using Ord_trans[of j _ n] by auto
      from \<open>i\<in>_\<close> consider (a) "i=n \<and> i\<notin>n" | (b) "i\<in>n" by auto
      then
      have " fst(?G`i) \<noteq> fst(?G`j)"
      proof(cases)
        case a
        with \<open>j\<in>n\<close> HI
        have "?G`i=<a,b>" "?G`j=g`j" "g`j\<in>h" 
          unfolding iso_FinFun_def by auto
        with \<open>a\<notin>_\<close> \<open>h\<in>_\<close> 
        show ?thesis using  FiniteFun_fst_type by auto
      next
        case b
        with \<open>i\<in>n\<close> \<open>j\<in>i\<close> \<open>j\<in>n\<close> HI
        show ?thesis unfolding cons_like_def using mem_not_refl by auto
      qed
    }
    then show ?thesis unfolding cons_like_def by auto
  qed
  with 1 show ?case by auto
qed


definition TO :: "i \<Rightarrow> i" where
  "TO(f) \<equiv> {f`i . i \<in> domain(f)}"


lemma IsoD_eq : 
  assumes "n\<in>\<omega>" "g\<in>n\<rightarrow>A\<times>B" "f\<in>A-||> B" "iso_FinFun(A,B,n,g,f)"
  shows "TO(g) = f"
proof
  {
    fix ab
    assume "ab\<in>TO(g)"
    with assms
    obtain i where "i\<in>n" "g`i=ab" "ab\<in>A\<times>B"
      unfolding TO_def using domain_of_fun by auto
    with assms
    have "ab\<in>f" unfolding iso_FinFun_def by auto
  }
  then show "TO(g) \<subseteq> f" by auto
next
  {
    fix ab
    assume "ab\<in>f"
    with assms
    obtain i where "i\<in>n" "g`i=ab" "ab\<in>A\<times>B"
      unfolding iso_FinFun_def by auto
    with assms have "ab \<in> TO(g)" unfolding TO_def using domain_of_fun by auto
  }
  then show "f \<subseteq> TO(g)" ..
qed

lemma TO_succ_eq :
  assumes "n\<in>\<omega>" "f\<in>succ(n) \<rightarrow> A"
  shows "TO(f) = cons(f`n,TO(restrict(f,n)))"
  using assms domain_restrict domain_of_fun 
  unfolding TO_def by auto

lemma Iso_Intro2:
  assumes "n\<in>\<omega>" "f\<in>n\<rightarrow>A\<times>B" "cons_like(n,f)"
  shows "TO(f) \<in> (A -||> B) \<and> iso_FinFun(A,B,n,f,TO(f))" 
  using assms
proof(induct n  arbitrary:f rule:nat_induct)
  case 0
  fix f
  assume "f\<in>0\<rightarrow>A\<times>B"
  then
  have "f=0" by simp
  then have "TO(f)=0" unfolding TO_def by simp 
  then show "TO(f) \<in> (A -||> B) \<and> iso_FinFun(A,B,0,f,TO(f))" 
    using emptyI unfolding iso_FinFun_def by simp 
next
  case (succ x)
  fix f
  let ?f'="restrict(f,x)"
  assume "f\<in>succ(x)\<rightarrow>A\<times>B" "cons_like(succ(x),f)"
  with succ.hyps \<open>f\<in>_\<close>
  have "cons_like(x,?f')" "?f' \<in> x\<rightarrow>A\<times>B" "f`x\<in>A\<times>B" 
    using cons_like_lt succI1 apply_funtype by simp_all
  with succ.hyps  \<open>?f'\<in>_\<close> \<open>x\<in>\<omega>\<close>
  have HI: "TO(?f') \<in> A -||> B" (is "(?h) \<in> _") "iso_FinFun(A,B,x,?f',TO(?f'))"
    by auto
  then
  have "fst(f`x) \<notin> domain(?h)" 
  proof -
    {assume "fst(f`x) \<in> domain(?h)"
      with HI \<open>x\<in>_\<close> obtain i b
        where "i\<in>x" "<fst(?f'`i),b>\<in>?h" "i<x" "fst(f`x) = fst(?f'`i)"
        unfolding iso_FinFun_def using ltI by auto
      with \<open>cons_like(succ(x),f)\<close> 
      have False
        unfolding cons_like_def by auto
    }then show ?thesis ..
  qed
  with HI assms \<open>f`x\<in>_\<close>
  have "cons(f`x,?h) \<in> A-||>B" (is "?h' \<in>_") using consI by auto
  have "iso_FinFun(A,B,succ(x),f,?h')"
    unfolding iso_FinFun_def
  proof
    { fix i
      assume "i\<in>succ(x)"
      with \<open>x\<in>_\<close> consider (a) "i=x"| (b) "i\<in>x\<and>i\<noteq>x" by auto
      then have "f`i\<in> ?h'" 
      proof(cases,simp)
        case b
        with \<open>iso_FinFun(_,_,_,?f',?h)\<close> 
        show ?thesis unfolding iso_FinFun_def by simp
      qed
    }
    then show "\<forall>i\<in>succ(x). f ` i \<in> cons(f ` x, ?h)" ..
  next
    {
      fix ab
      assume "ab\<in>?h'"
      then consider "ab=f`x" | "ab \<in> ?h" using cons_iff by auto
      then
      have "\<exists>i \<in> succ(x) . f`i = ab" unfolding iso_FinFun_def 
      proof(cases,simp)
        case 2
        with HI obtain i
          where 2:"i\<in>x" "?f'`i=ab"  unfolding iso_FinFun_def by auto
        with \<open>x\<in>_\<close>
        have "i\<noteq>x" "i\<in>succ(x)" using  ltI[OF \<open>i\<in>_\<close>] by auto
        with 2 HI show ?thesis by auto
      qed
    } then show "\<forall>ab\<in>cons(f ` x, ?h). \<exists>i\<in>succ(x). f ` i = ab" ..
  qed
  with \<open>?h'\<in>_\<close>
  show "TO(f) \<in> A -||>B \<and> iso_FinFun(A,B,succ(x),f,TO(f))" 
    using TO_succ_eq[OF \<open>x\<in>_\<close> \<open>f\<in>_\<close>,symmetric] by auto
qed

lemma Iso_Intro2':
  assumes "n\<in>\<omega>" "f\<in>n\<rightarrow>A\<times>B" "cons_like(n,f)"
  shows "\<exists> g \<in> (A -||> B) . iso_FinFun(A,B,n,f,g)" 
  using assms Iso_Intro2 by blast

definition H :: "[i,i] \<Rightarrow> i" where
  "H(A,B) \<equiv> {f \<in> (A\<times>B)\<^bsup><\<omega>\<^esup> . cons_like(domain(f),f) }"


lemma ISO_eq :
  shows "A-||>B = {TO(h) . h \<in> H(A,B) } " 
    (is "?Y=?X")
proof
  {
    fix f
    assume "f\<in> ?Y"
    then obtain n g where 
      1: "n\<in>\<omega>" "g\<in>n\<rightarrow>A\<times>B" "iso_FinFun(A,B,n,g,f)" "cons_like(n,g)"
      using Iso_intro1 by blast
    with \<open>f\<in>_\<close>
    have "cons_like(n,g)" "f=TO(g)" "domain(g) = n" "g\<in>H(A,B)"
      using  IsoD_eq domain_of_fun
      unfolding H_def
      by auto
    with 1 have "f\<in>?X" 
      by auto
  } then show "?Y\<subseteq>?X" ..
next
  {
    fix g
    assume "g\<in> ?X"
    then obtain f where 
      1: "f\<in>H(A,B)" "g=TO(f)" "cons_like(domain(f),f)"
      using RepFun_iff unfolding H_def by auto
    then obtain n where "n\<in>\<omega>" "f\<in>n\<rightarrow>A\<times>B" "domain(f) = n"
      unfolding H_def using domain_of_fun by force
    with 1
    have "g\<in>?Y"
      using Iso_Intro2 by auto
  } then show "?X\<subseteq>?Y" ..
qed

reldb_add "fst" "is_fst"
relativize "cons_like" "cons_like_rel"
relativize "TO" "TO_r"
\<comment> \<open>
TODO:

1. Prove M(H), should be easy because we know M(A\<times>B^\<omega>).
2. Prove M({TO(f) . f\<in>H}), should be easy because TO is trivial.
\<close>

end (* M_seqspace *)


end