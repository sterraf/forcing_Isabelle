theory Edwin imports L_axioms
begin

lemma "\<forall>x\<in>{4,5,6} . 0<x"
proof 
  {
    fix x
    assume "x\<in>{4,4,5,6}"
    then have "0<x" 
      by auto
  }
  then have
    "x \<in> {4, 4, 5, 6} \<Longrightarrow> 0 < x" for x .
  fix x
  assume
    "x \<in> {4,5,6}"
  then have
oops

lemma "{0} \<union> {1} = {0,1}"
proof 
oops  
  
lemma "{x\<in>{0,1,2} . 0<x} = { x #+1 . x\<in>{0,1}}"
  by auto

txt\<open>Proof by contradiction\<close>    
lemma "\<forall>x \<in> nat-{0,1,2}. 2<x"
proof
  fix x
  assume "x\<in> nat-{0,1,2}"
  then have 
    one : "x\<in>nat" "x\<noteq>0" "x\<noteq>1" "x\<noteq>2"
    by auto
  {
    assume "\<not> 2<x"
    with \<open>x\<in>nat\<close>  not_lt_iff_le have "x\<le>2" by simp
    then have "x=0 \<or> x=1 \<or> x=2" 
      unfolding lt_def by auto
    with one have "False" by simp
  }
  then show "2<x" by auto
qed

txt\<open>Direct proof\<close>    
lemma "\<forall>x \<in> nat-{0,1,2}. 2<x"
proof
  fix x
  assume "x\<in> nat-{0,1,2}"
  then have 
    "x\<in>nat" "x\<noteq>0" "x\<noteq>1" "x\<noteq>2"
    by auto
  then have 
    "\<not>(x\<le>2)" 
    unfolding lt_def by auto
  with \<open>x\<in>nat\<close>  show  "2<x" 
    using not_lt_iff_le by simp
qed
  
txt\<open>One-liner\<close>    
lemma "\<forall>x \<in> nat-{0,1,2}. 2<x"
  by (clarsimp simp add:not_lt_iff_le, auto simp add:lt_def)

lemma "\<forall>x \<in> nat-succ(2). 2<x"
  by (clarsimp simp add:not_lt_iff_le, auto simp add:lt_def)

lemma "n\<in>nat \<Longrightarrow> \<forall>x \<in> nat-succ(n). n<x"
  by (clarsimp simp add:not_lt_iff_le, auto simp add:lt_def)
    

lemma lt_dest [dest!] :"i<j \<Longrightarrow> i\<in>j \<and> Ord(j)"  
  by (simp add: lt_def)
    
lemma lt_intro [intro!] : "i\<in>j \<Longrightarrow> Ord(j) \<Longrightarrow> i<j"  
  by (simp add: lt_def)

definition
  Succ :: "i \<Rightarrow> o" where
  "Succ(\<alpha>) == \<exists>\<beta>. Ord(\<beta>) \<and> \<alpha> = succ(\<beta>)"
(*
eps_induct: \<lbrakk> \<And>x. \<forall>y\<in>x. P(y) \<Longrightarrow> P(x) \<rbrakk>  \<Longrightarrow>  P(a)

oadd_0: Ord(?i) \<Longrightarrow> ?i ++ 0 = ?i
oadd_succ: Ord(?j) \<Longrightarrow> ?i ++ succ(?j) = succ(?i ++ ?j)
oadd_Limit: Limit(?j) \<Longrightarrow> ?i ++ ?j = (\<Union>k\<in>?j. ?i ++ k)
*)


lemma 
  "Ord(a) \<Longrightarrow> 0 ++ a = a"
proof (induct a rule:eps_induct)
  case (1 a)
  then show ?case
    proof (cases "a =0")
      case True
      then show ?thesis 
        using oadd_0 by simp
    next
      case False
      then show ?thesis 
        proof (cases "Limit(a)")
          case True
          then have
            "0 ++ a = (\<Union>k\<in>a. 0 ++ k)"
            using oadd_Limit by simp
          also have
            "   ... = (\<Union>k\<in>a. k)" 
            using 1 Ord_in_Ord by simp
          also have 
            "   ... = a" 
            using \<open>Limit(a)\<close> Limit_Union_eq by simp
          finally show ?thesis .
        next
          case False
          then have
            "\<exists>y. y<a \<and> \<not>(succ(y) < a)"
            using 1 \<open>a\<noteq>0\<close> not_lt_iff_le unfolding Limit_def  by simp
          then obtain y where
            "y<a" "\<not>(succ(y) < a)"  "Ord(y)"
             using 1 Ord_in_Ord by auto
          then have
            "succ(y) = a"
            using succ_leI  by blast
          then have 
            "0 ++ a = 0 ++ succ(y)" by simp
          also have
            "   ... = succ(0 ++ y)" 
            using \<open>Ord(y)\<close> oadd_succ  by simp
          also have
            "   ... = succ(y)"
            using 1 \<open>Ord(y)\<close> by  simp
          finally  show ?thesis 
            using \<open>succ(y) = a\<close> by simp
        qed
    qed
qed

lemma 
  assumes "Ord(a)"
  shows "0 ++ a = a" using assms
proof (induct a rule:eps_induct)
  case (1 a)
  then show ?case
  proof -
    consider (a) "a=0" | (b) "a\<noteq>0 \<and> Limit(a)" | (c) "a\<noteq>0 \<and> \<not>Limit(a)" by blast
    then show ?thesis
    proof cases
      case (a)
      then show ?thesis 
        using oadd_0 by simp
    next
      case (b)
      then have
        "0 ++ a = (\<Union>k\<in>a. 0 ++ k)"
        using oadd_Limit by simp
      also have
        "   ... = (\<Union>k\<in>a. k)" 
        using 1 Ord_in_Ord by simp
      also have 
        "   ... = a" 
        using b Limit_Union_eq by simp
      finally show ?thesis .
    next
      case (c)
      then have
        "\<exists>y. y<a \<and> \<not>(succ(y) < a)"
        using 1 c not_lt_iff_le unfolding Limit_def  by simp
      then obtain y where
        "y<a" "\<not>(succ(y) < a)"  "Ord(y)"
        using 1 Ord_in_Ord  by auto
      then have
        "succ(y) = a"
        using succ_leI  by blast
      then have 
        "0 ++ a = 0 ++ succ(y)" by simp
      also have
        "   ... = succ(0 ++ y)" 
        using \<open>Ord(y)\<close> oadd_succ  by simp
      also have
        "   ... = succ(y)"
        using 1 \<open>Ord(y)\<close> by  simp
      finally  show ?thesis 
        using \<open>succ(y) = a\<close> by simp
    qed
  qed
qed

lemma 
  assumes "Ord(a)"
  shows "0++a = a" using assms
proof (induct rule:trans_induct3)
  case 0
  then show ?case using oadd_0 by simp
next
  case (succ y)
  have
    " 0 ++ succ(y) = succ(0 ++ y)" 
    using \<open>Ord(y)\<close> oadd_succ  by simp
  also have
    "   ... = succ(y)"
    using succ  by  simp
  finally show ?case .
next
  case (limit a)
  then have
    "0 ++ a = (\<Union>k\<in>a. 0 ++ k)"
    using oadd_Limit by simp
  also have
    "   ... = (\<Union>k\<in>a. k)" 
    using limit Ord_in_Ord by simp
  also have 
    "   ... = a" 
    using limit Limit_Union_eq by simp
  finally show ?case .
qed
     
lemma 
  assumes "Ord(c)" "Ord(b)" "Ord(a)" 
  shows "a ++ (b ++ c) = (a ++ b) ++ c" 
  using assms
proof (induct rule:trans_induct3)
  case 0
  then have "a++(b++0) = a++b" using  oadd_0  by simp
  also have "... = (a++b)++0" using assms  by simp
  finally show ?case .
next
  case (succ y)
  then have "(a++b)++succ(y) = succ((a++b)++y)" using oadd_succ by simp
  also have "... = succ(a++(b++y))" using succ by simp
  also have "... = a++succ(b++y)" using oadd_succ by simp
  also have "... = a++(b++succ(y))" using \<open>Ord(y)\<close>  oadd_succ by simp
  finally show ?case ..
next
  case (limit c)
  then have "a++b++c=(\<Union>w\<in>c.(a++b++w))" using oadd_Limit by simp
  also have "... = (\<Union>w\<in>c. (a++(b++w)))" using limit by simp
  also have "... = (\<Union>w\<in>b++c. a++w)" (*using limit oadd_Limit oadd_lt_mono apply auto sorry*)
  proof (intro equalityI subsetI)
    fix x
    assume "x \<in> (\<Union>w\<in>c. a ++ (b ++ w))" 
    then obtain w where "w\<in>c" "x\<in> a++(b++w)" using UN_E by auto
    with limit have "b++w\<in>b++c" 
      unfolding Limit_def using oadd_lt_mono (* [of b b]*) by blast
    with \<open>x\<in> a++(b++w)\<close> have "\<exists>v\<in>b++c. x\<in>a++v" by auto
    then show " x \<in> (\<Union>v\<in>b ++ c. a ++ v)" by simp
  next
    fix x
    assume " x \<in> (\<Union>w\<in>b ++ c. a ++ w)"
    then obtain v where "v\<in>b++c" "x\<in>a++v" using UN_E by auto
    then have   "v\<in>(\<Union>w\<in>c. b++w)" using limit oadd_Limit  by auto
    then obtain z where "z\<in>c" "v\<in>b++z" by auto
    then have "a++v\<in>a++(b++z)" using \<open>Ord(a)\<close> \<open>Ord(b)\<close> oadd_lt_mono  by blast
    with \<open>x\<in>a++v\<close> have "x\<in>a++(b++z)" using Ord_trans  by blast
    with \<open>x\<in>a++(b++z)\<close> \<open>z\<in>c\<close> have \<open>\<exists>w\<in>c. x\<in>a++(b++w)\<close> by auto 
    then show "x\<in>(\<Union>w\<in>c. a ++ (b ++ w))"  by simp
  qed
  also have "... = a++(b++c)" using limit oadd_Limit oadd_LimitI by simp
  finally show ?case ..
qed

  
lemma 
  assumes "Ord(c)" "Ord(b)" "Ord(a)" 
  shows "a ++ (b ++ c) = (a ++ b) ++ c" 
  using assms
(*
  In the following proof, it seems that we can't help but following
  the scheme of proof of the induct method. We tried to start with
    
  proof (induct rule:trans_induct3,simp_all)

  and the simplifier ruled out the trivial base and successor cases,
  but then the limit case could not be matched to the remaining goal 
*)  
proof (induct rule:trans_induct3)
  case 0 
  then show ?case by simp
next
  case succ 
  then show ?case by simp
next
  case (limit c) 
   then have "a++b++c=(\<Union>w\<in>c.(a++b++w))" using oadd_Limit by simp
  also have "... = (\<Union>w\<in>c. (a++(b++w)))" using limit by simp
  also have "... = (\<Union>w\<in>b++c. a++w)" (*using limit oadd_Limit oadd_lt_mono apply auto sorry*)
  proof (intro equalityI subsetI)
    fix x
    assume "x \<in> (\<Union>w\<in>c. a ++ (b ++ w))" 
    then obtain w where "w\<in>c" "x\<in> a++(b++w)" using UN_E by auto
    with limit have "b++w\<in>b++c" 
      unfolding Limit_def using oadd_lt_mono (* [of b b]*) by blast
    with \<open>x\<in> a++(b++w)\<close> have "\<exists>v\<in>b++c. x\<in>a++v" by auto
    then show " x \<in> (\<Union>v\<in>b ++ c. a ++ v)" by simp
  next
    fix x
    assume " x \<in> (\<Union>w\<in>b ++ c. a ++ w)"
    then obtain v where "v\<in>b++c" "x\<in>a++v" using UN_E by auto
    then have   "v\<in>(\<Union>w\<in>c. b++w)" using limit oadd_Limit  by auto
    then obtain z where "z\<in>c" "v\<in>b++z" by auto
    then have "a++v\<in>a++(b++z)" using \<open>Ord(a)\<close> \<open>Ord(b)\<close> oadd_lt_mono  by blast
    with \<open>x\<in>a++v\<close> have "x\<in>a++(b++z)" using Ord_trans  by blast
    with \<open>x\<in>a++(b++z)\<close> \<open>z\<in>c\<close> have \<open>\<exists>w\<in>c. x\<in>a++(b++w)\<close> by auto 
    then show "x\<in>(\<Union>w\<in>c. a ++ (b ++ w))"  by simp
  qed
  also have "... = a++(b++c)" using  limit oadd_Limit oadd_LimitI by simp
  finally show ?case ..
qed
  
end
  
