theory Forcing_Main
  imports 
  (* minimum infrastructure to define the formulas *)
  Forcing_Data
  Synthetic_Definition
  (* Top elements of the development *)
  Choice_Axiom
  Ordinals_In_MG
  Succession_Poset

begin

schematic_goal ZF_union_auto:
    "Union_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?zfunion(i,j,h)))"
  unfolding Union_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_union_fm" from_schematic "ZF_union_auto"

schematic_goal ZF_power_auto:
    "power_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?zfpow(i,j,h)))"
  unfolding power_ax_def powerset_def subset_def
  by ((rule sep_rules | simp)+)

synthesize "ZF_power_fm" from_schematic "ZF_power_auto"

schematic_goal ZF_pairing_auto:
    "upair_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?zfpair(i,j,h)))"
  unfolding upair_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_pairing_fm" from_schematic "ZF_pairing_auto"

schematic_goal ZF_foundation_auto:
    "foundation_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?zfpow(i,j,h)))"
  unfolding foundation_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_foundation_fm" from_schematic "ZF_foundation_auto"

schematic_goal ZF_extensionality_auto:
    "extensionality(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?zfpow(i,j,h)))"
  unfolding extensionality_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_extensionality_fm" from_schematic "ZF_extensionality_auto"

schematic_goal ZF_infinity_auto:
    "infinity_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?\<phi>(i,j,h)))"
  unfolding infinity_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_infinity_fm" from_schematic "ZF_infinity_auto"

schematic_goal ZF_choice_auto:
    "choice_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?\<phi>(i,j,h)))"
  unfolding choice_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_choice_fm" from_schematic "ZF_choice_auto"

syntax
  "_choice" :: "i"  ("AC")
translations
  "AC" \<rightharpoonup> "CONST ZF_choice_fm"


lemmas ZFC_fm_defs = ZF_extensionality_fm_def ZF_foundation_fm_def ZF_pairing_fm_def
              ZF_union_fm_def ZF_infinity_fm_def ZF_power_fm_def ZF_choice_fm_def

lemmas ZFC_fm_sats = ZF_extensionality_auto ZF_foundation_auto ZF_pairing_auto
              ZF_union_auto ZF_infinity_auto ZF_power_auto ZF_choice_auto

definition
  ZF_fin :: "i" where
  "ZF_fin \<equiv> { ZF_extensionality_fm, ZF_foundation_fm, ZF_pairing_fm,
              ZF_union_fm, ZF_infinity_fm, ZF_power_fm }"

definition
  ZFC_fin :: "i" where
  "ZFC_fin \<equiv> ZF_fin \<union> {ZF_choice_fm}"

lemma ZFC_fin_type : "ZFC_fin \<subseteq> formula"
  unfolding ZFC_fin_def ZF_fin_def ZFC_fm_defs by (auto)

consts 
  nForall :: "[i,i] \<Rightarrow> i"
primrec
  "nForall(0,p) = p"
  "nForall(succ(n),p) = Forall(nForall(n,p))" 

lemma nForall_type [TC]: 
      "\<lbrakk> n \<in> nat; p \<in> formula \<rbrakk> \<Longrightarrow> nForall(n,p) \<in> formula"
  by (induct set:nat, auto)

lemma nForall_assoc: "n\<in>nat \<Longrightarrow> nForall(succ(n),p) = nForall(n,Forall(p))"
  by (induct set:nat; simp)

(* declare nForall.simps(2)[simp del] nForall_assoc[simp] *)

definition
  g_separation_fm :: "i \<Rightarrow> i \<Rightarrow> i" where
  "g_separation_fm(n,p) == nForall(n, 
                              Forall(Exists(Forall(
                              Iff(Member(0,1),And(Member(0,2),
                                              incr_bv1^2(p)))))))"

lemma g_separation_fm_type [TC]: "n \<in> nat \<Longrightarrow> p \<in> formula \<Longrightarrow> g_separation_fm(n,p) \<in> formula"
  by (simp add: g_separation_fm_def)

lemma g_separation_fm_zero [simp]: 
  assumes"p \<in> formula" 
  shows "g_separation_fm(0,p) = Forall(Exists(Forall(
                              Iff(Member(0,1),And(Member(0,2),
                                              incr_bv1^2(p))))))"
  using assms
  by (simp add: g_separation_fm_def)

lemma g_separation_fm_succ [simp]:
  assumes "n \<in> nat" "p \<in> formula" 
  shows "g_separation_fm(succ(n),p) = Forall(g_separation_fm(n,p))"
  using assms
  by (simp add: g_separation_fm_def)

lemmas ZF_separation_simps = formula_add_params1[of _ 2 _ _ "[_,_]" ]

lemma last_init_eq :
  assumes "l \<in> list(A)" "length(l) = succ(n)"
  shows "\<exists> a\<in>A. \<exists>l'\<in>list(A). l = l'@[a]"
proof-
  from \<open>l\<in>_\<close> \<open>length(_) = _\<close>
  have "rev(l) \<in> list(A)" "length(rev(l)) = succ(n)"
    by simp_all
  then
  obtain a l' where "a\<in>A" "l'\<in>list(A)" "rev(l) = Cons(a,l')"
    by (cases;simp)
  then
  have "l = rev(l') @ [a]" "rev(l') \<in> list(A)"
    using rev_rev_ident[OF \<open>l\<in>_\<close>] by auto
  with \<open>a\<in>_\<close>
  show ?thesis by blast
qed

lemma take_drop_eq :
  assumes "l\<in>list(M)"
  shows "\<And> n . n < succ(length(l)) \<Longrightarrow> l = take(n,l) @ drop(n,l)"
  using \<open>l\<in>list(M)\<close>
proof induct
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
  proof -
    {
      fix i
      assume "i<succ(succ(length(l)))"
      with \<open>l\<in>list(M)\<close>
      consider (lt) "i = 0" | (eq) "\<exists>k\<in>nat. i = succ(k) \<and> k < succ(length(l))"
        using \<open>l\<in>list(M)\<close>  le_natI nat_imp_quasinat
        by (cases rule:nat_cases[of i];auto)
      then
      have "take(i,Cons(a,l)) @ drop(i,Cons(a,l)) = Cons(a,l)"
        using Cons
        by (cases;auto)
    }
    then show ?thesis using Cons by auto
  qed
qed

lemma list_split :
assumes "n \<le> succ(length(rest))" "rest \<in> list(M)"
shows  "\<exists>re\<in>list(M). \<exists>st\<in>list(M). rest = re @ st \<and> length(re) = pred(n)"
proof -
  from assms
  have "pred(n) \<le> length(rest)"
    using pred_mono[OF _ \<open>n\<le>_\<close>] pred_succ_eq by auto
  with \<open>rest\<in>_\<close>
  have "pred(n)\<in>nat" "rest = take(pred(n),rest) @ drop(pred(n),rest)" (is "_ = ?re @ ?st")
    using take_drop_eq[OF \<open>rest\<in>_\<close>] le_natI by auto
  then
  have "length(?re) = pred(n)" "?re\<in>list(M)" "?st\<in>list(M)"
    using length_take[rule_format,OF _ \<open>pred(n)\<in>_\<close>] \<open>pred(n) \<le> _\<close> \<open>rest\<in>_\<close>
    unfolding min_def
    by auto
  then
  show ?thesis
    using rev_bexI[of _ _ "\<lambda> re. \<exists>st\<in>list(M). rest = re @ st \<and> length(re) = pred(n)"]
      \<open>length(?re) = _\<close> \<open>rest = _\<close>
    by auto
qed

lemma sats_nForall:
  assumes
    "\<phi> \<in> formula"
  shows
    "n\<in>nat \<Longrightarrow> ms \<in> list(M) \<Longrightarrow>
       (M, ms \<Turnstile> (nForall(n,\<phi>)) \<longleftrightarrow>
       (\<forall>rest \<in> list(M). length(rest) = n \<longrightarrow> (M, rest @ ms \<Turnstile> \<phi>)))"
proof (induct n arbitrary:ms set:nat)
  case 0
  with assms
  show ?case by simp
next
  case (succ n)
  have "(\<forall>rest\<in>list(M). length(rest) = succ(n) \<longrightarrow> P(rest,n)) \<longleftrightarrow>
        (\<forall>t\<in>M. \<forall>res\<in>list(M). length(res) = n \<longrightarrow> P(res @ [t],n))"
    if "n\<in>nat" for n P sorry
  from this[of _ "\<lambda>rest _. (M, rest @ ms \<Turnstile> \<phi>)"] \<open>n\<in>nat\<close>
  have "(\<forall>rest\<in>list(M). length(rest) = succ(n) \<longrightarrow> M, rest @ ms \<Turnstile> \<phi>) \<longleftrightarrow>
        (\<forall>t\<in>M. \<forall>res\<in>list(M). length(res) = n \<longrightarrow>  M, (res @ [t]) @ ms \<Turnstile> \<phi>)"
    by simp
    with assms succ(1,3) succ(2)[of "Cons(_,ms)"]
  show ?case
    using arity_sats_iff[of \<phi> _ M "Cons(_, ms @ _)"] app_assoc
    by (simp)
qed

definition
  sep_body_fm :: "i \<Rightarrow> i" where
  "sep_body_fm(p) == Forall(Exists(Forall(
                           Iff(Member(0,1),And(Member(0,2),
                                    incr_bv1^2(p))))))"

lemma sep_body_fm_type [TC]: "p \<in> formula \<Longrightarrow> sep_body_fm(p) \<in> formula"
  by (simp add: sep_body_fm_def)

lemma sats_sep_body_fm: 
  assumes
    "\<phi> \<in> formula" "ms\<in>list(M)" "rest\<in>list(M)"
  shows
    "M, rest @ ms \<Turnstile> sep_body_fm(\<phi>) \<longleftrightarrow> 
     (\<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> M, Cons(x, rest @ ms) \<Turnstile> \<phi>)"
  using assms ZF_separation_simps unfolding sep_body_fm_def by simp

definition
  G_separation_fm :: "i \<Rightarrow> i \<Rightarrow> i" where
  "G_separation_fm(n,p) == nForall(n,sep_body_fm(p))"

lemma G_separation_fm_type [TC]: "n \<in> nat \<Longrightarrow> p \<in> formula \<Longrightarrow> G_separation_fm(n,p) \<in> formula"
  by (simp add: G_separation_fm_def)

lemma sats_G_separation_fm_iff:
  assumes   
    "\<phi> \<in> formula" "n\<in>nat" "ms \<in> list(M)"
  shows
    "M, ms \<Turnstile> (G_separation_fm(n,\<phi>)) \<longleftrightarrow>
      (\<forall>rest\<in>list(M). length(rest) = n \<longrightarrow>
         (\<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> (M, [x] @ rest @ ms \<Turnstile> \<phi>)))"
  using sats_nForall[OF _ assms(2,3), of "sep_body_fm(\<phi>)"] assms 
    sats_sep_body_fm
  unfolding G_separation_fm_def by simp 

lemma sats_g_separation_fm_imp:
  assumes   
    "\<phi> \<in> formula" 
  shows
    "n\<in>nat \<Longrightarrow> ms \<in> list(M) \<Longrightarrow> rest \<in> list(M) \<Longrightarrow> length(rest) = n \<Longrightarrow>
     arity(\<phi>) \<le> length(ms) #+ n #+ 1 \<Longrightarrow> M, ms \<Turnstile> (g_separation_fm(n,\<phi>)) \<Longrightarrow>
    \<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> (M, [x] @ rest @ ms \<Turnstile> \<phi>)"
proof (induct n arbitrary:ms rest set:nat)
  case 0
  with assms
  show ?case
    using ZF_separation_simps        
    using arity_sats_iff[of \<phi> rest M "Cons(_,ms)"]
    by simp
next
  case (succ n)
  from \<open>rest \<in> list(M)\<close> \<open>length(rest) = succ(n)\<close>
  obtain res t where "t\<in>M" "res\<in>list(M)" "rest=res @ [t]"
    using last_init_eq[OF \<open>rest\<in>_\<close> \<open>length(_) = _\<close>] by auto
  with assms succ(1,3-7) succ(2)[of "Cons(t,ms)" res]
  show ?case
    using ZF_separation_simps
      arity_sats_iff[of \<phi> "[t]" M "Cons(_, ms @ res)"] app_assoc
    by (simp)
qed

definition
  ZF_separation_fm :: "i \<Rightarrow> i" where
  "ZF_separation_fm(p) == G_separation_fm(pred(arity(p)),p)"

lemma ZF_separation_fm_type [TC]: "p \<in> formula \<Longrightarrow> ZF_separation_fm(p) \<in> formula"
  by (simp add: ZF_separation_fm_def)

lemma sats_ZF_separation_imp:
  assumes     
    "\<phi> \<in> formula" "rest \<in> list(M)" "M, [] \<Turnstile> (ZF_separation_fm(\<phi>))"
    "arity(\<phi>) \<le> succ(length(rest))"   
  shows
    "\<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> (M, [x] @ rest \<Turnstile> \<phi>)"
proof -
  obtain re st where "re\<in>list(M)" "st\<in>list(M)" 
    "rest = re @ st" "length(re) = Arith.pred(arity(\<phi>))"
    using list_split[OF \<open>arity(\<phi>) \<le> _\<close> \<open>rest\<in>_\<close>] by force
  moreover from \<open>\<phi>\<in>_\<close>
  have "arity(\<phi>) \<le> succ(Arith.pred(arity(\<phi>)))"
   using succpred_leI by simp
  moreover
  note assms
  ultimately
  show ?thesis
    using
      sats_g_separation_fm_imp[of \<phi> "Arith.pred(arity(\<phi>))" "[]" M re]
      arity_sats_iff[of \<phi> st M "Cons(_,re)"]
    unfolding ZF_separation_fm_def G_separation_fm_def sep_body_fm_def g_separation_fm_def
    by simp
qed

lemma sats_ZF_separation_fm_iff:
  "(\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p))))
   \<longleftrightarrow>
   (\<forall>\<phi>\<in>formula. \<forall>env\<in>list(M). arity(\<phi>) \<le> 1 #+ length(env) \<longrightarrow>
                    separation(##M,\<lambda>x. sats(M,\<phi>,[x] @ env)))"
proof (intro iffI ballI impI)
  assume "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))"
  show "separation(##M, \<lambda>x. M, [x] @ env \<Turnstile> \<phi>)" 
    if "env \<in> list(M)" "\<phi> \<in> formula" "arity(\<phi>) \<le> 1 #+ length(env)" for \<phi> env
    using that
  proof (induct)
    case Nil
    moreover from this
    have "Arith.pred(arity(\<phi>)) = 0" 
      using pred_le[of _ 0] by (simp)
    moreover from \<open>\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))\<close> and Nil
    have "M, [] \<Turnstile> (ZF_separation_fm(\<phi>))" by simp
    ultimately
    show ?case 
      using ZF_separation_simps
      unfolding separation_def ZF_separation_fm_def G_separation_fm_def sep_body_fm_def
      by simp
  next
    case (Cons a l)
    then 
    have "arity(\<phi>)\<in>nat" by simp
    then
    show ?case
    proof (induct "arity(\<phi>)")
      case 0
      moreover from this
      have "l\<in>list(M) \<Longrightarrow> a\<in>M \<Longrightarrow> arity(\<phi>) \<le> length(Cons(a,l))" 
           "n\<in>nat \<Longrightarrow> arity(\<phi>) \<le> n" for n a l by simp_all
      note Cons
      moreover from \<open>\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))\<close> and this
      have "M, [] \<Turnstile> (ZF_separation_fm(\<phi>))" by simp
      moreover from calculation
      have "\<forall>x\<in>M. \<exists>xa\<in>M. \<forall>xb\<in>M. xb \<in> xa \<longleftrightarrow> xb \<in> x \<and> M, [xb] \<Turnstile> \<phi>"
        using ZF_separation_simps 
        unfolding ZF_separation_fm_def G_separation_fm_def sep_body_fm_def
        by simp
      with Cons \<open>\<And>n. n\<in>nat \<Longrightarrow> arity(\<phi>) \<le> n\<close>
      show ?case
        using arity_sats_iff[of _ "Cons(a,l)" M, OF _ _ _ \<open>_ \<Longrightarrow> arity(\<phi>) \<le> length([_])\<close>]
        unfolding separation_def
        by simp
    next
      case (succ n)
      then
      have "n \<in> nat"
        "n \<equiv> arity(\<phi>) \<Longrightarrow> separation(\<lambda>a. (##M)(a), \<lambda>x. M, [x] @ Cons(a, l) \<Turnstile> \<phi>)" by simp_all
      moreover 
      note Cons
      moreover from \<open>\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))\<close> and this
      have "M, [] \<Turnstile> (ZF_separation_fm(\<phi>))" by simp
      ultimately
      show ?case
      using sats_ZF_separation_imp
      unfolding separation_def
      by (simp)
    qed
  qed
next
  assume asm:"\<forall>\<phi>\<in>formula. \<forall>env\<in>list(M). arity(\<phi>) \<le> 1 #+ length(env)
           \<longrightarrow> separation(##M, \<lambda>x. M, [x] @ env \<Turnstile> \<phi>)"
  show "\<phi>\<in>formula \<Longrightarrow> M, [] \<Turnstile> (ZF_separation_fm(\<phi>))" for \<phi>
  proof -
    assume "\<phi>\<in>formula"
    with asm
    have "separation(##M, \<lambda>x. M, [x] @ env \<Turnstile> \<phi>)" 
      if "arity(\<phi>) \<le> 1 #+ length(env)" "env\<in>list(M)" for env
      using that by simp
    then
    have "\<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> M, Cons(x,env) \<Turnstile> \<phi>"
      if "arity(\<phi>) \<le> 1 #+ length(env)" "env\<in>list(M)" for env
      using that unfolding separation_def by simp
    moreover
    have "\<forall>rest\<in>list(M). length(rest) = Arith.pred(arity(\<phi>)) \<longrightarrow> 
        (\<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> M, Cons(x, rest) \<Turnstile> \<phi>)"
    proof (intro ballI, intro impI)
      fix rest
      assume "rest \<in> list(M)" "length(rest) = Arith.pred(arity(\<phi>))"
      moreover from this and \<open>\<phi>\<in>_\<close>
      have "arity(\<phi>) \<le> 1 #+ length(rest)"
        using succpred_leI by simp
      moreover
      note \<open>\<lbrakk>_;_\<rbrakk>\<Longrightarrow> \<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> M, Cons(x,rest) \<Turnstile> \<phi>\<close>
      ultimately
      show "\<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> M, Cons(x, rest) \<Turnstile> \<phi>" by simp
    qed
    moreover
    note \<open>\<phi>\<in>_\<close>
    ultimately
    show "M, [] \<Turnstile> ZF_separation_fm(\<phi>)"
      using sats_G_separation_fm_iff
      unfolding ZF_separation_fm_def
      by simp
  qed
qed

schematic_goal sats_univalent_fm_auto:
  assumes 
    (*    Q_iff_sats:"\<And>a b z env aa bb. nth(a,Cons(z,env)) = aa \<Longrightarrow> nth(b,Cons(z,env)) = bb \<Longrightarrow> z\<in>A 
          \<Longrightarrow> aa \<in> A \<Longrightarrow> bb \<in> A \<Longrightarrow> env\<in> list(A) \<Longrightarrow> 
                 Q(aa,bb) \<longleftrightarrow> (A, Cons(z,env) \<Turnstile> (Q_fm(a,b)))" \<comment> \<open>using only one formula\<close> *)
    Q_iff_sats:"\<And>x y z. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z\<in>A \<Longrightarrow> 
                 Q(x,z) \<longleftrightarrow> (A,Cons(z,Cons(y,Cons(x,env))) \<Turnstile> Q1_fm)"
       "\<And>x y z. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z\<in>A \<Longrightarrow> 
                 Q(x,y) \<longleftrightarrow> (A,Cons(z,Cons(y,Cons(x,env))) \<Turnstile> Q2_fm)"
    and 
    asms: "nth(i,env) = B" "i \<in> nat" "env \<in> list(A)"
  shows
    "univalent(##A,B,Q) \<longleftrightarrow> sats(A,?ufm(i),env)"
  unfolding univalent_def 
  by (insert asms; (rule sep_rules Q_iff_sats | simp)+)
  
synthesize "univalent_fm" from_schematic "sats_univalent_fm_auto"

lemma univalent_fm_type [TC]: "q1\<in> formula \<Longrightarrow> q2\<in>formula \<Longrightarrow> i\<in>nat \<Longrightarrow> 
  univalent_fm(q2,q1,i) \<in>formula"
  by (simp add:univalent_fm_def)

definition
  swap_vars :: "i\<Rightarrow>i" where
  "swap_vars(\<phi>) \<equiv> 
      Exists(Exists(And(Equal(0,3),And(Equal(1,2),iterates(\<lambda>p. incr_bv(p)`2 , 2, \<phi>)))))" 

lemma swap_vars_type[TC] :
  "\<phi>\<in>formula \<Longrightarrow> swap_vars(\<phi>) \<in>formula" 
  unfolding swap_vars_def by simp

lemma sats_swap_vars :
  "[x,y] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> 
    sats(M, swap_vars(\<phi>),[x,y] @ env) \<longleftrightarrow> sats(M, \<phi>,[y,x] @ env)"
  unfolding swap_vars_def
  using sats_incr_bv_iff [of _ _ M _ "[y,x]"] by simp

definition
  univalent_Q1 :: "i \<Rightarrow> i" where
  "univalent_Q1(\<phi>) \<equiv> incr_bv1(swap_vars(\<phi>))"

definition
  univalent_Q2 :: "i \<Rightarrow> i" where
  "univalent_Q2(\<phi>) \<equiv> incr_bv(swap_vars(\<phi>))`0"

lemma univalent_Qs_type [TC]: 
  assumes "\<phi>\<in>formula"
  shows "univalent_Q1(\<phi>) \<in> formula" "univalent_Q2(\<phi>) \<in> formula"
  unfolding univalent_Q1_def univalent_Q2_def using assms by simp_all

lemma sats_univalent_fm_assm:
  assumes 
    "x \<in> A" "y \<in> A" "z\<in>A" "env\<in> list(A)" "\<phi> \<in> formula"
  shows 
    "(A, ([x,z] @ env) \<Turnstile> \<phi>) \<longleftrightarrow> (A, Cons(z,Cons(y,Cons(x,env))) \<Turnstile> (univalent_Q1(\<phi>)))"
    "(A, ([x,y] @ env) \<Turnstile> \<phi>) \<longleftrightarrow> (A, Cons(z,Cons(y,Cons(x,env))) \<Turnstile> (univalent_Q2(\<phi>)))"
  unfolding univalent_Q1_def univalent_Q2_def
  using 
    sats_incr_bv_iff[of _ _ A _ "[]"] \<comment> \<open>simplifies iterates of incr_bv(_)`0\<close>
    sats_incr_bv1_iff[of _ "Cons(x,env)" A z y] 
    sats_swap_vars  assms 
   by simp_all

definition
  ZF_replacement_fm :: "i \<Rightarrow> i" where
  "ZF_replacement_fm(p) \<equiv> 
    nForall(pred(pred(arity(p))),Forall(Implies(
        univalent_fm(univalent_Q2(incr_bv(p)`2),univalent_Q1(incr_bv(p)`2),0),
        Exists(Forall(
          Iff(Member(0,1),Exists(And(Member(0,3),incr_bv(incr_bv(p)`2)`2))))))))"

lemma ZF_replacement_fm_type [TC]: "p \<in> formula \<Longrightarrow> ZF_replacement_fm(p) \<in> formula"
  by (simp add: ZF_replacement_fm_def)

lemmas ZF_replacement_simps = formula_add_params1[of \<phi> 2 _ M "[_,_]" ]
  sats_incr_bv_iff[of _ _ M _ "[]"] \<comment> \<open>simplifies iterates of incr_bv(_)`0\<close>
  sats_incr_bv_iff[of _ _ M _ "[_,_]"]\<comment> \<open>simplifies incr_bv(_)`2\<close>
  sats_incr_bv1_iff[of _ _ M] sats_swap_vars for \<phi> M

lemma \<comment> \<open>test for replacement formula\<close>
  fixes \<phi> M
  assumes 
    "\<phi> \<in> formula" "arity(\<phi>) = 4" "M, [] \<Turnstile> (ZF_replacement_fm(\<phi>))" 
  shows "Q" 
    using assms ZF_replacement_simps
    unfolding ZF_replacement_fm_def univalent_fm_def
     univalent_Q1_def univalent_Q2_def
    apply simp \<comment> \<open>check first 3rd assumption!\<close>
    oops

lemma sats_ZF_replacement_fm_iff:
  "(\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_replacement_fm(p))))
   \<longleftrightarrow>
   (\<forall>\<phi>\<in>formula. \<forall>env\<in>list(M). arity(\<phi>) \<le> 2 #+ length(env) \<longrightarrow> 
                    strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,[x,y] @ env)))"
  sorry

definition
  ZF_inf :: "i" where
  "ZF_inf == {ZF_separation_fm(p) . p \<in> formula } \<union> {ZF_replacement_fm(p) . p \<in> formula }"
              
lemma unions : "A\<subseteq>formula \<and> B\<subseteq>formula \<Longrightarrow> A\<union>B \<subseteq> formula"
  by auto
  
lemma ZF_inf_subset_formula : "ZF_inf \<subseteq> formula"
  unfolding ZF_inf_def by auto
    
definition
  ZFC :: "i" where
  "ZFC == ZF_inf \<union> ZFC_fin"

definition
  ZF :: "i" where
  "ZF == ZF_inf \<union> ZF_fin"

definition 
  ZF_minus_P :: "i" where
  "ZF_minus_P == ZF - { ZF_power_fm }"

lemma ZFC_subset_formula: "ZFC \<subseteq> formula"
  by (simp add:ZFC_def unions ZF_inf_subset_formula ZFC_fin_type)
  
txt\<open>Satisfaction of a set of sentences\<close>
definition
  satT :: "[i,i] \<Rightarrow> o"  ("_ \<Turnstile> _" 60) where
  "A \<Turnstile> \<Phi>  \<equiv>  \<forall>\<phi>\<in>\<Phi>. (A,[] \<Turnstile> \<phi>)"

lemma satTI [intro!]: 
  assumes "\<And>\<phi>. \<phi>\<in>\<Phi> \<Longrightarrow> A,[] \<Turnstile> \<phi>"
  shows "A \<Turnstile> \<Phi>"
  using assms unfolding satT_def by simp

lemma satTD [dest] :"A \<Turnstile> \<Phi> \<Longrightarrow>  \<phi>\<in>\<Phi> \<Longrightarrow> A,[] \<Turnstile> \<phi>"
  unfolding satT_def by simp

lemma sats_ZFC_iff_sats_ZF_AC: 
  "(N \<Turnstile> ZFC) \<longleftrightarrow> (N \<Turnstile> ZF) \<and> (N, [] \<Turnstile> AC)"
    unfolding ZFC_def ZFC_fin_def ZF_def by auto

lemma M_ZF_iff_M_satT: "M_ZF(M) \<longleftrightarrow> (M \<Turnstile> ZF)"
proof
  assume "M \<Turnstile> ZF"
  then
  have fin: "upair_ax(##M)" "Union_ax(##M)" "power_ax(##M)"
    "extensionality(##M)" "foundation_ax(##M)" "infinity_ax(##M)"
    unfolding ZF_def ZF_fin_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by simp_all
  {
    fix \<phi> env
    assume "\<phi> \<in> formula" "env\<in>list(M)" 
    moreover from \<open>M \<Turnstile> ZF\<close>
    have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))" 
         "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_replacement_fm(p)))"
      unfolding ZF_def ZF_inf_def by auto
    moreover from calculation
    have "arity(\<phi>) \<le> succ(length(env)) \<Longrightarrow> separation(##M, \<lambda>x. (M, Cons(x, env) \<Turnstile> \<phi>))"
      "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_separation_fm_iff sats_ZF_replacement_fm_iff by simp_all  
  }
  with fin
  show "M_ZF(M)"
    unfolding M_ZF_def by simp
next
  assume \<open>M_ZF(M)\<close>
  then
  have "M \<Turnstile> ZF_fin" 
    unfolding M_ZF_def ZF_fin_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by blast
  moreover from \<open>M_ZF(M)\<close>
  have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))" 
       "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_replacement_fm(p)))"
    unfolding M_ZF_def using sats_ZF_separation_fm_iff 
      sats_ZF_replacement_fm_iff by simp_all
  ultimately
  show "M \<Turnstile> ZF"
    unfolding ZF_def ZF_inf_def by blast
qed

(* 
lemma surj_imp_well_ord:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "\<exists>s. well_ord(B,r)" 
*)

definition
  minimum :: "i \<Rightarrow> i \<Rightarrow> i" where
  "minimum(r,B) \<equiv> THE b. b\<in>B \<and> (\<forall>y\<in>B. y \<noteq> b \<longrightarrow> <b, y> \<in> r)"

lemma well_ord_imp_min:
  assumes 
    "well_ord(A,r)" "B \<subseteq> A" "B \<noteq> 0"
  shows 
    "minimum(r,B) \<in> B" 
proof -
  from \<open>well_ord(A,r)\<close>
  have "wf[A](r)"
    using well_ord_is_wf[OF \<open>well_ord(A,r)\<close>] by simp
  with \<open>B\<subseteq>A\<close>
  have "wf[B](r)"
    using Sigma_mono Int_mono wf_subset unfolding wf_on_def by simp
  then
  have "\<forall> x. x \<in> B \<longrightarrow> (\<exists>z\<in>B. \<forall>y. \<langle>y, z\<rangle> \<in> r\<inter>B\<times>B \<longrightarrow> y \<notin> B)"
    unfolding wf_on_def using wf_eq_minimal
    by blast
  with \<open>B\<noteq>0\<close>
  obtain z where
    B: "z\<in>B \<and> (\<forall>y. <y,z>\<in>r\<inter>B\<times>B \<longrightarrow> y\<notin>B)"
    by blast
  then
  have "z\<in>B \<and> (\<forall>y\<in>B. y \<noteq> z \<longrightarrow> \<langle>z, y\<rangle> \<in> r)"
  proof -
    {
      fix y
      assume "y\<in>B" "y\<noteq>z"
      with \<open>well_ord(A,r)\<close> B \<open>B\<subseteq>A\<close>
      have "<z,y>\<in>r|<y,z>\<in>r|y=z"
        unfolding well_ord_def tot_ord_def linear_def by auto
      with B \<open>y\<in>B\<close> \<open>y\<noteq>z\<close>
      have "<z,y>\<in>r"
        by (cases;auto)
    }
    with B
    show ?thesis by blast
  qed
  have "v = z" if "v\<in>B \<and> (\<forall>y\<in>B. y \<noteq> v \<longrightarrow> \<langle>v, y\<rangle> \<in> r)" for v
    using that B by auto
  with \<open>z\<in>B \<and> (\<forall>y\<in>B. y \<noteq> z \<longrightarrow> \<langle>z, y\<rangle> \<in> r)\<close>
  show ?thesis
    unfolding minimum_def 
    using the_equality2[OF ex1I[of "\<lambda>x .x\<in>B \<and> (\<forall>y\<in>B. y \<noteq> x \<longrightarrow> \<langle>x, y\<rangle> \<in> r)" z]]
    by auto
qed

lemma well_ord_surj_imp_lepoll:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "B \<lesssim> A"
proof -
  let ?f="\<lambda>b\<in>B. minimum(r, {a\<in>A. h`a=b})"
  have "b \<in> B \<Longrightarrow> minimum(r, {a \<in> A . h ` a = b}) \<in> {a\<in>A. h`a=b}" for b
  proof -
    fix b
    assume "b\<in>B"
    with \<open>h \<in> surj(A,B)\<close>
    have "\<exists>a\<in>A. h`a=b" 
      unfolding surj_def by blast
    then
    have "{a\<in>A. h`a=b} \<noteq> 0"
      by auto
    with assms
    show "minimum(r,{a\<in>A. h`a=b}) \<in> {a\<in>A. h`a=b}"
      using well_ord_imp_min by blast
  qed
  moreover from this
  have "?f : B \<rightarrow> A"
      using lam_type[of B _ "\<lambda>_.A"] by simp
  moreover 
  have "?f ` w = ?f ` x \<Longrightarrow> w = x" if "w\<in>B" "x\<in>B" for w x
  proof -
    from calculation(1)[OF that(1)] calculation(1)[OF that(2)]
    have "w = h ` minimum(r, {a \<in> A . h ` a = w})"
         "x = h ` minimum(r, {a \<in> A . h ` a = x})"
      by simp_all  
    moreover
    assume "?f ` w = ?f ` x"
    moreover from this and that
    have "minimum(r, {a \<in> A . h ` a = w}) = minimum(r, {a \<in> A . h ` a = x})"
      by simp_all
    moreover from calculation(1,2,4)
    show "w=x" by simp
    qed
  ultimately
  show ?thesis
  unfolding lepoll_def inj_def by blast
qed

lemma (in forcing_data) surj_nat_MG :
  "\<exists>f. f \<in> surj(nat,M[G])"
proof -
  let ?f="\<lambda>n\<in>nat. val(G,enum`n)"
  have "x \<in> nat \<Longrightarrow> val(G, enum ` x)\<in> M[G]" for x
    using GenExtD[THEN iffD2, of _ G] bij_is_fun[OF M_countable] by force
  then
  have "?f: nat \<rightarrow> M[G]"
    using lam_type[of nat "\<lambda>n. val(G,enum`n)" "\<lambda>_.M[G]"] by simp
  moreover
  have "\<exists>n\<in>nat. ?f`n = x" if "x\<in>M[G]" for x
    using that GenExtD[of _ G] bij_is_surj[OF M_countable] 
    unfolding surj_def by auto
  ultimately
  show ?thesis
    unfolding surj_def by blast
qed

lemma (in G_generic) MG_eqpoll_nat: "M[G] \<approx> nat"
proof -
  interpret MG: M_ZF_trans "M[G]"
    using Transset_MG generic pairing_in_MG 
      Union_MG  extensionality_in_MG power_in_MG
      foundation_in_MG  strong_replacement_in_MG[simplified]
      separation_in_MG[simplified] infinty_in_MG
    by unfold_locales simp_all
  obtain f where "f \<in> surj(nat,M[G])"
    using surj_nat_MG by blast
  then
  have "M[G] \<lesssim> nat" 
    using well_ord_surj_imp_lepoll well_ord_Memrel[of nat]
    by simp
  moreover
  have "nat \<lesssim> M[G]"
    using MG.nat_into_M subset_imp_lepoll by auto
  ultimately
  show ?thesis using eqpollI 
    by simp
qed

theorem extensions_of_ctms:
  assumes 
    "M \<approx> nat" "Transset(M)" "M \<Turnstile> ZF"
  shows 
    "\<exists>N. 
      M \<subseteq> N \<and> N \<approx> nat \<and> Transset(N) \<and> (N \<Turnstile> ZF) \<and>  M\<noteq>N \<and>  
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)) \<and>
      ((M, []\<Turnstile> AC) \<longrightarrow> (N \<Turnstile> ZFC))" 
proof -
  from \<open>M \<approx> nat\<close>
  obtain enum where "enum \<in> bij(nat,M)"
    using eqpoll_sym unfolding eqpoll_def by blast
  with assms
  interpret M_ctm M enum
    using M_ZF_iff_M_satT
    by intro_locales (simp_all add:M_ctm_axioms_def)
  interpret ctm_separative "2^<\<omega>" funle 0 M enum
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
    show "\<exists>q\<in>2^<\<omega>.  \<exists>r\<in>2^<\<omega>. q \<preceq>f f \<and> r \<preceq>f f \<and> q \<bottom>f r"
      by (rule_tac bexI)+ \<comment> \<open>why the heck auto-tools don't solve this?\<close>
  next
    show "2^<\<omega> \<in> M" using nat_into_M seqspace_closed by simp
  next
    show "funle \<in> M" using funle_in_M .
  qed
  from cohen_extension_is_proper
  obtain G where "M_generic(G)" 
    "M \<noteq> GenExt(G)" (is "M\<noteq>?N") 
    by blast
  then 
  interpret G_generic "2^<\<omega>" funle 0 _ enum  G by unfold_locales
  interpret MG: M_ZF "?N"
    using generic pairing_in_MG 
      Union_MG  extensionality_in_MG power_in_MG
      foundation_in_MG  strong_replacement_in_MG[simplified]
      separation_in_MG[simplified] infinty_in_MG
    by unfold_locales simp_all
  have "?N \<Turnstile> ZF" 
    using M_ZF_iff_M_satT[of ?N] MG.M_ZF_axioms by simp
  moreover 
  have "M, []\<Turnstile> AC \<Longrightarrow> ?N \<Turnstile> ZFC"
  proof -
    assume "M, [] \<Turnstile> AC"
    then
    have "choice_ax(##M)"
      unfolding ZF_choice_fm_def using ZF_choice_auto by simp
    then
    have "choice_ax(##?N)" using choice_in_MG by simp
    with \<open>?N \<Turnstile> ZF\<close>
    show "?N \<Turnstile> ZFC"
      using ZF_choice_auto sats_ZFC_iff_sats_ZF_AC 
      unfolding ZF_choice_fm_def by simp
  qed
  moreover
  note \<open>M \<noteq> ?N\<close>
  moreover
  have "Transset(?N)" using Transset_MG .
  moreover
  have "M \<subseteq> ?N" using M_subset_MG[OF one_in_G] generic by simp
  ultimately
  show ?thesis
    using Ord_MG_iff MG_eqpoll_nat
    by (rule_tac x="?N" in exI, simp)
qed

end