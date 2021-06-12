theory Aleph_Relative
  imports
    CardinalArith_Relative
begin

definition
  HAleph :: "[i,i] \<Rightarrow> i" where
  "HAleph(i,r) \<equiv> if(i=0, nat, if(\<not>Limit(i),
                            csucc(r`( \<Union> i )),
                                   \<Union>j\<in>i. r`j))"

reldb_add functional "Limit" "Limit"
relationalize "Limit" "is_Limit" external

relativize functional "HAleph" "HAleph_rel"
relationalize "HAleph_rel" "is_HAleph"

definition
  Aleph' :: "i => i"  where
  "Aleph'(a) == transrec(a,\<lambda>i r. HAleph(i,r))"

relativize functional "Aleph'" "Aleph_rel"
relationalize "Aleph_rel" "is_Aleph"

context M_cardinal_arith_jump
begin

rel_closed for "Aleph"
  sorry

end (* M_cardinal_arith_jump *)

lemma HAleph_eq_Aleph_recursive:
  "Ord(i) \<Longrightarrow> HAleph(i,r) = (if i = 0 then nat
                else if \<exists>j. i = succ(j) then csucc(r ` (THE j. i = succ(j))) else \<Union>j<i. r ` j)"
proof -
  assume "Ord(i)"
  moreover from this
  have "i = succ(j) \<Longrightarrow> (\<Union>succ(j)) = j" for j
    using Ord_Union_succ_eq by simp
  moreover from \<open>Ord(i)\<close>
  have "(\<exists>j. i = succ(j)) \<longleftrightarrow> \<not>Limit(i) \<and> i \<noteq> 0"
    using Ord_cases_disj by auto
  ultimately
  show ?thesis
    unfolding HAleph_def OUnion_def
    by auto
qed

lemma Aleph'_eq_Aleph: "Ord(a) \<Longrightarrow> Aleph'(a) = Aleph(a)"
  unfolding Aleph'_def Aleph_def transrec2_def
  using HAleph_eq_Aleph_recursive
  by (intro transrec_equal_on_Ord) auto

reldb_rem functional "Aleph'"
reldb_rem relational "is_Aleph"
reldb_add functional "Aleph" "Aleph_rel"
reldb_add relational "Aleph" "is_Aleph"

abbreviation
  Aleph_r :: "[i,i\<Rightarrow>o] \<Rightarrow> i" (\<open>\<aleph>\<^bsub>_\<^esub>\<^bsup>_\<^esup>\<close>) where
  "Aleph_r(a,M) \<equiv> Aleph_rel(M,a)"

abbreviation
  Aleph_r_set :: "[i,i] \<Rightarrow> i" (\<open>\<aleph>\<^bsub>_\<^esub>\<^bsup>_\<^esup>\<close>) where
  "Aleph_r_set(a,M) \<equiv> Aleph_rel(##M,a)"

lemma Aleph_rel_def': "Aleph_rel(M,a) \<equiv> transrec(a, \<lambda>i r. HAleph_rel(M, i, r))"
  unfolding Aleph_rel_def .

lemma succ_mem_Limit: "Limit(j) \<Longrightarrow> i \<in> j \<Longrightarrow> succ(i) \<in> j"
  using Limit_has_succ[THEN ltD] ltI Limit_is_Ord by auto

locale M_aleph =  M_cardinal_arith_jump +
  assumes 
  aleph_rel_replacement:  "strong_replacement(M, \<lambda>x y. y = \<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup>)" 

begin

lemma Aleph_rel_zero: "\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^esup> = nat"
  using def_transrec [OF Aleph_rel_def',of _ 0] 
  unfolding HAleph_rel_def by simp

lemma Aleph_rel_succ: "Ord(\<alpha>) \<Longrightarrow> M(\<alpha>) \<Longrightarrow> \<aleph>\<^bsub>succ(\<alpha>)\<^esub>\<^bsup>M\<^esup> = csucc_rel(M,\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>)"
  using Ord_Union_succ_eq
  by (subst def_transrec [OF Aleph_rel_def'])
    (simp add:HAleph_rel_def)

lemma Aleph_rel_limit:
  assumes "Limit(\<alpha>)" "M(\<alpha>)"
  shows "\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup> = \<Union>{\<aleph>\<^bsub>j\<^esub>\<^bsup>M\<^esup> . j \<in> \<alpha>}"
proof -
  note trans=transM[OF _ \<open>M(\<alpha>)\<close>]
  from \<open>M(\<alpha>)\<close>
  have "\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup> = HAleph_rel(M, \<alpha>, \<lambda>x\<in>\<alpha>. \<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup>)"
    using def_transrec [OF Aleph_rel_def',of M \<alpha>] by simp
  also
  have "... = \<Union>{a . j \<in> \<alpha>, M(a) \<and> a = \<aleph>\<^bsub>j\<^esub>\<^bsup>M\<^esup>}"
    unfolding HAleph_rel_def
    using assms zero_not_Limit trans by auto
  also
  have "... = \<Union>{\<aleph>\<^bsub>j\<^esub>\<^bsup>M\<^esup> . j \<in> \<alpha>}"
    using Aleph_rel_closed[OF trans] by auto
  finally
  show ?thesis .
qed

lemma Aleph_rel_cont: "Limit(l) \<Longrightarrow> M(l) \<Longrightarrow> \<aleph>\<^bsub>l\<^esub>\<^bsup>M\<^esup> = (\<Union>i<l. \<aleph>\<^bsub>i\<^esub>\<^bsup>M\<^esup>)"
  using Limit_is_Ord Aleph_rel_limit
  by (simp add:OUnion_def)

lemma Ord_Aleph_rel:
  assumes "Ord(a)"shows "M(a) \<Longrightarrow> Ord(\<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup>)"
  using \<open>Ord(a)\<close>
proof(induct a rule:trans_induct3)
  case 0
  show ?case using Aleph_rel_zero by simp
next
  case (succ x)
  with \<open>Ord(x)\<close>
  have "M(x)" "Ord(\<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup>)" by simp_all
  then
  have "Ord(csucc_rel(M,\<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup>))"
    using Card_rel_is_Ord Card_rel_csucc_rel Aleph_rel_closed
    by simp
  with \<open>Ord(x)\<close> \<open>M(x)\<close>
  show ?case using Aleph_rel_succ by simp
next
  case (limit x)
  note trans=transM[OF _ \<open>M(x)\<close>]
  from limit
  have "\<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup> = (\<Union>i\<in>x. \<aleph>\<^bsub>i\<^esub>\<^bsup>M\<^esup>)"
    using Aleph_rel_cont OUnion_def Limit_is_Ord
    by auto
  with limit
  show ?case using Ord_UN Aleph_rel_closed trans by auto
qed

lemma Card_rel_Aleph_rel [simp, intro]:
  assumes "Ord(a)" and types: "M(a)" shows "Card\<^bsup>M\<^esup>(\<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup>)"
  using assms
proof (induct rule:trans_induct3)
  case 0
  then
  show ?case
    using Aleph_rel_zero Card_rel_nat by simp
next
  case (succ x)
  then
  show ?case
    using Card_rel_csucc_rel Aleph_rel_succ Ord_Aleph_rel by simp
next
  case (limit x)
  moreover
  from this
  have "M({y . z \<in> x, M(y) \<and> M(z) \<and> y = \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>})"
    using aleph_rel_replacement by simp
  ultimately
  show ?case
    using Ord_Aleph_rel Card_nat
    by (subst def_transrec [OF Aleph_rel_def'])
      (auto simp add:HAleph_rel_def)
qed

lemma Aleph_rel_increasing:
  assumes ab: "a < b" and types: "M(a)" "M(b)"
  shows "\<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup> < \<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>"
proof -
  { fix x
    have "Ord(b)" using ab by (blast intro: lt_Ord2)
    moreover
    assume "M(x)"
    moreover
    note \<open>M(b)\<close>
    ultimately
    have "x < b \<Longrightarrow> \<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup> < \<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>"
    proof (induct b arbitrary: x rule: trans_induct3)
      case 0 thus ?case by simp
    next
      case (succ b)
      then
      show ?case
        using Card_rel_csucc_rel Ord_Aleph_rel Ord_Union_succ_eq lt_csucc_rel
          lt_trans[of _ "\<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>" "csucc\<^bsup>M\<^esup>(\<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>)"]
        by (subst (2) def_transrec[OF Aleph_rel_def'])
          (auto simp add: le_iff HAleph_rel_def)
    next
      case (limit l)
      then
      have sc: "succ(x) < l"
        by (blast intro: Limit_has_succ)
      then
      have "\<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup> < (\<Union>j<l. \<aleph>\<^bsub>j\<^esub>\<^bsup>M\<^esup>)"
        using limit Ord_Aleph_rel Ord_OUN
          (*            by (blast intro: OUN_upper_lt Card_is_Ord ltD lt_Ord*)
        apply (rule_tac OUN_upper_lt)
        apply (blast intro: Card_rel_is_Ord ltD lt_Ord)
      proof -
        from \<open>x<l\<close> \<open>Limit(l)\<close>
        have "Ord(x)"
          using Limit_is_Ord Ord_in_Ord
          by (auto dest!:ltD)
        with \<open>M(x)\<close>
        show "\<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup> < \<aleph>\<^bsub>succ(x)\<^esub>\<^bsup>M\<^esup>"
          using Card_rel_csucc_rel Ord_Aleph_rel lt_csucc_rel
            ltD[THEN [2] Ord_in_Ord] succ_in_MI[OF \<open>M(x)\<close>]
            Aleph_rel_succ[of x]
          by (simp)
      next
        from \<open>M(l)\<close> \<open>Limit(l)\<close>
        show "Ord(\<Union>j<l. \<aleph>\<^bsub>j\<^esub>\<^bsup>M\<^esup>)"
          using Ord_Aleph_rel lt_Ord Limit_is_Ord Ord_in_Ord
          by (rule_tac Ord_OUN)
            (auto dest:transM ltD intro!:Ord_Aleph_rel)
      qed
      then
      show ?case using limit Aleph_rel_cont by simp
    qed
  }
  with types
  show ?thesis using ab by simp
qed


end (* M_aleph *)

end