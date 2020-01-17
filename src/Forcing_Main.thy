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

definition
  ZF_fin :: "i" where
  "ZF_fin \<equiv> {ZF_extensionality_fm,ZF_foundation_fm,ZF_pairing_fm,
              ZF_union_fm,ZF_infinity_fm,ZF_power_fm}"

consts 
  nForall :: "[i,i] \<Rightarrow> i"
primrec
  "nForall(0,p) = p"
  "nForall(succ(n),p) = Forall(nForall(n,p))" 


lemma nForall_type [TC]: 
      "[| n \<in> nat; p \<in> formula |] ==> nForall(n,p) \<in> formula"
  by (induct_tac "n",auto)

definition
  ZF_separation_fm :: "i \<Rightarrow> i" where
  "ZF_separation_fm(p) == nForall(pred(arity(p)), 
                              Forall(Exists(Forall(
                              Iff(Member(0,1),And(Member(0,2),
                                              incr_bv1^2(p)))))))"
                                                
lemma ZF_separation_fm_type [TC]: "p \<in> formula \<Longrightarrow> ZF_separation_fm(p) \<in> formula"
  by (simp add: ZF_separation_fm_def)

lemmas ZF_separation_simps = formula_add_params1[of _ 2 _ _ "[_,_]" ] 

lemma \<comment> \<open>test for separation formula\<close>
  fixes \<phi> M
  assumes 
    "\<phi> \<in> formula" "arity(\<phi>) = 3" "M, [] \<Turnstile> (ZF_separation_fm(\<phi>))" 
  shows "Q" 
    using assms ZF_separation_simps
    unfolding ZF_separation_fm_def 
    apply simp \<comment> \<open>check first 3rd assumption!\<close>
    oops

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

notepad
begin
  fix M
  assume assms:"p \<in> formula \<Longrightarrow> M, [] \<Turnstile> (ZF_separation_fm(p))" for p
  have "\<phi>\<in>formula \<Longrightarrow> arity(\<phi>) \<le> 1 #+ length(env) \<Longrightarrow>
        separation(##M,\<lambda>x. sats(M,\<phi>,[x] @ env))" if "env\<in>list(M)" for \<phi> env
    using that
  proof (induct)
    case Nil
    moreover from this
    have "Arith.pred(arity(\<phi>)) = 0" 
      using pred_le[of _ 0] by (simp)
    moreover
    note assms[of \<phi>]
    ultimately
    show ?case 
      using formula_add_params1[of \<phi> 2 _ M "[_,_]" ]
      unfolding separation_def ZF_separation_fm_def
      by simp
  next
    case (Cons a l)
    then
    have "Arith.pred(arity(\<phi>)) \<le> 1 #+ length(l)" 
      using pred_le[of _ "succ(length(l))"] by (simp)
    have "Arith.pred(arity(\<phi>)) = n \<Longrightarrow> 
          separation(\<lambda>a. (##M)(a), \<lambda>x. (M, ([x] @ Cons(a, l)) \<Turnstile> \<phi>))"
      if "n \<in> nat" for n  using that
    proof (induct)
      case 0
      with assms[of \<phi>] and Cons
      show ?case 
        using formula_add_params1[of \<phi> 2 _ M "Cons(a,l)"  "[]"]
        unfolding separation_def ZF_separation_fm_def
        apply simp
        sorry
    next
      case (succ n)
      with assms[of \<phi>] and Cons
      show ?case 
      (*
      lemma formula_add_params1 [rule_format]:
        "[| p \<in> formula; n \<in> nat; x \<in> A |]
         ==> \<forall>bvs \<in> list(A). \<forall>env \<in> list(A).
                length(bvs) = n \<longrightarrow>
                sats(A, iterates(incr_bv1, n, p), Cons(x, bvs@env)) \<longleftrightarrow>
                sats(A, p, Cons(x,env))"
      *)
        using formula_add_params1[of \<phi> 2 _ M "Cons(a,l)"  "[]"]
          sats_univalent_fm_auto[OF sats_univalent_fm_assm]
        unfolding separation_def ZF_separation_fm_def univalent_fm_def
        apply simp
        sorry
    qed
    moreover from \<open>\<phi>\<in>_\<close>
    have "Arith.pred(arity(\<phi>)) \<in> nat" by simp
    ultimately
    show ?case by simp
  qed
end (* notepad *)




end