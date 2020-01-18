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
  "_choice"  :: "i"  ("AC")
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

lemma sats_ZF_separation_fm_iff:
  "(\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p))))
   \<longleftrightarrow>
   (\<forall>\<phi>\<in>formula. \<forall>env\<in>list(M). arity(\<phi>) \<le> 1 #+ length(env) \<longrightarrow>
                    separation(##M,\<lambda>x. sats(M,\<phi>,[x] @ env)))"
  sorry

lemma sats_ZF_replacement_fm_iff:
  "(\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_replacement_fm(p))))
   \<longleftrightarrow>
   (\<forall>\<phi>\<in>formula. \<forall>env\<in>list(M). arity(\<phi>) \<le> 2 #+ length(env) \<longrightarrow> 
                    strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,[x,y] @ env)))"
  sorry

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
    (* "y\<in>B \<Longrightarrow> y\<noteq>minimum(r,B) \<Longrightarrow> <b, y> \<in> r" *)
  sorry

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
    "enum \<in> bij(nat,M)" "Transset(M)" "M \<Turnstile> ZF"
  shows 
    "\<exists>N. 
      M \<subseteq> N \<and> Transset(N) \<and> N \<approx> nat \<and> (N \<Turnstile> ZF) \<and>  M\<noteq>N \<and>  
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)) \<and>
      ((M, []\<Turnstile> AC) \<longrightarrow> (N \<Turnstile> ZFC))" 
proof -
  from assms
  interpret M_ctm
    using M_ZF_iff_M_satT
    by intro_locales (simp_all add:M_ctm_axioms_def)
  interpret ctm_separative "2^<\<omega>" funle 0
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
  interpret G_generic "2^<\<omega>" funle 0 _ _  G by unfold_locales
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