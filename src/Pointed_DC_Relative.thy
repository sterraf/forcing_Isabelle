section\<open>Relative DC\<close>

theory Pointed_DC_Relative 
  imports
    Cardinal_Library_Relative

begin

consts dc_witness :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
primrec
  wit0   : "dc_witness(0,A,a,s,R) = a"
  witrec : "dc_witness(succ(n),A,a,s,R) = s`{x\<in>A. \<langle>dc_witness(n,A,a,s,R),x\<rangle>\<in>R}"

lemmas dc_witness_def = dc_witness_nat_def

relativize functional "dc_witness" "dc_witness_rel"
relationalize "dc_witness_rel" "is_dc_witness"
manual_schematic for "is_dc_witness" assuming "nonempty"
  oops

context M_basic
begin

lemma dc_witness_closed[intro,simp]:
  assumes "M(n)" "M(A)" "M(a)" "M(s)" "M(R)"
  shows "M(dc_witness(n,A,a,s,R))"
  sorry

lemma dc_witness_char:
  assumes "M(A)"
  shows "dc_witness(n,A,a,s,R) = dc_witness_rel(M,n,A,a,s,R)"
proof -
  from assms
  have "{x \<in> A . \<langle>rec, x\<rangle> \<in> R} =  {x \<in> A . M(x) \<and> \<langle>rec, x\<rangle> \<in> R}" for rec
    by (auto dest:transM)
  then
  show ?thesis
    unfolding dc_witness_def dc_witness_rel_def by simp
qed

lemma first_section_closed:
  assumes
    "M(A)" "M(a)" "M(R)"
  shows "M({x \<in> A . \<langle>a, x\<rangle> \<in> R})"
proof -
  have "{x \<in> A . \<langle>a, x\<rangle> \<in> R} = range({a} \<times> range(R) \<inter> R) \<inter> A"
    by (intro equalityI) auto
  with assms
  show ?thesis
    by simp
qed

lemma witness_into_A [TC]:
  assumes "a\<in>A"
    "\<forall>X[M]. X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X"
    "\<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0" "n\<in>nat"
    "M(A)" "M(a)" "M(s)" "M(R)"
  shows "dc_witness(n, A, a, s, R)\<in>A"
  using \<open>n\<in>nat\<close>
proof(induct n)
  case 0
  then show ?case using \<open>a\<in>A\<close> by simp
next
  case (succ x)
  with succ assms(1,3-)
  show ?case 
    using nat_into_M first_section_closed
    by (simp, rule_tac rev_subsetD, rule_tac assms(2)[rule_format]) 
      auto
qed

lemma witness_related:
  assumes "a\<in>A"
    "(\<forall>X[M]. X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X)"
    "\<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0" "n\<in>nat"
    "M(a)" "M(A)" "M(s)" "M(R)" "M(n)"
  shows "\<langle>dc_witness(n, A, a, s, R),dc_witness(succ(n), A, a, s, R)\<rangle>\<in>R"
proof -
  note assms
  moreover from this
  have "dc_witness(n, A, a, s, R)\<in>A" (is "?x \<in> A")
    using witness_into_A[of _ _ s R n] by simp
  moreover from assms
  have "M({x \<in> A . \<langle>dc_witness(n, A, a, s, R), x\<rangle> \<in> R})"
    using first_section_closed[of A "dc_witness(n, A, a, s, R)"]
    by simp
  ultimately
  show ?thesis by auto
qed

lemma witness_funtype:
  assumes "a\<in>A"
    "\<forall>X[M]. X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X \<in> X"
    "\<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R} \<noteq> 0"
    "M(A)" "M(a)" "M(s)" "M(R)"
  shows "(\<lambda>n\<in>nat. dc_witness(n, A, a, s, R)) \<in> nat \<rightarrow> A" (is "?f \<in> _ \<rightarrow> _")
proof -
  have "?f \<in> nat \<rightarrow> {dc_witness(n, A, a, s, R). n\<in>nat}" (is "_ \<in> _ \<rightarrow> ?B")
    using lam_funtype assms by simp
  then
  have "?B \<subseteq> A"
    using witness_into_A assms by auto
  with \<open>?f \<in> _\<close>
  show ?thesis
    using fun_weaken_type
    by simp
qed

lemma witness_to_fun:   
  assumes "a\<in>A"
    "\<forall>X[M]. X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X"
    "\<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0"
    "M(A)" "M(a)" "M(s)" "M(R)"
  shows "\<exists>f \<in> nat\<rightarrow>A. \<forall>n\<in>nat. f`n =dc_witness(n,A,a,s,R)"
  using assms bexI[of _ "\<lambda>n\<in>nat. dc_witness(n,A,a,s,R)"] witness_funtype
  by simp

end (* M_basic *)

context M_library
begin

(* Should port the whole AC theory, including the absolute version
  of the following theorem *)
lemma AC_M_func:
  assumes "\<And>x. x \<in> A \<Longrightarrow> (\<exists>y. y \<in> x)" "M(A)"
  shows "\<exists>f \<in> A \<rightarrow>\<^bsup>M\<^esup> \<Union>(A). \<forall>x \<in> A. f`x \<in> x"
proof -
  from \<open>M(A)\<close>
  interpret mpiA:M_Pi_assumptions _ A "\<lambda>x. x"
    using Pi_replacement Pi_separation
    apply unfold_locales apply (auto dest:transM simp:Sigfun_def)[3] (* FIXME: Slow *)
    sorry
  from \<open>M(A)\<close>
  interpret mpic_A:M_Pi_assumptions_choice _ A "\<lambda>x. x"
    apply unfold_locales
     apply (unfold strong_replacement_def, blast)[1]
    sorry
  from \<open>M(A)\<close>
  interpret mpi2:M_Pi_assumptions2 _ A "\<lambda>_. \<Union>A" "\<lambda>x. x"
    apply unfold_locales
       apply (auto dest:transM)
    sorry
  from assms
  show ?thesis
    using mpi2.Pi_rel_type apply_type mpiA.mem_Pi_rel_abs mpi2.mem_Pi_rel_abs
      function_space_rel_char
    by (rule_tac mpic_A.AC_Pi_rel[THEN rexE], simp, rule_tac x=x in bexI)
      (auto, rule_tac C="\<lambda>x. x" in Pi_type, auto)
qed

lemma non_empty_family: "[| 0 \<notin> A;  x \<in> A |] ==> \<exists>y. y \<in> x"
by (subgoal_tac "x \<noteq> 0", blast+)

lemma AC_M_func0: "0 \<notin> A \<Longrightarrow> M(A) \<Longrightarrow> \<exists>f \<in> A \<rightarrow>\<^bsup>M\<^esup> \<Union>(A). \<forall>x \<in> A. f`x \<in> x"
  by (rule AC_M_func) (simp_all add: non_empty_family)

lemma AC_M_func_Pow_rel:
  assumes "M(C)"
  shows "\<exists>f \<in> (Pow\<^bsup>M\<^esup>(C)-{0}) \<rightarrow>\<^bsup>M\<^esup> C. \<forall>x \<in> Pow\<^bsup>M\<^esup>(C)-{0}. f`x \<in> x"
  apply (rule AC_M_func0 [THEN bexE]) defer 2
    apply (rule_tac [2] bexI)
     prefer 2 apply assumption
  apply (simp_all add:assms)
  sorry

theorem pointed_DC:
  assumes "\<forall>x\<in>A. \<exists>y\<in>A. \<langle>x,y\<rangle>\<in> R" "M(A)" "M(R)"
  shows "\<forall>a\<in>A. \<exists>f \<in> nat\<rightarrow>\<^bsup>M\<^esup> A. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>f`n,f`succ(n)\<rangle>\<in>R)"
proof -
  have 0:"\<forall>y\<in>A. {x \<in> A . \<langle>y, x\<rangle> \<in> R} \<noteq> 0"
    using assms by auto
  from \<open>M(A)\<close>
  obtain g where 1: "g \<in> Pow\<^bsup>M\<^esup>(A)-{0} \<rightarrow> A" "\<forall>X[M]. X \<noteq> 0 \<and> X \<subseteq> A \<longrightarrow> g ` X \<in> X"
      "M(g)"
    using AC_M_func_Pow_rel[of A] mem_Pow_rel_abs
      function_space_rel_char[of "Pow\<^bsup>M\<^esup>(A)-{0}" A] by auto
  {
    fix a
    assume "a\<in>A"
    let ?f ="\<lambda>n\<in>nat. dc_witness(n,A,a,g,R)"
    note \<open>a\<in>A\<close>
    moreover from this
    have f0: "?f`0 = a" by simp
    moreover
    note \<open>a\<in>A\<close> \<open>M(g)\<close> \<open>M(A)\<close> \<open>M(R)\<close>
    moreover from calculation
    have "\<langle>?f ` n, ?f ` succ(n)\<rangle> \<in> R" if "n\<in>nat" for n
      using witness_related[OF \<open>a\<in>A\<close> _ 0, of g n] 1 that
      by (auto dest:transM)
    moreover from calculation
    have "M(?f)" sorry
    ultimately
    have "\<exists>f[M]. f\<in>nat \<rightarrow> A \<and> f ` 0 = a \<and> (\<forall>n\<in>nat. \<langle>f ` n, f ` succ(n)\<rangle> \<in> R)"
      using 0 1 \<open>a\<in>_\<close>
      by (rule_tac x="(\<lambda>n\<in>\<omega>. dc_witness(n, A, a, g, R))" in rexI)
        (simp_all, rule_tac witness_funtype, auto dest:transM)
  }
  with \<open>M(A)\<close>
  show ?thesis using function_space_rel_char by auto
qed

lemma aux_DC_on_AxNat2 : "\<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> R \<Longrightarrow>
                  \<forall>x\<in>A\<times>nat. \<exists>y\<in>A\<times>nat. \<langle>x,y\<rangle> \<in> {\<langle>a,b\<rangle>\<in>R. snd(b) = succ(snd(a))}"
  by (rule ballI, erule_tac x="x" in ballE, simp_all)

lemma infer_snd : "c\<in> A\<times>B \<Longrightarrow> snd(c) = k \<Longrightarrow> c=\<langle>fst(c),k\<rangle>"
  by auto

corollary DC_on_A_x_nat :
  assumes "(\<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> R)" "a\<in>A" "M(A)" "M(R)"
  shows "\<exists>f \<in> nat\<rightarrow>\<^bsup>M\<^esup>A. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>\<langle>f`n,n\<rangle>,\<langle>f`succ(n),succ(n)\<rangle>\<rangle>\<in>R)" (is "\<exists>x\<in>_.?P(x)")
proof -
  let ?R'="{\<langle>a,b\<rangle>\<in>R. snd(b) = succ(snd(a))}"
  from assms(1)
  have "\<forall>x\<in>A\<times>nat. \<exists>y\<in>A\<times>nat. \<langle>x,y\<rangle> \<in> ?R'"
    using aux_DC_on_AxNat2 by simp
  moreover
  note \<open>a\<in>_\<close> \<open>M(A)\<close>
  moreover from this
  have "M(A \<times> \<omega>)" by simp
  moreover
  have "M(?R')" sorry
  ultimately
  obtain f where
    F:"f\<in>nat\<rightarrow>\<^bsup>M\<^esup> A\<times>\<omega>" "f ` 0 = \<langle>a,0\<rangle>"  "\<forall>n\<in>nat. \<langle>f ` n, f ` succ(n)\<rangle> \<in> ?R'"
    using pointed_DC[of "A\<times>nat" ?R'] by blast
  with \<open>M(A)\<close>
  have "M(f)" using function_space_rel_char by simp
  then
  have "M(\<lambda>x\<in>nat. fst(f`x))" (is "M(?f)")
    using lam_replacement_fst lam_replacement_hcomp
      lam_replacement_constant lam_replacement_identity
      lam_replacement_apply
    by (rule_tac lam_replacement_iff_lam_closed[THEN iffD1, rule_format])
      auto
  with F \<open>M(A)\<close>
  have "?f\<in>nat\<rightarrow>\<^bsup>M\<^esup> A" "?f ` 0 = a" using function_space_rel_char by auto
  have 1:"n\<in> nat \<Longrightarrow> f`n= \<langle>?f`n, n\<rangle>" for n
  proof(induct n set:nat)
    case 0
    then show ?case using F by simp
  next
    case (succ x)
    with \<open>M(A)\<close>
    have "\<langle>f`x, f`succ(x)\<rangle> \<in> ?R'" "f`x \<in> A\<times>nat" "f`succ(x)\<in>A\<times>nat"
      using F function_space_rel_char[of \<omega> "A\<times>\<omega>"] by auto
    then
    have "snd(f`succ(x)) = succ(snd(f`x))" by simp
    with succ \<open>f`x\<in>_\<close>
    show ?case using infer_snd[OF \<open>f`succ(_)\<in>_\<close>] by auto
  qed
  have "\<langle>\<langle>?f`n,n\<rangle>,\<langle>?f`succ(n),succ(n)\<rangle>\<rangle> \<in> R" if "n\<in>nat" for n
    using that 1[of "succ(n)"] 1[OF \<open>n\<in>_\<close>] F(3) by simp
  with \<open>f`0=\<langle>a,0\<rangle>\<close>
  show ?thesis
    using rev_bexI[OF \<open>?f\<in>_\<close>] by simp
qed

lemma aux_sequence_DC :
  assumes "\<forall>x\<in>A. \<forall>n\<in>nat. \<exists>y\<in>A. \<langle>x,y\<rangle> \<in> S`n"
    "R={\<langle>\<langle>x,n\<rangle>,\<langle>y,m\<rangle>\<rangle> \<in> (A\<times>nat)\<times>(A\<times>nat). \<langle>x,y\<rangle>\<in>S`m }"
  shows "\<forall> x\<in>A\<times>nat . \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> R"
  using assms Pair_fst_snd_eq by auto

lemma aux_sequence_DC2 : "\<forall>x\<in>A. \<forall>n\<in>nat. \<exists>y\<in>A. \<langle>x,y\<rangle> \<in> S`n \<Longrightarrow>
        \<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> {\<langle>\<langle>x,n\<rangle>,\<langle>y,m\<rangle>\<rangle>\<in>(A\<times>nat)\<times>(A\<times>nat). \<langle>x,y\<rangle>\<in>S`m }"
  by auto

lemma sequence_DC:
  assumes "\<forall>x\<in>A. \<forall>n\<in>nat. \<exists>y\<in>A. \<langle>x,y\<rangle> \<in> S`n" "M(A)" "M(S)"
  shows "\<forall>a\<in>A. (\<exists>f \<in> nat\<rightarrow>\<^bsup>M\<^esup> A. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>f`n,f`succ(n)\<rangle>\<in>S`succ(n)))"
proof -
  from assms
  have "M({x \<in> (A \<times> \<omega>) \<times> A \<times> \<omega> . (\<lambda>\<langle>\<langle>x,n\<rangle>,y,m\<rangle>. \<langle>x, y\<rangle> \<in> S ` m)(x)})" sorry
  with assms
  show ?thesis
    by (rule_tac ballI) (drule aux_sequence_DC2, drule DC_on_A_x_nat, auto)
qed 

end (* M_library *)

end