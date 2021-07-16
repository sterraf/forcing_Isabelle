section\<open>Various results missing from ZF.\<close>

theory ZF_Miscellanea
  imports
    ZF
    Nat_Miscellanea
begin

lemma funcI : "f \<in> A \<rightarrow> B \<Longrightarrow> a \<in> A \<Longrightarrow> b= f ` a \<Longrightarrow> \<langle>a, b\<rangle> \<in> f"
  by(simp_all add: apply_Pair)

lemma vimage_fun_sing:
  assumes "f\<in>A\<rightarrow>B" "b\<in>B"
  shows "{a\<in>A . f`a=b} = f-``{b}"
using assms vimage_singleton_iff function_apply_equality Pi_iff funcI by auto

lemma image_fun_subset: "S\<in>A\<rightarrow>B \<Longrightarrow> C\<subseteq>A\<Longrightarrow> {S ` x . x\<in> C} = S``C"
  using image_function[symmetric,of S C] domain_of_fun Pi_iff by auto

definition
  minimum :: "i \<Rightarrow> i \<Rightarrow> i" where
  "minimum(r,B) \<equiv> THE b. first(b,B,r)"

lemma minimum_in: "\<lbrakk> well_ord(A,r); B\<subseteq>A; B\<noteq>0 \<rbrakk> \<Longrightarrow> minimum(r,B) \<in> B"
  using the_first_in unfolding minimum_def by simp

\<comment> \<open>MOVE THIS to an appropriate place. Now it is repeated in
   \<^file>\<open>Forcing_Main.thy\<close>. But consider that ported versions follow,
   and hence perhaps we should only have the relative version.\<close>
lemma well_ord_surj_imp_inj_inverse:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "(\<lambda>b\<in>B. minimum(r, {a\<in>A. h`a=b})) \<in> inj(B,A)"
proof -
  let ?f="\<lambda>b\<in>B. minimum(r, {a\<in>A. h`a=b})"
  have "minimum(r, {a \<in> A . h ` a = b}) \<in> {a\<in>A. h`a=b}" if "b\<in>B" for b
  proof -
    from \<open>h \<in> surj(A,B)\<close> that
    have "{a\<in>A. h`a=b} \<noteq> 0"
      unfolding surj_def by blast
    with \<open>well_ord(A,r)\<close>
    show "minimum(r,{a\<in>A. h`a=b}) \<in> {a\<in>A. h`a=b}"
      using minimum_in by blast
  qed
  moreover from this
  have "?f : B \<rightarrow> A"
      using lam_type[of B _ "\<lambda>_.A"] by simp
  moreover
  have "?f ` w = ?f ` x \<Longrightarrow> w = x" if "w\<in>B" "x\<in>B" for w x
  proof -
    from calculation that
    have "w = h ` minimum(r,{a\<in>A. h`a=w})"
         "x = h ` minimum(r,{a\<in>A. h`a=x})"
      by simp_all
    moreover
    assume "?f ` w = ?f ` x"
    moreover from this and that
    have "minimum(r, {a \<in> A . h ` a = w}) = minimum(r, {a \<in> A . h ` a = x})"
      unfolding minimum_def by simp_all
    moreover from calculation(1,2,4)
    show "w=x" by simp
    qed
  ultimately
  show ?thesis
    unfolding inj_def by blast
qed

lemma well_ord_surj_imp_lepoll:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "B\<lesssim>A"
   unfolding lepoll_def using well_ord_surj_imp_inj_inverse[OF assms]
   by blast

\<comment> \<open>New result\<close>
lemma surj_imp_well_ord:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "\<exists>s. well_ord(B,s)"
  using assms lepoll_well_ord[OF well_ord_surj_imp_lepoll]
  by force

lemma Pow_sing : "Pow({a}) = {0,{a}}"
proof(intro equalityI,simp_all)
  have "z \<in> {0,{a}}" if "z \<subseteq> {a}" for z
    using that by auto
  then
  show " Pow({a}) \<subseteq> {0, {a}}" by auto
qed

lemma Pow_cons:
  shows "Pow(cons(a,A)) = Pow(A) \<union> {{a} \<union> X . X: Pow(A)}"
  using Un_Pow_subset Pow_sing
proof(intro equalityI,auto simp add:Un_Pow_subset)
  {
    fix C D
    assume "\<And> B . B\<in>Pow(A) \<Longrightarrow> C \<noteq> {a} \<union> B" "C \<subseteq> {a} \<union> A" "D \<in> C"
    moreover from this
    have "\<forall>x\<in>C . x=a \<or> x\<in>A" by auto
    moreover from calculation
    consider (a) "D=a" | (b) "D\<in>A" by auto
    from this
    have "D\<in>A"
    proof(cases)
      case a
      with calculation show ?thesis by auto
    next
      case b
      then show ?thesis by simp
    qed
  }
  then show "\<And>x xa. (\<forall>xa\<in>Pow(A). x \<noteq> {a} \<union> xa) \<Longrightarrow> x \<subseteq> cons(a, A) \<Longrightarrow> xa \<in> x \<Longrightarrow> xa \<in> A"
    by auto
qed

lemma app_nm :
  assumes "n\<in>nat" "m\<in>nat" "f\<in>n\<rightarrow>m" "x \<in> nat"
  shows "f`x \<in> nat"
proof(cases "x\<in>n")
  case True
  then show ?thesis using assms in_n_in_nat apply_type by simp
next
  case False
  then show ?thesis using assms apply_0 domain_of_fun by simp
qed

end