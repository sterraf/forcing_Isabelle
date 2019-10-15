theory Mostowski imports Interface Recursion_Thms begin

definition Hmos :: "[i,i,i,i] \<Rightarrow> i" where
  "Hmos(A,R,x,f) == {f`u . u \<in> (R-``{x}) \<inter> A}"
  
definition mos :: "[i,i,i] \<Rightarrow> i" where
  "mos(A,R,x) = wfrec[A](R,x,Hmos(A,R))"
  
lemma mos_eq : 
  assumes wfr:"wf[A](R)" and 1:"x \<in>A"
  shows "mos(A,R,x) = {mos(A,R,y) . y \<in> (R-``{x})\<inter>A}"
proof -
  have "mos(A,R,x) = wfrec[A](R,x,Hmos(A,R))"
    unfolding mos_def ..
  also have "... = Hmos(A,R,x,\<lambda>y\<in>(R-``{x})\<inter>A. wfrec[A](R,y,Hmos(A,R)))" (is "_=Hmos(_,_,_,?f)")
    by (subst (1) wfrec_on[OF wfr 1],simp)
  also have "... = {?f`u . u \<in> R-``{x}\<inter>A}"
    unfolding Hmos_def ..
  also have "... = {wfrec[A](R,u,Hmos(A,R)) . u \<in> R-``{x} \<inter>A}"
    by simp
  also have "... = {mos(A,R,u) . u \<in> R-``{x}\<inter>A}"
    unfolding mos_def ..
  finally show ?thesis by simp
qed

lemma mos_trans :
  assumes "wf(R)" 
  shows "Transset({mos(A,R,x) . x \<in> A})"
proof -
  let ?mA="{mos(A,R,x) . x \<in> A}"
  {
    fix x y
    assume "x\<in>?mA" "y\<in>x"
    then obtain u where
      "u\<in>A" "x=mos(A,R,u)" "y\<in>mos(A,R,u)" using assms mos_eq by blast
    then obtain z where
      "z\<in>R-``{u}\<inter>A" "y=mos(A,R,z)" using assms mos_eq[OF wf_imp_wf_on[OF \<open>wf(R)\<close>] \<open>u\<in>A\<close>] by force
    then have "y \<in> ?mA" by blast
  } then show ?thesis using TranssetI by blast
qed