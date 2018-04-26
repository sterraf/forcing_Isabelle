theory Sep_instances imports Formula Relative_hacked ZFCaxioms begin

(* We define a "locale" with the hipothesis about model M *)
locale M_separation =
  fixes M
  assumes trans_M:          "Transset(M)"
      and upair_M:          "upair_ax(##M)"
      and Union_M:          "Union_ax(##M)"
      and M_non_empty:      "0 \<in> M"

lemma is_M_separation :
  "Transset(A) \<Longrightarrow> upair_ax(##A) \<Longrightarrow> Union_ax(##A) \<Longrightarrow> 
   0\<in>A \<Longrightarrow>
   M_separation(A)"
  by (rule M_separation.intro,assumption+)

lemma Transset_M :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)

lemma (in M_separation) upair_abs [simp]:
     "z \<in> M ==> upair(##M,a,b,z) \<longleftrightarrow> z={a,b}"
  apply (simp add: upair_def)
  apply (insert trans_M)
  apply (blast intro: Transset_M)
  done


lemma  sep1params : 
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 2  \<rbrakk> \<Longrightarrow> sats(M,ZFseparation(\<phi>),[]) \<longleftrightarrow>
  (\<forall>a\<in>M . \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,\<phi>,[x,d,a])))"
  apply (unfold ZFseparation_def)
  apply (simp, fold incr_bv1_def)
  apply (simp add: sats_incr_bv1_iff)
  done

lemma  sep2params : 
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 3  \<rbrakk> \<Longrightarrow> sats(M,ZFseparation(\<phi>),[]) \<longleftrightarrow>
  (\<forall>b\<in>M. \<forall>a\<in>M . \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,\<phi>,[x,d,a,b])))"
  apply (unfold ZFseparation_def)
  apply (simp, fold incr_bv1_def)
  apply (simp add: sats_incr_bv1_iff)
  done
    
lemma (in M_separation) septest: 
  "((\<forall>a\<in>M . \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,Neg(Member(0,2)),[x,d,a])))) \<longrightarrow>
   (\<forall>w\<in>M. Relative_hacked.separation(##M,\<lambda>x. x\<notin>w))"
  by (simp add: Relative_hacked.separation_def)  

lemma aritm : "1\<union>3 =3 "
  by auto
    
lemma (in M_separation) ZFsep_septest : 
  "sats(M,ZFseparation(Neg(Member(0,2))),[])  \<longrightarrow>
   (\<forall>w\<in>M. Relative_hacked.separation(##M,\<lambda>x. x\<notin>w))"
  apply (simp add: Relative_hacked.separation_def)
  apply (rule  impI)
  apply (rule_tac Q="sats(M, ZFseparation(Neg(Member(0, 2))), [])" and
                  P="((\<forall>b\<in>M .\<forall>a\<in>M . \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,Neg(Member(0,2)),[x,d,a,b]))))"
              in impE)
  apply (simp add:septest)
  apply (rule iffD1)
  apply (rule_tac  \<phi>="Neg(Member(0,2))" in sep2params)
  prefer 3 apply (assumption)
    apply (simp)+
  prefer 2 
  apply (unfold ZFseparation_def)
   apply (fold incr_bv1_def)
   apply (simp)
  apply (simp add: sats_incr_bv1_iff add:aritm)
  apply auto
  done
    
lemma sats_Inter_seps : 
      "sats(M,ZFseparation(Forall(Implies(Member(0,2),Member(1,0)))),[])
       \<longrightarrow> (\<forall>A\<in>M. Relative_hacked.separation(##M, \<lambda>x. \<forall>y\<in>M. y\<in>A \<longrightarrow> x\<in>y))" 
  apply (unfold Relative_hacked.separation_def,simp_all)
  apply (rule impI)
  
  apply (rule sep1params)
(*  apply (rule_tac P="sats(M,ZFseparation(Forall(Implies(Member(0,2),Member(1,0)))),[])" in iffD1) *) 
      
end