theory GenExt_pair imports Names Forcing_data Relative begin

context forcing_data
begin
  
lemma upair_abs [simp]:
     "z \<in> M \<Longrightarrow> upair(##M,a,b,z)  \<longleftrightarrow> z={a,b}"
  apply (simp add: upair_def)
  apply (insert trans_M)
  apply (blast intro: Transset_M)
done

lemma upairs_in_M :
  "upair_ax(##M) \<Longrightarrow> a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> {a,b} \<in> M"
  apply (simp add: upair_ax_def)
done

lemma one_in_M : "one \<in> M"
  by (insert trans_M,insert one_in_P,insert P_in_M,rule Transset_M)
 
lemma pairs_in_M : 
  " \<lbrakk> upair_ax(##M) ; a \<in> M ; b \<in> M ; c \<in> M ; d \<in> M \<rbrakk> \<Longrightarrow> {\<langle>a,c\<rangle>,\<langle>b,d\<rangle>} \<in> M"
  apply (unfold Pair_def)
  apply ((rule upairs_in_M)+,assumption+)+
done

lemma sigma_in_M :
  "upair_ax(##M) \<Longrightarrow> one \<in> G \<Longrightarrow> \<tau> \<in> M \<Longrightarrow> \<rho> \<in> M \<Longrightarrow> {\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>} \<in> M"
  by (rule pairs_in_M,simp_all add: upair_ax_def one_in_M)
  
lemma valsigma :
  "one \<in> G \<Longrightarrow> {\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>} \<in> M \<Longrightarrow>
   val(G,{\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>}) = {val(G,\<tau>),val(G,\<rho>)}"
  apply (insert one_in_P)
  apply (rule trans)
   apply (rule def_val,assumption)
  apply (auto simp add: Sep_and_Replace)
done
      
lemma pair_preserv : 
  "one \<in> G \<Longrightarrow> upair_ax(##M) \<Longrightarrow> upair_ax(##M[G])"
  apply (simp add: upair_ax_def)
  apply (rule ballI)+
  apply (drule def_GenExt1)+
  apply (rule bexE,assumption)
  apply (rule_tac A="M" and P="\<lambda>w. y=val(G,w)" in bexE,assumption)
  apply (rename_tac x y \<tau> \<rho>)
  apply (rule_tac x="val(G,{\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>})" in bexI)
   apply (subst valsigma,assumption+)
   defer 1 apply (simp add: upair_def)
   apply (rule def_GenExt2)
   apply (insert sigma_in_M,simp_all add: upair_ax_def)
done

end
end
  
