(*
----------------------------------------------
First steps towards a formalization of Forcing
---------------------------------------------

Proof of preservation of the axiom of Pairing in the generic
extension M[G].

*)

theory Gen_ext_pair imports Names Forcing_data begin

context M_extra_assms
begin
  
lemma one_in_M : "one \<in> M"
  by (insert trans_M,insert one_in_P,insert P_in_M,rule Transset_intf)
 
lemma pairs_in_M : 
  " \<lbrakk> a \<in> M ; b \<in> M ; c \<in> M ; d \<in> M \<rbrakk> \<Longrightarrow> {\<langle>a,c\<rangle>,\<langle>b,d\<rangle>} \<in> M"
  by (unfold Pair_def, ((rule upairM)+,assumption+)+)

lemma sigma_in_M :
  "one \<in> G \<Longrightarrow> \<tau> \<in> M \<Longrightarrow> \<rho> \<in> M \<Longrightarrow> {\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>} \<in> M"
  by (rule pairs_in_M,simp_all add: upair_ax_def one_in_M)
  
lemma valsigma :
  "one \<in> G \<Longrightarrow> {\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>} \<in> M \<Longrightarrow>
   val(G,{\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>}) = {val(G,\<tau>),val(G,\<rho>)}"
  apply (insert one_in_P)
  apply (rule trans)
   apply (rule def_val,assumption)
  apply (auto simp add: Sep_and_Replace)
done
      
lemma pairing_axiom : 
  "one \<in> G \<Longrightarrow> upair_ax(##M[G])"
  apply (simp add: upair_ax_def)
  apply (rule ballI)+
  apply (drule GenExtD)+
  apply (rule bexE,assumption)
  apply (rule_tac A="M" and P="\<lambda>w. y=val(G,w)" in bexE,assumption)
  apply (rename_tac x y \<tau> \<rho>)
  apply (rule_tac x="val(G,{\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>})" in bexI)
   apply (subst valsigma,assumption+)
   defer 1 apply (simp add: upair_def)
   apply (rule GenExtI)
   apply (insert sigma_in_M,simp_all add: upair_ax_def)
done

end
end
  
