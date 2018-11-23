theory Pairing_Axiom imports Names Forcing_data Interface2 begin

context forcing_data
begin

lemma upairs_in_M :
  "a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> {a,b} \<in> M"
  apply (insert upair_ax,simp add: upair_ax_def)
done

lemma one_in_M : "one \<in> M"
  by (insert trans_M,insert one_in_P,insert P_in_M,rule Transset_M)
 
lemma pairs_in_M : 
  " \<lbrakk> a \<in> M ; b \<in> M ; c \<in> M ; d \<in> M \<rbrakk> \<Longrightarrow> {\<langle>a,c\<rangle>,\<langle>b,d\<rangle>} \<in> M"
  by (insert upair_ax,unfold Pair_def,((rule upairs_in_M)+,assumption+)+)

lemma sigma_in_M :
  "one \<in> G \<Longrightarrow> \<tau> \<in> M \<Longrightarrow> \<rho> \<in> M \<Longrightarrow> {\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>} \<in> M"
  by (insert upair_ax,rule pairs_in_M,simp_all add: upair_ax_def one_in_M)
  
lemma valsigma :
  "one \<in> G \<Longrightarrow> {\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>} \<in> M \<Longrightarrow>
   val(G,{\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>}) = {val(G,\<tau>),val(G,\<rho>)}"
  apply (insert one_in_P)
  apply (rule trans)
   apply (rule def_val)
  apply (auto simp add: Sep_and_Replace)
done
      
(* de la siguiente assumption solo usamos one \<in> G *)
lemma pairing_in_MG : 
  "M_generic(G) \<Longrightarrow> upair_ax(##M[G])"
  apply (insert upair_ax)
  apply (simp add: upair_ax_def)
  apply (rule ballI)+
  apply (drule GenExtD)+
  apply (rule bexE,assumption)
  apply (rule_tac A="M" and P="\<lambda>w. y=val(G,w)" in bexE,assumption)
  apply (rename_tac x y \<tau> \<rho>)
  apply (rule_tac x="val(G,{\<langle>\<tau>,one\<rangle>,\<langle>\<rho>,one\<rangle>})" in bexI)
   apply (subst valsigma,rule one_in_G,assumption)
    defer 1 apply (simp add: upair_def)
   apply (rule GenExtI)
   apply (insert sigma_in_M,simp_all add: upair_ax_def)
done

end
end
  
