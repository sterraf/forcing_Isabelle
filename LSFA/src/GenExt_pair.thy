theory GenExt_pair imports Names Forcing_data Relative begin

context forcing_data
begin
  
lemma upair_abs [simp]:
     "z \<in> M ==> upair(##M,a,b,z) \<longleftrightarrow> z={a,b}"
  apply (simp add: upair_def)
  apply (insert trans_M)
  apply (blast intro: Transset_M)
done

  
lemma upairs_in_M :
  "upair_ax(##M) \<Longrightarrow> a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> {a,b} \<in> M"
  apply (rule_tac M="##M" and P="\<lambda>z. upair(##M,a,b,z)" in rexE)
  apply (rule_tac M="##M" and x="b" and P="\<lambda>y. \<exists>z[##M]. upair(##M,a,y,z)" in rspec)
  apply (rule_tac M="##M" and x="a" and 
            P="\<lambda>x. \<forall>y[##M]. \<exists>z[##M]. upair(##M,x,y,z)" in rspec)
  apply (simp add: upair_ax_def,simp+)
done

lemma one_in_M : "one \<in> M"
  by (insert trans_M,insert one_in_P,insert P_in_M,rule Transset_M)
 
lemma pairs_in_M : 
  " upair_ax(##M) \<Longrightarrow> a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> {<a,one>,<b,one>} \<in> M"
  apply (insert one_in_M)
  apply (unfold Pair_def)
  apply ((rule upairs_in_M)+,assumption+)+
done

lemma sigma_as_collect :
  "{<\<tau>,one>,<\<rho>,one>} = {x\<in>{\<tau>,\<rho>}\<times>P. snd(x) = one} " 
  apply (insert one_in_P)
  apply auto
done
    
lemma valsigma :
  "one \<in> G \<Longrightarrow> \<tau> \<in> M \<Longrightarrow> \<rho> \<in> M \<Longrightarrow> {<\<tau>,one>,<\<rho>,one>} \<in> M \<Longrightarrow>
   val(G,{<\<tau>,one>,<\<rho>,one>}) = {val(G,\<tau>),val(G,\<rho>)}"
  apply (insert one_in_P)
  apply (subst sigma_as_collect)
  apply (rule trans)
  apply (rule val_of_name)
  apply (subst sigma_as_collect[symmetric],assumption)
  apply auto
done
    
lemma pair_preserv : 
  "one \<in> G \<Longrightarrow> upair_ax(##M) \<Longrightarrow> upair_ax(##M[G])"
  apply (simp add: upair_ax_def)
  apply (rule ballI)+
  apply (drule def_GenExt1)+
  apply (rule bexE,assumption)
  apply (rule_tac A="M" and P="\<lambda>w. y=val(G,w)" in bexE,assumption)
  apply (rename_tac x y \<tau> \<rho>)
  apply (rule_tac x="val(G,{<\<tau>,one>,<\<rho>,one>})" in bexI)
   apply (subst valsigma,assumption+)
  apply (rule pairs_in_M,simp_all add: upair_ax_def)
  apply (rule_tac b="x" in ssubst,assumption)
   apply (rule_tac b="y" in ssubst,assumption)
   apply (simp add: upair_def)
  apply (rule def_GenExt2)
  apply (rule pairs_in_M,simp_all add: upair_ax_def)
done
    
end
end
  
