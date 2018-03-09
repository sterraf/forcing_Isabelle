theory WF_e3 imports Main Formula L_axioms Cardinal begin

lemma falso0 : "\<forall>k. k\<in> nat \<longrightarrow> nat_rec(k,0,\<lambda> m . Union) = 0"
  apply (rule allI)
  apply (rule impI)
  apply (rule_tac n="k" in nat_induct)
   apply assumption
   apply (rule nat_rec_0)
   apply (subst nat_rec_succ)
   apply assumption
   apply clarsimp 
  done
    
lemma falso1: "\<forall>k. k\<in> nat \<longrightarrow> 0\<notin>nat_rec(k,0,\<lambda> m . Union)"
  apply (rule allI)
  apply (rule impI)
  apply (subst falso0)
   apply assumption
   apply (rule mem_not_refl)
done
    