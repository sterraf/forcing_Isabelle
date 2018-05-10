theory Renaming imports Main Formula begin

section\<open>Renaming of free variables\<close>

text\<open>TODO: this can be generalized to any pair of functions.\<close>

definition 
  perm_n :: "[i,i] \<Rightarrow> i" where
  "perm_n(m,f) == \<lambda>n \<in> succ(m)  . if n=0 then 0 else succ(f`pred(n))"

lemma nat_succ [TC]: "m \<in> nat \<Longrightarrow> n\<in>nat \<Longrightarrow> n \<in> m \<Longrightarrow> succ(n) \<in> succ(m)"
  by (rule Ord_succ_mem_iff [THEN iffD2],auto)

lemma zero_in [TC]: "m \<in> nat \<Longrightarrow> 0\<in>succ(m)"
  by (rule ltD,auto)
    
lemma succ_pred_eq [simp] :  "m \<in> nat \<Longrightarrow> m \<noteq> 0  \<Longrightarrow> succ(pred(m)) = m"
 by (erule_tac n="m" in natE,auto)

lemma in_n_in_nat :  "m \<in> nat \<Longrightarrow> n \<in> m \<Longrightarrow> n \<in> nat"
 by(rule_tac A="m" in subsetD,erule naturals_subset_nat,assumption)
   
lemma in_succ_in_nat [TC] : "m \<in> nat \<Longrightarrow> n \<in> succ(m) \<Longrightarrow> n \<in> nat"
  apply(rule_tac A="succ(m)" in subsetD,rule naturals_subset_nat)
  apply(rule nat_succ_iff [THEN iffD2],assumption+)
done
    
lemma perm_n_bd [TC] : "m \<in> nat \<Longrightarrow> n\<in> nat \<Longrightarrow> 
      f \<in> m \<rightarrow> m \<Longrightarrow> n \<in> succ(m) \<Longrightarrow> (if n = 0 then 0 else succ(f`pred(n))) \<in> succ(m)"
  apply (simp,rule conjI,simp add: zero_in)
  apply (rule impI, rule nat_succ,assumption) 
  apply (rule_tac A="m" in subsetD, rule naturals_subset_nat,assumption)
  apply (erule_tac A="m" in apply_type)
  apply (rule Ord_succ_mem_iff [THEN iffD1],simp,subst succ_pred_eq,assumption+)
  apply (erule_tac A="m" in apply_type)
  apply (rule Ord_succ_mem_iff [THEN iffD1],simp,subst succ_pred_eq,assumption+)
done

lemma perm_n_ap [TC] : "m \<in> nat \<Longrightarrow> n\<in> nat \<Longrightarrow> f \<in> m \<rightarrow> m \<Longrightarrow> n \<in> succ(m) \<Longrightarrow> perm_n(m,f)`n \<in> succ(m)"
  by (unfold perm_n_def,simp)
    
lemma perm_n_tc [TC] : 
  "m \<in> nat \<Longrightarrow> f \<in> m \<rightarrow> m \<Longrightarrow> perm_n(m,f) \<in> succ(m) \<rightarrow> succ(m)"
  apply (rule Pi_iff [THEN iffD2],rule conjI)
  apply (unfold perm_n_def,rule function_lam)
  apply (rule conjI,auto)
  apply (erule_tac p="x" and A="succ(m)" and 
        b="\<lambda> i. if i = 0 then 0 else succ(f`pred(i))" and 
        P="x\<in>succ(m)\<times>succ(m)" in lamE)
  apply(rename_tac n,case_tac "n=0",simp,simp)
  apply(subgoal_tac "f`pred(n) \<in> m")
  apply(rule nat_succ,assumption+,rule subsetD,erule naturals_subset_nat,assumption+)
  apply (erule_tac A="m" in apply_type)
  apply (rule Ord_succ_mem_iff [THEN iffD1],simp)
  apply (subst succ_pred_eq,rule_tac A="succ(m)" in subsetD,rule naturals_subset_nat)
  apply (simp,assumption+)
done

lemma perm_n_bij [TC] : "m \<in> nat \<Longrightarrow> f \<in> bij(m,m) \<Longrightarrow> perm_n(m,f)\<in>bij(succ(m),succ(m))"  
  apply (unfold perm_n_def)
  apply (rule_tac  d="\<lambda> n. if n =0 then 0 else succ(converse(f)`(pred(n)))" in lam_bijective)
  apply (rule perm_n_bd,assumption+)
  apply(rule_tac A="succ(m)" in subsetD)
  apply(rule naturals_subset_nat, rule nat_succ_iff [THEN iffD2],assumption+)
  apply (erule bij_is_fun,assumption+)
  apply(rule_tac n="y" in natE) 
  apply(erule_tac m="m" in in_succ_in_nat,assumption)
  apply(simp,rule_tac f="converse(f)" in perm_n_bd,assumption)
  apply(erule_tac m="m" in in_succ_in_nat,assumption)
  apply(rule bij_is_fun [OF bij_converse_bij],assumption+)    
  apply(rule_tac n="x" in natE, erule_tac m="m" in in_succ_in_nat,assumption)
  apply(simp,simp,erule left_inverse_bij)
  apply(rule Ord_succ_mem_iff [THEN iffD1],simp,assumption)
  apply(rule_tac n="y" in natE, erule_tac m="m" in in_succ_in_nat,assumption)
  apply(simp,simp,erule right_inverse_bij)
  apply(rule Ord_succ_mem_iff [THEN iffD1],simp,assumption)
done
    
(* TODO: remove this *)

definition 
  sum_id :: "i \<Rightarrow> i" where
  "sum_id(f) == id(1)\<union>(\<lambda> n \<in> nat-1 . succ(f`(pred(n))))"
  
lemma nat_dec : "nat = 1 \<union> (nat-1)"
  by (auto)

lemma suc_pred_z : "n \<in> nat \<Longrightarrow> succ(pred(n))\<noteq>n \<Longrightarrow> n=0"
 by (rule_tac n="n" in natE,auto)
  
lemma suc_comp [TC] : "f \<in> nat \<rightarrow> nat \<Longrightarrow> n \<in> nat-1 \<Longrightarrow> succ(f`(pred(n))) \<in> nat-1"
 by auto

lemma suc_comp_fn [TC] : "f \<in> nat \<rightarrow> nat \<Longrightarrow> 
   (\<lambda> n \<in> nat -1 . succ(f`(pred(n)))) \<in> nat-1 \<rightarrow> nat-1"
 by auto
  
lemma sum_id_tc [TC] : "f \<in> nat \<rightarrow> nat \<Longrightarrow>  sum_id(f) \<in> nat \<rightarrow> nat" 
 apply (subst (1 2) nat_dec)
 apply (unfold sum_id_def)
 apply (rule fun_disjoint_Un,rule id_type)
   prefer 2 apply (auto)
done

lemma sum_id_char : "f \<in> nat \<rightarrow> nat \<Longrightarrow> sum_id(f) = (\<lambda> n \<in> nat . if n =0 then 0 else succ(f`(pred(n))))"    
 apply (rule_tac A=nat and B="\<lambda> n . nat" and D="\<lambda> n . nat" in fun_extension)
 apply (rule sum_id_tc,auto)
 apply (unfold sum_id_def)
 apply (subst fun_disjoint_apply1,auto)
 apply (subst fun_disjoint_apply2,auto)
  done

lemma suc_bij : "f \<in> nat \<rightarrow> nat \<Longrightarrow> 
                 f \<in> bij(nat,nat) \<Longrightarrow> 
                  (\<lambda>n\<in>nat - 1. succ(f ` Arith.pred(n))) \<in> bij(nat - 1, nat - 1)"  
 apply (rule_tac d="\<lambda> n. succ(converse(f)`(pred(n)))" in lam_bijective)
 apply (auto)
 apply (subgoal_tac "converse(f) \<in> nat \<rightarrow> nat",auto)
 apply (rule bij_converse_bij [THEN bij_is_fun],auto)   
 apply (subst (asm) left_inverse_bij,auto)  
 apply (erule suc_pred_z,assumption)
 apply (subst (asm) right_inverse_bij,auto)  
 apply (erule suc_pred_z,assumption)
done

lemma sum_id_bij [TC] : "f \<in> bij(nat,nat) \<Longrightarrow> sum_id(f) \<in> bij(nat,nat)" 
 apply (subst (1 2) nat_dec) 
  apply (unfold sum_id_def)
  apply (rule bij_disjoint_Un)
  apply (simp add: id_bij)
  defer apply (auto)
  apply (rule suc_bij,erule bij_is_fun,assumption)    
  done
    
definition perm_list :: "[i,i,i] \<Rightarrow> i" where
  "perm_list(f,l,i) ==  nat_rec(i,Nil,\<lambda> a e . e@[nth(f`a,l)])"

(* TODO : nice property *)
lemma perm_perm : "\<lbrakk> l \<in> list(A) ; f \<in> bij(length(l),length(l)) \<rbrakk> \<Longrightarrow>
   perm_list(converse(f),perm_list(f,l,length(l)),length(l)) = l"
  apply(induct_tac l,simp,unfold perm_list_def)
  apply(rule nat_rec_0)
  oops
    
consts   rename :: "i=>i"
primrec
  "rename(Member(x,y)) =
      (\<lambda> n \<in> nat . \<lambda>f \<in> bij(n,n). Member (f`x, f`y))"

  "rename(Equal(x,y)) =
      (\<lambda> n \<in> nat . \<lambda>f \<in> bij(n,n). Equal (f`x, f`y))"

  "rename(Nand(p,q)) =
      (\<lambda> n \<in> nat . \<lambda>f \<in> bij(n,n). Nand (rename(p)`n`f, rename(q)`n`f))"

  "rename(Forall(p)) =
      (\<lambda> n \<in> nat . \<lambda>f \<in> bij(n,n). Forall (rename(p) `succ(n)` perm_n(n,f)))"


lemma app_bij [TC] : "f \<in> bij(A,B) \<Longrightarrow> a \<in> A \<Longrightarrow> f`a \<in> B"
  by (frule  bij_is_fun,auto)

lemma succ_in [TC] : "succ(x) < y  \<Longrightarrow> x \<in> y"
 by (rule ltD,rule succ_leE,erule leI)

lemma nat_ord [TC] : "n \<in> nat \<Longrightarrow> Ord(n)"
 by (auto)
  
lemmas Un_least_lt_iffn [TC] =  Un_least_lt_iff [OF nat_ord nat_ord]

lemma pred_le_s [TC] : "n \<in> nat \<Longrightarrow> pred(n) \<le> n"
 by (erule natE,simp,simp)
(*
lemma pred_le [TC] : "m \<in> nat \<Longrightarrow> n < m \<Longrightarrow> pred(n) \<le> m"
  apply (rule_tac j="n" in le_trans,rule pred_le_s)
  apply (erule in_n_in_nat,erule ltD,erule leI)
  done
*)        

lemma pred_le2 : "n\<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> pred(n) < m \<Longrightarrow> n \<le> m"
  by(subgoal_tac "n\<in>nat",rule_tac n="n" in natE,auto)

lemma un_leD1 : "i \<in> nat \<Longrightarrow> j\<in> nat \<Longrightarrow> k \<in> nat \<Longrightarrow>  i \<union> j < k \<Longrightarrow> i < k"   
  by (rule conjunct1,rule  iffD1, rule_tac j="j" in Un_least_lt_iffn,assumption+)

lemma un_leD2 : "i \<in> nat \<Longrightarrow> j\<in> nat \<Longrightarrow> k \<in> nat \<Longrightarrow>  i \<union> j < k \<Longrightarrow> j < k"   
  by (rule conjunct2,rule  iffD1, rule_tac j="j" in Un_least_lt_iffn,assumption+)

lemma ren_tc [TC] : "p \<in> formula \<Longrightarrow> 
      (\<forall> n f . n \<in> nat \<longrightarrow>f \<in> bij(n,n) \<longrightarrow> arity(p) < n \<longrightarrow> rename(p)`n`f \<in> formula)"
  apply (induct_tac p,simp_all)
  apply (clarsimp,subgoal_tac "f`x \<in> nat \<and> f`y \<in> nat",blast,rule conjI)
  apply(rule_tac m="n" in in_n_in_nat,assumption)
  apply(erule app_bij, rule succ_in,rule_tac j="succ(y)" in un_leD1,simp+)
  apply(rule_tac m="n"  in in_n_in_nat,assumption) 
  apply(erule app_bij, rule succ_in,rule_tac i="succ(x)" in un_leD2,simp+)
  apply (clarsimp,subgoal_tac "f`x \<in> nat \<and> f`y \<in> nat",blast,rule conjI)
  apply(rule_tac m="n" in in_n_in_nat,assumption)
  apply(erule app_bij, rule succ_in,rule_tac j="succ(y)" in un_leD1,simp+)
  apply(rule_tac m="n"  in in_n_in_nat,assumption) 
  apply(erule app_bij, rule succ_in,rule_tac i="succ(x)" in un_leD2,simp+)    
  apply(auto,subgoal_tac "arity(p)<n",simp)
  apply(rule conjunct1,rule  iffD1,rule Un_least_lt_iff,auto)
  apply(subgoal_tac "arity(q)<n",simp)
  apply(rule conjunct2,rule  iffD1,rule Un_least_lt_iff,auto)
  apply(rename_tac m g)
  apply(erule_tac x="succ(m)" in allE,rule impE,assumption,simp)
  apply (clarsimp)
  apply(rule_tac x="perm_n(m,g)"  in allE,assumption,rule impE)
  apply (assumption,simp,erule_tac P="arity(p) \<le> m" in impE)
  apply (simp,auto)
  apply(rule pred_le2,auto)
done
  
lemma renSat : "p \<in> formula \<Longrightarrow> (\<forall> f . f \<in> bij(arity(p),arity(p)) \<longrightarrow> 
        arity(p) \<le> length(env) \<longrightarrow>  (* es necesario? *)
        sats(M,p,env) \<longrightarrow> 
        sats(M,rename(p)`f,perm_list(converse(f),env,length(env))))"
  apply (induct_tac p)
  apply (unfold renActEnv_def)
  apply (rule mem_iff_sats [THEN iffD1])  
  apply (simp)