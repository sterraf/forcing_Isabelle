theory Nat_Miscelanea imports Main begin

section\<open>Auxiliary results\<close>

lemmas nat_succI =  Ord_succ_mem_iff [THEN iffD2,OF nat_into_Ord]

lemma nat_succD : "m \<in> nat \<Longrightarrow>  succ(n) \<in> succ(m) \<Longrightarrow> n \<in> m"
  by (drule_tac j="succ(m)" in ltI,auto elim:ltD)
    
lemmas zero_in =  ltD [OF nat_0_le]

lemma in_n_in_nat :  "m \<in> nat \<Longrightarrow> n \<in> m \<Longrightarrow> n \<in> nat"
  by(drule ltI[of "n"],auto simp add: lt_nat_in_nat)
    
lemma in_succ_in_nat : "m \<in> nat \<Longrightarrow> n \<in> succ(m) \<Longrightarrow> n \<in> nat"
  by(auto simp add:in_n_in_nat)
  
lemma ltI_neg : "x \<in> nat \<Longrightarrow> j \<le> x \<Longrightarrow> j \<noteq> x \<Longrightarrow> j < x"
  by (simp add: le_iff)
    
lemma succ_pred_eq  :  "m \<in> nat \<Longrightarrow> m \<noteq> 0  \<Longrightarrow> succ(pred(m)) = m"
 by (auto elim: natE)

lemma succ_mono : "j \<le> n \<Longrightarrow> succ(j) \<le> succ(n)"
  by (auto)
    
lemma succ_ltI : "n \<in> nat \<Longrightarrow> succ(j) < n \<Longrightarrow> j < n"
  apply (rule_tac j="succ(j)" in lt_trans,rule le_refl,rule Ord_succD)
  apply (rule nat_into_Ord,erule in_n_in_nat,erule ltD,simp)
done
      
lemma succ_In : "n \<in> nat \<Longrightarrow> succ(j) \<in> n \<Longrightarrow> j \<in> n"
 by (rule ltD, rule succ_ltI, auto intro: succ_ltI ltI)
    
lemmas succ_leD = succ_leE[OF leI]
    
lemma succpred_leI : "n \<in> nat \<Longrightarrow>  n \<le> succ(pred(n))"
  by (erule natE,simp_all)

lemma succpred_n0 : "p \<in> nat \<Longrightarrow>  succ(n) \<in> p \<Longrightarrow> p\<noteq>0"
  by (erule natE,simp_all)


lemma funcI : "f \<in> A \<rightarrow> B \<Longrightarrow> a \<in> A \<Longrightarrow> b= f ` a \<Longrightarrow> \<langle>a, b\<rangle> \<in> f"
  by(simp_all add: apply_Pair)

lemma bij_is_function  : "f\<in>bij(A,B) \<Longrightarrow> function(f)"
  by(drule bij_is_fun,simp add: Pi_iff)

lemmas natEin = natE [OF lt_nat_in_nat]  

lemma trich_nat : "\<lbrakk> m \<in> nat ; n \<le> m ; n \<noteq> m ; \<not> n < m \<rbrakk> \<Longrightarrow> P"
  apply(subgoal_tac "Ord(n)" "Ord(m)" "\<not> m < n")
  apply(rule_tac i="n" and j="m" in Ord_linear_lt;blast)
  apply(erule le_imp_not_lt,erule nat_into_Ord)
  apply(rule nat_into_Ord[OF le_in_nat];assumption)
done

lemma pred0E : "i \<in> nat \<Longrightarrow> pred(i) = 0 \<Longrightarrow> i = 1 | i = 0"
  by(rule natE,simp+)

lemma succ_in : "succ(x) \<le> y  \<Longrightarrow> x \<in> y"
 by (auto dest:ltD) 
  
lemmas Un_least_lt_iffn =  Un_least_lt_iff [OF nat_into_Ord nat_into_Ord]

lemma pred_le2 : "n\<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> pred(n) \<le> m \<Longrightarrow> n \<le> succ(m)"
  by(subgoal_tac "n\<in>nat",rule_tac n="n" in natE,auto)
    
lemma pred_le : "n\<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> n \<le> succ(m) \<Longrightarrow> pred(n) \<le> m"
  by(subgoal_tac "pred(n)\<in>nat",rule_tac n="n" in natE,auto)
    
lemma un_leD1 : "i \<in> nat \<Longrightarrow> j\<in> nat \<Longrightarrow> k \<in> nat \<Longrightarrow>  i \<union> j \<le> k \<Longrightarrow> i \<le> k"   
  by (rule conjunct1,rule  iffD1, rule_tac j="j" in Un_least_lt_iffn,assumption)
  
lemma un_leD2 : "i \<in> nat \<Longrightarrow> j\<in> nat \<Longrightarrow> k \<in> nat \<Longrightarrow>  i \<union> j \<le>k \<Longrightarrow> j \<le> k"   
  by (rule conjunct2,rule  iffD1, rule_tac j="j" in Un_least_lt_iffn,assumption)

lemma un_leI : "i \<in> nat \<Longrightarrow> j\<in> nat \<Longrightarrow> k \<in> nat \<Longrightarrow> i \<le> k \<Longrightarrow> j \<le> k \<Longrightarrow> i \<union> j \<le> k"   
  by(subst Un_def, rule Union_le,auto) 

lemma un_leI' : "k \<in> nat \<Longrightarrow> i \<le> k \<Longrightarrow> j \<le> k \<Longrightarrow> i \<union> j \<le> k"   
  by(subst Un_def, rule Union_le,auto) 

lemma gt1 : "n \<in> nat \<Longrightarrow> i \<in> n \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> i \<noteq> 1 \<Longrightarrow> 1<i"
  by(rule_tac n="i" in natE,erule in_n_in_nat,auto intro: Ord_0_lt)


lemma pred_mono : "m \<in> nat \<Longrightarrow> n \<le> m \<Longrightarrow> pred(n) \<le> pred(m)"
  by(rule_tac n="n" in natE,auto simp add:le_in_nat,erule_tac n="m" in natE,auto)
    
lemma pred2_Un: 
  assumes "j \<in> nat" "m \<le> j" "n \<le> j" 
  shows "pred(pred(m \<union> n)) \<le> pred(pred(j))" 
  using assms pred_mono[of "j"] le_in_nat un_leI' pred_mono by simp
    
end 