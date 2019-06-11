theory Nat_Miscellanea imports ZF begin

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
    
lemma succ_ltI : "n \<in> nat \<Longrightarrow> succ(j) < n \<Longrightarrow> j < n"
  apply (rule_tac j="succ(j)" in lt_trans,rule le_refl,rule Ord_succD)
  apply (rule nat_into_Ord,erule in_n_in_nat,erule ltD,simp)
done
      
lemma succ_In : "n \<in> nat \<Longrightarrow> succ(j) \<in> n \<Longrightarrow> j \<in> n"
 by (rule succ_ltI[THEN ltD], auto intro: ltI)
    
lemmas succ_leD = succ_leE[OF leI]
    
lemma succpred_leI : "n \<in> nat \<Longrightarrow>  n \<le> succ(pred(n))"
  by (auto elim: natE)

lemma succpred_n0 : "succ(n) \<in> p \<Longrightarrow> p\<noteq>0"
  by (auto)


lemma funcI : "f \<in> A \<rightarrow> B \<Longrightarrow> a \<in> A \<Longrightarrow> b= f ` a \<Longrightarrow> \<langle>a, b\<rangle> \<in> f"
  by(simp_all add: apply_Pair)

lemmas natEin = natE [OF lt_nat_in_nat]

lemma succ_in : "succ(x) \<le> y  \<Longrightarrow> x \<in> y"
 by (auto dest:ltD)
  
lemmas Un_least_lt_iffn =  Un_least_lt_iff [OF nat_into_Ord nat_into_Ord]

lemma pred_le2 : "n\<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> pred(n) \<le> m \<Longrightarrow> n \<le> succ(m)"
  by(subgoal_tac "n\<in>nat",rule_tac n="n" in natE,auto)
    
lemma pred_le : "n\<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> n \<le> succ(m) \<Longrightarrow> pred(n) \<le> m"
  by(subgoal_tac "pred(n)\<in>nat",rule_tac n="n" in natE,auto)
    
lemma Un_leD1 : "Ord(i)\<Longrightarrow> Ord(j)\<Longrightarrow> Ord(k)\<Longrightarrow>  i \<union> j \<le> k \<Longrightarrow> i \<le> k"   
  by (rule Un_least_lt_iff[THEN iffD1[THEN conjunct1]],simp_all)
  
lemma Un_leD2 : "Ord(i)\<Longrightarrow> Ord(j)\<Longrightarrow> Ord(k)\<Longrightarrow>  i \<union> j \<le>k \<Longrightarrow> j \<le> k"   
  by (rule Un_least_lt_iff[THEN iffD1[THEN conjunct2]],simp_all)

lemma gt1 : "n \<in> nat \<Longrightarrow> i \<in> n \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> i \<noteq> 1 \<Longrightarrow> 1<i"
  by(rule_tac n="i" in natE,erule in_n_in_nat,auto intro: Ord_0_lt)

lemma pred_mono : "m \<in> nat \<Longrightarrow> n \<le> m \<Longrightarrow> pred(n) \<le> pred(m)"
  by(rule_tac n="n" in natE,auto simp add:le_in_nat,erule_tac n="m" in natE,auto)
    
lemma pred2_Un: 
  assumes "j \<in> nat" "m \<le> j" "n \<le> j" 
  shows "pred(pred(m \<union> n)) \<le> pred(pred(j))" 
  using assms pred_mono[of "j"] le_in_nat Un_least_lt pred_mono by simp

lemma nat_union_abs1 : 
  "\<lbrakk> Ord(i) ; Ord(j) ; i \<le> j \<rbrakk> \<Longrightarrow> i \<union> j = j"
  by (rule Un_absorb1,erule le_imp_subset)

lemma nat_union_abs2 : 
  "\<lbrakk> Ord(i) ; Ord(j) ; i \<le> j \<rbrakk> \<Longrightarrow> j \<union> i = j"
  by (rule Un_absorb2,erule le_imp_subset)
    
lemma nat_un_max : "Ord(i) \<Longrightarrow> Ord(j) \<Longrightarrow> i \<union> j = max(i,j)"
  apply(auto simp add:max_def nat_union_abs1)
  apply(auto simp add:  not_lt_iff_le leI nat_union_abs2)
done

lemma nat_un_ty : "Ord(i) \<Longrightarrow>Ord(j) \<Longrightarrow> Ord(i\<union>j)"
  by simp  

lemma nat_max_ty : "Ord(i) \<Longrightarrow>Ord(j) \<Longrightarrow> Ord(max(i,j))"
  unfolding max_def by simp

lemma le_not_lt_nat : "Ord(p) \<Longrightarrow> Ord(q) \<Longrightarrow> \<not> p\<le> q \<Longrightarrow> q \<le> p" 
  by (rule ltE,rule not_le_iff_lt[THEN iffD1],auto,drule ltI[of q p],auto,erule leI)

lemmas nat_simp_union = nat_un_max nat_un_ty nat_max_ty max_def 

end 
