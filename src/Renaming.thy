theory Renaming imports Formula begin

section\<open>Auxiliary results\<close>

lemmas nat_succI =  Ord_succ_mem_iff [THEN iffD2,OF nat_into_Ord]

lemma nat_succD : "m \<in> nat \<Longrightarrow>  succ(n) \<in> succ(m) \<Longrightarrow> n \<in> m"
  by (drule_tac j="succ(m)" in ltI,auto,erule ltD)
    
lemmas zero_in [TC] =  ltD [OF nat_0_le]

lemma in_n_in_nat :  "m \<in> nat \<Longrightarrow> n \<in> m \<Longrightarrow> n \<in> nat"
 by(rule_tac A="m" in subsetD,erule naturals_subset_nat,assumption)

    
lemma in_succ_in_nat [TC] : "m \<in> nat \<Longrightarrow> n \<in> succ(m) \<Longrightarrow> n \<in> nat"
  by(rule le_in_nat[OF leI],erule ltI,simp+)
  
lemma ltI_neg : "x \<in> nat \<Longrightarrow> j \<le> x \<Longrightarrow> j \<noteq> x \<Longrightarrow> j < x"
  by (insert le_iff,simp)

lemma leD_cases [simp] : "x \<in> nat \<Longrightarrow> j \<le> x \<Longrightarrow> j = x \<or> j < x"
  by(insert le_iff,auto)
    
lemma succ_pred_eq [simp] :  "m \<in> nat \<Longrightarrow> m \<noteq> 0  \<Longrightarrow> succ(pred(m)) = m"
 by (erule_tac n="m" in natE,auto)

lemma succ_mono : "j \<le> n \<Longrightarrow> succ(j) \<le> succ(n)"
  by (auto)
    
lemma succ_ltI : "n \<in> nat \<Longrightarrow> succ(j) < n \<Longrightarrow> j < n"
  apply (rule_tac j="succ(j)" in lt_trans,rule le_refl,rule Ord_succD)
  apply (rule nat_into_Ord,erule in_n_in_nat,erule ltD,simp)
done
    
lemma le_in_nat [TC] :  "m \<in> nat \<Longrightarrow> n \<le> m \<Longrightarrow> n \<in> nat"
  apply (case_tac "m=n",simp)
  apply(frule ltI_neg,auto,erule_tac m="m" in in_n_in_nat,erule ltD)
done
  
lemma succ_In : "n \<in> nat \<Longrightarrow> succ(j) \<in> n \<Longrightarrow> j \<in> n"
 by (rule ltD,rule succ_ltI,simp,rule ltI,auto)
    
lemmas succ_leD = succ_leE[OF leI]
    
lemma succpred_leI : "n \<in> nat \<Longrightarrow>  n \<le> succ(pred(n))"
  by (erule natE,simp+)

lemma funcI : "f \<in> A \<rightarrow> B \<Longrightarrow> a \<in> A \<Longrightarrow> b= f ` a \<Longrightarrow> \<langle>a, b\<rangle> \<in> f"
  by(simp,rule apply_Pair,simp+)

lemma bij_is_function [TC] : "f\<in>bij(A,B) \<Longrightarrow> function(f)"
  by(drule bij_is_fun,simp add: Pi_iff)

lemmas natEin = natE [OF lt_nat_in_nat]  

lemma trich_nat : "\<lbrakk> m \<in> nat ; n \<le> m ; n \<noteq> m ; \<not> n < m \<rbrakk> \<Longrightarrow> P"
  apply(subgoal_tac "Ord(n)" "Ord(m)" "\<not> m < n")
  apply(rule_tac i="n" and j="m" in Ord_linear_lt,blast+)
  apply(erule le_imp_not_lt,erule nat_into_Ord)
  apply(rule nat_into_Ord[OF le_in_nat],assumption+)
done

lemma pred0E : "i \<in> nat \<Longrightarrow> pred(i) = 0 \<Longrightarrow> i = 1 | i = 0"
  by(rule natE,simp+)


lemma succ_in : "succ(x) \<le> y  \<Longrightarrow> x \<in> y"
 by (auto,rule ltD) 
  
lemmas Un_least_lt_iffn [TC] =  Un_least_lt_iff [OF nat_into_Ord nat_into_Ord]

lemma pred_le2 : "n\<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> pred(n) < m \<Longrightarrow> n \<le> m"
  by(subgoal_tac "n\<in>nat",rule_tac n="n" in natE,auto)

lemma un_leD1 : "i \<in> nat \<Longrightarrow> j\<in> nat \<Longrightarrow> k \<in> nat \<Longrightarrow>  i \<union> j \<le> k \<Longrightarrow> i \<le> k"   
  by (rule conjunct1,rule  iffD1, rule_tac j="j" in Un_least_lt_iffn,assumption+)

lemma un_leD2 : "i \<in> nat \<Longrightarrow> j\<in> nat \<Longrightarrow> k \<in> nat \<Longrightarrow>  i \<union> j < k \<Longrightarrow> j < k"   
  by (rule conjunct2,rule  iffD1, rule_tac j="j" in Un_least_lt_iffn,assumption+)


lemma app_bij [TC] : "f \<in> bij(A,B) \<Longrightarrow> a \<in> A \<Longrightarrow> f`a \<in> B"
  by (frule  bij_is_fun,auto)
        
section\<open>Involutions\<close>

definition invol :: "[i,i] \<Rightarrow> o" where
  "invol(A,f) == f\<in>bij(A,A) \<and> f = converse(f)"
  
lemma invol_bij : "invol(A,f) \<Longrightarrow> f\<in>bij(A,A)" by (unfold invol_def,simp)
lemma invol_conv : "invol(A,f) \<Longrightarrow> f=converse(f)" by (unfold invol_def,simp)
lemmas invol_conv_bij =  bij_converse_bij[OF invol_bij]
lemmas invol_fun = bij_is_fun[OF invol_bij]
lemmas invol_conv_fun = bij_is_fun[OF invol_conv_bij]
  
lemma invol_inverse [simp]: "invol(A,f) \<Longrightarrow> a \<in> A \<Longrightarrow> f`(f`a) = a"
  by(unfold invol_def,clarsimp,subst sym[of "converse(f)"],simp,rule right_inverse_bij,simp+)
  
section\<open>Renaming of free variables\<close>


definition 
  sum_id :: "[i,i] \<Rightarrow> i" where
  "sum_id(m,f) == \<lambda>n \<in> succ(m)  . if n=0 then 0 else succ(f`pred(n))"
  
lemma sum_id0 [simp] : "sum_id(m,f)`0 = 0"
  by(unfold sum_id_def,simp)

lemma sum_idS [simp] : "succ(x) \<in> succ(m) \<Longrightarrow> sum_id(m,f)`succ(x) = succ(f`x)"
  by(unfold sum_id_def,simp)
    
    
lemma sum_id_bd [TC] : "m \<in> nat \<Longrightarrow> n\<in> nat \<Longrightarrow> 
      f \<in> m \<rightarrow> m \<Longrightarrow> n \<in> succ(m) \<Longrightarrow> (if n = 0 then 0 else succ(f`pred(n))) \<in> succ(m)"
  apply (simp,rule conjI,simp add: zero_in)
  apply (rule impI, rule nat_succI,assumption) 
  apply (rule_tac A="m" in subsetD,simp)
  apply (erule_tac A="m" in apply_type)
  apply (rule Ord_succ_mem_iff [THEN iffD1],simp,subst succ_pred_eq,assumption+)
done

lemma sum_id_ap [TC] : "m \<in> nat \<Longrightarrow> f \<in> m \<rightarrow> m \<Longrightarrow> 
    n \<in> succ(m) \<Longrightarrow> sum_id(m,f)`n \<in> succ(m)"
  by (unfold sum_id_def,simp)
    
lemma sum_id_tc [TC] : 
  "m \<in> nat \<Longrightarrow> f \<in> m \<rightarrow> m \<Longrightarrow> sum_id(m,f) \<in> succ(m) \<rightarrow> succ(m)"
  apply (rule Pi_iff [THEN iffD2],rule conjI)
  apply (unfold sum_id_def,rule function_lam)
  apply (rule conjI,auto)
  apply (erule_tac p="x" and A="succ(m)" and 
        b="\<lambda> i. if i = 0 then 0 else succ(f`pred(i))" and 
        P="x\<in>succ(m)\<times>succ(m)" in lamE)
  apply(rename_tac n,case_tac "n=0",simp,simp)
  apply(subgoal_tac "f`pred(n) \<in> m")
   apply(rule nat_succI,assumption+)
  apply (erule_tac A="m" in apply_type)
  apply (rule Ord_succ_mem_iff [THEN iffD1],simp)
  apply (subst succ_pred_eq,rule_tac A="succ(m)" in subsetD,rule naturals_subset_nat)
  apply (simp+)
done

lemma sum_id_bij [TC] : "m \<in> nat \<Longrightarrow> f \<in> bij(m,m) \<Longrightarrow> sum_id(m,f)\<in>bij(succ(m),succ(m))"  
  apply (unfold sum_id_def)
  apply (rule_tac  d="\<lambda> n. if n =0 then 0 else succ(converse(f)`(pred(n)))" in lam_bijective)
  apply (rule sum_id_bd,assumption+)
  apply(rule_tac A="succ(m)" in subsetD)
  apply(rule naturals_subset_nat, rule nat_succ_iff [THEN iffD2],assumption+)
  apply(rule_tac n="x" in natE,erule_tac m="m" in in_succ_in_nat,assumption)
  apply(erule bij_is_fun)+
  apply(simp,rule_tac f="converse(f)" in sum_id_bd,assumption)
  apply(erule_tac m="m" in in_succ_in_nat,assumption)
  apply(rule bij_is_fun [OF bij_converse_bij],assumption+)    
  apply(rule_tac n="x" in natE, erule_tac m="m" in in_succ_in_nat,assumption)
  apply(simp+,erule left_inverse_bij)
  apply(rule Ord_succ_mem_iff [THEN iffD1],simp+)
  apply(rule_tac n="y" in natE, erule_tac m="m" in in_succ_in_nat,assumption)
  apply(simp+,erule right_inverse_bij)
  apply(rule Ord_succ_mem_iff [THEN iffD1],simp+)
done

lemma conv_sum_id [simp] : "m \<in> nat \<Longrightarrow> f \<in> bij(m,m) \<Longrightarrow> converse(sum_id(m,f))`0 = 0"
  by(subst (1) sum_id0[symmetric],subst left_inverse_bij,erule sum_id_bij,auto)
    
lemma sum_idRel : "m \<in> nat \<Longrightarrow> f\<in>bij(m,m) \<Longrightarrow> x \<in> m \<Longrightarrow>
  <succ(x),y> \<in> sum_id(m,f) \<Longrightarrow> y=succ(f`x)" 
  apply(subgoal_tac "sum_id(m,f)`(succ(x)) = succ(f`x)")
  apply(drule function_apply_equality)
  apply(rule fun_is_function,rule bij_is_fun,rule sum_id_bij,simp+)
  apply(rule sum_idS,rule nat_succI,simp+)
done


lemma conv_perm_s : "m \<in> nat \<Longrightarrow> f \<in> bij(m,m) \<Longrightarrow> succ(n) \<in> succ(m) \<Longrightarrow>
    (converse(sum_id(m, f))`succ(n) = sum_id(m, converse(f))`succ(n))"  
  apply(rule function_apply_equality,rule converseI)
  apply(subst sum_idS,simp)
  apply(rule funcI,rule sum_id_tc,simp,erule bij_is_fun)
    prefer 2 apply(subst sum_idS)
    prefer 2 apply(subst right_inverse_bij,simp+)
    apply(rule nat_succD,simp+,rule nat_succI,simp)
   apply(rule apply_type,rule bij_is_fun,erule bij_converse_bij,rule nat_succD,simp+)
done

lemma conv_perm_ap : "m \<in> nat \<Longrightarrow> f \<in> bij(m,m) \<Longrightarrow> n \<in> succ(m) \<Longrightarrow>
    (converse(sum_id(m, f))`n) = sum_id(m, converse(f))`n"  
  apply(rule_tac n="n" in natE,rule_tac m="succ(m)" in in_n_in_nat,simp+)
  apply(subst conv_perm_s,simp+)
done
    
lemma conv_perm : "m \<in> nat \<Longrightarrow> f \<in> bij(m,m) \<Longrightarrow> 
    converse(sum_id(m, f)) = sum_id(m, converse(f))"
  apply(rule fun_extension,rule bij_is_fun,rule bij_converse_bij,simp+)
  apply(rule bij_is_fun,simp+,rule conv_perm_ap,simp+)
done

text\<open>This function is a more general version of @{term upt}, which
can be recovered as @{term "tabulate(id)"}.\<close>
definition 
  tabulate :: "[i,i] \<Rightarrow> i" where 
  "tabulate(f,i) = nat_rec(i,Nil, \<lambda> j l . l@[f`j])" 
 
lemma tab_succ : "\<lbrakk> j \<in> nat ; f \<in> n \<rightarrow> A \<rbrakk> \<Longrightarrow> 
                       tabulate(f,succ(j)) = tabulate(f,j)@[f`j]"
   by(unfold tabulate_def,subst nat_rec_succ,assumption+,simp)
  
  
lemma tab_tc_aux [rule_format] : "i \<in> nat \<Longrightarrow> 
  \<forall> m f . i\<le> m \<longrightarrow> f \<in> m \<rightarrow> A \<longrightarrow> tabulate(f,i) \<in> list(A)"
  apply(erule_tac n="i" in nat_induct)
  apply(clarsimp,unfold tabulate_def,subst nat_rec_0,simp)
  apply(rename_tac i)
  apply(clarsimp,subst nat_rec_succ,simp,rule app_type)
  prefer 2 apply(simp,erule apply_type,erule ltD)
  apply(rename_tac n g)
  apply(subgoal_tac "i\<le>n")
  apply(auto,erule leI)
done

lemma tab_tc [TC] : "\<lbrakk> j \<in> nat ;  f \<in> j \<rightarrow> A \<rbrakk> \<Longrightarrow> 
                       tabulate(f,j) \<in> list(A)"
 by (rule tab_tc_aux,assumption,auto)


lemma tab_length [simp] : "\<lbrakk> j \<in> nat \<rbrakk> \<Longrightarrow> \<forall> n . n \<in> nat \<longrightarrow> j \<le> n \<longrightarrow> (\<forall> f . (f \<in> n \<rightarrow> A) \<longrightarrow> 
                       length(tabulate(f,j)) = j)"
  apply(erule nat_induct)
  apply(unfold tabulate_def,subst nat_rec_0,(rule allI,rule impI)+,simp)
  apply((rule allI,rule impI)+,subst nat_rec_succ,assumption)
  apply(rule impI,rule allI,rule impI)
  apply(subst length_app,fold tabulate_def,rule tab_tc_aux,simp)
  apply(rule_tac j="succ(x)" in le_trans,simp,assumption+,simp)
  apply(rule apply_type,assumption,erule ltD,simp)
  apply(subst natify_ident,rule length_type,rule tab_tc_aux,assumption)
  apply(erule leI,assumption)
  apply(subgoal_tac "x\<le>n",simp,erule leI)
done

lemma tab_length2 [simp] : "\<lbrakk> j \<in> nat ; n \<in> nat ;  f \<in> n \<rightarrow> A ; j < n \<rbrakk> \<Longrightarrow> 
                       length(tabulate(f,j)) = j"
  by(subgoal_tac "j\<le>n",insert tab_length,simp,erule leI)


definition nth_i :: "i \<Rightarrow> i" where
  "nth_i(l) == \<lambda> n\<in>length(l).nth(n,l)"

lemma nth_eq [simp] : "l \<in> list(A) \<Longrightarrow> n \<in> length(l) \<Longrightarrow> nth_i(l)`n=nth(n,l)"
  by(unfold nth_i_def,simp)
    
lemma nth_i_type [TC] : "l \<in> list(A) \<Longrightarrow> nth_i(l) \<in> length(l) \<rightarrow> A"
  by (unfold nth_i_def,rule lam_type,rule nth_type,auto,rule ltI,simp,rule nat_into_Ord,auto)

text\<open>The action of a permutation over a list.\<close>
definition perm_list :: "[i,i] \<Rightarrow> i" where
 "perm_list(f,l) ==tabulate(nth_i(l) O f,length(l))"


lemma nth_tab_gen: 
  "m \<in>nat \<Longrightarrow> \<forall> n . n \<in> nat \<longrightarrow> m \<le> n \<longrightarrow> (\<forall> f . (f \<in> n \<rightarrow> A \<longrightarrow>(
   \<forall> j . j < m \<longrightarrow> nth(j,tabulate(f,m)) = f`j)))" 
  apply(erule nat_induct,simp)
  apply(rule allI,(rule impI)+)+
  apply(case_tac "j=x")
  apply(simp,unfold tabulate_def,subst nat_rec_succ,assumption)
   apply(fold tabulate_def,subst nth_append)
  apply(rule_tac i="x" and m="n" and A="A" in tab_tc_aux,assumption,erule leI,assumption+)
  apply(simp,blast)
  apply(subst tab_succ,assumption+,simp,subst nth_append) 
    apply(rule_tac i="x" and m="n" and A="A" in tab_tc_aux,assumption,erule leI,assumption+)
    apply(erule_tac m="x" in le_in_nat,assumption)
  apply(simp,rule conjI)
  prefer 2 apply(rule impI,erule_tac m="x" and n="j" in trich_nat,assumption+)
  apply(subgoal_tac "x\<le>n",blast,erule leI)
  done

lemma nth_tab: 
  "j \<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> f \<in> m \<rightarrow> A \<Longrightarrow> j \<in> m \<Longrightarrow> nth(j,tabulate(f,m)) = f`j" 
 by(subgoal_tac "j<m",insert nth_tab_gen,auto,erule ltI,erule nat_into_Ord)
 
lemma nth_after_type [TC]: 
  "l\<in>list(A) \<Longrightarrow> f \<in> length(l) \<rightarrow> length(l) \<Longrightarrow>
   j < length(l) \<Longrightarrow> nth(f`j,l) \<in> A" 
  apply(subgoal_tac "f`j < length(l)")
  apply(erule nth_type,assumption)
  apply(rule ltI,erule apply_type,erule ltE,simp+)
done


lemma perm_list_tc [TC] : " l \<in> list(A) \<Longrightarrow> 
    f\<in> bij(length(l),length(l)) \<Longrightarrow> 
    perm_list(f,l) \<in> list(A)"
  apply(unfold perm_list_def,rule tab_tc,rule length_type,simp)
  apply(rule comp_fun,erule bij_is_fun,simp)
done

lemma perm_list_length [simp] : " l \<in> list(A) \<Longrightarrow> 
    f\<in> bij(length(l),length(l)) \<Longrightarrow> 
    length(perm_list(f,l)) = length(l)"
  apply(unfold perm_list_def,subst tab_length,simp,rule length_type,simp+)
  apply(rule comp_fun,erule bij_is_fun,simp+)
done
    
lemma nth_tab_perm [simp] : "\<lbrakk> m \<in> nat ; h \<in> m \<rightarrow> A ; f \<in> bij(m,m) ; n \<in> m \<rbrakk> \<Longrightarrow>
  nth(converse(f)`n,tabulate(h O f,m)) = h`n"
 apply(subst nth_tab,auto,rule in_n_in_nat,assumption,rule apply_type)    
 apply(rule bij_is_fun[OF bij_converse_bij],assumption+)
 apply(rule comp_fun,rule bij_is_fun,assumption+)
 apply(subst comp_fun_apply,erule bij_is_fun)
 apply(rule apply_type,rule bij_is_fun[OF bij_converse_bij],assumption+)
 apply(subst right_inverse_bij,simp+)
done

lemma perm_list_eq [simp] : "\<lbrakk> l \<in> list(A) ; a \<in> A ; f \<in> bij(length(l),length(l)) \<rbrakk> \<Longrightarrow> 
  perm_list(sum_id(length(l),f), Cons(a, l)) = Cons(a,perm_list(f,l))"  
  apply(rule nth_equalityI)
  apply(rule perm_list_tc,simp+)
  apply(erule natE,simp)
  apply(unfold perm_list_def)
  apply(subst nth_tab,simp+)
  apply(rule comp_fun,rule sum_id_tc,simp,erule bij_is_fun)
  apply(subst length.simps(2)[symmetric],rule nth_i_type,simp+)
  apply(subst comp_fun_apply) 
  apply(rule sum_id_tc,simp,erule bij_is_fun,simp)
  apply(subst sum_id0,subst nth_eq,simp+)
  apply(subst nth_tab,simp+)
  apply(rule comp_fun,rule sum_id_tc,simp,erule bij_is_fun)
  apply(subst length.simps(2)[symmetric],rule nth_i_type,simp+)
  apply(rule ltD,simp)
  apply(subst comp_fun_apply,rule sum_id_tc,simp,erule bij_is_fun)
  apply(rule ltD,simp)
  apply(subst nth_eq,simp+)
  apply(rule apply_type,rule sum_id_tc,simp,rule bij_is_fun,simp,rule ltD,simp)
  apply(subst sum_idS,rule ltD,simp,subst nth_Cons)
  apply(rule in_n_in_nat,rule length_type,simp,rule apply_type,rule bij_is_fun,simp,erule ltD)
  apply(subst nth_tab,simp+)  
  apply(rule comp_fun,erule bij_is_fun)
  apply(rule nth_i_type,simp+,rule ltD,simp)
  apply(subst comp_fun_apply,erule bij_is_fun,rule ltD,simp)
  apply(subst nth_eq,simp+,rule apply_type,erule bij_is_fun,rule ltD,simp+)
done
    
lemma nth_perm_conv [simp] : "\<lbrakk> l \<in> list(A) ; f \<in> bij(length(l),length(l)) ; n \<in> length(l) \<rbrakk> \<Longrightarrow>
  nth(converse(f)`n,perm_list(f,l)) = nth(n,l)"
  by (unfold perm_list_def,subst nth_tab_perm,simp+)

lemma nth_perm [simp] : "\<lbrakk> l \<in> list(A) ; f \<in> bij(length(l),length(l)) ; n \<in> length(l) \<rbrakk> \<Longrightarrow>
  nth(n,perm_list(f,l)) = nth(f`n,l)"
  apply (unfold perm_list_def,subst nth_tab,rule in_n_in_nat,(erule length_type,simp)+)
  apply(erule length_type,rule comp_fun,erule bij_is_fun,simp+)
  apply(subst comp_fun_apply,erule bij_is_fun,simp,erule nth_eq,rule apply_type,erule bij_is_fun,simp)
done

section\<open>Renaming of formulas\<close>
consts   rename :: "i=>i"
primrec
  "rename(Member(x,y)) =
      (\<lambda> n \<in> nat . \<lambda>f \<in> bij(n,n). Member (f`x, f`y))"

  "rename(Equal(x,y)) =
      (\<lambda> n \<in> nat . \<lambda>f \<in> bij(n,n). Equal (f`x, f`y))"

  "rename(Nand(p,q)) =
      (\<lambda> n \<in> nat . \<lambda>f \<in> bij(n,n). Nand (rename(p)`n`f, rename(q)`n`f))"

  "rename(Forall(p)) =
      (\<lambda> n \<in> nat . \<lambda>f \<in> bij(n,n). Forall (rename(p) `succ(n)` sum_id(n,f)))"


lemma ren_mem [simp] : "\<lbrakk> i \<in> nat ; j\<in>nat ; n \<in> nat ; f \<in> bij(n,n)\<rbrakk> \<Longrightarrow> 
  rename(Member(i,j))`n`f = Member(f`i,f`j)"
  by (auto)

lemma ren_eq [simp] : "\<lbrakk> i \<in> nat ; j\<in>nat ; n \<in> nat ; f \<in> bij(n,n)\<rbrakk> \<Longrightarrow> 
  rename(Equal(i,j))`n`f = Equal(f`i,f`j)"
  by (auto)

lemma ren_nand [simp] : "\<lbrakk> p \<in> formula ; q\<in>formula ; n \<in> nat ; f \<in> bij(n,n)\<rbrakk> \<Longrightarrow> 
  rename(Nand(p,q))`n`f = Nand(rename(p)`n`f,rename(q)`n`f)"
  by (auto)

lemma ren_forall [simp] : "\<lbrakk> p \<in> formula ; n \<in> nat ; f \<in> bij(n,n)\<rbrakk> \<Longrightarrow> 
  rename(Forall(p))`n`f = Forall(rename(p)`succ(n)`sum_id(n,f))"
  by (auto)
    
lemma ren_tc : "p \<in> formula \<Longrightarrow> 
      (\<forall> n f . n \<in> nat \<longrightarrow>f \<in> bij(n,n) \<longrightarrow> arity(p) \<le> n \<longrightarrow> rename(p)`n`f \<in> formula)"
  apply (induct_tac p,simp_all)
  apply (clarsimp,subgoal_tac "f`x \<in> nat \<and> f`y \<in> nat",blast,rule conjI)
  apply(rule_tac m="n" in in_n_in_nat,assumption,erule app_bij)
  apply(rule succ_in,rule_tac j="succ(y)"  in un_leD1,simp+)
  apply(rule_tac m="n"  in in_n_in_nat,assumption) 
  apply(erule app_bij, rule succ_in,rule_tac i="succ(x)" in un_leD2,simp+)
  apply (clarsimp,subgoal_tac "f`x \<in> nat \<and> f`y \<in> nat",blast,rule conjI)
  apply(rule_tac m="n" in in_n_in_nat,assumption)
  apply(erule app_bij, rule succ_in,rule_tac j="succ(y)" in un_leD1,simp+)
  apply(rule_tac m="n"  in in_n_in_nat,assumption) 
  apply(erule app_bij, rule succ_in,rule_tac i="succ(x)" in un_leD2,simp+)    
  apply(auto,subgoal_tac "arity(p)\<le>n",simp)
    apply(rule Un_least_lt_iff[THEN iffD1[THEN conjunct1]])
      apply(rule nat_into_Ord,erule arity_type)
     apply(rule_tac n="arity(q)" in nat_into_Ord,erule arity_type,simp)
  apply(subgoal_tac "arity(q)\<le>n",simp)
   apply(rule Un_least_lt_iff[THEN iffD1[THEN conjunct2]])
   apply((rule nat_into_Ord,erule arity_type)+,simp)
  apply(rename_tac m g)
  apply(erule_tac x="succ(m)" in allE,rule impE,assumption,simp)
  apply (clarsimp)
  apply(rule_tac x="sum_id(m,g)"  in allE,assumption,rule impE)
  apply (assumption,simp,erule_tac P="arity(p) \<le> succ(m)" in impE)
  apply (auto,rule pred_le2,simp+)
done

lemma ren_tc2 [TC] : "p \<in> formula \<Longrightarrow> n \<in> nat \<Longrightarrow> f \<in> bij(n,n) \<Longrightarrow> arity(p) \<le> n \<Longrightarrow> rename(p)`n`f \<in> formula"
  by (insert ren_tc,auto)
  
lemma Nand_equiv : "\<lbrakk> env \<in> list(M) ; env' \<in> list(M) ; 
  p \<in> formula;q \<in> formula ; p' \<in> formula ; q' \<in> formula ;
  sats(M,p,env) \<longleftrightarrow> sats(M,p',env') ;
sats(M,q,env) \<longleftrightarrow> sats(M,q',env') \<rbrakk> \<Longrightarrow>
sats(M,Nand(p,q),env) \<longleftrightarrow> sats(M,Nand(p',q'),env')" 
  by(auto)

lemma Forall_equiv : "\<lbrakk> env \<in> list(M) ; env' \<in> list(M) ; 
  p \<in> formula; p' \<in> formula ; \<And> a . a  \<in> M  \<longrightarrow>
  (sats(M,p,Cons(a,env)) \<longleftrightarrow> sats(M,p',Cons(a,env')))  \<rbrakk> \<Longrightarrow>
sats(M,Forall(p),env) \<longleftrightarrow> sats(M,Forall(p'),env')" 
  by(simp)


lemma arity_meml : "l \<in> nat \<Longrightarrow> Member(x,y) \<in> formula \<Longrightarrow> arity(Member(x,y)) \<le> l \<Longrightarrow> x \<in> l"
  by(simp,rule subsetD,rule le_imp_subset,assumption,simp)  
lemma arity_memr : "l \<in> nat \<Longrightarrow> Member(x,y) \<in> formula \<Longrightarrow> arity(Member(x,y)) \<le> l \<Longrightarrow> y \<in> l"
  by(simp,rule subsetD,rule le_imp_subset,assumption,simp)  
lemma arity_eql : "l \<in> nat \<Longrightarrow> Equal(x,y) \<in> formula \<Longrightarrow> arity(Equal(x,y)) \<le> l \<Longrightarrow> x \<in> l"
  by(simp,rule subsetD,rule le_imp_subset,assumption,simp)  
lemma arity_eqr : "l \<in> nat \<Longrightarrow> Equal(x,y) \<in> formula \<Longrightarrow> arity(Equal(x,y)) \<le> l \<Longrightarrow> y \<in> l"
  by(simp,rule subsetD,rule le_imp_subset,assumption,simp)  
lemmas mem_sat_ch = mem_iff_sats [THEN iffD2]        
lemmas mem_sat_chr = mem_iff_sats [THEN iffD1]        

lemma mem_iff_sats2:
  "env\<in>list(A) \<Longrightarrow> sats(A, Member(i,j), env) \<Longrightarrow> nth(i,env) \<in> nth(j,env)"
by (insert satisfies.simps(1),simp)

lemma renSat : "p \<in> formula \<Longrightarrow> (\<forall> env . env \<in> list(M) \<longrightarrow>
         (\<forall> f . f \<in> bij(length(env),length(env)) \<longrightarrow>
        arity(p) \<le> length(env) \<longrightarrow>
         sats(M,p,env) \<longleftrightarrow> 
         sats(M,rename(p)`length(env)`converse(f),perm_list(f,env))))"
   apply (induct_tac p,(rule allI,(rule impI)+)+)
   apply (subst ren_mem,assumption+,erule length_type)
   apply(erule bij_converse_bij,rule iffI)
   apply(rule iffD1,rule_tac x="nth(x,env)" and y="nth(y,env)" in mem_iff_sats)
   apply(rule nth_perm_conv,assumption+,rule arity_meml,erule length_type,simp,assumption)
   apply(rule nth_perm_conv,assumption+,rule arity_memr,erule length_type,simp,assumption)
   apply(simp+)
   apply(rule mem_iff_sats[THEN iffD2]) 
   apply(rule nth_perm_conv,assumption+,rule_tac y="y" in arity_meml,erule length_type,simp+)
   apply(rule nth_perm_conv,assumption+,rule_tac x="x" in arity_memr,erule length_type,simp,simp,simp,simp)
   apply (rule allI,(rule impI)+)+ 
   apply (subst ren_eq,assumption+,erule length_type)
   apply(erule bij_converse_bij,rule iffI)
   apply(rule iffD1,rule_tac x="nth(x,env)" and y="nth(y,env)" in equal_iff_sats)
   apply(rule nth_perm_conv,assumption+,rule arity_eql,erule length_type,simp,assumption)
   apply(rule nth_perm_conv,assumption+,rule arity_eqr,erule length_type,simp,assumption)
   apply(erule perm_list_tc,assumption,simp)
   apply(rule iffD1,rule_tac i="x" and j="y" and x="nth(x,env)" and y="nth(y,env)" in equal_iff_sats,simp+)
   apply(rule equal_iff_sats[THEN iffD2]) 
   apply(rule nth_perm_conv,assumption+,rule_tac y="y" in arity_meml,erule length_type,simp+)
   apply(rule nth_perm_conv,assumption+,rule_tac x="x" in arity_memr,erule length_type,simp,simp,simp,simp)
   apply (rule allI,(rule impI)+)+
   apply (subst ren_nand,assumption+,simp)
   apply(erule bij_converse_bij)
   apply(subgoal_tac "arity(q) \<le> length(env)")
   prefer 2      
      apply(simp,rule_tac j="arity(Nand(p,q))" in le_trans,simp,rule Un_upper2_le,
           (rule nat_into_Ord,rule arity_type,assumption)+,simp)
    apply(subgoal_tac "arity(p) \<le> length(env)")
    prefer 2
      apply(simp,rule_tac j="arity(Nand(p,q))" in le_trans,simp,rule Un_upper1_le,
           (rule nat_into_Ord,rule arity_type,assumption)+,simp)
     apply(rule Nand_equiv,simp,simp,simp,simp,simp,simp,simp,simp)
    apply (rule allI,(rule impI)+)+
  apply(subst ren_forall,assumption,erule length_type,erule bij_converse_bij )
 apply(rule Forall_equiv,simp+)
  apply(rule ren_tc2,simp+)
  apply(rule_tac j="succ(pred(arity(p)))" in le_trans,rule succpred_leI,simp+)
  apply(rule impI)
  apply(subgoal_tac "Cons(a,perm_list(f,env)) = perm_list(sum_id(length(env),f),Cons(a,env))",simp)
  apply(erule_tac x="Cons(a,env)" in allE)
  apply(subgoal_tac "Cons(a,env) \<in> list(M)")
  apply(subgoal_tac "sum_id(length(env),f) \<in> bij(length(Cons(a,env)),length(Cons(a,env)))")
  apply(erule impE,assumption,erule_tac x="sum_id(length(env),f)" in allE)
  apply(erule impE,assumption)
    apply(erule impE)
  apply(rule_tac j="succ(pred(arity(p)))" in le_trans)
   apply (rule succpred_leI,erule arity_type,simp,simp+)
    prefer 3 apply(simp)
   prefer 2 apply(simp)
   apply(subst conv_perm,erule length_type,simp,rule iff_refl)
  apply(subst perm_list_eq,simp+)
done

lemma sat_env_eq : "p \<in> formula \<Longrightarrow> env \<in> list(M) \<Longrightarrow> env'\<in> list(M) \<Longrightarrow>
   env=env' \<Longrightarrow>         sats(M,p,env) \<longleftrightarrow> sats(M,p,env')"
  by(auto)
    

    
definition ext_fun :: "[i,i,i] \<Rightarrow> i" where
    "ext_fun(f,k,m) == \<lambda> n \<in> m . if n <k then f`n else n"

      
lemma ext_fun_bij : "k \<in> nat \<Longrightarrow> f\<in>bij(k,k) \<Longrightarrow> m \<in> nat \<Longrightarrow> k<m \<Longrightarrow> 
  ext_fun(f,k,m) \<in> bij(m,m)"
  apply(unfold ext_fun_def)
  apply(rule_tac  d="\<lambda> n. if n < k then converse(f)`n else n" in lam_bijective)
   apply(case_tac "x<k",simp,rule ltD,rule_tac j="k" in lt_trans,rule ltI)
   apply(rule apply_type,rule bij_is_fun,simp+,erule ltD,simp+)
   apply(case_tac "y<k",simp,rule ltD,rule_tac j="k" in lt_trans,rule ltI)
   apply(rule apply_type,rule bij_is_fun,simp+,erule ltD,simp+,auto)
   apply(erule left_inverse_bij,erule ltD)
   apply(subgoal_tac "f`x < k",simp,rule ltI,rule apply_type)
   apply(erule bij_is_fun,erule ltD,simp)
   apply(erule right_inverse_bij,erule ltD)
  apply(subgoal_tac "converse(f)`y < k",simp,rule ltI,rule app_bij)
  apply(erule bij_converse_bij,erule ltD,simp)
done

lemma ext_fun_bije [TC] : "k\<in>nat \<Longrightarrow> f\<in>bij(k,k) \<Longrightarrow> m \<in> nat \<Longrightarrow> k\<le>m \<Longrightarrow> ext_fun(f,k,m) \<in> bij(m,m)"
  apply(erule leE,rule ext_fun_bij,simp+)
  apply(unfold ext_fun_def)
  apply(rule_tac d="\<lambda> n . converse(f)`n" in lam_bijective,auto)
  apply(erule left_inverse_bij,erule ltD)
  apply(drule_tac i="x" in ltI,simp+)
  apply(erule right_inverse_bij,simp)
  apply(subgoal_tac "converse(f)`y < m",rule notE,assumption+)
  apply(rule ltI,rule app_bij,simp+)
done

lemma ext_fun_lek: "m \<in> nat \<Longrightarrow> f \<in> k \<rightarrow> k \<Longrightarrow> n \<in> k \<Longrightarrow> k\<le>m \<Longrightarrow> ext_fun(f,k,m)`n=f`n"
  apply(unfold ext_fun_def,subst beta,rule ltD,drule ltI[of "n" "k"],simp,erule lt_trans2,assumption)
  apply(auto,drule ltI[of "n" "k"],simp,auto)
done
    
lemma ext_fun_lek1: "m \<in> nat \<Longrightarrow> invol(k,f) \<Longrightarrow> n \<in> k \<Longrightarrow> k\<le>m \<Longrightarrow> ext_fun(f,k,m)`n=j \<Longrightarrow> f`j=n"
  apply(rule inj_apply_equality,rule bij_is_inj,rule ext_fun_bije[of "k"],simp,erule invol_bij,assumption+)
  apply(subst (asm) ext_fun_lek,assumption+,rule bij_is_fun[OF invol_bij],simp+)
  apply(subst ext_fun_lek,assumption+,rule bij_is_fun[OF invol_bij],simp+)
  apply(rule apply_type,rule  bij_is_fun[OF invol_bij],simp)
  apply(subst sym[of "f`n" "j"],simp)
  apply(rule apply_type,rule  bij_is_fun[OF invol_bij],simp+)
  apply(subst ext_fun_lek,assumption+,rule bij_is_fun[OF invol_bij],simp+)
  apply(subst invol_inverse,simp)  
  apply(subst sym[of "f`n" "j"],simp)
  apply(rule apply_type,rule  bij_is_fun[OF invol_bij],simp+)
  apply(subst (asm) ext_fun_lek,assumption+,rule bij_is_fun[OF invol_bij],simp+)
  apply(rule ltD,rule lt_trans2,rule ltI)
  apply(rule apply_type,rule  bij_is_fun[OF invol_bij],simp)
  apply(subst sym[of "f`n" "j"],simp)
  apply(rule apply_type,rule  bij_is_fun[OF invol_bij],simp+)
  apply(rule ltD,rule lt_trans2,erule ltI,simp+)
  done
    
(* Cómo demostramos que converse(f) = g 

Probamos converse(f)`n = y \<Longrightarrow> g`y=n

*)
    
  
  
lemma ext_fun_gek: "m \<in> nat \<Longrightarrow> f \<in> k \<rightarrow> k \<Longrightarrow>  k \<le>n \<Longrightarrow> n\<in>m \<Longrightarrow> ext_fun(f,k,m)`n=n"
  by(unfold ext_fun_def,subst beta,simp,auto,drule le_imp_not_lt,auto)

lemma conv_ext_ltk : "m \<in> nat \<Longrightarrow> invol(k,f) \<Longrightarrow> n \<in> k \<Longrightarrow> k \<le> m \<Longrightarrow>
    (converse(ext_fun(f,k,m))`n = ext_fun(f,k,m)`n)"  
  apply(rule function_apply_equality,rule converseI)
  apply(subst ext_fun_lek,simp)
  apply(erule invol_fun,simp+)
  apply(rule funcI,rule bij_is_fun[OF ext_fun_bije],simp+,erule invol_bij,simp+) 
  apply(rule ltD,rule lt_trans2,rule ltI,rule apply_type)
  apply(erule invol_fun,simp+,subst ext_fun_lek,simp+,erule invol_fun) 
  apply(rule apply_type,erule invol_fun,simp+)
  apply(rule bij_is_function,rule bij_converse_bij,rule ext_fun_bije,auto)
  apply(erule invol_bij)
done
lemma conv_ext_gek : "m \<in> nat \<Longrightarrow> invol(k,f) \<Longrightarrow> k \<le> n \<Longrightarrow> n \<in> m \<Longrightarrow>
    (converse(ext_fun(f,k,m))`n = ext_fun(f,k,m)`n)"  
  apply(rule function_apply_equality,rule converseI)
   apply(rule funcI,rule bij_is_fun[OF ext_fun_bije],rule in_n_in_nat,assumption)
   apply(rule ltD,erule lt_trans1,rule ltI,simp+)
  apply(erule invol_bij,simp) 
   apply(rule lt_trans1,simp,drule ltI[of "n"],simp,erule leI) 
    apply(rule apply_type,rule bij_is_fun,rule ext_fun_bije)
    apply(rule in_n_in_nat,assumption)
   apply(rule ltD,erule lt_trans1,rule ltI,simp+)
  apply(erule invol_bij,simp) 
   apply(rule lt_trans1,simp,drule ltI[of "n"],simp,erule leI,simp) 
  apply(subst ext_fun_gek,auto)
  apply(erule invol_fun)
  apply(subst ext_fun_gek,auto,erule invol_fun)
  apply(subst ext_fun_gek,auto,erule invol_fun)
  apply(subst ext_fun_gek,auto,erule invol_fun)
    apply(rule bij_is_function,rule bij_converse_bij,rule ext_fun_bije,auto)
  apply(rule in_n_in_nat,assumption)
   apply(rule ltD,erule lt_trans1,rule ltI,simp+,erule invol_bij)
 apply(rule lt_trans1,simp,drule ltI[of "n"],simp,erule leI)
done
    
    
lemma conv_ext_ap : "m\<in>nat \<Longrightarrow> invol(k,f) \<Longrightarrow> k\<le> m \<Longrightarrow> n \<in> m \<Longrightarrow>
  converse(ext_fun(f,k,m))`n = ext_fun(f,k,m)`n"
  apply(case_tac "n<k")
  apply(subst conv_ext_ltk,auto,erule ltD)
  apply(subgoal_tac "k\<le>n")
  apply(rule conv_ext_gek,auto)  
  apply(rule_tac not_le_iff_lt[THEN iffD1],auto,rule nat_into_Ord,rule in_n_in_nat,auto)
done

lemma conv_ext : "m\<in>nat \<Longrightarrow> invol(k,f) \<Longrightarrow> k\<le> m \<Longrightarrow> 
  converse(ext_fun(f,k,m)) = ext_fun(f,k,m)"
  apply(rule fun_extension,rule bij_is_fun)
    apply(rule bij_converse_bij,rule ext_fun_bije,auto)
    apply(erule invol_bij,rule bij_is_fun,rule ext_fun_bije,auto)
   apply(erule invol_bij,erule conv_ext_ap,auto)
done

lemma inv_ext : "m\<in>nat \<Longrightarrow> invol(k,f) \<Longrightarrow> k\<le> m \<Longrightarrow>
                   invol(m,ext_fun(f,k,m))"
  apply(unfold invol_def,rule conjI)
   apply(fold invol_def,rule ext_fun_bije,auto,erule invol_bij)  
  apply(rule sym,rule conv_ext,auto)
done
    
definition 
  swap01 :: "i" where
  "swap01 == \<lambda> n \<in> 2 . if n=0 then 1 else 0"

lemma swap01_bij [TC] : "swap01 \<in> bij(2,2)"
  by(unfold swap01_def,rule_tac  d="\<lambda> n. if n =0 then 1 else 0" in lam_bijective,auto)
lemma swap_0 [simp]: "swap01`0 = 1"
    by(unfold swap01_def,simp,auto)
lemma swap_1 [simp]: "swap01`1 = 0"
    by(unfold swap01_def,simp)
lemma swap_auto [simp] : "x < 2 \<Longrightarrow> converse(swap01)`x = (swap01`x)" 
  apply(rule function_apply_equality,rule converseI)    
  apply(case_tac "x\<le>0",simp+,rule funcI,rule bij_is_fun,simp)
  apply(blast,simp,simp,rule leE[of "x" "1"],simp,auto)
  apply(rule funcI,rule bij_is_fun,simp+,blast,simp)
done
   
lemma swap_conv : "converse(swap01) = swap01"
  apply(rule fun_extension,rule bij_is_fun)
  apply(rule bij_converse_bij,simp,rule bij_is_fun,simp,drule ltI,auto)
    done
lemma swap_invol : "invol(2,swap01)" 
 by (unfold invol_def,rule conjI,simp,rule sym, rule swap_conv)

lemma conv_swap_ext : "m\<in>nat \<Longrightarrow> 2\<le> m \<Longrightarrow> 
 converse(ext_fun(swap01,2,m)) = ext_fun(swap01,2,m)"  
  by(rule conv_ext,simp,rule swap_invol,simp)
    
lemma eswap0 [simp] : "m \<in> nat \<Longrightarrow> 2 \<le> m \<Longrightarrow> ext_fun(swap01,2,m)`0 = 1"
  by(subst ext_fun_lek,auto,rule bij_is_fun,simp)

lemma eswap1 [simp] : "m \<in> nat \<Longrightarrow> 2 \<le> m \<Longrightarrow> ext_fun(swap01,2,m)`1 = 0"
  by(subst ext_fun_lek,auto,rule bij_is_fun,simp)

lemma eswapn [simp] : "m \<in> nat \<Longrightarrow> 2 \<le> n \<Longrightarrow> n \<in> m \<Longrightarrow> ext_fun(swap01,2,m)`n = n"
  by(subst ext_fun_gek,auto,rule bij_is_fun,simp)

    
lemma swap_env : "l \<in> list(M) \<Longrightarrow> a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> 
  perm_list(ext_fun(swap01,2,succ(succ(length(l)))),Cons(a,(Cons(b,l)))) =
  Cons(b,Cons(a,l))"
  apply(subgoal_tac 
  "ext_fun(swap01,2, succ(succ(length(l)))) \<in> bij(length(Cons(a, Cons(b, l))), length(Cons(a, Cons(b, l))))")
prefer 2 apply(simp,rule_tac m="succ(succ(length(l)))" in ext_fun_bije,simp+)
  apply(rule nth_equalityI,rule perm_list_tc,simp+)
  apply(case_tac "i=0",simp)
  apply(case_tac "i=1",simp+) 
  apply(subst nth_perm,simp+,rule ltD,simp+)
  apply(subgoal_tac "\<exists> j . i = succ(succ(j))")
  apply(erule exE)
  apply(subst nth_perm,simp+,rule ltD,simp+)
  apply(subst eswapn,simp+,rule ltD,simp+)
  apply(rule_tac x="pred(pred(i))" in exI)
  apply(subst succ_pred_eq,erule pred_type)
  prefer 2 apply(subst succ_pred_eq,simp+,auto)
  apply(drule pred0E,simp,auto)
done

(*        
sats(M,p,env) \<longleftrightarrow> sats(M,rename(p)`length(env)`converse(f),perm_list(f,env))))"
*)
lemma ren_sat : "p \<in> formula \<Longrightarrow> env \<in> list(M) \<Longrightarrow> f \<in> bij(length(env),length(env)) \<Longrightarrow>
        arity(p) \<le> length(env) \<Longrightarrow>
        sats(M,p,env) \<longleftrightarrow> 
        sats(M,rename(p)`length(env)`converse(f),perm_list(f,env))"
 by(insert renSat,simp)
  
lemma sats_swap_0_1 :
  "\<lbrakk> \<phi> \<in> formula ; env \<in> list(M) ; a \<in> M ; b \<in> M ; arity(\<phi>) \<le> succ(succ(length(env))) \<rbrakk> \<Longrightarrow>
  sats(M,\<phi>,Cons(b,Cons(a,env))) \<longleftrightarrow>
  sats(M,rename(\<phi>)`succ(succ(length(env)))`ext_fun(swap01,2,succ(succ(length(env)))),Cons(a,Cons(b,env)))"
  apply(subst swap_env[symmetric,of "env" "M" "b" "a"],simp+)
  apply(rule iff_trans)
  apply(rule_tac f="ext_fun(swap01,2,succ(succ(length(env))))" in ren_sat,simp+)
  apply(rule ext_fun_bije,simp+)
  apply(subst conv_swap_ext,simp+)
done

lemmas simpmiguel =  leD_cases   succ_pred_eq   invol_inverse  sum_id0 sum_idS conv_sum_id   
	tab_length   tab_length2   nth_eq   perm_list_length  nth_tab_perm 
	perm_list_eq   nth_perm_conv   nth_perm   ren_mem   ren_eq   ren_nand   
	ren_forall   swap_0  swap_1 swap_auto  eswap0  eswap1  eswapn 
lemmas TCmiguel =  zero_in  in_succ_in_nat  le_in_nat bij_is_function Un_least_lt_iffn 
       		   app_bij sum_id_bd sum_id_ap sum_id_tc sum_id_bij tab_tc nth_i_type 
		   nth_after_type perm_list_tc ren_tc2 ext_fun_bije swap01_bij 
end 