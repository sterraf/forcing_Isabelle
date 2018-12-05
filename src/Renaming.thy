theory Renaming 
  imports 
    Nat_Miscelanea 
    "~~/src/ZF/Constructible/Formula"
begin

section\<open>Auxiliary results\<close>

lemma funcI : "f \<in> A \<rightarrow> B \<Longrightarrow> a \<in> A \<Longrightarrow> b= f ` a \<Longrightarrow> \<langle>a, b\<rangle> \<in> f"
  by(simp,rule apply_Pair,simp+)

lemma bij_is_function  : "f\<in>bij(A,B) \<Longrightarrow> function(f)"
  by(drule bij_is_fun,simp add: Pi_iff)

lemma app_bij : "f \<in> bij(A,B) \<Longrightarrow> a \<in> A \<Longrightarrow> f`a \<in> B"
  by (frule  bij_is_fun,simp)

lemma bij_app_n : "n\<in>nat \<Longrightarrow> f\<in>bij(n,n) \<Longrightarrow> x \<in> nat \<Longrightarrow> f`x \<in> nat"  
  apply(case_tac "x\<in>n",rule_tac m="n" in in_n_in_nat,(simp add:app_bij)+)
  apply(subst apply_0,drule bij_is_fun,subst  domain_of_fun,assumption+,auto)
done
    
section\<open>Involutions\<close>

definition invol :: "[i,i] \<Rightarrow> o" where
  "invol(A,f) == f\<in>bij(A,A) \<and> f = converse(f)"
  
lemma invol_bij : "invol(A,f) \<Longrightarrow> f\<in>bij(A,A)" by (simp add: invol_def)
lemma invol_conv : "invol(A,f) \<Longrightarrow> f=converse(f)" by (simp add: invol_def)
lemmas invol_conv_bij =  bij_converse_bij[OF invol_bij]
lemmas invol_fun = bij_is_fun[OF invol_bij]
lemmas invol_conv_fun = bij_is_fun[OF invol_conv_bij]
  
lemma invol_inverse : "invol(A,f) \<Longrightarrow> a \<in> A \<Longrightarrow> f`(f`a) = a"  
  by(simp add: invol_def,clarsimp,subst sym[of "converse(f)"],
      simp,rule right_inverse_bij,simp+)
  
section\<open>Renaming of free variables\<close>

definition 
  sum_id :: "[i,i] \<Rightarrow> i" where
  "sum_id(m,f) == \<lambda>n \<in> succ(m)  . if n=0 then 0 else succ(f`pred(n))"
    
lemma sum_id0 : "sum_id(m,f)`0 = 0"
  by(unfold sum_id_def,simp)

lemma sum_idS : "succ(x) \<in> succ(m) \<Longrightarrow> sum_id(m,f)`succ(x) = succ(f`x)"
  by(unfold sum_id_def,simp)
    
lemma sum_id_bd  : "m \<in> nat \<Longrightarrow> n\<in> nat \<Longrightarrow> 
      f \<in> m \<rightarrow> m \<Longrightarrow> n \<in> succ(m) \<Longrightarrow> (if n = 0 then 0 else succ(f`pred(n))) \<in> succ(m)"
  apply (simp,rule conjI,simp add: zero_in)
  apply (rule impI, rule nat_succI,assumption) 
  apply (rule_tac A="m" in subsetD,simp)
  apply (erule_tac A="m" in apply_type)
  apply (rule Ord_succ_mem_iff [THEN iffD1],simp,subst succ_pred_eq,assumption+)
done

lemma sum_id_ap : "m \<in> nat \<Longrightarrow> f \<in> m \<rightarrow> m \<Longrightarrow> 
    n \<in> succ(m) \<Longrightarrow> sum_id(m,f)`n \<in> succ(m)"
  by (unfold sum_id_def, subst beta,assumption,rule sum_id_bd,simp add: in_succ_in_nat,
   erule in_succ_in_nat,simp+)
    
lemma sum_id_tc : 
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

lemma sum_id_bij  : "m \<in> nat \<Longrightarrow> f \<in> bij(m,m) \<Longrightarrow> sum_id(m,f)\<in>bij(succ(m),succ(m))"  
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

lemma conv_sum_id : "m \<in> nat \<Longrightarrow> f \<in> bij(m,m) \<Longrightarrow> converse(sum_id(m,f))`0 = 0"
  by(subst (1) sum_id0[symmetric],subst left_inverse_bij,erule sum_id_bij,auto simp add: zero_in)
    
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
  apply(rule bij_is_function,rule  bij_converse_bij, rule sum_id_bij,simp+)
done

lemma conv_perm_ap : "m \<in> nat \<Longrightarrow> f \<in> bij(m,m) \<Longrightarrow> n \<in> succ(m) \<Longrightarrow>
    (converse(sum_id(m, f))`n) = sum_id(m, converse(f))`n"  
  apply(rule_tac n="n" in natE,rule_tac m="succ(m)" in in_n_in_nat,(simp add:sum_id0 conv_sum_id)+)
  apply(subst conv_perm_s,simp+)
done
    
lemma conv_perm : "m \<in> nat \<Longrightarrow> f \<in> bij(m,m) \<Longrightarrow> 
    converse(sum_id(m, f)) = sum_id(m, converse(f))"
  apply(rule fun_extension,rule bij_is_fun,rule bij_converse_bij,rule sum_id_bij,simp+)
  apply(rule bij_is_fun,rule sum_id_bij,simp,erule bij_converse_bij,simp add:conv_perm_ap)
done

lemma sum_id_invol : "m \<in> nat \<Longrightarrow> invol(m,f) \<Longrightarrow> 
  invol(succ(m),sum_id(m,f))"  
  apply(unfold invol_def,rule conjI)
   apply(fold invol_def,rule sum_id_bij,auto,erule invol_bij)
  apply(subst conv_perm,simp+,erule invol_bij)
  apply(subst invol_conv,simp+)
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

lemma tab_tc  : "\<lbrakk> j \<in> nat ;  f \<in> j \<rightarrow> A \<rbrakk> \<Longrightarrow> 
                       tabulate(f,j) \<in> list(A)"
 by (rule tab_tc_aux,assumption,auto)


lemma tab_length  : "\<lbrakk> j \<in> nat \<rbrakk> \<Longrightarrow> \<forall> n . n \<in> nat \<longrightarrow> j \<le> n \<longrightarrow> (\<forall> f . (f \<in> n \<rightarrow> A) \<longrightarrow> 
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

lemma tab_length2 : "\<lbrakk> n \<in> nat ; f \<in> n \<rightarrow> A ; j < n \<rbrakk> \<Longrightarrow> 
                       length(tabulate(f,j)) = j"
  by(subgoal_tac "j\<le>n",subgoal_tac "j \<in> nat",insert tab_length,simp,erule in_n_in_nat,erule ltD,erule leI)


definition nth_i :: "i \<Rightarrow> i" where
  "nth_i(l) == \<lambda> n\<in>length(l).nth(n,l)"

lemma nth_eq  : "l \<in> list(A) \<Longrightarrow> n \<in> length(l) \<Longrightarrow> nth_i(l)`n=nth(n,l)"
  by(unfold nth_i_def,simp)
    
lemma nth_i_type : "l \<in> list(A) \<Longrightarrow> nth_i(l) \<in> length(l) \<rightarrow> A"
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
  apply(simp add:tab_length2,blast)
  apply(subst tab_succ,assumption+,simp,subst nth_append) 
  apply(rule_tac i="x" and m="n" and A="A" in tab_tc_aux,assumption,erule leI,assumption+)
  apply(erule le_in_nat,simp add:tab_length2)
  apply(simp add:tab_length2,rule conjI)
  prefer 2 apply(rule impI,erule_tac m="x" and n="j" in trich_nat,assumption+)
  apply(subgoal_tac "x\<le>n",blast,erule leI)
  done

lemma nth_tab: 
  "m \<in> nat \<Longrightarrow> f \<in> m \<rightarrow> A \<Longrightarrow> j \<in> m \<Longrightarrow> nth(j,tabulate(f,m)) = f`j" 
 by(subgoal_tac "j<m",insert nth_tab_gen,auto simp add:tab_length2,erule ltI,erule nat_into_Ord)
 
lemma nth_after_type : 
  "l\<in>list(A) \<Longrightarrow> f \<in> length(l) \<rightarrow> length(l) \<Longrightarrow>
   j < length(l) \<Longrightarrow> nth(f`j,l) \<in> A" 
  apply(subgoal_tac "f`j < length(l)")
  apply(erule nth_type,assumption)
  apply(rule ltI,erule apply_type,erule ltE,simp+)
done


lemma perm_list_tc  : " l \<in> list(A) \<Longrightarrow> 
    f\<in> bij(length(l),length(l)) \<Longrightarrow> 
    perm_list(f,l) \<in> list(A)"
  apply(unfold perm_list_def,rule tab_tc,rule length_type,simp add:nth_i_type)
  apply(rule comp_fun,erule bij_is_fun,simp add:nth_i_type)
done

lemma perm_list_length : " l \<in> list(A) \<Longrightarrow> 
    f\<in> bij(length(l),length(l)) \<Longrightarrow> 
    length(perm_list(f,l)) = length(l)"
  apply(unfold perm_list_def,subst tab_length,simp add:nth_i_type,rule length_type,simp+)
  apply(rule comp_fun,erule bij_is_fun,rule nth_i_type,simp+)
done
    
lemma nth_tab_perm : "\<lbrakk> m \<in> nat ; h \<in> m \<rightarrow> A ; f \<in> bij(m,m) ; n \<in> m \<rbrakk> \<Longrightarrow>
  nth(converse(f)`n,tabulate(h O f,m)) = h`n"
  apply(subst nth_tab,simp,rule comp_fun,erule bij_is_fun,simp)
 apply(rule apply_type,rule bij_is_fun[OF bij_converse_bij],assumption+)
 apply(subst comp_fun_apply,erule bij_is_fun)
 apply(rule apply_type,rule bij_is_fun[OF bij_converse_bij],assumption+)
 apply(subst right_inverse_bij,simp+)
done

lemma perm_list_eq  : "\<lbrakk> l \<in> list(A) ; a \<in> A ; f \<in> bij(length(l),length(l)) \<rbrakk> \<Longrightarrow> 
  perm_list(sum_id(length(l),f), Cons(a, l)) = Cons(a,perm_list(f,l))"  
  apply(rule nth_equalityI)
  apply((rule perm_list_tc,(simp add:sum_id_bij)+)+,simp add: sum_id_bij perm_list_length)
  apply(erule natE)
  apply(unfold  perm_list_def)
   apply(subst nth_tab,simp)
   apply(fold perm_list_def,simp+)
  apply(rule comp_fun,rule sum_id_tc,simp,erule bij_is_fun)
  apply(subst length.simps(2)[symmetric],rule nth_i_type,simp+,rule zero_in,simp+)
  apply(subst comp_fun_apply,rule sum_id_tc,simp+,erule bij_is_fun,rule zero_in,simp) 
  apply(subst sum_id0,subst nth_eq,simp+,rule zero_in,simp+)
  apply(unfold  perm_list_def)
   apply(subst nth_tab,simp)
   apply(fold perm_list_def,simp)
  apply(rule comp_fun,rule sum_id_tc,simp,erule bij_is_fun)
    apply(subst length.simps(2)[symmetric],rule nth_i_type,simp+)
   apply(drule ltD,subst (asm) perm_list_length[of "Cons(a,l)"],(simp add:sum_id_bij)+)
   apply(subst comp_fun_apply,rule sum_id_tc,simp,rule bij_is_fun,simp)
   apply(drule ltD,subst (asm) perm_list_length[of "Cons(a,l)"],(simp add:sum_id_bij)+)
  apply(subst nth_eq,simp+,rule app_bij,rule sum_id_bij,simp+)
   apply(drule ltD,subst (asm) perm_list_length[of "Cons(a,l)"],(simp add:sum_id_bij)+)
   apply(subst sum_idS)
   apply(drule ltD,subst (asm) perm_list_length[of "Cons(a,l)"],(simp add:sum_id_bij)+)
  apply(subst nth_Cons)
   apply(rule_tac m="length(l)" in in_n_in_nat,simp,rule app_bij,simp)
   apply(subst (asm) perm_list_length[of "Cons(a,l)"],(simp add:sum_id_bij)+,rule ltD,simp)
  apply(unfold perm_list_def,subst nth_tab,simp+)
  apply(fold perm_list_def)
  apply(rule comp_fun,erule bij_is_fun,rule nth_i_type,simp)
   apply(subst (asm) perm_list_length[of "Cons(a,l)"],(simp add:sum_id_bij)+,rule ltD,simp)  
   apply(subst comp_fun_apply,erule bij_is_fun)
   apply(subst (asm) perm_list_length[of "Cons(a,l)"],(simp add:sum_id_bij)+,rule ltD,simp)  
  apply(subst nth_eq,simp,frule app_bij)
   apply(subst (asm) perm_list_length[of "Cons(a,l)"],(simp add:sum_id_bij)+,rule ltD,simp+)  
done
    
lemma nth_perm_conv : "\<lbrakk> l \<in> list(A) ; f \<in> bij(length(l),length(l)) ; n \<in> length(l) \<rbrakk> \<Longrightarrow>
  nth(converse(f)`n,perm_list(f,l)) = nth(n,l)"
  by (unfold perm_list_def,subst nth_tab_perm,simp,erule nth_i_type,(simp add:nth_eq)+)

lemma nth_perm : "\<lbrakk> l \<in> list(A) ; f \<in> bij(length(l),length(l)) ; n \<in> length(l) \<rbrakk> \<Longrightarrow>
  nth(n,perm_list(f,l)) = nth(f`n,l)"
  apply (unfold perm_list_def,subst nth_tab,simp,rule comp_fun,erule bij_is_fun)
  apply(erule nth_i_type,simp)
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

lemma ren_mem  : "\<lbrakk> i \<in> nat ; j\<in>nat ; n \<in> nat ; f \<in> bij(n,n)\<rbrakk> \<Longrightarrow> 
  rename(Member(i,j))`n`f = Member(f`i,f`j)"
  by (auto)

lemma ren_eq  : "\<lbrakk> i \<in> nat ; j\<in>nat ; n \<in> nat ; f \<in> bij(n,n)\<rbrakk> \<Longrightarrow> 
  rename(Equal(i,j))`n`f = Equal(f`i,f`j)"
  by (auto)

lemma ren_nand  : "\<lbrakk> p \<in> formula ; q\<in>formula ; n \<in> nat ; f \<in> bij(n,n)\<rbrakk> \<Longrightarrow> 
  rename(Nand(p,q))`n`f = Nand(rename(p)`n`f,rename(q)`n`f)"
  by (auto)

lemma ren_forall  : "\<lbrakk> p \<in> formula ; n \<in> nat ; f \<in> bij(n,n)\<rbrakk> \<Longrightarrow> 
  rename(Forall(p))`n`f = Forall(rename(p)`succ(n)`sum_id(n,f))"
  by (auto)
lemma arity_meml : "l \<in> nat \<Longrightarrow> Member(x,y) \<in> formula \<Longrightarrow> arity(Member(x,y)) \<le> l \<Longrightarrow> x \<in> l"
  by(simp,rule subsetD,rule le_imp_subset,assumption,simp)  
lemma arity_memr : "l \<in> nat \<Longrightarrow> Member(x,y) \<in> formula \<Longrightarrow> arity(Member(x,y)) \<le> l \<Longrightarrow> y \<in> l"
  by(simp,rule subsetD,rule le_imp_subset,assumption,simp)  
lemma arity_eql : "l \<in> nat \<Longrightarrow> Equal(x,y) \<in> formula \<Longrightarrow> arity(Equal(x,y)) \<le> l \<Longrightarrow> x \<in> l"
  by(simp,rule subsetD,rule le_imp_subset,assumption,simp)  
lemma arity_eqr : "l \<in> nat \<Longrightarrow> Equal(x,y) \<in> formula \<Longrightarrow> arity(Equal(x,y)) \<le> l \<Longrightarrow> y \<in> l"
  by(simp,rule subsetD,rule le_imp_subset,assumption,simp)     
lemma  nand_ar1 : "p \<in> formula \<Longrightarrow> q\<in>formula \<Longrightarrow>arity(p) \<le> arity(Nand(p,q))"
  by (simp,rule Un_upper1_le,simp+)  
lemma nand_ar2 : "p \<in> formula \<Longrightarrow> q\<in>formula \<Longrightarrow>arity(q) \<le> arity(Nand(p,q))"
  by (simp,rule Un_upper2_le,simp+)  
 
(* Do we need this? *)   
lemma ren_tc :    
  fixes "p"
  assumes "p \<in> formula" 
  shows "(\<And> n f . n \<in> nat \<Longrightarrow> f \<in> bij(n,n) \<Longrightarrow> arity(p) \<le> n \<Longrightarrow> rename(p)`n`f \<in> formula)"
 using assms proof (induct set:formula)
  case (Member x y) 
  then have 1: "f`x \<in> n"  "f`y \<in> n" 
    by (simp add:  arity_meml  app_bij,simp add: arity_memr app_bij) 
  then have 2:"f`x \<in> nat" "f`y \<in> nat" using Member and 1
    by(rule_tac m="n" in in_n_in_nat,simp,simp,rule_tac m="n" in in_n_in_nat,simp,simp)
  then show ?case using Member and 2 by simp
 next
   case (Equal x y)
  then have  "f`x \<in> n"  "f`y \<in> n" 
    by (simp add:  arity_meml  app_bij,simp add: arity_memr app_bij) 
  then have "f`x \<in> nat" "f`y \<in> nat" using Equal 
    by(rule_tac m="n" in in_n_in_nat,simp,simp,rule_tac m="n" in in_n_in_nat,simp,simp)
   then show ?case using Equal by simp
 next
   case (Nand p q)
  then have "arity(p)\<le>arity(Nand(p,q))" "arity(q)\<le>arity(Nand(p,q))"
    by (subst  nand_ar1,simp,simp,simp,subst nand_ar2,simp+)
  then have "arity(p)\<le>n" "arity(q)\<le>n" using Nand
    by (rule_tac j="arity(Nand(p,q))" in le_trans,simp,simp)+
   then show ?case using Nand by (auto)
 next
   case (Forall p)
     then have "arity(p) \<in> nat" "pred(arity(p)) \<le> n" by (simp+)
     then have 2: "arity(p) \<le> succ(n)" using Forall 
       by (rule_tac n="arity(p)" in pred_le2,simp+)
     then have "rename(p)`succ(n)`sum_id(n,f) \<in> formula" using Forall
       by(simp add:sum_id_bij)
     then show ?case using 2 and Forall by(simp)
 qed

lemma ren_lib_tc : "p \<in> formula \<Longrightarrow> 
  (\<And> n f . n \<in> nat \<Longrightarrow>  f \<in> bij(n,n) \<Longrightarrow>  rename(p)`n`f \<in> formula)"
  by (induct set:formula,auto simp add: bij_app_n sum_id_bij)


lemma ren_arity :
  fixes "p"
  assumes "p \<in> formula" 
  shows "\<And> n f . n \<in> nat \<Longrightarrow> f \<in> bij(n,n) \<Longrightarrow> arity(p) \<le> n \<Longrightarrow> arity(rename(p)`n`f)\<le>n"  
using assms 
  proof (induct set:formula)
  case (Member x y) 
  then have"f`x \<in> n"  "f`y \<in> n" 
    by (simp add:  arity_meml  app_bij,simp add: arity_memr app_bij) 
  then show ?case using Member by (simp add: un_leI' ltI)  
next
  case (Equal x y)
  then have "f`x \<in> n" "f`y \<in> n" 
    by (simp add: arity_eql app_bij,simp add: arity_eqr app_bij) 
  then show ?case using Equal by (simp add: un_leI' ltI)
next
  case (Nand p q) 
  then have "arity(p)\<le>arity(Nand(p,q))" 
            "arity(q)\<le>arity(Nand(p,q))"
    by (subst  nand_ar1,simp,simp,simp,subst nand_ar2,simp+)
  then have "arity(p)\<le>n" 
        and "arity(q)\<le>n" using Nand
    by (rule_tac j="arity(Nand(p,q))" in le_trans,simp,simp)+
  then have "arity(rename(p)`n`f) \<le> n" 
        and "arity(rename(q)`n`f) \<le> n" using Nand by (simp+)
  then show ?case using Nand by (simp add:un_leI')
next
  case (Forall p)
    from Forall have 2: "sum_id(n,f) \<in> bij(succ(n),succ(n))" by (simp add:sum_id_bij)
    from Forall have 3:"arity(p) \<le> succ(n)" by (rule_tac n="arity(p)" in natE,simp+)
    then have "arity(rename(p)`succ(n)`sum_id(n,f))\<le>succ(n)" using 2 and Forall 
        by (simp)
    then show ?case using Forall and 2 and 3 by(simp add: pred_le arity_type ren_tc)
qed
  
lemma ren_tc0 : "p \<in> formula \<Longrightarrow> n \<in> nat \<Longrightarrow> f \<in> bij(n,n) \<Longrightarrow> 
          arity(p) = 0 \<Longrightarrow> rename(p)`n`f \<in> formula"
  by (insert ren_tc,auto)


lemma nand_eq : "p = q \<Longrightarrow> r = s \<Longrightarrow> Nand(p,r) = Nand(q,s)"    
  by simp

lemma forall_arityE : "p \<in> formula \<Longrightarrow> m \<in> nat \<Longrightarrow> arity(Forall(p)) \<le> m \<Longrightarrow> arity(p) \<le> succ(m)"
  by(rule_tac n="arity(p)" in natE,erule arity_type,simp+)

lemma forall_ar : "arity(Forall(p)) = pred(arity(p))"
  by simp
    
lemma coincidence :
  fixes "p"
  assumes pf : "p \<in> formula"
  shows  gf :"(\<And> m n f g . m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> f \<in> bij(m,m) \<Longrightarrow> g \<in> bij(n,n) \<Longrightarrow>
    arity(p) \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> (\<And> x . x \<in> arity(p) \<Longrightarrow> f`x=g`x) \<Longrightarrow>
    rename(p)`m`f = rename(p)`n`g)" 
  using pf 
  proof(induct p)
  case (Member x y)
  then show ?case by simp
next
  case (Equal x y)
  then show ?case by simp
next
  case (Nand p q)
  then have 1: "arity(p)\<le>m" "arity(q)\<le>m" 
    by(rule_tac j="arity(Nand(p,q))" in le_trans,erule_tac q="q" in nand_ar1,blast,blast,
          rule_tac j="arity(Nand(p,q))" in le_trans,erule_tac p="p" in nand_ar2,blast+)       
  then have "\<And> x .  x \<in> arity(p) \<Longrightarrow> f`x=g`x"  "\<And> x .  x \<in> arity(q) \<Longrightarrow> f`x=g`x" 
    using Nand by (simp+)      
  then have "rename(p)`m`f = rename(p)`n`g" "rename(q)`m`f = rename(q)`n`g" using 1 and Nand
    by (blast+)
  then show ?case using Nand by (simp)      
next  
  case (Forall q)
  have Pq : "(\<And> i j h k . i \<in> nat \<Longrightarrow> j \<in> nat \<Longrightarrow> h \<in> bij(i,i) \<Longrightarrow> k \<in> bij(j,j) \<Longrightarrow>
    arity(q) \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> (\<And> x . x \<in> arity(q) \<Longrightarrow> h`x=k`x) \<Longrightarrow>
    rename(q)`i`h = rename(q)`j`k)" using Forall
    by (blast)
  have 1:"succ(m)\<in> nat" "succ(n)\<in> nat" "arity(q) \<le> succ(m)" "succ(m) \<le> succ(n)" 
    using Forall
    by (simp,simp,erule_tac p="q" and m="m" in forall_arityE,blast+)
  have 2:"\<And> x . x \<in> arity(q) \<Longrightarrow> sum_id(m,f)`x = sum_id(n,g)`x" using 1 and Forall 
      and sum_id0 
    apply(rule_tac n="x" in natE,rule_tac m="arity(q)" in in_n_in_nat)
    apply(rule arity_type,blast,blast)
    apply(fastforce)
    apply(simp,subst (1 2) sum_idS)
    apply(rule_tac A="succ(m)" in subsetD,rule le_imp_subset,erule succ_mono)
    apply(rule_tac A="arity(q)" in subsetD,rule le_imp_subset,rule pred_le2)
    apply(simp,simp,simp,simp)
    apply(rule_tac A="arity(q)" in subsetD,rule le_imp_subset,rule pred_le2)
    apply(simp,simp,simp,simp)
    apply(simp+,subgoal_tac "xa \<in> pred(arity(q))",simp)
    apply(rule nat_succD,simp,subst succ_pred_eq,simp+,rule succpred_n0,simp+)
  done
  then have              
            "sum_id(m,f)\<in>bij(succ(m),succ(m))"
            "sum_id(n,g)\<in>bij(succ(n),succ(n))"      
    using 1 and Forall 
    by(simp add:sum_id_bij,simp add:sum_id_bij)
  then have "rename(q)`succ(m)`sum_id(m,f) = rename(q)`succ(n)`sum_id(n,g)"
    using 1 and 2 
      by(simp add:Pq[of "succ(m)" "succ(n)" "sum_id(m,f)"])
    then show ?case using  1 and 2 and Pq and Forall
      by(subst (1 2) ren_forall,fastforce+)
qed
    
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

lemmas mem_sat_ch = mem_iff_sats [THEN iffD2]   
lemmas mem_sat_chr = mem_iff_sats [THEN iffD1]        

lemma mem_iff_sats2:
  "env\<in>list(A) \<Longrightarrow> sats(A, Member(i,j), env) \<Longrightarrow> nth(i,env) \<in> nth(j,env)"
by (insert satisfies.simps(1),simp)

lemma renSat : 
  fixes "p"
  assumes pf : "p \<in> formula"
  shows  " (\<And> env . env \<in> list(M) \<Longrightarrow>
         (\<And> f . f \<in> bij(length(env),length(env)) \<Longrightarrow>
        arity(p) \<le> length(env) \<Longrightarrow>
         sats(M,p,env) \<longleftrightarrow> 
         sats(M,rename(p)`length(env)`converse(f),perm_list(f,env))))"
  using pf 
  proof(induct p)
    case (Member x y)
    then have "x \<in> length(env)" "y \<in> length(env)" 
      by(simp add : arity_meml,simp add:arity_memr)
    then have "nth(x,env) \<in> nth(y,env) \<longleftrightarrow> nth(converse(f)`x,perm_list(f,env)) \<in> nth(converse(f)`y,perm_list(f,env))"
      using Member
      by((subst nth_perm_conv,simp,simp,simp)+,simp)
    then show ?case using Member 
      apply(subst ren_mem,simp,simp,simp)
      apply(erule bij_converse_bij)
      apply(simp,rule mem_iff_sats,(simp add:nth_perm perm_list_tc)+)
    done
    next
    case (Equal x y)
    then have "x \<in> length(env)" "y \<in> length(env)" 
      by(simp add : arity_meml,simp add:arity_memr)
    then have "nth(x,env) = nth(y,env) \<longleftrightarrow> nth(converse(f)`x,perm_list(f,env)) = nth(converse(f)`y,perm_list(f,env))"
      using Equal
      by((subst nth_perm_conv,simp,simp,simp)+,simp)
    then show ?case using Equal 
      apply(subst ren_eq,simp,simp,simp)
      apply(erule bij_converse_bij)
      apply(simp,rule equal_iff_sats,(simp add:nth_perm perm_list_tc)+)
    done
  next
    case (Nand p q)
    then have 1: "arity(p) \<le> length(env)" "arity(q)\<le>length(env)" using nand_ar1 nand_ar2
      by(rule_tac j="arity(Nand(p,q))" in le_trans,simp,simp)+
    then have "sats(M,p,env) \<longleftrightarrow> sats(M,rename(p)`length(env)`converse(f),perm_list(f,env))" 
              "sats(M,q,env) \<longleftrightarrow> sats(M,rename(q)`length(env)`converse(f),perm_list(f,env))"
      using Nand
      by (simp+)
    then show ?case using Nand and 1
       apply(subst ren_nand,simp,simp,simp)
       apply(erule bij_converse_bij)
      apply(rule Nand_equiv,(simp add:perm_list_tc ren_tc)+)
    done
    next
      case (Forall p)
      then have 1: "sum_id(length(env),f) \<in> bij(succ(length(env)),succ(length(env)))"
        by(simp add:sum_id_bij)
      then have 2: "arity(p) \<le> succ(length(env))" using Forall
        apply(rule_tac j="succ(pred(arity(p)))" in le_trans)
         apply(rule succpred_leI,simp+)
       done
      then have 3:"\<And> a . a\<in> M \<Longrightarrow>
         sats(M, p, Cons(a, env)) \<longleftrightarrow>
         sats(M, rename(p) ` succ(length(env)) ` converse(sum_id(length(env), f)), perm_list(sum_id(length(env),f), Cons(a,env)))"
        using Forall and 1 
          by(simp)
      then show ?case using Forall
        apply(subst ren_forall,simp,simp)
        apply(erule bij_converse_bij)
        apply(rule Forall_equiv,(simp add:perm_list_tc)+,rule ren_lib_tc,(simp add:sum_id_bij)+)
        apply(simp add: perm_list_eq conv_perm) 
      done
  qed
    
lemma ren_Sat_eq : "p \<in> formula \<Longrightarrow>  env \<in> list(M) \<Longrightarrow>
         f \<in> bij(arity(p),arity(p)) \<Longrightarrow>
        arity(p) = length(env) \<Longrightarrow>
         sats(M,p,env) \<longleftrightarrow> 
         sats(M,rename(p)`arity(p)`converse(f),perm_list(f,env))"
 by(insert renSat,auto)

lemma ren_Sat_leq : "p \<in> formula \<Longrightarrow>  env \<in> list(M) \<Longrightarrow>
         f \<in> bij(length(env),length(env)) \<Longrightarrow>
         arity(p) \<le> length(env) \<Longrightarrow>
         sats(M,p,env) \<longleftrightarrow> 
         sats(M,rename(p)`length(env)`converse(f),perm_list(f,env))"
 by(insert renSat,auto)
   
   
lemma sat_env_eq : "p \<in> formula \<Longrightarrow> env \<in> list(M) \<Longrightarrow> env'\<in> list(M) \<Longrightarrow>
   env=env' \<Longrightarrow>         sats(M,p,env) \<longleftrightarrow> sats(M,p,env')"
  by(auto)
    

    
definition ext_fun :: "[i,i,i] \<Rightarrow> i" where
    "ext_fun(f,k,m) == \<lambda> n \<in> m . if m = 1 then 0 else if n <k then f`n else n"

lemma ext_fun_bij1 : "ext_fun(f,k,1) \<in> bij(1,1)"
  by(unfold ext_fun_def,rule_tac  d="\<lambda> n. 0" in lam_bijective,simp+,auto)

lemma ext_fun1 : "ext_fun(f,k,1)`n = 0"
   by(simp add:ext_fun_def)
      
lemma ext_fun_bij : "k \<in> nat \<Longrightarrow> f\<in>bij(k,k) \<Longrightarrow> m \<in> nat \<Longrightarrow> k<m \<Longrightarrow> 
  ext_fun(f,k,m) \<in> bij(m,m)"
  apply(unfold ext_fun_def)
  apply(rule_tac  d="\<lambda> n. if m = 1 then 0 else if n < k then converse(f)`n else n" in lam_bijective,simp)
    apply(clarsimp)
   apply(rule ltD,rule_tac j="k" in lt_trans,rule ltI)
   apply(rule apply_type,rule bij_is_fun,simp+,erule ltD,simp+)
   apply(clarsimp,rule ltD,rule_tac j="k" in lt_trans,rule ltI)
   apply(rule apply_type,rule bij_is_fun,simp+,erule ltD,simp+,auto)
   apply(erule left_inverse_bij,erule ltD)
   apply(subgoal_tac "f`x < k",simp,rule ltI,rule apply_type)
   apply(erule bij_is_fun,erule ltD,simp)
   apply(erule right_inverse_bij,erule ltD)
  apply(subgoal_tac "converse(f)`y < k",simp,rule ltI,rule app_bij)
  apply(erule bij_converse_bij,erule ltD,simp)
done

lemma ext_fun_bije : "k\<in>nat \<Longrightarrow> f\<in>bij(k,k) \<Longrightarrow> m \<in> nat \<Longrightarrow> k\<le>m \<Longrightarrow> ext_fun(f,k,m) \<in> bij(m,m)"
  apply(erule leE,rule ext_fun_bij,simp+)
  apply(unfold ext_fun_def)
  apply(rule_tac d="\<lambda> n . if m = 1 then 0 else converse(f)`n" in lam_bijective,clarsimp,rule app_bij,simp+)
  apply(clarsimp,rule app_bij,erule bij_converse_bij,auto)
  apply(erule left_inverse_bij,erule ltD)
  apply(drule_tac i="x" in ltI,simp+)
  apply(erule right_inverse_bij,simp)
  apply(subgoal_tac "converse(f)`y < m",rule notE,assumption+)
  apply(rule ltI,rule app_bij,simp+)
done  

lemma ext_fun_bij0 : "ext_fun(f,k,0) \<in> bij(0,0)"
  apply(unfold ext_fun_def)
  apply(rule_tac  d="\<lambda> n. if n < k then converse(f)`n else n" in lam_bijective)
  apply(auto)
done
    
lemma ext_fun_lek: "m \<in> nat \<Longrightarrow> f \<in> k \<rightarrow> k \<Longrightarrow> n \<in> k \<Longrightarrow> m\<noteq>1 \<Longrightarrow> k\<le>m \<Longrightarrow> ext_fun(f,k,m)`n=f`n"
  apply(unfold ext_fun_def,subst beta,rule ltD,drule ltI[of "n" "k"],rule nat_into_Ord)
  apply(erule_tac i="k" and j="m" in leE,erule in_n_in_nat,erule ltD,simp,rule lt_trans2,simp+)
  apply(auto,drule ltI[of "n" "k"],rule nat_into_Ord)
  apply(erule_tac i="k" and j="m" in leE,erule in_n_in_nat,erule ltD,simp,auto)
  done    
 
lemma ext_fun_gek: "m \<in> nat \<Longrightarrow> f \<in> k \<rightarrow> k \<Longrightarrow>  k \<le>n \<Longrightarrow> n\<in>m \<Longrightarrow> ext_fun(f,k,m)`n=n"
  by(unfold ext_fun_def,subst beta,simp,auto,drule le_imp_not_lt,auto)

lemma conv_ext_1 : "n \<in> 1 \<Longrightarrow>
    (converse(ext_fun(f,k,1))`n = ext_fun(f,k,1)`n)"  
  apply(rule function_apply_equality,rule converseI,simp add:ext_fun_def)
  apply(rule_tac A="1" and B="1" in funcI,auto,rule Pi_type,auto)
  apply(rule fun_is_function,rule bij_is_fun,rule bij_converse_bij,rule ext_fun_bij1)
  done
    
lemma conv_ext_ltk : "m \<in> nat \<Longrightarrow> invol(k,f) \<Longrightarrow> n \<in> k \<Longrightarrow> m\<noteq>1 \<Longrightarrow> k \<le> m \<Longrightarrow>
    (converse(ext_fun(f,k,m))`n = ext_fun(f,k,m)`n)"  
  apply(rule function_apply_equality,rule converseI)
  apply(subst ext_fun_lek,simp)
  apply(erule invol_fun,simp+)
  apply(rule funcI,rule bij_is_fun[OF ext_fun_bije],simp add: le_in_nat,erule invol_bij,simp+) 
  apply(rule ltD,rule lt_trans2,rule ltI,rule apply_type)
  apply(erule invol_fun,simp,rule nat_into_Ord,erule le_in_nat,simp+,subst ext_fun_lek,simp) 
  apply(rule invol_fun,simp+,rule apply_type,erule invol_fun,simp+,simp add: invol_inverse)
  apply(rule bij_is_function,rule bij_converse_bij,rule ext_fun_bije,auto)
  apply(simp add:le_in_nat,erule invol_bij)
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
  apply(case_tac "m=1",simp,rule conv_ext_1,simp)
  apply(case_tac "n<k")
  apply(subst conv_ext_ltk,auto,erule ltD)
  apply(subgoal_tac "k\<le>n")
  apply(rule conv_ext_gek,auto)  
  apply(rule_tac not_le_iff_lt[THEN iffD1],auto,(rule nat_into_Ord,rule in_n_in_nat,rule le_in_nat,auto+))
  apply(rule nat_into_Ord,erule le_in_nat,simp)
done

lemma conv_ext : "m\<in>nat \<Longrightarrow> invol(k,f) \<Longrightarrow> k\<le> m \<Longrightarrow> 
  converse(ext_fun(f,k,m)) = ext_fun(f,k,m)"
  apply(rule fun_extension,rule bij_is_fun)
    apply(rule bij_converse_bij,rule ext_fun_bije,auto simp add:le_in_nat)
    apply(erule invol_bij,rule bij_is_fun,rule ext_fun_bije,auto simp add:le_in_nat invol_bij)
   apply(simp add: conv_ext_ap)
done

lemma inv_ext : "m\<in>nat \<Longrightarrow> invol(k,f) \<Longrightarrow> k\<le> m \<Longrightarrow>
                   invol(m,ext_fun(f,k,m))"
  apply(unfold invol_def,rule conjI)
   apply(fold invol_def,rule ext_fun_bije,simp add:le_in_nat,erule invol_bij,simp+) 
  apply(rule sym,rule conv_ext,auto)
done
    
definition 
  swap01 :: "i" where
  "swap01 == \<lambda> n \<in> 2 . if n=0 then 1 else 0"
    
lemma swap_0 : "swap01`0 = 1"
    by(unfold swap01_def,simp,auto)
lemma swap_1 : "swap01`1 = 0"
  by(unfold swap01_def,simp)

lemma swap01_bij : "swap01 \<in> bij(2,2)"
  by(unfold swap01_def,rule_tac  d="\<lambda> n. if n =0 then 1 else 0" in lam_bijective,auto)
    
    
lemma swap_auto  : "x < 2 \<Longrightarrow> converse(swap01)`x = (swap01`x)" 
  apply(rule function_apply_equality,rule converseI,insert swap01_bij)    
   apply(case_tac "x\<le>0",rule funcI,rule bij_is_fun,simp,rule app_bij,simp+,auto)
    apply(simp add:swap_0 swap_1)
  apply(rule leE[of "x" "1"],simp,auto)
  apply(rule funcI,rule bij_is_fun,(simp add:swap_1)+,auto,(simp add:swap_0 swap_1))
  apply(insert swap01_bij,simp add: bij_is_function bij_converse_bij)+
done
   
lemma swap_conv : "converse(swap01) = swap01"
  apply(rule fun_extension,rule bij_is_fun,insert swap01_bij)
  apply(rule bij_converse_bij,simp,rule bij_is_fun,simp,drule ltI,auto simp add:pred0E swap_auto)
 done

lemma swap_invol : "invol(2,swap01)" 
 by (unfold invol_def,rule conjI,rule swap01_bij,rule sym, rule swap_conv)

lemma conv_swap_ext : "m\<in>nat \<Longrightarrow> 2\<le> m \<Longrightarrow> 
 converse(ext_fun(swap01,2,m)) = ext_fun(swap01,2,m)"  
  by(rule conv_ext,simp,rule swap_invol,simp)
    
lemma eswap0 : "m \<in> nat \<Longrightarrow> 2 \<le> m \<Longrightarrow> ext_fun(swap01,2,m)`0 = 1"
  by(insert swap01_bij,subst ext_fun_lek,(simp add:bij_is_fun)+,auto simp add:swap_0)

lemma eswap1  : "m \<in> nat \<Longrightarrow> 2 \<le> m \<Longrightarrow> ext_fun(swap01,2,m)`1 = 0"
  by(insert swap01_bij,subst ext_fun_lek,(simp add:bij_is_fun)+,auto simp add:swap_1)

lemma eswapn  : "m \<in> nat \<Longrightarrow> 2 \<le> n \<Longrightarrow> n \<in> m \<Longrightarrow> ext_fun(swap01,2,m)`n = n"
  by(insert swap01_bij,subst ext_fun_gek,auto,rule bij_is_fun,simp)

    
lemma swap_env : "l \<in> list(M) \<Longrightarrow> a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> 
  perm_list(ext_fun(swap01,2,succ(succ(length(l)))),Cons(a,(Cons(b,l)))) =
  Cons(b,Cons(a,l))"
  apply(insert swap01_bij)
  apply(subgoal_tac 
  "ext_fun(swap01,2, succ(succ(length(l)))) \<in> bij(length(Cons(a, Cons(b, l))), length(Cons(a, Cons(b, l))))")
prefer 2 apply(simp,rule_tac m="succ(succ(length(l)))" in ext_fun_bije,simp+)
  apply(rule nth_equalityI,rule perm_list_tc,(simp add:perm_list_length)+)
  apply(case_tac "i=0",simp add: eswap0,subst nth_perm,simp+,rule zero_in,simp,simp add:eswap0)
  apply(case_tac "i=1",(simp add: eswap1) +) 
  apply(subst nth_perm,(simp add:eswap1)+,rule ltD,(simp add:eswap1)+)
  apply(subgoal_tac "\<exists> j . i = succ(succ(j))")
  apply(erule exE)
  apply(subst nth_perm,simp+,rule ltD,simp+)
  apply(subst eswapn,simp+,(rule nat_succI,simp)+,erule ltD,simp)
  apply(rule_tac x="pred(pred(i))" in exI)
  apply(subst succ_pred_eq,erule pred_type)
  prefer 2 apply(subst succ_pred_eq,simp+,auto)
  apply(drule pred0E,simp,auto)
done

lemma ren_sat : "p \<in> formula \<Longrightarrow> env \<in> list(M) \<Longrightarrow> f \<in> bij(length(env),length(env)) \<Longrightarrow>
        arity(p) \<le> length(env) \<Longrightarrow>
        sats(M,p,env) \<longleftrightarrow> 
        sats(M,rename(p)`length(env)`converse(f),perm_list(f,env))"
 by(insert renSat,simp)

definition swap_0_1 :: "i \<Rightarrow> i" where
  "swap_0_1(p) = rename(p)`arity(p)`ext_fun(swap01,2,arity(p))"   

lemma arity_swap_0_1 :
  "p\<in>formula \<Longrightarrow> arity(swap_0_1(p)) \<le> arity(p)"
  apply (simp add: swap_0_1_def) 
  apply(rule ren_arity,simp+)
  apply(rule_tac n="arity(p)" in natE,simp+,rule ext_fun_bij0)
   apply(case_tac "x=0",simp,rule ext_fun_bij1)
  apply(insert swap01_bij)
  apply(subgoal_tac "1<arity(p)",rule ext_fun_bije,simp+,rule ltI_neg,simp+,erule not_sym,simp)
done

lemma arity_2 :
  "p\<in>formula \<Longrightarrow>arity(p) = 2 \<Longrightarrow> 
    arity(swap_0_1(p)) = 0 \<or> arity(swap_0_1(p)) = 1 \<or> arity(swap_0_1(p)) = 2"
  by (rule leE,rule arity_swap_0_1,simp+,erule leE,simp+) 

lemma arity_3 :
  "p\<in>formula \<Longrightarrow>arity(p) = succ(2) \<Longrightarrow> 
    arity(swap_0_1(p)) = 0 \<or> arity(swap_0_1(p)) = 1 \<or> 
  arity(swap_0_1(p)) = 2 \<or> arity(swap_0_1(p)) = succ(2)"
  by (rule leE,rule arity_swap_0_1,simp+,erule leE,erule leE,simp+) 


  
lemma swap_0_1_tc[TC] :
  "p\<in>formula \<Longrightarrow> swap_0_1(p) \<in> formula"
  apply (simp add: swap_0_1_def) 
  apply(rule ren_lib_tc,simp+)
  apply(rule_tac n="arity(p)" in natE,simp+,rule ext_fun_bij0)
  apply(case_tac "x=0",simp,rule ext_fun_bij1)
  apply(insert swap01_bij)
  apply(subgoal_tac "1<arity(p)",rule ext_fun_bije,simp+,rule ltI_neg,simp+,erule not_sym)
done
        
lemma sats_swap_0_1 :
  "\<lbrakk> \<phi> \<in> formula ; env \<in> list(M) ; a \<in> M ; b \<in> M ; 1 < arity(\<phi>) 
    ; arity(\<phi>) \<le> succ(succ(length(env))) \<rbrakk> \<Longrightarrow>  
  sats(M,\<phi>,Cons(b,Cons(a,env))) \<longleftrightarrow>
  sats(M,swap_0_1(\<phi>),Cons(a,Cons(b,env)))"
  apply(subst swap_env[symmetric,of "env" "M" "b" "a"],simp+)
  apply(unfold swap_0_1_def)
  apply(rule iff_trans)
  apply(rule_tac f="ext_fun(swap01,2,succ(succ(length(env))))" in ren_Sat_leq,simp+)
    apply(insert swap01_bij)
    apply(rule ext_fun_bije,simp+)
  apply(subst conv_swap_ext,simp+)
  apply(subst coincidence[of _  "arity(\<phi>)" "succ(succ(length(env)))"  "ext_fun(swap01,2,arity(\<phi>))"],simp+)
  apply(auto,rule ext_fun_bije,simp+)    
  apply(rule ext_fun_bije,simp+)
  apply(case_tac "x=0",simp add:eswap0)
  apply(case_tac "x=1",simp add:eswap1)
  apply(subgoal_tac "2\<le>x")
  apply(subst eswapn,simp+,rule_tac A="arity(\<phi>)" in subsetD,erule le_imp_subset,simp)
  apply(subst eswapn,simp+,subgoal_tac "arity(\<phi>) \<in> nat")   
  apply(rule gt1,simp+)
done

lemma sats_swap_0_12 :
  "\<lbrakk> \<phi> \<in> formula ; env \<in> list(M) ; a \<in> M ; b \<in> M  ; arity(\<phi>) = 2  \<rbrakk> \<Longrightarrow>
  sats(M,swap_0_1(\<phi>),Cons(b,Cons(a,env))) \<longleftrightarrow>
  sats(M,\<phi>,[a,b]@env)"
  apply(subgoal_tac "arity(\<phi>) \<le> succ(succ(length(env)))")
  apply(subgoal_tac "2 \<le> arity(\<phi>)")
  apply(insert sats_swap_0_1,simp)
  apply(simp+) 
done

lemma sats_swap_0_13 :
  "\<lbrakk> \<phi> \<in> formula ; env \<in> list(M) ; a \<in> M ; b \<in> M ; c \<in> M ; arity(\<phi>) = succ(2)  \<rbrakk> \<Longrightarrow>
  sats(M,\<phi>,Cons(b,Cons(a,Cons(c,env)))) \<longleftrightarrow>
  sats(M,swap_0_1(\<phi>),Cons(a,Cons(b,Cons(c,env))))"
  apply(subgoal_tac "arity(\<phi>) \<le> succ(succ(length(Cons(c,env))))")
  apply(subgoal_tac "2 \<le> arity(\<phi>)")
  apply(insert sats_swap_0_1,simp)
  apply(simp+) 
done

end 