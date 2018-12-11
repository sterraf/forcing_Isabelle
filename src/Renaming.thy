theory Renaming imports Nat_Miscelanea Formula begin
  
section\<open>Auxiliary results\<close>
  
lemma app_nm : "n\<in>nat \<Longrightarrow> m\<in>nat \<Longrightarrow> f\<in>n\<rightarrow>m \<Longrightarrow> x \<in> nat \<Longrightarrow> f`x \<in> nat"  
  apply(case_tac "x\<in>n",rule_tac m="m" in in_n_in_nat,(simp add:apply_type)+)
  apply(subst apply_0,subst  domain_of_fun,assumption+,auto)
  done
    
section\<open>Renaming of free variables\<close>
  
definition 
  sum_id :: "[i,i] \<Rightarrow> i" where
  "sum_id(m,f) == \<lambda>j \<in> succ(m)  . if j=0 then 0 else succ(f`pred(j))"
  
lemma sum_id0 : "sum_id(m,f)`0 = 0"
  by(unfold sum_id_def,simp)
    
lemma sum_idS : "succ(x) \<in> succ(m) \<Longrightarrow> sum_id(m,f)`succ(x) = succ(f`x)"
  by(unfold sum_id_def,simp)
    
lemma sum_id_tc : 
  "n \<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> f \<in> n \<rightarrow> m \<Longrightarrow> sum_id(n,f) \<in> succ(n) \<rightarrow> succ(m)"
  apply (rule Pi_iff [THEN iffD2],rule conjI)
   apply (unfold sum_id_def,rule function_lam)
  apply (rule conjI,auto)
  apply (erule_tac p="x" and A="succ(n)" and 
      b="\<lambda> i. if i = 0 then 0 else succ(f`pred(i))" and 
      P="x\<in>succ(n)\<times>succ(m)" in lamE)
  apply(rename_tac j,case_tac "j=0",simp,simp add:zero_in)
  apply(subgoal_tac "f`pred(j) \<in> m",simp)
   apply(rule nat_succI,assumption+)
  apply (erule_tac A="n" in apply_type)
  apply (rule Ord_succ_mem_iff [THEN iffD1],simp)
  apply (subst succ_pred_eq,rule_tac A="succ(n)" in subsetD,rule naturals_subset_nat)
     apply (simp+)
  done
    
    
section\<open>Renaming of formulas\<close>
  
consts   ren :: "i=>i"
primrec
  "ren(Member(x,y)) =
      (\<lambda> n \<in> nat . \<lambda> m \<in> nat. \<lambda>f \<in> n \<rightarrow> m. Member (f`x, f`y))"
  
  "ren(Equal(x,y)) =
      (\<lambda> n \<in> nat . \<lambda> m \<in> nat. \<lambda>f \<in> n \<rightarrow> m. Equal (f`x, f`y))"
  
  "ren(Nand(p,q)) =
      (\<lambda> n \<in> nat . \<lambda> m \<in> nat. \<lambda>f \<in> n \<rightarrow> m. Nand (ren(p)`n`m`f, ren(q)`n`m`f))"
  
  "ren(Forall(p)) =
      (\<lambda> n \<in> nat . \<lambda> m \<in> nat. \<lambda>f \<in> n \<rightarrow> m. Forall (ren(p)`succ(n)`succ(m)`sum_id(n,f)))"
  
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
    
lemma nand_ar1D : "p \<in> formula \<Longrightarrow> q\<in>formula \<Longrightarrow> arity(Nand(p,q)) \<le> n \<Longrightarrow> arity(p) \<le> n"
  by(auto simp add:  le_trans[OF Un_upper1_le[of "arity(p)" "arity(q)"]])  
lemma nand_ar2D : "p \<in> formula \<Longrightarrow> q\<in>formula \<Longrightarrow> arity(Nand(p,q)) \<le> n \<Longrightarrow> arity(q) \<le> n"
  by(auto simp add:  le_trans[OF Un_upper2_le[of "arity(p)" "arity(q)"]])  
    
    
lemma ren_tc : "p \<in> formula \<Longrightarrow> 
  (\<And> n m f . n \<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> f \<in> n\<rightarrow>m \<Longrightarrow>  ren(p)`n`m`f \<in> formula)"
  by (induct set:formula,auto simp add: app_nm sum_id_tc)
    
    
lemma ren_arity :
  fixes "p"
  assumes "p \<in> formula" 
  shows "\<And> n m f . n \<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> f \<in> n\<rightarrow>m \<Longrightarrow> arity(p) \<le> n \<Longrightarrow> arity(ren(p)`n`m`f)\<le>m"  
  using assms 
proof (induct set:formula)
  case (Member x y) 
  then have "f`x \<in> m" "f`y \<in> m"
    using Member assms by (simp add: arity_meml apply_funtype,simp add:arity_memr apply_funtype) 
  then show ?case using Member by (simp add: un_leI' ltI)  
next
  case (Equal x y)
  then have "f`x \<in> m" "f`y \<in> m" 
    using Equal assms by (simp add: arity_eql apply_funtype,simp add:arity_eqr apply_funtype)     
  then show ?case using Equal by (simp add: un_leI' ltI)
next
  case (Nand p q) 
  then have "arity(p)\<le>arity(Nand(p,q))" 
    "arity(q)\<le>arity(Nand(p,q))"
    by (subst  nand_ar1,simp,simp,simp,subst nand_ar2,simp+)
  then have "arity(p)\<le>n" 
    and "arity(q)\<le>n" using Nand
    by (rule_tac j="arity(Nand(p,q))" in le_trans,simp,simp)+
  then have "arity(ren(p)`n`m`f) \<le> m" and  "arity(ren(q)`n`m`f) \<le> m" 
    using Nand by auto
  then show ?case using Nand by (simp add:un_leI')
next
  case (Forall p)
  from Forall have "succ(n)\<in>nat"  "succ(m)\<in>nat" by auto
  from Forall have 2: "sum_id(n,f) \<in> succ(n)\<rightarrow>succ(m)" by (simp add:sum_id_tc)
  from Forall have 3:"arity(p) \<le> succ(n)" by (rule_tac n="arity(p)" in natE,simp+)
  then have "arity(ren(p)`succ(n)`succ(m)`sum_id(n,f))\<le>succ(m)" using  
      Forall \<open>succ(n)\<in>nat\<close> \<open>succ(m)\<in>nat\<close> 2 by force
  then show ?case using Forall 2 3 ren_tc arity_type pred_le by auto
qed
  
lemma forall_arityE : "p \<in> formula \<Longrightarrow> m \<in> nat \<Longrightarrow> arity(Forall(p)) \<le> m \<Longrightarrow> arity(p) \<le> succ(m)"
  by(rule_tac n="arity(p)" in natE,erule arity_type,simp+)
    
lemma B : 
  assumes "m \<in> nat" "n \<in> nat"  
    "\<rho> \<in> list(A)" "\<rho>' \<in> list(A)"
    "f \<in> n \<rightarrow> m"
    "\<And> i . i < n \<Longrightarrow> nth(i,\<rho>) = nth(f`i,\<rho>')"
    "a \<in> A" "j \<in> succ(n)"
  shows "nth(j,Cons(a,\<rho>)) = nth(sum_id(n,f)`j,Cons(a,\<rho>'))"
proof -
  let ?g="sum_id(n,f)"   
  have "succ(n) \<in> nat" using \<open>n\<in>nat\<close> by simp
  then have "j \<in> nat" using \<open>j\<in>succ(n)\<close> in_n_in_nat by blast
  then have "nth(j,Cons(a,\<rho>)) = nth(?g`j,Cons(a,\<rho>'))" 
  proof (cases rule:natE[OF \<open>j\<in>nat\<close>])
    case 1
    then show ?thesis using assms sum_id0 by simp
  next
    case (2 i)
    with \<open>j\<in>succ(n)\<close> have "succ(i)\<in>succ(n)" by simp
    with \<open>n\<in>nat\<close> have "i \<in> n" using nat_succD assms by simp
    have "f`i\<in>m" using \<open>f\<in>n\<rightarrow>m\<close> apply_type \<open>i\<in>n\<close> by simp
    then have "f`i \<in> nat" using in_n_in_nat \<open>m\<in>nat\<close> by simp
    have "nth(succ(i),Cons(a,\<rho>)) = nth(i,\<rho>)" using \<open>i\<in>nat\<close> by simp
    also have "... = nth(f`i,\<rho>')" using assms \<open>i\<in>n\<close> ltI by simp
    also have "... = nth(succ(f`i),Cons(a,\<rho>'))" using \<open>f`i\<in>nat\<close> by simp
    also have "... = nth(?g`succ(i),Cons(a,\<rho>'))" 
      using sum_idS \<open>succ(i)\<in>succ(n)\<close> cases by simp
    finally have "nth(succ(i),Cons(a,\<rho>)) = nth(?g`succ(i),Cons(a,\<rho>'))" .
    then show ?thesis using \<open>j=succ(i)\<close> by simp
  qed
  then show ?thesis .
qed
  
lemma renSat : 
  fixes "\<phi>"
  assumes "\<phi> \<in> formula"
  shows  "\<And> n m \<rho> \<rho>' f . \<lbrakk>  n \<in> nat ; m \<in> nat ; \<rho> \<in> list(M) ; \<rho>' \<in> list(M) ; f \<in> n \<rightarrow> m ;
            arity(\<phi>) \<le> n ;
            \<And> i . i < n \<Longrightarrow> nth(i,\<rho>) = nth(f`i,\<rho>') \<rbrakk> \<Longrightarrow>
         sats(M,\<phi>,\<rho>) \<longleftrightarrow> sats(M,ren(\<phi>)`n`m`f,\<rho>')"
  using \<open>\<phi> \<in> formula\<close> 
proof(induct \<phi>)
  case (Member x y)
  have 0: "ren(Member(x,y))`n`m`f = Member(f`x,f`y)" using Member assms arity_type by force
  have 1: "x \<in> n" using Member arity_meml by simp
  have "y \<in> n" using Member arity_memr by simp
  then show ?case using Member assms 1 0 ltI by simp      
next
  case (Equal x y)
  have 0: "ren(Equal(x,y))`n`m`f = Equal(f`x,f`y)" using Equal assms arity_type by force
  have 1: "x \<in> n" using Equal arity_eql by simp
  have "y \<in> n" using Equal arity_eqr by simp
  then show ?case using Equal assms 1 0 ltI by simp      
next
  case (Nand p q)
  have 0:"ren(Nand(p,q))`n`m`f = Nand(ren(p)`n`m`f,ren(q)`n`m`f)" using Nand by simp
  have "arity(p) \<le> n" using Nand nand_ar1D by simp 
  then have 1:"i \<in> arity(p) \<Longrightarrow> i \<in> n" for i using subsetD[OF le_imp_subset[OF \<open>arity(p) \<le> n\<close>]] by simp
  then have "i \<in> arity(p) \<Longrightarrow> nth(i,\<rho>) = nth(f`i,\<rho>')" for i using Nand ltI by simp
  then have 2:"sats(M,p,\<rho>) \<longleftrightarrow> sats(M,ren(p)`n`m`f,\<rho>')" using \<open>arity(p)\<le>n\<close> 1 Nand by simp
  have "arity(q) \<le> n" using Nand nand_ar2D by simp 
  then have 3:"i \<in> arity(q) \<Longrightarrow> i \<in> n" for i using subsetD[OF le_imp_subset[OF \<open>arity(q) \<le> n\<close>]] by simp
  then have "i \<in> arity(q) \<Longrightarrow> nth(i,\<rho>) = nth(f`i,\<rho>')" for i using Nand ltI by simp
  then have 4:"sats(M,q,\<rho>) \<longleftrightarrow> sats(M,ren(q)`n`m`f,\<rho>')" using assms \<open>arity(q)\<le>n\<close> 3 Nand by simp  
  then show ?case using Nand 0 2 4 by simp
next
  case (Forall p)
  have 0:"ren(Forall(p))`n`m`f = Forall(ren(p)`succ(n)`succ(m)`sum_id(n,f))" 
    using Forall by simp
  have 1:"sum_id(n,f) \<in> succ(n) \<rightarrow> succ(m)" (is "?g \<in> _") using sum_id_tc Forall by simp
  then have 2: "arity(p) \<le> succ(n)" 
    using Forall le_trans[of _ "succ(pred(arity(p)))"] succpred_leI by simp
  have "succ(n)\<in>nat" "succ(m)\<in>nat" using Forall by auto
  then have A:"\<And> j .j < succ(n) \<Longrightarrow> nth(j, Cons(a, \<rho>)) = nth(?g`j, Cons(a, \<rho>'))" if "a\<in>M" for a
    using that B Forall ltD by force
  have 4:
    "sats(M,p,Cons(a,\<rho>)) \<longleftrightarrow> sats(M,ren(p)`succ(n)`succ(m)`?g,Cons(a,\<rho>'))" if "a\<in>M" for a
  proof - 
    have C:"Cons(a,\<rho>) \<in> list(M)" "Cons(a,\<rho>')\<in>list(M)" using Forall that by auto   
    have "sats(M,p,Cons(a,\<rho>)) \<longleftrightarrow> sats(M,ren(p)`succ(n)`succ(m)`?g,Cons(a,\<rho>'))" 
      using Forall(2)[OF \<open>succ(n)\<in>nat\<close> \<open>succ(m)\<in>nat\<close> C(1) C(2) 1 2 A[OF \<open>a\<in>M\<close>]] by simp
    then show ?thesis .
  qed
  then show ?case using Forall 0 1 2 4 by simp
qed
  
  
  (* Swapping *)    
definition ext_fun :: "[i,i,i] \<Rightarrow> i" where
  "ext_fun(f,k,m) == \<lambda> n \<in> m . if m = 1 then 0 else if n <k then f`n else n"
  
lemma ext_fun_tc1 : "ext_fun(f,k,1) \<in> 1\<rightarrow>1"
  by(rule Pi_iff[THEN iffD2],auto simp add: ext_fun_def function_lam,erule lamE,auto)
    
lemma ext_fun_tc : "k \<in> nat \<Longrightarrow> f\<in>k\<rightarrow>k \<Longrightarrow> m \<in> nat \<Longrightarrow> k<m \<Longrightarrow> 
  ext_fun(f,k,m) \<in> m\<rightarrow>m"
  apply(rule Pi_iff[THEN iffD2],auto simp add: ext_fun_def function_lam,erule lamE,auto)
  apply(subgoal_tac "f`n < k",rule ltD, rule lt_trans,auto simp add:ltI)
  apply(rule ltI,rule apply_type[of _ k],auto simp add:ltD)
  done
    
    
lemma ext_fun_tce : "k\<in>nat \<Longrightarrow> f\<in>k\<rightarrow>k \<Longrightarrow> m \<in> nat \<Longrightarrow> k\<le>m \<Longrightarrow> ext_fun(f,k,m) \<in> m\<rightarrow>m"
  apply(erule leE,rule ext_fun_tc,simp+)
  apply(unfold ext_fun_def,rule Pi_iff[THEN iffD2], auto simp add: function_lam)
  apply(erule lamE,auto)
  done
    
definition 
  swap01 :: "i" where
  "swap01 == \<lambda> n \<in> 2 . if n=0 then 1 else 0"
  
lemma swap_0 : "swap01`0 = 1"
  by(unfold swap01_def,simp,auto)
lemma swap_1 : "swap01`1 = 0"
  by(unfold swap01_def,simp)
    
lemma swap01_tc : "swap01 \<in> 2\<rightarrow>2"
  by(unfold swap01_def,auto simp add:Pi_iff function_lam,erule lamE,auto)
    
lemma eswap0 : "m \<in> nat \<Longrightarrow> 2 \<le> m \<Longrightarrow> ext_fun(swap01,2,m)`0 = 1"
  by(auto simp add: ext_fun_def swap_0, rule ltD,rule lt_trans[of _ 1],auto)
    
lemma eswap1  : "m \<in> nat \<Longrightarrow> 2 \<le> m \<Longrightarrow> ext_fun(swap01,2,m)`1 = 0"
  by(auto simp add: ext_fun_def swap_1)
    
lemma eswapn  : "m \<in> nat \<Longrightarrow> 2 \<le> n \<Longrightarrow> n \<in> m \<Longrightarrow> ext_fun(swap01,2,m)`n = n"
  by(auto simp add: ext_fun_def swap01_def,rule notE,auto simp add: le_imp_not_lt)
    
lemma swap_env' : "n \<in> nat\<Longrightarrow>l \<in> list(M) \<Longrightarrow> a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> 2 \<le> n \<Longrightarrow> i < n \<Longrightarrow>
  nth(i,Cons(a,Cons(b,l))) = nth(ext_fun(swap01,2,n)`i,Cons(b,Cons(a,l)))"
  apply(subgoal_tac "i\<in>nat")
   apply(case_tac "i=0",simp add: eswap0)
   apply(case_tac "i=1",(simp add: eswap1) +) 
   apply(subgoal_tac "\<exists> j . i = succ(succ(j))",subst eswapn,auto)
    apply(erule ltD,rule_tac x="pred(pred(i))" in exI)
   apply(subst succ_pred_eq,erule pred_type)
    prefer 2 apply(subst succ_pred_eq,simp+,auto)
   apply(drule pred0E,simp_all,rule in_n_in_nat,simp,erule ltD)
  done
    
definition swap_0_1 :: "i \<Rightarrow> i" where
  "swap_0_1(p) = ren(p)`arity(p)`arity(p)`ext_fun(swap01,2,arity(p))"   
  
lemma arity_2 :
  "p\<in>formula \<Longrightarrow>arity(p) = 2 \<Longrightarrow> 
    arity(swap_0_1(p)) = 0 \<or> arity(swap_0_1(p)) = 1 \<or> arity(swap_0_1(p)) = 2"
  apply (rule leE,rule ren_arity[of p 2 2 "ext_fun(swap01,2,2)"])
        apply (auto simp add:ext_fun_tce swap01_tc swap_0_1_def,erule leE,auto) 
  done
    
lemma arity_3 :
  "p\<in>formula \<Longrightarrow>arity(p) = succ(2) \<Longrightarrow> 
    arity(swap_0_1(p)) = 0 \<or> arity(swap_0_1(p)) = 1 \<or> 
  arity(swap_0_1(p)) = 2 \<or> arity(swap_0_1(p)) = succ(2)"
  apply (rule leE,rule ren_arity[of p "succ(2)" "succ(2)" "ext_fun(swap01,2,succ(2))"],simp+)
     apply (auto simp add: ext_fun_tc swap01_tc swap_0_1_def,erule leE,auto,erule leE,auto) 
  done
    
lemma ext_fun1_tc : "ext_fun(f,k,1) \<in> 1 \<rightarrow> 1"
  by(unfold ext_fun_def,rule lam_type,auto)
    
lemma ext_fun0 : "ext_fun(f,k,0) = 0"
  by(simp add:ext_fun_def)
    
    
lemma swap_0_1_tc[TC] :
  "p\<in>formula \<Longrightarrow> swap_0_1(p) \<in> formula"
  apply (simp add: swap_0_1_def) 
  apply(rule ren_tc,simp+)
  apply(rule_tac n="arity(p)" in natE,auto simp add: ext_fun0)
  apply(case_tac "x=0",auto simp add:ext_fun1_tc)
  apply(rule ext_fun_tce,auto simp add:swap01_tc,drule nat_0_le,erule leE,auto)
  done
    
lemma sats_swap_0_12 :
  "\<lbrakk> \<phi> \<in> formula ; env \<in> list(M) ; a \<in> M ; b \<in> M  ; arity(\<phi>) = 2  \<rbrakk> \<Longrightarrow>
  sats(M,swap_0_1(\<phi>),Cons(b,Cons(a,env))) \<longleftrightarrow>
  sats(M,\<phi>,[a,b]@env)"
  apply(unfold swap_0_1_def,rule renSat[symmetric],auto simp add: ext_fun_tce swap01_tc)
  apply(rule swap_env',auto)
  done
    
lemma sats_swap_0_13 :
  "\<lbrakk> \<phi> \<in> formula ; env \<in> list(M) ; a \<in> M ; b \<in> M ; c \<in> M ; arity(\<phi>) = succ(2)  \<rbrakk> \<Longrightarrow>
  sats(M,\<phi>,Cons(b,Cons(a,Cons(c,env)))) \<longleftrightarrow>
  sats(M,swap_0_1(\<phi>),Cons(a,Cons(b,Cons(c,env))))"
  apply(unfold swap_0_1_def,rule renSat,auto,rule ext_fun_tce,auto simp add:swap01_tc)
  apply(rule swap_env',auto)
  done    
end 