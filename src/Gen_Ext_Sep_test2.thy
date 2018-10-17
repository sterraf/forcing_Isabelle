theory Gen_Ext_Sep_test2 imports Forces_locale Renaming begin

(*  [P, leq, one] @ [p, \<theta>, \<sigma>, \<pi>] @ params @ [u]) =
    [\<theta>, p, u, P, leq, one, \<sigma>, \<pi>] @ params 
<0,3>,<1,4>,<2,5>,<3,1>,<4,0>,<5,6>,<6,7>,<7#+n,2>,

*)
  
definition 
  f :: "i\<Rightarrow>i" where
  "f(n) == {<0,3>,<1,4>,<2,5>,<3,1>,<4,0>,<5,6>,<6,7>,<7#+n,2>}" 
(*\<langle>0, 3\<rangle>, \<langle>1, 4\<rangle>, \<langle>2, 5\<rangle>, \<langle>3, 1\<rangle>, \<langle>4, 0\<rangle>, \<langle>5, 6\<rangle>, \<langle>6#+n, 2\<rangle>}"*)

lemma f_range : "range(f(n)) = 8"
  by(unfold f_def,auto)
    
definition 
  fInv :: "i\<Rightarrow>i" where
  "fInv(n) == {<3,0>,<4,1>,<5,2>,<1,3>,<0,4>,<6,5>,<7,6>,<2,7#+n>}"

lemma f_ftc : "n \<in> nat \<Longrightarrow> f(n) \<in> (7 \<union> {7#+n}) -||> 8"
  by (simp add : f_def,(rule consI,auto)+,rule emptyI)
  
lemma fInv_ftc : "n \<in> nat \<Longrightarrow> fInv(n) \<in> 8 -||> (7 \<union> {7#+n})"
  by (simp add : fInv_def,(rule consI,auto)+,rule emptyI)

    
lemma dom_f : "domain(f(n)) = 7 \<union> {7#+n}"
  by(unfold f_def,auto)

lemma dom_fInv : "domain(fInv(n)) = 8"     
  by(unfold fInv_def,auto)
    
lemma f_tc: "n \<in> nat \<Longrightarrow> f(n) \<in> (7 \<union> {7#+n}) -> 8"
  by(subst dom_f[symmetric],rule FiniteFun_is_fun,erule f_ftc)  

lemma fInv_tc: "n \<in> nat \<Longrightarrow> fInv(n) \<in> 8 \<rightarrow> (7 \<union> {7#+n})"
  by(subst dom_fInv[symmetric],rule FiniteFun_is_fun,erule fInv_ftc)  
     
lemma conv_f_eq : "n \<in> nat \<Longrightarrow> fInv(n) = converse(f(n))"
  by(unfold fInv_def f_def,auto)

lemma conv_fInv_eq : "n \<in> nat \<Longrightarrow> converse(fInv(n)) = f(n)"
  by(unfold fInv_def f_def,auto)
    
lemma ble2 :  "i \<in> nat \<Longrightarrow> succ(j) \<in> i#+1 \<Longrightarrow> j \<in> i"
  by(case_tac "j \<in> nat",auto simp add:nat_succD)

lemma ble1 :  "j \<in> nat \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> i \<in> nat \<Longrightarrow> j \<in> i#+1 \<Longrightarrow> pred(j) \<in> i"
  by(rule natE[of "i"],simp+,blast,auto simp add : nat_succD succ_pred_eq)
    
definition 
  gInv :: "i \<Rightarrow> i" where
  "gInv(n) == \<lambda> j \<in> (8#+n)-8 . pred(j)"

definition 
  g :: "i \<Rightarrow> i" where
  "g(n) == \<lambda> j \<in> (7#+n)-7 . succ(j)"

    
lemma g_tc : " g(n) \<in> ((7#+n)-7) \<rightarrow> (8#+n)-8"
  apply(unfold g_def,rule lam_type)
  apply(subgoal_tac "succ(j)< 8#+n" "j\<notin>7", rule DiffI,erule ltD)
  apply(rule notI,simp add:ble2,rule notI,frule DiffD2,simp)
  apply(frule DiffD1,subst add_succ,rule succ_leI,erule ltI,simp)
done

lemma gInv_tc : " gInv(n) \<in>  (8#+n)-8 \<rightarrow> ((7#+n)-7)"
  apply(unfold gInv_def,rule lam_type)
  apply(subgoal_tac "j \<notin> 8" "j \<noteq> 0" "j \<in> nat" "8#+ n =(7#+n)#+1",rule DiffI,rule ble1,simp+) 
  apply(rule notI,subgoal_tac "j\<in>8",simp,frule ltI[of _ "7"],simp,subst succ_pred_eq[symmetric],simp+,rule nat_succI,simp+)
  apply(rule in_n_in_nat,auto)
done
  
lemma compUnEq : "B \<subseteq> A \<Longrightarrow> (A - B) \<union> B = A"
  by(auto)

lemma ble3 : "n \<in> nat \<Longrightarrow> 8#+n = ((7#+n) - 7) \<union> (7 \<union> {7#+n})"
  apply (subgoal_tac "7 \<subseteq> 7#+n", subst Un_assoc[symmetric],subst compUnEq,simp,force)  
  apply(rule le_imp_subset, rule add_le_self,simp)
done
    
lemma ble4 : "n \<in> nat \<Longrightarrow> 8#+n = ((8#+n) - 8) \<union> 8"
  by(subgoal_tac "8 \<subseteq> 8#+n",simp add:compUnEq,rule le_imp_subset, rule add_le_self,simp)
    
lemma disjI : "(\<forall> x \<in> A . x \<notin> B) \<Longrightarrow> (\<forall> x \<in> B . x \<notin> A) \<Longrightarrow> A \<inter> B \<subseteq> 0"
  by(clarsimp)

lemma ble5 : "(A - B) \<inter> (B \<union> {A}) = 0"
  by(rule equalityI,simp_all, rule disjI,auto,erule mem_irrefl,erule mem_irrefl)

lemma disjunctE : "A \<inter> B = 0 \<Longrightarrow> (\<forall> x \<in> A . x \<notin> B) \<and> (\<forall> x \<in> B . x \<notin> A)"
  by(auto)
    
lemma ble6 : "A \<inter> B = 0 \<Longrightarrow> a \<in> A \<Longrightarrow> a \<notin> B" 
  by(auto simp add: disjunctE ble5)

lemma ble7 : "A \<inter> B = 0 \<Longrightarrow> a \<in> B \<Longrightarrow> a \<notin> A" 
  by(rule ble6,subst Int_commute,simp+)
    
definition fUg :: "i \<Rightarrow> i" where
  "fUg(n) = g(n) \<union> f(n)"

definition fUgInv :: "i \<Rightarrow> i" where
  "fUgInv(n) = gInv(n) \<union> fInv(n)"

lemma fUg_tc : "n \<in> nat \<Longrightarrow> fUg(n) \<in> (8#+n) -> 8#+n"
  apply(subst (1) ble3,assumption+)
  apply(subst ble4,assumption+,unfold fUg_def)
  apply(rule fun_disjoint_Un,rule g_tc,erule f_tc,rule ble5)
done

  
lemma apply_fun: "fa \<in> Pi(A,B) ==> <a,b>: fa \<Longrightarrow> fa`a = b"
  by(auto simp add: apply_iff)
    
lemma congIn : "a \<in> A \<Longrightarrow> A = B \<Longrightarrow> a\<in> B"
  by auto

lemma notSuccIn : "x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> x \<notin> y \<Longrightarrow> succ(x) \<notin> succ(y)"
  by(auto,drule ltI[of _ "y"],simp,subgoal_tac "x\<in>y",simp,rule ltD,rule lt_trans[of _ "succ(x)"],simp+)
    
lemma g_inj : "n \<in> nat \<Longrightarrow> g(n) \<in> inj((7#+n)-7,(8#+n)-8)"
  apply(rule_tac d="\<lambda> x . gInv(n)`x" in f_imp_injective,rule g_tc)
  apply(rule ballI)
  apply(unfold gInv_def,subst beta,rule apply_type,rule g_tc,assumption)
  apply(unfold g_def,subst beta,assumption)
  apply(simp add: nat_succI)
done


lemma ble8 : "n \<in> nat \<Longrightarrow> y \<in> 8 #+ n - 8 \<Longrightarrow> Arith.pred(y) \<in> 7 #+ n - 7"
  apply(subgoal_tac "y \<noteq>0",rule DiffI,rule ble1,rule in_n_in_nat[of "8#+n"],simp+)
  prefer 2   apply(rule notI,simp,subgoal_tac "0\<in>8",simp,rule zero_in,simp)
  apply(rule notI,subgoal_tac "succ(pred(y)) \<in> 8",subst (asm) succ_pred_eq)
  apply(rule in_n_in_nat[of "8#+n"],simp+,rule nat_succI,simp+)
done
    
lemma g_surj : "n \<in> nat\<Longrightarrow> g(n) \<in> surj(7#+n-7,8#+n-8)"
  apply(rule_tac d="\<lambda> x . gInv(n)`x" in f_imp_surjective,rule g_tc)
  apply(unfold gInv_def,subst beta,simp,rule ble8,simp+)
  apply(unfold g_def,subst beta,rule ble8,simp+)
  apply(subgoal_tac "y\<noteq>0",rule succ_pred_eq,rule in_n_in_nat[of "8#+n"],simp+)
  apply(rule notI,simp,subgoal_tac "0\<in>8",simp,rule zero_in,simp)
done

lemma g_bij : "n \<in> nat\<Longrightarrow> g(n) \<in> bij(7#+n-7,8#+n-8)"
  by(unfold bij_def,rule IntI,rule g_inj,simp, rule g_surj,simp)
    
lemma g_range : "n \<in> nat \<Longrightarrow> range(g(n)) = (8#+n)-8"
  by(rule surj_range,erule g_surj)

lemma conv_g_ap : "n \<in> nat \<Longrightarrow> i \<in> 8#+n -8 \<Longrightarrow> converse(g(n))`i = gInv(n)`i"
  apply(rule left_inverse_eq,erule g_inj)
   apply(unfold gInv_def,subst beta,assumption)
  apply(unfold g_def,subst beta,rule ble8,simp+)  
  apply(subgoal_tac "i\<noteq>0",rule succ_pred_eq,rule in_n_in_nat[of "8#+n"],simp+)
  apply(rule notI,simp,subgoal_tac "0\<in>8",simp,rule zero_in,simp,subst beta,simp,rule ble8,simp+)
done

lemma conv_g_eq : "n \<in> nat \<Longrightarrow> converse(g(n)) = gInv(n)"
  apply(rule fun_extension,rule inj_converse_fun, erule g_inj)
   apply(subst g_range,simp,rule gInv_tc)
  apply(rule conv_g_ap,simp,subst (asm) g_range,simp+)
done
  
lemma fUg_inj: "n \<in> nat \<Longrightarrow> fUg(n) \<in> inj(8#+n,8#+n)"   
  apply(rule_tac d="\<lambda> x . fUgInv(n)`x" in f_imp_injective, erule fUg_tc)
  apply(clarify,drule_tac a="x" in congIn,erule ble3,rule_tac c="x" in UnE,assumption)
   apply(unfold fUg_def fUgInv_def)
   apply(subst fun_disjoint_apply1[of "x"],subst dom_f)
    prefer 2 apply(subst fun_disjoint_apply1)
    prefer 2 apply(unfold g_def,subst beta,simp,unfold gInv_def,subst beta)
      prefer 4 apply(rule ble6, rule ble5,simp)
     prefer 2 apply(rule pred_succ_eq)
    prefer 3 
       apply(subst fun_disjoint_apply2[of "x"],subst domain_lam,rule ble7,rule ble5,simp)
    apply(subst fun_disjoint_apply2,subst domain_lam)
     apply(rule notI,drule DiffD2,rule notE,assumption,rule apply_type,rule f_tc,simp+)
    apply(subst conv_f_eq,simp,rule left_inverse_lemma,erule f_tc)
  apply(subst conv_f_eq[symmetric],simp,erule fInv_tc,simp,rule DiffI,drule DiffD1)
    apply(simp add: nat_succI,rule notSuccIn,simp,rule in_n_in_nat[of "7#+n"],simp+)
    apply(subst dom_fInv,rule notSuccIn,rule in_n_in_nat[of "7#+n"],simp+)
  done

    
lemma fUg_range : "n \<in> nat \<Longrightarrow> range(fUg(n)) = 8#+n"
  apply(unfold fUg_def,subst range_Un_eq,subst ble4,simp,subst g_range,simp)
  apply(subst f_range,simp)
done
lemma fUg_surj: "n \<in> nat \<Longrightarrow> fUg(n) \<in> surj(8#+n,8#+n)" 
  by(subst (2) fUg_range[symmetric],simp,rule fun_is_surj,erule fUg_tc)
  
lemma fUg_bij: "n \<in> nat \<Longrightarrow> fUg(n) \<in> bij(8#+n,8#+n)" 
  by(unfold bij_def,rule IntI,erule fUg_inj,erule fUg_surj)
    
lemma fUg_conv_bij: "n \<in> nat \<Longrightarrow> converse(fUg(n)) \<in> bij(8#+n,8#+n)" 
  by (erule fUg_bij [THEN bij_converse_bij])

lemma conv_fUg_eq: "n \<in> nat \<Longrightarrow> converse(fUg(n)) = fUgInv(n)" 
  apply(unfold fUg_def fUgInv_def,subst converse_Un)
  apply(subst conv_f_eq,simp,subst conv_g_eq,simp+) 
done

lemma ble0 : "f1 \<in> bij(a,b) \<Longrightarrow> g1 = converse(f1) \<Longrightarrow> converse(g1) = f1"
  apply(subgoal_tac "g1 \<in> bij(b,a)",rule fun_extension)
  apply(rule bij_is_fun,rule bij_converse_bij,simp,rule bij_is_fun,simp)
   apply(rule left_inverse_eq,rule bij_is_inj,simp,simp,rule left_inverse_bij,simp+)
   apply(rule apply_type,rule bij_is_fun,simp+)
  done
    
lemma conv_fUgInv_eq: "n \<in> nat \<Longrightarrow> fUg(n) = converse(fUgInv(n))" 
  apply(subst conv_fUg_eq[symmetric],simp)
  apply(unfold fUg_def,subst converse_Un,subst converse_Un)
  apply(subst conv_f_eq[symmetric],simp,subst conv_g_eq,simp+) 
  apply(subst ble0[of "g(n)"],rule g_bij,simp,subst conv_g_eq,simp+) 
  apply(subst conv_fInv_eq,simp+) 
done

  
lemma fUgInv_bij : "n \<in> nat \<Longrightarrow> fUgInv(n) \<in>  bij(8#+n,8#+n)"
  by(subst conv_fUg_eq[symmetric],simp,erule fUg_conv_bij)
  
lemma env_len : "{p,q,r,s,t,u,v,w} \<subseteq> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> length([p, q, r, s, t, u,v] @ env @ [w]) = 8#+length(env)"
  by(simp)
lemma env_len2 : "{p,q,r,s,t,u,v,w} \<subseteq> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> length([t,s,w,p,q,r,u,v]@env) = 8#+length(env)"
  by(simp)
    
lemma in8 : "i \<in> 8 \<Longrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> i =6 \<or> i=7" 
by (auto)
lemma in7 : "i \<in> 7 \<Longrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> i=6" 
by (auto)
lemma tonto : "xf \<in> nat \<Longrightarrow> x \<in> nat \<Longrightarrow> succ(succ(succ(succ(succ(succ(succ(xf))))))) \<in> succ(succ(succ(succ(succ(succ(succ(succ(x)))))))) \<Longrightarrow> xf \<le> x"
  by(rule ltI,rule ltD,auto,rule lt_trans[of _ "succ(succ(succ(succ(succ(succ(succ(xf)))))))"],simp,rule leI,rule ltI,assumption,simp)
  
    
(*
 [P, leq, one] @ [p, \<theta>, \<sigma>, \<pi>] @ params @ [u]) 
 [\<theta>, p, u, P, leq, one, \<sigma>, \<pi>] @ params 
*)
lemma perm_sep_env: "{p,q,r,s,t,u,v,w} \<subseteq> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow>
  perm_list(fUg(length(env)),[t,s,w,p,q,r,u,v]@env) = [p,q,r,s,t,u,v]@env@[w]"
  apply(rule nth_equalityI)
  apply(rule perm_list_tc[of _ "M"],simp,(subst env_len2,assumption+)+)
  apply(rule fUg_bij,simp,simp add:app_type)
  apply(subst perm_list_length[of _ "M"],simp,(subst env_len2,assumption+)+)
  apply(rule fUg_bij,simp,simp)
  apply(subst (asm) perm_list_length[of _ "M"],simp,(subst env_len2,assumption+)+)
  apply(rule fUg_bij,simp)
   apply(subst (asm) env_len2,assumption+)
   apply(subst nth_perm[of _ "M"],simp)
  apply(subst env_len2,assumption+)+
  apply(rule fUg_bij,simp,subst env_len2,assumption+,erule ltD,drule ltD)
  apply(subst (asm) ble3,simp,rule_tac c="i" in UnE,assumption)
  apply(unfold fUg_def)
   apply(subst fun_disjoint_apply1,subst dom_f)
    prefer 3
    apply(subst fun_disjoint_apply2,subst domain_of_fun,rule g_tc)
     prefer 2
    apply(rule_tac c="i" and A="7" in UnE,assumption) 
    apply(drule in7)
    apply(erule disjE,simp,subst apply_fun,rule f_tc,(simp add:f_def,simp)+)
    apply(rule_tac P="i=1" in disjE,assumption,subst apply_fun,rule f_tc,simp,simp add:f_def,simp)
   apply(rule_tac P="i=2" in disjE,assumption,subst apply_fun,rule f_tc,simp,simp add:f_def,simp add:nth_append)
    apply(rule_tac P="i=3" in disjE,assumption,subst apply_fun,rule f_tc,simp,simp add:f_def,simp)
    apply(rule_tac P="i=4" in disjE,assumption,subst apply_fun,rule f_tc,simp,simp add:f_def,simp)
    apply(rule_tac P="i=5" in disjE,assumption,subst apply_fun,rule f_tc,simp,simp add:f_def,simp)
    apply(subst apply_fun,rule f_tc,simp,simp add:f_def,simp)
   apply(subst apply_fun,rule f_tc,simp,simp add:f_def,simp,simp add:nth_append,clarsimp)
   apply(rule ble7,rule ble5,simp,rule ble6,rule ble5,simp)
  apply(unfold g_def,subst beta,assumption)
  apply(simp)
  apply(rule_tac n="length(env)" in natE,simp+)
  apply(rule_tac n="i" in natE,simp+,subgoal_tac "i\<in>7",clarsimp,rule ltD,simp)  
  apply(rule_tac n="xa" in natE,simp+,subgoal_tac "xa\<in>7",clarsimp,rule ltD,simp)
  apply(rule_tac n="xb" in natE,simp+,subgoal_tac "xa\<in>7",clarsimp,rule ltD,simp+)
  apply(rule_tac n="xc" in natE,simp+,subgoal_tac "xa\<in>7",clarsimp,rule ltD,simp+)
  apply(rule_tac n="xd" in natE,simp+,subgoal_tac "xa\<in>7",clarsimp,rule ltD,simp+)
  apply(erule_tac n="xe" in natE,simp)    
  apply(rule_tac n="xf" in natE,simp+,clarsimp)
  apply(subst (asm) nth_append,simp+,drule_tac xf="xg" and x="x" in tonto,simp+)
done

lemma perm_sep_env2: "{p,q,r,s,t,u,v,w} \<subseteq> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow>
  perm_list(converse(fUg(length(env))),[p,q,r,s,t,u,v]@env@[w]) = [t,s,w,p,q,r,u,v]@env"
 apply(rule nth_equalityI)
  apply(rule perm_list_tc[of _ "M"],simp,simp add:app_type,(subst env_len,assumption+)+)
  apply(rule fUg_conv_bij,simp,simp add:app_type)
  apply(subst perm_list_length[of _ "M"],simp add:app_type,(subst env_len,assumption+)+)
  apply(rule fUg_conv_bij,simp,simp)
  apply(subst (asm) perm_list_length[of _ "M"],simp add:app_type,(subst env_len,assumption+)+)
  apply(rule fUg_conv_bij,simp)
   apply(subst (asm) env_len,assumption+)
   apply(subst nth_perm[of _ "M"],simp add:app_type)
  apply(subst env_len,assumption+)+
  apply(rule fUg_conv_bij,simp,subst env_len,assumption+,erule ltD,drule ltD)
  apply(subst perm_sep_env[symmetric],assumption+)
  apply(subst nth_perm_conv[of _ "M"],simp add:app_type,(subst env_len2,assumption+)+)
  apply(rule fUg_bij,simp,(subst env_len2,assumption+)+,simp)
done

(* Results to be exported: fUg_bij conv_fUgInv_eq  conv_fUg_eq fUgInv_bij *)
  
context forcing_thms begin  

lemmas transitivity = Transset_intf trans_M

lemma one_in_M: "one \<in> M"
  by (insert one_in_P P_in_M, simp add: transitivity)

lemma G_nonempty: "M_generic(G) \<Longrightarrow> G\<noteq>0"
proof -
  have "P\<subseteq>P" ..
  assume
    "M_generic(G)"
  with P_in_M P_dense \<open>P\<subseteq>P\<close> show
    "G \<noteq> 0"
    unfolding M_generic_def by auto
qed
    
lemma iff_impl_trans: "Q\<longleftrightarrow>R \<Longrightarrow> R\<longrightarrow>S \<Longrightarrow> Q \<longrightarrow>S"
                      "Q\<longrightarrow>R \<Longrightarrow> R\<longleftrightarrow>S \<Longrightarrow> Q \<longrightarrow>S"
                      "Q\<longrightarrow>R \<Longrightarrow> R\<longrightarrow> S \<Longrightarrow> Q\<longrightarrow> S"
  by simp_all  

(* theorem separation_in_genext: *)
(* lemma    *) 

notepad begin   (************** notepad **************)
  {
    fix G \<phi> 
    assume
      "M_generic(G)" 
    with G_nonempty have 
      "G\<noteq>0" .
    assume
      "Transset(M[G])"
    from \<open>M_generic(G)\<close> have 
      "filter(G)" "G\<subseteq>P" 
      unfolding M_generic_def filter_def by simp_all
    assume
      phi: "\<phi>\<in>formula" "arity(\<phi>) \<le> 2"
    let
      ?\<chi>="And(Member(0,2),\<phi>)"
      and   
      ?Pl1="[P,leq,one]"
    fix params
    assume
      "params\<in>list(M)"
    let 
      ?lenenv="length(params)"    
    let
      ?new_form="rename(forces(?\<chi>))`(8#+?lenenv)`fUg(?lenenv)"
    let
      ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),?new_form)))"
    from \<open>params\<in>list(M)\<close> have
      "?lenenv \<in> nat" (*"length(params) \<in> nat"*) by simp_all
    with phi have 
      "arity(?\<chi>) \<le> length(params)#+3" 
      by (simp add:nat_union_abs1,subst nat_union_abs2,(simp add: leI)+)
    with phi have
      "arity(forces(?\<chi>)) \<le> ?lenenv#+8"
      using arity_forces 
        by(simp add:nat_union_abs1,subst nat_union_abs2,(simp add: leI)+)
    with phi definability[of "?\<chi>"] fUg_bij[of ?lenenv] arity_forces \<open>?lenenv \<in> nat\<close> have
      nf_form : "?new_form \<in> formula"
      using ren_lib_tc[of "forces(?\<chi>)" _ "fUg(?lenenv)"]  \<open>?lenenv \<in> nat\<close>
        by(simp)
    then have
      "?\<psi> \<in> formula"
      by simp
    fix \<pi> \<sigma>
    assume
      "\<pi>\<in>M" "\<sigma>\<in>M" "domain(\<pi>) \<times> P \<in> M"
    note in_M1 = \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> \<open>params\<in>list(M)\<close> \<open>domain(\<pi>) \<times> P \<in> M\<close>  P_in_M one_in_M leq_in_M
    {
      fix u
      assume
        "u \<in> domain(\<pi>) \<times> P" "u \<in> M"
      with in_M1 \<open>?new_form \<in> formula\<close> \<open>?\<psi>\<in>formula\<close> have
        Eq1: "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]@params) \<longleftrightarrow> 
                        (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                          sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]@params))"
        by (auto simp add: transitivity)
      {
        fix p \<theta> 
        assume 
          "\<theta> \<in> M" "p\<in>P"
        with P_in_M have "p\<in>M" by (simp add: transitivity)
        note
          in_M = in_M1 \<open>\<theta> \<in> M\<close> \<open>p\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>u \<in> domain(\<pi>) \<times> P\<close> \<open>u \<in> M\<close>
        then have
          "[\<theta>,\<sigma>]@params@[u] \<in> list(M)" by simp
        let
          ?new_env="perm_list(converse(fUg(?lenenv)),?Pl1@[p,\<theta>,\<sigma>,\<pi>]@params@[u])"
        let
          ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),?new_form)))"
        have 
          "n\<in>nat \<Longrightarrow> n<3 \<Longrightarrow> 3 \<union> n = 3" for n   
          by(rule nat_union_abs2,(simp add: leI)+)
        moreover have  
          "1 \<union> 3 = 3" by auto
        ultimately have
          chi: "?\<chi> \<in> formula" "arity(?\<chi>) \<le> 3" "forces(?\<chi>)\<in> formula" 
          and cho: "\<And> n  . n \<in> nat \<Longrightarrow>  3 \<union> arity(\<phi>) \<le> succ(succ(succ(succ(n))))" 
          using phi by (auto)
        with arity_forces have
          "arity(forces(?\<chi>)) \<le> 7" 
          by simp
        from in_M have
          "?Pl1 \<in> list(M)" by simp
        from in_M have
          len : "8#+?lenenv = length(?Pl1@[p,\<theta>,\<sigma>,\<pi>]@params@[u])" 
          using \<open>?lenenv\<in>nat\<close>  by simp 
        have
          Eq1': "?new_env = [\<theta>,p,u,P,leq,one,\<sigma>,\<pi>]@params"
          using in_M perm_sep_env2 app_type
          by simp
        then have
          "sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]@params) \<longleftrightarrow> sats(M,?new_form,?new_env)"
          by simp
        also have
          "sats(M,?new_form,?new_env) \<longleftrightarrow> 
           sats(M,rename(forces(?\<chi>))`(8#+length(params))`fUg(length(params)),?new_env)"           
          by simp
        have
          "... \<longleftrightarrow> sats(M,forces(?\<chi>),?Pl1@[p,\<theta>,\<sigma>,\<pi>]@params@[u])"
          using  phi in_M  transD trans_M  chi cho 
          apply(subst conv_fUgInv_eq,simp,subst conv_fUg_eq,simp)
          apply(subst len,rule ren_Sat_leq[symmetric],simp,simp add:app_type)
          apply(subst (1 2) len[symmetric],rule fUgInv_bij)
           apply(auto simp add: arity_forces nat_union_abs1)
           done
          also have
          "... \<longleftrightarrow> sats(M,forces(?\<chi>), [P, leq, one,p,\<theta>,\<sigma>,\<pi>]@(params@[u]))" by simp
        also have
          "... \<longleftrightarrow> sats(M,forces(?\<chi>), [P, leq, one,p,\<theta>,\<sigma>,\<pi>])"
          using  in_M \<open>arity(forces(?\<chi>)) \<le> 7\<close> \<open>forces(?\<chi>)\<in>formula\<close>
          by (rule_tac arity_sats_iff, auto)
        also have
          " ... \<longleftrightarrow> (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                           sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)]))"
          using in_M phi chi and definition_of_forces 
        proof (intro iffI)
          assume
            a1: "sats(M, forces(?\<chi>), [P, leq, one,p,\<theta>,\<sigma>,\<pi>])"
          note definition_of_forces [THEN iffD1] 
          then have
            "p \<in> P \<Longrightarrow> ?\<chi>\<in>formula \<Longrightarrow> [\<theta>,\<sigma>,\<pi>] \<in> list(M) \<Longrightarrow>
                  sats(M, forces(?\<chi>), [P, leq, one, p] @ [\<theta>,\<sigma>,\<pi>]) \<Longrightarrow> 
              \<forall>G. M_generic(G) \<and> p \<in> G \<longrightarrow> sats(M[G], ?\<chi>, map(val(G), [\<theta>,\<sigma>,\<pi>]))" .
          then show
            "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                  sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)])"
            using  \<open>?\<chi>\<in>formula\<close> \<open>p\<in>P\<close> a1 \<open>\<theta>\<in>M\<close> \<open>\<sigma>\<in>M\<close> \<open>\<pi>\<in>M\<close> by auto
        next
          assume
            "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                   sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)])"
          with definition_of_forces [THEN iffD2] show
            "sats(M, forces(?\<chi>), [P, leq, one,p,\<theta>,\<sigma>,\<pi>])"
            using  \<open>?\<chi>\<in>formula\<close> \<open>p\<in>P\<close> in_M by auto
        qed
        finally have
          "sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]@params) \<longleftrightarrow> (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                           sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)]))" by simp
      }
      then have
        Eq3: "\<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow>
      sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]@params) \<longleftrightarrow>
      (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)]))" 
        for \<theta> p by simp
      with Eq1 have
        "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]@params) \<longleftrightarrow> 
            (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                           (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)])))"
        "\<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow>
      sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]@params) \<longleftrightarrow>
      (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)]))"  for \<theta> p
        by auto
    }
    with in_M1 \<open>?new_form \<in> formula\<close> \<open>?\<psi>\<in>formula\<close> have
      Equivalence: "u\<in> domain(\<pi>) \<times> P \<Longrightarrow> u \<in> M \<Longrightarrow> 
            sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]@params) \<longleftrightarrow> 
            (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
               (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)])))" 
      for u 
      by simp
    from Equivalence  [THEN iffD1]  \<open>M_generic(G)\<close> have
      "u \<in> domain(\<pi>) \<times> P \<Longrightarrow> u \<in> M \<Longrightarrow>
        sats(M,?\<psi>,[u, P, leq, one,\<sigma>, \<pi>]@params) \<Longrightarrow>
          (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                (p \<in> G \<longrightarrow> 
                sats(M[G], ?\<chi>, [val(G, \<theta>), val(G, \<sigma>), val(G, \<pi>)])))" for u
      by force
    moreover have
      "val(G,\<sigma>)\<in>M[G]" and "\<theta>\<in>M \<Longrightarrow> val(G,\<theta>)\<in>M[G]" for \<theta>
      using GenExt_def \<open>\<sigma>\<in>M\<close> by auto
    ultimately have
      "u \<in> domain(\<pi>) \<times> P \<Longrightarrow> u \<in> M \<Longrightarrow>
        sats(M,?\<psi>,[u, P, leq, one,\<sigma>, \<pi>]@params) \<Longrightarrow>
          (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                (p \<in> G \<longrightarrow> 
                val(G,\<theta>) \<in> val(G,\<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<sigma>), val(G, \<pi>)])))" for u
      using \<open>\<pi>\<in>M\<close> by auto
    with \<open>domain(\<pi>)*P\<in>M\<close> have
      "\<forall>u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]@params)  \<longrightarrow>
      (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
        (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<sigma>), val(G, \<pi>)])))"
      by (simp add:transitivity)
    then have
      "{u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]@params) } \<subseteq>
     {u\<in>domain(\<pi>)*P . \<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
       (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<sigma>), val(G, \<pi>)]))}"
      (is "?n\<subseteq>?m") 
      by auto
    with val_mono have
      first_incl: "?n\<in>M \<Longrightarrow> ?m\<in>M \<Longrightarrow> val(G,?n) \<subseteq> val(G,?m)" 
      by simp
    fix c w
    assume 
      "val(G,\<pi>) = c" "val(G,\<sigma>) = w"
    assume
      "domain(\<pi>)\<in>M"
    assume 
      "?n \<in> M"  "?m \<in> M" 
    then have
      in_val_n: "<\<theta>,p>\<in>domain(\<pi>)*P \<Longrightarrow> <\<theta>,p>\<in>M \<Longrightarrow> p\<in>G \<Longrightarrow> p\<in>P \<Longrightarrow> 
      sats(M,?\<psi>,[<\<theta>,p>] @ ?Pl1 @ [\<sigma>,\<pi>]@params) \<Longrightarrow> val(G,\<theta>)\<in>val(G,?n)" for \<theta> p
      using val_of_elem by simp
    from \<open>?m\<in>M\<close> val_of_name and \<open>val(G,\<pi>) = c\<close> \<open>val(G,\<sigma>) = w\<close> have
      "val(G,?m) =
               {val(G,t) .. t\<in>domain(\<pi>) , \<exists>q\<in>P .  
                    (\<exists>\<theta>\<in>M. \<exists>p\<in>P. <t,q> = \<langle>\<theta>, p\<rangle> \<and> 
            (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), w, c])) \<and> q \<in> G)}"
      by auto
    also have
      "... =  {val(G,t) .. t\<in>domain(\<pi>) , \<exists>q\<in>P. 
                   val(G, t) \<in> c \<and> sats(M[G], \<phi>, [val(G, t), w, c]) \<and> q \<in> G}" 
    proof -
      have
        "t\<in>M \<Longrightarrow>
      (\<exists>q\<in>P. (\<exists>\<theta>\<in>M. \<exists>p\<in>P. <t,q> = \<langle>\<theta>, p\<rangle> \<and> 
              (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), w, c])) \<and> q \<in> G)) 
      \<longleftrightarrow> 
      (\<exists>q\<in>P. val(G, t) \<in> c \<and> sats(M[G], \<phi>, [val(G, t), w, c]) \<and> q \<in> G)" for t
        by auto
      then show ?thesis using \<open>domain(\<pi>)\<in>M\<close> by (auto simp add:transitivity)
    qed
    also have
      "... =  {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}"
    proof
      show 
        "... \<subseteq> {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}"
        by auto
    next 
      (* 
      {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}
      \<subseteq>
      {val(G,t)..t\<in>domain(\<pi>),\<exists>q\<in>P.val(G,t)\<in>c\<and>sats(M[G],\<phi>,[val(G,t),w])\<and>q\<in>G}
    *)
      {
        fix x
        assume
          "x\<in>{x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}"
        then have
          "\<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G"
          by simp
        with \<open>val(G,\<pi>) = c\<close> \<open>\<pi>\<in>M\<close> have 
          "\<exists>q\<in>P. \<exists>t\<in>domain(\<pi>). val(G,t) =x \<and> sats(M[G], \<phi>, [val(G,t), w, c]) \<and> q \<in> G" 
          using Sep_and_Replace def_val by auto
      }
      then show 
        " {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G} \<subseteq> ..."
        by (force simp add: SepReplace_iff [THEN iffD2])
    qed
    also have
      " ... = {x\<in>c. sats(M[G], \<phi>, [x, w, c])}"
      using \<open>G\<subseteq>P\<close> \<open>G\<noteq>0\<close> by force
    finally have
      val_m: "val(G,?m) = {x\<in>c. sats(M[G], \<phi>, [x, w, c])}" by simp
    {
      fix x
      assume
        Eq4: "x \<in> {x\<in>c. sats(M[G], \<phi>, [x, w, c])}"
      with \<open>val(G,\<pi>) = c\<close> have 
        "x \<in> val(G,\<pi>)" by simp
      with \<open>\<pi>\<in>M\<close> have
        "\<exists>\<theta>. \<exists>q\<in>G. <\<theta>,q>\<in>\<pi> \<and> val(G,\<theta>) =x" 
        using elem_of_val_pair by auto
      then obtain \<theta> q where
        "<\<theta>,q>\<in>\<pi>" "q\<in>G" "val(G,\<theta>)=x" by auto
      from \<open><\<theta>,q>\<in>\<pi>\<close> \<open>\<pi>\<in>M\<close> trans_M have 
        "\<theta>\<in>M"
        unfolding Pair_def Transset_def by auto 
      with \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> have
        "[val(G,\<theta>), val(G,\<sigma>), val(G,\<pi>)]\<in>list(M[G])" 
        using GenExt_def by auto
      with  Eq4 \<open>val(G,\<theta>)=x\<close> \<open>val(G,\<pi>) = c\<close> \<open>val(G,\<sigma>) = w\<close> \<open>x \<in> val(G,\<pi>)\<close> have
        Eq5: "sats(M[G], And(Member(0,2),\<phi>), [val(G,\<theta>), val(G,\<sigma>), val(G,\<pi>)])" 
        by auto
          (* Recall ?\<chi> = And(Member(0,2),\<phi>) *)
      with \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close>  \<open>\<sigma>\<in>M\<close> and truth_lemma and Eq5 have
        "(\<exists>r\<in>G. sats(M,forces(?\<chi>), [P,leq,one,r,\<theta>,\<sigma>,\<pi>]))"
        using \<open>M_generic(G)\<close> \<open>\<phi>\<in>formula\<close> by auto
      then obtain r where      (* I can't "obtain" this directly *)
        "r\<in>G" "sats(M,forces(?\<chi>), [P,leq,one,r,\<theta>,\<sigma>,\<pi>])" by auto
      with \<open>filter(G)\<close> and \<open>q\<in>G\<close> obtain p where
        "p\<in>G" "<p,q>\<in>leq" "<p,r>\<in>leq" 
        unfolding filter_def compat_in_def by force
      with \<open>r\<in>G\<close>  \<open>q\<in>G\<close> P_in_M have
        "p\<in>P" "r\<in>P" "q\<in>P" "p\<in>M"
        using \<open>G\<subseteq>P\<close>  by (auto simp add:transitivity)
      with \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> \<open>sats(M,forces(And(Member(0,2),\<phi>)), [P,leq,one,r,\<theta>,\<sigma>,\<pi>])\<close> have
        "sats(M,forces(?\<chi>), [P,leq,one,p,\<theta>,\<sigma>,\<pi>])"
        using \<open><p,r>\<in>leq\<close> streghtening by simp
      with \<open>p\<in>P\<close> \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> have
        "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                 sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F,\<pi>)])"
        using definition_of_forces by simp
      with \<open>p\<in>P\<close> \<open>\<theta>\<in>M\<close>  have
        Eq6: "\<exists>\<theta>'\<in>M. \<exists>p'\<in>P.  <\<theta>,p> = <\<theta>',p'> \<and> (\<forall>F. M_generic(F) \<and> p' \<in> F \<longrightarrow> 
                 sats(M[F], ?\<chi>, [val(F, \<theta>'), val(F, \<sigma>), val(F,\<pi>)]))" by auto
      from \<open>\<pi>\<in>M\<close> \<open><\<theta>,q>\<in>\<pi>\<close> have
        "<\<theta>,q> \<in> M" by (simp add:transitivity)
      from \<open><\<theta>,q>\<in>\<pi>\<close> \<open>\<theta>\<in>M\<close> \<open>p\<in>P\<close>  \<open>p\<in>M\<close> have
        "<\<theta>,p>\<in>M" "<\<theta>,p>\<in>domain(\<pi>)\<times>P" 
        using pairM by auto
      with \<open>\<theta>\<in>M\<close> Eq6 \<open>p\<in>P\<close> have
        "sats(M,?\<psi>,[<\<theta>,p>] @ ?Pl1 @ [\<sigma>,\<pi>]@params)"
        using Equivalence [THEN iffD2]  by auto
          (* with \<open><\<theta>,p>\<in>domain(\<pi>)\<times>P\<close> have
      "\<exists>u\<in>domain(\<pi>)\<times>P. sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>]@params)" by auto *)
      with \<open><\<theta>,p>\<in>domain(\<pi>)\<times>P\<close>  \<open><\<theta>,p>\<in>M\<close> \<open>p\<in>G\<close> \<open>val(G,\<theta>)=x\<close> have
        "x\<in>val(G,?n)"   
        using in_val_n by auto
    }
    with val_m  have 
      "val(G,?m) \<subseteq> val(G,?n)" by auto
    with \<open>?n\<in>M\<close> \<open>?m\<in>M\<close> val_m first_incl have
      "val(G,?n) = {x\<in>c. sats(M[G], \<phi>, [x, w, c])}" by auto
    with \<open>?n\<in>M\<close> GenExt_def have
      "{x\<in>c. sats(M[G], \<phi>, [x, w, c])}\<in> M[G]" by force
  }
  then have
    sep_aux: "M_generic(G) \<Longrightarrow> Transset(M[G]) \<Longrightarrow>
     \<phi> \<in> formula \<Longrightarrow> arity(\<phi>) \<le> 2 \<Longrightarrow> val(G, \<pi>) = c \<Longrightarrow> val(G, \<sigma>) = w \<Longrightarrow> params \<in> list(M) \<Longrightarrow> 
     \<pi> \<in> M \<Longrightarrow> \<sigma> \<in> M \<Longrightarrow> domain(\<pi>) \<times> P \<in> M \<Longrightarrow>  domain(\<pi>) \<in> M \<Longrightarrow>
     {u \<in> domain(\<pi>) \<times> P .
        sats(M, Exists(Exists(And(pair_fm(0, 1, 2), rename(forces(And(Member(0, 2), \<phi>))) ` 
          (7#+length(params)) ` fUg(length(params))))),
         [u] @ [P, leq, one] @ [\<sigma>,\<pi>] @ params)} \<in>  M \<Longrightarrow>
     {u \<in> domain(\<pi>) \<times> P .
       \<exists>\<theta>\<in>M. \<exists>p\<in>P. u = \<langle>\<theta>, p\<rangle> \<and> (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<sigma>),val(G,\<pi>)]))} \<in> M 
      \<Longrightarrow>
      {x\<in>c. sats(M[G], \<phi>, [x, w, c])}\<in> M[G]" for G \<pi> c w \<sigma> \<phi> params by simp
  {
    fix \<phi> G \<pi> c \<sigma> w params   
    assume 
      asm: "arity(\<phi>)= 1" "M_generic(G)" "Transset(M[G])" "
     \<phi> \<in> formula " "val(G, \<pi>) = c" "val(G, \<sigma>) = w" "params \<in> list(M)" 
      "\<pi> \<in> M" "\<sigma> \<in> M" "domain(\<pi>) \<times> P \<in> M" " domain(\<pi>) \<in> M" "
     {u \<in> domain(\<pi>) \<times> P .
        sats(M, Exists(Exists(And(pair_fm(0, 1, 2), rename(forces(And(Member(0, 2), \<phi>))) ` 
          (7#+length(params)) ` fUg(length(params))))),
         [u] @ [P, leq, one] @ [\<sigma>,\<pi>] @ params)} \<in>  M" "
     {u \<in> domain(\<pi>) \<times> P .
       \<exists>\<theta>\<in>M. \<exists>p\<in>P. u = \<langle>\<theta>, p\<rangle> \<and> (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<sigma>),val(G,\<pi>)]))} \<in> M"
      "c\<in>M[G]" "w\<in>M[G]"
    then have
      "arity(\<phi>)\<le> 2"  by simp_all
    with asm sep_aux have
      S_in_MG: "{x\<in>c. sats(M[G], \<phi>, [x,w, c])}\<in> M[G]"  by simp
    {
      fix x
      assume 
        "x\<in>c"
      with asm have
        "x\<in>M[G]"
        by (simp add:\<open>Transset(M[G])\<close> Transset_intf)
      with \<open>arity(\<phi>) = 1\<close> \<open>\<phi> \<in> formula\<close> \<open>c\<in>M[G]\<close> \<open>w\<in>M[G]\<close> have
        "sats(M[G], \<phi>, [x]@[w, c]) \<longleftrightarrow> sats(M[G], \<phi>, [x])" 
        by (rule_tac arity_sats_iff, simp_all)   (* Enhance this *)
    }
    with S_in_MG have
      "{x\<in>c. sats(M[G], \<phi>, [x])}\<in> M[G]"  by simp   
  }
  {
    fix \<phi> G \<pi> c \<sigma> w params   
    assume 
      asm: "arity(\<phi>)= 2" "M_generic(G)" "Transset(M[G])" "
     \<phi> \<in> formula " "val(G, \<pi>) = c" "val(G, \<sigma>) = w" "params \<in> list(M)" 
      "\<pi> \<in> M" "\<sigma> \<in> M" "domain(\<pi>) \<times> P \<in> M" " domain(\<pi>) \<in> M" "
     {u \<in> domain(\<pi>) \<times> P .
        sats(M, Exists(Exists(And(pair_fm(0, 1, 2), rename(forces(And(Member(0, 2), \<phi>))) ` 
          (7#+length(params)) ` fUg(length(params))))),
         [u] @ [P, leq, one] @ [\<sigma>,\<pi>] @ params)} \<in>  M" "
     {u \<in> domain(\<pi>) \<times> P .
       \<exists>\<theta>\<in>M. \<exists>p\<in>P. u = \<langle>\<theta>, p\<rangle> \<and> (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<sigma>),val(G,\<pi>)]))} \<in> M"
      "c\<in>M[G]" "w\<in>M[G]"
    then have
      "arity(\<phi>)\<le> 2"  by simp_all
    with asm sep_aux have
      S_in_MG: "{x\<in>c. sats(M[G], \<phi>, [x,w,c])}\<in> M[G]"  by simp
    {
      fix x
      assume 
        "x\<in>c" 
      with asm have
        "x\<in>M[G]"
        by (simp add:\<open>Transset(M[G])\<close> Transset_intf)
      with \<open>arity(\<phi>)= 2\<close> \<open>\<phi> \<in> formula\<close> \<open>c\<in>M[G]\<close> \<open>w\<in>M[G]\<close> have
        "sats(M[G], \<phi>, [x,w]@[c]) \<longleftrightarrow> sats(M[G], \<phi>, [x,w])" 
        by (rule_tac arity_sats_iff, simp_all)   (* Enhance this *)
    }
    with S_in_MG have
      "{x\<in>c. sats(M[G], \<phi>, [x,w])}\<in> M[G]"  by simp   
  }
end