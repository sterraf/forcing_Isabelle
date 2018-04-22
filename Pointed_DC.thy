(*  Title:      ZF/AC/DC.thy
    Author:     Krzysztof Grabczewski

The proofs concerning the Axiom of Dependent Choice.
*)

theory Pointed_DC
imports DC (*AC_Equiv Hartog Cardinal_aux*)
begin

definition
  pointDC :: o  where
    "pointDC == \<forall>a A B R. a \<in> domain(R) \<and> R \<subseteq> A*B \<and> R\<noteq>0 \<and> range(R) \<subseteq> domain(R) 
                    \<longrightarrow> (\<exists>f \<in> nat->domain(R). f`0 = a \<and> (\<forall>n \<in> nat. <f`n,f`succ(n)>\<in>R))"

(* ************************************************************************
   DC(omega) ==> DC                                                       
                                                                          
   The scheme of the proof:                                               
                                                                          
   Assume DC(omega). Let R and x satisfy the premise of DC.               
                                                                          
   Define XX and RR as follows:                                           
                                                                          
    XX = (\<Union>n \<in> nat. {f \<in> succ(n)->domain(R). \<forall>k \<in> n. <f`k, f`succ(k)> \<in> R})

    RR = {<z1,z2>:Fin(XX)*XX. 
           (domain(z2)=succ(\<Union>f \<in> z1. domain(f)) &
            (\<forall>f \<in> z1. restrict(z2, domain(f)) = f)) |      
           (~ (\<exists>g \<in> XX. domain(g)=succ(\<Union>f \<in> z1. domain(f)) &
                        (\<forall>f \<in> z1. restrict(g, domain(f)) = f)) &           
            z2={<0,x>})}                                          
                                                                          
   Then XX and RR satisfy the hypotheses of DC(omega).                    
   So applying DC:                                                        
                                                                          
         \<exists>f \<in> nat->XX. \<forall>n \<in> nat. f``n RR f`n                             
                                                                          
   Thence                                                                 
                                                                          
         ff = {<n, f`n`n>. n \<in> nat}                                         
                                                                          
   is the desired function.                                               
                                                                          
************************************************************************* *)
locale imp_ptdDC =
  fixes XX and RR and a and x and R and f and allRR
  defines XX_def: "XX == (\<Union>n \<in> nat.
                      {f \<in> succ(n)->domain(R). f`0 = a \<and> (\<forall>k \<in> n. <f`k, f`succ(k)> \<in> R)})"
      and RR_def:
         "RR == {<z1,z2>:Fin(XX)*XX. 
                  (domain(z2)=succ(\<Union>f \<in> z1. domain(f))  
                    & (\<forall>f \<in> z1. restrict(z2, domain(f)) = f))
                  | (~ (\<exists>g \<in> XX. domain(g)=succ(\<Union>f \<in> z1. domain(f))  
                     & (\<forall>f \<in> z1. restrict(g, domain(f)) = f)) & z2={<0,a>})}"
      and allRR_def:
        "allRR == \<forall>b<nat.
                   <f``b, f`b> \<in>  
                    {<z1,z2>\<in>Fin(XX)*XX. (domain(z2)=succ(\<Union>f \<in> z1. domain(f))
                                    & (\<Union>f \<in> z1. domain(f)) = b  
                                    & (\<forall>f \<in> z1. restrict(z2,domain(f)) = f))}"
  assumes  point_in_dom: "a \<in> domain(R)"
      and  x_in_dom: "x \<in> domain(R)"
      
lemma singleton_in_funs_ptd: 
 "a \<in> X ==> {<0,a>} \<in> 
            (\<Union>n \<in> nat. {f \<in> succ(n)->X. f`0 = a \<and> (\<forall>k \<in> n. <f`k, f`succ(k)> \<in> R)})"
apply (rule nat_0I [THEN UN_I])
apply (force simp add: singleton_0 [symmetric]
             intro!: singleton_fun [THEN Pi_type])
done
        
lemma (in imp_ptdDC) lemma4ptd:
     "[| range(R) \<subseteq> domain(R);  a \<in> domain(R) |]   
      ==> RR \<subseteq> Pow(XX)*XX &   
             (\<forall>Y \<in> Pow(XX). Y \<prec> nat \<longrightarrow> (\<exists>x \<in> XX. <Y,x>:RR))"
apply (rule conjI)
apply (force dest!: FinD [THEN PowI] simp add: RR_def)
apply (rule impI [THEN ballI])
apply (drule Finite_Fin [OF lesspoll_nat_is_Finite PowD], assumption)
apply (case_tac
       "\<exists>g \<in> XX. domain (g) =
             succ(\<Union>f \<in> Y. domain(f)) & (\<forall>f\<in>Y. restrict(g, domain(f)) = f)")
apply (simp add: RR_def, blast)
apply (safe del: domainE)
apply (unfold XX_def RR_def)
  apply (rule rev_bexI)
apply (erule  singleton_in_funs_ptd)
  apply (simp add: nat_0I [THEN rev_bexI] cons_fun_type2)
 
done

lemma (in imp_ptdDC) UN_image_succ_eq:
     "[| f \<in> nat->X; n \<in> nat |] 
      ==> (\<Union>x \<in> f``succ(n). P(x)) =  P(f`n) \<union> (\<Union>x \<in> f``n. P(x))"
by (simp add: image_fun OrdmemD) 

lemma (in imp_ptdDC) UN_image_succ_eq_succ:
     "[| (\<Union>x \<in> f``n. P(x)) = y; P(f`n) = succ(y);   
         f \<in> nat -> X; n \<in> nat |] ==> (\<Union>x \<in> f``succ(n). P(x)) = succ(y)"
by (simp add: UN_image_succ_eq, blast)

lemma (in imp_ptdDC) apply_domain_type:
     "[| h \<in> succ(n) -> D;  n \<in> nat; domain(h)=succ(y) |] ==> h`y \<in> D"
by (fast elim: apply_type dest!: trans [OF sym domain_of_fun])

lemma (in imp_ptdDC) image_fun_succ:
     "[| h \<in> nat -> X; n \<in> nat |] ==> h``succ(n) = cons(h`n, h``n)"
by (simp add: image_fun OrdmemD) 

lemma (in imp_ptdDC) f_n_type:
     "[| domain(f`n) = succ(k); f \<in> nat -> XX;  n \<in> nat |]    
      ==> f`n \<in> succ(k) -> domain(R)"
apply (unfold XX_def)
apply (drule apply_type, assumption)
apply (fast elim: domain_eq_imp_fun_type)
done

lemma (in imp_ptdDC) f_n_pairs_in_R [rule_format]: 
     "[| h \<in> nat -> XX;  domain(h`n) = succ(k);  n \<in> nat |]   
      ==> \<forall>i \<in> k. <h`n`i, h`n`succ(i)> \<in> R"
apply (unfold XX_def)
apply (drule apply_type, assumption)
apply (elim UN_E CollectE)
apply (drule domain_of_fun [symmetric, THEN trans], assumption, simp)
done

lemma (in imp_ptdDC) restrict_cons_eq_restrict: 
     "[| restrict(h, domain(u))=u;  h \<in> n->X;  domain(u) \<subseteq> n |]   
      ==> restrict(cons(<n, y>, h), domain(u)) = u"
apply (unfold restrict_def)
apply (simp add: restrict_def Pi_iff)
apply (erule sym [THEN trans, symmetric])
apply (blast elim: mem_irrefl)  
done

lemma (in imp_ptdDC) all_in_image_restrict_eq:
     "[| \<forall>x \<in> f``n. restrict(f`n, domain(x))=x;   
         f \<in> nat -> XX;   
         n \<in> nat;  domain(f`n) = succ(n);   
         (\<Union>x \<in> f``n. domain(x)) \<subseteq> n |]  
      ==> \<forall>x \<in> f``succ(n). restrict(cons(<succ(n),y>, f`n), domain(x)) = x"
apply (rule ballI)
apply (simp add: image_fun_succ)
apply (drule f_n_type, assumption+)
apply (erule disjE)
 apply (simp add: domain_of_fun restrict_cons_eq) 
apply (blast intro!: restrict_cons_eq_restrict)
done

lemma aux1 : "0\<in>domain(f`m) \<Longrightarrow> f ` m ` 0 = a \<Longrightarrow>  cons(\<langle>succ(m), z\<rangle>, f ` m) ` 0 = a"
sorry
  
lemma (in imp_ptdDC) simplify_recursion: 
     "[| \<forall>b<nat. <f``b, f`b> \<in> RR;   
         f \<in> nat -> XX; range(R) \<subseteq> domain(R)|]    
      ==> allRR"
apply (unfold RR_def allRR_def)
apply (rule oallI, drule ltD)
apply (erule nat_induct)
apply (drule_tac x=0 in ospec, blast intro: Limit_has_0) 
apply (force simp add: singleton_fun [THEN domain_of_fun] singleton_in_funs) 
(*induction step*) (** LEVEL 5 **)
(*prevent simplification of ~\<exists> to \<forall>~ *)
apply (simp only: separation split)
apply (drule_tac x="succ(x)" in ospec, blast intro: ltI)
apply (elim conjE disjE)
apply (force elim!: trans subst_context
             intro!: UN_image_succ_eq_succ)
apply (erule notE)
apply (simp add: XX_def UN_image_succ_eq_succ)
apply (elim conjE bexE)
apply (drule apply_domain_type, assumption+)
apply (erule domainE)+
apply (frule f_n_type)
apply (simp add: XX_def, assumption+)
apply (rule rev_bexI, erule nat_succI)
apply (rename_tac m i j z) 
apply (rule_tac x = "cons(<succ(m), z>, f`m)" in bexI)
prefer 2 apply (blast intro: cons_fun_type2) 
apply (rule conjI)
prefer 2 apply (rule conjI)
prefer 2 apply (fast del: ballI subsetI
                 elim: trans [OF _ subst_context, THEN domain_cons_eq_succ]
                       subst_context
                       all_in_image_restrict_eq [simplified XX_def]
                       trans equalityD1)
(*one remaining subgoal*)
apply (rule ballI)
apply (erule succE)
(** LEVEL 25 **)
 apply (simp add: cons_val_n cons_val_k)
(*assumption+ will not perform the required backtracking!*)
apply (drule f_n_pairs_in_R [simplified XX_def, OF _ domain_of_fun], 
       assumption, assumption, assumption)
   apply (simp add: nat_into_Ord [THEN succ_in_succ] succI2 cons_val_k)
(* Final goal introduced by 'a' *)
  apply (rule aux1)
  prefer 2 apply (assumption)
oops    


lemma (in imp_ptdDC) lemma2ptd: 
     "[| allRR; f \<in> nat->XX; range(R) \<subseteq> domain(R); x \<in> domain(R); n \<in> nat |]
      ==> f`n \<in> succ(n) -> domain(R) & (\<forall>i \<in> n. <f`n`i, f`n`succ(i)>:R)"
apply (unfold allRR_def)
apply (drule ospec)
apply (erule ltI [OF _ Ord_nat])
apply (erule CollectE, simp)
apply (rule conjI)
prefer 2 apply (fast elim!: f_n_pairs_in_R trans subst_context)
apply (unfold XX_def)
apply (fast elim!: trans [THEN domain_eq_imp_fun_type] subst_context)
done

lemma (in imp_ptdDC) lemma3ptd:
     "[| allRR; f \<in> nat->XX; n\<in>nat; range(R) \<subseteq> domain(R);  x \<in> domain(R) |]
      ==> f`n`n = f`succ(n)`n"
apply (frule lemma2ptd [THEN conjunct1, THEN domain_of_fun], assumption+)
apply (unfold allRR_def)
apply (drule ospec) 
apply (drule ltI [OF nat_succI Ord_nat], assumption, simp)
apply (elim conjE ballE)
apply (erule restrict_eq_imp_val_eq [symmetric], force) 
apply (simp add: image_fun OrdmemD) 
done


theorem DC_nat_imp_ptdDC: "DC(nat) ==> pointDC"
apply (unfold DC_def pointDC_def)
apply (intro allI impI)
apply (erule asm_rl conjE ex_in_domain [THEN exE] allE)+
apply (erule impE [OF _ imp_ptdDC.lemma4ptd], assumption+)
apply (erule bexE)
apply (drule imp_ptdDC.simplify_recursion, assumption+)
apply (rule_tac x = "\<lambda>n \<in> nat. f`n`n" in bexI)
apply (rule_tac [2] lam_type)
apply (erule_tac [2] apply_type [OF imp_ptdDC.lemma2ptd [THEN conjunct1] succI1])
apply (rule ballI)
apply (frule_tac n="succ(n)" in imp_ptdDC.lemma2ptd, 
       (assumption|erule nat_succI)+)
apply (drule imp_ptdDC.lemma3ptd, auto)
done

end