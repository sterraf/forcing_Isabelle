theory forces_locale imports Formula val_check ZFCaxioms Pointed_DC begin

locale forcing_poset =
  fixes P leq uno
  assumes uno_in_P:         "uno \<in> P"
      and leq_preord:       "preorder_on(P,leq)"
      and uno_max:          "\<forall>p\<in>P. <p,uno>\<in>leq"

definition (in forcing_poset)
  dense :: "i\<Rightarrow>o" where
  "dense(D) == \<forall>p\<in>P. \<exists>d\<in>D . <d,p>\<in>leq"
    
definition (in forcing_poset)
  increasing :: "i\<Rightarrow>o" where
  "increasing(F) == \<forall>p\<in>P. \<forall>x\<in>P. x\<in>F \<and> <x,p>\<in>leq \<longrightarrow> p\<in>F"


(* En esta definición habría que agregar que (A,r) es preorden? *)
definition compat_in :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "compat_in(A,r,p,q) == \<exists>d\<in>A . <d,p>\<in>r \<and> <d,q>\<in>r"

lemma compat_inI : 
      "\<lbrakk> d\<in>A ; <d,p>\<in>r ; <d,g>\<in>r \<rbrakk> \<Longrightarrow> compat_in(A,r,p,g)"
  apply (simp add: compat_in_def)
  apply (rule_tac x="d" in bexI,simp+)
  done

lemma refl_compat:
  "\<lbrakk> refl(A,r) ; <p,q> \<in> r | p=q | <q,p> \<in> r ; p\<in>A ; q\<in>A\<rbrakk> \<Longrightarrow> compat_in(A,r,p,q)"
  apply (simp add: refl_def)
  apply (rule_tac P="<p,q>\<in>r" and Q="p=q \<or> <q,p>\<in>r" in disjE,assumption)
  apply (rule_tac d="p" in compat_inI,assumption,simp+)
  apply (rule_tac P="p=q" in disjE,assumption)
   apply (rule_tac d="q" in compat_inI,assumption,simp+)
  apply (rule_tac d="q" in compat_inI,assumption,simp)
  apply (rule bspec,assumption+)
  done
 
lemma  chain_compat:
  "refl(A,r) \<Longrightarrow> linear(A,r) \<Longrightarrow>  (\<forall>p\<in>A.\<forall>q\<in>A. compat_in(A,r,p,q))"
  apply (rule ballI,rule ballI)
  apply (unfold linear_def)
  apply (drule_tac x="p" in bspec,assumption,drule_tac x="q" in bspec,assumption)
  apply (rule refl_compat,assumption+)
  done

definition (in forcing_poset)
  compat :: "i\<Rightarrow>i\<Rightarrow>o" where
  "compat(p,q) == compat_in(P,leq,p,q)"

definition (in forcing_poset)
  antichain :: "i\<Rightarrow>o" where
  "antichain(A) == A\<subseteq>P \<and> (\<forall>p\<in>A.\<forall>q\<in>A.(\<not>compat(p,q)))"

definition (in forcing_poset)
  filter :: "i\<Rightarrow>o" where
  "filter(G) == G\<subseteq>P \<and> increasing(G) \<and> (\<forall>p\<in>G. \<forall>q\<in>G. compat_in(G,leq,p,q))"

definition (in forcing_poset) 
  upclosure :: "i\<Rightarrow>i" where
  "upclosure(A) == {p\<in>P.\<exists>a\<in>A.<a,p>\<in>leq}"
  
lemma (in forcing_poset) upclosureI [intro] : "p\<in>P \<Longrightarrow> a\<in>A \<Longrightarrow> <a,p>\<in>leq \<Longrightarrow> p\<in>upclosure(A)"
  by (simp add:upclosure_def, auto)

lemma (in forcing_poset) upclosureE [elim] :
  "p\<in>upclosure(A) \<Longrightarrow> (\<And>x a. x\<in>P \<Longrightarrow> a\<in>A \<Longrightarrow> <a,x>\<in>leq \<Longrightarrow> R) \<Longrightarrow> R"
  apply (simp add:upclosure_def)
  apply (erule conjE)
  apply (drule_tac P="\<lambda>a.\<langle>a, p\<rangle> \<in> leq" 
               and Q="R" in bexE, assumption+)
done

lemma (in forcing_poset) upclosureD [dest] :
   "p\<in>upclosure(A) \<Longrightarrow> \<exists>a\<in>A.(<a,p>\<in>leq) \<and> p\<in>P"
  by (simp add:upclosure_def)
   
lemma  (in forcing_poset) upclosure_increasing :
  "A\<subseteq>P \<Longrightarrow> increasing(upclosure(A))"
  apply (unfold increasing_def upclosure_def, simp)
  apply clarify
  apply (rule_tac x="a" in bexI)
  apply (insert leq_preord, unfold preorder_on_def)
  apply (drule conjunct2, unfold trans_on_def) 
  apply (drule_tac x="a" in bspec, fast)
  apply (drule_tac x="x" in bspec, assumption) 
  apply (drule_tac x="p" in bspec, assumption)
  apply (simp, assumption)
  done
  
lemma (in forcing_poset) upclosure_in_P: "A \<subseteq> P \<Longrightarrow> upclosure(A) \<subseteq> P"
  apply (rule   subsetI)
  apply (simp add:upclosure_def)  
  done

lemma (in forcing_poset) A_sub_upclosure: "A \<subseteq> P \<Longrightarrow> A\<subseteq>upclosure(A)"
  apply (rule   subsetI)
  apply (simp add:upclosure_def, auto)
  apply (insert leq_preord, unfold preorder_on_def refl_def, auto)
  done
 
lemma (in forcing_poset) elem_upclosure: "A\<subseteq>P \<Longrightarrow> x\<in>A  \<Longrightarrow> x\<in>upclosure(A)"
  by (blast dest:A_sub_upclosure)
    
lemma (in forcing_poset) closure_compat_filter:
  "A\<subseteq>P \<Longrightarrow> (\<forall>p\<in>A.\<forall>q\<in>A. compat_in(A,leq,p,q)) \<Longrightarrow> filter(upclosure(A))"
  apply (unfold filter_def)
  apply (intro conjI)
  apply (rule upclosure_in_P, assumption)
   apply (rule upclosure_increasing, assumption)
  apply (unfold compat_in_def)
  apply (rule ballI)+
  apply (rename_tac x y)
  apply (drule upclosureD)+
  apply (erule bexE)+
  apply (rename_tac a b)
  apply (drule_tac A="A" 
               and x="a" in bspec, assumption)
  apply (drule_tac A="A" 
               and x="b" in bspec, assumption)
  apply (auto)
  apply (rule_tac x="d" in bexI)
  prefer 2 apply (simp add:A_sub_upclosure [THEN subsetD])
  apply (insert leq_preord, unfold preorder_on_def trans_on_def,  drule conjunct2)
  apply (rule conjI)
  apply (drule_tac x="d" in bspec, rule_tac A="A" in subsetD, assumption+) 
  apply (drule_tac x="a" in bspec, rule_tac A="A" in subsetD, assumption+) 
  apply (drule_tac x="x" in bspec, assumption, auto)
done

(*****************************************
 *  No use for these for a while         *
 *                                       *
theorem Ord_dependent_choice:
    "Ord(A) \<Longrightarrow> \<forall>a\<in>A.\<exists>b\<in>A. <a,b> \<in> s  \<Longrightarrow>
     \<forall>x\<in>A.\<exists>f\<in>(nat\<rightarrow>A).f`0=x \<and> (\<forall>n\<in>nat.(<f`n,f`(n+1)>\<in> s))"
  oops
    
theorem wo_dependent_choice:
    "well_ord(A,r) \<Longrightarrow> \<forall>a\<in>A.\<exists>b\<in>A. <a,b> \<in> s  \<Longrightarrow>
     \<forall>x\<in>A.\<exists>f\<in>(nat\<rightarrow>A).f`0=x \<and> (\<forall>n\<in>nat.(<f`n,f`(n+1)>\<in> s))"
  oops
 *                                       *
 *****************************************)

locale countable_generic = forcing_poset +
  fixes \<D>
  assumes countable_subs_of_P:  "\<D> \<in> nat\<rightarrow>Pow(P)"
  and     seq_of_denses:        "\<forall>n \<in> nat. dense(\<D>`n)"

definition (in countable_generic)
  D_generic :: "i\<Rightarrow>o" where
  "D_generic(G) == filter(G) \<and> (\<forall>n\<in>nat.(\<D>`n)\<inter>G\<noteq>0)"

lemma refl_monot_domain: "refl(B,r) \<Longrightarrow> A\<subseteq>B \<Longrightarrow> refl(A,r)"  
  apply (drule subset_iff [THEN iffD1])
  apply (unfold refl_def) 
  apply (blast)
  done

lemma decr_seq_linear: "f \<in> nat -> P \<Longrightarrow>
         \<forall>n\<in>nat.  \<langle>f ` succ(n), f ` n\<rangle> \<in> leq \<Longrightarrow>
           trans[P](leq) \<Longrightarrow> linear(f `` nat, leq)"
  apply (unfold linear_def)
  apply (rule ball_image_simp [THEN iffD2], assumption, simp, rule ballI)+
  apply (rename_tac y)
  sorry

lemma ball_distr_conj_iff: "(\<forall>x\<in>A. P(x) \<and> Q(x)) \<longleftrightarrow> (\<forall>x\<in>A. P(x)) \<and> (\<forall>x\<in>A. Q(x))"
 by blast
    
lemma subset_fun_image: "f:N\<rightarrow>P \<Longrightarrow> f``N\<subseteq>P"
  apply (simp add: image_fun)
  apply (rule subsetI, simp, erule bexE)
  apply (simp add:apply_funtype)
  done
    
(*  "[| f \<in> Pi(A,B);  C \<subseteq> A |] ==> f``C = {f`x. x \<in> C}"
apply (simp add: Pi_iff)
apply (blast intro: image_function)
done
*)
lemma (in forcing_poset) aux_RS1:  "f \<in> N \<rightarrow> P \<Longrightarrow> n\<in>N \<Longrightarrow> f`n \<in> upclosure(f ``N)"
  apply (rule_tac  elem_upclosure)
   apply (rule subset_fun_image, assumption)
  apply (simp add: image_fun, blast)
  done
    
theorem (in countable_generic) rasiowa_sikorski: 
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> D_generic(G)"
  apply (subgoal_tac 
        "\<forall>x\<in>P. \<forall>n\<in>nat. 
          \<exists>y\<in>P. <x,y> \<in> (\<lambda>m\<in>nat. {<x,y>\<in>P*P. <y,x>\<in>leq \<and> y\<in>\<D>`(pred(m))})`n")
   apply (drule sequence_DC, simp)      
   apply (drule_tac x="p" in bspec, assumption) 
    apply (erule bexE, rename_tac f)
   apply (subgoal_tac "linear(f``nat, leq)")
   apply (subgoal_tac "refl(f``nat, leq)")
     apply (drule chain_compat, assumption)
     apply(rule_tac x="upclosure(f``nat)" in exI)
     apply(rule conjI)
      apply (rule_tac b="p" and a="f`0" in ssubst, simp)
      apply (rule aux_RS1, simp_all)
     apply (unfold D_generic_def, rule conjI)
      apply (rule closure_compat_filter)
        apply (drule_tac C="nat" in image_fun,  simp_all, blast)
      apply (rule ballI, rename_tac n)
     apply (rule_tac a="f`succ(n)" in not_emptyI, simp)
      apply (rule aux_RS1, simp_all)
      prefer 3 apply (insert seq_of_denses)
      apply (rule ballI)+
      apply (rename_tac x n)
      apply (drule_tac x="pred(n)" and A="nat" in bspec, simp_all add:dense_def)
      apply (drule_tac x="x" in bspec, assumption)
      apply (erule bexE, rename_tac d)
      apply (rule_tac x="d" in bexI, simp)
      apply (insert countable_subs_of_P)
      apply (subgoal_tac "\<D> ` Arith.pred(n)\<subseteq>P", blast)
      apply (rule  PowD)
      apply (rule_tac f="\<D>" in apply_funtype, simp+)
   apply (rule_tac a="{f`x. x \<in> nat}" 
               and P="\<lambda>x. refl(x,leq)" in ssubst)
    apply (frule_tac C="nat" in image_fun, simp_all)
   apply (insert leq_preord, unfold preorder_on_def, drule conjunct1)
   apply (rule_tac A="{f ` x . x \<in> nat}" 
               and B="P" in refl_monot_domain, auto)
  apply (rule_tac P="P" in decr_seq_linear, assumption)
   apply (drule ball_distr_conj_iff [THEN iffD1], (erule conjE) | assumption)+
  done
    
locale forcing_data = forcing_poset +
  fixes M enum
  assumes trans_M:          "Transset(M)"
      and M_model_ZF:       "satT(M,ZFTh,[])"
      and M_countable:      "enum\<in>bij(nat,M)"
      and P_in_M:           "P \<in> M"

definition (in forcing_data)
  generic :: "i\<Rightarrow>o" where
  "generic(G) == filter(G) \<and> (\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"
      
(* Prototyping Forcing relation and theorems as a locale*)
locale forcing_thms = forcing_poset + forcing_data +
  fixes forces :: "i \<Rightarrow> i"
  assumes definition_of_forces: "\<forall>env\<in>list(M).
                  sats(M,forces(\<phi>), [P,leq,uno,p] @ env) \<longleftrightarrow>
                  (\<forall>G.(generic(G)\<and> p\<in>G)\<longrightarrow>sats(gen_ext(M,P,G),\<phi>,map(valR(M,P,G),env)))"
      and definability:      "forces(\<phi>) \<in> formula"
      and truth_lemma:      "\<forall>env\<in>list(M).\<forall>G.(generic(G) \<and> p\<in>G)\<longrightarrow>
                  ((\<exists>p\<in>P.(sats(M,forces(\<phi>), [P,leq,uno,p] @ env))) \<longleftrightarrow>
                  (sats(gen_ext(M,P,G),\<phi>,map(valR(M,P,G),env))))"

lemma (in forcing_thms) bounded_separation_in_genext:
    "\<forall>p\<in>formula. arity(p)<5 \<longrightarrow> sats(gen_ext(M,P,G),ZFSeparation(p),[])"
oops

theorem (in forcing_thms) separation_in_genext:
    "\<forall>p\<in>formula. sats(gen_ext(M,P,G),ZFSeparation(p),[])"
oops
end