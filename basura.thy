theory basura imports Formula val_check ZFCaxioms Pointed_DC begin

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

lemma decr_succ_decr: "f \<in> nat -> P \<Longrightarrow> preorder_on(P,leq) \<Longrightarrow>
         \<forall>n\<in>nat.  \<langle>f ` succ(n), f ` n\<rangle> \<in> leq \<Longrightarrow>
           n\<in>nat \<Longrightarrow> m\<in>nat \<Longrightarrow> n\<le>m \<longrightarrow> \<langle>f ` m, f ` n\<rangle> \<in> leq"
  apply (unfold preorder_on_def, erule conjE)
  apply (induct_tac m, simp add:refl_def, rename_tac x)
  apply (rule impI)
  apply (case_tac "n\<le>x", simp)
    apply (drule_tac x="x" in bspec, assumption)
   apply (unfold trans_on_def)
   apply (drule_tac x="f`succ(x)" in bspec, simp)
   apply (drule_tac x="f`x" in bspec, simp)
   apply (drule_tac x="f`n" in bspec, auto)
   apply (drule_tac le_succ_iff [THEN iffD1], simp add: refl_def)
  done
lemma not_le_imp_lt: "[| ~ i \<le> j ; Ord(i);  Ord(j) |] ==>  j<i"
  by (simp add:not_le_iff_lt)

lemma decr_seq_linear: "refl(P,leq) \<Longrightarrow> f \<in> nat -> P \<Longrightarrow>
         \<forall>n\<in>nat.  \<langle>f ` succ(n), f ` n\<rangle> \<in> leq \<Longrightarrow>
           trans[P](leq) \<Longrightarrow> linear(f `` nat, leq)"
  apply (unfold linear_def)
  apply (rule ball_image_simp [THEN iffD2], assumption, simp, rule ballI)+
  apply (rename_tac y)
    apply (case_tac "x\<le>y")
   apply (drule_tac leq="leq" and n="x" and m="y" in decr_succ_decr)
    (* probando que es preorder_on ... capaz sacar esto de todos lados *)
       apply (simp add:preorder_on_def)
    (* listo esa prueba *)
      apply (simp+)
  apply (drule not_le_imp_lt [THEN leI], simp_all)
   apply (drule_tac leq="leq" and n="y" and m="x" in decr_succ_decr)
    (* probando que es preorder_on ... capaz sacar esto de todos lados *)
       apply (simp add:preorder_on_def)
    (* listo esa prueba *)
     apply (simp+)
    done

   
lemma ball_distr_conj_iff: "(\<forall>x\<in>A. P(x) \<and> Q(x)) \<longleftrightarrow> (\<forall>x\<in>A. P(x)) \<and> (\<forall>x\<in>A. Q(x))"
 by blast
    
lemma subset_fun_image: "f:N\<rightarrow>P \<Longrightarrow> f``N\<subseteq>P"
  apply (simp add: image_fun)
  apply (rule subsetI, simp, erule bexE)
  apply (simp add:apply_funtype)
  done

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
   apply (drule sequence_DC)      
   apply (drule_tac x="p" in bspec)
 apply (assumption) 

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
    prefer 3 
     (* comienza  prueba del subgoal *)
    apply (insert seq_of_denses)
   
      apply (rule ballI)+
      apply (rename_tac x n)
      apply (drule_tac x="pred(n)" and A="nat" in bspec, simp_all add:dense_def)
      apply (drule_tac x="x" in bspec, assumption)
      apply (erule bexE, rename_tac d)
      apply (rule_tac x="d" in bexI, simp)
      apply (insert countable_subs_of_P)
      apply (subgoal_tac "\<D> ` Arith.pred(n)\<subseteq>P", blast)
      apply (rule  PowD)
    apply (rule_tac f="\<D>" in apply_funtype)
     apply simp+
   apply (rule_tac a="{f`x. x \<in> nat}" 
               and P="\<lambda>x. refl(x,leq)" in ssubst)
    apply (frule_tac C="nat" in image_fun, simp_all)
   apply (insert leq_preord, unfold preorder_on_def, drule conjunct1)
   apply (rule_tac A="{f ` x . x \<in> nat}" 
               and B="P" in refl_monot_domain, auto)
  apply (rule_tac P="P" in decr_seq_linear, assumption)
   apply (drule ball_distr_conj_iff [THEN iffD1], (erule conjE) | assumption)+
  oops

theorem (in countable_generic) rasiowa_sikorski:
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> D_generic(G)"
proof -
  assume 
        0:  "p\<in>P"
  let
            ?S="(\<lambda>m\<in>nat. {<x,y>\<in>P*P. <y,x>\<in>leq \<and> y\<in>\<D>`(pred(m))})"
  have 
            "\<forall>x\<in>P. \<forall>n\<in>nat. \<exists>y\<in>P. <x,y> \<in> ?S`n"
  proof (intro ballI)
    fix x n
    assume 
        1:  "x\<in>P"
            and
        2:  "n\<in>nat"
    then show 
            "\<exists>y\<in>P. <x,y> \<in> ?S`n"
    proof (simp)
      from seq_of_denses and 2 have "dense(\<D> ` pred(n))" by (simp)
      with 1 have
            "\<exists>d\<in>\<D> ` Arith.pred(n). \<langle>d, x\<rangle> \<in> leq"
        unfolding dense_def by (simp)
      then obtain d where
        3:  "d \<in> \<D> ` Arith.pred(n) \<and> \<langle>d, x\<rangle> \<in> leq"
        by (rule bexE, simp)
      from countable_subs_of_P have
            "\<D> ` Arith.pred(n) \<in> Pow(P)"
        using 2 by (blast dest:apply_funtype intro:pred_type) (* (rule apply_funtype [OF _ pred_type]) *)
      then have
            "\<D> ` Arith.pred(n) \<subseteq> P" 
        by (rule PowD)
      then have
            "d \<in> P \<and> \<langle>d, x\<rangle> \<in> leq \<and> d \<in> \<D> ` Arith.pred(n)"
        using 3 by auto
      then show 
            "\<exists>y\<in>P. \<langle>y, x\<rangle> \<in> leq \<and> y \<in> \<D> ` Arith.pred(n)"
        using 1 and 2 by (auto) 
    qed
  qed
  with sequence_DC have
            "\<forall>a\<in>P. (\<exists>f \<in> nat->P. f`0 = a \<and> (\<forall>n \<in> nat. <f`n,f`succ(n)>\<in>?S`succ(n)))"
    by (blast)
  then obtain f where
        8:  "f : nat\<rightarrow>P"
    and
        4:  "f ` 0 = p \<and>
             (\<forall>n\<in>nat.
              f ` n \<in> P \<and> f ` succ(n) \<in> P \<and> \<langle>f ` succ(n), f ` n\<rangle> \<in> leq \<and> 
              f ` succ(n) \<in> \<D> ` n)"
    using 0 by (auto)
  then have   
       7:   "f``nat  \<subseteq> P"
    by (simp add:subset_fun_image)
  with leq_preord have 
       5:   "refl(f``nat, leq) \<and> trans[P](leq)"
    unfolding preorder_on_def  by (blast intro:refl_monot_domain)
  from 4 have
            "\<forall>n\<in>nat.  \<langle>f ` succ(n), f ` n\<rangle> \<in> leq"
    by (simp)
  with 8 and 5 and leq_preord and decr_seq_linear have
       6:   "linear(f``nat, leq)"
    unfolding preorder_on_def by (blast)
  with 5 and chain_compat have 
            "(\<forall>p\<in>f``nat.\<forall>q\<in>f``nat. compat_in(f``nat,leq,p,q))"             
    by (auto)
  then have
     fil:   "filter(upclosure(f``nat))"
   (is "filter(?G)")
    using closure_compat_filter and 7 by simp
  have
    gen:   "\<forall>n\<in>nat. \<D> ` n \<inter> ?G \<noteq> 0"
  proof
    fix n
    assume  
           "n\<in>nat"
    with 8 and 4 have
            "f`succ(n) \<in> ?G \<and> f`succ(n) \<in> \<D> ` n"
      using aux_RS1 by simp
    then show 
       9:   "\<D> ` n \<inter> ?G \<noteq> 0"
      by blast
  qed
  from 4 and 8 have 
            "p \<in> ?G"
    using aux_RS1 by auto
  with gen and fil show ?thesis  
    unfolding D_generic_def by auto
qed
  
    
lemma (in countable_generic) RS_relation:
  assumes
        1:  "x\<in>P"
            and
        2:  "n\<in>nat"
  shows
            "\<exists>y\<in>P. <x,y> \<in> (\<lambda>m\<in>nat. {<x,y>\<in>P*P. <y,x>\<in>leq \<and> y\<in>\<D>`(pred(m))})`n"
proof -
  from seq_of_denses and 2 have "dense(\<D> ` pred(n))" by (simp)
  with 1 have
            "\<exists>d\<in>\<D> ` Arith.pred(n). \<langle>d, x\<rangle> \<in> leq"
    unfolding dense_def by (simp)
  then obtain d where
        3:  "d \<in> \<D> ` Arith.pred(n) \<and> \<langle>d, x\<rangle> \<in> leq"
    by (rule bexE, simp)
  from countable_subs_of_P have
            "\<D> ` Arith.pred(n) \<in> Pow(P)"
    using 2 by (blast dest:apply_funtype intro:pred_type) (* (rule apply_funtype [OF _ pred_type]) *)
  then have
            "\<D> ` Arith.pred(n) \<subseteq> P" 
    by (rule PowD)
  then have
            "d \<in> P \<and> \<langle>d, x\<rangle> \<in> leq \<and> d \<in> \<D> ` Arith.pred(n)"
    using 3 by auto
  then show ?thesis using 1 and 2 by auto
qed
        
theorem (in countable_generic) 
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> D_generic(G)"
proof -
  assume 
        0:  "p\<in>P"
  let
            ?S="(\<lambda>m\<in>nat. {<x,y>\<in>P*P. <y,x>\<in>leq \<and> y\<in>\<D>`(pred(m))})"
  from RS_relation have
            "\<forall>x\<in>P. \<forall>n\<in>nat. \<exists>y\<in>P. <x,y> \<in> ?S`n"
    by (auto)
  with sequence_DC have
            "\<forall>a\<in>P. (\<exists>f \<in> nat->P. f`0 = a \<and> (\<forall>n \<in> nat. <f`n,f`succ(n)>\<in>?S`succ(n)))"
    by (blast)
  then obtain f where
        8:  "f : nat\<rightarrow>P"
    and
        4:  "f ` 0 = p \<and>
             (\<forall>n\<in>nat.
              f ` n \<in> P \<and> f ` succ(n) \<in> P \<and> \<langle>f ` succ(n), f ` n\<rangle> \<in> leq \<and> 
              f ` succ(n) \<in> \<D> ` n)"
    using 0 by (auto)
  then have   
       7:   "f``nat  \<subseteq> P"
    by (simp add:subset_fun_image)
  with leq_preord have 
       5:   "refl(f``nat, leq) \<and> trans[P](leq)"
    unfolding preorder_on_def  by (blast intro:refl_monot_domain)
  from 4 have
            "\<forall>n\<in>nat.  \<langle>f ` succ(n), f ` n\<rangle> \<in> leq"
    by (simp)
  with 8 and 5 and leq_preord and decr_seq_linear have
       6:   "linear(f``nat, leq)"
    unfolding preorder_on_def by (blast)
  with 5 and chain_compat have 
            "(\<forall>p\<in>f``nat.\<forall>q\<in>f``nat. compat_in(f``nat,leq,p,q))"             
    by (auto)
  then have
     fil:   "filter(upclosure(f``nat))"
   (is "filter(?G)")
    using closure_compat_filter and 7 by simp
  have
    gen:   "\<forall>n\<in>nat. \<D> ` n \<inter> ?G \<noteq> 0"
  proof
    fix n
    assume  
           "n\<in>nat"
    with 8 and 4 have
            "f`succ(n) \<in> ?G \<and> f`succ(n) \<in> \<D> ` n"
      using aux_RS1 by simp
    then show 
       9:   "\<D> ` n \<inter> ?G \<noteq> 0"
      by blast
  qed
  from 4 and 8 have 
            "p \<in> ?G"
    using aux_RS1 by auto
  with gen and fil show ?thesis  
    unfolding D_generic_def by auto
qed
  


definition 
  antichain :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "antichain(P,leq,A) == A\<subseteq>P \<and> (\<forall>p\<in>A.\<forall>q\<in>A.(\<not> compat_in(P,leq,p,q)))"

definition 
  ccc :: "i \<Rightarrow> i \<Rightarrow> o" where
  "ccc(P,leq) == \<forall>A. antichain(P,leq,A) \<longrightarrow> |A| \<le> nat"
  
end