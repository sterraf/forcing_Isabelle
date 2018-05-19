theory forcing_posets imports Pointed_DC  begin

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

lemma subset_fun_image: "f:N\<rightarrow>P \<Longrightarrow> f``N\<subseteq>P"
  apply (simp add: image_fun)
  apply (rule subsetI, simp, erule bexE)
  apply (simp add:apply_funtype)
  done
    
definition 
  antichain :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "antichain(P,leq,A) == A\<subseteq>P \<and> (\<forall>p\<in>A.\<forall>q\<in>A.(\<not> compat_in(P,leq,p,q)))"

definition 
  ccc :: "i \<Rightarrow> i \<Rightarrow> o" where
  "ccc(P,leq) == \<forall>A. antichain(P,leq,A) \<longrightarrow> |A| \<le> nat"

locale forcing_poset =
  fixes P leq uno
  assumes uno_in_P:         "uno \<in> P"
      and leq_preord:       "preorder_on(P,leq)"
      and uno_max:          "\<forall>p\<in>P. <p,uno>\<in>leq"
begin
definition 
  dense :: "i\<Rightarrow>o" where
  "dense(D) == \<forall>p\<in>P. \<exists>d\<in>D . <d,p>\<in>leq"
    
definition 
  increasing :: "i\<Rightarrow>o" where
  "increasing(F) == \<forall>p\<in>P. \<forall>x\<in>P. x\<in>F \<and> <x,p>\<in>leq \<longrightarrow> p\<in>F"


definition 
  compat :: "i\<Rightarrow>i\<Rightarrow>o" where
  "compat(p,q) == compat_in(P,leq,p,q)"

definition 
  antichain :: "i\<Rightarrow>o" where
  "antichain(A) == A\<subseteq>P \<and> (\<forall>p\<in>A.\<forall>q\<in>A.(\<not>compat(p,q)))"

definition 
  filter :: "i\<Rightarrow>o" where
  "filter(G) == G\<subseteq>P \<and> increasing(G) \<and> (\<forall>p\<in>G. \<forall>q\<in>G. compat_in(G,leq,p,q))"

definition  
  upclosure :: "i\<Rightarrow>i" where
  "upclosure(A) == {p\<in>P.\<exists>a\<in>A.<a,p>\<in>leq}"
  
lemma  upclosureI [intro] : "p\<in>P \<Longrightarrow> a\<in>A \<Longrightarrow> <a,p>\<in>leq \<Longrightarrow> p\<in>upclosure(A)"
  by (simp add:upclosure_def, auto)

lemma  upclosureE [elim] :
  "p\<in>upclosure(A) \<Longrightarrow> (\<And>x a. x\<in>P \<Longrightarrow> a\<in>A \<Longrightarrow> <a,x>\<in>leq \<Longrightarrow> R) \<Longrightarrow> R"
  apply (simp add:upclosure_def)
  apply (erule conjE)
  apply (drule_tac P="\<lambda>a.\<langle>a, p\<rangle> \<in> leq" 
               and Q="R" in bexE, assumption+)
done

lemma  upclosureD [dest] :
   "p\<in>upclosure(A) \<Longrightarrow> \<exists>a\<in>A.(<a,p>\<in>leq) \<and> p\<in>P"
  by (simp add:upclosure_def)
   
lemma   upclosure_increasing :
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
  
lemma  upclosure_in_P: "A \<subseteq> P \<Longrightarrow> upclosure(A) \<subseteq> P"
  apply (rule   subsetI)
  apply (simp add:upclosure_def)  
  done

lemma  A_sub_upclosure: "A \<subseteq> P \<Longrightarrow> A\<subseteq>upclosure(A)"
  apply (rule   subsetI)
  apply (simp add:upclosure_def, auto)
  apply (insert leq_preord, unfold preorder_on_def refl_def, auto)
  done
 
lemma  elem_upclosure: "A\<subseteq>P \<Longrightarrow> x\<in>A  \<Longrightarrow> x\<in>upclosure(A)"
  by (blast dest:A_sub_upclosure)
    
lemma  closure_compat_filter:
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
    
lemma  aux_RS1:  "f \<in> N \<rightarrow> P \<Longrightarrow> n\<in>N \<Longrightarrow> f`n \<in> upclosure(f ``N)"
  apply (rule_tac  elem_upclosure)
   apply (rule subset_fun_image, assumption)
  apply (simp add: image_fun, blast)
  done    
end
  
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
        
theorem (in countable_generic) rasiowa_sikorski:
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> D_generic(G)"
proof -
  assume 
      Eq1:  "p\<in>P"
  let
            ?S="(\<lambda>m\<in>nat. {<x,y>\<in>P*P. <y,x>\<in>leq \<and> y\<in>\<D>`(pred(m))})"
  from RS_relation have
            "\<forall>x\<in>P. \<forall>n\<in>nat. \<exists>y\<in>P. <x,y> \<in> ?S`n"
    by (auto)
  with sequence_DC have
            "\<forall>a\<in>P. (\<exists>f \<in> nat->P. f`0 = a \<and> (\<forall>n \<in> nat. <f`n,f`succ(n)>\<in>?S`succ(n)))"
    by (blast)
  then obtain f where
      Eq2:  "f : nat\<rightarrow>P"
    and
      Eq3:  "f ` 0 = p \<and>
             (\<forall>n\<in>nat.
              f ` n \<in> P \<and> f ` succ(n) \<in> P \<and> \<langle>f ` succ(n), f ` n\<rangle> \<in> leq \<and> 
              f ` succ(n) \<in> \<D> ` n)"
    using Eq1 by (auto)
  then have   
      Eq4:  "f``nat  \<subseteq> P"
    by (simp add:subset_fun_image)
  with leq_preord have 
      Eq5:  "refl(f``nat, leq) \<and> trans[P](leq)"
    unfolding preorder_on_def  by (blast intro:refl_monot_domain)
  from Eq3 have
            "\<forall>n\<in>nat.  \<langle>f ` succ(n), f ` n\<rangle> \<in> leq"
    by (simp)
  with Eq2 and Eq5 and leq_preord and decr_seq_linear have
      Eq6:  "linear(f``nat, leq)"
    unfolding preorder_on_def by (blast)
  with Eq5 and chain_compat have 
            "(\<forall>p\<in>f``nat.\<forall>q\<in>f``nat. compat_in(f``nat,leq,p,q))"             
    by (auto)
  then have
      fil:  "filter(upclosure(f``nat))"
   (is "filter(?G)")
    using closure_compat_filter and Eq4 by simp
  have
      gen:  "\<forall>n\<in>nat. \<D> ` n \<inter> ?G \<noteq> 0"
  proof
    fix n
    assume  
            "n\<in>nat"
    with Eq2 and Eq3 have
            "f`succ(n) \<in> ?G \<and> f`succ(n) \<in> \<D> ` n"
      using aux_RS1 by simp
    then show 
            "\<D> ` n \<inter> ?G \<noteq> 0"
      by blast
  qed
  from Eq3 and Eq2 have 
            "p \<in> ?G"
    using aux_RS1 by auto
  with gen and fil show ?thesis  
    unfolding D_generic_def by auto
qed

  
end