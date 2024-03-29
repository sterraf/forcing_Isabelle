(*
----------------------------------------------
First steps towards a formalization of Forcing
---------------------------------------------

Definition of forcing notions: preorders with top,
dense subsets, generic filters. Proof of the
Rasiowa-Sikorski theorem.
*)
theory Forcing_notions imports Pointed_DC  begin

definition compat_in :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "compat_in(A,r,p,q) == \<exists>d\<in>A . \<langle>d,p\<rangle>\<in>r \<and> \<langle>d,q\<rangle>\<in>r"

lemma compat_inI : 
  "\<lbrakk> d\<in>A ; \<langle>d,p\<rangle>\<in>r ; \<langle>d,g\<rangle>\<in>r \<rbrakk> \<Longrightarrow> compat_in(A,r,p,g)"
  by (auto simp add: compat_in_def)

lemma refl_compat:
  "\<lbrakk> refl(A,r) ; \<langle>p,q\<rangle> \<in> r | p=q | \<langle>q,p\<rangle> \<in> r ; p\<in>A ; q\<in>A\<rbrakk> \<Longrightarrow> compat_in(A,r,p,q)"
  by (auto simp add: refl_def compat_inI)
 
lemma  chain_compat:
  "refl(A,r) \<Longrightarrow> linear(A,r) \<Longrightarrow>  (\<forall>p\<in>A.\<forall>q\<in>A. compat_in(A,r,p,q))"
  by (simp add: refl_compat linear_def)

lemma subset_fun_image: "f:N\<rightarrow>P \<Longrightarrow> f``N\<subseteq>P"
  by (auto simp add: image_fun apply_funtype)
    
definition 
  antichain :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "antichain(P,leq,A) == A\<subseteq>P \<and> (\<forall>p\<in>A.\<forall>q\<in>A.(\<not> compat_in(P,leq,p,q)))"

definition 
  ccc :: "i \<Rightarrow> i \<Rightarrow> o" where
  "ccc(P,leq) == \<forall>A. antichain(P,leq,A) \<longrightarrow> |A| \<le> nat"

locale forcing_notion =
  fixes P leq one
  assumes one_in_P:         "one \<in> P"
      and leq_preord:       "preorder_on(P,leq)"
      and one_max:          "\<forall>p\<in>P. \<langle>p,one\<rangle>\<in>leq"
begin
definition 
  dense :: "i\<Rightarrow>o" where
  "dense(D) == \<forall>p\<in>P. \<exists>d\<in>D . \<langle>d,p\<rangle>\<in>leq"

definition 
  dense_below :: "i\<Rightarrow>i\<Rightarrow>o" where
  "dense_below(D,q) == \<forall>p\<in>P. \<langle>p,q\<rangle>\<in>leq \<longrightarrow> (\<exists>d\<in>D . \<langle>d,p\<rangle>\<in>leq)"

lemma P_dense: "dense(P)"
  using leq_preord
  unfolding preorder_on_def refl_def dense_def
  by blast  
    
definition 
  increasing :: "i\<Rightarrow>o" where
  "increasing(F) == \<forall>x\<in>F. \<forall> p \<in> P . \<langle>x,p\<rangle>\<in>leq \<longrightarrow> p\<in>F"


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
  "upclosure(A) == {p\<in>P.\<exists>a\<in>A.\<langle>a,p\<rangle>\<in>leq}"
  
lemma  upclosureI [intro] : "p\<in>P \<Longrightarrow> a\<in>A \<Longrightarrow> \<langle>a,p\<rangle>\<in>leq \<Longrightarrow> p\<in>upclosure(A)"
  by (simp add:upclosure_def, auto)

lemma  upclosureE [elim] :
  "p\<in>upclosure(A) \<Longrightarrow> (\<And>x a. x\<in>P \<Longrightarrow> a\<in>A \<Longrightarrow> \<langle>a,x\<rangle>\<in>leq \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp add:upclosure_def)

lemma  upclosureD [dest] :
   "p\<in>upclosure(A) \<Longrightarrow> \<exists>a\<in>A.(\<langle>a,p\<rangle>\<in>leq) \<and> p\<in>P"
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
  apply (drule_tac A="A" and x="a" in bspec, assumption)
  apply (drule_tac A="A" and x="b" in bspec, assumption)
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

lemma refl_monot_domain: "refl(B,r) \<Longrightarrow> A\<subseteq>B \<Longrightarrow> refl(A,r)"  
  apply (drule subset_iff [THEN iffD1])
  apply (unfold refl_def) 
  apply (blast)
  done

lemma decr_succ_decr: "f \<in> nat \<rightarrow> P \<Longrightarrow> preorder_on(P,leq) \<Longrightarrow>
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
lemma not_le_imp_lt: "\<lbrakk> ~ i \<le> j ; Ord(i);  Ord(j) \<rbrakk> \<Longrightarrow>  j<i"
  by (simp add:not_le_iff_lt)

lemma decr_seq_linear: "refl(P,leq) \<Longrightarrow> f \<in> nat \<rightarrow> P \<Longrightarrow>
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

  
locale countable_generic = forcing_notion +
  fixes \<D>
  assumes countable_subs_of_P:  "\<D> \<in> nat\<rightarrow>Pow(P)"
  and     seq_of_denses:        "\<forall>n \<in> nat. dense(\<D>`n)"

begin
  
definition
  D_generic :: "i\<Rightarrow>o" where
  "D_generic(G) == filter(G) \<and> (\<forall>n\<in>nat.(\<D>`n)\<inter>G\<noteq>0)"



lemma RS_relation:
  assumes
        1:  "x\<in>P"
            and
        2:  "n\<in>nat"
  shows
            "\<exists>y\<in>P. \<langle>x,y\<rangle> \<in> (\<lambda>m\<in>nat. {\<langle>x,y\<rangle>\<in>P*P. \<langle>y,x\<rangle>\<in>leq \<and> y\<in>\<D>`(pred(m))})`n"
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
        
theorem rasiowa_sikorski:
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> D_generic(G)"
proof -
  assume 
      Eq1:  "p\<in>P"
  let
            ?S="(\<lambda>m\<in>nat. {\<langle>x,y\<rangle>\<in>P*P. \<langle>y,x\<rangle>\<in>leq \<and> y\<in>\<D>`(pred(m))})"
  from RS_relation have
            "\<forall>x\<in>P. \<forall>n\<in>nat. \<exists>y\<in>P. \<langle>x,y\<rangle> \<in> ?S`n"
    by (auto)
  with sequence_DC have
            "\<forall>a\<in>P. (\<exists>f \<in> nat\<rightarrow>P. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>f`n,f`succ(n)\<rangle>\<in>?S`succ(n)))"
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
  
end