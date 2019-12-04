theory Forcing_Notions imports ZF begin

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
    
lemma refl_monot_domain: "refl(B,r) \<Longrightarrow> A\<subseteq>B \<Longrightarrow> refl(A,r)"  
  unfolding refl_def by blast

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
      and one_max:          "\<forall>p\<in>P. <p,one>\<in>leq"
begin

abbreviation Leq :: "[i, i] \<Rightarrow> o"  (infixl "\<preceq>" 50)
  where "x \<preceq> y \<equiv> <x,y>\<in>leq"

lemma refl_leq:
  "r\<in>P \<Longrightarrow> r\<preceq>r"
  using leq_preord unfolding preorder_on_def refl_def by simp

definition 
  dense :: "i\<Rightarrow>o" where
  "dense(D) == \<forall>p\<in>P. \<exists>d\<in>D . d\<preceq>p"

definition 
  dense_below :: "i\<Rightarrow>i\<Rightarrow>o" where
  "dense_below(D,q) == \<forall>p\<in>P. p\<preceq>q \<longrightarrow> (\<exists>d\<in>D. d\<in>P \<and> d\<preceq>p)"

lemma P_dense: "dense(P)"
  by (insert leq_preord, auto simp add: preorder_on_def refl_def dense_def)
    
definition 
  increasing :: "i\<Rightarrow>o" where
  "increasing(F) == \<forall>x\<in>F. \<forall> p \<in> P . x\<preceq>p \<longrightarrow> p\<in>F"

definition 
  compat :: "i\<Rightarrow>i\<Rightarrow>o" where
  "compat(p,q) == compat_in(P,leq,p,q)"

definition 
  antichain :: "i\<Rightarrow>o" where
  "antichain(A) == A\<subseteq>P \<and> (\<forall>p\<in>A.\<forall>q\<in>A.(\<not>compat(p,q)))"

definition 
  filter :: "i\<Rightarrow>o" where
  "filter(G) == G\<subseteq>P \<and> increasing(G) \<and> (\<forall>p\<in>G. \<forall>q\<in>G. compat_in(G,leq,p,q))"

lemma filterD : "filter(G) \<Longrightarrow> x \<in> G \<Longrightarrow> x \<in> P"
  by (auto simp add : subsetD filter_def)

lemma filter_leqD : "filter(G) \<Longrightarrow> x \<in> G \<Longrightarrow> y \<in> P \<Longrightarrow> x\<preceq>y \<Longrightarrow> y \<in> G"
  by (simp add: filter_def increasing_def)
    
lemma low_bound_filter : 
  assumes "filter(G)" and "p\<in>G" and "q\<in>G"
  shows "\<exists>r\<in>G. r\<preceq>p \<and> r\<preceq>q" 
  using assms 
  unfolding compat_in_def filter_def by blast
  
definition  
  upclosure :: "i\<Rightarrow>i" where
  "upclosure(A) == {p\<in>P.\<exists>a\<in>A. a\<preceq>p}"
  
lemma  upclosureI [intro] : "p\<in>P \<Longrightarrow> a\<in>A \<Longrightarrow> a\<preceq>p \<Longrightarrow> p\<in>upclosure(A)"
  by (simp add:upclosure_def, auto)

lemma  upclosureE [elim] :
  "p\<in>upclosure(A) \<Longrightarrow> (\<And>x a. x\<in>P \<Longrightarrow> a\<in>A \<Longrightarrow> a\<preceq>x \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp add:upclosure_def)

lemma  upclosureD [dest] :
   "p\<in>upclosure(A) \<Longrightarrow> \<exists>a\<in>A.(a\<preceq>p) \<and> p\<in>P"
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

lemma decr_seq_linear: "refl(P,leq) \<Longrightarrow> f \<in> nat \<rightarrow> P \<Longrightarrow>
         \<forall>n\<in>nat.  \<langle>f ` succ(n), f ` n\<rangle> \<in> leq \<Longrightarrow>
           trans[P](leq) \<Longrightarrow> linear(f `` nat, leq)"
  apply (unfold linear_def)
  apply (rule ball_image_simp [THEN iffD2], assumption, simp, rule ballI)+
  apply (rename_tac y)
    apply (case_tac "x\<le>y")
   apply (drule_tac n="x" and m="y" in decr_succ_decr)
    (* probando que es preorder_on ... capaz sacar esto de todos lados *)
       apply (simp add:preorder_on_def)
    (* listo esa prueba *)
      apply (simp+) 
  apply (drule not_le_iff_lt[THEN iffD1, THEN leI, rotated 2], simp_all)
   apply (drule_tac n="y" and m="x" in decr_succ_decr)
    (* probando que es preorder_on ... capaz sacar esto de todos lados *)
       apply (simp add:preorder_on_def)
    (* listo esa prueba *)
     apply (simp+)
  done

end (* forcing_notion *)

locale countable_generic = forcing_notion +
  fixes \<D>
  assumes countable_subs_of_P:  "\<D> \<in> nat\<rightarrow>Pow(P)"
  and     seq_of_denses:        "\<forall>n \<in> nat. dense(\<D>`n)"

begin
  
definition
  D_generic :: "i\<Rightarrow>o" where
  "D_generic(G) == filter(G) \<and> (\<forall>n\<in>nat.(\<D>`n)\<inter>G\<noteq>0)"

lemma RS_sequence_imp_rasiowa_sikorski:
  assumes 
    "p\<in>P" "f : nat\<rightarrow>P" "f ` 0 = p"
    "\<And>n. n\<in>nat \<Longrightarrow> f ` succ(n)\<preceq> f ` n \<and> f ` succ(n) \<in> \<D> ` n" 
  shows
    "\<exists>G. p\<in>G \<and> D_generic(G)"
proof -
  note assms
  moreover from this 
  have "f``nat  \<subseteq> P"
    by (simp add:subset_fun_image)
  moreover from calculation
  have "refl(f``nat, leq) \<and> trans[P](leq)"
    using leq_preord unfolding preorder_on_def by (blast intro:refl_monot_domain)
  moreover from calculation 
  have "\<forall>n\<in>nat.  f ` succ(n)\<preceq> f ` n" by (simp)
  moreover from calculation
  have "linear(f``nat, leq)"
    using leq_preord and decr_seq_linear unfolding preorder_on_def by (blast)
  moreover from calculation
  have "(\<forall>p\<in>f``nat.\<forall>q\<in>f``nat. compat_in(f``nat,leq,p,q))"             
    using chain_compat by (auto)
  ultimately  
  have "filter(upclosure(f``nat))" (is "filter(?G)")
    using closure_compat_filter by simp
  moreover
  have "\<forall>n\<in>nat. \<D> ` n \<inter> ?G \<noteq> 0"
  proof
    fix n
    assume "n\<in>nat"
    with assms 
    have "f`succ(n) \<in> ?G \<and> f`succ(n) \<in> \<D> ` n"
      using aux_RS1 by simp
    then 
    show "\<D> ` n \<inter> ?G \<noteq> 0"  by blast
  qed
  moreover from assms 
  have "p \<in> ?G"
    using aux_RS1 by auto
  ultimately 
  show ?thesis unfolding D_generic_def by auto
qed
  
end (* countable_generic *)

consts RS_seq :: "[i,i,i,i,i,i] \<Rightarrow> i"
primrec
  "RS_seq(0,P,leq,p,enum,\<D>) = p"
  "RS_seq(succ(n),P,leq,p,enum,\<D>) = 
    enum`(\<mu> m. \<langle>enum`m, RS_seq(n,P,leq,p,enum,\<D>)\<rangle> \<in> leq \<and> enum`m \<in> \<D> ` n)"

context countable_generic
begin

lemma preimage_rangeD:
  assumes "f\<in>Pi(A,B)" "b \<in> range(f)" 
  shows "\<exists>a\<in>A. f`a = b"
  using assms apply_equality[OF _ assms(1), of _ b] domain_type[OF _ assms(1)] by auto

lemma countable_RS_sequence_aux:
  fixes p enum
  defines "f(n) \<equiv> RS_seq(n,P,leq,p,enum,\<D>)"
    and   "Q(q,k,m) \<equiv> enum`m\<preceq> q \<and> enum`m \<in> \<D> ` k"
  assumes "n\<in>nat" "p\<in>P" "P \<subseteq> range(enum)" "enum:nat\<rightarrow>M"
    "\<And>x k. x\<in>P \<Longrightarrow> k\<in>nat \<Longrightarrow>  \<exists>q\<in>P. q\<preceq> x \<and> q \<in> \<D> ` k" 
  shows 
    "f(succ(n)) \<in> P \<and> f(succ(n))\<preceq> f(n) \<and> f(succ(n)) \<in> \<D> ` n"
  using \<open>n\<in>nat\<close>
proof (induct)
  case 0
  from assms 
  obtain q where "q\<in>P" "q\<preceq> p" "q \<in> \<D> ` 0" by blast
  moreover from this and \<open>P \<subseteq> range(enum)\<close>
  obtain m where "m\<in>nat" "enum`m = q" 
    using preimage_rangeD[OF \<open>enum:nat\<rightarrow>M\<close>] by blast
  moreover 
  have "\<D>`0 \<subseteq> P"
    using apply_funtype[OF countable_subs_of_P] by simp
  moreover note \<open>p\<in>P\<close>
  ultimately
  show ?case 
    using LeastI[of "Q(p,0)" m] unfolding Q_def f_def by auto
next
  case (succ n)
  with assms 
  obtain q where "q\<in>P" "q\<preceq> f(succ(n))" "q \<in> \<D> ` succ(n)" by blast
  moreover from this and \<open>P \<subseteq> range(enum)\<close>
  obtain m where "m\<in>nat" "enum`m\<preceq> f(succ(n))" "enum`m \<in> \<D> ` succ(n)"
    using preimage_rangeD[OF \<open>enum:nat\<rightarrow>M\<close>] by blast
  moreover note succ
  moreover from calculation
  have "\<D>`succ(n) \<subseteq> P" 
    using apply_funtype[OF countable_subs_of_P] by auto
  ultimately
  show ?case
    using LeastI[of "Q(f(succ(n)),succ(n))" m] unfolding Q_def f_def by auto
qed

lemma countable_RS_sequence:
  fixes p enum
  defines "f \<equiv> \<lambda>n\<in>nat. RS_seq(n,P,leq,p,enum,\<D>)"
    and   "Q(q,k,m) \<equiv> enum`m\<preceq> q \<and> enum`m \<in> \<D> ` k"
  assumes "n\<in>nat" "p\<in>P" "P \<subseteq> range(enum)" "enum:nat\<rightarrow>M"
  shows 
    "f`0 = p" "f`succ(n)\<preceq> f`n \<and> f`succ(n) \<in> \<D> ` n" "f`succ(n) \<in> P"
proof -
  from assms
  show "f`0 = p" by simp
  {
    fix x k
    assume "x\<in>P" "k\<in>nat"
    then
    have "\<exists>q\<in>P. q\<preceq> x \<and> q \<in> \<D> ` k"
      using seq_of_denses apply_funtype[OF countable_subs_of_P] 
      unfolding dense_def by blast
  }
  with assms
  show "f`succ(n)\<preceq> f`n \<and> f`succ(n) \<in> \<D> ` n" "f`succ(n)\<in>P"
    unfolding f_def using countable_RS_sequence_aux by simp_all
qed

lemma RS_seq_type: 
  assumes "n \<in> nat" "p\<in>P" "P \<subseteq> range(enum)" "enum:nat\<rightarrow>M"
  shows "RS_seq(n,P,leq,p,enum,\<D>) \<in> P"
  using assms countable_RS_sequence(1,3)  
  by (induct;simp) 

lemma RS_seq_funtype:
  assumes "p\<in>P" "P \<subseteq> range(enum)" "enum:nat\<rightarrow>M"
  shows "(\<lambda>n\<in>nat. RS_seq(n,P,leq,p,enum,\<D>)): nat \<rightarrow> P"
  using assms lam_type RS_seq_type by auto

lemmas countable_rasiowa_sikorski = 
  RS_sequence_imp_rasiowa_sikorski[OF _ RS_seq_funtype countable_RS_sequence(1,2)]
end (* countable_generic *)

end
