theory Pointed_DC imports AC

begin
txt\<open>This proof of DC is from Moschovakis "Notes on Set Theory"\<close>

consts dc_witness :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
primrec
  wit0   : "dc_witness(0,A,a,s,R) = a"
  witrec :"dc_witness(succ(n),A,a,s,R) = s`{x\<in>A. <dc_witness(n,A,a,s,R),x>\<in>R }"
  
lemma witness_into_A [TC]:  "a\<in>A \<Longrightarrow> n\<in>nat \<Longrightarrow>
                             (\<forall>X . X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X) \<Longrightarrow>
                             \<forall>y\<in>A. {x\<in>A. <y,x>\<in>R } \<noteq> 0 \<Longrightarrow>
                             dc_witness(n, A, a, s, R)\<in>A"
  apply (induct_tac n ,simp+)
  apply (drule_tac x="dc_witness(x, A, a, s, R)" in bspec, assumption)
  apply (drule_tac x="{xa \<in> A . \<langle>dc_witness(x, A, a, s, R), xa\<rangle> \<in> R}" in  spec)
  apply auto 
  done
lemma witness_related :  "a\<in>A \<Longrightarrow> n\<in>nat \<Longrightarrow>
                             (\<forall>X . X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X) \<Longrightarrow>
                             \<forall>y\<in>A. {x\<in>A. <y,x>\<in>R } \<noteq> 0 \<Longrightarrow>
                             <dc_witness(n, A, a, s, R),dc_witness(succ(n), A, a, s, R)>\<in>R"
  apply (frule_tac n="n" and s="s"  and R="R" in witness_into_A, assumption+)
   apply (drule_tac x="dc_witness(n, A, a, s, R)" in bspec, assumption)
  apply (drule_tac x= "{x \<in> A . \<langle>dc_witness(n, A, a, s, R), x\<rangle> \<in> R}" in spec)
  apply (simp, blast) 
  done
    
lemma witness_funtype: "a\<in>A \<Longrightarrow> 
                        (\<forall>X . X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X) \<Longrightarrow>
                        \<forall>y\<in>A. {x\<in>A. <y,x>\<in>R } \<noteq> 0 \<Longrightarrow>
                        (\<lambda>n\<in>nat. dc_witness(n, A, a, s, R)) \<in> nat -> A"
  apply (rule_tac B="{dc_witness(n, A, a, s, R). n\<in>nat}" in fun_weaken_type)
  apply (rule lam_funtype)
  apply ( blast intro:witness_into_A)
  done
    
lemma witness_to_fun: "a\<in>A \<Longrightarrow> (\<forall>X . X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X) \<Longrightarrow>
                             \<forall>y\<in>A. {x\<in>A. <y,x>\<in>R } \<noteq> 0 \<Longrightarrow>
                             \<exists>f \<in> nat->A. \<forall>n\<in>nat. f`n =dc_witness(n,A,a,s,R)"
  apply (rule_tac x="\<lambda>n\<in>nat. dc_witness(n,A,a,s,R)" in  bexI, simp)
  apply (rule witness_funtype, simp+)
  done

theorem pointed_DC  : "(\<forall>x\<in>A. \<exists>y\<in>A. <x,y>\<in> R) \<Longrightarrow>
                       \<forall>a\<in>A. (\<exists>f \<in> nat->A. f`0 = a \<and> (\<forall>n \<in> nat. <f`n,f`succ(n)>\<in>R))"
  apply (rule)
  apply (insert AC_func_Pow)
  apply (drule allI)
  apply (rotate_tac 2)
  apply (drule_tac x="A" in spec)
  apply (drule_tac P="\<lambda>f .\<forall>x\<in>Pow(A) - {0}. f ` x \<in> x"
               and A="Pow(A)-{0}\<rightarrow> A" 
               and Q=" \<exists>f\<in>nat -> A. f ` 0 = a \<and> (\<forall>n\<in>nat. \<langle>f ` n, f ` succ(n)\<rangle> \<in> R)" in bexE)
  prefer 2 apply (assumption)           
  apply (rename_tac s)
  apply (rule_tac x="\<lambda>n\<in>nat. dc_witness(n,A,a,s,R)" in bexI)
   prefer 2  apply (blast intro:witness_funtype)
  apply (rule  conjI, simp)
  apply (rule ballI, rename_tac m)
  apply (subst beta, simp)+
  apply (rule witness_related, simp+, blast)
  done
    
end