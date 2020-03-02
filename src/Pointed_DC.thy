section\<open>A pointed version of DC\<close>
theory Pointed_DC imports ZF.AC

begin
txt\<open>This proof of DC is from Moschovakis "Notes on Set Theory"\<close>

consts dc_witness :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
primrec
  wit0   : "dc_witness(0,A,a,s,R) = a"
  witrec :"dc_witness(succ(n),A,a,s,R) = s`{x\<in>A. \<langle>dc_witness(n,A,a,s,R),x\<rangle>\<in>R }"
  
lemma witness_into_A [TC]:  "a\<in>A \<Longrightarrow> n\<in>nat \<Longrightarrow>
                             (\<forall>X . X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X) \<Longrightarrow>
                             \<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0 \<Longrightarrow>
                             dc_witness(n, A, a, s, R)\<in>A"
  apply (induct_tac n ,simp+)
  apply (drule_tac x="dc_witness(x, A, a, s, R)" in bspec, assumption)
  apply (drule_tac x="{xa \<in> A . \<langle>dc_witness(x, A, a, s, R), xa\<rangle> \<in> R}" in  spec)
  apply auto 
  done
lemma witness_related :  "a\<in>A \<Longrightarrow> n\<in>nat \<Longrightarrow>
                             (\<forall>X . X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X) \<Longrightarrow>
                             \<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0 \<Longrightarrow>
                             \<langle>dc_witness(n, A, a, s, R),dc_witness(succ(n), A, a, s, R)\<rangle>\<in>R"
  apply (frule_tac n="n" and s="s"  and R="R" in witness_into_A, assumption+)
   apply (drule_tac x="dc_witness(n, A, a, s, R)" in bspec, assumption)
  apply (drule_tac x= "{x \<in> A . \<langle>dc_witness(n, A, a, s, R), x\<rangle> \<in> R}" in spec)
  apply (simp, blast) 
  done
    
lemma witness_funtype: "a\<in>A \<Longrightarrow> 
                        (\<forall>X . X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X) \<Longrightarrow>
                        \<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0 \<Longrightarrow>
                        (\<lambda>n\<in>nat. dc_witness(n, A, a, s, R)) \<in> nat \<rightarrow> A"
  apply (rule_tac B="{dc_witness(n, A, a, s, R). n\<in>nat}" in fun_weaken_type)
  apply (rule lam_funtype)
  apply ( blast intro:witness_into_A)
  done
    
lemma witness_to_fun: "a\<in>A \<Longrightarrow> (\<forall>X . X\<noteq>0 \<and> X\<subseteq>A \<longrightarrow> s`X\<in>X) \<Longrightarrow>
                             \<forall>y\<in>A. {x\<in>A. \<langle>y,x\<rangle>\<in>R } \<noteq> 0 \<Longrightarrow>
                             \<exists>f \<in> nat\<rightarrow>A. \<forall>n\<in>nat. f`n =dc_witness(n,A,a,s,R)"
  apply (rule_tac x="\<lambda>n\<in>nat. dc_witness(n,A,a,s,R)" in  bexI, simp)
  apply (rule witness_funtype, simp+)
  done

theorem pointed_DC  : "(\<forall>x\<in>A. \<exists>y\<in>A. \<langle>x,y\<rangle>\<in> R) \<Longrightarrow>
                       \<forall>a\<in>A. (\<exists>f \<in> nat\<rightarrow>A. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>f`n,f`succ(n)\<rangle>\<in>R))"
  apply (rule)
  apply (insert AC_func_Pow)
  apply (drule allI)
  apply (drule_tac x="A" in spec)
  apply (drule_tac P="\<lambda>f .\<forall>x\<in>Pow(A) - {0}. f ` x \<in> x"
               and A="Pow(A)-{0}\<rightarrow> A" 
               and Q=" \<exists>f\<in>nat\<rightarrow> A. f ` 0 = a \<and> (\<forall>n\<in>nat. \<langle>f ` n, f ` succ(n)\<rangle> \<in> R)" in bexE)
  prefer 2 apply (assumption)           
  apply (rename_tac s)
  apply (rule_tac x="\<lambda>n\<in>nat. dc_witness(n,A,a,s,R)" in bexI)
   prefer 2  apply (blast intro:witness_funtype)
  apply (rule  conjI, simp)
  apply (rule ballI, rename_tac m)
  apply (subst beta, simp)+
  apply (rule witness_related, auto)
  done

    
lemma aux_DC_on_AxNat2 : "\<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> R \<Longrightarrow>
                  \<forall>x\<in>A\<times>nat. \<exists>y\<in>A\<times>nat. \<langle>x,y\<rangle> \<in> {\<langle>a,b\<rangle>\<in>R. snd(b) = succ(snd(a))}"
  apply (rule ballI, erule_tac x="x" in ballE, simp_all)
  done

lemma infer_snd : "c\<in> A\<times>B \<Longrightarrow> snd(c) = k \<Longrightarrow> c=\<langle>fst(c),k\<rangle>"
  by auto
    
corollary DC_on_A_x_nat : 
  "(\<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> R) \<Longrightarrow>
    \<forall>a\<in>A. (\<exists>f \<in> nat\<rightarrow>A. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>\<langle>f`n,n\<rangle>,\<langle>f`succ(n),succ(n)\<rangle>\<rangle>\<in>R))"
  apply (frule aux_DC_on_AxNat2)
  apply (drule_tac R="{\<langle>a,b\<rangle>\<in>R. snd(b) = succ(snd(a))}" in  pointed_DC)
  apply (rule ballI)
  apply (rotate_tac)
  apply (drule_tac x="\<langle>a,0\<rangle>" in  bspec, simp)
  apply (erule bexE, rename_tac g)  
  apply (rule_tac x="\<lambda>x\<in>nat. fst(g`x)" and A="nat\<rightarrow>A" in bexI, auto)
  apply (subgoal_tac "\<forall>n\<in>nat. g`n= \<langle>fst(g ` n), n\<rangle>")
   prefer 2 apply (rule ballI, rename_tac m)
   apply (induct_tac m, simp)
   apply (rename_tac d, auto)
  apply (frule_tac A="nat" and x="d" in bspec, simp)
  apply (rule_tac A="A" and B="nat" in infer_snd, auto)
  apply (rule_tac a="\<langle>fst(g ` d), d\<rangle>" and b="g ` d" in ssubst, assumption)
    (* Notorio: simp, auto ni blast lo hacen aquí! 
       El problema es que está usando "mal" las assumptions: esta sí sirve
       apply (simp (no_asm)) *)
  apply (subst snd_conv, simp)
  done

lemma aux_sequence_DC : "\<And>R. \<forall>x\<in>A. \<forall>n\<in>nat. \<exists>y\<in>A. \<langle>x,y\<rangle> \<in> S`n \<Longrightarrow>
                        R={\<langle>\<langle>x,n\<rangle>,\<langle>y,m\<rangle>\<rangle>\<in>(A\<times>nat)\<times>(A\<times>nat). \<langle>x,y\<rangle>\<in>S`m } \<Longrightarrow>
                        \<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> R"
  apply (rule ballI, rename_tac v)
  apply (frule Pair_fst_snd_eq)  
  apply (erule_tac x="fst(v)" in ballE)
   apply (drule_tac x="succ(snd(v))" in bspec, auto)
  done

lemma aux_sequence_DC2 : "\<forall>x\<in>A. \<forall>n\<in>nat. \<exists>y\<in>A. \<langle>x,y\<rangle> \<in> S`n \<Longrightarrow>
        \<forall>x\<in>A\<times>nat. \<exists>y\<in>A. \<langle>x,\<langle>y,succ(snd(x))\<rangle>\<rangle> \<in> {\<langle>\<langle>x,n\<rangle>,\<langle>y,m\<rangle>\<rangle>\<in>(A\<times>nat)\<times>(A\<times>nat). \<langle>x,y\<rangle>\<in>S`m }"
  by auto
    
lemma sequence_DC: "\<forall>x\<in>A. \<forall>n\<in>nat. \<exists>y\<in>A. \<langle>x,y\<rangle> \<in> S`n \<Longrightarrow>
    \<forall>a\<in>A. (\<exists>f \<in> nat\<rightarrow>A. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>f`n,f`succ(n)\<rangle>\<in>S`succ(n)))"
  apply (drule aux_sequence_DC2)
  apply (drule DC_on_A_x_nat, auto)
  done
end