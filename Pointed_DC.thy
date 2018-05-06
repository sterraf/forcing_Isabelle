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

lemma aux_seqDC : "\<forall>x\<in>A*nat. \<exists>y\<in>A. <x,<y,succ(snd(x))>> \<in> R \<Longrightarrow>
                  \<forall>x\<in>A*nat. \<exists>y\<in>A*nat. <x,y> \<in> R"
  apply (rule ballI, erule_tac x="x" in ballE, simp_all)
  apply (erule_tac A="A" in bexE, rename_tac y)
  apply (intro bexI, auto)
  done
lemma aux_seqDC2 : "\<forall>x\<in>A*nat. \<exists>y\<in>A. <x,<y,succ(snd(x))>> \<in> R \<Longrightarrow>
                  \<forall>x\<in>A*nat. \<exists>y\<in>A*nat. <x,y> \<in> {<a,b>\<in>R. snd(b) = succ(snd(a))}"
  apply (rule ballI, erule_tac x="x" in ballE, simp_all)
  done

lemma infer_snd : "c\<in> A*B \<Longrightarrow> snd(c) = k \<Longrightarrow> c=<fst(c),k>"
  by auto
    
corollary sequence_DC : 
  "(\<forall>x\<in>A*nat. \<exists>y\<in>A. <x,<y,succ(snd(x))>> \<in> R) \<Longrightarrow>
    \<forall>a\<in>A. (\<exists>f \<in> nat->A. f`0 = a \<and> (\<forall>n \<in> nat. <<f`n,n>,<f`succ(n),succ(n)>>\<in>R))"
  apply (frule aux_seqDC2)
  apply (drule_tac R="{<a,b>\<in>R. snd(b) = succ(snd(a))}" in  pointed_DC)
  apply (rule ballI)
  apply (rotate_tac)
  apply (drule_tac x="<a,0>" in  bspec, simp)
  apply (erule bexE, rename_tac g)  
  apply (rule_tac x="\<lambda>x\<in>nat. fst(g`x)" and A="nat\<rightarrow>A" in bexI, auto)
  apply (subgoal_tac "\<forall>n\<in>nat. g`n= \<langle>fst(g ` n), n\<rangle>")
   prefer 2 apply (rule ballI, rename_tac m)
   apply (induct_tac m, simp)
   apply (rename_tac d, auto)
  apply (frule_tac A="nat" and x="d" in bspec, simp)
  apply (rule_tac A="A" and B="nat" in infer_snd, auto)
  apply (rule_tac a="\<langle>fst(g ` d), d\<rangle>" and b="g ` d" in ssubst, assumption)
    (* Notorio: simp, auto ni blast lo hacen aquí! *)
  apply (subst snd_conv, simp)
  done

end