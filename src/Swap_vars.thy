theory Swap_vars imports Formula begin

definition
  swap_var :: "[i , i] \<Rightarrow> i" where
  "swap_var(i,n) == if i=n then succ(i) else (if i=succ(n) then n else i)"

lemma swap_var_type [TC] : 
  "\<lbrakk> i \<in> nat ; n \<in> nat \<rbrakk> \<Longrightarrow> swap_var(i,n) \<in> nat"
  by (simp add:swap_var_def)

consts swap_suc :: "i\<Rightarrow>i" 
primrec
  "swap_suc(Member(x,y)) =
    (\<lambda> n \<in> nat . Member(swap_var(x,n),swap_var(y,n)))"
  "swap_suc(Equal(x,y)) = 
    (\<lambda> n \<in> nat . Equal(swap_var(x,n),swap_var(y,n)))"
  "swap_suc(Nand(p,q)) =
    (\<lambda> n \<in> nat . Nand(swap_suc(p)`n,swap_suc(q)`n))"
  "swap_suc(Forall(p)) =
    (\<lambda> n \<in> nat . Forall(swap_suc(p)`(succ(n))))"

lemma swap_suc_type [TC] : 
  "\<lbrakk> \<phi> \<in> formula  \<rbrakk> \<Longrightarrow> swap_suc(\<phi>) \<in> nat \<rightarrow> formula"
  by (induct_tac \<phi>,simp_all)

lemma sats_swap_suc : 
  "\<lbrakk> \<phi> \<in> formula ; n \<in> nat ; env \<in> list(M) ; env' \<in> list(M) ; n = length(env) \<rbrakk> \<Longrightarrow> 
    sats(M,\<phi>,env@[a,b]@env') \<longleftrightarrow> sats(M,swap_suc(\<phi>)`n,env@[b,a]@env')"
  sorry

definition
  swap_0_1 :: "i \<Rightarrow> i" where
  "swap_0_1(\<phi>) == swap_suc(\<phi>)`0"

lemma [TC] : "\<phi> \<in> formula \<Longrightarrow> swap_0_1(\<phi>) \<in> formula"
  by (simp add: swap_0_1_def)
  

lemma sats_swap_0_1 :
  "\<lbrakk> \<phi> \<in> formula ; env \<in> list(M) ; a \<in> M ; b \<in> M\<rbrakk> \<Longrightarrow>
  sats(M,swap_0_1(\<phi>),Cons(a,Cons(b,env))) \<longleftrightarrow> 
  sats(M,\<phi>,Cons(b,Cons(a,env)))"
  sorry

end