theory Swap_vars imports Formula begin

definition
  swap_var :: "[i , i] \<Rightarrow> i" where
  "swap_var(i,n) == if i=n then succ(i) else (if i=succ(n) then n else i)"

lemma swap_var_type [TC] : 
  "\<lbrakk> i \<in> nat ; n \<in> nat \<rbrakk> \<Longrightarrow> swap_var(i,n) \<in> nat"
  by (simp add:swap_var_def)

lemma swap_var_eq : "\<lbrakk> i\<in>nat ; n\<in>nat ; i=n \<rbrakk> \<Longrightarrow> swap_var(i,n) = succ(i)"
  by (simp add: swap_var_def)

lemma swap_var_eq_succ : "\<lbrakk> i\<in>nat ; n\<in>nat ; i=succ(n) \<rbrakk> \<Longrightarrow> swap_var(i,n) = n"
  by (simp add: swap_var_def)

lemma swap_var_neq : "\<lbrakk> i\<in>nat ; n\<in>nat ; i\<noteq>n \<and> i\<noteq>succ(n) \<rbrakk> \<Longrightarrow> swap_var(i,n) = i"
  by (simp add: swap_var_def)
  

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

lemma nth_length_append : 
  "\<lbrakk> x \<in> A ; l \<in> list(A) ; l' \<in> list(A) \<rbrakk> \<Longrightarrow> nth(length(l),l@Cons(x,l')) = x"
  by (induct_tac l,simp_all)

lemma nth_succ_length_append :
  "\<lbrakk> x \<in> A ; l \<in> list(A) ; l' \<in> list(A) \<rbrakk> \<Longrightarrow> nth(succ(length(l)),l@Cons(x,Cons(y,l'))) = y"
  by (induct_tac l,simp_all)


lemma nth_great_length_append : 
  "\<lbrakk> x \<in> A ; y \<in> A ; l \<in> list(A) ; l' \<in> list(A) ; 
     n \<in> nat\<rbrakk> \<Longrightarrow> n \<noteq> length(l) \<and>  n \<noteq> succ(length(l)) \<longrightarrow>
      nth(n,l@Cons(x,Cons(y,l'))) = nth(n,l@Cons(y,Cons(x,l')))"
  apply (simp add: nth_append)
  sorry
  

lemma sats_swap_suc [rule_format] : 
  "\<lbrakk> \<phi> \<in> formula ; a\<in>M ; b\<in>M ; env' \<in> list(M)\<rbrakk> \<Longrightarrow> \<forall>env\<in>list(M).
   sats(M,swap_suc(\<phi>)`(length(env)),env@[b,a]@env') \<longleftrightarrow> sats(M,\<phi>,env@[a,b]@env')"
  apply (induct_tac \<phi>)
  apply (simp_all add: swap_var_def length_type nth_length_append 
                       nth_succ_length_append nth_great_length_append)
  apply auto
  done
  
definition
  swap_0_1 :: "i \<Rightarrow> i" where
  "swap_0_1(\<phi>) == swap_suc(\<phi>)`0"

lemma [TC] : "\<phi> \<in> formula \<Longrightarrow> swap_0_1(\<phi>) \<in> formula"
  by (simp add: swap_0_1_def)
  
lemma sats_swap_0_1 :
  "\<lbrakk> \<phi> \<in> formula ; env \<in> list(M) ; a \<in> M ; b \<in> M\<rbrakk> \<Longrightarrow>
  sats(M,swap_0_1(\<phi>),Cons(a,Cons(b,env))) \<longleftrightarrow> 
  sats(M,\<phi>,Cons(b,Cons(a,env)))"
  apply (insert sats_swap_suc [of \<phi> b M a env "[]"])
  apply (simp add: swap_0_1_def)
  done

end