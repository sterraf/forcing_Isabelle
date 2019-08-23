theory Forces_Definition imports Interface Names begin
(* 1min 8 secs processing time *)

definition
  ftype :: "i\<Rightarrow>i" where
  "ftype == fst"

definition
  name1 :: "i\<Rightarrow>i" where
  "name1(x) == fst(snd(x))"

definition
  name2 :: "i\<Rightarrow>i" where
  "name2(x) == fst(snd(snd(x)))"

definition
   cond_of :: "i\<Rightarrow>i" where
  "cond_of(x) == snd(snd(snd((x))))"

lemma components_simp [simp]:
  "ftype(<f,n1,n2,c>) = f"
  "name1(<f,n1,n2,c>) = n1"
  "name2(<f,n1,n2,c>) = n2"
  "cond_of(<f,n1,n2,c>) = c"
  unfolding ftype_def name1_def name2_def cond_of_def
  by simp_all

(* p ||- \<tau> = \<theta> \<equiv>
  \<forall>\<sigma>. \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<longrightarrow> (\<forall>q. <q,p>\<in>leq \<longrightarrow> (q ||- \<sigma>\<in>\<tau>) = (q ||- \<sigma>\<in>\<theta>) ) *)
definition
  eq_case :: "[i,i,i,i,i,i] \<Rightarrow> o" where
  "eq_case(t1,t2,p,P,leq,f) \<equiv> \<forall>s. s\<in>domain(t1) \<union> domain(t2) \<longrightarrow>
      (\<forall>q. <q,p>\<in>leq \<longrightarrow> f`<1,s,t1,q> = f`<1,s,t2,q>)"

(* p ||-
   \<pi> \<in> \<tau> \<equiv> \<forall>v. <v,p>\<in>leq \<longrightarrow> (\<exists>q. <q,v>\<in>leq \<and> (\<exists>\<sigma>. \<exists>r. <\<sigma>,r>\<in>\<tau> \<and> <q,r>\<in>leq \<and>  q ||- \<pi> = \<sigma>)) *)
definition
  mem_case :: "[i,i,i,i,i,i] \<Rightarrow> o" where
  "mem_case(t1,t2,p,P,leq,f) \<equiv> \<forall>v. <v,p>\<in>leq \<longrightarrow>
    (\<exists>q. \<exists>s. \<exists>r. <q,v>\<in>leq \<and> <s,r> \<in> t2 \<and> <q,r>\<in>leq \<and>  f`<0,t1,s,q> = 1)"

(*definition
  Hfrc :: "[i,i,i,i] \<Rightarrow> o" where
  "Hfrc(P,leq,fnnc,f) \<equiv>
      ftype(fnnc) = 0 \<and>  eq_case(name1(fnnc),name2(fnnc),cond_of(fnnc),P,leq,f)
    \<or> ftype(fnnc) = 1 \<and> mem_case(name1(fnnc),name2(fnnc),cond_of(fnnc),P,leq,f)"
*)
definition
  Hfrc :: "[i,i,i,i] \<Rightarrow> o" where
  "Hfrc(P,leq,fnnc,f) \<equiv> \<exists>ft. \<exists>n1. \<exists>n2. \<exists>c. fnnc = <ft,n1,n2,c> \<and>
     (  ft = 0 \<and>  eq_case(n1,n2,c,P,leq,f)
      \<or> ft = 1 \<and> mem_case(n1,n2,c,P,leq,f))"

definition
  frecrel :: "i \<Rightarrow> i" where
  "frecrel(A) \<equiv> {<x,y> \<in> A\<times>A . 
            name1(x) \<in> domain(name1(y)) \<union> domain(name2(y)) \<and> 
            (name2(x) = name1(y) \<or> name2(x) = name2(y)) 
          \<or> name1(x) = name1(y) \<and> name2(x) \<in> domain(name2(y))}"

definition
  frc_at :: "[i,i,i] \<Rightarrow> i" where
  "frc_at(P,leq,fnnc) \<equiv> wfrec(frecrel(eclose({fnnc})),fnnc,\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"

lemma frecrel_fst_snd:
  "frecrel(A) = {z \<in> A\<times>A . 
            name1(fst(z)) \<in> domain(name1(snd(z))) \<union> domain(name2(snd(z))) \<and> 
            (name2(fst(z)) = name1(snd(z)) \<or> name2(fst(z)) = name2(snd(z))) 
          \<or> name1(fst(z)) = name1(snd(z)) \<and> name2(fst(z)) \<in> domain(name2(snd(z)))}"
  unfolding frecrel_def
  by (intro equalityI subsetI CollectI; elim CollectE; auto)

(*

Strategy
========

(* Warning: Hypotheses missing! *)
sats_is_wfrec_fm:
  MH(a2, a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env))))) ==> 
  sats(A, is_wfrec_fm(p,x,y,z), env) \<longleftrightarrow> is_wfrec(##A, MH, nth(x,env), nth(y,env), nth(z,env))

is_wfrec_iff_sats:
  MH(a2, a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env)))))) ==> 
  is_wfrec(##A, MH, x, y, z) \<longleftrightarrow> sats(A, is_wfrec_fm(p,i,j,k), env)

trans_wfrec_abs:
  trans(r) ==>  wfrec_replacement(M,MH,r) ==> relation2(M,MH,H) ==>
  is_wfrec(M,MH,r,a,z) \<longleftrightarrow> z=wfrec(r,a,H)


forces(t1=t2,P,leq,one,p) <--> 1 = frc_at(P,leq,<0,t1,t2,p>)
M,[P,leq,one,p,t1,t2] |= forces(Equal(0,1))  <--> 1 = frc_at(P,leq,<0,t1,t2,p>)

1 = frc_at(P,leq,<0,t1,t2,p>)
1 = wfrec(frecrel(eclose({<0,t1,t2,p>})),<0,t1,t2,p>,\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))
is_wfrec(##M,is_Hfrc_at(##M,P,leq),frecrel(eclose({<0,t1,t2,p>})),<0,t1,t2,p>,1)
sats(M, is_wfrec_fm(is_Hfrc_at_fm,x,y,z), [P,leq,one,p,t1,t2,frecrel(eclose({<0,t1,t2,p>})),<0,t1,t2,p>,1])
M, [P,leq,one,p,t1,t2,frecrel(eclose({<0,t1,t2,p>})),<0,t1,t2,p>,1] |= is_wfrec_fm(is_Hfrc_at_fm,6,7,8)
o bien
M, [frecrel(eclose({<0,t1,t2,p>})),<0,t1,t2,p>,1,P,leq,one,p,t1,t2] |= is_wfrec_fm(is_Hfrc_at_fm,0,1,2)


M, [P,leq,one,p,t1,t2] |=  Exists z on tup fet. 
               is_wfrec_fm(is_Hfrc_at_fm(4,5,6),fet,tup,on) & is_one_fm(on) &
               empty_fm(z) & is_tuple_fm(z,  8  ,  9  ,p,tup) & frecrel_eclose_fm(tup,fet)
                                           t1+8   t2+8

forces(Equal(t1,t2)) \<equiv> Exists Exists Exists Exists. 
               is_wfrec_fm(is_Hfrc_at_fm(4,5,6),0,1,2) \<and> is_one_fm(2) \<and> empty_fm(3) \<and> 
               is_tuple_fm(3, t1 #+ 8, t2 #+ 8, 7, 1) \<and> frecrel_eclose_fm(1,0)
*)

(*       --w--
x=<t1,t2,t3,t4>
      ---z---- *)
definition
  is_ftype :: "(i\<Rightarrow>o)\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "is_ftype(M,x,t1) == \<exists>z[M]. pair(M,t1,z,x)"

definition
  is_name1 :: "(i\<Rightarrow>o)\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "is_name1(M,x,t2) == \<exists>t1[M]. \<exists>z[M]. \<exists>w[M]. pair(M,t1,z,x) \<and> pair(M,t2,w,z)"

definition
  is_name2 :: "(i\<Rightarrow>o)\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "is_name2(M,x,t3) == \<exists>t1[M]. \<exists>z[M]. \<exists>t2[M]. \<exists>w[M]. \<exists>t4[M].
                           pair(M,t1,z,x) \<and> pair(M,t2,w,z) \<and> pair(M,t3,t4,w)"

definition
  is_cond_of :: "(i\<Rightarrow>o)\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "is_cond_of(M,x,t4) == \<exists>t1[M]. \<exists>z[M]. \<exists>t2[M]. \<exists>w[M]. \<exists>t3[M].
                           pair(M,t1,z,x) \<and> pair(M,t2,w,z) \<and> pair(M,t3,t4,w)"

definition
  is_one :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
  "is_one(M,o) == \<forall>z[M]. z\<in>o \<longleftrightarrow> empty(M,z)"

lemma (in M_trivial) is_one_abs [simp]:
     "M(o) ==> is_one(M,o) \<longleftrightarrow> o=1"
  by (simp add: is_one_def,blast intro: transM)

(* "eq_case(t1,t2,p,P,leq,f) \<equiv> \<forall>s\<in>domain(t1) \<union> domain(t2). \<forall>q. <q,p>\<in>leq \<longrightarrow>
                                 f`<1,s,t1,q> = f`<1,s,t2,q>" *)
definition
  is_eq_case :: "[i\<Rightarrow>o,i,i,i,i,i,i] \<Rightarrow> o" where
  "is_eq_case(M,t1,t2,p,P,leq,f) \<equiv>
   \<forall>s[M]. (\<exists>d[M]. is_domain(M,t1,d) \<and> s\<in>d) \<or> (\<exists>d[M]. is_domain(M,t2,d) \<and> s\<in>d)
       \<longrightarrow> (\<forall>q[M]. (\<exists>qp[M]. pair(M,q,p,qp) \<and> qp\<in>leq) \<longrightarrow>
            (\<exists>t1q[M]. \<exists>st1q[M]. \<exists>ost1q[M]. \<exists>t2q[M]. \<exists>st2q[M]. \<exists>o[M]. \<exists>ost2q[M]. \<exists>vf[M].
             pair(M,t1,q,t1q) \<and> pair(M,s,t1q,st1q) \<and> pair(M,o,st1q,ost1q) \<and>
             pair(M,t2,q,t2q) \<and> pair(M,s,t2q,st2q) \<and>
             is_one(M,o) \<and> pair(M,o,st2q,ost2q) \<and>
             fun_apply(M,f,ost2q,vf) \<and> fun_apply(M,f,ost1q,vf)))"

(*  "mem_case(t1,t2,p,P,leq,f) \<equiv> \<forall>v. <v,p>\<in>leq \<longrightarrow>
    (\<exists>q. \<exists>s. \<exists>r. <q,v>\<in>leq \<and> <s,r> \<in> t2 \<and> <q,r>\<in>leq \<and>  f`<0,t1,s,q> = 1)" *)
definition
  is_mem_case :: "[i\<Rightarrow>o,i,i,i,i,i,i] \<Rightarrow> o" where
  "is_mem_case(M,t1,t2,p,P,leq,f) \<equiv> \<forall>v[M]. \<forall>vp[M]. pair(M,v,p,vp) \<and> vp\<in>leq \<longrightarrow>
    (\<exists>q[M]. \<exists>qv[M]. \<exists>s[M]. \<exists>r[M]. \<exists>sr[M]. \<exists>qr[M]. \<exists>sq[M]. \<exists>t1sq[M]. \<exists>z[M]. \<exists>zt1sq[M]. \<exists>o[M].
     pair(M,q,v,qv) \<and> pair(M,s,r,sr) \<and> pair(M,q,r,qr) \<and> pair(M,s,q,sq) \<and>
     empty(M,z) \<and> pair(M,t1,sq,t1sq) \<and> pair(M,z,t1sq,zt1sq) \<and>
     is_one(M,o) \<and> sr\<in>t2 \<and> qv\<in>leq \<and> qr\<in>leq \<and> fun_apply(M,f,zt1sq,o))"

(* "Hfrc(P,leq,fnnc,f) \<equiv>
      ftype(fnnc) = 0 \<and>  eq_case(name1(fnnc),name2(fnnc),cond_of(fnnc),P,leq,f)
    \<or> ftype(fnnc) = 1 \<and> mem_case(name1(fnnc),name2(fnnc),cond_of(fnnc),P,leq,f)" *)
(* definition
  is_Hfrc :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_Hfrc(M,P,leq,fnnc,f) \<equiv>
     \<exists>ft[M]. \<exists>n1[M]. \<exists>n2[M]. \<exists>co[M]. \<exists>ec[M]. \<exists>mc[M].
     is_ftype(M,fnnc,ft) \<and> is_name1(M,fnnc,n1) \<and> is_name2(M,fnnc,n2) \<and> is_cond_of(M,fnnc,co) \<and>
      (  (\<exists>z[M]. empty(M,z)  \<and> ft=z \<and> is_eq_case(M,n1,n2,co,P,leq,f))
       \<or> (\<exists>o[M]. is_one(M,o) \<and> ft=o \<and> is_mem_case(M,n1,n2,co,P,leq,f)))"
*)

(*  "Hfrc(P,leq,fnnc,f) \<equiv> \<exists>ft. \<exists>n1. \<exists>n2. \<exists>c. fnnc = <ft,n1,n2,c> \<and>
     (  ft = 0 \<and>  eq_case(n1,n2,c,P,leq,f)
      \<or> ft = 1 \<and> mem_case(n1,n2,c,P,leq,f))" *)
definition
  is_Hfrc :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_Hfrc(M,P,leq,fnnc,f) \<equiv>
     \<exists>ft[M]. \<exists>n1[M]. \<exists>n2[M]. \<exists>co[M]. \<exists>nc[M]. \<exists>nnc[M].
      pair(M,n2,co,nc) \<and> pair(M,n1,nc,nnc) \<and> pair(M,ft,nnc,fnnc) \<and>
      (  (empty(M,ft) \<and> is_eq_case(M,n1,n2,co,P,leq,f))
       \<or> (is_one(M,ft) \<and>  is_mem_case(M,n1,n2,co,P,leq,f)))"

definition
  is_Hfrc_at :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_Hfrc_at(M,P,leq,fnnc,f,z) \<equiv> 
            (empty(M,z) \<and> \<not> is_Hfrc(M,P,leq,fnnc,f))
          \<or> (is_one(M,z) \<and> is_Hfrc(M,P,leq,fnnc,f))"

(*  "frecrel(A) \<equiv> {<x,y> \<in> A\<times>A . 
            name1(x) \<in> domain(name1(y)) \<union> domain(name2(y)) \<and> 
            (name2(x) = name1(y) \<or> name2(x) = name2(y)) 
          \<or> name1(x) = name1(y) \<and> name2(x) \<in> domain(name2(y))}" *)
definition
  frecrelP :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
  "frecrelP(M,xy) \<equiv>  
          (\<exists>x[M]. \<exists>y[M]. \<exists>n1x[M]. \<exists>n2x[M]. \<exists>n1y[M]. \<exists>n2y[M]. \<exists>dn1[M]. \<exists>dn2[M].
           pair(M,x,y,xy) 
          \<and> is_name1(M,x,n1x)\<and> is_name2(M,x,n2x) \<and> is_name1(M,y,n1y) \<and> is_name2(M,y,n2y)
          \<and> is_domain(M,n1y,dn1) \<and> is_domain(M,n2y,dn2) \<and> 
          ( 
             (n1x \<in> dn1 \<or> n1x \<in> dn2) \<and> (n2x = n1y \<or> n2x = n2y)
           \<or> n1x = n1y \<and> n2x \<in> dn2
          )
          )"
definition
  is_frecrel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_frecrel(M,A,r) \<equiv> \<exists>A2[M]. cartprod(M,A,A,A2) \<and> is_Collect(M,A2,frecrelP(M),r)"

(*   "frc_at(P,leq,fnnc) \<equiv>
      wfrec(frecrel(eclose({fnnc})),fnnc,\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))" *)
definition
  is_frc_at :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_frc_at(M,P,leq,fnnc,z) \<equiv>
  is_wfrec(M,\<lambda>x f z. z = bool_of_o(Hfrc(P,leq,x,f)),frecrel(eclose({fnnc})),fnnc,z)"

definition
  is_tuple_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "is_tuple_fm(z,t1,t2,p,tup) = Exists(Exists(And(pair_fm(t2 #+ 2,p #+ 2,0),
                      And(pair_fm(t1 #+ 2,0,1),pair_fm(z #+ 2,1,tup #+ 2)))))"

context M_basic
begin

lemma components_abs [simp]:
  "\<lbrakk>M(x); M(y); x\<in>A1\<times>A2 \<rbrakk> \<Longrightarrow> is_ftype(M,x,y) \<longleftrightarrow> ftype(x) = y"
  "\<lbrakk>M(x); M(y); x\<in>A1\<times>A2\<times>A3 \<rbrakk> \<Longrightarrow> is_name1(M,x,y) \<longleftrightarrow> name1(x) = y"
  "\<lbrakk>M(x); M(y); x\<in>A1\<times>A2\<times>A3\<times>A4 \<rbrakk> \<Longrightarrow> is_name2(M,x,y) \<longleftrightarrow> name2(x) = y"
  "\<lbrakk>M(x); M(y); x\<in>A1\<times>A2\<times>A3\<times>A4 \<rbrakk> \<Longrightarrow> is_cond_of(M,x,y) \<longleftrightarrow> cond_of(x) = y"
  unfolding ftype_def  is_ftype_def name1_def is_name1_def
    name2_def is_name2_def cond_of_def is_cond_of_def
  by auto

lemma components_abs' [simp]:
  "\<lbrakk>M(f); M(n1); M(n2); M(c); M(y) \<rbrakk> \<Longrightarrow> is_ftype(M,<f,n1,n2,c>,y) \<longleftrightarrow> ftype(<f,n1,n2,c>) = y"
  "\<lbrakk>M(f); M(n1); M(n2); M(c); M(y) \<rbrakk> \<Longrightarrow> is_name1(M,<f,n1,n2,c>,y) \<longleftrightarrow> name1(<f,n1,n2,c>) = y"
  "\<lbrakk>M(f); M(n1); M(n2); M(c); M(y) \<rbrakk> \<Longrightarrow> is_name2(M,<f,n1,n2,c>,y) \<longleftrightarrow> name2(<f,n1,n2,c>) = y"
  "\<lbrakk>M(f); M(n1); M(n2); M(c); M(y) \<rbrakk> \<Longrightarrow> is_cond_of(M,<f,n1,n2,c>,y) \<longleftrightarrow> cond_of(<f,n1,n2,c>) = y"
  unfolding ftype_def  is_ftype_def name1_def is_name1_def
    name2_def is_name2_def cond_of_def is_cond_of_def
  by auto

lemma in_domain: "M(y) \<Longrightarrow> x\<in>domain(y) \<Longrightarrow> M(x)"
  by (erule domainE, unfold Pair_def, blast dest:transM)

lemma comp_in_M:
  "M(leq) \<Longrightarrow> <p,q>\<in>leq \<Longrightarrow> M(p)"
  "M(leq) \<Longrightarrow> <p,q>\<in>leq \<Longrightarrow> M(q)"
  using transM unfolding Pair_def
  by blast+

lemma eq_case_abs [simp]:
  "\<lbrakk>M(t1); M(t2); M(p); M(P); M(leq); M(f)\<rbrakk> \<Longrightarrow> is_eq_case(M,t1,t2,p,P,leq,f) \<longleftrightarrow> eq_case(t1,t2,p,P,leq,f)"
  unfolding eq_case_def is_eq_case_def
  apply (simp)
  apply (intro iffI, unfold rall_def)
   prefer 2 apply (simp)
  apply (intro allI impI)
  apply (rename_tac s q)
  apply (drule_tac x=s in spec)
  apply (subgoal_tac "M(s)")
   apply (drule mp, assumption)+
   apply (drule_tac x=q in spec)
  apply (simp add: comp_in_M(1))
   apply (blast dest:in_domain)
  done

lemma mem_case_abs [simp]:
  "\<lbrakk>M(t1); M(t2); M(p); M(P); M(leq); M(f)\<rbrakk> \<Longrightarrow> is_mem_case(M,t1,t2,p,P,leq,f) \<longleftrightarrow> mem_case(t1,t2,p,P,leq,f)"
  unfolding mem_case_def is_mem_case_def
  apply simp
  apply (unfold rall_def)
  apply (intro iffI allI impI)
  apply (drule_tac x=v in spec)
  apply (subgoal_tac "M(v)")
    apply (drule mp, assumption)+
    apply blast
  apply (simp add: comp_in_M(1))
  apply (drule_tac x=x in spec)
  apply (blast intro:comp_in_M)
  done

lemma Hfrc_abs [simp]:
  "\<lbrakk>M(fnnc); M(P); M(leq); M(f)\<rbrakk> \<Longrightarrow>
   is_Hfrc(M,P,leq,fnnc,f) \<longleftrightarrow> Hfrc(P,leq,fnnc,f)"
  unfolding is_Hfrc_def Hfrc_def
  by auto

lemma Hfrc_at_abs [simp]:
  "\<lbrakk>M(fnnc); M(P); M(leq); M(f) ; M(z)\<rbrakk> \<Longrightarrow>
   is_Hfrc_at(M,P,leq,fnnc,f,z) \<longleftrightarrow>  z = bool_of_o(Hfrc(P,leq,fnnc,f)) "
  unfolding is_Hfrc_at_def
  by auto

lemma frecrelP_abs [simp] :
  "M(z) \<Longrightarrow>
   frecrelP(M,z) \<longleftrightarrow>  name1(fst(z)) \<in> domain(name1(snd(z))) \<union> domain(name2(snd(z))) \<and> 
            (name2(fst(z)) = name1(snd(z)) \<or> name2(fst(z)) = name2(snd(z))) 
          \<or> name1(fst(z)) = name1(snd(z)) \<and> name2(fst(z)) \<in> domain(name2(snd(z)))"
  unfolding frecrelP_def rex_def 
  sorry

lemma frecrel_abs [simp] :
  "\<lbrakk>M(A); M(r)\<rbrakk> \<Longrightarrow>
   is_frecrel(M,A,r) \<longleftrightarrow>  r = frecrel(A) "
  unfolding is_frecrel_def frecrel_fst_snd 
  using transM[OF _ cartprod_closed[of A A]]
  by simp

schematic_goal sats_is_frecrel_fm_auto:
  assumes 
    "a\<in>nat"  "r\<in>nat" "env\<in>list(A)"
  shows
    "is_frecrel(##A,nth(a, env),nth(r, env))
    \<longleftrightarrow> sats(A,?ifrl_fm(a,r),env)"
    and
    "(?ifrl_fm(a,r) \<in> formula)"
  (*  (* 28 secs *) 
    unfolding is_frecrel_def  is_Collect_def frecrelP_def is_name1_def is_name2_def
   by (insert assms ; (rule sep_rules cartprod_iff_sats | simp del:sats_cartprod_fm))+ 
       *)
    (* 17 secs *)
  unfolding is_frecrel_def  is_Collect_def frecrelP_def
   apply (insert assms ; (rule sep_rules cartprod_iff_sats | simp del:sats_cartprod_fm))
   apply (insert assms ; (rule sep_rules cartprod_iff_sats | simp del:sats_cartprod_fm))
    apply (insert assms ; (rule sep_rules cartprod_iff_sats | simp del:sats_cartprod_fm))
      apply (insert assms ; (rule sep_rules cartprod_iff_sats | simp del:sats_cartprod_fm))
            apply (unfold  is_name1_def is_name2_def)
            apply (insert assms ; (rule sep_rules | simp del:sats_cartprod_fm))+
  done

schematic_goal is_frecrel_iff_sats:
  assumes
    "nth(a,env) = aa" "nth(r,env) = rr" "a\<in> nat"  "r\<in> nat"  "env \<in> list(A)"
  shows
       "is_frecrel(##A, aa,rr) \<longleftrightarrow> sats(A, ?is_one_fm(a,r), env)"
  unfolding \<open>nth(a,env) = aa\<close>[symmetric] \<open>nth(r,env) = rr\<close>[symmetric]
  by (rule sats_is_frecrel_fm_auto(1); simp add:assms)

schematic_goal sats_is_one_fm_auto:
  assumes 
    "z\<in>nat" "env\<in>list(A)"
  shows
    "is_one(##A,nth(z, env))
    \<longleftrightarrow> sats(A,?io_fm(z),env)"
    and
    "(?io_fm(z) \<in> formula)"
   unfolding is_one_def  
   by (insert assms ; (rule sep_rules | simp))+

schematic_goal is_one_iff_sats :
  assumes
    "nth(i,env) = x" "i \<in> nat"  "env \<in> list(A)"
  shows
       "is_one(##A, x) \<longleftrightarrow> sats(A, ?is_one_fm(i), env)"
  unfolding \<open>nth(i,env) = x\<close>[symmetric] 
  by (rule sats_is_one_fm_auto(1); simp add:assms)

schematic_goal sats_is_mem_case_fm_auto:
  assumes 
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "is_mem_case(##A, nth(n1, env),nth(n2, env),nth(p, env),nth(P, env), nth(leq, env),nth(f,env))
    \<longleftrightarrow> sats(A,?imc_fm(n1,n2,p,P,leq,f),env)"
    and
    "(?imc_fm(n1,n2,p,P,leq,f) \<in> formula)"
   unfolding is_mem_case_def
       (* 19 secs *)
   apply (insert assms ; (rule sep_rules  | simp))
   apply ((rule sep_rules  | simp))+
                    apply ((rule sep_rules is_one_iff_sats[of 0]  | simp))
                      apply (insert assms ; (rule sep_rules  | simp))+
  done

schematic_goal sats_is_eq_case_fm_auto:
  assumes 
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "is_eq_case(##A, nth(n1, env),nth(n2, env),nth(p, env),nth(P, env), nth(leq, env),nth(f,env))
    \<longleftrightarrow> sats(A,?iec_fm(n1,n2,p,P,leq,f),env)"
    and
    "(?iec_fm(n1,n2,p,P,leq,f) \<in> formula)"
  unfolding is_eq_case_def
    (* 9 secs *)
    apply (insert assms ; (rule sep_rules  | simp))
   apply ((rule sep_rules  | simp))+
                    apply ((rule sep_rules is_one_iff_sats[of 0]  | simp))
                      apply (insert assms ; (rule sep_rules  | simp))+
  done
             
schematic_goal is_mem_case_iff_sats:
  assumes
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"    
    "nth(n1,env) = nn1" "nth(n2,env) = nn2" "nth(p,env) = pp" "nth(P,env) = PP" 
    "nth(leq,env) = lleq" "nth(f,env) = ff"  
  shows
    "is_mem_case(##A, nn1,nn2,pp,PP, lleq,ff)
    \<longleftrightarrow> sats(A,?imc_fm(n1,n2,p,P,leq,f),env)"
  unfolding   \<open>nth(n1,env) = nn1\<close>[symmetric] \<open>nth(n2,env) = nn2\<close>[symmetric] 
    \<open>nth(p,env) = pp\<close>[symmetric] \<open>nth(P,env) = PP\<close>[symmetric] 
    \<open>nth(leq,env) = lleq\<close>[symmetric] \<open>nth(f,env) = ff\<close>[symmetric]  
  by (rule sats_is_mem_case_fm_auto(1); simp add:assms)

schematic_goal is_eq_case_iff_sats :
  assumes
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"    
    "nth(n1,env) = nn1" "nth(n2,env) = nn2" "nth(p,env) = pp" "nth(P,env) = PP" 
    "nth(leq,env) = lleq" "nth(f,env) = ff"  
  shows
    "is_eq_case(##A, nn1,nn2,pp,PP, lleq,ff)
    \<longleftrightarrow> sats(A,?iec_fm(n1,n2,p,P,leq,f),env)"
  unfolding   \<open>nth(n1,env) = nn1\<close>[symmetric] \<open>nth(n2,env) = nn2\<close>[symmetric] 
    \<open>nth(p,env) = pp\<close>[symmetric] \<open>nth(P,env) = PP\<close>[symmetric] 
    \<open>nth(leq,env) = lleq\<close>[symmetric] \<open>nth(f,env) = ff\<close>[symmetric]  
  by (rule sats_is_eq_case_fm_auto(1); simp add:assms)

lemma empty_iff_sats':
      "[| nth(i,env) = x; i \<in> nat; env \<in> list(A)|]
       ==> empty(##A, x) \<longleftrightarrow> sats(A, empty_fm(i), env)"
by simp

lemmas function_iff_sats' =
        empty_iff_sats' number1_iff_sats
        upair_iff_sats pair_iff_sats union_iff_sats
        big_union_iff_sats cons_iff_sats successor_iff_sats
        fun_apply_iff_sats  Memrel_iff_sats
        pred_set_iff_sats domain_iff_sats range_iff_sats field_iff_sats
        image_iff_sats pre_image_iff_sats
        relation_iff_sats is_function_iff_sats

lemmas sep_rules' = nth_0 nth_ConsI FOL_iff_sats function_iff_sats'
                   fun_plus_iff_sats 
                    omega_iff_sats FOL_sats_iff 


schematic_goal sats_is_Hfrc_fm_auto:
  assumes 
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "is_Hfrc(##A,nth(P, env), nth(leq, env), nth(fnnc, env),nth(f, env))
    \<longleftrightarrow> sats(A,?hfrc_fm(P,leq,fnnc,f),env)"
    and
    "(?hfrc_fm(P,leq,fnnc,f) \<in> formula)"
  unfolding is_Hfrc_def 
  (* 11 secs *)
  by (insert assms; (rule sep_rules' is_mem_case_iff_sats[of 4 3 2 "P #+ 6" "leq #+ 6" "f #+ 6"] is_eq_case_iff_sats[of 4 3 2 "P #+ 6" "leq #+ 6" "f #+ 6"] is_one_iff_sats | simp))+

schematic_goal is_Hfrc_iff_sats:
  assumes
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "env\<in>list(A)"    
    "nth(P,env) = PP"  "nth(leq,env) = lleq" "nth(fnnc,env) = ffnnc" "nth(f,env) = ff" 
  shows
    "is_Hfrc(##A, PP, lleq,ffnnc,ff)
    \<longleftrightarrow> sats(A,?ihfrc_fm(P,leq,fnnc,f),env)"
  unfolding   \<open>nth(P,env) = PP\<close>[symmetric] \<open>nth(leq,env) = lleq\<close>[symmetric] 
    \<open>nth(fnnc,env) = ffnnc\<close>[symmetric]  \<open>nth(f,env) = ff\<close>[symmetric]  
  by (rule sats_is_Hfrc_fm_auto(1); simp add:assms)

schematic_goal sats_is_Hfrc_at_fm_auto:
  assumes 
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "z\<in>nat" "env\<in>list(A)"
  shows
    "is_Hfrc_at(##A,nth(P, env), nth(leq, env), nth(fnnc, env),nth(f, env),nth(z, env))
    \<longleftrightarrow> sats(A,?hfrc_fm(P,leq,fnnc,f,z),env)"
    and
    "(?hfrc_fm(P,leq,fnnc,f,z) \<in> formula)"
  unfolding is_Hfrc_at_def 
  by (insert assms; (rule sep_rules' is_one_iff_sats is_Hfrc_iff_sats[of P leq fnnc f] | simp))+

schematic_goal is_Hfrc_at_iff_sats:
  assumes
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "z\<in>nat" "env\<in>list(A)"    
    "nth(P,env) = PP"  "nth(leq,env) = lleq" "nth(fnnc,env) = ffnnc" 
    "nth(f,env) = ff" "nth(z,env) = zz"
  shows
    "is_Hfrc_at(##A, PP, lleq,ffnnc,ff,zz)
    \<longleftrightarrow> sats(A,?hfrc_at_fm(P,leq,fnnc,f,z),env)"
  unfolding   \<open>nth(P,env) = PP\<close>[symmetric] \<open>nth(leq,env) = lleq\<close>[symmetric] 
    \<open>nth(fnnc,env) = ffnnc\<close>[symmetric]  \<open>nth(f,env) = ff\<close>[symmetric]
    \<open>nth(z,env) = zz\<close>[symmetric]  
  by (rule sats_is_Hfrc_at_fm_auto(1); simp add:assms)

lemma is_tuple_fm_def_type [TC]:
  "\<lbrakk>z\<in>nat ; t1\<in>nat ; t2\<in>nat ; p\<in>nat ; tup\<in>nat\<rbrakk> \<Longrightarrow> is_tuple_fm(z,t1,t2,p,tup) \<in> formula"
  unfolding is_tuple_fm_def
  by simp

lemma relation2_Hfrc_at_abs:
  "\<lbrakk>M(P); M(leq)\<rbrakk> \<Longrightarrow> 
  relation2(M,is_Hfrc_at(M,P,leq),\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"
  unfolding relation2_def
  by simp

end (* context M_basic *)

definition
  is_Hfrc_at_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "is_Hfrc_at_fm(P,leq,fnnc,f,z) \<equiv> Or(And(empty_fm(z),
             Neg(Exists
                  (Exists
                    (Exists
                      (Exists
                        (Exists
                          (And(pair_fm(2, 1, 0),
                               Exists
                                (And(pair_fm(4, 1, 0),
                                     And(pair_fm(5, 0, succ(succ(succ(succ(succ(succ(fnnc))))))),
                                         Or(And(empty_fm(5),
                                                Forall
                                                 (Implies
                                                   (Or(Exists(And(domain_fm(6, 0), Member(1, 0))), Exists(And(domain_fm(5, 0), Member(1, 0)))),
                                                    Forall
                                                     (Implies
                                                       (Exists(And(pair_fm(1, 5, 0), Member(0, succ(succ(succ(leq #+ 6)))))),
                                                        Exists
                                                         (And(pair_fm(7, 1, 0),
                                                              Exists
                                                               (And(pair_fm(3, 1, 0),
                                                                    Exists
                                                                     (Exists
                                                                       (Exists
 (Exists
   (And(pair_fm(0, 4, 3),
        And(pair_fm(11, 6, 2),
            And(pair_fm(7, 2, 1),
                And(Forall(Iff(Member(0, 1), empty_fm(0))),
                    Exists
                     (And(pair_fm(1, 2, 0),
                          Exists
                           (And(fun_apply_fm(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(f #+ 6)))))))))), 1, 0),
                                fun_apply_fm(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(f #+ 6)))))))))), 5, 0)))))))))))))))))))))),
                                            And(Forall(Iff(Member(0, 6), empty_fm(0))),
                                                Forall
                                                 (Implies
                                                   (Exists(And(pair_fm(1, 4, 0), Member(0, succ(succ(leq #+ 6))))),
                                                    Exists
                                                     (Exists
                                                       (And(pair_fm(1, 2, 0),
                                                            Exists
                                                             (Exists
                                                               (Exists
                                                                 (And(pair_fm(2, 1, 0),
                                                                      Exists
                                                                       (And
 (pair_fm(5, 2, 0),
  Exists
   (And(pair_fm(4, 6, 0),
        Exists
         (Exists
           (And(empty_fm(0),
                And(pair_fm(14, 2, 1),
                    Exists
                     (And(pair_fm(1, 2, 0),
                          Exists
                           (And(Forall(Iff(Member(0, 1), empty_fm(0))),
                                And(Member(6, succ(14)),
                                    And(Member(9, succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(leq #+ 6))))))))))))),
                                        And(Member(5, succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(leq #+ 6))))))))))))),
                                            fun_apply_fm
                                             (succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(f #+ 6)))))))))))), 1,
                                              0)))))))))))))))))))))))))))))))))))))),
         And(Forall(Iff(Member(0, succ(z)), empty_fm(0))),
             Exists
              (Exists
                (Exists
                  (Exists
                    (Exists
                      (And(pair_fm(2, 1, 0),
                           Exists
                            (And(pair_fm(4, 1, 0),
                                 And(pair_fm(5, 0, succ(succ(succ(succ(succ(succ(fnnc))))))),
                                     Or(And(empty_fm(5),
                                            Forall
                                             (Implies
                                               (Or(Exists(And(domain_fm(6, 0), Member(1, 0))), Exists(And(domain_fm(5, 0), Member(1, 0)))),
                                                Forall
                                                 (Implies
                                                   (Exists(And(pair_fm(1, 5, 0), Member(0, succ(succ(succ(leq #+ 6)))))),
                                                    Exists
                                                     (And(pair_fm(7, 1, 0),
                                                          Exists
                                                           (And(pair_fm(3, 1, 0),
                                                                Exists
                                                                 (Exists
                                                                   (Exists
                                                                     (Exists
                                                                       (And
 (pair_fm(0, 4, 3),
  And(pair_fm(11, 6, 2),
      And(pair_fm(7, 2, 1),
          And(Forall(Iff(Member(0, 1), empty_fm(0))),
              Exists
               (And(pair_fm(1, 2, 0),
                    Exists
                     (And(fun_apply_fm(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(f #+ 6)))))))))), 1, 0),
                          fun_apply_fm(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(f #+ 6)))))))))), 5, 0)))))))))))))))))))))),
                                        And(Forall(Iff(Member(0, 6), empty_fm(0))),
                                            Forall
                                             (Implies
                                               (Exists(And(pair_fm(1, 4, 0), Member(0, succ(succ(leq #+ 6))))),
                                                Exists
                                                 (Exists
                                                   (And(pair_fm(1, 2, 0),
                                                        Exists
                                                         (Exists
                                                           (Exists
                                                             (And(pair_fm(2, 1, 0),
                                                                  Exists
                                                                   (And(pair_fm(5, 2, 0),
Exists
 (And(pair_fm(4, 6, 0),
      Exists
       (Exists
         (And(empty_fm(0),
              And(pair_fm(14, 2, 1),
                  Exists
                   (And(pair_fm(1, 2, 0),
                        Exists
                         (And(Forall(Iff(Member(0, 1), empty_fm(0))),
                              And(Member(6, succ(14)),
                                  And(Member(9, succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(leq #+ 6))))))))))))),
                                      And(Member(5, succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(leq #+ 6))))))))))))),
                                          fun_apply_fm
                                           (succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(f #+ 6)))))))))))), 1,
                                            0))))))))))))))))))))))))))))))))))))))"

definition
  is_frecrel_fm :: "[i,i] \<Rightarrow> i" where
  "is_frecrel_fm(a,r) \<equiv> Exists
       (And(cartprod_fm(succ(a), succ(a), 0),
            Forall
             (Iff(Member(0, succ(succ(r))),
                  And(Member(0, 1),
                      Exists
                       (Exists
                         (And(pair_fm(1, 0, 2),
                              Exists
                               (And(Exists(Exists(And(pair_fm(1, 0, 4), Exists(pair_fm(3, 0, 1))))),
                                    Exists
                                     (And(Exists
                                           (Exists(And(pair_fm(1, 0, 5), Exists(Exists(And(pair_fm(1, 0, 2), Exists(pair_fm(5, 0, 1)))))))),
                                          Exists
                                           (And(Exists(Exists(And(pair_fm(1, 0, 5), Exists(pair_fm(3, 0, 1))))),
                                                Exists
                                                 (And(Exists
                                                       (Exists
                                                         (And(pair_fm(1, 0, 6),
                                                              Exists(Exists(And(pair_fm(1, 0, 2), Exists(pair_fm(5, 0, 1)))))))),
                                                      Exists
                                                       (And(domain_fm(2, 0),
                                                            Exists
                                                             (And(domain_fm(2, 0),
                                                                  Or(And(Or(Member(5, 1), Member(5, 0)), Or(Equal(4, 3), Equal(4, 2))),
                                                                     And(Equal(5, 3), Member(4, 0)))))))))))))))))))))))"

definition
  is_one_fm :: "i \<Rightarrow> i" where
  "is_one_fm(z) \<equiv> Forall(Iff(Member(0, succ(z)), empty_fm(0)))"

definition
  frecrel_eclose_fm :: "[i,i] \<Rightarrow> i" where
  "frecrel_eclose_fm(tup,fet) \<equiv> Exists(And(is_eclose_fm(succ(tup),0),is_frecrel_fm(0,succ(fet))))"

definition
  forces_eq :: "[i,i] \<Rightarrow> i" where
  "forces_eq(t1,t2) \<equiv> Exists(Exists(Exists(Exists(And(And(And(And(
               is_wfrec_fm(is_Hfrc_at_fm(4,5,2,1,0),0,1,2),is_one_fm(2)),empty_fm(3)),
               is_tuple_fm(3, t1 #+ 8, t2 #+ 8, 7, 1)),frecrel_eclose_fm(1,0))))))"

definition
  forces_mem :: "[i,i] \<Rightarrow> i" where
  "forces_mem(t1,t2) \<equiv> Exists(Exists(Exists(Exists(And(And(And(And(
               is_wfrec_fm(is_Hfrc_at_fm(4,5,2,1,0),0,1,2),is_one_fm(2)),is_one_fm(3)),
               is_tuple_fm(3, t1 #+ 8, t2 #+ 8, 7, 1)),frecrel_eclose_fm(1,0))))))"


(*
forces (\<not>\<phi>) == (\<forall>q\<in>P. (<q,p>\<in>leq \<longrightarrow> \<not> forces(\<phi>)))
forces(And(\<phi>,\<psi>)) == And(forces(\<phi>), forces(\<psi>))

forces(Nand(\<phi>,\<psi>)) == (\<forall>q\<in>P. (<q,p>\<in>leq \<longrightarrow> \<not> And(forces(\<phi>), forces(\<psi>))))
forces(Nand(\<phi>,\<psi>)) == (\<forall>q. \<forall>qp. q\<in>P \<longrightarrow> (<q,p> = qp \<and> qp\<in>leq \<longrightarrow> \<not> And(forces(\<phi>), forces(\<psi>))))
                       1    0  1 (0+2)   1 (3+2) 0    0  (1+2) 
forces(Nand(\<phi>,\<psi>)) == Forall(Forall(Implies(Member(1,2),
              Implies(And(pair_fm(1,5,0),Member(0,3)),Neg(And(forces(\<phi>), forces(\<psi>)))))))
*)
consts forces :: "i\<Rightarrow>i"
primrec
  "forces(Member(x,y)) = forces_mem(x,y)"
  "forces(Equal(x,y))  = forces_eq(x,y)"
  (* Problem: This definition does not preserve the place of P,leq,one,p 
              in the environment *)
  "forces(Nand(p,q))   = Forall(Forall(Implies(Member(1,2),
                  Implies(And(pair_fm(1,5,0),Member(0,3)),Neg(And(forces(p), forces(q)))))))"
  "forces(Forall(p))   = Forall(forces(p))" (* check indexes *)

consts forces_ren :: "[i,i,i]\<Rightarrow>i"
primrec
  "forces_ren(fren,fref,Member(x,y)) = forces_mem(x,y)"
  "forces_ren(fren,fref,Equal(x,y))  = forces_eq(x,y)"
  "forces_ren(fren,fref,Nand(p,q))   = Forall(Forall(Implies(Member(1,2),
                  Implies(And(pair_fm(1,5,0),Member(0,3)),
                  Neg(And(fren`forces_ren(fren,fref,p), fren`forces_ren(fren,fref,q)))))))"
  "forces_ren(fren,fref,Forall(p))   = Forall(fref`forces_ren(fren,fref,p))" (* check indexes *)

context M_basic
begin

lemma sats_is_frecrel_fm:
  assumes
    "a\<in>nat"  "r\<in>nat" "env\<in>list(A)"
  shows
    "is_frecrel(##A,nth(a, env),nth(r, env))
    \<longleftrightarrow> sats(A,is_frecrel_fm(a,r),env)"
  unfolding is_frecrel_fm_def using assms sats_is_frecrel_fm_auto
  by simp

lemma sats_is_Hfrc_at_fm:
  assumes
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "z\<in>nat" "env\<in>list(A)"
  shows
    "is_Hfrc_at(##A,nth(P, env), nth(leq, env), nth(fnnc, env),nth(f, env),nth(z, env))
    \<longleftrightarrow> sats(A,is_Hfrc_at_fm(P,leq,fnnc,f,z),env)"
  unfolding is_Hfrc_at_fm_def using assms sats_is_Hfrc_at_fm_auto by simp

lemma frecrel_eclose_fm_type [TC]:
  "tup \<in> nat \<Longrightarrow> fet \<in> nat \<Longrightarrow> frecrel_eclose_fm(tup,fet) \<in> formula"
  unfolding frecrel_eclose_fm_def is_frecrel_fm_def
  by simp

lemma forces_eq_type [TC]:
  "t1 \<in> nat \<Longrightarrow> t2 \<in> nat \<Longrightarrow> forces_eq(t1,t2) \<in> formula"
  unfolding forces_eq_def is_one_fm_def is_Hfrc_at_fm_def
  by simp

lemma forces_mem_type [TC]:
  "t1 \<in> nat \<Longrightarrow> t2 \<in> nat \<Longrightarrow> forces_mem(t1,t2) \<in> formula"
  unfolding forces_mem_def is_one_fm_def is_Hfrc_at_fm_def
  by simp

lemma pred_Un:
  "x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> Arith.pred(succ(x) \<union> y) = x \<union> Arith.pred(y)"
  "x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> Arith.pred(x \<union> succ(y)) = Arith.pred(x) \<union> y"
  using pred_Un_distrib pred_succ_eq by simp_all

lemma arity_forces_eq:
  "t1 \<in> nat \<Longrightarrow> t2 \<in> nat \<Longrightarrow> arity(forces_eq(t1,t2)) = (t1 \<union> t2) #+ 5"
  unfolding forces_eq_def is_one_fm_def is_Hfrc_at_fm_def is_tuple_fm_def
    frecrel_eclose_fm_def is_frecrel_fm_def cartprod_fm_def
    is_eclose_fm_def mem_eclose_fm_def finite_ordinal_fm_def
    eclose_n_fm_def is_iterates_fm_def iterates_MH_fm_def
    is_wfrec_fm_def is_recfun_fm_def restriction_fm_def pre_image_fm_def
    is_nat_case_fm_def quasinat_fm_def Memrel_fm_def fm_defs
  apply (simp add:nat_union_abs1 nat_union_abs2 pred_Un, simp add:nat_simp_union)
  apply (intro conjI impI)
   apply (rule le_anti_sym,simp_all)
  apply (drule not_le_imp_lt,simp_all, drule leI,simp)
done

lemma arity_forces_mem:
  "t1 \<in> nat \<Longrightarrow> t2 \<in> nat \<Longrightarrow> arity(forces_mem(t1,t2)) = (t1 \<union> t2) #+ 5"
  unfolding forces_mem_def is_one_fm_def is_Hfrc_at_fm_def is_tuple_fm_def
    frecrel_eclose_fm_def is_frecrel_fm_def cartprod_fm_def
    is_eclose_fm_def mem_eclose_fm_def finite_ordinal_fm_def
    eclose_n_fm_def is_iterates_fm_def iterates_MH_fm_def
    is_wfrec_fm_def is_recfun_fm_def restriction_fm_def pre_image_fm_def
    is_nat_case_fm_def quasinat_fm_def Memrel_fm_def fm_defs
  apply (simp add:nat_union_abs1 nat_union_abs2 pred_Un, simp add:nat_simp_union)
  apply (intro conjI impI)
   apply (rule le_anti_sym,simp_all)
  apply (drule not_le_imp_lt,simp_all, drule leI,simp)
  done

lemma lambda_Hfrc_at_abs:
  "\<lbrakk>M(P); M(leq)\<rbrakk> \<Longrightarrow>
   (\<lambda>b c d. M(b) \<longrightarrow> M(c) \<longrightarrow> M(d) \<longrightarrow> is_Hfrc_at(M,P,leq,b,c,d)) \<equiv> (\<lambda>b c d. M(b) \<longrightarrow> M(c) \<longrightarrow> M(d) \<longrightarrow> d = bool_of_o(Hfrc(P, leq, b, c)))"
  by simp

lemma lambda_is_wfrec: "\<lbrakk>M(r); M(a); M(z) \<rbrakk> \<Longrightarrow> is_wfrec(M,MH,r,a,z) \<longleftrightarrow> 
        is_wfrec(M,\<lambda>b c d. M(b) \<longrightarrow> M(c) \<longrightarrow> M(d) \<longrightarrow> MH(b,c,d),r,a,z)"
  unfolding is_wfrec_def M_is_recfun_def by force

end (* context M_basic *)


context M_trancl 
begin

lemma wfrec_trancl_frecrel: 
  "wfrec(frecrel(eclose({fnnc})), fnnc, \<lambda>x f. bool_of_o(Hfrc(P, leq, x, f))) =
   wfrec(frecrel(eclose({fnnc}))^+, fnnc, \<lambda>x f. bool_of_o(Hfrc(P, leq, x, f)))"
  sorry

lemma horrible_aux:
  "is_wfrec(M, \<lambda>b c d. M(b) \<longrightarrow> M(c) \<longrightarrow> M(d) \<longrightarrow> is_Hfrc_at(M, P, leq, b, c, d), frecrel(eclose({fnnc}))^+, fnnc, z) \<longleftrightarrow>
   is_wfrec(M, \<lambda>b c d. M(b) \<longrightarrow> M(c) \<longrightarrow> M(d) \<longrightarrow> d = bool_of_o(Hfrc(P, leq, b, c)), frecrel(eclose({fnnc})), fnnc, z)"
  sorry

lemma frc_at_abs:
  assumes
    "M(fnnc)" "M(P)" "M(leq)" "M(z)" "M(frecrel(eclose({fnnc}))^+)" "M(frecrel(eclose({fnnc})))"
    "wfrec_replacement(M, is_Hfrc_at(M, P, leq), frecrel(eclose({fnnc}))^+)"
    "wf(frecrel(eclose({fnnc}))^+)"
  shows
    "is_frc_at(M,P,leq,fnnc,z) \<longleftrightarrow> z = frc_at(P,leq,fnnc)"
  unfolding is_frc_at_def frc_at_def using
  trans_wfrec_abs[OF _ trans_trancl relation_trancl _ _ _ assms(7) relation2_Hfrc_at_abs[of P leq], of fnnc z]
  apply (simp add:wfrec_trancl_frecrel)
  apply (insert assms; subst lambda_is_wfrec, assumption+)
  apply (subst (asm) lambda_is_wfrec, assumption+)
  apply (simp add: horrible_aux)
  done

end (* context M_trancl *)

context forcing_data
begin

lemma def_one: "xa \<in>M \<Longrightarrow> (\<forall>x\<in>M. x \<in> xa \<longleftrightarrow> x = 0) \<longleftrightarrow> xa = 1"
  sorry

lemma uno_in_M: "1\<in>M"
  by (simp del:setclass_iff add:setclass_iff[symmetric])

lemma sats_forces_eq: "\<lbrakk> [P,leq,one,p,t1,t2] @ env \<in> list(M); \<And>x. x\<in>M \<Longrightarrow> frecrel(x)\<in>M \<rbrakk> \<Longrightarrow>
          sats(M,forces_eq(0,1),[P,leq,one,p,t1,t2] @ env) \<longleftrightarrow>
          sats(M, is_wfrec_fm(is_Hfrc_at_fm(4, 5, 2, 1, 0), 0, 1, 2),
                  [frecrel(eclose(<0,t1,t2,p>)), <0,t1,t2,p>, 1, 0, P, leq, one, p, t1, t2] @ env)"
proof -
  assume "x\<in>M \<Longrightarrow> frecrel(x)\<in>M" for x
  assume "[P,leq,one,p,t1,t2] @ env \<in> list(M)"
  then
  have "sats(M,forces_eq(0,1),[P,leq,one,p,t1,t2] @ env) \<longleftrightarrow> (\<exists>x\<in>M. \<exists>xa\<in>M. \<exists>xb\<in>M. \<exists>xc\<in>M.
               sats(M, is_wfrec_fm(is_Hfrc_at_fm(4, 5, 2, 1, 0), 0, 1, 2), [xc, xb, xa, x, P, leq, one, p, t1, t2] @ env) \<and>
               xa = 1 \<and>
               sats(M, empty_fm(3), [xc, xb, 1, x, P, leq, one, p, t1, t2] @ env) \<and>
               sats(M, Exists(Exists(And(pair_fm(11, 9, 0), And(pair_fm(10, 0, 1), pair_fm(5, 1, 3))))),
                    [xc, xb, 1, x, P, leq, one, p, t1, t2] @ env) \<and>
               sats(M, Exists(And(is_eclose_fm(2, 0), is_frecrel_fm(0, 1))), [xc, xb, 1, x, P, leq, one, p, t1, t2] @ env))"
    unfolding forces_eq_def is_one_fm_def is_tuple_fm_def frecrel_eclose_fm_def
    using M_inhabit def_one
    by simp
  moreover from \<open>[P,leq,one,p,t1,t2] @ env \<in> list(M)\<close>
  have "... \<longleftrightarrow> (\<exists>x\<in>M. \<exists>xa\<in>M. \<exists>xb\<in>M. \<exists>xc\<in>M.
               sats(M, is_wfrec_fm(is_Hfrc_at_fm(4, 5, 2, 1, 0), 0, 1, 2), [xc, xb, xa, x, P, leq, one, p, t1, t2] @ env) \<and>
               xa = 1 \<and>
               x = 0 \<and>
               sats(M, Exists(Exists(And(pair_fm(11, 9, 0), And(pair_fm(10, 0, 1), pair_fm(5, 1, 3))))),
                    [xc, xb, 1, x, P, leq, one, p, t1, t2] @ env) \<and>
               sats(M, Exists(And(is_eclose_fm(2, 0), is_frecrel_fm(0, 1))), [xc, xb, 1, x, P, leq, one, p, t1, t2] @ env))"
    by force
  moreover from \<open>[P,leq,one,p,t1,t2] @ env \<in> list(M)\<close>
  have "... \<longleftrightarrow> (\<exists>xa\<in>M. \<exists>xb\<in>M. \<exists>xc\<in>M.
               sats(M, is_wfrec_fm(is_Hfrc_at_fm(4, 5, 2, 1, 0), 0, 1, 2), [xc, xb, xa, 0, P, leq, one, p, t1, t2] @ env) \<and>
               xa = 1 \<and>
               sats(M, Exists(Exists(And(pair_fm(11, 9, 0), And(pair_fm(10, 0, 1), pair_fm(5, 1, 3))))),
                    [xc, xb, 1, 0, P, leq, one, p, t1, t2] @ env) \<and>
               sats(M, Exists(And(is_eclose_fm(2, 0), is_frecrel_fm(0, 1))), [xc, xb, 1, 0, P, leq, one, p, t1, t2] @ env))"
    using M_inhabit by force
  moreover from \<open>[P,leq,one,p,t1,t2] @ env \<in> list(M)\<close>
  have " ... \<longleftrightarrow> (\<exists>xb\<in>M. \<exists>xc\<in>M.
               sats(M, is_wfrec_fm(is_Hfrc_at_fm(4, 5, 2, 1, 0), 0, 1, 2), [xc, xb, 1, 0, P, leq, one, p, t1, t2] @ env) \<and>
               sats(M, Exists(Exists(And(pair_fm(11, 9, 0), And(pair_fm(10, 0, 1), pair_fm(5, 1, 3))))),
                    [xc, xb, 1, 0, P, leq, one, p, t1, t2] @ env) \<and>
               sats(M, Exists(And(is_eclose_fm(2, 0), is_frecrel_fm(0, 1))), [xc, xb, 1, 0, P, leq, one, p, t1, t2] @ env))"
    using uno_in_M by auto
  moreover from \<open>[P,leq,one,p,t1,t2] @ env \<in> list(M)\<close>
  have " ... \<longleftrightarrow> (\<exists>xb\<in>M. \<exists>xc\<in>M.
               sats(M, is_wfrec_fm(is_Hfrc_at_fm(4, 5, 2, 1, 0), 0, 1, 2), [xc, xb, 1, 0, P, leq, one, p, t1, t2] @ env) \<and>
               (\<exists>c1\<in>M. \<exists>c0\<in>M. sats(M, And(pair_fm(11, 9, 0), And(pair_fm(10, 0, 1), pair_fm(5, 1, 3))),
                    [c0, c1, xc, xb, 1, 0, P, leq, one, p, t1, t2] @ env)) \<and>
               sats(M, Exists(And(is_eclose_fm(2, 0), is_frecrel_fm(0, 1))), [xc, xb, 1, 0, P, leq, one, p, t1, t2] @ env))"
    using uno_in_M M_inhabit by simp
  moreover from \<open>[P,leq,one,p,t1,t2] @ env \<in> list(M)\<close>
  have " ... \<longleftrightarrow> (\<exists>xb\<in>M. \<exists>xc\<in>M.
               sats(M, is_wfrec_fm(is_Hfrc_at_fm(4, 5, 2, 1, 0), 0, 1, 2), [xc, xb, 1, 0, P, leq, one, p, t1, t2] @ env) \<and>
               xb = <0,t1,t2,p> \<and> sats(M,pair_fm(5, 1, 3),
                    [<t2,p>, <t1,t2,p>, xc, xb, 1, 0, P, leq, one, p, t1, t2] @ env) \<and>
               sats(M, Exists(And(is_eclose_fm(2, 0), is_frecrel_fm(0, 1))), [xc, xb, 1, 0, P, leq, one, p, t1, t2] @ env))"
    using uno_in_M M_inhabit tuples_in_M by simp
  moreover from \<open>[P,leq,one,p,t1,t2] @ env \<in> list(M)\<close>
  have " ... \<longleftrightarrow> (\<exists>xc\<in>M.
               sats(M, is_wfrec_fm(is_Hfrc_at_fm(4, 5, 2, 1, 0), 0, 1, 2), [xc, <0,t1,t2,p>, 1, 0, P, leq, one, p, t1, t2] @ env) \<and>
               sats(M, Exists(And(is_eclose_fm(2, 0), is_frecrel_fm(0, 1))), [xc, <0,t1,t2,p>, 1, 0, P, leq, one, p, t1, t2] @ env))"
    using uno_in_M M_inhabit tuples_in_M by auto
  moreover from \<open>[P,leq,one,p,t1,t2] @ env \<in> list(M)\<close>
  have " ... \<longleftrightarrow> (\<exists>xc\<in>M.
               sats(M, is_wfrec_fm(is_Hfrc_at_fm(4, 5, 2, 1, 0), 0, 1, 2), [xc, <0,t1,t2,p>, 1, 0, P, leq, one, p, t1, t2] @ env) \<and>
               (\<exists>ec\<in>M. sats(M, is_eclose_fm(2, 0), [ec, xc, <0,t1,t2,p>, 1, 0, P, leq, one, p, t1, t2] @ env)
                    \<and>  sats(M, is_frecrel_fm(0, 1), [ec, xc, <0,t1,t2,p>, 1, 0, P, leq, one, p, t1, t2] @ env)) )"
    using uno_in_M M_inhabit tuples_in_M by simp
  moreover from \<open>[P,leq,one,p,t1,t2] @ env \<in> list(M)\<close> \<open>eclose(<0,t1,t2,p>)\<in>M \<Longrightarrow> frecrel(eclose(<0,t1,t2,p>))\<in>M\<close>
  have " ... \<longleftrightarrow> sats(M, is_wfrec_fm(is_Hfrc_at_fm(4, 5, 2, 1, 0), 0, 1, 2),
                  [frecrel(eclose(<0,t1,t2,p>)), <0,t1,t2,p>, 1, 0, P, leq, one, p, t1, t2] @ env)"
    using uno_in_M M_inhabit tuples_in_M sats_is_frecrel_fm[symmetric] eclose_closed by auto
  ultimately show ?thesis by simp
qed

lemma forces_Nand: "\<lbrakk> [P,leq,one,p] @ env \<in> list(M); \<phi>\<in>formula; \<psi>\<in>formula\<rbrakk> \<Longrightarrow>
          sats(M,forces(Nand(\<phi>,\<psi>)),[P,leq,one,p] @ env) \<longleftrightarrow>
          (\<forall>x\<in>P. \<langle>x, p\<rangle> \<in> leq \<longrightarrow>
          \<not> (sats(M, forces(\<phi>),[\<langle>x, p\<rangle>,x,P,leq,one,p] @ env) \<and>
             sats(M, forces(\<psi>),[\<langle>x, p\<rangle>,x,P,leq,one,p] @ env)))"
  using tuples_in_M Transset_intf[OF trans_M, of _ P] by auto

lemma forces_Neg: "\<lbrakk> [P,leq,one,p] @ env \<in> list(M); \<phi>\<in>formula\<rbrakk> \<Longrightarrow>
          sats(M,forces(Neg(\<phi>)),[P,leq,one,p] @ env) \<longleftrightarrow>
          (\<forall>x\<in>P. \<langle>x, p\<rangle> \<in> leq \<longrightarrow>
          \<not> sats(M, forces(\<phi>),[\<langle>x, p\<rangle>,x,P,leq,one,p] @ env))"
  unfolding Neg_def 
  using tuples_in_M Transset_intf[OF trans_M, of _ P] by auto

end (* context forcing_data *)

locale forces_rename = forcing_data + 
  fixes fren :: "i" and fref :: "i"
  assumes
  fren_action: "[x,q,P,leq,one,p] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> 
      sats(M, fren`\<phi>,[x,q,P,leq,one,p] @ env) \<longleftrightarrow> sats(M, \<phi>,[P,leq,one,q] @ env)"
  and
  fref_action: "[x,P,leq,one,p] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> 
      sats(M, fref`\<phi>,[x,P,leq,one,p] @ env) \<longleftrightarrow> sats(M, \<phi>,[P,leq,one,p,x] @ env)"
  and
  renaming_type [TC]: "\<phi>\<in>formula \<Longrightarrow> fren`\<phi> \<in> formula" "\<phi>\<in>formula \<Longrightarrow> fref`\<phi> \<in> formula"
  and 
  (* The next one will follow by induction *)
  forces_ren_type [TC]: "forces_ren(fren,fref, \<phi>) \<in> formula" 
  and
  frecrel_closed: "x\<in>M \<Longrightarrow> frecrel(x)\<in>M"

begin

lemma sats_forces_ren_Nand: 
  assumes 
    "[P,leq,one,p] @ env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "sats(M,forces_ren(fren,fref,Nand(\<phi>,\<psi>)),[P,leq,one,p] @ env) \<longleftrightarrow>
          (\<forall>x\<in>M. x\<in>P \<longrightarrow> \<langle>x, p\<rangle> \<in> leq \<longrightarrow>
          \<not> (sats(M, forces_ren(fren,fref,\<phi>),[P,leq,one,x] @ env) \<and>
             sats(M, forces_ren(fren,fref,\<psi>),[P,leq,one,x] @ env)))"
proof -
  from assms
  have "sats(M,forces_ren(fren,fref,Nand(\<phi>,\<psi>)),[P,leq,one,p] @ env) \<longleftrightarrow>
          (\<forall>x\<in>M. x\<in>P \<longrightarrow> \<langle>x, p\<rangle> \<in> leq \<longrightarrow>
          \<not> (sats(M, fren`forces_ren(fren,fref,\<phi>),[\<langle>x, p\<rangle>,x,P,leq,one,p] @ env) \<and>
             sats(M, fren`forces_ren(fren,fref,\<psi>),[\<langle>x, p\<rangle>,x,P,leq,one,p] @ env)))"
    using tuples_in_M  by simp
  also from assms
  have "... \<longleftrightarrow> (\<forall>x\<in>M. x\<in>P \<longrightarrow> \<langle>x, p\<rangle> \<in> leq \<longrightarrow>
          \<not> (sats(M, forces_ren(fren,fref,\<phi>),[P,leq,one,x] @ env) \<and>
             sats(M, forces_ren(fren,fref,\<psi>),[P,leq,one,x] @ env)))"
    using tuples_in_M fren_action by simp
  (* also from assms
  have "... \<longleftrightarrow> (\<forall>x\<in>P. \<langle>x, p\<rangle> \<in> leq \<longrightarrow>
          \<not> (sats(M, forces_ren(fren,fref,\<phi>),[P,leq,one,x] @ env) \<and>
             sats(M, forces_ren(fren,fref,\<psi>),[P,leq,one,x] @ env)))"
    using tuples_in_M Transset_intf[OF trans_M, of _ P]  by auto *)
  finally
  show ?thesis .
qed

lemma sats_forces_ren_Neg: "\<lbrakk> [P,leq,one,p] @ env \<in> list(M); \<phi>\<in>formula\<rbrakk> \<Longrightarrow>
          sats(M,forces_ren(fren,fref,Neg(\<phi>)),[P,leq,one,p] @ env) \<longleftrightarrow> 
          (\<forall>q\<in>M. q\<in>P \<longrightarrow> \<langle>q, p\<rangle> \<in> leq \<longrightarrow>
          \<not> sats(M, forces_ren(fren,fref,\<phi>),[P,leq,one,q] @ env))" 
  unfolding Neg_def sats_forces_ren_Nand
  by simp

lemma sats_forces_ren_Forall:
  assumes
    "p\<in>P" "[P,leq,one,p] @ env \<in> list(M)" "\<phi>\<in>formula"
  shows
    "sats(M,forces_ren(fren,fref,Forall(\<phi>)),[P,leq,one,p] @ env) \<longleftrightarrow> 
     (\<forall>x\<in>M. sats(M, forces_ren(fren,fref,\<phi>),[P,leq,one,p,x] @ env))"
  using assms fref_action by simp

lemma sats_forces_ren_Equal:
  assumes
    "p\<in>P" "[P,leq,one,p,x,y] @ env \<in> list(M)" 
  shows
    "sats(M,forces_ren(fren,fref,Equal(0,1)),[P,leq,one,p,x,y] @ env) \<longleftrightarrow> 
     sats(M, is_wfrec_fm(is_Hfrc_at_fm(4, 5, 2, 1, 0), 0, 1, 2),
         [frecrel(eclose(<0,x,y,p>)), <0,x,y,p>, 1, 0, P, leq, one, p, x, y] @ env)"
  using assms sats_forces_eq frecrel_closed by simp

lemma
  assumes
    "p\<in>P" "[P,leq,one,p] @ env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "sats(M,forces_ren(fren,fref,And(\<phi>,\<psi>)),[P,leq,one,p] @ env) \<longleftrightarrow>
      sats(M, forces_ren(fren,fref,\<phi>),[P,leq,one,p] @ env) \<and>
      sats(M, forces_ren(fren,fref,\<psi>),[P,leq,one,p] @ env)"
  oops

end