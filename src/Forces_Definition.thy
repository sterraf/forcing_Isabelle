theory Forces_Definition imports FrecR Synthetic_Definition begin

(* \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x,y) *)
definition
  frecrelP :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
  "frecrelP(M,xy) \<equiv> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,xy) \<and> is_frecR(M,x,y))"

definition
  frecrelP_fm :: "i \<Rightarrow> i" where
  "frecrelP_fm(a) == Exists(Exists(And(pair_fm(1,0,a#+2),frecR_fm(1,0))))"

lemma frecrelP_fm_type[TC] :
  "a\<in>nat \<Longrightarrow> frecrelP_fm(a)\<in>formula" 
  unfolding frecrelP_fm_def by simp

lemma sats_frecrelP_fm :
  assumes "a\<in>nat" "env\<in>list(A)"
  shows "sats(A,frecrelP_fm(a),env) \<longleftrightarrow> frecrelP(##A,nth(a, env))"
  unfolding frecrelP_def frecrelP_fm_def
  using assms by (simp add: sats_frecR_fm)

lemma frecrelP_iff_sats:
  assumes
    "nth(a,env) = aa" "a\<in> nat"  "env \<in> list(A)"
  shows
       "frecrelP(##A,aa)  \<longleftrightarrow> sats(A, frecrelP_fm(a), env)"
  using assms
  by (simp add:sats_frecrelP_fm)

(* {z\<in>A\<times>A. \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x,y)} *)
definition
  is_frecrel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_frecrel(M,A,r) \<equiv> \<exists>A2[M]. cartprod(M,A,A,A2) \<and> is_Collect(M,A2, frecrelP(M) ,r)"

definition
  frecrel_fm :: "[i,i] \<Rightarrow> i" where
  "frecrel_fm(a,r) \<equiv> Exists(And(cartprod_fm(a#+1,a#+1,0),is_Collect_fm(0,frecrelP_fm(0),r#+1)))" 

lemma frecrel_fm_type[TC] :
  "\<lbrakk>a\<in>nat;b\<in>nat\<rbrakk> \<Longrightarrow> frecrel_fm(a,b)\<in>formula"
  unfolding frecrel_fm_def by simp

lemma sats_frecrel_fm :
  assumes 
    "a\<in>nat"  "r\<in>nat" "env\<in>list(A)"
  shows
    "sats(A,frecrel_fm(a,r),env)
    \<longleftrightarrow> is_frecrel(##A,nth(a, env),nth(r, env))"
  unfolding is_frecrel_def frecrel_fm_def
  using assms
  by (simp add:sats_is_Collect_fm sats_frecrelP_fm)

lemma is_frecrel_iff_sats:
  assumes
    "nth(a,env) = aa" "nth(r,env) = rr" "a\<in> nat"  "r\<in> nat"  "env \<in> list(A)"
  shows
       "is_frecrel(##A, aa,rr) \<longleftrightarrow> sats(A, frecrel_fm(a,r), env)"
  using assms
  by (simp add:sats_frecrel_fm)

definition
  names_below :: "i \<Rightarrow> i \<Rightarrow> i" where
  "names_below(P,x) \<equiv> 2\<times>eclose(x)\<times>eclose(x)\<times>P"

definition
  is_names_below :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_names_below(M,P,x,nb) == \<exists>p1[M]. \<exists>p0[M]. \<exists>t[M]. \<exists>ec[M]. 
              is_eclose(M,x,ec) \<and> number2(M,t) \<and> cartprod(M,ec,P,p0) \<and> cartprod(M,ec,p0,p1)
              \<and> cartprod(M,t,p1,nb)"

definition
  number2_fm :: "i\<Rightarrow>i" where
  "number2_fm(a) == Exists(And(number1_fm(0), succ_fm(0,succ(a))))"

lemma number2_fm_type[TC] :
  "a\<in>nat \<Longrightarrow> number2_fm(a) \<in> formula"
  unfolding number2_fm_def by simp

lemma sats_number2_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, number2_fm(x), env) \<longleftrightarrow> number2(##A, nth(x,env))"
by (simp add: number2_fm_def number2_def)

definition 
  is_names_below_fm :: "[i,i,i] \<Rightarrow> i" where
  "is_names_below_fm(P,x,nb) == Exists(Exists(Exists(Exists(
                    And(is_eclose_fm(x #+ 4,0),And(number2_fm(1),
                    And(cartprod_fm(0,P #+ 4,2),And(cartprod_fm(0,2,3),cartprod_fm(1,3,nb#+4)))))))))"

lemma is_names_below_fm_type[TC]:
  "\<lbrakk>P\<in>nat;x\<in>nat;nb\<in>nat\<rbrakk> \<Longrightarrow> is_names_below_fm(P,x,nb)\<in>formula" 
  unfolding is_names_below_fm_def by simp

lemma sats_is_names_below_fm :
  assumes
    "P\<in>nat" "x\<in>nat" "nb\<in>nat" "env\<in>list(A)" 
  shows
    "sats(A,is_names_below_fm(P,x,nb),env)
    \<longleftrightarrow> is_names_below(##A,nth(P, env),nth(x, env),nth(nb, env))" 
   unfolding is_names_below_fm_def is_names_below_def using assms by simp

definition
  is_tuple :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_tuple(M,z,t1,t2,p,t) == \<exists>t1t2p[M]. \<exists>t2p[M]. pair(M,t2,p,t2p) \<and> pair(M,t1,t2p,t1t2p) \<and>
                                                  pair(M,z,t1t2p,t)" 


definition
  is_tuple_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "is_tuple_fm(z,t1,t2,p,tup) = Exists(Exists(And(pair_fm(t2 #+ 2,p #+ 2,0),
                      And(pair_fm(t1 #+ 2,0,1),pair_fm(z #+ 2,1,tup #+ 2)))))"

lemma is_tuple_fm_type[TC] : 
  "z\<in>nat \<Longrightarrow> t1\<in>nat \<Longrightarrow> t2\<in>nat \<Longrightarrow> p\<in>nat \<Longrightarrow> tup\<in>nat \<Longrightarrow> is_tuple_fm(z,t1,t2,p,tup)\<in>formula" 
  unfolding is_tuple_fm_def by simp

lemma sats_is_tuple_fm :
  assumes
    "z\<in>nat"  "t1\<in>nat" "t2\<in>nat" "p\<in>nat" "tup\<in>nat" "env\<in>list(A)"
  shows
    "sats(A,is_tuple_fm(z,t1,t2,p,tup),env)
    \<longleftrightarrow> is_tuple(##A,nth(z, env),nth(t1, env),nth(t2, env),nth(p, env),nth(tup, env))"
  unfolding is_tuple_def is_tuple_fm_def using assms by simp

lemma is_tuple_iff_sats:
  assumes
    "nth(a,env) = aa" "nth(b,env) = bb" "nth(c,env) = cc" "nth(d,env) = dd" "nth(e,env) = ee"
    "a\<in>nat" "b\<in>nat" "c\<in>nat" "d\<in>nat" "e\<in>nat"  "env \<in> list(A)"
  shows
       "is_tuple(##A,aa,bb,cc,dd,ee)  \<longleftrightarrow> sats(A, is_tuple_fm(a,b,c,d,e), env)"
  using assms by (simp add: sats_is_tuple_fm)

(* Definition of forces for equality and membership *)

(* p ||- \<tau> = \<theta> \<equiv>
  \<forall>\<sigma>. \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<longrightarrow> (\<forall>q\<in>P. <q,p>\<in>leq \<longrightarrow> ((q ||- \<sigma>\<in>\<tau>) \<longleftrightarrow> (q ||- \<sigma>\<in>\<theta>)) ) *)
definition
  eq_case :: "[i,i,i,i,i,i] \<Rightarrow> o" where
  "eq_case(t1,t2,p,P,leq,f) \<equiv> \<forall>s. s\<in>domain(t1) \<union> domain(t2) \<longrightarrow>
      (\<forall>q. q\<in>P \<and> <q,p>\<in>leq \<longrightarrow> (f`<1,s,t1,q>=1  \<longleftrightarrow> f`<1,s,t2,q> =1))"


definition
  is_eq_case :: "[i\<Rightarrow>o,i,i,i,i,i,i] \<Rightarrow> o" where
  "is_eq_case(M,t1,t2,p,P,leq,f) \<equiv>
   \<forall>s[M]. (\<exists>d[M]. is_domain(M,t1,d) \<and> s\<in>d) \<or> (\<exists>d[M]. is_domain(M,t2,d) \<and> s\<in>d)
       \<longrightarrow> (\<forall>q[M]. q\<in>P \<and> (\<exists>qp[M]. pair(M,q,p,qp) \<and> qp\<in>leq) \<longrightarrow>
            (\<exists>ost1q[M]. \<exists>ost2q[M]. \<exists>o[M].  \<exists>vf1[M]. \<exists>vf2[M].
             is_tuple(M,o,s,t1,q,ost1q) \<and>
             is_tuple(M,o,s,t2,q,ost2q) \<and> number1(M,o) \<and> 
             fun_apply(M,f,ost1q,vf1) \<and> fun_apply(M,f,ost2q,vf2) \<and>
             (vf1 = o \<longleftrightarrow> vf2 = o)))"

(* p ||-
   \<pi> \<in> \<tau> \<equiv> \<forall>v\<in>P. <v,p>\<in>leq \<longrightarrow> (\<exists>q\<in>P. <q,v>\<in>leq \<and> (\<exists>\<sigma>. \<exists>r\<in>P. <\<sigma>,r>\<in>\<tau> \<and> <q,r>\<in>leq \<and>  q ||- \<pi> = \<sigma>)) *)
definition
  mem_case :: "[i,i,i,i,i,i] \<Rightarrow> o" where
  "mem_case(t1,t2,p,P,leq,f) \<equiv> \<forall>v\<in>P. <v,p>\<in>leq \<longrightarrow>
    (\<exists>q. \<exists>s. \<exists>r. r\<in>P \<and> q\<in>P \<and> <q,v>\<in>leq \<and> <s,r> \<in> t2 \<and> <q,r>\<in>leq \<and>  f`<0,t1,s,q> = 1)"

definition
  is_mem_case :: "[i\<Rightarrow>o,i,i,i,i,i,i] \<Rightarrow> o" where
  "is_mem_case(M,t1,t2,p,P,leq,f) \<equiv> \<forall>v[M]. \<forall>vp[M]. v\<in>P \<and> pair(M,v,p,vp) \<and> vp\<in>leq \<longrightarrow>
    (\<exists>q[M]. \<exists>qv[M]. \<exists>s[M]. \<exists>r[M]. \<exists>sr[M]. \<exists>qr[M]. \<exists>z[M]. \<exists>zt1sq[M]. \<exists>o[M].
     r\<in> P \<and> q\<in>P \<and> pair(M,q,v,qv) \<and> pair(M,s,r,sr) \<and> pair(M,q,r,qr) \<and> 
     empty(M,z) \<and> is_tuple(M,z,t1,s,q,zt1sq) \<and>
     number1(M,o) \<and> sr\<in>t2 \<and> qv\<in>leq \<and> qr\<in>leq \<and> fun_apply(M,f,zt1sq,o))"


schematic_goal sats_is_mem_case_fm_auto:
  assumes 
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "is_mem_case(##A, nth(n1, env),nth(n2, env),nth(p, env),nth(P, env), nth(leq, env),nth(f,env))
    \<longleftrightarrow> sats(A,?imc_fm(n1,n2,p,P,leq,f),env)"
   unfolding is_mem_case_def 
   by (insert assms ; (rule sep_rules'  is_tuple_iff_sats | simp)+)


synthesize "mem_case_fm" from_schematic "sats_is_mem_case_fm_auto"


schematic_goal sats_is_eq_case_fm_auto:
  assumes 
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "is_eq_case(##A, nth(n1, env),nth(n2, env),nth(p, env),nth(P, env), nth(leq, env),nth(f,env))
    \<longleftrightarrow> sats(A,?iec_fm(n1,n2,p,P,leq,f),env)"
  unfolding is_eq_case_def
    by (insert assms ; (rule sep_rules'  is_tuple_iff_sats | simp)+)

synthesize "eq_case_fm" from_schematic "sats_is_eq_case_fm_auto"


lemma mem_case_fm_type[TC] :
  "\<lbrakk>n1\<in>nat;n2\<in>nat;p\<in>nat;P\<in>nat;leq\<in>nat;f\<in>nat\<rbrakk> \<Longrightarrow> mem_case_fm(n1,n2,p,P,leq,f)\<in>formula"
  unfolding mem_case_fm_def by simp

lemma eq_case_fm_type[TC] :
  "\<lbrakk>n1\<in>nat;n2\<in>nat;p\<in>nat;P\<in>nat;leq\<in>nat;f\<in>nat\<rbrakk> \<Longrightarrow> eq_case_fm(n1,n2,p,P,leq,f)\<in>formula"
  unfolding eq_case_fm_def by simp

lemma sats_eq_case_fm :
  assumes 
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "sats(A,eq_case_fm(n1,n2,p,P,leq,f),env) \<longleftrightarrow> 
    is_eq_case(##A, nth(n1, env),nth(n2, env),nth(p, env),nth(P, env), nth(leq, env),nth(f,env))"
  unfolding eq_case_fm_def is_eq_case_def using assms by (simp add: sats_is_tuple_fm)

lemma sats_mem_case_fm :
  assumes 
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "sats(A,mem_case_fm(n1,n2,p,P,leq,f),env) \<longleftrightarrow> 
    is_mem_case(##A, nth(n1, env),nth(n2, env),nth(p, env),nth(P, env), nth(leq, env),nth(f,env))"
  unfolding mem_case_fm_def is_mem_case_def using assms by (simp add: sats_is_tuple_fm)

lemma mem_case_iff_sats:
  assumes
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"    
    "nth(n1,env) = nn1" "nth(n2,env) = nn2" "nth(p,env) = pp" "nth(P,env) = PP" 
    "nth(leq,env) = lleq" "nth(f,env) = ff"  
  shows
    "is_mem_case(##A, nn1,nn2,pp,PP, lleq,ff)
    \<longleftrightarrow> sats(A,mem_case_fm(n1,n2,p,P,leq,f),env)"
  using assms
  by (simp add:sats_mem_case_fm)

lemma eq_case_iff_sats :
  assumes
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"    
    "nth(n1,env) = nn1" "nth(n2,env) = nn2" "nth(p,env) = pp" "nth(P,env) = PP" 
    "nth(leq,env) = lleq" "nth(f,env) = ff"  
  shows
    "is_eq_case(##A, nn1,nn2,pp,PP, lleq,ff)
    \<longleftrightarrow> sats(A,eq_case_fm(n1,n2,p,P,leq,f),env)"
  using assms
  by (simp add:sats_eq_case_fm)

definition
  Hfrc :: "[i,i,i,i] \<Rightarrow> o" where
  "Hfrc(P,leq,fnnc,f) \<equiv> \<exists>ft. \<exists>n1. \<exists>n2. \<exists>c. c\<in>P \<and> fnnc = <ft,n1,n2,c> \<and>
     (  ft = 0 \<and>  eq_case(n1,n2,c,P,leq,f)
      \<or> ft = 1 \<and> mem_case(n1,n2,c,P,leq,f))"

definition
  is_Hfrc :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_Hfrc(M,P,leq,fnnc,f) \<equiv>
     \<exists>ft[M]. \<exists>n1[M]. \<exists>n2[M]. \<exists>co[M]. 
      co\<in>P \<and> is_tuple(M,ft,n1,n2,co,fnnc) \<and>
      (  (empty(M,ft) \<and> is_eq_case(M,n1,n2,co,P,leq,f))
       \<or> (number1(M,ft) \<and>  is_mem_case(M,n1,n2,co,P,leq,f)))"

definition 
  Hfrc_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "Hfrc_fm(P,leq,fnnc,f) \<equiv> 
    Exists(Exists(Exists(Exists(
      And(Member(0,P #+ 4),And(is_tuple_fm(3,2,1,0,fnnc #+ 4),
      Or(And(empty_fm(3),eq_case_fm(2,1,0,P #+ 4,leq #+ 4,f #+ 4)),
         And(number1_fm(3),mem_case_fm(2,1,0,P #+ 4,leq #+ 4,f #+ 4)))))))))"

lemma Hfrc_fm_type[TC] :
  "\<lbrakk>P\<in>nat;leq\<in>nat;fnnc\<in>nat;f\<in>nat\<rbrakk> \<Longrightarrow> Hfrc_fm(P,leq,fnnc,f)\<in>formula"
  unfolding Hfrc_fm_def by simp

lemma sats_Hfrc_fm:
  assumes 
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "sats(A,Hfrc_fm(P,leq,fnnc,f),env)
    \<longleftrightarrow> is_Hfrc(##A,nth(P, env), nth(leq, env), nth(fnnc, env),nth(f, env))"
  unfolding is_Hfrc_def Hfrc_fm_def 
  using assms
  by (simp add:sats_eq_case_fm sats_is_tuple_fm sats_mem_case_fm)

schematic_goal Hfrc_iff_sats:
  assumes
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "env\<in>list(A)"    
    "nth(P,env) = PP"  "nth(leq,env) = lleq" "nth(fnnc,env) = ffnnc" "nth(f,env) = ff" 
  shows
    "is_Hfrc(##A, PP, lleq,ffnnc,ff)
    \<longleftrightarrow> sats(A,Hfrc_fm(P,leq,fnnc,f),env)"
  using assms
  by (simp add:sats_Hfrc_fm)
                              
definition
  is_Hfrc_at :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_Hfrc_at(M,P,leq,fnnc,f,z) \<equiv> 
            (empty(M,z) \<and> \<not> is_Hfrc(M,P,leq,fnnc,f))
          \<or> (number1(M,z) \<and> is_Hfrc(M,P,leq,fnnc,f))"

definition
  Hfrc_at_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "Hfrc_at_fm(P,leq,fnnc,f,z) \<equiv> Or(And(empty_fm(z),Neg(Hfrc_fm(P,leq,fnnc,f))),
                                      And(number1_fm(z),Hfrc_fm(P,leq,fnnc,f)))" 

lemma Hfrc_at_fm_type[TC] :
  "\<lbrakk>P\<in>nat;leq\<in>nat;fnnc\<in>nat;f\<in>nat;z\<in>nat\<rbrakk> \<Longrightarrow> Hfrc_at_fm(P,leq,fnnc,f,z)\<in>formula"
  unfolding Hfrc_at_fm_def by simp

lemma sats_Hfrc_at_fm:
  assumes 
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "z\<in>nat" "env\<in>list(A)"
  shows
    "sats(A,Hfrc_at_fm(P,leq,fnnc,f,z),env)
    \<longleftrightarrow> is_Hfrc_at(##A,nth(P, env), nth(leq, env), nth(fnnc, env),nth(f, env),nth(z, env))"
  unfolding is_Hfrc_at_def Hfrc_at_fm_def using assms sats_Hfrc_fm
  by simp

lemma is_Hfrc_at_iff_sats:
  assumes
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "z\<in>nat" "env\<in>list(A)"    
    "nth(P,env) = PP"  "nth(leq,env) = lleq" "nth(fnnc,env) = ffnnc" 
    "nth(f,env) = ff" "nth(z,env) = zz"
  shows
    "is_Hfrc_at(##A, PP, lleq,ffnnc,ff,zz)
    \<longleftrightarrow> sats(A,Hfrc_at_fm(P,leq,fnnc,f,z),env)"
  using assms by (simp add:sats_Hfrc_at_fm)

definition
  frc_at :: "[i,i,i] \<Rightarrow> i" where
  "frc_at(P,leq,fnnc) \<equiv> wfrec(frecrel(names_below(P,fnnc)),fnnc,\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"

definition
  tran_closure_fm :: "i\<Rightarrow>i\<Rightarrow>i" where
  "tran_closure_fm(i,j) ==
Exists
         (And(Forall
               (Implies
                 (field_fm(succ(succ(i)), 0),
                  Forall
                   (Iff(Member(0, 2),
                        Exists
                         (And(omega_fm(0),
                              Exists
                               (And(Member(0, 1),
                                    Exists
                                     (And(succ_fm(1, 0),
                                          Exists
                                           (And(typed_function_fm(1, 5, 0),
                                                And(Exists
                                                     (Exists
 (And(pair_fm(1, 0, 6), Exists(And(empty_fm(0), And(fun_apply_fm(3, 0, 2), fun_apply_fm(3, 5, 1))))))),
                                                    Forall
                                                     (Implies
 (Member(0, 3),
  Exists
   (And(fun_apply_fm(2, 1, 0),
        Exists
         (And(succ_fm(2, 0),
              Exists
               (And(fun_apply_fm(4, 1, 0),
                    Exists
                     (And(pair_fm(3, 1, 0),
                          Member
                           (0, succ(succ(succ(succ(succ(succ
   (succ(succ(succ(succ(succ(succ(i)))))))))))))))))))))))))))))))))))),
              composition_fm(succ(i), 0, succ(j))))"

lemma tran_closure_fm_type[TC] :
  "\<lbrakk>x\<in>nat;f\<in>nat\<rbrakk> \<Longrightarrow> tran_closure_fm(x,f)\<in>formula"
  unfolding tran_closure_fm_def by simp

lemma sats_tran_closure_fm :
  assumes
    "i\<in>nat"  "j\<in>nat" "env\<in>list(A)"
  shows
    "tran_closure(##A,nth(i, env),nth(j, env))
    \<longleftrightarrow> sats(A,tran_closure_fm(i,j),env)"
  unfolding tran_closure_fm_def tran_closure_def rtran_closure_def rtran_closure_mem_def using assms 
  by simp

definition
  forcerel_fm :: "i\<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "forcerel_fm(p,x,z) == Exists(Exists(And(tran_closure_fm(1, z#+2),
                                        And(is_names_below_fm(p#+2,x#+2,0),frecrel_fm(0,1)))))"

lemma forcerel_fm_type[TC]: 
  "\<lbrakk>p\<in>nat;x\<in>nat;z\<in>nat\<rbrakk> \<Longrightarrow> forcerel_fm(p,x,z)\<in>formula" 
  unfolding forcerel_fm_def by simp

(* is_frc_at(x,z) \<equiv> is_wfrec(##M,is_Hfrc_at(##M,P,leq),forcerel(x),x,z) *)
definition
  frc_at_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "frc_at_fm(p,l,x,z) == Exists(And(forcerel_fm(succ(p),succ(x),0),
          is_wfrec_fm(Hfrc_at_fm(6#+p,6#+l,2,1,0),0,succ(x),succ(z))))"

lemma frc_at_fm_type [TC] :
  "\<lbrakk>p\<in>nat;l\<in>nat;x\<in>nat;z\<in>nat\<rbrakk> \<Longrightarrow> frc_at_fm(p,l,x,z)\<in>formula"
  unfolding frc_at_fm_def by simp

(* \<exists>o\<in>M. \<exists>z\<in>M. \<exists>t\<in>M. number1(##M,o) \<and> empty(##M,z) \<and> 
                                is_tuple(##M,z,t1,t2,p,t) \<and> is_frc_at(t,o) *)
definition
  forces_eq_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "forces_eq_fm(p,l,q,t1,t2) \<equiv> 
     Exists(Exists(Exists(And(number1_fm(2),And(empty_fm(1),
              And(is_tuple_fm(1,t1#+3,t2#+3,q#+3,0),frc_at_fm(p#+3,l#+3,0,2) ))))))"

(* \<exists>o\<in>M. \<exists>t\<in>M. number1(##M,o) \<and>  
                                is_tuple(##M,o,t1,t2,p,t) \<and> is_frc_at(t,o)*)
definition
  forces_mem_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "forces_mem_fm(p,l,q,t1,t2) \<equiv> Exists(Exists(And(number1_fm(1),
                          And(is_tuple_fm(1,t1#+2,t2#+2,q#+2,0),frc_at_fm(p#+2,l#+2,0,1)))))"

lemma forces_eq_fm_type [TC]:
  "\<lbrakk> p\<in>nat;l\<in>nat;q\<in>nat;t1\<in>nat;t2\<in>nat\<rbrakk> \<Longrightarrow> forces_eq_fm(p,l,q,t1,t2) \<in> formula"
  unfolding forces_eq_fm_def 
  by simp

lemma forces_mem_fm_type [TC]:
  "\<lbrakk> p\<in>nat;l\<in>nat;q\<in>nat;t1\<in>nat;t2\<in>nat\<rbrakk> \<Longrightarrow> forces_mem_fm(p,l,q,t1,t2) \<in> formula"
  unfolding forces_mem_fm_def
  by simp


(*
lemma arity_forces_eq_fm [simp]:
  "\<lbrakk>\<And>x. x\<in>formula \<Longrightarrow> arity(r(x)) = arity(x) \<rbrakk> \<Longrightarrow> t1 \<in> nat \<Longrightarrow> t2 \<in> nat \<Longrightarrow> arity(forces_eq_fm(r,t1,t2)) = (t1 \<union> t2) #+ 5"
  unfolding forces_eq_fm_def number1_fm_def is_Hfrc_at_fm_def is_tuple_fm_def
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

lemma arity_forces_mem_fm [simp]:
  "t1 \<in> nat \<Longrightarrow> t2 \<in> nat \<Longrightarrow> arity(forces_mem_fm(t1,t2)) = (t1 \<union> t2) #+ 5"
  unfolding forces_mem_fm_def number1_fm_def is_Hfrc_at_fm_def is_tuple_fm_def
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
*)

context forcing_data
begin

(* Absoluteness of components *)
lemma fst_abs [simp]:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_fst(##M,x,y) \<longleftrightarrow> y = fst(x)"
  unfolding fst_def is_fst_def using pair_in_M_iff zero_in_M
  by (auto;rule_tac the_0 the_0[symmetric],auto)

lemma snd_abs [simp]:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_snd(##M,x,y) \<longleftrightarrow> y = snd(x)"
  unfolding snd_def is_snd_def using pair_in_M_iff zero_in_M
  by (auto;rule_tac the_0 the_0[symmetric],auto)

lemma ftype_abs[simp] :
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_ftype(##M,x,y) \<longleftrightarrow> y = ftype(x)" unfolding ftype_def  is_ftype_def by simp

lemma name1_abs[simp] :
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_name1(##M,x,y) \<longleftrightarrow> y = name1(x)"
  unfolding name1_def is_name1_def
  by (rule hcomp_abs[OF fst_abs];simp_all add:fst_snd_closed)

lemma snd_snd_abs:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_snd_snd(##M,x,y) \<longleftrightarrow> y = snd(snd(x))"
  unfolding is_snd_snd_def
  by (rule hcomp_abs[OF snd_abs];simp_all add:fst_snd_closed)

lemma name2_abs[simp]:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_name2(##M,x,y) \<longleftrightarrow> y = name2(x)"
  unfolding name2_def is_name2_def
  by (rule hcomp_abs[OF fst_abs snd_snd_abs];simp_all add:fst_snd_closed)

lemma cond_of_abs[simp]:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_cond_of(##M,x,y) \<longleftrightarrow> y = cond_of(x)"
  unfolding cond_of_def is_cond_of_def
  by (rule hcomp_abs[OF snd_abs snd_snd_abs];simp_all add:fst_snd_closed)

lemma tuple_abs[simp]:
  "\<lbrakk>z\<in>M;t1\<in>M;t2\<in>M;p\<in>M;t\<in>M\<rbrakk> \<Longrightarrow> 
   is_tuple(##M,z,t1,t2,p,t) \<longleftrightarrow> t = <z,t1,t2,p>" 
  unfolding is_tuple_def using tuples_in_M by simp

lemma in_domain: "y\<in>M \<Longrightarrow> x\<in>domain(y) \<Longrightarrow> x\<in>M"
  using domainE[of x y] trans_M Transset_intf[of M _ y] pair_in_M_iff by auto

lemma comp_in_M:
  "<p,q>\<in>leq \<Longrightarrow> p\<in>M"
  "<p,q>\<in>leq \<Longrightarrow> q\<in>M"
  using leq_in_M trans_M Transset_intf[of M _ leq] pair_in_M_iff by auto

(* Absoluteness of Hfrc *)

lemma eq_case_abs [simp]:
  assumes
    "t1\<in>M" "t2\<in>M" "p\<in>M" "f\<in>M" 
  shows
    "is_eq_case(##M,t1,t2,p,P,leq,f) \<longleftrightarrow> eq_case(t1,t2,p,P,leq,f)"
proof -
  have "\<langle>q,p\<rangle>\<in>leq \<Longrightarrow> q\<in>M" for q
    using comp_in_M by simp
  moreover
  have "\<langle>s,y\<rangle>\<in>t \<Longrightarrow> s\<in>M" if "t\<in>M" for s y t
    using that trans_M Transset_intf[of M _ t] pair_in_M_iff by auto
  moreover
  have "\<langle>s,y\<rangle>\<in>t \<Longrightarrow> s\<in>domain(t)" if "t\<in>M" for s y t
    using that unfolding domain_def by auto
  ultimately
  have 
    "(\<forall>s\<in>M. s \<in> domain(t1) \<or> s \<in> domain(t2) \<longrightarrow> (\<forall>q\<in>M. q\<in>P \<and> \<langle>q, p\<rangle> \<in> leq \<longrightarrow> 
                              (f ` \<langle>1, s, t1, q\<rangle> =1 \<longleftrightarrow> f ` \<langle>1, s, t2, q\<rangle>=1))) \<longleftrightarrow>
    (\<forall>s. s \<in> domain(t1) \<or> s \<in> domain(t2) \<longrightarrow> (\<forall>q. q\<in>P \<and> \<langle>q, p\<rangle> \<in> leq \<longrightarrow> 
                                  (f ` \<langle>1, s, t1, q\<rangle> =1 \<longleftrightarrow> f ` \<langle>1, s, t2, q\<rangle>=1)))" 
    using assms by auto
  then show ?thesis
    unfolding eq_case_def is_eq_case_def 
    using assms pair_in_M_iff n_in_M[of 1] domain_closed tuples_in_M 
      apply_closed leq_in_M
    by simp
qed

lemma mem_case_abs [simp]:
  assumes
    "t1\<in>M" "t2\<in>M" "p\<in>M" "f\<in>M" 
  shows
    "is_mem_case(##M,t1,t2,p,P,leq,f) \<longleftrightarrow> mem_case(t1,t2,p,P,leq,f)"
  sorry
(*
lemma mem_case_abs [simp]:
  "\<lbrakk>(##M)(t1); (##M)(t2); (##M)(p); (##M)(f)\<rbrakk> \<Longrightarrow> 
      is_mem_case(##M,t1,t2,p,P,leq,f) \<longleftrightarrow> mem_case(t1,t2,p,P,leq,f)"
  unfolding mem_case_def is_mem_case_def
  using pair_in_M_iff zero_in_M n_in_M[of 1]
  apply (simp del:setclass_iff rall_setclass_is_ball)
  apply (unfold rall_def)
  apply (intro iffI allI impI)
  apply (drule_tac x=v in spec)
  apply (subgoal_tac "(##M)(v)")
    apply (drule mp, assumption)+
    apply blast
  apply (simp add: comp_in_M(1) del:setclass_iff rall_setclass_is_ball)
  apply (drule_tac x=x in spec)
  apply (blast intro:comp_in_M)
  done
*)

lemma Hfrc_abs:
  "\<lbrakk>fnnc\<in>M; f\<in>M\<rbrakk> \<Longrightarrow>
   is_Hfrc(##M,P,leq,fnnc,f) \<longleftrightarrow> Hfrc(P,leq,fnnc,f)"
  unfolding is_Hfrc_def Hfrc_def using pair_in_M_iff
  by auto

lemma Hfrc_at_abs:
  "\<lbrakk>fnnc\<in>M; f\<in>M ; z\<in>M\<rbrakk> \<Longrightarrow>
   is_Hfrc_at(##M,P,leq,fnnc,f,z) \<longleftrightarrow>  z = bool_of_o(Hfrc(P,leq,fnnc,f)) "
  unfolding is_Hfrc_at_def using Hfrc_abs
  by auto

lemma components_closed :
  "x\<in>M \<Longrightarrow> ftype(x)\<in>M"
  "x\<in>M \<Longrightarrow> name1(x)\<in>M"
  "x\<in>M \<Longrightarrow> name2(x)\<in>M"
  "x\<in>M \<Longrightarrow> cond_of(x)\<in>M"
  unfolding ftype_def name1_def name2_def cond_of_def using fst_snd_closed by simp_all

lemma frecR_abs :
  "x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> frecR(x,y) \<longleftrightarrow> is_frecR(##M,x,y)" 
  unfolding frecR_def is_frecR_def using components_closed domain_closed by simp

lemma frecrelP_abs :
    "z\<in>M \<Longrightarrow> frecrelP(##M,z) \<longleftrightarrow> (\<exists>x y. z = <x,y> \<and> frecR(x,y))"
  using pair_in_M_iff frecR_abs unfolding frecrelP_def by auto

lemma frecrel_abs:
  assumes 
   "A\<in>M" "r\<in>M"
 shows
   "is_frecrel(##M,A,r) \<longleftrightarrow>  r = frecrel(A)"
proof -
  from \<open>A\<in>M\<close>
  have "z\<in>M" if "z\<in>A\<times>A" for z
    using cartprod_closed Transset_intf[OF trans_M] that by simp
  then
  have "Collect(A\<times>A,frecrelP(##M)) = Collect(A\<times>A,\<lambda>z. (\<exists>x y. z = <x,y> \<and> frecR(x,y)))"
    using Collect_cong[of "A\<times>A" "A\<times>A" "frecrelP(##M)"] assms frecrelP_abs by simp
  with assms
  show ?thesis unfolding is_frecrel_def def_frecrel using cartprod_closed
    by simp
qed

lemma frecrel_closed:
  assumes 
   "x\<in>M" 
 shows
   "frecrel(x)\<in>M" 
  unfolding frecrel_def frecR_def Rrel_def
  sorry

(* transitive relation of forces for atomic formulas *)
definition
  forcerel :: "i \<Rightarrow> i" where
  "forcerel(x) \<equiv> frecrel(names_below(P,x))^+"

lemma wf_forcerel :
  "wf(forcerel(x))"
  unfolding forcerel_def using wf_trancl wf_frecrel .

lemma restrict_trancl_forcerel:
  assumes "frecR(w,y)"
  shows "restrict(f,frecrel(names_below(P,x))-``{y})`w
       = restrict(f,(frecrel(names_below(P,x))^+)-``{y})`w" 
  unfolding forcerel_def frecrel_def using assms restrict_trancl_Rrel[of frecR] 
     by (simp)

lemma names_belowI : 
  assumes "frecR(<ft,n1,n2,p>,<a,b,c,d>)" "p\<in>P"
  shows "<ft,n1,n2,p> \<in> names_below(P,<a,b,c,d>)" (is "?x \<in> names_below(_,?y)")
proof -
  from assms
  have "ft \<in> 2" "a \<in> 2" 
    unfolding frecR_def by (auto simp add:components_simp)
  have A: "b \<in> eclose(?y) " "c \<in> eclose(?y)" 
    using components_in_eclose by simp_all
  from assms
  consider (e) "n1 \<in> domain(b) \<union> domain(c) \<and> (n2 = b \<or> n2 =c)" 
    | (m) "n1 = b \<and> n2 \<in> domain(c)"
    unfolding frecR_def by (auto simp add:components_simp)
  then show ?thesis 
  proof cases
    case e
    then 
    have "n1 \<in> eclose(b) \<or> n1 \<in> eclose(c)"  
      using Un_iff in_dom_in_eclose by auto
    with e
    have "n1 \<in> eclose(?y)" "n2 \<in> eclose(?y)"
      using mem_eclose_trans components_in_eclose by auto
    with A \<open>ft\<in>2\<close> \<open>p\<in>P\<close> 
    show ?thesis unfolding names_below_def by  auto
  next
    case m
    then
    have "n1 \<in> eclose(?y)" "n2 \<in> eclose(c)"
      using mem_eclose_trans in_dom_in_eclose components_in_eclose by auto
    with A \<open>ft\<in>2\<close> \<open>p\<in>P\<close> 
    show ?thesis unfolding names_below_def using mem_eclose_trans by auto    
  qed
qed

lemmas names_belowI' = names_belowI[OF frecRI1] names_belowI[OF frecRI2] names_belowI[OF frecRI3] 

lemma Hfrc_restrict_trancl: "bool_of_o(Hfrc(P, leq, y, restrict(f,frecrel(names_below(P,x))-``{y})))
         = bool_of_o(Hfrc(P, leq, y, restrict(f,(frecrel(names_below(P,x))^+)-``{y})))"
  unfolding Hfrc_def bool_of_o_def eq_case_def mem_case_def 
  using  restrict_trancl_forcerel frecRI1 frecRI2 frecRI3 by simp


(* Recursive definition of forces for atomic formulas using a transitive relation *)
lemma frc_at_trancl: "frc_at(P,leq,z) = wfrec(forcerel(z),z,\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"
proof -
  have "frc_at(P,leq,z) = wfrec(frecrel(names_below(P,z)),z,\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"
    (is "_ = wfrec(?r,_,?H)")
    unfolding frc_at_def ..
  also
  have " ... = wftrec(?r^+, z, \<lambda>y f. ?H(y, restrict(f,?r-``{y})))"
    unfolding wfrec_def ..
  also
  have " ... = wftrec(?r^+, z, \<lambda>y f. ?H(y, restrict(f,(?r^+)-``{y})))"
    using Hfrc_restrict_trancl by simp
  also
  have " ... =  wfrec(?r^+, z, ?H)"
    unfolding wfrec_def using trancl_eq_r[OF relation_trancl trans_trancl] by simp
  finally
  show ?thesis unfolding forcerel_def .
qed


(* frecrel(names_below(P,x)) *)
definition
  is_forcerel :: "i \<Rightarrow> i \<Rightarrow> o" where
  "is_forcerel(x,z) == \<exists>r\<in>M. \<exists>nb\<in>M. tran_closure(##M,r,z) \<and> 
                        (is_names_below(##M,P,x,nb) \<and> is_frecrel(##M,nb,r))"

lemma sats_forcerel_fm:
  assumes
    "p\<in>nat" "x\<in>nat"  "z\<in>nat" "env\<in>list(M)" "nth(p,env) = P" 
  shows
    "sats(M,forcerel_fm(p,x,z),env) \<longleftrightarrow> is_forcerel(nth(x, env),nth(z, env))"
proof -
  have "sats(M,tran_closure_fm(1,z #+ 2),Cons(nb,Cons(r,env))) \<longleftrightarrow>
        tran_closure(##M, r, nth(z, env))" if "r\<in>M" "nb\<in>M" for r nb
    using that assms sats_tran_closure_fm[of 1 "z #+ 2" "[nb,r]@env"] by simp
  moreover
  have "sats(M, is_names_below_fm(succ(succ(p)), succ(succ(x)), 0), Cons(nb, Cons(r, env))) \<longleftrightarrow>
        is_names_below(##M, P, nth(x, env), nb)"
    if "r\<in>M" "nb\<in>M" for nb r
    using assms that sats_is_names_below_fm[of "p #+ 2" "x #+ 2" 0 "[nb,r]@env"] by simp
  moreover
  have "sats(M, frecrel_fm(0, 1), Cons(nb, Cons(r, env))) \<longleftrightarrow> 
        is_frecrel(##M, nb, r)"
    if "r\<in>M" "nb\<in>M" for r nb
    using assms that sats_frecrel_fm[of 0 1 "[nb,r]@env"] by simp
  ultimately
  show ?thesis using assms  unfolding is_forcerel_def forcerel_fm_def by simp
qed

(* Don't know if this is true *)
lemma  aux_def_frc_at: "x\<in>names_below(P,y) \<Longrightarrow>
  wfrec(forcerel(y), x, H) =  wfrec(forcerel(x), x, H)"
  sorry

(* This is NOT true (though it might be with \<subseteq>) *)
lemma vimage_forcerel: "forcerel(\<langle>ft,n1,n2,p\<rangle>) -`` {\<langle>ft,n1,n2,p\<rangle>} = names_below(P,\<langle>ft,n1,n2,p\<rangle>)"
  sorry

lemma def_frc_at : "frc_at(P,leq,<ft,n1,n2,p>) = 
   bool_of_o( p \<in>P \<and> 
  (  ft = 0 \<and>  (\<forall>s. s\<in>domain(n1) \<union> domain(n2) \<longrightarrow>
        (\<forall>q. q\<in>P \<and> <q,p>\<in>leq \<longrightarrow> (frc_at(P,leq,<1,s,n1,q>) =1 \<longleftrightarrow> frc_at(P,leq,<1,s,n2,q>) =1)))
   \<or> ft = 1 \<and> ( \<forall>v\<in>P. <v,p>\<in>leq \<longrightarrow>
    (\<exists>q. \<exists>s. \<exists>r. r\<in>P \<and> q\<in>P \<and> <q,v>\<in>leq \<and> <s,r> \<in> n2 \<and> <q,r>\<in>leq \<and>  frc_at(P,leq,<0,n1,s,q>) = 1))))"
proof -
  let ?r="\<lambda>y. forcerel(y)" and ?Hf="\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f))"
  let ?arg="<ft,n1,n2,p>"
  from wf_forcerel 
  have wfr: "\<forall>w . wf(?r(w))" ..
  with wfrec [of "?r(?arg)" ?arg ?Hf] 
  have "frc_at(P,leq,?arg) = ?Hf( ?arg, \<lambda>x\<in>?r(?arg) -`` {?arg}. wfrec(?r(?arg), x, ?Hf))"
    unfolding frc_at_trancl by simp 
  also
  have " ... = ?Hf( ?arg, \<lambda>x\<in>names_below(P,?arg). wfrec(?r(?arg), x, ?Hf))"
    using vimage_forcerel by simp
  also
  have " ... = ?Hf( ?arg, \<lambda>x\<in>names_below(P,?arg). frc_at(P,leq,x))"
    using aux_def_frc_at unfolding frc_at_trancl by simp
  finally 
  show ?thesis using names_belowI' unfolding Hfrc_def eq_case_def mem_case_def 
    apply auto sorry
qed


definition
  forces_eq :: "[i,i,i] \<Rightarrow> o" where
  "forces_eq(p,t1,t2) \<equiv> frc_at(P,leq,<0,t1,t2,p>) = 1"

definition
  forces_mem :: "[i,i,i] \<Rightarrow> o" where
  "forces_mem(p,t1,t2) \<equiv> frc_at(P,leq,<1,t1,t2,p>) = 1"


lemma def_forces_eq: "p\<in>P \<Longrightarrow> forces_eq(p,t1,t2) \<longleftrightarrow> 
      (\<forall>s\<in>domain(t1) \<union> domain(t2). \<forall>q. q\<in>P \<and> <q,p>\<in>leq \<longrightarrow> 
      (forces_mem(q,s,t1) \<longleftrightarrow> forces_mem(q,s,t2)))" 
  unfolding forces_eq_def forces_mem_def using def_frc_at[of 0 t1 t2 p]  unfolding bool_of_o_def 
  by auto

lemma def_forces_mem: "p\<in>P \<Longrightarrow> forces_mem(p,t1,t2) \<longleftrightarrow> 
     (\<forall>v\<in>P. <v,p>\<in>leq \<longrightarrow>
      (\<exists>q. \<exists>s. \<exists>r. r\<in>P \<and> q\<in>P \<and> <q,v>\<in>leq \<and> <s,r> \<in> t2 \<and> <q,r>\<in>leq \<and> forces_eq(q,t1,s)))"
  unfolding forces_eq_def forces_mem_def using def_frc_at[of 1 t1 t2 p]  unfolding bool_of_o_def 
  by auto

definition
  is_frc_at :: "[i,i] \<Rightarrow> o" where
  "is_frc_at(x,z) \<equiv> \<exists>r\<in>M. is_forcerel(x,r) \<and> is_wfrec(##M,is_Hfrc_at(##M,P,leq),r,x,z)"

lemma trans_forcerel_t : "trans(forcerel(x))"
  unfolding forcerel_def using trans_trancl .

lemma relation_forcerel_t : "relation(forcerel(x))" 
  unfolding forcerel_def using relation_trancl .

lemma oneN_in_M[simp]: "1\<in>M"
  by (simp del:setclass_iff add:setclass_iff[symmetric])


lemma twoN_in_M : "2\<in>M" 
  by (simp del:setclass_iff add:setclass_iff[symmetric])

lemma forcerel_in_M :
  assumes 
    "x\<in>M" 
  shows 
    "forcerel(x)\<in>M" 
  unfolding forcerel_def def_frecrel names_below_def
proof -
  let ?Q = "2 \<times> eclose(x) \<times> eclose(x) \<times> P"
  have "?Q \<times> ?Q \<in> M"
    using \<open>x\<in>M\<close> P_in_M twoN_in_M eclose_closed cartprod_closed by simp
  moreover
  have "separation(##M,\<lambda>z. \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x, y))"
  proof -
    have "arity(frecrelP_fm(0)) = 1"
      unfolding number1_fm_def frecrelP_fm_def 
      by (simp del:FOL_sats_iff pair_abs empty_abs
                  add: fm_defs frecR_fm_def number1_fm_def components_defs nat_simp_union)
    then
    have "separation(##M, \<lambda>z. sats(M,frecrelP_fm(0) , [z]))"
      using separation_ax by simp
    moreover
    have "frecrelP(##M,z) \<longleftrightarrow> sats(M,frecrelP_fm(0),[z])" 
      if "z\<in>M" for z
      using that sats_frecrelP_fm[of 0 "[z]"] by simp
    ultimately
    have "separation(##M,frecrelP(##M))" 
      unfolding separation_def by simp
    then 
    show ?thesis using frecrelP_abs
        separation_cong[of "##M" "frecrelP(##M)" "\<lambda>z. \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x, y)"]
      by simp
  qed
  ultimately
  show "{z \<in> ?Q \<times> ?Q . \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x, y)}^+ \<in> M" 
    using separation_closed frecrelP_abs trancl_closed by simp
qed
  
lemma relation2_Hfrc_at_abs:
  "relation2(##M,is_Hfrc_at(##M,P,leq),\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"
  unfolding relation2_def using Hfrc_at_abs
  by simp

lemma Hfrc_at_closed :
  "\<forall>x\<in>M. \<forall>g\<in>M. function(g) \<longrightarrow> bool_of_o(Hfrc(P,leq,x,g))\<in>M" 
  unfolding bool_of_o_def using zero_in_M n_in_M[of 1] by simp

lemma wfrec_Hfrc_at :
    assumes
      "X\<in>M" 
    shows 
      "wfrec_replacement(##M,is_Hfrc_at(##M,P,leq),forcerel(X))"
proof -
  have 0:"is_Hfrc_at(##M,P,leq,a,b,c) \<longleftrightarrow> 
        sats(M,Hfrc_at_fm(8,9,2,1,0),[c,b,a,d,e,y,x,z,P,leq,forcerel(X)])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "y\<in>M" "x\<in>M" "z\<in>M" 
    for a b c d e y x z
    using that P_in_M leq_in_M \<open>X\<in>M\<close> forcerel_in_M 
          is_Hfrc_at_iff_sats[of concl:M P leq a b c 8 9 2 1 0 
                                       "[c,b,a,d,e,y,x,z,P,leq,forcerel(X)]"] by simp
  have 1:"sats(M,is_wfrec_fm(Hfrc_at_fm(8,9,2,1,0),5,1,0),[y,x,z,P,leq,forcerel(X)]) \<longleftrightarrow>
                   is_wfrec(##M, is_Hfrc_at(##M,P,leq),forcerel(X), x, y)"
    if "x\<in>M" "y\<in>M" "z\<in>M" for x y z
    using  that \<open>X\<in>M\<close> forcerel_in_M P_in_M leq_in_M
           sats_is_wfrec_fm[OF 0] 
    by simp
  let 
    ?f="Exists(And(pair_fm(1,0,2),is_wfrec_fm(Hfrc_at_fm(8,9,2,1,0),5,1,0)))"
  have satsf:"sats(M, ?f, [x,z,P,leq,forcerel(X)]) \<longleftrightarrow>
              (\<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hfrc_at(##M,P,leq),forcerel(X), x, y))" 
    if "x\<in>M" "z\<in>M" for x z
    using that 1 \<open>X\<in>M\<close> forcerel_in_M P_in_M leq_in_M by (simp del:pair_abs)
  have artyf:"arity(?f) = 5" 
    unfolding is_wfrec_fm_def Hfrc_at_fm_def Hfrc_fm_def  is_Replace_fm_def PHcheck_fm_def
              pair_fm_def upair_fm_def is_recfun_fm_def fun_apply_fm_def big_union_fm_def
              pre_image_fm_def restriction_fm_def image_fm_def fm_defs number1_fm_def
              eq_case_fm_def mem_case_fm_def is_tuple_fm_def
    by (simp add:nat_simp_union)
  moreover 
    have "?f\<in>formula"
      unfolding fm_defs Hfrc_at_fm_def by simp
    ultimately
  have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,P,leq,forcerel(X)]))"
    using replacement_ax 1 artyf \<open>X\<in>M\<close> forcerel_in_M P_in_M leq_in_M by simp
  then
  have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hfrc_at(##M,P,leq),forcerel(X), x, y))"
    using repl_sats[of M ?f "[P,leq,forcerel(X)]"] satsf by (simp del:pair_abs)
  then 
  show ?thesis unfolding wfrec_replacement_def by simp
qed

lemma names_below_abs :
  "\<lbrakk>Q\<in>M;x\<in>M;nb\<in>M\<rbrakk> \<Longrightarrow> is_names_below(##M,Q,x,nb) \<longleftrightarrow> nb = names_below(Q,x)" 
  unfolding is_names_below_def names_below_def 
  using succ_in_M_iff zero_in_M cartprod_closed eclose_closed by simp

lemma names_below_closed:
  "\<lbrakk>Q\<in>M;x\<in>M\<rbrakk> \<Longrightarrow> names_below(Q,x) \<in> M"
  unfolding names_below_def using zero_in_M cartprod_closed eclose_closed succ_in_M_iff by simp

lemma "names_below_productE" :
  " Q \<in> M \<Longrightarrow>
 x \<in> M \<Longrightarrow> (\<And>A1 A2 A3 A4. A1 \<in> M \<Longrightarrow> A2 \<in> M \<Longrightarrow> A3 \<in> M \<Longrightarrow> A4 \<in> M \<Longrightarrow> R(A1 \<times> A2 \<times> A3 \<times> A4)) 
       \<Longrightarrow> R(names_below(Q,x))" 
  unfolding names_below_def using zero_in_M eclose_closed[of x]  twoN_in_M by auto

lemma forcerel_abs :
  "\<lbrakk>x\<in>M;z\<in>M\<rbrakk> \<Longrightarrow> is_forcerel(x,z) \<longleftrightarrow> z = forcerel(x)" 
  unfolding is_forcerel_def forcerel_def 
  using frecrel_abs names_below_abs trancl_abs P_in_M twoN_in_M eclose_closed names_below_closed
         names_below_productE[of concl:"\<lambda>p. is_frecrel(##M,p,_) \<longleftrightarrow>  _ = frecrel(p)"] frecrel_closed
  by simp

lemma frc_at_abs:
  assumes "fnnc\<in>M" "z\<in>M" 
  shows "is_frc_at(fnnc,z) \<longleftrightarrow> z = frc_at(P,leq,fnnc)"
proof -
  from assms
  have "(\<exists>r\<in>M. is_forcerel(fnnc, r) \<and> is_wfrec(##M, is_Hfrc_at(##M, P, leq), r, fnnc, z))
        \<longleftrightarrow> is_wfrec(##M, is_Hfrc_at(##M, P, leq), forcerel(fnnc), fnnc, z)"
    using forcerel_abs forcerel_in_M by simp
  then 
  show ?thesis
  unfolding frc_at_trancl is_frc_at_def
  using assms wfrec_Hfrc_at[of fnnc] wf_forcerel trans_forcerel_t relation_forcerel_t forcerel_in_M
        Hfrc_at_closed relation2_Hfrc_at_abs
        trans_wfrec_abs[of "forcerel(fnnc)" fnnc z "is_Hfrc_at(##M,P,leq)" "\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f))"]
  by (simp del:setclass_iff  add:setclass_iff[symmetric])
qed

(* frc_at(P,leq,<0,t1,t2,p>) = 1*) 
definition
  is_forces_eq :: "[i,i,i] \<Rightarrow> o" where
  "is_forces_eq(p,t1,t2) == \<exists>o\<in>M. \<exists>z\<in>M. \<exists>t\<in>M. number1(##M,o) \<and> empty(##M,z) \<and> 
                                is_tuple(##M,z,t1,t2,p,t) \<and> is_frc_at(t,o)"

(* frc_at(P,leq,<1,t1,t2,p>) = 1*) 
definition
  is_forces_mem :: "[i,i,i] \<Rightarrow> o" where
  "is_forces_mem(p,t1,t2) == \<exists>o\<in>M. \<exists>t\<in>M. number1(##M,o) \<and>  
                                is_tuple(##M,o,t1,t2,p,t) \<and> is_frc_at(t,o)"

lemma forces_eq_abs :
  "\<lbrakk>p\<in>M ; t1\<in>M ; t2\<in>M\<rbrakk> \<Longrightarrow> is_forces_eq(p,t1,t2) \<longleftrightarrow> forces_eq(p,t1,t2)"
  unfolding is_forces_eq_def forces_eq_def
  using frc_at_abs zero_in_M tuples_in_M by auto

lemma forces_mem_abs :
  "\<lbrakk>p\<in>M ; t1\<in>M ; t2\<in>M\<rbrakk> \<Longrightarrow> is_forces_mem(p,t1,t2) \<longleftrightarrow> forces_mem(p,t1,t2)"
  unfolding is_forces_mem_def forces_mem_def
  using frc_at_abs zero_in_M tuples_in_M by auto

lemma sats_frc_at_fm :
  assumes
    "nth(p,env) = P" "nth(l,env) = leq" "nth(i,env) = x" "nth(j,env) = z"  
    "p\<in>nat" "l\<in>nat" "i\<in>nat" "j\<in>nat" "x\<in>M" "z\<in>M" "env\<in>list(M)" "i < length(env)" "j < length(env)"
  shows
    "sats(M,frc_at_fm(p,l,i,j),env) \<longleftrightarrow> is_frc_at(x,z)" 
proof -
  {
    fix r
    assume "r\<in>M"
  have 0:"is_Hfrc_at(##M,P,leq,a2, a1, a0) \<longleftrightarrow> 
         sats(M, Hfrc_at_fm(6#+p,6#+l,2,1,0), [a0,a1,a2,a3,a4,r]@env)" 
        if "a0\<in>M" "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" for a0 a1 a2 a3 a4
    using  that assms P_in_M leq_in_M forcerel_in_M \<open>r\<in>M\<close>
          is_Hfrc_at_iff_sats[of "6#+p" "6#+l" 2 1 0 "[a0,a1,a2,a3,a4,r]@env" M]  by simp
  have "sats(M,is_wfrec_fm(Hfrc_at_fm(6 #+ p, 6 #+ l, 2, 1, 0), 0, succ(i), succ(j)),[r]@env) \<longleftrightarrow>
         is_wfrec(##M, is_Hfrc_at(##M, P, leq), r,nth(i, env), nth(j, env))"
    using assms forcerel_in_M P_in_M leq_in_M \<open>r\<in>M\<close> 
          sats_is_wfrec_fm[OF 0[simplified]]  
    by simp
}
  moreover
  have "sats(M, forcerel_fm(succ(p), succ(i), 0), Cons(r, env)) \<longleftrightarrow>
        is_forcerel(x,r)" if "r\<in>M" for r
    using assms sats_forcerel_fm that by simp
  ultimately
  show ?thesis unfolding is_frc_at_def frc_at_fm_def
    using assms by simp
qed

lemma sats_forces_eq_fm: 
  assumes  "p\<in>nat" "l\<in>nat" "r\<in>nat" "q\<in>nat" "t1\<in>nat" "t2\<in>nat"  "env\<in>list(M)"
           "nth(t1,env)=tt1" "nth(t2,env)=tt2" "nth(q,env)=qq" "nth(p,env)=P" "nth(l,env)=leq" 
         shows "sats(M,forces_eq_fm(p,l,q,t1,t2),env) \<longleftrightarrow> is_forces_eq(qq,tt1,tt2)"
unfolding forces_eq_fm_def is_forces_eq_def using assms sats_is_tuple_fm oneN_in_M zero_in_M sats_frc_at_fm
  by simp

lemma sats_forces_mem_fm: 
  assumes  "p\<in>nat" "l\<in>nat" "r\<in>nat" "q\<in>nat" "t1\<in>nat" "t2\<in>nat"  "env\<in>list(M)"
           "nth(t1,env)=tt1" "nth(t2,env)=tt2" "nth(q,env)=qq" "nth(p,env)=P" "nth(l,env)=leq" 
  shows "sats(M,forces_mem_fm(p,l,q,t1,t2),env) \<longleftrightarrow> is_forces_mem(qq,tt1,tt2)"
  unfolding forces_mem_fm_def is_forces_mem_def using assms sats_is_tuple_fm
            oneN_in_M zero_in_M sats_frc_at_fm
  by simp

end (* context forcing_data *)


(* DEFINE THIS *)
rename "forces_nand" src "[P,leq,o,q]" tgt "[q,P,leq,o,p]"

definition forces_nand_ren :: "i \<Rightarrow> i" where
  "forces_nand_ren(env) == sum(forces_nand_fn,id(length(env)),4,5,length(env))"

definition 
  ren_forces_nand :: "[i,i] \<Rightarrow> i" where
  "ren_forces_nand(\<phi>,env) = ren(\<phi>)`(4#+length(env))`(5#+length(env))`forces_nand_ren(env)" 


lemma ren_forces_nand_type[TC] :
  "\<phi>\<in>formula \<Longrightarrow> env \<in> list(M) \<Longrightarrow> ren_forces_nand(\<phi>,env) \<in>formula" 
  unfolding ren_forces_nand_def forces_nand_fn_def forces_nand_ren_def
  using  forces_nand_thm(1) ren_tc
  by simp

lemma ren_forces_nand_arity: 
  assumes  "\<phi>\<in>formula" "arity(\<phi>)\<le> 4#+length(env)" "env \<in> list(M)"
    shows "arity(ren_forces_nand(\<phi>,env)) \<le> 5#+length(env)"
  unfolding ren_forces_nand_def forces_nand_fn_def forces_nand_ren_def
    using assms forces_nand_thm(1) ren_arity
    by simp

lemma sats_ren_forces_nand: 
  "[q,P,leq,o,p] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> arity(\<phi>) \<le> 4 #+ length(env) \<Longrightarrow>
   sats(M, ren_forces_nand(\<phi>,env),[q,P,leq,o,p] @ env) \<longleftrightarrow> sats(M, \<phi>,[P,leq,o,q] @ env)"
  unfolding ren_forces_nand_def forces_nand_fn_def forces_nand_ren_def
  apply (rule sats_iff_sats_ren[symmetric],auto simp add:forces_nand_thm(1)[of _ M,simplified])
  apply (auto simp add: forces_nand_thm(2)[simplified,symmetric])
  done

definition
  ren_forces_forall :: "i\<Rightarrow>i" where
  "ren_forces_forall(f) \<equiv> f" 

lemma ren_forces_forall_type[TC] :
  "\<phi>\<in>formula \<Longrightarrow> ren_forces_forall(\<phi>) \<in>formula" 
  unfolding ren_forces_forall_def by simp

lemma sats_ren_forces_forall :
  "[x,P,leq,one,p] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> 
    sats(M, ren_forces_forall(\<phi>),[x,P,leq,o,p] @ env) \<longleftrightarrow> sats(M, \<phi>,[P,leq,o,p,x] @ env)"
  sorry

definition 
  leq_fm :: "[i,i,i] \<Rightarrow> i" where
  "leq_fm(leq,q,p) \<equiv> Exists(And(pair_fm(q#+1,p#+1,0),Member(0,leq#+1)))" 

lemma leq_fm_type[TC] :
  "\<lbrakk>leq\<in>nat;q\<in>nat;p\<in>nat\<rbrakk> \<Longrightarrow> leq_fm(leq,q,p)\<in>formula" 
  unfolding leq_fm_def by simp

lemma sats_leq_fm :
  "\<lbrakk> leq\<in>nat;q\<in>nat;p\<in>nat;env\<in>list(A) \<rbrakk> \<Longrightarrow> 
     sats(A,leq_fm(leq,q,p),env) \<longleftrightarrow> 
    (\<exists>qp\<in>A. (pair(##A,nth(q,env),nth(p,env),qp) \<and>qp\<in>nth(leq,env)))" 
  unfolding leq_fm_def by simp

consts forces' :: "i\<Rightarrow>i"
primrec
  "forces'(Member(x,y)) = forces_mem_fm(0,1,3,x#+4,y#+4)"
  "forces'(Equal(x,y))  = forces_eq_fm(0,1,3,x#+4,y#+4)"
  "forces'(Nand(p,q))   = 
        Neg(Exists(And(Member(0,1),And(leq_fm(2,0,4),And(ren_forces_nand(forces'(p)),
                                         ren_forces_nand(forces'(q)))))))"
  "forces'(Forall(p))   = Forall(ren_forces_forall(forces'(p)))" 

definition 
  forces :: "i\<Rightarrow>i" where
  "forces(\<phi>) \<equiv> And(Member(3,0),forces'(\<phi>))"

lemma forces'_type [TC]:  "\<phi>\<in>formula \<Longrightarrow> forces'(\<phi>) \<in> formula" 
  by (induct \<phi> set:formula; simp)

lemma forces_type[TC] : "\<phi>\<in>formula \<Longrightarrow> forces(\<phi>) \<in> formula"
  unfolding forces_def by simp

lemma (in forcing_data) sats_forces_Member :
  assumes  "x\<in>nat" "y\<in>nat" "env\<in>list(M)"
           "nth(x,env)=xx" "nth(y,env)=yy" "q\<in>M" 
         shows "sats(M,forces(Member(x,y)),[P,leq,one,q]@env) \<longleftrightarrow> 
                (q\<in>P \<and> is_forces_mem(q,xx,yy))"
  unfolding forces_def using assms sats_forces_mem_fm P_in_M leq_in_M one_in_M 
  by simp

lemma (in forcing_data) sats_forces_Equal :
  assumes  "x\<in>nat" "y\<in>nat" "env\<in>list(M)"
           "nth(x,env)=xx" "nth(y,env)=yy" "q\<in>M" 
         shows "sats(M,forces(Equal(x,y)),[P,leq,one,q]@env) \<longleftrightarrow> 
                (q\<in>P \<and> is_forces_eq(q,xx,yy))"
  unfolding forces_def using assms sats_forces_eq_fm P_in_M leq_in_M one_in_M 
  by simp

lemma (in forcing_data) sats_forces_Nand :
  assumes  "\<phi>\<in>formula" "\<psi>\<in>formula" "env\<in>list(M)" "p\<in>M" 
  shows "sats(M,forces(Nand(\<phi>,\<psi>)),[P,leq,one,p]@env) \<longleftrightarrow> 
         (p\<in>P \<and> \<not>(\<exists>q\<in>M. q\<in>P \<and> (\<exists>qp\<in>M. pair(##M,q,p,qp) \<and> qp\<in>leq) \<and> 
               (sats(M,forces'(\<phi>),[P,leq,one,q]@env) \<and> sats(M,forces'(\<psi>),[P,leq,one,q]@env))))"
  unfolding forces_def using sats_leq_fm assms sats_ren_forces_nand P_in_M leq_in_M one_in_M  
  by simp
  
lemma (in forcing_data) sats_forces_Neg :
  assumes  "\<phi>\<in>formula" "\<psi>\<in>formula" "env\<in>list(M)" "p\<in>M" 
  shows "sats(M,forces(Neg(\<phi>)),[P,leq,one,p]@env) \<longleftrightarrow> 
         (p\<in>P \<and> \<not>(\<exists>q\<in>M. q\<in>P \<and> (\<exists>qp\<in>M. pair(##M,q,p,qp) \<and> qp\<in>leq) \<and> 
               (sats(M,forces'(\<phi>),[P,leq,one,q]@env))))"
  unfolding Neg_def using assms sats_forces_Nand 
  by simp

lemma (in forcing_data) sats_forces_Forall :
  assumes  "\<phi>\<in>formula" "env\<in>list(M)" "p\<in>M" 
  shows "sats(M,forces(Forall(\<phi>)),[P,leq,one,p]@env) \<longleftrightarrow> 
         p\<in>P \<and> (\<forall>x\<in>M. sats(M,forces'(\<phi>),[P,leq,one,p,x]@env))"
  unfolding forces_def using assms sats_ren_forces_forall P_in_M leq_in_M one_in_M  
  by simp

(*
lemma arity_forces_ren:
  shows "\<phi>\<in>formula \<Longrightarrow> arity(forces_ren(auxren,fren,fref, \<phi>)) =  arity(\<phi>) #+ 4"
proof (induct set:formula)
  case (Member x y)
  then 
  show ?case by (simp add:nat_simp_union)
next
  case (Equal x y)
  then 
  show ?case by (simp add:nat_simp_union)
next
  case (Nand \<phi> \<psi>)
  then 
  show ?case 
    by (simp add:fm_defs nat_union_abs1 nat_union_abs2 pred_Un, simp add:nat_simp_union)
next
  case (Forall \<phi>)
  then
  show ?case 
    apply (simp) (* This is false as it stands, it needs arity(\<phi>) \<noteq> 0 *)
    sorry
qed
*)

end 