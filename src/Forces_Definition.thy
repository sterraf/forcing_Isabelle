theory Forces_Definition imports FrecR begin

(*
name1(x) \<in> domain(name1(y)) \<union> domain(name2(y)) \<and> 
            (name2(x) = name1(y) \<or> name2(x) = name2(y)) 
          \<or> name1(x) = name1(y) \<and> name2(x) \<in> domain(name2(y))*)
definition
  is_frecR :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_frecR(M,x,y) \<equiv> \<exists> ftx[M]. \<exists> n1x[M]. \<exists>n2x[M]. \<exists>fty[M]. \<exists>n1y[M]. \<exists>n2y[M]. \<exists>dn1[M]. \<exists>dn2[M].
  is_ftype(M,x,ftx) \<and> is_name1(M,x,n1x)\<and> is_name2(M,x,n2x) \<and>
  is_ftype(M,y,fty) \<and> is_name1(M,y,n1y) \<and> is_name2(M,y,n2y)
          \<and> is_domain(M,n1y,dn1) \<and> is_domain(M,n2y,dn2) \<and> 
          (  (number1(M,ftx) \<and> empty(M,fty) \<and> (n1x \<in> dn1 \<or> n1x \<in> dn2) \<and> (n2x = n1y \<or> n2x = n2y))
           \<or> (empty(M,ftx) \<and> number1(M,fty) \<and> n1x = n1y \<and> n2x \<in> dn2))"

(*
\<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x,y) *)
definition
  frecrelP :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
  "frecrelP(M,xy) \<equiv> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,xy) \<and> is_frecR(M,x,y))"


(* {z\<in>A\<times>A. \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x,y)} *)
definition
  is_frecrel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_frecrel(M,A,r) \<equiv> \<exists>A2[M]. cartprod(M,A,A,A2) \<and> is_Collect(M,A2, frecrelP(M) ,r)"

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

lemma sats_is_names_below_fm :
  assumes
    "P\<in>nat" "x\<in>nat" "nb\<in>nat" "env\<in>list(A)" 
  shows
    "is_names_below(##A,nth(P, env),nth(x, env),nth(nb, env))
    \<longleftrightarrow> sats(A,is_names_below_fm(P,x,nb),env)" 
   unfolding is_names_below_fm_def is_names_below_def using assms by simp




definition
  forcerel :: "i \<Rightarrow> i \<Rightarrow> i" where
  "forcerel(P,x) \<equiv> frecrel(names_below(P,x))"

schematic_goal sats_frecrelP_fm_auto:
  assumes 
    "a\<in>nat" "env\<in>list(A)"
  shows
    "frecrelP(##A,nth(a, env))
    \<longleftrightarrow> sats(A,?frp_fm(a,r),env)"
    unfolding is_frecrel_def is_frecR_def is_Collect_def frecrelP_def is_ftype_def is_name1_def is_name2_def 
   by (insert assms ; (rule sep_rules empty_iff_sats cartprod_iff_sats is_one_iff_sats  | simp del:sats_cartprod_fm)+)

schematic_goal sats_is_frecrel_fm_auto:
  assumes 
    "a\<in>nat"  "r\<in>nat" "env\<in>list(A)"
  shows
    "is_frecrel(##A,nth(a, env),nth(r, env))
    \<longleftrightarrow> sats(A,?ifrl_fm(a,r),env)"
    unfolding is_frecrel_def is_frecR_def is_Collect_def frecrelP_def is_name1_def is_name2_def is_ftype_def
   by (insert assms ; (rule sep_rules cartprod_iff_sats | simp del:sats_cartprod_fm)+) 

schematic_goal is_frecrel_iff_sats:
  assumes
    "nth(a,env) = aa" "nth(r,env) = rr" "a\<in> nat"  "r\<in> nat"  "env \<in> list(A)"
  shows
       "is_frecrel(##A, aa,rr) \<longleftrightarrow> sats(A, ?ifrl_fm(a,r), env)"
  unfolding \<open>nth(a,env) = aa\<close>[symmetric] \<open>nth(r,env) = rr\<close>[symmetric]
  by (rule sats_is_frecrel_fm_auto(1); simp add:assms)


(* Definition of forces for equality and membership *)

(* p ||- \<tau> = \<theta> \<equiv>
  \<forall>\<sigma>. \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<longrightarrow> (\<forall>q\<in>P. <q,p>\<in>leq \<longrightarrow> ((q ||- \<sigma>\<in>\<tau>) \<longleftrightarrow> (q ||- \<sigma>\<in>\<theta>)) ) *)
definition
  eq_case :: "[i,i,i,i,i,i] \<Rightarrow> o" where
  "eq_case(t1,t2,p,P,leq,f) \<equiv> \<forall>s. s\<in>domain(t1) \<union> domain(t2) \<longrightarrow>
      (\<forall>q. q\<in>P \<and> <q,p>\<in>leq \<longrightarrow> (f`<1,s,t1,q>=1  \<longleftrightarrow> f`<1,s,t2,q> =1))"

(* p ||-
   \<pi> \<in> \<tau> \<equiv> \<forall>v\<in>P. <v,p>\<in>leq \<longrightarrow> (\<exists>q\<in>P. <q,v>\<in>leq \<and> (\<exists>\<sigma>. \<exists>r\<in>P. <\<sigma>,r>\<in>\<tau> \<and> <q,r>\<in>leq \<and>  q ||- \<pi> = \<sigma>)) *)
definition
  mem_case :: "[i,i,i,i,i,i] \<Rightarrow> o" where
  "mem_case(t1,t2,p,P,leq,f) \<equiv> \<forall>v\<in>P. <v,p>\<in>leq \<longrightarrow>
    (\<exists>q. \<exists>s. \<exists>r. r\<in>P \<and> q\<in>P \<and> <q,v>\<in>leq \<and> <s,r> \<in> t2 \<and> <q,r>\<in>leq \<and>  f`<0,t1,s,q> = 1)"

definition
  Hfrc :: "[i,i,i,i] \<Rightarrow> o" where
  "Hfrc(P,leq,fnnc,f) \<equiv> \<exists>ft. \<exists>n1. \<exists>n2. \<exists>c. c\<in>P \<and> fnnc = <ft,n1,n2,c> \<and>
     (  ft = 0 \<and>  eq_case(n1,n2,c,P,leq,f)
      \<or> ft = 1 \<and> mem_case(n1,n2,c,P,leq,f))"

definition
  frc_at :: "[i,i,i] \<Rightarrow> i" where
  "frc_at(P,leq,fnnc) \<equiv> wfrec(forcerel(P,fnnc),fnnc,\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"


(* "eq_case(t1,t2,p,P,leq,f) \<equiv> \<forall>s\<in>domain(t1) \<union> domain(t2).
                        \<forall>q. q\<in>P \<and> <q,p>\<in>leq \<longrightarrow> f`<1,s,t1,q> = f`<1,s,t2,q>" *)
definition
  is_eq_case :: "[i\<Rightarrow>o,i,i,i,i,i,i] \<Rightarrow> o" where
  "is_eq_case(M,t1,t2,p,P,leq,f) \<equiv>
   \<forall>s[M]. (\<exists>d[M]. is_domain(M,t1,d) \<and> s\<in>d) \<or> (\<exists>d[M]. is_domain(M,t2,d) \<and> s\<in>d)
       \<longrightarrow> (\<forall>q[M]. q\<in>P \<and> (\<exists>qp[M]. pair(M,q,p,qp) \<and> qp\<in>leq) \<longrightarrow>
            (\<exists>t1q[M]. \<exists>st1q[M]. \<exists>ost1q[M]. \<exists>t2q[M]. \<exists>st2q[M]. \<exists>o[M]. \<exists>ost2q[M]. \<exists>vf1[M]. \<exists>vf2[M].
             pair(M,t1,q,t1q) \<and> pair(M,s,t1q,st1q) \<and> pair(M,o,st1q,ost1q) \<and>
             pair(M,t2,q,t2q) \<and> pair(M,s,t2q,st2q) \<and>
             is_one(M,o) \<and> pair(M,o,st2q,ost2q) \<and>
             fun_apply(M,f,ost2q,vf1) \<and> fun_apply(M,f,ost1q,vf2) \<and>
             (vf2 = o \<longleftrightarrow> vf1 =o)))"

(*  "mem_case(t1,t2,p,P,leq,f) \<equiv> \<forall>v\<in>P. <v,p>\<in>leq \<longrightarrow>
    (\<exists>q. \<exists>s. \<exists>r. r\<in>P \<and> q\<in>P \<and> <q,v>\<in>leq \<and> <s,r> \<in> t2 \<and> <q,r>\<in>leq \<and>  f`<0,t1,s,q> = 1)" *)
definition
  is_mem_case :: "[i\<Rightarrow>o,i,i,i,i,i,i] \<Rightarrow> o" where
  "is_mem_case(M,t1,t2,p,P,leq,f) \<equiv> \<forall>v[M]. \<forall>vp[M]. v\<in>P \<and> pair(M,v,p,vp) \<and> vp\<in>leq \<longrightarrow>
    (\<exists>q[M]. \<exists>qv[M]. \<exists>s[M]. \<exists>r[M]. \<exists>sr[M]. \<exists>qr[M]. \<exists>sq[M]. \<exists>t1sq[M]. \<exists>z[M]. \<exists>zt1sq[M]. \<exists>o[M].
     r\<in> P \<and> q\<in>P \<and> pair(M,q,v,qv) \<and> pair(M,s,r,sr) \<and> pair(M,q,r,qr) \<and> pair(M,s,q,sq) \<and>
     empty(M,z) \<and> pair(M,t1,sq,t1sq) \<and> pair(M,z,t1sq,zt1sq) \<and>
     is_one(M,o) \<and> sr\<in>t2 \<and> qv\<in>leq \<and> qr\<in>leq \<and> fun_apply(M,f,zt1sq,o))"

definition
  is_Hfrc :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_Hfrc(M,P,leq,fnnc,f) \<equiv>
     \<exists>ft[M]. \<exists>n1[M]. \<exists>n2[M]. \<exists>co[M]. \<exists>nc[M]. \<exists>nnc[M].
      co\<in>P \<and> pair(M,n2,co,nc) \<and> pair(M,n1,nc,nnc) \<and> pair(M,ft,nnc,fnnc) \<and>
      (  (empty(M,ft) \<and> is_eq_case(M,n1,n2,co,P,leq,f))
       \<or> (is_one(M,ft) \<and>  is_mem_case(M,n1,n2,co,P,leq,f)))"

definition
  is_Hfrc_at :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_Hfrc_at(M,P,leq,fnnc,f,z) \<equiv> 
            (empty(M,z) \<and> \<not> is_Hfrc(M,P,leq,fnnc,f))
          \<or> (is_one(M,z) \<and> is_Hfrc(M,P,leq,fnnc,f))"


(*   "frc_at(P,leq,fnnc) \<equiv>
      wfrec(forcerel(P,fnnc),fnnc,\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))" *)
definition
  is_frc_at :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_frc_at(M,P,leq,fnnc,z) \<equiv> is_wfrec(M,is_Hfrc_at(M,P,leq),forcerel(P,fnnc),fnnc,z)"

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
    "is_tuple(##A,nth(z, env),nth(t1, env),nth(t2, env),nth(p, env),nth(tup, env))
    \<longleftrightarrow> sats(A,is_tuple_fm(z,t1,t2,p,tup),env)"
  unfolding is_tuple_def is_tuple_fm_def using assms by simp

schematic_goal sats_is_mem_case_fm_auto:
  assumes 
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "is_mem_case(##A, nth(n1, env),nth(n2, env),nth(p, env),nth(P, env), nth(leq, env),nth(f,env))
    \<longleftrightarrow> sats(A,?imc_fm(n1,n2,p,P,leq,f),env)"
   unfolding is_mem_case_def
   by (insert assms ; (rule sep_rules is_one_iff_sats | simp)+)

schematic_goal sats_is_eq_case_fm_auto:
  assumes 
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "is_eq_case(##A, nth(n1, env),nth(n2, env),nth(p, env),nth(P, env), nth(leq, env),nth(f,env))
    \<longleftrightarrow> sats(A,?iec_fm(n1,n2,p,P,leq,f),env)"
  unfolding is_eq_case_def
    by (insert assms ; (rule sep_rules  is_one_iff_sats[of 0] | simp)+)
             
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
  unfolding is_Hfrc_def 
  by (insert assms; (rule sep_rules' is_mem_case_iff_sats[of 4 3 2 "P #+ 6" "leq #+ 6" "f #+ 6"] 
        is_eq_case_iff_sats[of 4 3 2 "P #+ 6" "leq #+ 6" "f #+ 6"] is_one_iff_sats | simp)+)

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
  unfolding is_Hfrc_at_def 
  by (insert assms; (rule sep_rules' is_one_iff_sats is_Hfrc_iff_sats[of P leq fnnc f] | simp)+)

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

definition
  is_Hfrc_at_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "is_Hfrc_at_fm(P,leq,fnnc,f,z) \<equiv> 
Or(And(empty_fm(z),
             Neg(Exists
                  (Exists
                    (Exists
                      (Exists
                        (And(Member(0, succ(succ(succ(succ(P))))),
                             Exists
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
                                                           (And(Member(0, succ(succ(P #+ 6))), Exists(And(pair_fm(1, 5, 0), Member(0, succ(succ(succ(leq #+ 6))))))),
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
      Exists(And(fun_apply_fm(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(f #+ 6))))))))))), 6, 0), Iff(Equal(0, 3), Equal(1, 3))))))))))))))))))))))))),
                                                And(Forall(Iff(Member(0, 6), empty_fm(0))),
                                                    Forall
                                                     (Implies
                                                       (And(Member(0, succ(P #+ 6)), Exists(And(pair_fm(1, 4, 0), Member(0, succ(succ(leq #+ 6)))))),
                                                        Exists
                                                         (Exists
                                                           (Exists
                                                             (Exists
                                                               (And(Member(0, succ(succ(succ(succ(succ(P #+ 6)))))),
                                                                    And(Member(3, succ(succ(succ(succ(succ(P #+ 6)))))),
                                                                        And(pair_fm(3, 4, 2),
                                                                            Exists
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
                            fun_apply_fm(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(f #+ 6)))))))))))), 1, 0))))))))))))))))))))))))))))))))))))))))),
         And(Forall(Iff(Member(0, succ(z)), empty_fm(0))),
             Exists
              (Exists
                (Exists
                  (Exists
                    (And(Member(0, succ(succ(succ(succ(P))))),
                         Exists
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
                                                       (And(Member(0, succ(succ(P #+ 6))), Exists(And(pair_fm(1, 5, 0), Member(0, succ(succ(succ(leq #+ 6))))))),
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
  Exists(And(fun_apply_fm(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(f #+ 6))))))))))), 6, 0), Iff(Equal(0, 3), Equal(1, 3))))))))))))))))))))))))),
                                            And(Forall(Iff(Member(0, 6), empty_fm(0))),
                                                Forall
                                                 (Implies
                                                   (And(Member(0, succ(P #+ 6)), Exists(And(pair_fm(1, 4, 0), Member(0, succ(succ(leq #+ 6)))))),
                                                    Exists
                                                     (Exists
                                                       (Exists
                                                         (Exists
                                                           (And(Member(0, succ(succ(succ(succ(succ(P #+ 6)))))),
                                                                And(Member(3, succ(succ(succ(succ(succ(P #+ 6)))))),
                                                                    And(pair_fm(3, 4, 2),
                                                                        Exists
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
                        fun_apply_fm(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(f #+ 6)))))))))))), 1, 0)))))))))))))))))))))))))))))))))))))))))"

definition
  is_frecrel_fm :: "[i,i] \<Rightarrow> i" where
  "is_frecrel_fm(a,r) \<equiv>  Exists
       (And(cartprod_fm(succ(a), succ(a), 0),
            Forall
             (Iff(Member(0, succ(succ(r))),
                  And(Member(0, 1),
                      Exists
                       (Exists
                         (And(pair_fm(1, 0, 2),
                              Exists
                               (And(Exists(pair_fm(1, 0, 3)),
                                    Exists
                                     (And(Exists(Exists(And(pair_fm(1, 0, 5), Exists(pair_fm(3, 0, 1))))),
                                          Exists
                                           (And(Exists(Exists(And(pair_fm(1, 0, 6), Exists(Exists(And(pair_fm(1, 0, 2), Exists(pair_fm(5, 0, 1)))))))),
                                                Exists
                                                 (And(Exists(pair_fm(1, 0, 5)),
                                                      Exists
                                                       (And(Exists(Exists(And(pair_fm(1, 0, 7), Exists(pair_fm(3, 0, 1))))),
                                                            Exists
                                                             (And(Exists(Exists(And(pair_fm(1, 0, 8), Exists(Exists(And(pair_fm(1, 0, 2), Exists(pair_fm(5, 0, 1)))))))),
                                                                  Exists
                                                                   (And(domain_fm(2, 0),
                                                                        Exists
                                                                         (And(domain_fm(2, 0),
                                                                              Or(And(number1_fm(7), And(empty_fm(4), And(Or(Member(6, 1), Member(6, 0)), Or(Equal(5, 3), Equal(5, 2))))),
                                                                                 And(empty_fm(7), And(number1_fm(4), And(Equal(6, 3), Member(5, 0)))))))))))))))))))))))))))))"

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


lemma sats_tran_closure_fm :
  assumes
    "i\<in>nat"  "j\<in>nat" "env\<in>list(A)"
  shows
    "tran_closure(##A,nth(i, env),nth(j, env))
    \<longleftrightarrow> sats(A,tran_closure_fm(i,j),env)"
  unfolding tran_closure_fm_def tran_closure_def rtran_closure_def rtran_closure_mem_def using assms 
  by simp


definition
  frecrel_eclose_fm :: "[i,i] \<Rightarrow> i" where
  "frecrel_eclose_fm(tup,fet) \<equiv> Exists(Exists(
    And(upair_fm(tup#+2,tup#+2,1),And(is_eclose_fm(1,0),is_frecrel_fm(0,fet #+ 2)))))"

definition
  forces_eq_fm :: "[i\<Rightarrow>i,i,i] \<Rightarrow> i" where
  "forces_eq_fm(r,t1,t2) \<equiv> Exists(Exists(Exists(Exists(And(And(And(And(
               r(is_wfrec_fm(is_Hfrc_at_fm(5,6,2,1,0),2,3,4)),number1_fm(2)),empty_fm(3)),
               is_tuple_fm(3, t1 #+ 8, t2 #+ 8, 7, 1)),frecrel_eclose_fm(1,0))))))"

definition
  forces_mem_fm :: "[i,i] \<Rightarrow> i" where
  "forces_mem_fm(t1,t2) \<equiv> Exists(Exists(Exists(Exists(And(And(And(And(
               is_wfrec_fm(is_Hfrc_at_fm(5,6,2,1,0),2,3,4),number1_fm(2)),number1_fm(3)),
               is_tuple_fm(3, t1 #+ 8, t2 #+ 8, 7, 1)),frecrel_eclose_fm(1,0))))))"

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

lemma forces_eq_fm_type [TC]:
  assumes [TC]:"\<And>x. x\<in>formula \<Longrightarrow> r(x)\<in>formula" 
  shows "t1 \<in> nat \<Longrightarrow> t2 \<in> nat \<Longrightarrow> forces_eq_fm(r,t1,t2) \<in> formula"
  unfolding forces_eq_fm_def is_Hfrc_at_fm_def
  by simp

lemma forces_mem_fm_type [TC]:
  "t1 \<in> nat \<Longrightarrow> t2 \<in> nat \<Longrightarrow> forces_mem_fm(t1,t2) \<in> formula"
  unfolding forces_mem_fm_def is_Hfrc_at_fm_def
  by simp

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


consts forces_ren :: "[i\<Rightarrow>i,i,i,i]\<Rightarrow>i"
primrec
  "forces_ren(auxren,fren,fref,Member(x,y)) = forces_mem_fm(x,y)" (* Not ready yet *)
  "forces_ren(auxren,fren,fref,Equal(x,y))  = forces_eq_fm(auxren,x,y)"
  "forces_ren(auxren,fren,fref,Nand(p,q))   = Forall(Forall(Implies(Member(1,2),
                  Implies(And(pair_fm(1,5,0),Member(0,3)),
                  Neg(And(fren`forces_ren(auxren,fren,fref,p), fren`forces_ren(auxren,fren,fref,q)))))))"
  "forces_ren(auxren,fren,fref,Forall(p))   = Forall(fref`forces_ren(auxren,fren,fref,p))" (* check indexes *)


context forcing_data
begin

lemma components_abs [simp]:
  "\<lbrakk>x\<in>M; y\<in>M; x\<in>A1\<times>A2 \<rbrakk> \<Longrightarrow> is_ftype(##M,x,y) \<longleftrightarrow> ftype(x) = y"
  "\<lbrakk>x\<in>M; y\<in>M; x\<in>A1\<times>A2\<times>A3 \<rbrakk> \<Longrightarrow> is_name1(##M,x,y) \<longleftrightarrow> name1(x) = y"
  "\<lbrakk>x\<in>M; y\<in>M; x\<in>A1\<times>A2\<times>A3\<times>A4 \<rbrakk> \<Longrightarrow> is_name2(##M,x,y) \<longleftrightarrow> name2(x) = y"
  "\<lbrakk>x\<in>M; y\<in>M; x\<in>A1\<times>A2\<times>A3\<times>A4 \<rbrakk> \<Longrightarrow> is_cond_of(##M,x,y) \<longleftrightarrow> cond_of(x) = y"
  unfolding ftype_def  is_ftype_def name1_def is_name1_def
    name2_def is_name2_def cond_of_def is_cond_of_def using pair_in_M_iff
  by auto

lemma components_abs' [simp]:
  "\<lbrakk>f\<in>M; n1\<in>M; n2\<in>M; c\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_ftype(##M,<f,n1,n2,c>,y) \<longleftrightarrow> ftype(<f,n1,n2,c>) = y"
  "\<lbrakk>f\<in>M; n1\<in>M; n2\<in>M; c\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_name1(##M,<f,n1,n2,c>,y) \<longleftrightarrow> name1(<f,n1,n2,c>) = y"
  "\<lbrakk>f\<in>M; n1\<in>M; n2\<in>M; c\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_name2(##M,<f,n1,n2,c>,y) \<longleftrightarrow> name2(<f,n1,n2,c>) = y"
  "\<lbrakk>f\<in>M; n1\<in>M; n2\<in>M; c\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_cond_of(##M,<f,n1,n2,c>,y) \<longleftrightarrow> cond_of(<f,n1,n2,c>) = y"
  unfolding ftype_def  is_ftype_def name1_def is_name1_def
    name2_def is_name2_def cond_of_def is_cond_of_def using pair_in_M_iff
  by auto

lemma in_domain: "y\<in>M \<Longrightarrow> x\<in>domain(y) \<Longrightarrow> x\<in>M"
  using domainE[of x y] trans_M Transset_intf[of M _ y] pair_in_M_iff by auto


lemma comp_in_M:
  "<p,q>\<in>leq \<Longrightarrow> p\<in>M"
  "<p,q>\<in>leq \<Longrightarrow> q\<in>M"
  using leq_in_M trans_M Transset_intf[of M _ leq] pair_in_M_iff by auto

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
  "x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> x\<in>A1\<times>A2\<times>A3\<times>A4 \<Longrightarrow> y\<in>A1\<times>A2\<times>A3\<times>A4 \<Longrightarrow> frecR(x,y) \<longleftrightarrow> is_frecR(##M,x,y)" 
  unfolding frecR_def is_frecR_def using components_closed domain_closed by simp

lemma frecrelP_abs :
  assumes
    "A1\<in>M" "A2\<in>M" "A3\<in>M" "A4\<in>M" "z\<in>(A1\<times>A2\<times>A3\<times>A4)\<times>(A1\<times>A2\<times>A3\<times>A4)"
  shows
    "frecrelP(##M,z) \<longleftrightarrow> (\<exists>x y. z = <x,y> \<and> frecR(x,y))"
proof -
  let ?Q= "A1\<times>A2\<times>A3\<times>A4"
  have "?Q\<times>?Q\<in>M"
    using assms cartprod_closed by simp
  then
  have "z\<in>M" 
    using \<open>z\<in>?Q\<times>?Q\<close> Transset_intf[OF trans_M] by simp
  moreover
  have "x\<in>M \<and> y\<in>M" if "z = <x,y>" for x y
    using pair_in_M_iff that calculation by simp
  moreover 
  have "x\<in>(A1\<times>A2\<times>A3\<times>A4) \<and> y\<in>(A1\<times>A2\<times>A3\<times>A4)" if "z=<x,y>" for x y
    using that \<open>z\<in>(A1\<times>A2\<times>A3\<times>A4)\<times>(A1\<times>A2\<times>A3\<times>A4)\<close> by simp
  ultimately
  show ?thesis unfolding frecrelP_def using assms frecR_abs by auto
qed

lemma frecrel_abs:
  assumes 
   "A1\<in>M" "A2\<in>M" "A3\<in>M" "A3\<in>M""A4\<in>M" "r\<in>M"
 shows
   "is_frecrel(##M,A1\<times>A2\<times>A3\<times>A4,r) \<longleftrightarrow>  r = frecrel(A1\<times>A2\<times>A3\<times>A4) "
proof -
  let ?Q= "A1\<times>A2\<times>A3\<times>A4"
  have 0:"?Q\<in>M"
    using assms cartprod_closed by simp
  then
  have 1: "?Q \<times> ?Q \<in> M" 
    using cartprod_closed by simp
  moreover
  have "x\<in>M \<and> y\<in>M" if "z = <x,y>" "z\<in>M" for x y z
    using pair_in_M_iff that by simp
  moreover 
  have "x\<in>(A1\<times>A2\<times>A3\<times>A4) \<and> y\<in>(A1\<times>A2\<times>A3\<times>A4)" 
          if "z = <x,y>" "z\<in>(A1\<times>A2\<times>A3\<times>A4)\<times>(A1\<times>A2\<times>A3\<times>A4)" for x y z
    using that by simp
  have 
    "Collect(?Q\<times>?Q,frecrelP(##M)) = Collect(?Q\<times>?Q,\<lambda>z. (\<exists>x y. z = <x,y> \<and> frecR(x,y)))"
    using Collect_cong[of "?Q\<times>?Q" "?Q\<times>?Q" "frecrelP(##M)"] assms frecrelP_abs by simp
  then
  show ?thesis unfolding is_frecrel_def def_frecrel using assms cartprod_closed by simp
qed

lemma restrict_trancl_forcerel:
  assumes "frecR(w,y)"
  shows "restrict(f,forcerel(P,x)-``{y})`w
       = restrict(f,(forcerel(P,x)^+)-``{y})`w" 
  unfolding forcerel_def frecrel_def using assms restrict_trancl_Rrel[of frecR] 
     by (simp)




lemma names_belowI : 
  assumes "frecR(<ft,n1,n2,p>,<a,b,c,d>)" "p\<in>P"
  shows "<ft,n1,n2,p> \<in> names_below(P,<a,b,c,d>)" (is "?x \<in> names_below(_,?y)")
proof -
  from assms
  have "ft \<in> 2" "a \<in> 2" 
    unfolding frecR_def by auto
  have A: "b \<in> eclose(?y) " "c \<in> eclose(?y)" 
    using components_in_eclose by simp_all
  from assms
  consider (e) "n1 \<in> domain(b) \<union> domain(c) \<and> (n2 = b \<or> n2 =c)" 
    | (m) "n1 = b \<and> n2 \<in> domain(c)"
    unfolding frecR_def by auto
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


lemma Hfrc_restrict_trancl: "bool_of_o(Hfrc(P, leq, y, restrict(f,forcerel(P,x)-``{y})))
         = bool_of_o(Hfrc(P, leq, y, restrict(f,(forcerel(P,x)^+)-``{y})))"
  unfolding Hfrc_def bool_of_o_def eq_case_def mem_case_def 
  using  restrict_trancl_forcerel frecRI1 frecRI2 frecRI3 by simp

(* transitive force relation *)
definition
  forcerel_t :: "i \<Rightarrow> i" where
  "forcerel_t(x) == forcerel(P,x)^+"


(* frecrel(names_below(P,x)) *)
definition
  is_forcerel :: "i \<Rightarrow> i \<Rightarrow> o" where
  "is_forcerel(x,z) == \<exists>r\<in>M. \<exists>nb\<in>M. tran_closure(##M,r,z) \<and> 
                        is_names_below(##M,P,x,nb) \<and> is_frecrel(##M,nb,r)"

definition
  is_forcerel_fm :: "i\<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "is_forcerel_fm(p,x,z) == Exists(Exists(And(tran_closure_fm(1, z#+2),
                                        And(is_names_below_fm(p#+2,x#+2,0),
                                            is_frecrel_fm(0,1)))))"

(*
lemma sats_is_forcerel_fm:
  assumes
    "p\<in>nat" "x\<in>nat"  "z\<in>nat" "env\<in>list(A)" "nth(p,env) = P" 
  shows
    "is_forcerel(##A,nth(x, env),nth(z, env))
    \<longleftrightarrow> sats(A,is_forecel_fm(p,x,z),env)"
  sorry
*)

lemma frc_at_trancl: "frc_at(P,leq,z) = wfrec(forcerel_t(z),z,\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"
proof -
  have "frc_at(P,leq,z) = wfrec(forcerel(P,z),z,\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"
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
  show ?thesis unfolding forcerel_t_def .
qed

lemma wf_forcerel :
  "wf(forcerel(P,x))"
  unfolding forcerel_def using wf_frecrel .

(* Don't know if this is true *)
lemma  aux_def_frc_at: "x\<in>names_below(P,y) \<Longrightarrow>
  wfrec(forcerel(P,y), x, H) =  wfrec(forcerel(P,x), x, H)"
  sorry

(* This is NOT true (though it might be with \<subseteq>) *)
lemma vimage_forcerel: "forcerel(P,\<langle>ft,n1,n2,p\<rangle>) -`` {\<langle>ft,n1,n2,p\<rangle>} = names_below(P,\<langle>ft,n1,n2,p\<rangle>)"
  sorry

lemma def_frc_at : "frc_at(P,leq,<ft,n1,n2,p>) = 
   bool_of_o( p \<in>P \<and> 
  (  ft = 0 \<and>  (\<forall>s. s\<in>domain(n1) \<union> domain(n2) \<longrightarrow>
        (\<forall>q. q\<in>P \<and> <q,p>\<in>leq \<longrightarrow> (frc_at(P,leq,<1,s,n1,q>) =1 \<longleftrightarrow> frc_at(P,leq,<1,s,n2,q>) =1)))
   \<or> ft = 1 \<and> ( \<forall>v\<in>P. <v,p>\<in>leq \<longrightarrow>
    (\<exists>q. \<exists>s. \<exists>r. r\<in>P \<and> q\<in>P \<and> <q,v>\<in>leq \<and> <s,r> \<in> n2 \<and> <q,r>\<in>leq \<and>  frc_at(P,leq,<0,n1,s,q>) = 1))))"
proof -
  let ?r="\<lambda>y. forcerel(P,y)" and ?Hf="\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f))"
  let ?arg="<ft,n1,n2,p>"
  from wf_forcerel 
  have wfr: "\<forall>w . wf(?r(w))" ..
  with wfrec [of "?r(?arg)" ?arg ?Hf] 
  have "frc_at(P,leq,?arg) = ?Hf( ?arg, \<lambda>x\<in>?r(?arg) -`` {?arg}. wfrec(?r(?arg), x, ?Hf))"
    unfolding frc_at_def by simp 
  also
  have " ... = ?Hf( ?arg, \<lambda>x\<in>names_below(P,?arg). wfrec(?r(?arg), x, ?Hf))"
    using vimage_forcerel by simp
  also
  have " ... = ?Hf( ?arg, \<lambda>x\<in>names_below(P,?arg). frc_at(P,leq,x))"
    using aux_def_frc_at unfolding frc_at_def by simp
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
  is_frc_at_t :: "[i,i] \<Rightarrow> o" where
  "is_frc_at_t(x,z) \<equiv> is_wfrec(##M,is_Hfrc_at(##M,P,leq),forcerel_t(x),x,z)"

lemma wf_forcerel_t :
  "x\<in>M \<Longrightarrow> wf(forcerel_t(x))"
  unfolding forcerel_t_def using wf_forcerel wf_trancl by simp

lemma trans_forcerel_t : "trans(forcerel_t(x))"
  unfolding forcerel_t_def using trans_trancl .

lemma relation_forcerel_t : "relation(forcerel_t(x))" 
  unfolding forcerel_t_def using relation_trancl .

lemma oneN_in_M[simp]: "1\<in>M"
  by (simp del:setclass_iff add:setclass_iff[symmetric])


lemma twoN_in_M : "2\<in>M" 
  by (simp del:setclass_iff add:setclass_iff[symmetric])


lemma forcerel_in_M :
  assumes 
    "x\<in>M" 
  shows 
    "forcerel(P,x)\<in>M" 
  unfolding forcerel_t_def forcerel_def def_frecrel names_below_def
proof -
  let ?Q = "2 \<times> eclose(x) \<times> eclose(x) \<times> P"
  have "?Q \<times> ?Q \<in> M"
    using \<open>x\<in>M\<close> P_in_M twoN_in_M eclose_closed cartprod_closed by simp
  moreover
  have "separation(##M,\<lambda>z. \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x, y))"
  proof -
    obtain fp_fm where
      fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow> 
    (frecrelP(##M,nth(0,env)) \<longleftrightarrow> sats(M,fp_fm(0),env))"
      and 
      "fp_fm(0) \<in> formula" 
      and
      "arity(fp_fm(0)) = 1"
      using sats_frecrelP_fm_auto 
        sorry (* by (simp del:FOL_sats_iff pair_abs empty_abs add: fm_defs nat_simp_union) *)
    then
    have "separation(##M, \<lambda>z. sats(M,fp_fm(0) , [z]))"
      using separation_ax by simp
    moreover
    have "frecrelP(##M,z) \<longleftrightarrow> sats(M,fp_fm(0),[z])" 
      if "z\<in>M" for z
      using that fmsats[of "[z]"] by simp
    ultimately
    have "separation(##M,frecrelP(##M))" 
      unfolding separation_def by simp
    then 
    show ?thesis using frecrelP_abs
        separation_cong[of "##M" "frecrelP(##M)" "\<lambda>z. \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x, y)"]
      sorry
  qed
  ultimately
  show "{z \<in> ?Q \<times> ?Q . \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x, y)} \<in> M" 
    using separation_closed frecrelP_abs by simp
qed


lemma forcerel_t_in_M :
  assumes 
    "x\<in>M" 
  shows 
    "forcerel_t(x)\<in>M" 
  unfolding forcerel_t_def using assms  forcerel_in_M trancl_closed by simp


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
      "wfrec_replacement(##M,is_Hfrc_at(##M,P,leq),forcerel_t(X))"
proof -
  have 0:"is_Hfrc_at(##M,P,leq,a,b,c) \<longleftrightarrow> 
        sats(M,is_Hfrc_at_fm(8,9,2,1,0),[c,b,a,d,e,y,x,z,P,leq,forcerel_t(X)])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "y\<in>M" "x\<in>M" "z\<in>M" 
    for a b c d e y x z
    using that P_in_M leq_in_M \<open>X\<in>M\<close> forcerel_t_in_M 
          sats_is_Hfrc_at_fm[of concl:M 8 "[c,b,a,d,e,y,x,z,P,leq,forcerel_t(X)]" 9 2 1 0] by simp
  have 1:"sats(M,is_wfrec_fm(is_Hfrc_at_fm(8,9,2,1,0),5,1,0),[y,x,z,P,leq,forcerel_t(X)]) \<longleftrightarrow>
                   is_wfrec(##M, is_Hfrc_at(##M,P,leq),forcerel_t(X), x, y)"
    if "x\<in>M" "y\<in>M" "z\<in>M" for x y z
    using  that \<open>X\<in>M\<close> forcerel_t_in_M P_in_M leq_in_M
           sats_is_wfrec_fm[OF 0] 
    by simp
  let 
    ?f="Exists(And(pair_fm(1,0,2),is_wfrec_fm(is_Hfrc_at_fm(8,9,2,1,0),5,1,0)))"
  have satsf:"sats(M, ?f, [x,z,P,leq,forcerel_t(X)]) \<longleftrightarrow>
              (\<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hfrc_at(##M,P,leq),forcerel_t(X), x, y))" 
    if "x\<in>M" "z\<in>M" for x z
    using that 1 \<open>X\<in>M\<close> forcerel_t_in_M P_in_M leq_in_M by (simp del:pair_abs)
  have artyf:"arity(?f) = 5" 
    unfolding is_wfrec_fm_def is_Hfrc_at_fm_def is_Replace_fm_def PHcheck_fm_def
              pair_fm_def upair_fm_def is_recfun_fm_def fun_apply_fm_def big_union_fm_def
              pre_image_fm_def restriction_fm_def image_fm_def fm_defs
    by (simp add:nat_simp_union)
  moreover 
    have "?f\<in>formula"
      unfolding fm_defs is_Hfrc_at_fm_def by simp
    ultimately
  have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,P,leq,forcerel_t(X)]))"
    using replacement_ax 1 artyf \<open>X\<in>M\<close> forcerel_t_in_M P_in_M leq_in_M by simp
  then
  have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hfrc_at(##M,P,leq),forcerel_t(X), x, y))"
    using repl_sats[of M ?f "[P,leq,forcerel_t(X)]"] satsf by (simp del:pair_abs)
  then 
  show ?thesis unfolding wfrec_replacement_def by simp
qed


lemma frc_at_abs:
  "\<lbrakk>fnnc\<in>M ; z\<in>M\<rbrakk> \<Longrightarrow> is_frc_at_t(fnnc,z) \<longleftrightarrow> z = frc_at(P,leq,fnnc)"
  unfolding frc_at_trancl is_frc_at_t_def
  using wfrec_Hfrc_at[of fnnc] wf_forcerel_t trans_forcerel_t relation_forcerel_t forcerel_t_in_M
        Hfrc_at_closed relation2_Hfrc_at_abs 
        trans_wfrec_abs[of "forcerel_t(fnnc)" fnnc z "is_Hfrc_at(##M,P,leq)" "\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f))"]
  by (simp del:setclass_iff  add:setclass_iff[symmetric])


(*
definition
  is_forces_eq :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_forces_eq(M,P,leq,p,t1,t2) == 
      \<exists>o[M]. is_one(M,o) \<and> is_frc_at()


  "forces_eq(P,leq,p,t1,t2) \<equiv> frc_at(P,leq,<0,t1,t2,p>) = 1"
*)


lemma def_one: 
  assumes 
    "xa\<in>M"
  shows 
    "(\<forall>x\<in>M. x \<in> xa \<longleftrightarrow> x = 0) \<longleftrightarrow> xa = 1"
proof auto
  assume  1:"\<forall>x\<in>M. x \<in> xa \<longleftrightarrow> x = 0"
  have "0\<in>xa" 
    using 1 zero_in_M by simp
  then show "xa=1" 
    unfolding succ_def using equal_singleton[of _ xa 0] 
              1 \<open>xa\<in>M\<close> trans_M Transset_intf[of M] by auto
qed
  
end (* context forcing_data *)

locale forces_rename = forcing_data + 
  fixes fren :: "i" and fref :: "i" and auxren :: "i\<Rightarrow>i"
  assumes
  sats_fren: "[x,q,P,leq,one,p] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> 
      sats(M, fren`\<phi>,[x,q,P,leq,one,p] @ env) \<longleftrightarrow> sats(M, \<phi>,[P,leq,one,q] @ env)"
  and
  arity_fren [simp]: "arity(fren`\<phi>) = arity(\<phi>) #+ 2"
  and
  sats_fref: "[x,P,leq,one,p] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> 
      sats(M, fref`\<phi>,[x,P,leq,one,p] @ env) \<longleftrightarrow> sats(M, \<phi>,[P,leq,one,p,x] @ env)"
  and
  arity_fref [simp]: "arity(fref`\<phi>) = arity(\<phi>)"
  and (* Note: this is a function i\<Rightarrow>i *)
  sats_auxren: "[fec,tup,o,z,pp,l] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> 
      sats(M,auxren(\<phi>),[fec,tup,o,z,pp,l] @ env) \<longleftrightarrow> sats(M,\<phi>,[pp,l,fec,tup,o,z] @ env)"
  and
  arity_auxren [simp]: "arity(auxren(\<phi>)) = arity(\<phi>)"
  and
  renaming_type [TC]: "\<phi>\<in>formula \<Longrightarrow> fren`\<phi> \<in> formula" "\<phi>\<in>formula \<Longrightarrow> fref`\<phi> \<in> formula"
         "\<phi>\<in>formula \<Longrightarrow> auxren(\<phi>) \<in> formula"
  and
  wfrec_isHfrcat_replacement: "wfrec_replacement(##M, is_Hfrc_at(##M, P, leq), forcerel(P,fnnc)^+)"

begin

definition
  forces :: "i\<Rightarrow>i" where
  "forces(\<phi>) \<equiv> And(Member(3,0),forces_ren(auxren,fren,fref, \<phi>))"


lemma sats_forces_eq_fm': 
  assumes " [P,leq,one,p,t1,t2] @ env \<in> list(M)"
  shows "sats(M,forces_eq_fm(auxren,0,1),[P,leq,one,p,t1,t2] @ env) \<longleftrightarrow>
         sats(M,is_wfrec_fm(is_Hfrc_at_fm(5,6,2,1,0),2,3,4),
       [P,leq,forcerel(P,<0,t1,t2,p>),<0,t1,t2,p>,1,0, one,p,t1,t2] @ env)"
proof -
  from assms
  have "<0,t1,t2,p> \<in> M" 
    using M_inhabit tuples_in_M by simp
  then
  have "forcerel(P,<0,t1,t2,p>) \<in> M" 
    using forcerel_in_M by simp
  note inM = assms oneN_in_M M_inhabit \<open><0,t1,t2,p>\<in>M\<close> \<open>forcerel(P,<0,t1,t2,p>)\<in>M\<close>
  let ?\<phi>="is_wfrec_fm(is_Hfrc_at_fm(5,6,2,1,0),2,3,4)"
  have "?\<phi>\<in>formula" unfolding is_Hfrc_at_fm_def by simp
  let ?\<psi>="And(pair_fm(11,9,0),And(pair_fm(10,0,1),pair_fm(5,1,3)))"
  let ?\<theta>="Exists(Exists(And(upair_fm(3,3,1),And(is_eclose_fm(1,0),is_frecrel_fm(0,2)))))"
  from assms
  have "sats(M,forces_eq_fm(auxren,0,1),[P,leq,one,p,t1,t2] @ env) \<longleftrightarrow> (\<exists>x\<in>M. \<exists>xa\<in>M. \<exists>xb\<in>M. \<exists>xc\<in>M.
          sats(M,auxren(?\<phi>),[xc,xb,xa,x,P,leq,one,p,t1,t2] @ env) \<and>
          xa = 1 \<and> sats(M,empty_fm(3),[xc,xb,1,x,P,leq,one,p,t1,t2] @ env) \<and>
          sats(M,is_tuple_fm(3,8,9,7,1),[xc,xb,1,x,P,leq,one,p,t1,t2] @ env) \<and>
          sats(M,?\<theta>,[xc,xb,1,x,P,leq,one,p,t1,t2] @ env))"
    unfolding forces_eq_fm_def frecrel_eclose_fm_def
    using M_inhabit def_one
    by simp
  moreover from assms
  have "... \<longleftrightarrow> (\<exists>xa\<in>M. \<exists>xb\<in>M. \<exists>xc\<in>M.
          sats(M,auxren(?\<phi>),[xc,xb,xa,0,P,leq,one,p,t1,t2] @ env) \<and>
          xa = 1 \<and>
          sats(M,is_tuple_fm(3,8,9,7,1),[xc,xb,1,0,P,leq,one,p,t1,t2] @ env) \<and>
          sats(M,?\<theta>,[xc,xb,1,0,P,leq,one,p,t1,t2] @ env))"
    using M_inhabit by force
  moreover from assms
  have " ... \<longleftrightarrow> (\<exists>xb\<in>M. \<exists>xc\<in>M.
          sats(M,auxren(?\<phi>),[xc,xb,1,0,P,leq,one,p,t1,t2] @ env) \<and>
          (\<exists>c1\<in>M. \<exists>c0\<in>M. sats(M,?\<psi>,[c0,c1,xc,xb,1,0,P,leq,one,p,t1,t2] @ env)) \<and>
          sats(M,?\<theta>,[xc,xb,1,0,P,leq,one,p,t1,t2] @ env))"
    using oneN_in_M M_inhabit unfolding is_tuple_fm_def by auto
  moreover from assms
  have " ... \<longleftrightarrow> (\<exists>xc\<in>M.
          sats(M,auxren(?\<phi>),[xc,<0,t1,t2,p>,1,0,P,leq,one,p,t1,t2] @ env) \<and>
          sats(M,?\<theta>,[xc,<0,t1,t2,p>,1,0,P,leq,one,p,t1,t2] @ env))"
    using oneN_in_M M_inhabit tuples_in_M by auto
  moreover from inM
  have " ... \<longleftrightarrow> (\<exists>xc\<in>M.
          sats(M,auxren(?\<phi>),[xc,<0,t1,t2,p>,1,0,P,leq,one,p,t1,t2] @ env) \<and>
          (\<exists>s\<in>M. \<exists>ec\<in>M. sats(M,is_eclose_fm(1,0),[ec,s,xc,<0,t1,t2,p>,1,0,P,leq,one,p,t1,t2] @ env)
               \<and>  sats(M,upair_fm(3,3,1),[ec,s,xc,<0,t1,t2,p>,1,0,P,leq,one,p,t1,t2] @ env)
               \<and>  sats(M,is_frecrel_fm(0,2),[ec,s,xc,<0,t1,t2,p>,1,0,P,leq,one,p,t1,t2] @ env)) )"
    by (simp)
  moreover from inM
  have " ... \<longleftrightarrow> sats(M,auxren(?\<phi>),[forcerel(P,<0,t1,t2,p>),<0,t1,t2,p>,1,0,P,leq,one,p,t1,t2] @ env)"
    using sats_is_frecrel_fm[symmetric] cons_closed by simp
  moreover from inM
  have " ... \<longleftrightarrow> sats(M,?\<phi>,[P,leq,forcerel(P,<0,t1,t2,p>),<0,t1,t2,p>,1,0, one,p,t1,t2] @ env)"
    using sats_auxren[OF _ \<open>?\<phi>\<in>formula\<close>, of _ _ _ _ _ _ "[one,p,t1,t2] @ env"] by (simp)
  ultimately show ?thesis by simp
qed

lemma MH: "a0\<in>M \<Longrightarrow> a1\<in>M \<Longrightarrow> a2\<in>M \<Longrightarrow> a3\<in>M \<Longrightarrow> a4 \<in> M \<Longrightarrow> env\<in>list(M) \<Longrightarrow> 
      is_Hfrc_at(##M,P,leq,a2,a1,a0) \<longleftrightarrow> sats(M,is_Hfrc_at_fm(5,6,2,1,0),[a0,a1,a2,a3,a4,P,leq] @ env)"
  using sats_is_Hfrc_at_fm[of 5 6 2 1 0 "[a0,a1,a2,a3,a4,P,leq] @ env" M] P_in_M leq_in_M
  by (simp)

lemma sats_forces_eq_fm: 
  assumes  "n\<in>nat" "m\<in>nat" "p\<in>M" "t1\<in>M" "t2\<in>M" "env\<in>list(M)"
           "nth(n,env)=t1"  "nth(m,env)=t2"
  shows "sats(M,forces_eq_fm(auxren,n,m),[P,leq,one,p]@env) \<longleftrightarrow> is_frc_at_t(<0,t1,t2,p>,1)"
  sorry





lemma sats_forces_mem_fm: 
  assumes  "n\<in>nat" "m\<in>nat" "p\<in>M" "t1\<in>M" "t2\<in>M" "env\<in>list(M)"
           "nth(n,env)=t1"  "nth(m,env)=t2"
  shows "sats(M,forces_mem_fm(n,m),[P,leq,one,p]@env) \<longleftrightarrow> is_frc_at(##M,P,leq,<1,t1,t2,p>,1)"
  sorry

lemma sats_forces_eq_fm0: 
  assumes  "p\<in>M" "t1\<in>M" "t2\<in>M" "env\<in>list(M)"
  shows "sats(M,forces_eq_fm(auxren,0,1),[P,leq,one,p,t1,t2]@env) \<longleftrightarrow> is_frc_at(##M,P,leq,<0,t1,t2,p>,1)"
proof -
  have satsMH:"(is_Hfrc_at(##M, P, leq, a2, a1, a0) \<longleftrightarrow>
        sats(M, is_Hfrc_at_fm(5, 6, 2, 1, 0),
        [a0,a1,a2,a3,a4,P,leq,forcerel(P,<0,t1,t2,p>),<0,t1,t2,p>,1,0, one,p,t1,t2]@env))" 
    if "a0\<in>M" "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" for a0 a1 a2 a3 a4
    using that assms P_in_M leq_in_M one_in_M 
        sats_is_Hfrc_at_fm[of 5 6 2 1 0 
        "[a0,a1,a2,a3,a4,P,leq,forcerel(P,<0,t1,t2,p>),<0,t1,t2,p>,1,0, one,p,t1,t2]@env"]
        tuples_in_M zero_in_M oneN_in_M forcerel_in_M by simp
  have "sats(M,is_wfrec_fm(is_Hfrc_at_fm(5,6,2,1,0),2,3,4),
            [P,leq,forcerel(P,<0,t1,t2,p>),<0,t1,t2,p>,1,0, one,p,t1,t2]@env) \<longleftrightarrow>
        is_frc_at(##M,P,leq,<0,t1,t2,p>,1)" 
    unfolding is_frc_at_def using assms P_in_M leq_in_M one_in_M
      forcerel_in_M tuples_in_M oneN_in_M zero_in_M sats_is_wfrec_fm[OF satsMH[simplified]]
    by simp
  then show ?thesis using assms P_in_M one_in_M leq_in_M sats_forces_eq_fm' by simp
qed

(* por qué tenemos el env? *)
(*
lemma sats_forces_eq_fm:
  assumes  "[P,leq,one,p,t1,t2] @ env \<in> list(M)"
  shows "sats(M,forces_eq_fm(auxren,0,1),[P,leq,one,p,t1,t2] @ env) \<longleftrightarrow> is_frc_at(##M,P,leq,<0,t1,t2,p>,1)"
proof -
  note assms
  moreover from this
  have "forcerel(P,\<langle>0, t1, t2, p\<rangle>)\<in>M" "\<langle>0, t1, t2, p\<rangle>\<in>M"
    using tuples_in_M cons_closed eclose_closed M_inhabit forcerel_closed by simp_all
  moreover from calculation
  have "is_wfrec(##M,is_Hfrc_at(##M,P,leq),forcerel(P,\<langle>0,t1,t2,p\<rangle>),\<langle>0,t1,t2,p\<rangle>,1) \<longleftrightarrow>
   is_wfrec(##M,\<lambda>x f z. z = bool_of_o(Hfrc(P,leq,x,f)),forcerel(P,\<langle>0,t1,t2,p\<rangle>),\<langle>0,t1,t2,p\<rangle>,1)"
    using tuples_in_M oneN_in_M is_wfrec_cong[OF _ _ _ Hfrc_at_abs] (* esto es horrible *)
    by simp
  moreover from assms
  have "Ord(length(env))" using nat_into_Ord[OF length_type, of env M] by simp
  ultimately
  show ?thesis
  unfolding is_frc_at_def 
  using forcerel_closed sats_forces_eq_fm' eclose_closed oneN_in_M M_inhabit tuples_in_M cons_closed
    sats_is_wfrec_fm[OF MH[simplified], of "[forcerel(P,<0,t1,t2,p>), <0,t1,t2,p>, 1, 0, one, p, t1, t2] @ env" 2 3 4]
     Hfrc_at_abs nat_into_Ord[OF length_type, of env M] by simp
qed
*)

lemma forces_ren_type [TC]:  "\<phi>\<in>formula \<Longrightarrow> forces_ren(auxren,fren,fref, \<phi>) \<in> formula" 
  by (induct \<phi> set:formula; simp)

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

lemma sats_forces_ren_Nand: 
  assumes 
    "[P,leq,one,p] @ env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "sats(M,forces_ren(auxren,fren,fref,Nand(\<phi>,\<psi>)),[P,leq,one,p] @ env) \<longleftrightarrow>
          (\<forall>x\<in>M. x\<in>P \<longrightarrow> \<langle>x, p\<rangle> \<in> leq \<longrightarrow>
          \<not> (sats(M, forces_ren(auxren,fren,fref,\<phi>),[P,leq,one,x] @ env) \<and>
             sats(M, forces_ren(auxren,fren,fref,\<psi>),[P,leq,one,x] @ env)))"
proof -
  from assms
  have "sats(M,forces_ren(auxren,fren,fref,Nand(\<phi>,\<psi>)),[P,leq,one,p] @ env) \<longleftrightarrow>
          (\<forall>x\<in>M. x\<in>P \<longrightarrow> \<langle>x, p\<rangle> \<in> leq \<longrightarrow>
          \<not> (sats(M, fren`forces_ren(auxren,fren,fref,\<phi>),[\<langle>x, p\<rangle>,x,P,leq,one,p] @ env) \<and>
             sats(M, fren`forces_ren(auxren,fren,fref,\<psi>),[\<langle>x, p\<rangle>,x,P,leq,one,p] @ env)))"
    using tuples_in_M  by simp
  also from assms
  have "... \<longleftrightarrow> (\<forall>x\<in>M. x\<in>P \<longrightarrow> \<langle>x, p\<rangle> \<in> leq \<longrightarrow>
          \<not> (sats(M, forces_ren(auxren,fren,fref,\<phi>),[P,leq,one,x] @ env) \<and>
             sats(M, forces_ren(auxren,fren,fref,\<psi>),[P,leq,one,x] @ env)))"
    using tuples_in_M sats_fren by simp
  finally
  show ?thesis .
qed

lemma sats_forces_ren_Neg: "\<lbrakk> [P,leq,one,p] @ env \<in> list(M); \<phi>\<in>formula\<rbrakk> \<Longrightarrow>
          sats(M,forces_ren(auxren,fren,fref,Neg(\<phi>)),[P,leq,one,p] @ env) \<longleftrightarrow> 
          (\<forall>q\<in>M. q\<in>P \<longrightarrow> \<langle>q, p\<rangle> \<in> leq \<longrightarrow>
          \<not> sats(M, forces_ren(auxren,fren,fref,\<phi>),[P,leq,one,q] @ env))" 
  unfolding Neg_def sats_forces_ren_Nand
  by simp

lemma sats_forces_ren_Forall:
  assumes
    "p\<in>P" "[P,leq,one,p] @ env \<in> list(M)" "\<phi>\<in>formula"
  shows
    "sats(M,forces_ren(auxren,fren,fref,Forall(\<phi>)),[P,leq,one,p] @ env) \<longleftrightarrow> 
     (\<forall>x\<in>M. sats(M, forces_ren(auxren,fren,fref,\<phi>),[P,leq,one,p,x] @ env))"
  using assms sats_fref by simp

lemma sats_forces_ren_Equal:
  assumes
    "p\<in>P" "[P,leq,one,p,x,y] @ env \<in> list(M)" 
  shows
    "sats(M,forces_ren(auxren,fren,fref,Equal(0,1)),[P,leq,one,p,x,y] @ env) \<longleftrightarrow> 
     is_frc_at(##M,P,leq,<0,x,y,p>,1)"
  using assms sats_forces_eq_fm[of 0 1 p x y] forcerel_in_M by simp

lemma sats_forces_Nand: 
  assumes 
    "[P,leq,one,p] @ env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula" "p\<in>P"
  shows
    "sats(M,forces(Nand(\<phi>,\<psi>)),[P,leq,one,p] @ env) \<longleftrightarrow>
          (\<forall>x\<in>M. x\<in>P \<longrightarrow> \<langle>x, p\<rangle> \<in> leq \<longrightarrow>
          \<not> (sats(M, forces(\<phi>),[P,leq,one,x] @ env) \<and>
             sats(M, forces(\<psi>),[P,leq,one,x] @ env)))" (is "?Q \<longleftrightarrow> _")
  unfolding forces_def using sats_forces_ren_Nand assms by simp

lemma sats_forces_Neg: "\<lbrakk> [P,leq,one,p] @ env \<in> list(M); \<phi>\<in>formula; p\<in>P\<rbrakk> \<Longrightarrow>
          sats(M,forces(Neg(\<phi>)),[P,leq,one,p] @ env) \<longleftrightarrow> 
          (\<forall>q\<in>M. q\<in>P \<longrightarrow> \<langle>q, p\<rangle> \<in> leq \<longrightarrow>
          \<not> sats(M, forces(\<phi>),[P,leq,one,q] @ env))" 
  unfolding forces_def using sats_forces_ren_Neg
  by simp

lemma sats_forces_Forall:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula"
  shows
    "sats(M,forces(Forall(\<phi>)),[P,leq,one,p] @ env) \<longleftrightarrow> 
     (\<forall>x\<in>M. sats(M, forces(\<phi>),[P,leq,one,p,x] @ env))"
  using assms sats_forces_ren_Forall P_in_M leq_in_M one_in_M
    Transset_intf[OF trans_M _ P_in_M] unfolding forces_def by simp

lemma sats_forces_Equal:
  assumes
    "p\<in>P" "x\<in>M" "y\<in>M" "env\<in>list(M)"
  shows
    "sats(M,forces(Equal(0,1)),[P,leq,one,p,x,y] @ env) \<longleftrightarrow> forces_eq(p,t1,t2) "
  oops

(*  using assms sats_forces_ren_Equal forcerel_in_M
    wfrec_isHfrcat_replacement frc_at_abs  M_inhabit eclose_closed
    tuples_in_M Transset_intf[OF trans_M _ P_in_M] oneN_in_M trancl_closed cons_closed
  unfolding forces_def by simp
*)
lemma
  assumes
    "p\<in>P" "[P,leq,one,p] @ env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "sats(M,forces_ren(auxren,fren,fref,And(\<phi>,\<psi>)),[P,leq,one,p] @ env) \<longleftrightarrow>
      sats(M, forces_ren(auxren,fren,fref,\<phi>),[P,leq,one,p] @ env) \<and>
      sats(M, forces_ren(auxren,fren,fref,\<psi>),[P,leq,one,p] @ env)"
  oops

end (* forces_rename *)

end
