theory Interface imports ZFCAxioms_formula Relative Names begin

(* Extensionality *)
lemma extension_intf :
   "sats(A,extension_ax_fm,[])
   \<longleftrightarrow>
   extensionality(##A)"
  by (simp add: extension_ax_fm_def extensionality_def)

(* Foundation *)
lemma foundation_intf :
  "sats(A,foundation_ax_fm,[])
   \<longleftrightarrow>
   foundation_ax(##A)"
  by (simp add: foundation_ax_fm_def foundation_ax_def)

(* Pairing *)
lemma pairing_intf :
  "sats(A,pairing_ax_fm,[])
   \<longleftrightarrow>
   upair_ax(##A)"
  by (simp add: pairing_ax_fm_def upair_ax_def)

(* Union *)
lemma union_intf :
  "sats(A,union_ax_fm,[])
  \<longleftrightarrow>
  Union_ax(##A)"
  by (simp add: union_ax_fm_def Union_ax_def)

(* Powerset *)
lemma power_intf :
  "sats(A,powerset_ax_fm,[])
  \<longleftrightarrow>
  power_ax(##A)"
  by (simp add: powerset_ax_fm_def power_ax_def powerset_def subset_def subset_fm_def)

(* Separation *)
    
lemma aux_pred2: "n\<le>2 \<Longrightarrow> Arith.pred(Arith.pred(n)) = 0"
  apply (case_tac "n=0 \<or> n=1 \<or> n=2" )
  prefer 2 apply (simp add: lt_def)
  apply auto
done    
    
lemma sep_0_params :
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) \<le> 2  \<rbrakk> \<Longrightarrow> sats(M,separation_ax_fm(\<phi>),[]) \<longleftrightarrow>
  (\<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,incr_bv1(\<phi>),[x,y,d])))"
  apply (simp add: separation_ax_fm_def)
  apply (subst aux_pred2,assumption,simp)
done
    
lemma sep_1_params : 
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 3  \<rbrakk> \<Longrightarrow> sats(M,separation_ax_fm(\<phi>),[]) \<longleftrightarrow>
  (\<forall>a\<in>M . \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,incr_bv1(\<phi>),[x,y,d,a])))"
  by (simp add: separation_ax_fm_def sats_incr_bv1_iff)

lemma sep_2_params : 
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 4  \<rbrakk> \<Longrightarrow> sats(M,separation_ax_fm(\<phi>),[]) \<longleftrightarrow>
  (\<forall>b\<in>M. \<forall>a\<in>M. \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,\<phi>,[x,d,a,b])))"
  by (simp add: separation_ax_fm_def sats_incr_bv1_iff)

lemma sep_5_params :
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 7  \<rbrakk> \<Longrightarrow> sats(M,separation_ax_fm(\<phi>),[]) \<longleftrightarrow>
  (\<forall>a5\<in>M. \<forall>a4\<in>M. \<forall>a3\<in>M. \<forall>a2\<in>M. \<forall>a1\<in>M. \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,\<phi>,[x,d,a1,a2,a3,a4,a5])))"
  by (simp add: separation_ax_fm_def sats_incr_bv1_iff)

(* VER ESTO! Importante cómo usamos el parámetro "d" *)
lemma separ_5_params :
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 7  \<rbrakk> \<Longrightarrow> sats(M,separation_ax_fm(\<phi>),[]) \<longleftrightarrow>
  (\<forall>a5\<in>M. \<forall>a4\<in>M. \<forall>a3\<in>M. \<forall>a2\<in>M. \<forall>a1\<in>M. separation(##M,\<lambda>x. sats(M,\<phi>,[x,d,a1,a2,a3,a4,a5])))"
  apply (simp add: sep_5_params separation_def)
  sorry

(* Instances of separation for interface with M_basic *)

    
lemma nat_union_abs1 : 
  "\<lbrakk> Ord(i) ; Ord(j) ; i \<le> j \<rbrakk> \<Longrightarrow> i \<union> j = j"
  by (rule Un_absorb1,erule le_imp_subset)

lemma nat_union_abs2 : 
  "\<lbrakk> Ord(i) ; Ord(j) ; i \<le> j \<rbrakk> \<Longrightarrow> j \<union> i = j"
  by (rule Un_absorb2,erule le_imp_subset)

lemma inter_sep_intf :
  "sats(M,separation_ax_fm(Forall(Implies(Member(0,3),Member(1,0)))),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. separation(##M,\<lambda>x . \<forall>y\<in>M . y\<in>A \<longrightarrow> x\<in>y))"
  apply (rule iff_trans)
   apply (rule sep_1_params,simp+)
  apply (simp add: Un_commute nat_union_abs1)
   apply (simp add: separation_def sats_incr_bv1_iff)
  done

lemma diff_sep_intf :
  "sats(M,separation_ax_fm(Neg(Member(0,2))),[])
  \<longleftrightarrow>
  (\<forall>B\<in>M. separation(##M,\<lambda>x . x\<notin>B))"
  apply (rule iff_trans,rule sep_1_params,simp+)
   prefer 2
   apply (simp add: separation_def sats_incr_bv1_iff)
  apply auto
  done

  
definition
  cartprod_sep_fm :: "i" where
  "cartprod_sep_fm == 
              Exists(And(Member(0,4),
                     Exists(And(Member(0,4),pair_fm(1,0,2)))))"

lemma cartprof_sep_fm_type [TC] : 
  "cartprod_sep_fm \<in> formula"
  by (simp add: cartprod_sep_fm_def)

lemma cartprod_sep_intf :
  "sats(M,separation_ax_fm(cartprod_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. \<forall>B\<in>M. separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A \<and> (\<exists>y\<in>M. y\<in>B \<and> pair(##M,x,y,z))))"
  apply (rule iff_trans)
   apply (rule sep_2_params)
    apply (unfold cartprod_sep_fm_def,simp+)
   prefer 2
   apply (simp add: separation_def)
  apply (simp add: pair_fm_def upair_fm_def Un_commute nat_union_abs1)
  done

definition
  image_sep_fm :: "i" where
  "image_sep_fm == 
    Exists(And(Member(0,3),
              Exists(And(Member(0,5),pair_fm(0,2,1)))))"

lemma image_sep_fm_type [TC] : 
  "image_sep_fm \<in> formula"
  by (simp add: image_sep_fm_def)

lemma image_sep_intf :
  "sats(M,separation_ax_fm(image_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. \<forall>r\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M. x\<in>A & pair(##M,x,y,p))))"
  apply (rule iff_trans)
  apply (rule sep_2_params)
    apply (unfold image_sep_fm_def,simp+)
   prefer 2
   apply (simp add: separation_def)
  apply (simp add: pair_fm_def upair_fm_def Un_commute nat_union_abs1)
  done

definition
  converse_sep_fm :: "i" where
  "converse_sep_fm == 
    Exists(And(Member(0,3),
      Exists(Exists(And(pair_fm(1,0,2),pair_fm(0,1,3))))))"

lemma converse_sep_fm_type [TC] : "converse_sep_fm \<in> formula"
  by (simp add: converse_sep_fm_def)

lemma converse_sep_intf : 
  "sats(M,separation_ax_fm(converse_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. separation(##M,\<lambda>z. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M.
                      \<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,z))))"
  apply (rule iff_trans,rule sep_1_params)
    apply (unfold converse_sep_fm_def,simp+)
   prefer 2
   apply (simp add: separation_def sats_incr_bv1_iff)
  apply (simp add: pair_fm_def upair_fm_def Un_commute nat_union_abs1)
  done
  
definition
  restrict_sep_fm :: "i" where
  "restrict_sep_fm == Exists(And(Member(0,3),Exists(pair_fm(1,0,2))))"

lemma restrict_sep_fm_type [TC] : "restrict_sep_fm \<in> formula"
  by (simp add: restrict_sep_fm_def)
 
lemma restrict_sep_intf :
  "sats(M,separation_ax_fm(restrict_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A & (\<exists>y\<in>M. pair(##M,x,y,z))))"
  apply (rule iff_trans,rule sep_1_params)
    apply (unfold restrict_sep_fm_def,simp+)
   prefer 2
   apply (simp add: separation_def sats_incr_bv1_iff)
  apply (simp add: pair_fm_def upair_fm_def Un_commute nat_union_abs1)
  done

definition 
  comp_sep_fm :: "i" where
  "comp_sep_fm ==
    Exists(Exists(Exists(Exists(Exists
      (And(pair_fm(4,2,5),And(pair_fm(4,3,1),
          And(pair_fm(3,2,0),And(Member(1,7),Member(0,8))))))))))"

lemma comp_sep_fm_type [TC] : "comp_sep_fm \<in> formula"
  by (simp add: comp_sep_fm_def)

lemma comp_sep_intf :         
  "sats(M,separation_ax_fm(comp_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>s\<in>M. 
    separation(##M,\<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
              pair(##M,x,z,xz) & pair(##M,x,y,xy) & pair(##M,y,z,yz) &
              xy\<in>s & yz\<in>r))"
  apply (rule iff_trans,rule sep_2_params)
    apply (unfold comp_sep_fm_def,simp+)
  prefer 2
   apply (simp add: separation_def)
  apply (simp add: pair_fm_def upair_fm_def Un_commute nat_union_abs1)
  done

lemma pred_sep_intf :
  "sats(M,separation_ax_fm(Exists(And(Member(0,4),pair_fm(1,3,0)))),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>x\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & pair(##M,y,x,p)))"
  apply (rule iff_trans,rule sep_2_params,simp+)
  prefer 2
   apply (simp add: separation_def)
  apply (simp add: pair_fm_def upair_fm_def Un_commute nat_union_abs1)
  done

lemma memrel_sep_intf :
  "sats(M,separation_ax_fm(Exists(Exists(And(pair_fm(1,0,2),Member(1,0))))),[])
  \<longleftrightarrow>
  separation(##M, \<lambda>z. \<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) & x \<in> y)"
  apply (rule iff_trans,rule sep_0_params,simp+)
  prefer 2
   apply (simp add: separation_def sats_incr_bv1_iff)
    apply (unfold pair_fm_def upair_fm_def)
  apply (simp add:Un_commute nat_union_abs1)
  done

definition
  is_recfun_sep_fm :: "i" where
  "is_recfun_sep_fm == 
  Exists(Exists(And(pair_fm(2,5,1),And(Member(1,8),And(pair_fm(2,4,0),And(Member(0,8),
                Exists(Exists(And(fun_apply_fm(9,4,1),And(fun_apply_fm(8,4,0),
                Neg(Equal(1,0))))))))))))"

lemma is_recfun_sep_fm [TC] : "is_recfun_sep_fm \<in> formula"
  by (simp add: is_recfun_sep_fm_def)

lemma is_recfun_sep_intf :
  "sats(M,separation_ax_fm(is_recfun_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>f\<in>M. \<forall>g\<in>M. \<forall>a\<in>M. \<forall>b\<in>M. 
    separation(##M,\<lambda>x. \<exists>xa\<in>M. \<exists>xb\<in>M.
                    pair(##M,x,a,xa) & xa \<in> r & pair(##M,x,b,xb) & xb \<in> r &
                    (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M,f,x,fx) & fun_apply(##M,g,x,gx) &
                                     fx \<noteq> gx)))" 
  apply (rule iff_trans,rule sep_5_params)
    apply (unfold is_recfun_sep_fm_def,simp+)
  prefer 2
   apply (simp add: separation_def)
  apply (simp add: pair_fm_def upair_fm_def fun_apply_fm_def big_union_fm_def image_fm_def
                  Un_commute nat_union_abs1)
  done




(* Instances of replacement for interface with M_basic *)

lemma sats_incr_bv0_iff:
  "[| p \<in> formula; env \<in> list(A); x \<in> A |]
   ==> sats(A, incr_bv(p)`0, Cons(x, env)) \<longleftrightarrow>
       sats(A, p, env)"
  by(insert sats_incr_bv_iff [of p env A x "[]"],simp)

lemma sats_incr_bv2_iff:
  "[| p \<in> formula; env \<in> list(A); x \<in> A ; y \<in> A ; z \<in> A |]
   ==> sats(A, incr_bv(p)`2, Cons(x, Cons(y,Cons(z,env)))) \<longleftrightarrow>
       sats(A, p, Cons(x,Cons(y,env)))"
  by (insert sats_incr_bv_iff [of p env A z "[x,y]"],simp)

lemma univalent_intf : 
  "\<lbrakk> \<phi> \<in> formula ; A \<in> M ; env \<in> list(M)\<rbrakk> \<Longrightarrow> 
    sats(M,univalent_fm(\<phi>),Cons(A,env)) \<longleftrightarrow> 
    univalent(##M,A,\<lambda>x. \<lambda>y. sats(M,\<phi>,[x,y,A]@env))"
  by (simp add: univalent_fm_def univalent_def sats_incr_bv1_iff
                   sats_incr_bv0_iff sats_swap_0_1)
  
lemma repl_1_params :
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 4  \<rbrakk> \<Longrightarrow> 
    sats(M,strong_replacement_ax_fm(\<phi>),[]) \<longleftrightarrow>
    (\<forall>t\<in>M. \<forall>A\<in>M. univalent(##M,A,\<lambda>x. \<lambda>y. sats(M,\<phi>,[x,y,A,t])) \<longrightarrow>
    (\<exists>Y\<in>M. \<forall>b\<in>M. b \<in> Y \<longleftrightarrow> (\<exists>x\<in>M. x\<in>A \<and> sats(M,incr_bv(\<phi>)`2,[x,b,Y,A,t]))))" 
  by (simp add: strong_replacement_ax_fm_def univalent_intf)

definition 
  is_cons_fm :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "is_cons_fm(a,b,z) == Exists(And(upair_fm(succ(a),succ(a),0),union_fm(0,succ(b),succ(z))))"

lemma is_cons_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> is_cons_fm(x,y,z) \<in> formula"
by (simp add: is_cons_fm_def)

lemma is_cons_fm [simp] :
  "\<lbrakk> a \<in> nat ; b \<in> nat ; z \<in> nat ; env \<in> list(A) \<rbrakk> \<Longrightarrow> 
    sats(A,is_cons_fm(a,b,z),env) \<longleftrightarrow> 
    is_cons(##A,nth(a,env),nth(b,env),nth(z,env))"
  by (simp add: is_cons_fm_def is_cons_def)

definition 
  funspace_succ_fm :: "i" where
  "funspace_succ_fm == 
    Exists(Exists(Exists(Exists(And(pair_fm(3,2,4),And(pair_fm(7,2,1),
        And(is_cons_fm(1,3,0),upair_fm(0,0,5))))))))"

lemma funspace_succ_fm_type [TC] : 
  "funspace_succ_fm \<in> formula"
  by (simp add: funspace_succ_fm_def)

lemma funspace_succ_rep_intf : 
  "sats(M,strong_replacement_ax_fm(funspace_succ_fm),[])
  \<longleftrightarrow>
  (\<forall>n\<in>M. strong_replacement(##M,
          \<lambda>p z. \<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M.
                pair(##M,f,b,p) & pair(##M,n,b,nb) & is_cons(##M,nb,f,cnbf) &
                upair(##M,cnbf,cnbf,z)))"
  apply (rule iff_trans, rule repl_1_params,simp)
   prefer 2
   apply (simp_all add: funspace_succ_fm_def strong_replacement_def univalent_def sats_incr_bv2_iff)
  apply (simp add: pair_fm_def upair_fm_def is_cons_fm_def union_fm_def Un_commute nat_union_abs1)
  done

(* Inifinite *)

lemma nat_included_inductive : 
    "0 \<in> I \<and> (\<forall>y\<in>I. succ(y) \<in> I) \<Longrightarrow> nat \<subseteq> I"
  apply (rule subsetI, rename_tac n)
  apply (induct_tac n, auto) 
  done

lemma sep_finite_ord_intf :
  "sats(M,separation_ax_fm(finite_ordinal_fm(0)),[])
  \<longleftrightarrow>
  (separation(##M, \<lambda>x. finite_ordinal(##M,x)))"
  apply (rule iff_trans, rule sep_0_params,simp+)
   prefer 2
   apply (simp add: separation_def sats_incr_bv1_iff)
  apply (simp add: finite_ordinal_fm_def limit_ordinal_fm_def empty_fm_def succ_fm_def cons_fm_def
                   union_fm_def upair_fm_def Un_commute nat_union_abs1)
  done

(* Interface for Transset *)
lemma Transset_intf :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)

lemma interface_M_basic : 
  "\<lbrakk> Transset(M) ; satT(M,ZFTh,[]) ; \<And>P. replacement(##M,P) ; nat \<in> M \<rbrakk> \<Longrightarrow> PROP M_basic(##M)"
  apply (rule M_basic.intro, rule M_trivial.intro)
    apply (simp,rule Transset_intf,assumption+)
    apply (simp_all add: pairing_intf[symmetric] union_intf[symmetric] power_intf[symmetric])
    apply (rule satT_sats,assumption,simp add: ZFTh_def ZF_fin_def)+
    apply (insert inter_sep_intf[of M] diff_sep_intf[of M] cartprod_sep_intf[of M]
                image_sep_intf[of M] converse_sep_intf[of M] restrict_sep_intf[of M]
                pred_sep_intf[of M] memrel_sep_intf[of M] comp_sep_intf[of M] 
                is_recfun_sep_intf[of M] funspace_succ_rep_intf[of M]
                comp_sep_intf [of M] funspace_succ_rep_intf[of M] is_recfun_sep_intf[of M])
    apply (rule M_basic_axioms.intro)
    apply (simp_all add: sep_spec repl_spec)
  done

(* aprender lemmas, que es para agrupar lemmas *)
end