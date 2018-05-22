(* Interface between internalized axiom formulas and 
   ZF axioms *)
theory Interface imports ZFCAxioms_formula Relative_hacked Names begin

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

(* Interface for Transset *)
lemma Transset_intf :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)
    
locale M_ZF =  
  fixes M
  assumes trans_M:          "Transset(M)"
      and M_model_ZF:       "satT(M,ZFTh,[])"
      and M_nempty:         "0 \<in> M"

begin
lemma intf_M_trivial :
  "M_trivial_no_repl(##M)"
  apply (insert trans_M M_model_ZF M_nempty)
  apply (rule M_trivial_no_repl.intro)
  apply (simp,rule Transset_intf,assumption+)
  apply (simp_all add: pairing_intf[symmetric] union_intf[symmetric] 
                       power_intf[symmetric] ZFTh_def ZF_fin_def satT_sats)
done
    
interpretation Mtriv : M_trivial_no_repl "##M" by (rule intf_M_trivial)
  

(* Separation *)
lemma uniq_dec: "<C,D> \<in> M \<Longrightarrow> 
             \<forall>A\<in>M. \<forall>B\<in>M. <C,D> = \<langle>A, B\<rangle> \<longrightarrow> P(x, A, B)
            \<longleftrightarrow>
              P(x, C, D)"
  by simp
    
lemma tupling_sep_2p :
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>A\<in>M. \<forall>B\<in>M. pair(##M,A,B,v) \<longrightarrow> P(x,A,B))))
    \<longleftrightarrow>
     (\<forall>A\<in>M. \<forall>B\<in>M. separation(##M,\<lambda>x. P(x,A,B)))"
  apply (simp add: separation_def)
proof (intro ballI iffI)
  fix A B z
  assume
        Eq1:  "\<forall>v\<in>M. \<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and> (\<forall>A\<in>M. \<forall>B\<in>M. v = \<langle>A, B\<rangle> \<longrightarrow> P(x, A, B))"
     and
        Eq2:  "A\<in>M" "B\<in>M" "z\<in>M"  (* no puedo poner la conjunción *)
  then have 
        Eq3:  "<A,B>\<in>M"
    by (simp del:setclass_iff add:setclass_iff[symmetric])
  with Eq1 have 
              "\<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and> (\<forall>C\<in>M. \<forall>D\<in>M. <A,B> = \<langle>C, D\<rangle> \<longrightarrow> P(x, C, D))"
    by (rule bspec)
  with uniq_dec and Eq3 and Eq2 show
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and>  P(x, A, B)"
    by simp
next
  fix v z
  assume
       asms:  "v\<in>M"   "z\<in>M"
              "\<forall>A\<in>M. \<forall>B\<in>M. \<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> P(x, A, B)"
  consider (a) "\<exists>A\<in>M. \<exists>B\<in>M. v = \<langle>A, B\<rangle>" | (b) "\<forall>A\<in>M. \<forall>B\<in>M. v \<noteq> \<langle>A, B\<rangle>" by auto
  then show                (* "then" is important here *)
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> 
                    (\<forall>A\<in>M. \<forall>B\<in>M. v = \<langle>A, B\<rangle> \<longrightarrow> P(x, A, B))"
  proof cases
    case a
    then obtain A B where  (* also here *)
        Eq4:  "A\<in>M" "B\<in>M" "v = \<langle>A, B\<rangle>"
      by auto
    then have
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> P(x, A, B)"
      using asms by simp
    then show ?thesis using Eq4 and uniq_dec by simp
  next
    case b
    then have
              "\<forall>x\<in>M. x \<in> z \<longleftrightarrow> x \<in> z \<and> (\<forall>A\<in>M. \<forall>B\<in>M. v = \<langle>A, B\<rangle> \<longrightarrow> P(x, A, B))"
      by simp
    then show ?thesis using b and asms by auto
  qed
qed
  
lemma tupling_sep_5p : 
"(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. 
                  v = \<langle>A1, \<langle>A2, \<langle>A3, \<langle>A4, A5\<rangle>\<rangle>\<rangle>\<rangle> \<longrightarrow> P(x,A1,A2,A3,A4,A5))))
    \<longleftrightarrow>
 (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. separation(##M,\<lambda>x. P(x,A1,A2,A3,A4,A5)))"
  sorry
  
  
end
  
(* Tupling para fórmula para instancia de separación.
   Se asume que la aridad es 3: las dos primeras variables son los
   parámetros que se van a tuplear, la siguiente es el x de separación*)
  


definition 
  tupling_fm_2_params :: "i \<Rightarrow> i" where
  "tupling_fm_2_params(\<phi>) = Forall(Forall(Implies(pair_fm(1,0,3),\<phi>)))"

lemma [TC] :  "\<lbrakk> \<phi> \<in> formula \<rbrakk> \<Longrightarrow> tupling_fm_2_params(\<phi>) \<in> formula"
  by (simp add: tupling_fm_2_params_def)
    
lemma arity_tup2p :  
  "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>) = 3 \<rbrakk> \<Longrightarrow> arity(tupling_fm_2_params(\<phi>)) = 2"
  by (simp add: tupling_fm_2_params_def arity_incr_bv_lemma pair_fm_def 
                upair_fm_def Un_commute nat_union_abs1)
  
lemma separation_intf : 
      "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>)=1 \<or> arity(\<phi>)=2 \<rbrakk> \<Longrightarrow> 
        sats(M,separation_ax_fm(\<phi>),[]) \<longleftrightarrow> 
       (\<forall>a\<in>M. separation(##M,\<lambda>x. sats(M,\<phi>,[x,a])))"
  by (simp add: separation_ax_fm_def separation_def sats_incr_bv1_iff)
    

(* Instances of separation for interface with M_basic *)
lemma inter_sep_intf :
  "sats(M,separation_ax_fm(Forall(Implies(Member(0,2),Member(1,0)))),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. separation(##M,\<lambda>x . \<forall>y\<in>M . y\<in>A \<longrightarrow> x\<in>y))"
  by (simp add: separation_def separation_intf separation_ax_fm_def sats_incr_bv1_iff)

lemma diff_sep_intf :
  "sats(M,separation_ax_fm(Neg(Member(0,1))),[])
  \<longleftrightarrow>
  (\<forall>B\<in>M. separation(##M,\<lambda>x . x\<notin>B))"
  by (simp add: separation_def separation_intf separation_ax_fm_def sats_incr_bv1_iff)
    
  (* cartprod_sep_fm vars:
     0 \<longrightarrow> B
     1 \<longrightarrow> A
     2 \<longrightarrow> x *)
definition
  cartprod_sep_fm :: "i" where
  "cartprod_sep_fm == 
              Exists(And(Member(0,2),
                     Exists(And(Member(0,2),pair_fm(1,0,4)))))"

lemma cartprof_sep_fm_type [TC] : 
  "cartprod_sep_fm \<in> formula"
  by (simp add: cartprod_sep_fm_def)
    
lemma [simp] : "arity(cartprod_sep_fm) = 3" 
  by (simp add: cartprod_sep_fm_def pair_fm_def upair_fm_def 
                Un_commute nat_union_abs1)


lemma (in M_ZF) cartprod_sep_intf :
  "sats(M,separation_ax_fm(tupling_fm_2_params(cartprod_sep_fm)),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. \<forall>B\<in>M. separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A \<and> (\<exists>y\<in>M. y\<in>B \<and> pair(##M,x,y,z))))"
  apply (rule iff_trans)
   apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp+)
  apply (rule iff_trans) 
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2_params_def cartprod_sep_fm_def)
  done
  
definition
  image_sep_fm :: "i" where
  "image_sep_fm == 
    Exists(And(Member(0,1),
          Exists(And(Member(0,3),pair_fm(0,4,1)))))"
  
lemma image_sep_fm_type [TC] : 
  "image_sep_fm \<in> formula"
  by (simp add: image_sep_fm_def)

    
lemma [simp] : "arity(image_sep_fm) = 3" 
  by (simp add: image_sep_fm_def pair_fm_def upair_fm_def 
                Un_commute nat_union_abs1)
               

lemma (in M_ZF) image_sep_intf :
  "sats(M,separation_ax_fm(tupling_fm_2_params(image_sep_fm)),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. \<forall>r\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M. x\<in>A & pair(##M,x,y,p))))"
  apply (rule iff_trans)
   apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp+)
  apply (rule iff_trans)
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2_params_def image_sep_fm_def)
  done

definition
  converse_sep_fm :: "i" where
  "converse_sep_fm == 
    Exists(And(Member(0,2),
      Exists(Exists(And(pair_fm(1,0,2),pair_fm(0,1,3))))))"
  
lemma converse_sep_fm_type [TC] : "converse_sep_fm \<in> formula"
  by (simp add: converse_sep_fm_def)

lemma [simp] : "arity(converse_sep_fm) = 2"
  by (simp add: converse_sep_fm_def pair_fm_def upair_fm_def 
                Un_commute nat_union_abs1)
    
lemma converse_sep_intf : 
  "sats(M,separation_ax_fm(converse_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. separation(##M,\<lambda>z. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M.
                      \<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,z))))"
  by (simp add: separation_def separation_intf separation_ax_fm_def 
                     sats_incr_bv1_iff converse_sep_fm_def)
  
definition
  restrict_sep_fm :: "i" where
  "restrict_sep_fm == Exists(And(Member(0,2),Exists(pair_fm(1,0,2))))"

lemma restrict_sep_fm_type [TC] : "restrict_sep_fm \<in> formula"
  by (simp add: restrict_sep_fm_def)
    
lemma [simp] : "arity(restrict_sep_fm) = 2"
  by (simp add: restrict_sep_fm_def pair_fm_def upair_fm_def 
                Un_commute nat_union_abs1)

lemma restrict_sep_intf :
  "sats(M,separation_ax_fm(restrict_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A & (\<exists>y\<in>M. pair(##M,x,y,z))))"
  by (simp add: separation_def separation_intf separation_ax_fm_def 
                     sats_incr_bv1_iff restrict_sep_fm_def)

definition 
  comp_sep_fm :: "i" where
  "comp_sep_fm ==
    Exists(Exists(Exists(Exists(Exists
      (And(pair_fm(4,2,7),And(pair_fm(4,3,1),
          And(pair_fm(3,2,0),And(Member(1,5),Member(0,6))))))))))"

lemma comp_sep_fm_type [TC] : "comp_sep_fm \<in> formula"
  by (simp add: comp_sep_fm_def)

lemma [simp] : "arity(comp_sep_fm) = 3"
  by (simp add: comp_sep_fm_def pair_fm_def upair_fm_def Un_commute nat_union_abs1)

lemma (in M_ZF) comp_sep_intf :
  "sats(M,separation_ax_fm(tupling_fm_2_params(comp_sep_fm)),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>s\<in>M. 
    separation(##M,\<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
              pair(##M,x,z,xz) & pair(##M,x,y,xy) & pair(##M,y,z,yz) &
              xy\<in>s & yz\<in>r))"
  apply (rule iff_trans)
   apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp+)
  apply (rule iff_trans)
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2_params_def comp_sep_fm_def)
  done

lemma (in M_ZF) pred_sep_intf :
  "sats(M,separation_ax_fm(
       tupling_fm_2_params(Exists(And(Member(0,2),pair_fm(3,1,0))))),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>x\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & pair(##M,y,x,p)))"
   apply (rule iff_trans)
   apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp+)
   apply (simp add: pair_fm_def upair_fm_def Un_commute nat_union_abs1)
  apply (rule iff_trans)
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2_params_def comp_sep_fm_def)
  done

definition
  memrel_fm :: "i" where
  "memrel_fm == Exists(Exists(And(pair_fm(1,0,2),Member(1,0))))"
    
lemma [TC] : "memrel_fm \<in> formula"
  by (simp add: memrel_fm_def)
  
lemma [simp] : "arity(memrel_fm) = 1"
  by (simp add: memrel_fm_def pair_fm_def upair_fm_def Un_commute nat_union_abs1)
    
lemma sats_memrel :
   "\<lbrakk> a\<in>M ; x\<in>M  \<rbrakk>  \<Longrightarrow> 
    sats(M,memrel_fm,[x,a]) \<longleftrightarrow> 
    (\<exists>z\<in>M. \<exists>y\<in>M. pair(##M,z,y,x) & z \<in> y)"
   by (simp add: memrel_fm_def)

lemma (in M_ZF) memrel_sep_intf :
  "sats(M,separation_ax_fm(memrel_fm),[])
  \<longleftrightarrow>
  separation(##M, \<lambda>z. \<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) & x \<in> y)"
  apply (simp add: separation_def separation_intf sats_memrel)
  apply (insert M_nempty,auto)
  done

(*    
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

lemmas M_basic_sep_instances = inter_sep_intf diff_sep_intf cartprod_sep_intf
                image_sep_intf converse_sep_intf restrict_sep_intf
                pred_sep_intf memrel_sep_intf comp_sep_intf is_recfun_sep_intf
    
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

lemma interface_M_basic : 
  "\<lbrakk> Transset(M) ; satT(M,ZFTh,[]) ; 0 \<in> M \<rbrakk> \<Longrightarrow> M_basic_no_repl(##M)"
  apply (rule M_basic_no_repl.intro, rule M_trivial_no_repl.intro)
    apply (simp,rule Transset_intf,assumption+)
      apply (simp_all add: pairing_intf[symmetric] union_intf[symmetric] 
                           power_intf[symmetric])
     apply (rule satT_sats,assumption,simp add: ZFTh_def ZF_fin_def)+
    apply (insert M_basic_sep_instances[of M] funspace_succ_rep_intf[of M])
    apply (rule M_basic_no_repl_axioms.intro)
    apply (simp_all add: sep_spec repl_spec)
  done
*)
end