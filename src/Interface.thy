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
    
lemma sep0params :
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) \<le> 2  \<rbrakk> \<Longrightarrow> sats(M,separation_ax_fm(\<phi>),[]) \<longleftrightarrow>
  (\<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,incr_bv1(\<phi>),[x,y,d])))"
  apply (simp add: separation_ax_fm_def)
  apply (subst aux_pred2,assumption,simp)
done
    
lemma sep1params : 
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 3  \<rbrakk> \<Longrightarrow> sats(M,separation_ax_fm(\<phi>),[]) \<longleftrightarrow>
  (\<forall>a\<in>M . \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,incr_bv1(\<phi>),[x,y,d,a])))"
  by (simp add: separation_ax_fm_def sats_incr_bv1_iff)

lemma sep2params : 
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 4  \<rbrakk> \<Longrightarrow> sats(M,separation_ax_fm(\<phi>),[]) \<longleftrightarrow>
  (\<forall>b\<in>M. \<forall>a\<in>M. \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,\<phi>,[x,d,a,b])))"
  by (simp add: separation_ax_fm_def sats_incr_bv1_iff)

lemma sep5params :
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 7  \<rbrakk> \<Longrightarrow> sats(M,separation_ax_fm(\<phi>),[]) \<longleftrightarrow>
  (\<forall>a5\<in>M. \<forall>a4\<in>M. \<forall>a3\<in>M. \<forall>a2\<in>M. \<forall>a1\<in>M. \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,\<phi>,[x,d,a1,a2,a3,a4,a5])))"
  by (simp add: separation_ax_fm_def sats_incr_bv1_iff)

(* Instances of separation for interface with M_basic *)

    
lemma nat_union_abs1 : 
  "\<lbrakk> Ord(i) ; Ord(j) ; i \<le> j \<rbrakk> \<Longrightarrow> i \<union> j = j"
  by (rule Un_absorb1,erule le_imp_subset)

lemma nat_union_abs2 : 
  "\<lbrakk> Ord(i) ; Ord(j) ; i \<le> j \<rbrakk> \<Longrightarrow> j \<union> i = j"
  by (rule Un_absorb2,erule le_imp_subset)
    
    
lemma maxnat1 : 
  "1 \<union> 4 \<union> (2 \<union> 1) = 4"
  by auto

lemma maxnat2 :
  "1 \<union> 5 \<union> Arith.pred(1 \<union> 5 \<union> arity(pair_fm(1, 0, 2))) = 5"
  sorry

lemma maxnat3 :
  "Arith.pred(1 \<union> 4 \<union> Arith.pred(1 \<union> 6 \<union> arity(pair_fm(0, 2, 1)))) = 4"
  sorry

lemma maxnat4 :
  "Arith.pred(1 \<union> 4 \<union> Arith.pred(Arith.pred(arity(pair_fm(1, 0, 2)) 
      \<union> arity(pair_fm(0, 1, 3))))) = 3"
  sorry

    
lemma maxnat5 :
  "Arith.pred(1 \<union> 4 \<union> Arith.pred(arity(pair_fm(1, 0, 2)))) = 3"
  apply (unfold pair_fm_def upair_fm_def)
  apply (simp add:Un_commute nat_union_abs1)
done
    
lemma maxnat6 :
  "Arith.pred
     (Arith.pred
       (Arith.pred
         (Arith.pred
           (Arith.pred
             (arity(pair_fm(4, 2, 5)) \<union>
              (arity(pair_fm(4, 3, 1)) \<union> (arity(pair_fm(3, 2, 0)) \<union> (2 \<union> 8 \<union> (1 \<union> 9))))))))) =
    4"
  apply (unfold pair_fm_def upair_fm_def)
  apply (simp add:Un_commute nat_union_abs1)
done
    
lemma maxnat7 :
  "Arith.pred(1 \<union> 5 \<union> arity(pair_fm(1, 3, 0))) = 4"
  apply (unfold pair_fm_def upair_fm_def)
  apply (simp add:Un_commute nat_union_abs1)
done

lemma maxnat8 :
  "Arith.pred(Arith.pred(arity(pair_fm(1, 0, 2)) \<union> (2 \<union> 1))) = 1"
  apply (unfold pair_fm_def upair_fm_def)
  apply (simp add:Un_commute nat_union_abs1)
done
    
lemma maxnat9 :
  "Arith.pred
     (Arith.pred
       (arity(pair_fm(2, 5, 1)) \<union>
        (2 \<union> 9 \<union>
         (arity(pair_fm(2, 4, 0)) \<union>
          (1 \<union> 9 \<union>
           Arith.pred
            (Arith.pred
              (arity(fun_apply_fm(9, 4, 1)) \<union> (arity(fun_apply_fm(8, 4, 0)) \<union> (2 \<union> 1))))))))) =
    7"
   apply (unfold pair_fm_def upair_fm_def fun_apply_fm_def image_fm_def big_union_fm_def)
  apply (simp add:Un_commute nat_union_abs1)
done


lemma inter_sep_intf :
  "sats(M,separation_ax_fm(Forall(Implies(Member(0,3),Member(1,0)))),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. separation(##M,\<lambda>x . \<forall>y\<in>M . y\<in>A \<longrightarrow> x\<in>y))"
  apply (rule iff_trans)
   apply (rule sep1params,simp+)
   apply (subst maxnat1,simp)
   apply (simp add: separation_def sats_incr_bv1_iff)
  done

lemma diff_sep_intf :
  "sats(M,separation_ax_fm(Neg(Member(0,2))),[])
  \<longleftrightarrow>
  (\<forall>B\<in>M. separation(##M,\<lambda>x . x\<notin>B))"
  apply (rule iff_trans,rule sep1params,simp+)
   prefer 2
   apply (simp add: separation_def sats_incr_bv1_iff)
  apply auto
  done

  
definition
  cartprod_sep_fm :: "i" where
  "cartprod_sep_fm == 
              Exists(And(Member(0,4),
                     Exists(And(Member(0,4),pair_fm(1,0,2)))))"

lemma cartprod_sep_intf :
  "sats(M,separation_ax_fm(cartprod_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. \<forall>B\<in>M. separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A \<and> (\<exists>y\<in>M. y\<in>B \<and> pair(##M,x,y,z))))"
  apply (rule iff_trans)
   apply (rule sep2params)
    apply (unfold cartprod_sep_fm_def,simp+)
   prefer 2
   apply (simp add: separation_def)
  apply (subst maxnat2,simp)
  done

definition
  image_sep_fm :: "i" where
  "image_sep_fm == 
    Exists(And(Member(0,3),
              Exists(And(Member(0,5),pair_fm(0,2,1)))))"

lemma image_sep_intf :
  "sats(M,separation_ax_fm(image_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. \<forall>r\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M. x\<in>A & pair(##M,x,y,p))))"
  apply (rule iff_trans)
  apply (rule sep2params)
    apply (unfold image_sep_fm_def,simp+)
   prefer 2
   apply (simp add: separation_def)
  apply (rule maxnat3)
  done

definition
  converse_sep_fm :: "i" where
  "converse_sep_fm == 
    Exists(And(Member(0,3),
      Exists(Exists(And(pair_fm(1,0,2),pair_fm(0,1,3))))))"

lemma converse_sep_intf : 
  "sats(M,separation_ax_fm(converse_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. separation(##M,\<lambda>z. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M.
                      \<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,z))))"
  apply (rule iff_trans,rule sep1params)
    apply (unfold converse_sep_fm_def,simp+)
   prefer 2
   apply (simp add: separation_def sats_incr_bv1_iff)
  apply (rule maxnat4)
  done
  
definition
  restrict_sep_fm :: "i" where
  "restrict_sep_fm == Exists(And(Member(0,3),Exists(pair_fm(1,0,2))))"

lemma restrict_sep_intf :
  "sats(M,separation_ax_fm(restrict_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A & (\<exists>y\<in>M. pair(##M,x,y,z))))"
  apply (rule iff_trans,rule sep1params)
    apply (unfold restrict_sep_fm_def,simp+)
   prefer 2
   apply (simp add: separation_def sats_incr_bv1_iff)
  apply (rule maxnat5)
  done

definition 
  comp_sep_fm :: "i" where
  "comp_sep_fm ==
    Exists(Exists(Exists(Exists(Exists
      (And(pair_fm(4,2,5),And(pair_fm(4,3,1),
          And(pair_fm(3,2,0),And(Member(1,7),Member(0,8))))))))))"

lemma comp_sep_intf : 
  "sats(M,separation_ax_fm(comp_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>s\<in>M. 
    separation(##M,\<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
              pair(##M,x,z,xz) & pair(##M,x,y,xy) & pair(##M,y,z,yz) &
              xy\<in>s & yz\<in>r))"
  apply (rule iff_trans,rule sep2params)
    apply (unfold comp_sep_fm_def,simp+)
  prefer 2
   apply (simp add: separation_def)
  apply (subst maxnat6,simp)
  done

lemma pred_sep_intf :
  "sats(M,separation_ax_fm(Exists(And(Member(0,4),pair_fm(1,3,0)))),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>x\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & pair(##M,y,x,p)))"
  apply (rule iff_trans,rule sep2params,simp+)
  prefer 2
   apply (simp add: separation_def)
  apply (rule maxnat7)
  done

lemma memrel_sep_intf :
  "sats(M,separation_ax_fm(Exists(Exists(And(pair_fm(1,0,2),Member(1,0))))),[])
  \<longleftrightarrow>
  separation(##M, \<lambda>z. \<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) & x \<in> y)"
  apply (rule iff_trans,rule sep0params,simp+)
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

lemma is_recfun_sep_intf :
  "sats(M,separation_ax_fm(is_recfun_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>f\<in>M. \<forall>g\<in>M. \<forall>a\<in>M. \<forall>b\<in>M. 
    separation(##M,\<lambda>x. \<exists>xa\<in>M. \<exists>xb\<in>M.
                    pair(##M,x,a,xa) & xa \<in> r & pair(##M,x,b,xb) & xb \<in> r &
                    (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M,f,x,fx) & fun_apply(##M,g,x,gx) &
                                     fx \<noteq> gx)))" 
  apply (rule iff_trans,rule sep5params)
    apply (unfold is_recfun_sep_fm_def,simp+)
  prefer 2
   apply (simp add: separation_def)
  apply (rule maxnat9)
  done

(* Instances of replacement for interface with M_basic *)
lemma repl1params :
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 4  \<rbrakk> \<Longrightarrow> 
    sats(M,replacement_ax_fm(\<phi>),[]) \<longleftrightarrow>
    (\<forall>t\<in>M. \<forall>A\<in>M. univalent(##M,A,\<lambda>x. \<lambda>y. sats(M,\<phi>,[x,y,A,t])) \<longrightarrow>
    (\<exists>Y\<in>M. \<forall>b\<in>M. b \<in> Y \<longleftrightarrow> (\<exists>x\<in>M. x\<in>A \<and> sats(M,\<phi>,[x,b,Y,A,t]))))" 
  sorry

definition 
  is_cons_fm :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "is_cons_fm(a,b,z) == Exists(And(upair_fm(a,a,0),union_fm(0,b,z)))"

lemma is_cons_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> is_cons_fm(x,y,z) \<in> formula"
by (simp add: is_cons_fm_def)

definition 
  funspace_succ_fm :: "i" where
  "funspace_succ_fm == 
    Exists(Exists(Exists(Exists(And(pair_fm(3,2,4),And(pair_fm(6,2,1),
        And(is_cons_fm(1,3,0),upair_fm(0,0,5))))))))"

lemma funspace_succ_rep_intf : 
  "sats(M,replacement_ax_fm(funspace_succ_fm),[])
  \<longleftrightarrow>
  (\<forall>n\<in>M. strong_replacement(##M,
          \<lambda>p z. \<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M.
                pair(##M,f,b,p) & pair(##M,n,b,nb) & is_cons(##M,nb,f,cnbf) &
                upair(##M,cnbf,cnbf,z)))"
  apply (rule iff_trans, rule repl1params)
    apply (unfold funspace_succ_fm_def,simp+)
  prefer 2
  apply (simp add: strong_replacement_def)

(*
M(n) ==>
      strong_replacement(M, \<lambda>p z. \<exists>f[M]. \<exists>b[M]. \<exists>nb[M]. \<exists>cnbf[M].
                pair(M,f,b,p) & pair(M,n,b,nb) & is_cons(M,nb,f,cnbf) &
                upair(M,cnbf,cnbf,z))"
*)

end