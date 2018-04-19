theory MG_sats_pair imports Formula val_check ZFCaxioms begin

(* Internalized version of Strong Pairing axiom *)
definition
  ZFpairingStrong :: "i" where
  "ZFpairingStrong == Forall(Forall(Exists(upair_fm(2,1,0))))"

lemma ZFpair_type[TC]: "ZFpairingStrong \<in> formula"
  by (simp add: ZFpairingStrong_def)


(* Equivalence between versions of Pairing *)
lemma upair_fm_Pairing[simp] : 
   "sats(A,ZFpairingStrong,[])
   \<longleftrightarrow>
   (\<forall>x\<in>A. \<forall>y\<in>A . \<exists>z\<in>A . sats(A,upair_fm(0,1,2),[x,y,z]))"
  by (simp add: ZFpairingStrong_def)

lemma upair_fm_ax[simp] : 
  "(\<forall>x\<in>A. \<forall>y\<in>A . \<exists>z\<in>A . sats(A,upair_fm(0,1,2),[x,y,z]))
  \<longleftrightarrow>
   upair_ax(##A)"
  by (simp add: upair_ax_def)

lemma pairStrong_upair_ax :
  "sats(A,ZFpairingStrong,[]) \<Longrightarrow> upair_ax(##A)"
  apply (simp add: upair_ax_def)
  done


lemma sats_upair : "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> {x,y} \<in> A \<Longrightarrow> 
               sats(A,upair_fm(0,1,2),[x,y,{x,y}])"
  apply (unfold upair_fm_def)
  apply (rule sats_And_iff [THEN iffD2])
  apply (auto)
done


(* We define a "locale" with the hipothesis about model M *)
locale M_model =
  fixes M P G uno
  assumes trans_M:          "Transset(M)"
      and upair_M:          "upair_ax(##M)"
      and Union_M:          "Union_ax(##M)"
      and P_in_M:           "P \<in> M"
      and uno_in_P:         "uno \<in> P"
      and uno_in_G:         "uno \<in> G"

lemma is_M_model :
  "Transset(A) \<Longrightarrow> upair_ax(##A) \<Longrightarrow> Union_ax(##A) \<Longrightarrow> 
   P \<in> A \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow>
   M_model(A,P,G,uno)"
  by (rule M_model.intro,assumption+)

lemma Transset_M :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)

lemma (in M_model) upair_abs [simp]:
     "z \<in> M ==> upair(##M,a,b,z) \<longleftrightarrow> z={a,b}"
  apply (simp add: upair_def)
  apply (insert trans_M)
  apply (blast intro: Transset_M)
  done


(* Definition of the generic extension of M (M[G]) *)
definition 
  gen_ext :: "[i,i,i] \<Rightarrow> i" where
  "gen_ext(M,P,G) = {valR(M,P,G,\<tau>). \<tau> \<in> M}"


lemma (in M_model) upairs_in_M :
  "a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> {a,b} \<in> M"
  apply (rule_tac M="##M" and P="\<lambda>z. upair(##M,a,b,z)" in rexE)
  apply (rule_tac M="##M" and x="b" and P="\<lambda>y. \<exists>z[##M]. upair(##M,a,y,z)" in rspec)
  apply (rule_tac M="##M" and x="a" and 
            P="\<lambda>x. \<forall>y[##M]. \<exists>z[##M]. upair(##M,x,y,z)" in rspec)
  apply (insert upair_M,simp add: upair_ax_def,simp+)
  done

lemma (in M_model) uno_in_M : "uno \<in> M"
  by (insert trans_M,insert uno_in_P,insert P_in_M,rule Transset_M)
 
lemma (in M_model) pairs_in_M : 
  " a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> {<a,uno>,<b,uno>} \<in> M"
  apply (insert uno_in_M)
  apply (unfold Pair_def)
  apply ((rule upairs_in_M)+,assumption+)+
  done

lemma (in M_model) def_gen_ext : 
  "x \<in> gen_ext(M,P,G) \<Longrightarrow> \<exists>\<tau>\<in>M. x = valR(M,P,G,\<tau>)"
  apply (unfold gen_ext_def)
  apply (rule RepFun_iff [THEN iffD1],assumption)
  done

lemma (in M_model) in_val :
  "x \<in> valR(M,P,G,\<sigma>) \<Longrightarrow> \<exists>\<tau>\<in>domain(\<sigma>). x = valR(M,P,G,\<tau>)"
  sorry

lemma (in M_model) domain_sigma :
  "{w \<in> domain({\<langle>\<tau>, uno\<rangle>, \<langle>\<rho>, uno\<rangle>}) . 
   \<exists>p\<in>P. \<langle>w, p\<rangle> \<in> {\<langle>\<tau>, uno\<rangle>, \<langle>\<rho>, uno\<rangle>} \<and> p \<in> G} = {\<tau>,\<rho>}"
  by (insert uno_in_P,insert uno_in_G,auto)

lemma (in M_model) val_sigma : 
    "\<tau> \<in> M \<Longrightarrow> \<rho> \<in> M \<Longrightarrow> {<\<tau>,uno>,<\<rho>,uno>} \<in> M \<Longrightarrow>
     valR(M,P,G,{<\<tau>,uno>,<\<rho>,uno>}) = {valR(M,P,G,\<tau>),valR(M,P,G,\<rho>)}"
  apply (rule trans)
  apply (rule_tac h="valR(M,P,G)" in def_wfrec)
  apply (rule valR_def,rule wf_trancl,rule wf_Memrel)
  apply (unfold Hval_def)
  apply (subst domain_sigma)
  apply (subst lam_dom,auto)
  apply (rule_tac a="\<tau>" and b="{\<langle>\<tau>, uno\<rangle>, \<langle>\<rho>, uno\<rangle>}" in vimageI)
  apply (insert trans_M)
  apply (rule e3_Memrel,assumption+)
  apply (rule_tac  a="{\<tau>}" and b="<\<tau>,uno>" in e3I,simp)
  apply (simp add: Pair_def,simp+)
  apply (rule_tac a="\<rho>" and b="{\<langle>\<tau>, uno\<rangle>, \<langle>\<rho>, uno\<rangle>}" in vimageI)
  apply (rule e3_Memrel,assumption+)
  apply (rule_tac  a="{\<rho>}" and b="<\<rho>,uno>" in e3I,simp)
  apply (simp add: Pair_def,simp+)
  done
  
lemma (in M_model) gen_ext : 
  "x \<in> M \<Longrightarrow> valR(M,P,G,x) \<in> gen_ext(M,P,G)"
  apply (simp add: gen_ext_def)
  apply auto
  done

theorem (in M_model) gen_ext_sats_pair : 
  "sats(gen_ext(M,P,G),ZFpairingStrong,[])"
  apply (rule iffD2,rule_tac A="gen_ext(M,P,G)" in upair_fm_Pairing)
  apply (rule ballI)+
  apply (drule def_gen_ext)+
  apply (rule_tac A="M" and P="\<lambda>w. x=valR(M,P,G,w)" in bexE,assumption)
  apply (rule_tac A="M" and P="\<lambda>w. y=valR(M,P,G,w)" in bexE,assumption)
  apply (rename_tac x y \<tau> \<rho>)
  apply (rule_tac x="valR(M,P,G,{<\<tau>,uno>,<\<rho>,uno>})" in bexI)
  apply (subst val_sigma,assumption+)
  apply (insert trans_M,insert upair_M,insert P_in_M,insert uno_in_P,insert uno_in_G)
  apply (rule_tac a="\<tau>" and b="\<rho>" in pairs_in_M,assumption+)
  apply (rule_tac b="x" in ssubst,assumption)
  apply (rule_tac b="y" in ssubst,assumption)
  apply (rule sats_upair)
  apply (rule gen_ext,assumption)+
  apply (subst val_sigma[symmetric],assumption+)
  apply (rule pairs_in_M,assumption+)
  apply (rule gen_ext,rule pairs_in_M,assumption+)
  done


lemma (in M_model) gen_ext_trans : 
  "Transset(gen_ext(M,P,G))"
  apply (simp add: Transset_def)
  apply (rule ballI)
  apply (rule subsetI)
  apply (rename_tac y x)
  apply (drule def_gen_ext)
  apply (rule_tac A="M" and P="\<lambda>w. y=valR(M,P,G,w)" in bexE,assumption)
  apply (rename_tac y x \<sigma>)
  apply (drule_tac a="y" and P="\<lambda>w. x \<in> w" in subst,assumption)
  apply (drule in_val)
  apply (rule_tac A="domain(\<sigma>)" and P="\<lambda>w. x=valR(M,P,G,w)" in bexE,assumption)
  apply (rename_tac y x \<sigma> \<tau>)
  apply (drule in_domain_e3)
  apply (rule_tac a="valR(M,P,G,\<tau>)" and P="\<lambda>w. w \<in> gen_ext(M,P,G)" in ssubst,assumption)
  apply (rule gen_ext)
  apply (rule_tac x="\<tau>" and y="\<sigma>" in transM_e3)
  apply (insert trans_M,assumption+)
  done

lemma (in M_model) sep1params : 
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 2  \<rbrakk> \<Longrightarrow> sats(M,ZFseparation(\<phi>),[]) \<longleftrightarrow>
  (\<forall>a\<in>M . \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,\<phi>,[x,d,a])))"
  apply (unfold ZFseparation_def)
  apply (simp, fold incr_bv1_def)
  apply (simp add: sats_incr_bv1_iff)
  done

lemma (in M_model) abs_sep : 
  "(\<forall>a\<in>M . \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,\<phi>,[x,d,a]))) \<longleftrightarrow> 
  (\<forall>a\<in>M . \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,\<phi>,[x,d,a])))"
  sorry

lemma (in M_model) sep3params : 
  "\<lbrakk> \<phi>\<in>formula ; arity(\<phi>) = 4  \<rbrakk> \<Longrightarrow> sats(M,ZFseparation(\<phi>),[]) \<longleftrightarrow>
  (\<forall>a1\<in>M. \<forall>a2\<in>M. \<forall>a3\<in>M . \<forall>d\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. 
  (x\<in>y \<longleftrightarrow> x\<in>d \<and> sats(M,\<phi>,[x,d,a3,a2,a1])))"
  apply (unfold ZFseparation_def)
  apply (simp, fold incr_bv1_def)
  apply (simp add: sats_incr_bv1_iff)
  done

definition 
  ZF_big_union :: "i" where
  "ZF_big_union == Forall(Exists(big_union_fm(1,0)))"

lemma ZFbig_union_type [TC]: "ZF_big_union \<in> formula"
  by (simp add: ZF_big_union_def)

lemma ZF_union_fm[simp] : 
   "sats(A,ZF_big_union,[])
   \<longleftrightarrow>
   (\<forall>x\<in>A. \<exists>z\<in>A . sats(A,big_union_fm(1,0),[z,x]))"
  by (simp add: ZF_big_union_def)

lemma big_union_fm_ax[simp] : 
  "(\<forall>x\<in>A. \<exists>z\<in>A . sats(A,big_union_fm(1,0),[z,x]))
  \<longleftrightarrow>
   Union_ax(##A)"
  by (simp add: Union_ax_def)

lemma (in M_model) Union_abs [simp]:
  "[| A\<in>M; z\<in>M |] ==> big_union(##M,A,z) \<longleftrightarrow> z = \<Union>(A)"
  apply (simp add: big_union_def)
  apply (insert trans_M)
  apply (blast dest: Transset_M)
  done

lemma (in M_model) M_union_closed :
    "A \<in> M \<Longrightarrow> \<Union>A \<in> M"
  by (insert Union_M, simp add: Union_ax_def)


end