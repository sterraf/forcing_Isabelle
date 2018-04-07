theory MG_sats_pair imports Formula val_check  begin

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
      and P_in_M:           "P \<in> M"
      and uno_in_P:         "uno \<in> P"
      and uno_in_G:         "uno \<in> G"

lemma is_M_model :
  "Transset(A) \<Longrightarrow> upair_ax(##A) \<Longrightarrow> P \<in> A \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow>
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
  apply (rule_tac M="M" and P="P" and G="G" 
          in M_model.pairs_in_M,rule is_M_model,assumption+)
  apply (rule_tac b="x" in ssubst,assumption)
  apply (rule_tac b="y" in ssubst,assumption)
  apply (rule sats_upair)
  apply (rule gen_ext,assumption)+
  apply (subst val_sigma[symmetric],assumption+)
  apply (rule pairs_in_M,assumption+)
  apply (rule gen_ext,rule pairs_in_M,assumption+)
  done

end