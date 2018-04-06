theory Mextension imports Formula val_check ZFCaxioms begin

definition
  transClass :: "(i \<Rightarrow> o) \<Rightarrow> o" where
  "transClass(M) == \<forall>y. \<forall>x. y\<in>x \<longrightarrow> M(x) \<longrightarrow> M(y)"

locale M_model =
  fixes M
  assumes transM:           "[| y\<in>x; M(x) |] ==> M(y)"
      and upair_ax:         "upair_ax(M)"

lemma (in M_model) upair_abs [simp]:
     "M(z) ==> upair(M,a,b,z) \<longleftrightarrow> z={a,b}"
apply (simp add: upair_def)
apply (blast intro: transM)
done

lemma Transset_is_transClass :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> (##M)(x) \<Longrightarrow> (##M)(y)"
  apply (simp add: Transset_def)
  apply auto
  done

lemma is_M_model :
  "Transset(A) \<Longrightarrow> upair_ax(##A) \<Longrightarrow>
   M_model(##A)"
  apply (rule M_model.intro)
   apply (rule Transset_is_transClass,assumption+)
  done

lemma app_upair_abs : "Transset(A) \<Longrightarrow> upair_ax(##A) \<Longrightarrow> (##A)(z) \<Longrightarrow>
              upair(##A,a,b,z) \<longleftrightarrow> z={a,b}"
  apply (rule M_model.upair_abs)
   apply (rule is_M_model,assumption+)
  done

definition 
  gen_ext :: "[i,i,i] \<Rightarrow> i" where
  "gen_ext(M,P,G) = {valR(M,P,G,\<tau>). \<tau> \<in> M}"


definition
  ZFpairingStrong :: "i" where
  "ZFpairingStrong == Forall(Forall(Exists(upair_fm(2,1,0))))"

lemma ZFpair_type[TC]: "ZFpairingStrong \<in> formula"
  by (simp add: ZFpairingStrong_def)

lemma upair_fm_Pairing : 
  "(\<forall>x\<in>A. \<forall>y\<in>A . \<exists>z\<in>A . sats(A,upair_fm(0,1,2),[x,y,z]))
   \<longleftrightarrow>
   sats(A,ZFpairingStrong,[])"
  by (simp add: ZFpairingStrong_def)

lemma upair_fm_ax : 
  "(\<forall>x\<in>A. \<forall>y\<in>A . \<exists>z\<in>A . sats(A,upair_fm(0,1,2),[x,y,z]))
  \<longleftrightarrow>
   upair_ax(##A)"
  by (simp add: upair_ax_def)

lemma upairs_in_M :
  "Transset(M) \<Longrightarrow> upair_ax(##M) \<Longrightarrow> a\<in>M \<Longrightarrow> b\<in>M \<Longrightarrow> {a,b} \<in> M"
  apply (rule_tac M="##M" and P="\<lambda>z. upair(##M,a,b,z)" in rexE)
  apply (rule_tac M="##M" and x="b" and P="\<lambda>y. \<exists>z[##M]. upair(##M,a,y,z)" in rspec)
  apply (rule_tac M="##M" and x="a" and 
            P="\<lambda>x. \<forall>y[##M]. \<exists>z[##M]. upair(##M,x,y,z)" in rspec)
  apply (unfold upair_ax_def,assumption+)
  apply (simp+)
  apply (rule_tac a="x" and P="\<lambda>z. z\<in>M" in subst)
  apply (rule iffD1,rule_tac A="M" in app_upair_abs,assumption,unfold upair_ax_def)
  apply simp+
  done
  
lemma pairs_in_M : "Transset(M) \<Longrightarrow> upair_ax(##M) \<Longrightarrow> 
                    a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> uno \<in> M \<Longrightarrow>
                   {<a,uno>,<b,uno>} \<in> M"
  apply (unfold Pair_def)
  apply (rule upairs_in_M,assumption+)+
  done

lemma def_gen_ext : "x \<in> gen_ext(M,P,G) \<Longrightarrow>
                     \<exists>\<tau>\<in>M. x = valR(M,P,G,\<tau>)"
  sorry 

lemma val_sigma : "\<tau> \<in> M \<Longrightarrow> \<rho> \<in> M \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow> 
                  valR(M,P,G,{<\<tau>,uno>,<\<rho>,uno>}) = 
                  {valR(M,P,G,\<tau>),valR(M,P,G,\<rho>)}"
  sorry

(*lemma pair_in_model :"sats(A,ZFpairing,[]) \<Longrightarrow> *)

lemma sats_upair : "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> 
               sats(A,upair_fm(0,1,2),[x,y,{x,y}])"
  sorry

lemma gen_ext : "x \<in> M \<Longrightarrow> valR(M,P,G,x) \<in> gen_ext(M,P,G)"
  apply (simp add: gen_ext_def)
  apply auto
  done

(* aprendizaje: drule permite aplicar una regla en una assumption *)
theorem gen_ext_sats_pair : 
  "Transset(M) \<Longrightarrow> P \<in> M \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow> sats(M,ZFpairingStrong,[]) \<Longrightarrow> 
   sats(gen_ext(M,P,G),ZFpairingStrong,[])" 
  apply (rule iffD1,rule_tac A="gen_ext(M,P,G)" in upair_fm_Pairing)
  apply (rule ballI)+
  apply (drule def_gen_ext)+
  apply (rule_tac A="M" and P="\<lambda>w. x=valR(M,P,G,w)" in bexE,assumption)
  apply (rule_tac A="M" and P="\<lambda>w. y=valR(M,P,G,w)" in bexE,assumption)
  apply (rename_tac x y \<tau> \<rho>)
  apply (rule_tac x="valR(M,P,G,{<\<tau>,uno>,<\<rho>,uno>})" in bexI)
   apply (subst val_sigma,assumption+)
   apply (rule_tac b="x" in ssubst,assumption)
   apply (rule_tac b="y" in ssubst,assumption)
   apply (rule sats_upair)
    apply (rule gen_ext,assumption)+
  apply (rule gen_ext)
  apply (rule pairs_in_M,assumption)
     apply (rule iffD1,rule upair_fm_ax)
     apply (rule iffD2,rule upair_fm_Pairing,assumption+)
  apply (rule_tac  A="P" in subsetD)
   apply (rule transD,assumption+)
  done
