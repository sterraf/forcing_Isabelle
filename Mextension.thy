theory Mextension imports Formula val_check ZFCaxioms begin

definition 
  gen_ext :: "[i,i,i] \<Rightarrow> i" where
  "gen_ext(M,P,G) = {valR(M,P,G,\<tau>). \<tau> \<in> M}"


lemma upair_fm_Pairing : 
  "(\<forall>x\<in>A. \<forall>y\<in>A . \<exists>z\<in>A . sats(A,upair_fm(0,1,2),[x,y,z]))
   \<longleftrightarrow>
   sats(A,ZFpairing,[])"
  sorry

lemma def_gen_ext : "x \<in> gen_ext(M,P,G) \<Longrightarrow>
                     \<exists>\<tau>\<in>M. x = valR(M,P,G,\<tau>)"
  sorry 

lemma val_sigma : "\<tau> \<in> M \<Longrightarrow> \<rho> \<in> M \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow> 
                  valR(M,P,G,{<\<tau>,uno>,<\<rho>,uno>}) = 
                  {valR(M,P,G,\<tau>),valR(M,P,G,\<rho>)}"
  sorry

(*lemma pair_in_model :"sats(A,ZFpairing,[]) \<Longrightarrow> *)

lemma sigma_in_M : "\<tau> \<in> M \<Longrightarrow> \<rho> \<in> M \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow>
                   {<\<tau>,uno>,<\<rho>,uno>} \<in> M"
  sorry

lemma sats_upair : "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> 
               sats(A,upair_fm(0,1,2),[x,y,{x,y}])"
  sorry

lemma gen_ext : "x \<in> M \<Longrightarrow> valR(M,P,G,x) \<in> gen_ext(M,P,G)"
  apply (simp add: gen_ext_def)
  apply auto
  done

(* aprendizaje: drule permite aplicar una regla en una assumption *)
theorem gen_ext_sats_pair : 
  "uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow> sats(M,ZFpairing,[]) \<Longrightarrow> 
   sats(gen_ext(M,P,G),ZFpairing,[])" 
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
