theory ZF_Trans_Interpretations
  imports
    Cohen_Posets_Relative
    Forcing_Main
    Interface_SepInstances
    Interface_ReplacementInstances
begin

lemmas (in M_ZF_trans) separation_instances =
  separation_well_ord
  separation_obase_equals separation_is_obase
  separation_PiP_rel separation_surjP_rel
  separation_id_body separation_rvimage_body
  separation_radd_body separation_rmult_body
  separation_ord_iso_body

lemma (in M_ZF_trans) lam_replacement_inj_rel:
  shows 
  "lam_replacement(##M, \<lambda>p. inj\<^bsup>##M\<^esup>(fst(p),snd(p)))"
  using lam_replacement_iff_lam_closed[THEN iffD2,of "\<lambda>p. inj\<^bsup>M\<^esup>(fst(p),snd(p))"]
    LambdaPair_in_M[where \<phi>="is_inj_fm(0,1,2)" and is_f="is_inj(##M)" and env="[]",OF
      is_inj_fm_type _ is_inj_iff_sats[symmetric] inj_rel_iff,simplified]
     arity_is_inj_fm[of 0 1 2] nat_simp_union transitivity fst_snd_closed
     inj_rel_closed zero_in_M
  by simp

sublocale M_ZF_trans \<subseteq> M_pre_aleph "##M"
  apply (unfold_locales)
  using separation_instances HAleph_wfrec_repl 
  apply simp_all
  sorry

arity_theorem intermediate for "is_HAleph_fm" 
lemma arity_is_HAleph_fm: "arity(is_HAleph_fm(2, 1, 0)) = 3"
  using arity_fun_apply_fm[of "11" 0 1,simplified]
    arity_is_HAleph_fm' arity_ordinal_fm arity_is_If_fm
    arity_empty_fm arity_is_Limit_fm
    arity_is_If_fm 
    arity_is_Limit_fm arity_empty_fm 
    arity_Replace_fm[where i="12" and v=10 and n=3]
    pred_Un_distrib nat_simp_union
  by simp
  
lemma arity_is_Aleph: "arity(is_Aleph_fm(0, 1)) = 2"
  unfolding is_Aleph_fm_def 
  using arity_transrec_fm[OF _ _ _ _ arity_is_HAleph_fm] nat_simp_union
  by simp

lemma (in M_ZF_trans) replacement_is_aleph:
 "strong_replacement(##M, \<lambda>x y. Ord(x) \<and> is_Aleph(##M,x,y))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x y. M,[x,y] \<Turnstile> And(ordinal_fm(0),is_Aleph_fm(0,1))",THEN iffD1])
   apply (auto simp add: ordinal_iff_sats[where env="[_,_]",symmetric])
   apply(rule_tac is_Aleph_iff_sats[where env="[_,_]",THEN iffD2],simp_all add:zero_in_M)
   apply(rule_tac is_Aleph_iff_sats[where env="[_,_]",THEN iffD1],simp_all add:zero_in_M)
  apply(rule_tac replacement_ax[where env="[]",simplified])
    apply(simp_all add:arity_is_Aleph  nat_simp_union is_Aleph_fm_type)
  done

lemma (in M_ZF_trans) replacement_aleph_rel: 
  shows  "strong_replacement(##M, \<lambda>x y. Ord(x) \<and> y = \<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup>)"
  using strong_replacement_cong[THEN iffD2,OF _ replacement_is_aleph,where P1="\<lambda>x y . Ord(x) \<and> y=Aleph_rel(##M,x)"]
     is_Aleph_iff
  by auto

sublocale M_ZF_trans \<subseteq> M_aleph "##M"
  by (unfold_locales,simp add: replacement_aleph_rel)

sublocale M_ZF_trans \<subseteq> M_FiniteFun "##M"
  using separation_supset_body separation_cons_like_rel
    replacement_range replacement_omega_funspace
  by (unfold_locales,simp_all)

sublocale M_ZFC_trans \<subseteq> M_cardinal_AC "##M"
  using choice_ax
  sorry

end