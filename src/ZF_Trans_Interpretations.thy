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

definition is_order_body
  where "is_order_body(M,X,x,z) \<equiv> \<exists>A[M]. cartprod(M,X,X,A) \<and> subset(M,x,A) \<and> M(z) \<and> M(x) \<and>
           is_well_ord(M,X, x) \<and> is_ordertype(M,X, x,z)"


synthesize "is_order_body" from_definition assuming "nonempty"
arity_theorem for "pred_set_fm"
arity_theorem for "is_ordermap_fm"
arity_theorem for "image_fm"
arity_theorem for "lambda_fm"
arity_theorem for "is_ordertype_fm"
arity_theorem for "is_order_body_fm"

lemma arity_is_order_body: "arity(is_order_body_fm(2,0,1)) = 3"
  sorry

lemma (in M_ZF_trans) replacement_is_order_body:
 "X\<in>M \<Longrightarrow> strong_replacement(##M, is_order_body(##M,X))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f,X] \<Turnstile> is_order_body_fm(2,0,1)",THEN iffD1])
   apply(rule_tac is_order_body_iff_sats[where env="[_,_,X]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax[where env="[X]",simplified])
    apply(simp_all add: arity_is_order_body )
  done

(*FIXME: move this to CardinalArith_Relative *)
lemma (in M_pre_cardinal_arith) is_order_body_abs :
  "M(X) \<Longrightarrow> M(x) \<Longrightarrow> M(z) \<Longrightarrow> is_order_body(M, X, x, z) \<longleftrightarrow>
   M(z) \<and> M(x) \<and> x\<in>Pow_rel(M,X\<times>X) \<and> well_ord(X, x) \<and> z = ordertype(X, x)"
  using well_ord_abs is_well_ord_iff_wellordered is_ordertype_iff' ordertype_rel_abs
  well_ord_is_linear subset_abs Pow_rel_char
  unfolding is_order_body_def 
  by simp


definition H_order_pred where
  "H_order_pred(A,r) \<equiv>  \<lambda>x f . f `` Order.pred(A, x, r)"

relationalize "H_order_pred" "is_H_order_pred"

lemma (in M_basic) H_order_pred_abs :
  "M(A) \<Longrightarrow> M(r) \<Longrightarrow> M(x) \<Longrightarrow> M(f) \<Longrightarrow> M(z) \<Longrightarrow>
    is_H_order_pred(M,A,r,x,f,z) \<longleftrightarrow> z = H_order_pred(A,r,x,f)"
  unfolding is_H_order_pred_def H_order_pred_def
  by simp

synthesize "is_H_order_pred" from_definition assuming "nonempty"

definition order_pred_wfrec_body where
 "order_pred_wfrec_body(M,A,r,z,x) \<equiv> \<exists>y[M].
                pair(M, x, y, z) \<and>
                (\<exists>f[M].
                    (\<forall>z[M].
                        z \<in> f \<longleftrightarrow>
                        (\<exists>xa[M].
                            \<exists>y[M].
                               \<exists>xaa[M].
                                  \<exists>sx[M].
                                     \<exists>r_sx[M].
                                        \<exists>f_r_sx[M].
                                           pair(M, xa, y, z) \<and>
                                           pair(M, xa, x, xaa) \<and>
                                           upair(M, xa, xa, sx) \<and>
                                           pre_image(M, r, sx, r_sx) \<and>
                                           restriction(M, f, r_sx, f_r_sx) \<and>
                                           xaa \<in> r \<and> (\<exists>a[M]. image(M, f_r_sx, a, y) \<and> pred_set(M, A, xa, r, a)))) \<and>
                    (\<exists>a[M]. image(M, f, a, y) \<and> pred_set(M, A, x, r, a)))"


synthesize "order_pred_wfrec_body" from_definition
arity_theorem for "order_pred_wfrec_body_fm"

lemma (in M_ZF_trans) wfrec_replacement_order_pred: 
  "A\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> wfrec_replacement(##M, \<lambda>x g z. is_H_order_pred(##M,A,r,x,g,z) , r)"
  unfolding wfrec_replacement_def is_wfrec_def M_is_recfun_def is_H_order_pred_def
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f,r,A] \<Turnstile> order_pred_wfrec_body_fm(3,2,1,0)",THEN iffD1])
   apply(subst order_pred_wfrec_body_def[symmetric])
   apply(rule_tac order_pred_wfrec_body_iff_sats[where env="[_,_,r,A]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax[where env="[r,A]",simplified])
    apply(simp_all add: arity_order_pred_wfrec_body_fm nat_simp_union)
  done

lemma (in M_ZF_trans) wfrec_replacement_order_pred':
  "A\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> wfrec_replacement(##M, \<lambda>x g z. z = H_order_pred(A,r,x,g) , r)"
  using wfrec_replacement_cong[OF H_order_pred_abs[of A r,rule_format] refl,THEN iffD1,
      OF _ _ _ _ _ wfrec_replacement_order_pred[of A r]]
  by simp

sublocale M_ZF_trans \<subseteq> M_pre_cardinal_arith "##M"
  apply (unfold_locales)
  using separation_instances wfrec_replacement_order_pred'[unfolded H_order_pred_def]
  apply simp_all
  sorry

lemma (in M_ZF_trans) replacement_ordertype: 
  "X\<in>M \<Longrightarrow> strong_replacement(##M, \<lambda>x z. z \<in> M \<and> x \<in> M \<and> x \<in> Pow\<^bsup>M\<^esup>(X \<times> X) \<and> well_ord(X, x) \<and> z = ordertype(X, x))"
  using strong_replacement_cong[THEN iffD1,OF _ replacement_is_order_body,simplified] is_order_body_abs
  unfolding is_order_body_def
  by simp

lemma arity_is_jump_cardinal_body: "arity(is_jump_cardinal_body'_fm(0,1)) = 2"
  sorry

lemma (in M_ZF_trans) replacement_is_jump_cardinal_body:
 "strong_replacement(##M, is_jump_cardinal_body'(##M))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f] \<Turnstile> is_jump_cardinal_body'_fm(0,1)",THEN iffD1])
   apply(rule_tac is_jump_cardinal_body'_iff_sats[where env="[_,_]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax[where env="[]",simplified])
    apply(simp_all add: arity_is_jump_cardinal_body )
  done

(*FIXME: move this to CardinalArith_Relative *)
lemma (in M_pre_cardinal_arith) univalent_aux2: "M(X) \<Longrightarrow> univalent(M,Pow_rel(M,X\<times>X),
  \<lambda>r z. M(z) \<and> M(r) \<and> is_well_ord(M, X, r) \<and> is_ordertype(M, X, r, z))"
  using is_well_ord_iff_wellordered
    is_ordertype_iff[of _ X]
    trans_on_subset[OF well_ord_is_trans_on]
     well_ord_is_wf[THEN wf_on_subset_A] mem_Pow_rel_abs
  unfolding univalent_def
  by (simp)

lemma (in M_pre_cardinal_arith) is_jump_cardinal_body_abs :
  "M(X) \<Longrightarrow> M(c) \<Longrightarrow> is_jump_cardinal_body'(M, X, c) \<longleftrightarrow> c = jump_cardinal_body'_rel(M,X)"
  using well_ord_abs is_well_ord_iff_wellordered is_ordertype_iff' ordertype_rel_abs
  well_ord_is_linear subset_abs Pow_rel_iff Replace_abs[of "Pow_rel(M,X\<times>X)",OF _ _ 
    univalent_aux2]
  unfolding is_jump_cardinal_body'_def jump_cardinal_body'_rel_def
  by simp

lemma (in M_ZF_trans) replacement_jump_cardinal_body: 
  "strong_replacement(##M, \<lambda>x z. z \<in> M \<and> x \<in> M \<and> z = jump_cardinal_body(##M, x))"
  using strong_replacement_cong[THEN iffD1,OF _ replacement_is_jump_cardinal_body,simplified] 
    jump_cardinal_body_eq is_jump_cardinal_body_abs
  by simp

sublocale M_ZF_trans \<subseteq> M_pre_aleph "##M"
  apply (unfold_locales)
  using replacement_ordertype replacement_jump_cardinal_body HAleph_wfrec_repl
  by simp_all

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
  apply (unfold_locales)
  apply (simp_all add: lam_replacement_vimage_sing_fun lam_replacement_imp_strong_replacement)
  sorry

end