theory Interface_ReplacementInstances
  imports
    Discipline_Function
    Forcing_Data
    Aleph_Relative
    FiniteFun_Relative
    Cardinal_Relative
begin

subsection\<open>More Instances of Replacement\<close>

text\<open>This is the same way that we used for instances of separation.\<close>
lemma (in M_ZF_trans) replacement_is_range:
 "strong_replacement(##M, \<lambda>f y. is_range(##M,f,y))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f] \<Turnstile> range_fm(0,1)",THEN iffD1])
   apply(rule_tac range_iff_sats[where env="[_,_]",symmetric])
  apply(simp_all)
  apply(rule_tac replacement_ax[where env="[]",simplified])
    apply(simp_all add:arity_range_fm nat_simp_union range_type)
  done

lemma (in M_ZF_trans) replacement_range:
 "strong_replacement(##M, \<lambda>f y. y = range(f))"
  using strong_replacement_cong[THEN iffD2,OF iff_sym[OF range_abs] replacement_is_range]
  by simp

lemma (in M_ZF_trans) replacement_is_domain:
 "strong_replacement(##M, \<lambda>f y. is_domain(##M,f,y))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f] \<Turnstile> domain_fm(0,1)",THEN iffD1])
   apply(rule_tac domain_iff_sats[where env="[_,_]",symmetric])
  apply(simp_all)
  apply(rule_tac replacement_ax[where env="[]",simplified])
    apply(simp_all add:arity_domain_fm nat_simp_union domain_type)
  done

lemma (in M_ZF_trans) replacement_domain:
 "strong_replacement(##M, \<lambda>f y. y = domain(f))"
  using strong_replacement_cong[THEN iffD2,OF iff_sym[OF domain_abs] replacement_is_domain]
  by simp

text\<open>Alternatively, we can use closure under lambda and get the stronger version.\<close>
lemma (in M_ZF_trans) lam_replacement_domain : "lam_replacement(##M, domain)"
  using lam_replacement_iff_lam_closed[THEN iffD2,of domain]
    Lambda_in_M[where \<phi>="domain_fm(0,1)" and env="[]",
      OF domain_type _ domain_iff_sats[symmetric] domain_abs,simplified]
     arity_domain_fm[of 0 1] nat_simp_union transitivity domain_closed
  by simp

text\<open>Then we recover the original version. Notice that we need closedness because we
haven't yet interpreted M_replacement.\<close>
lemma (in M_ZF_trans) replacement_domain':
 "strong_replacement(##M, \<lambda>f y. y = domain(f))"
  using lam_replacement_imp_strong_replacement_aux lam_replacement_domain domain_closed
  by simp

(*FIXME: for some reason converse is not synthesized yet. Perhaps we might use the other way? *)

lemma (in M_ZF_trans) lam_replacement_fst : "lam_replacement(##M, fst)"
  using lam_replacement_iff_lam_closed[THEN iffD2,of fst]
    Lambda_in_M[where \<phi>="fst_fm(0,1)" and env="[]",OF
      _ _  fst_iff_sats[symmetric] fst_abs] fst_type
     arity_fst_fm[of 0 1] nat_simp_union transitivity fst_closed
  by simp

lemma (in M_ZF_trans) replacement_fst':
 "strong_replacement(##M, \<lambda>f y. y = fst(f))"
  using lam_replacement_imp_strong_replacement_aux lam_replacement_fst fst_closed
  by simp


lemma (in M_ZF_trans) lam_replacement_domain1 : "lam_replacement(##M, domain)"
  using lam_replacement_iff_lam_closed[THEN iffD2,of domain]
    Lambda_in_M[where \<phi>="domain_fm(0,1)" and env="[]",OF
      _ _  domain_iff_sats[symmetric] domain_abs] domain_type
     arity_domain_fm[of 0 1] nat_simp_union transitivity domain_closed
  by simp

lemma (in M_ZF_trans) lam_replacement_snd : "lam_replacement(##M, snd)"
  using lam_replacement_iff_lam_closed[THEN iffD2,of snd]
    Lambda_in_M[where \<phi>="snd_fm(0,1)" and env="[]",OF
      _ _  snd_iff_sats[symmetric] snd_abs] snd_type
     arity_snd_fm[of 0 1] nat_simp_union transitivity snd_closed
  by simp

lemma (in M_ZF_trans) replacement_snd':
 "strong_replacement(##M, \<lambda>f y. y = snd(f))"
  using lam_replacement_imp_strong_replacement_aux lam_replacement_snd snd_closed
  by simp

lemma (in M_ZF_trans) lam_replacement_Union : "lam_replacement(##M, Union)"
  using lam_replacement_iff_lam_closed[THEN iffD2,of Union]
    Lambda_in_M[where \<phi>="big_union_fm(0,1)" and env="[]",OF
      _ _ _ Union_abs] union_fm_def big_union_iff_sats[symmetric]
     arity_big_union_fm[of 0 1] nat_simp_union transitivity Union_closed
  by simp

lemma (in M_ZF_trans) replacement_Union':
 "strong_replacement(##M, \<lambda>f y. y = Union(f))"
  using lam_replacement_imp_strong_replacement_aux lam_replacement_Union Union_closed
  by simp

lemma (in M_ZF_trans) lam_replacement_Un:
  "lam_replacement(##M, \<lambda>p. fst(p) \<union> snd(p))"
  using lam_replacement_iff_lam_closed[THEN iffD2,of "\<lambda>p. fst(p)\<union>snd(p)"]
    LambdaPair_in_M[where \<phi>="union_fm(0,1,2)" and is_f="union(##M)" and env="[]",OF
      union_type _ union_iff_sats[symmetric] union_abs]
     arity_union_fm[of 0 1 2] nat_simp_union transitivity Un_closed fst_snd_closed
  by simp

lemma (in M_ZF_trans) lam_replacement_image:
  "lam_replacement(##M, \<lambda>p. fst(p) `` snd(p))"
  using lam_replacement_iff_lam_closed[THEN iffD2,of "\<lambda>p. fst(p)``snd(p)"]
    LambdaPair_in_M[where \<phi>="image_fm(0,1,2)" and is_f="image(##M)" and env="[]",OF
      image_type _ image_iff_sats[symmetric] image_abs]
     arity_image_fm[of 0 1 2] nat_simp_union transitivity image_closed fst_snd_closed
  by simp

synthesize "setdiff" from_definition "setdiff" assuming "nonempty"
arity_theorem for "setdiff_fm"

lemma (in M_ZF_trans) lam_replacement_Diff:
  "lam_replacement(##M, \<lambda>p. fst(p) - snd(p))"
  using lam_replacement_iff_lam_closed[THEN iffD2,of "\<lambda>p. fst(p) - snd(p)"]
    LambdaPair_in_M[where \<phi>="setdiff_fm(0,1,2)" and is_f="setdiff(##M)" and env="[]",
      OF setdiff_fm_type _ setdiff_iff_sats[symmetric] setdiff_abs]
     arity_setdiff_fm[of 0 1 2] nat_simp_union transitivity Diff_closed fst_snd_closed
     nonempty
  by simp

relationalize  "first_rel" "is_first" external
synthesize "first_fm" from_definition "is_first" assuming "nonempty"

relationalize  "minimum_rel" "is_minimum" external
manual_schematic "minimum_fm" for "is_minimum"assuming "nonempty"
  unfolding is_minimum_def using is_The_def oops

(*FIXME: we have to synthesize The!
manual_schematic "minimum_fm" for "is_minimum"assuming "nonempty"
  unfolding is_minimum_def using is_The_def
  sorry
*)

lemma (in M_ZF_trans) lam_replacement_Upair:
  "lam_replacement(##M, \<lambda>p. Upair(fst(p), snd(p)))"
  apply(rule_tac lam_replacement_iff_lam_closed[THEN iffD2,of "\<lambda>p. Upair(fst(p),snd(p))"])
  apply (auto) apply(rule Upair_closed[simplified],auto simp add:fst_snd_closed[simplified])
  apply (rule_tac
    LambdaPair_in_M[where \<phi>="upair_fm(0,1,2)" and is_f="upair(##M)" and env="[]",OF
      upair_type _ upair_iff_sats[symmetric]])
  apply (auto  simp: arity_upair_fm[of 0 1 2] nat_simp_union transitivity fst_snd_closed)
  using Upair_closed[simplified]
  by simp

lemma (in M_ZF_trans) lam_replacement_cartprod:
  "lam_replacement(##M, \<lambda>p. fst(p) \<times> snd(p))"
  apply(rule_tac lam_replacement_iff_lam_closed[THEN iffD2,of "\<lambda>p. fst(p)\<times>snd(p)"])
  apply (auto) apply(rule cartprod_closed[simplified],auto simp add:fst_snd_closed[simplified])
  apply (rule_tac
    LambdaPair_in_M[where \<phi>="cartprod_fm(0,1,2)" and is_f="cartprod(##M)" and env="[]",OF
      cartprod_type _ cartprod_iff_sats[symmetric]])
  apply (auto  simp: arity_cartprod_fm[of 0 1 2] nat_simp_union transitivity fst_snd_closed)
  using cartprod_closed[simplified]
  by simp

synthesize "pre_image" from_definition assuming "nonempty"
arity_theorem for "pre_image_fm"

lemma (in M_ZF_trans) lam_replacement_vimage:
  "lam_replacement(##M, \<lambda>p. fst(p) -`` snd(p))"
  apply(rule_tac lam_replacement_iff_lam_closed[THEN iffD2,of "\<lambda>p. fst(p)-``snd(p)"])
  apply (auto) apply(rule vimage_closed[simplified],auto simp add:fst_snd_closed[simplified])
  apply (rule_tac
    LambdaPair_in_M[where \<phi>="pre_image_fm(0,1,2)" and is_f="pre_image(##M)" and env="[]",OF
      pre_image_fm_type _ pre_image_iff_sats[symmetric]])
  apply (auto  simp: arity_pre_image_fm[of 0 1 2] nat_simp_union transitivity zero_in_M)
  using vimage_closed[simplified]
  by simp


definition is_omega_funspace :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o" where
  "is_omega_funspace(N,B,n,z) \<equiv>  \<exists>o[N]. omega(N,o) \<and> n\<in>o \<and>is_funspace(N, n, B, z)"

synthesize "omega_funspace" from_definition "is_omega_funspace" assuming "nonempty"
arity_theorem for "omega_funspace_fm"

lemma (in M_ZF_trans) omega_funspace_abs:
  "B\<in>M \<Longrightarrow> n\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> is_omega_funspace(##M,B,n,z) \<longleftrightarrow> n\<in>\<omega> \<and> is_funspace(##M,n,B,z)"
  unfolding is_omega_funspace_def using nat_in_M by simp

lemma (in M_ZF_trans) replacement_is_omega_funspace:
 "B\<in>M \<Longrightarrow> strong_replacement(##M, is_omega_funspace(##M,B))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f,B] \<Turnstile> omega_funspace_fm(2,0,1)",THEN iffD1])
   apply(rule_tac omega_funspace_iff_sats[where env="[_,_,B]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax[where env="[B]",simplified])
    apply(simp_all add:arity_omega_funspace_fm nat_simp_union)
  done

lemma (in M_ZF_trans) replacement_omega_funspace:
 "b\<in>M\<Longrightarrow>strong_replacement(##M, \<lambda>n z. n\<in>\<omega> \<and> is_funspace(##M,n,b,z))"
  using strong_replacement_cong[THEN iffD2,OF iff_sym[OF omega_funspace_abs[of  b]]]
   replacement_is_omega_funspace setclass_iff[THEN iffD1]
  by (simp del:setclass_iff)

definition HAleph_wfrec_repl_body where 
"HAleph_wfrec_repl_body(N,mesa,x,z) \<equiv> \<exists>y[N].
                   pair(N, x, y, z) \<and>
                   (\<exists>f[N].
                       (\<forall>z[N].
                           z \<in> f \<longleftrightarrow>
                           (\<exists>xa[N].
                               \<exists>y[N].
                                  \<exists>xaa[N].
                                     \<exists>sx[N].
                                        \<exists>r_sx[N].
                                           \<exists>f_r_sx[N].
                                              pair(N, xa, y, z) \<and>
                                              pair(N, xa, x, xaa) \<and>
                                              upair(N, xa, xa, sx) \<and>
                                              pre_image(N, mesa, sx, r_sx) \<and> restriction(N, f, r_sx, f_r_sx) \<and> xaa \<in> mesa \<and> is_HAleph(N, xa, f_r_sx, y))) \<and>
                       is_HAleph(N, x, f, y))"

(* MOVE THIS to an appropriate place *)
arity_theorem for "ordinal_fm"
arity_theorem for "is_Limit_fm"
arity_theorem for "empty_fm"
arity_theorem for "fun_apply_fm"

synthesize "HAleph_wfrec_repl_body" from_definition assuming "nonempty"
arity_theorem for "HAleph_wfrec_repl_body_fm"

\<comment> \<open>FIXME: Why @{thm arity_Replace_fm} doesn't work here? Revise the method we're using.\<close>
lemma arity_HAleph_wfrec_repl_body: "arity(HAleph_wfrec_repl_body_fm(2,0,1)) = 3"
  by (simp_all add: arity_HAleph_wfrec_repl_body_fm arity_is_If_fm nat_simp_union arity_fun_apply_fm
      arity_is_Limit_fm arity_empty_fm arity_Replace_fm[where i=11])

lemma (in M_ZF_trans) replacement_HAleph_wfrec_repl_body:
 "B\<in>M \<Longrightarrow> strong_replacement(##M, HAleph_wfrec_repl_body(##M,B))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f,B] \<Turnstile> HAleph_wfrec_repl_body_fm(2,0,1)",THEN iffD1])
   apply(rule_tac HAleph_wfrec_repl_body_iff_sats[where env="[_,_,B]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax[where env="[B]",simplified])
    apply(simp_all add: arity_HAleph_wfrec_repl_body)
  done

lemma (in M_ZF_trans) HAleph_wfrec_repl:
       "(##M)(sa) \<Longrightarrow>
        (##M)(esa) \<Longrightarrow>
        (##M)(mesa) \<Longrightarrow>
        strong_replacement
         (##M,
          \<lambda>x z. \<exists>y[##M].
                   pair(##M, x, y, z) \<and>
                   (\<exists>f[##M].
                       (\<forall>z[##M].
                           z \<in> f \<longleftrightarrow>
                           (\<exists>xa[##M].
                               \<exists>y[##M].
                                  \<exists>xaa[##M].
                                     \<exists>sx[##M].
                                        \<exists>r_sx[##M].
                                           \<exists>f_r_sx[##M].
                                              pair(##M, xa, y, z) \<and>
                                              pair(##M, xa, x, xaa) \<and>
                                              upair(##M, xa, xa, sx) \<and>
                                              pre_image(##M, mesa, sx, r_sx) \<and> restriction(##M, f, r_sx, f_r_sx) \<and> xaa \<in> mesa \<and> is_HAleph(##M, xa, f_r_sx, y))) \<and>
                       is_HAleph(##M, x, f, y)))"
  using replacement_HAleph_wfrec_repl_body unfolding HAleph_wfrec_repl_body_def by simp

definition fst2_snd2
  where "fst2_snd2(x) \<equiv> \<langle>fst(fst(x)), snd(snd(x))\<rangle>"

relativize functional "fst2_snd2" "fst2_snd2_rel"
relationalize "fst2_snd2_rel" "is_fst2_snd2"

lemma (in M_trivial) fst2_snd2_abs:
  assumes "M(x)" "M(res)"
shows "is_fst2_snd2(M, x, res) \<longleftrightarrow> res = fst2_snd2(x)"
  unfolding is_fst2_snd2_def fst2_snd2_def
  using fst_rel_abs[symmetric] snd_rel_abs[symmetric] fst_abs snd_abs assms
  by simp

synthesize "is_fst2_snd2" from_definition assuming "nonempty"
arity_theorem for "is_fst2_snd2_fm"

lemma (in M_ZF_trans) replacement_is_fst2_snd2:
 "strong_replacement(##M, is_fst2_snd2(##M))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f] \<Turnstile> is_fst2_snd2_fm(0,1)",THEN iffD1])
   apply(rule_tac is_fst2_snd2_iff_sats[where env="[_,_]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax[where env="[]",simplified])
    apply(simp_all add: arity_is_fst2_snd2_fm nat_simp_union)
  done

lemma (in M_ZF_trans) replacement_fst2_snd2: "strong_replacement(##M, \<lambda>x y. y = \<langle>fst(fst(x)), snd(snd(x))\<rangle>)"
  using strong_replacement_cong[THEN iffD1,OF fst2_snd2_abs replacement_is_fst2_snd2,simplified]
  unfolding fst2_snd2_def
  by simp


definition fst2_sndfst_snd2
  where "fst2_sndfst_snd2(x) \<equiv> \<langle>fst(fst(x)), snd(fst(x)), snd(snd(x))\<rangle>"

relativize functional "fst2_sndfst_snd2" "fst2_sndfst_snd2_rel"
relationalize "fst2_sndfst_snd2_rel" "is_fst2_sndfst_snd2"

lemma (in M_trivial) fst2_sndfst_snd2_abs:
  assumes "M(x)" "M(res)"
shows "is_fst2_sndfst_snd2(M, x, res) \<longleftrightarrow> res = fst2_sndfst_snd2(x)"
  unfolding is_fst2_sndfst_snd2_def fst2_sndfst_snd2_def
  using fst_rel_abs[symmetric] snd_rel_abs[symmetric] fst_abs snd_abs assms
  by simp

synthesize "is_fst2_sndfst_snd2" from_definition assuming "nonempty"
arity_theorem for "is_fst2_sndfst_snd2_fm"

lemma (in M_ZF_trans) replacement_is_fst2_sndfst_snd2:
 "strong_replacement(##M, is_fst2_sndfst_snd2(##M))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f] \<Turnstile> is_fst2_sndfst_snd2_fm(0,1)",THEN iffD1])
   apply(rule_tac is_fst2_sndfst_snd2_iff_sats[where env="[_,_]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax[where env="[]",simplified])
    apply(simp_all add: arity_is_fst2_sndfst_snd2_fm nat_simp_union)
  done

lemma (in M_ZF_trans) replacement_fst2_sndfst_snd2:
  "strong_replacement(##M, \<lambda>x y. y = \<langle>fst(fst(x)), snd(fst(x)), snd(snd(x))\<rangle>)"
  using strong_replacement_cong[THEN iffD1,OF fst2_sndfst_snd2_abs replacement_is_fst2_sndfst_snd2,simplified]
  unfolding fst2_sndfst_snd2_def
  by simp

(* FIXME: perhaps we should define this by recursion. *)
lemma banach_replacement: "strong_replacement(##M, \<lambda>x y. y = banach_functor(X, Y, f, g)^x (0))"
  unfolding banach_functor_def
  sorry

(* FIXME: perhaps we should interpret the locales in stages. *)
sublocale M_ZF_trans \<subseteq> M_inj "##M"
  apply unfold_locales sorry

lemma (in M_ZF_trans) lam_replacement_inj_rel:
  "lam_replacement(##M, \<lambda>p. inj\<^bsup>##M\<^esup>(fst(p),snd(p)))"
  using lam_replacement_iff_lam_closed[THEN iffD2,of "\<lambda>p. inj\<^bsup>M\<^esup>(fst(p),snd(p))"]
    LambdaPair_in_M[where \<phi>="is_inj_fm(0,1,2)" and is_f="is_inj(##M)" and env="[]",OF
      is_inj_fm_type _ is_inj_iff_sats[symmetric] inj_rel_iff,simplified]
     arity_is_inj_fm[of 0 1 2] nat_simp_union transitivity fst_snd_closed
     inj_rel_closed zero_in_M
  by simp

end