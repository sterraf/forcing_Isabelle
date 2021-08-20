theory Interface_ReplacementInstances
  imports
    Discipline_Function
    Forcing_Data
    Aleph_Relative
    FiniteFun_Relative
    Cardinal_Relative
    Interface_SepInstances
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
  using strong_replacement_cong[THEN iffD2,OF _ replacement_is_range] range_abs
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
  using strong_replacement_cong[THEN iffD2,OF _ replacement_is_domain] 
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

lemma (in M_ZF_trans) minimum_closed:
  assumes "B\<in>M"
  shows "minimum(r,B) \<in> M"
proof(cases "\<exists>!b. first(b,B,r)")
  case True
  then
  obtain b where "b = minimum(r,B)" "first(b,B,r)"
    using the_equality2
    unfolding minimum_def
    by auto
  then
  show ?thesis
    using first_is_elem transitivity[of b B] assms
    by simp
next
  case False
  then show ?thesis 
    using zero_in_M the_0
    unfolding minimum_def 
    by auto
qed

relationalize  "minimum_rel" "is_minimum" external
definition is_minimum' where
  "is_minimum'(M,R,X,u) \<equiv> (M(u) \<and> u \<in> X \<and> (\<forall>v[M]. \<exists>a[M]. (v \<in> X \<longrightarrow> v \<noteq> u \<longrightarrow> a \<in> R) \<and> pair(M, u, v, a))) \<and>
    (\<exists>x[M].
        (M(x) \<and> x \<in> X \<and> (\<forall>v[M]. \<exists>a[M]. (v \<in> X \<longrightarrow> v \<noteq> x \<longrightarrow> a \<in> R) \<and> pair(M, x, v, a))) \<and>
        (\<forall>y[M]. M(y) \<and> y \<in> X \<and> (\<forall>v[M]. \<exists>a[M]. (v \<in> X \<longrightarrow> v \<noteq> y \<longrightarrow> a \<in> R) \<and> pair(M, y, v, a)) \<longrightarrow> y = x)) \<or>
    \<not> (\<exists>x[M]. (M(x) \<and> x \<in> X \<and> (\<forall>v[M]. \<exists>a[M]. (v \<in> X \<longrightarrow> v \<noteq> x \<longrightarrow> a \<in> R) \<and> pair(M, x, v, a))) \<and>
               (\<forall>y[M]. M(y) \<and> y \<in> X \<and> (\<forall>v[M]. \<exists>a[M]. (v \<in> X \<longrightarrow> v \<noteq> y \<longrightarrow> a \<in> R) \<and> pair(M, y, v, a)) \<longrightarrow> y = x)) \<and>
    empty(M, u)"

synthesize "minimum" from_definition "is_minimum'" assuming "nonempty"
arity_theorem for "minimum_fm"

lemma is_minimum_eq :
  "M(R) \<Longrightarrow> M(X) \<Longrightarrow> M(u) \<Longrightarrow> is_minimum(M,R,X,u) \<longleftrightarrow> is_minimum'(M,R,X,u)"
  unfolding is_minimum_def is_minimum'_def is_The_def is_first_def by simp

context M_trivial
begin

lemma first_closed: 
  "M(B) \<Longrightarrow> M(r) \<Longrightarrow> first(u,r,B) \<Longrightarrow> M(u)"
  using transM[OF first_is_elem] by simp  

is_iff_rel for "first"
  unfolding is_first_def first_rel_def by auto

is_iff_rel for "minimum"
  unfolding is_minimum_def minimum_rel_def 
  using is_first_iff The_abs nonempty
  by force

end

lemma (in M_ZF_trans) lam_replacement_minimum:
  "lam_replacement(##M, \<lambda>p. minimum(fst(p), snd(p)))"
  apply(rule_tac lam_replacement_iff_lam_closed[THEN iffD2,of "\<lambda>p. minimum(fst(p),snd(p))"])
  apply (auto) apply(rule minimum_closed[simplified],auto simp add:fst_snd_closed[simplified])
  apply (rule_tac
    LambdaPair_in_M[where \<phi>="minimum_fm(0,1,2)" and is_f="is_minimum'(##M)" and env="[]",OF
      minimum_fm_type _ minimum_iff_sats[symmetric]])
  apply (auto  simp: arity_minimum_fm[of 0 1 2] nat_simp_union transitivity fst_snd_closed zero_in_M)
  using Upair_closed[simplified] minimum_closed is_minimum_eq is_minimum_iff minimum_abs
  by simp_all


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
  using strong_replacement_cong[THEN iffD2,OF _ replacement_is_omega_funspace[of b]]
     omega_funspace_abs[of b] setclass_iff[THEN iffD1]
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


lemmas (in M_ZF_trans) M_replacement_ZF_instances = lam_replacement_domain
  lam_replacement_fst lam_replacement_snd lam_replacement_Union
  lam_replacement_Upair lam_replacement_image
  lam_replacement_Diff lam_replacement_vimage
  separation_fst_equal separation_id_rel[simplified]
  separation_equal_apply separation_sndfst_eq_fstsnd
  separation_fstfst_eq_fstsnd separation_fstfst_eq
  separation_restrict_elem
  replacement_fst2_snd2 replacement_fst2_sndfst_snd2

sublocale M_ZF_trans \<subseteq> M_replacement "##M"
  by unfold_locales (simp_all add: M_replacement_ZF_instances del:setclass_iff)

definition RepFun_body :: "i \<Rightarrow> i \<Rightarrow> i"where
  "RepFun_body(u,v) \<equiv> {{\<langle>v, x\<rangle>} . x \<in> u}"

relativize functional "RepFun_body" "RepFun_body_rel"
relationalize "RepFun_body_rel" "is_RepFun_body"

lemma (in M_trivial) RepFun_body_abs:
  assumes "M(u)" "M(v)" "M(res)" 
shows "is_RepFun_body(M, u, v, res) \<longleftrightarrow> res = RepFun_body(u,v)"
  unfolding is_RepFun_body_def RepFun_body_def
  using fst_rel_abs[symmetric] snd_rel_abs[symmetric] fst_abs snd_abs assms
    Replace_abs[where P="\<lambda>xa a. a = {\<langle>v, xa\<rangle>}" and A="u"]
    univalent_triv transM[of _ u]
  by auto

synthesize "is_RepFun_body" from_definition assuming "nonempty"
arity_theorem for "is_RepFun_body_fm"
lemma aa:
  "arity( \<cdot>(\<cdot>\<exists>\<cdot>0 = 0\<cdot>\<cdot>) \<and> \<cdot>(\<cdot>\<exists>\<cdot>0 = 0\<cdot>\<cdot>) \<and> (\<cdot>\<exists>\<cdot>cons_fm(0, 3, 2) \<and> pair_fm(5, 1, 0) \<cdot>\<cdot>)\<cdot>\<cdot> ) = 5"
  using arity_cons_fm arity_pair_fm pred_Un_distrib nat_union_abs1
  by auto

lemma arity_RepFun: "arity(is_RepFun_body_fm(0, 1, 2)) = 3"
  unfolding is_RepFun_body_fm_def
  using arity_Replace_fm[OF _ _ _ _ aa] arity_fst_fm arity_snd_fm arity_empty_fm
    pred_Un_distrib nat_union_abs2 nat_union_abs1
  by simp

lemma (in M_ZF_trans) RepFun_SigFun_closed: "x \<in> M \<Longrightarrow> z \<in> M \<Longrightarrow> {{\<langle>z, x\<rangle>} . x \<in> x} \<in> M"
  using lam_replacement_surj_imp_inj1 lam_replacement_imp_strong_replacement RepFun_closed
    transitivity singleton_in_M_iff pair_in_M_iff
  by simp

lemma (in M_ZF_trans) replacement_RepFun_body:
  "lam_replacement(##M, \<lambda>p . {{\<langle>snd(p), x\<rangle>} . x \<in> fst(p)})"
  apply(rule_tac lam_replacement_iff_lam_closed[THEN iffD2,of "\<lambda>p. {{\<langle>snd(p), x\<rangle>} . x \<in> fst(p)}"])
  using  RepFun_SigFun_closed[OF fst_snd_closed[THEN conjunct1,simplified] 
      fst_snd_closed[THEN conjunct2,simplified]] transitivity
  apply auto
  apply (rule_tac
    LambdaPair_in_M[where \<phi>="is_RepFun_body_fm(0,1,2)" and is_f="is_RepFun_body(##M)" and env="[]",OF
      is_RepFun_body_fm_type _ is_RepFun_body_iff_sats[symmetric]])
  apply (auto  simp: arity_RepFun nat_simp_union transitivity zero_in_M RepFun_body_def RepFun_body_abs RepFun_SigFun_closed)
  done

sublocale M_ZF_trans \<subseteq> M_replacement_extra "##M"
  by unfold_locales (simp_all add: replacement_RepFun_body 
      lam_replacement_minimum del:setclass_iff)

sublocale M_ZF_trans \<subseteq> M_Perm "##M"
  using separation_PiP_rel separation_injP_rel separation_surjP_rel
    lam_replacement_imp_strong_replacement[OF 
      lam_replacement_Sigfun[OF lam_replacement_constant]]
    Pi_replacement1 unfolding Sigfun_def
  by unfold_locales simp_all

definition order_eq_map where
  "order_eq_map(M,A,r,a,z) \<equiv> \<exists>x[M]. \<exists>g[M]. \<exists>mx[M]. \<exists>par[M].
             ordinal(M,x) & pair(M,a,x,z) & membership(M,x,mx) &
             pred_set(M,A,a,r,par) & order_isomorphism(M,par,r,x,mx,g)"

synthesize "order_eq_map" from_definition assuming "nonempty"
arity_theorem for "is_ord_iso_fm"
arity_theorem for "order_eq_map_fm"


lemma (in M_ZF_trans) replacement_is_order_eq_map:
 "A\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> strong_replacement(##M, order_eq_map(##M,A,r))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f,A,r] \<Turnstile> order_eq_map_fm(2,3,0,1)",THEN iffD1])
   apply(rule_tac order_eq_map_iff_sats[where env="[_,_,A,r]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax[where env="[A,r]",simplified])
    apply(simp_all add: arity_order_eq_map_fm nat_simp_union)
  done

(* Banach *)
synthesize "is_banach_functor" from_definition assuming "nonempty"
arity_theorem for "is_banach_functor_fm"

definition banach_body_iterates where
  "banach_body_iterates(M,X,Y,f,g,W,n,x,z) \<equiv> 
\<exists>y[M].
                   pair(M, x, y, z) \<and>
                   (\<exists>fa[M].
                       (\<forall>z[M].
                           z \<in> fa \<longleftrightarrow>
                           (\<exists>xa[M].
                               \<exists>y[M].
                                  \<exists>xaa[M].
                                     \<exists>sx[M].
                                        \<exists>r_sx[M].
                                           \<exists>f_r_sx[M]. \<exists>sn[M]. \<exists>msn[M]. successor(M,n,sn) \<and>
                                              membership(M,sn,msn) \<and>
                                              pair(M, xa, y, z) \<and>
                                              pair(M, xa, x, xaa) \<and>
                                              upair(M, xa, xa, sx) \<and>
                                              pre_image(M, msn, sx, r_sx) \<and>
                                              restriction(M, fa, r_sx, f_r_sx) \<and>
                                              xaa \<in> msn \<and>
                                              (empty(M, xa) \<longrightarrow> y = W) \<and>
                                              (\<forall>m[M].
                                                  successor(M, m, xa) \<longrightarrow>
                                                  (\<exists>gm[M].
                                                      is_apply(M, f_r_sx, m, gm) \<and> is_banach_functor(M, X, Y, f, g, gm, y))) \<and>
                                              (is_quasinat(M, xa) \<or> empty(M, y)))) \<and>
                       (empty(M, x) \<longrightarrow> y = W) \<and>
                       (\<forall>m[M].
                           successor(M, m, x) \<longrightarrow>
                           (\<exists>gm[M]. is_apply(M, fa, m, gm) \<and> is_banach_functor(M, X, Y, f, g, gm, y))) \<and>
                       (is_quasinat(M, x) \<or> empty(M, y)))"

synthesize "is_quasinat" from_definition assuming "nonempty"
arity_theorem for "is_quasinat_fm"

synthesize "banach_body_iterates" from_definition assuming "nonempty"
arity_theorem for "banach_body_iterates_fm"

lemma (in M_ZF_trans) banach_iterates:
  assumes "X\<in>M" "Y\<in>M" "f\<in>M" "g\<in>M" "W\<in>M"
  shows "iterates_replacement(##M, is_banach_functor(##M,X,Y,f,g), W)"
proof -
  have "strong_replacement(##M, \<lambda> x z . banach_body_iterates(##M,X,Y,f,g,W,n,x,z))" if "n\<in>\<omega>" for n 
    apply(rule_tac strong_replacement_cong[
          where P="\<lambda> x z. M,[x,z,_,W,g,f,Y,X] \<Turnstile> banach_body_iterates_fm(7,6,5,4,3,2,0,1)",THEN iffD1])
     prefer 2
     apply(rule_tac replacement_ax[where env="[n,W,g,f,Y,X]",simplified])
    using assms that
    by(simp_all add:zero_in_M arity_banach_body_iterates_fm nat_simp_union transitivity[OF _ nat_in_M])
  then
  show ?thesis
    using assms zero_in_M transitivity[OF _ nat_in_M] Memrel_closed
    unfolding iterates_replacement_def wfrec_replacement_def is_wfrec_def M_is_recfun_def
      is_nat_case_def iterates_MH_def banach_body_iterates_def
    by simp
qed

definition banach_is_iterates_body where
  "banach_is_iterates_body(M,X,Y,f,g,W,n,y) \<equiv> \<exists>om[M]. omega(M,om) \<and> n \<in> om \<and>
             (\<exists>sn[M].
                 \<exists>msn[M].
                    successor(M, n, sn) \<and>
                    membership(M, sn, msn) \<and>
                    (\<exists>fa[M].
                        (\<forall>z[M].
                            z \<in> fa \<longleftrightarrow>
                            (\<exists>x[M].
                                \<exists>y[M].
                                   \<exists>xa[M].
                                      \<exists>sx[M].
                                         \<exists>r_sx[M].
                                            \<exists>f_r_sx[M].
                                               pair(M, x, y, z) \<and>
                                               pair(M, x, n, xa) \<and>
                                               upair(M, x, x, sx) \<and>
                                               pre_image(M, msn, sx, r_sx) \<and>
                                               restriction(M, fa, r_sx, f_r_sx) \<and>
                                               xa \<in> msn \<and>
                                               (empty(M, x) \<longrightarrow> y = W) \<and>
                                               (\<forall>m[M].
                                                   successor(M, m, x) \<longrightarrow>
                                                   (\<exists>gm[M].
                                                       fun_apply(M, f_r_sx, m, gm) \<and> is_banach_functor(M, X, Y, f, g, gm, y))) \<and>
                                               (is_quasinat(M, x) \<or> empty(M, y)))) \<and>
                        (empty(M, n) \<longrightarrow> y = W) \<and>
                        (\<forall>m[M].
                            successor(M, m, n) \<longrightarrow>
                            (\<exists>gm[M]. fun_apply(M, fa, m, gm) \<and> is_banach_functor(M, X, Y, f, g, gm, y))) \<and>
                        (is_quasinat(M, n) \<or> empty(M, y))))"

synthesize "banach_is_iterates_body" from_definition assuming "nonempty"
arity_theorem for "banach_is_iterates_body_fm"

lemma (in M_ZF_trans) banach_replacement_iterates: 
  assumes "X\<in>M" "Y\<in>M" "f\<in>M" "g\<in>M" "W\<in>M"
  shows "strong_replacement(##M, \<lambda>n y. n\<in>\<omega> \<and> is_iterates(##M,is_banach_functor(##M,X, Y, f, g),W,n,y))"
proof -
  have "strong_replacement(##M, \<lambda> n z . banach_is_iterates_body(##M,X,Y,f,g,W,n,z))"  
    apply(rule_tac strong_replacement_cong[
          where P="\<lambda> n z. M,[n,z,W,g,f,Y,X] \<Turnstile> banach_is_iterates_body_fm(6,5,4,3,2,0,1)",THEN iffD1])
     prefer 2
     apply(rule_tac replacement_ax[where env="[W,g,f,Y,X]",simplified])
    using assms 
    by(simp_all add:zero_in_M arity_banach_is_iterates_body_fm nat_simp_union transitivity[OF _ nat_in_M])
  then
  show ?thesis
    using assms nat_in_M
    unfolding is_iterates_def wfrec_replacement_def is_wfrec_def M_is_recfun_def
      is_nat_case_def iterates_MH_def banach_is_iterates_body_def
    by simp
qed

lemma (in M_ZF_trans) banach_replacement:
  assumes "(##M)(X)" "(##M)(Y)" "(##M)(f)" "(##M)(g)" 
  shows "strong_replacement(##M, \<lambda>n y. n\<in>nat \<and> y = banach_functor(X, Y, f, g)^n (0))"
  using iterates_abs[OF banach_iterates banach_functor_abs,of X Y f g] 
    assms banach_functor_closed zero_in_M
  apply (rule_tac strong_replacement_cong[THEN iffD1, OF _ banach_replacement_iterates[of X Y f g 0]])
  by(rule_tac conj_cong,simp_all)

end