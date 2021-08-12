theory Interface_ReplacementInstances
  imports
    Discipline_Function
    Forcing_Data
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

(*FIXME: we have to synthesize The!
manual_schematic "minimum_fm" for "is_minimum"assuming "nonempty"
  unfolding is_minimum_def using is_The_def
  sorry
*)

lemma (in M_ZF_trans) lam_replacement_cons:
  "lam_replacement(##M, \<lambda>p. cons(fst(p), snd(p)))"
  apply(rule_tac lam_replacement_iff_lam_closed[THEN iffD2,of "\<lambda>p. cons(fst(p),snd(p))"])
  apply (auto) apply(rule cons_closed[simplified],auto simp add:fst_snd_closed[simplified])
  apply (rule_tac
    LambdaPair_in_M[where \<phi>="cons_fm(0,1,2)" and is_f="is_cons(##M)" and env="[]",OF
      cons_type _ cons_iff_sats[symmetric] cons_abs,simplified])
  apply (auto  simp:     arity_cons_fm[of 0 1 2] nat_simp_union transitivity fst_snd_closed)
  using cons_closed[simplified]
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

end