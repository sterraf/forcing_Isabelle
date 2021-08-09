theory Interface_ReplacementInstances
  imports
    Discipline_Function
    Forcing_Data
    FiniteFun_Relative
    Cardinal_Relative
begin

subsection\<open>More Instances of Replacement\<close>

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

end