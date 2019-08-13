theory Replacement_Axiom
  imports
    Relative_Univ Separation_Axiom

begin

locale rep_rename = sep_rename +
  fixes renrep :: "i" and renf :: "i"
  assumes
  sats_renrep: "arity(\<phi>) \<le> 7 #+ length(env) \<Longrightarrow> [P,leq,one,p,\<rho>,\<tau>,\<pi>] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> 
       sats(M, \<phi>, [P,leq,one,p,\<rho>,\<tau>,\<pi>] @ env) \<longleftrightarrow> sats(M, renrep`\<phi>, [V,\<tau>,\<alpha>,P,leq,one,p,\<rho>,\<pi>] @ env)"
  and
  renrep_type [TC]: "\<phi>\<in>formula \<Longrightarrow> renrep`\<phi> \<in> formula"
  and
  arity_renrep: "\<phi>\<in>formula \<Longrightarrow> arity(renrep`\<phi>) = arity(\<phi>)"
  and
  sats_renf: "arity(\<phi>) \<le> 7 #+ length(env) \<Longrightarrow> [P,leq,one,p,\<rho>,\<tau>,\<pi>] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> 
       sats(M, \<phi>, [P,leq,one,p,\<rho>,\<tau>,\<pi>] @ env) \<longleftrightarrow> sats(M, renrep`\<phi>, [V,\<tau>,\<alpha>,P,leq,one,p,\<rho>,\<pi>] @ env)"
  and
  renf_type [TC]: "\<phi>\<in>formula \<Longrightarrow> renf`\<phi> \<in> formula"
  and
  arity_renf: "\<phi>\<in>formula \<Longrightarrow> arity(renf`\<phi>) = arity(\<phi>)"
begin

lemma pow_inter_M:
  assumes
    "x\<in>M" "y\<in>M"
  shows
    "powerset(##M,x,y) \<longleftrightarrow> y = Pow(x) \<inter> M"
  using assms by auto

schematic_goal sats_body_fm_auto:
  assumes
    "[P,leq,one,p,\<rho>,\<pi>] @ nenv \<in>list(M)" "\<phi>\<in>formula" "\<alpha>\<in>M" "arity(\<phi>) \<le> 3 #+ length(nenv)"
  shows 
    "(\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(##M,\<alpha>,V) \<and> \<tau>\<in>V \<and> sats(M,forces(\<phi>),[P,leq,one,p,\<rho>,\<tau>,\<pi>] @ nenv))
   \<longleftrightarrow> sats(M,?body_fm,[\<alpha>,P,leq,one,p,\<rho>,\<pi>] @ nenv)"
    and
    "?body_fm \<in> formula"
  apply (insert assms; (rule sep_rules is_Vset_iff_sats | simp))
  apply (rule sep_rules is_Vset_iff_sats  | simp)+
         apply (simp_all, blast)
     apply (rule length_type[THEN nat_into_Ord], blast)+
  apply ((rule sep_rules | simp))
  apply ((rule sep_rules | simp))
  apply ((rule sep_rules | simp))
  apply ((rule sep_rules | simp))
  apply ((rule sep_rules | simp))
  apply ((rule sep_rules | simp))
     apply ((rule sep_rules | simp))
    apply (rule sats_renrep[simplified])
      apply (insert assms; simp add: arity_forces renrep_type definability)+
  done

(* The formula synthesized above *)
definition
  body_fm :: "i\<Rightarrow>i" where
  "body_fm(\<phi>) \<equiv> Exists (Exists (And(Exists (And(empty_fm(0), is_transrec_fm (
        Exists (And(union_fm(9, 0, 1), Exists (And(big_union_fm(0, 1), 
          And(Equal(0, 0), is_Replace_fm (4, Exists (And(fun_apply_fm(6, 1, 0), 
            Forall (Iff(Member(0, 3), 
              Forall(Implies(Member(0, 1), Member(0, 2))))))), 0)))))),3, 1))),
      And(Member(1, 0), renrep ` forces(\<phi>)))))"

(* Move this to M_trivial *)
lemma comp_in_M: "p\<in>M \<Longrightarrow> fst(p) \<in> M \<and> snd(p)\<in> M"
  proof (cases "\<exists>a. \<exists>b. p = \<langle>a, b\<rangle>")
    case False
    then 
    show "fst(p) \<in> M \<and> snd(p) \<in> M" unfolding fst_def snd_def using zero_in_M by auto
  next
    case True
    then
    obtain a b where "p = \<langle>a, b\<rangle>" by blast
    with True
    have "fst(p) = a" "snd(p) = b" unfolding fst_def snd_def by simp_all
    moreover 
    assume "p\<in>M"
    moreover from this
    have "a\<in>M" 
      unfolding \<open>p = _\<close> Pair_def by (force intro:Transset_M[OF trans_M])
    moreover from  \<open>p\<in>M\<close>
    have "b\<in>M" 
      using Transset_M[OF trans_M, of "{a,b}" p] Transset_M[OF trans_M, of "b" "{a,b}"] 
      unfolding \<open>p = _\<close> Pair_def by (simp)
    ultimately
    show ?thesis by simp
  qed

lemma Replace_sats_in_MG:
  assumes
    "c\<in>M[G]" "env \<in> list(M[G])"
    "\<phi> \<in> formula" "arity(\<phi>) \<le> 2 #+ length(env)"
    "univalent(##M[G], c, \<lambda>x v. sats(M[G], \<phi>, [x, v] @ env))"
  shows
    "{v. x\<in>c, v\<in>M[G] \<and> sats(M[G], \<phi>, [x,v] @ env)} \<in> M[G]"
proof -
  from \<open>c\<in>M[G]\<close>
  obtain \<pi> where "val(G, \<pi>) = c" "\<pi> \<in> M"
    using GenExt_def by auto
  from \<open>env \<in> _\<close>
  obtain nenv where "nenv\<in>list(M)" "env = map(val(G),nenv)"
    using map_val by auto
  then
  have "length(nenv) = length(env)" by simp
  define f where "f(\<rho>p) \<equiv> \<mu> \<alpha>. \<alpha>\<in>M \<and> (\<exists>\<tau>\<in>M. \<tau> \<in> Vset(\<alpha>) \<and> 
        sats(M,forces(\<phi>),[P,leq,one,snd(\<rho>p),fst(\<rho>p),\<tau>,\<pi>] @ nenv))" (is "_ \<equiv> \<mu> \<alpha>. ?P(\<rho>p,\<alpha>)") for \<rho>p
  have "f(\<rho>p) = (\<mu> \<alpha>. \<alpha>\<in>M \<and> (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(##M,\<alpha>,V) \<and> \<tau>\<in>V \<and> 
        sats(M,forces(\<phi>),[P,leq,one,snd(\<rho>p),fst(\<rho>p),\<tau>,\<pi>] @ nenv)))" (is "_ = (\<mu> \<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>))") for \<rho>p
    unfolding f_def using Vset_abs Vset_closed Least_cong
    by (simp)
  moreover
  have "f(\<rho>p) \<in> M" for \<rho>p
    unfolding f_def using Least_closed[of "?P(\<rho>p)"] by simp
  ultimately
  have 1:"least(##M,\<lambda>\<alpha>. ?Q(\<rho>p,\<alpha>),f(\<rho>p))" for \<rho>p
    using least_abs[of "\<lambda>\<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>)" "f(\<rho>p)"] least_conj 
    by (simp del:setclass_iff add:setclass_iff[symmetric])
  define QQ where "QQ\<equiv>?Q"
  from 1
  have "least(##M,\<lambda>\<alpha>. QQ(\<rho>p,\<alpha>),f(\<rho>p))" for \<rho>p
    unfolding QQ_def .
  from \<open>arity(\<phi>) \<le> _\<close> \<open>length(nenv) = _\<close>
  have "arity(\<phi>) \<le> 3 #+ length(nenv)"
    using leI by simp
  with assms \<open>nenv\<in>list(M)\<close> \<open>\<pi>\<in>M\<close>
  (* Have to change the renaming for the following *)
  have body:"\<lbrakk>\<rho>p\<in>M; m\<in>M; \<alpha>\<in>M\<rbrakk> \<Longrightarrow> sats(M,body_fm(\<phi>),[\<alpha>,\<rho>p,m,P,leq,one,\<pi>] @ nenv) \<longleftrightarrow> ?Q(\<rho>p,\<alpha>)" for \<alpha> \<rho>p m
    using P_in_M leq_in_M one_in_M  sats_body_fm_auto[of _ _  \<pi> nenv \<phi>] 
    unfolding body_fm_def sorry
   (* by (simp, simp del:setclass_iff add:setclass_iff[symmetric])  *)
  let ?f_fm="least_fm(body_fm(\<phi>),1)"
  {
    fix \<rho>p m
    assume asm: "\<rho>p\<in>M" "m\<in>M"
    note inM = this P_in_M leq_in_M one_in_M \<open>nenv\<in>list(M)\<close> \<open>\<pi>\<in>M\<close>
    with body
    have body':"\<And>\<alpha>. \<alpha> \<in> M \<Longrightarrow> (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(\<lambda>a. (##M)(a), \<alpha>, V) \<and> \<tau> \<in> V \<and> sats(M, forces(\<phi>), [P,leq,one,snd(\<rho>p),fst(\<rho>p),\<tau>,\<pi>] @ nenv)) \<longleftrightarrow>
          sats(M, body_fm(\<phi>), Cons(\<alpha>, [\<rho>p, m, P, leq, one, \<pi>] @ nenv))" by simp
    from inM
    have "sats(M, ?f_fm,[\<rho>p,m,P,leq,one,\<pi>] @ nenv) \<longleftrightarrow> least(##M, QQ(\<rho>p), m)"
      using sats_least_fm[OF body', of 1] (*comp_in_M *) unfolding QQ_def 
      by (simp, simp del:setclass_iff add:setclass_iff[symmetric])
  }
  then
  have "sats(M, ?f_fm,[\<rho>p,m,P,leq,one,\<pi>] @ nenv) \<longleftrightarrow> least(##M, QQ(\<rho>p), m)" 
    if "\<rho>p\<in>M" "m\<in>M" for \<rho>p m using that by simp
  then
  have "univalent(##M, \<pi>, \<lambda>\<rho>p m. sats(M, ?f_fm, [\<rho>p,m] @ ([P,leq,one,\<pi>] @ nenv)))"
    unfolding univalent_def by (auto intro:unique_least)
  moreover from \<open>length(_) = _\<close> \<open>env \<in> _\<close>
  have "length([P,leq,one,\<pi>] @ nenv) = 4 #+ length(env)" by simp
  moreover from \<open>arity(_) \<le> 3 #+ length(nenv)\<close>
  have "arity(?f_fm) \<le> 6 #+ length(env)" (* or 8? *)
    unfolding body_fm_def using arity_forces arity_renrep sorry
  moreover
  have "?f_fm\<in>formula" sorry
  moreover
  note inM = P_in_M leq_in_M one_in_M \<open>nenv\<in>list(M)\<close> \<open>\<pi>\<in>M\<close>
  ultimately
  obtain Y where "Y\<in>M" "\<forall>m\<in>M. m \<in> Y \<longleftrightarrow> (\<exists>\<rho>p\<in>M. \<rho>p \<in> \<pi> \<and> 
          sats(M, ?f_fm, [\<rho>p,m] @ ([P,leq,one,\<pi>] @ nenv)))"
    using replacement_ax[of ?f_fm "[P,leq,one,\<pi>] @ nenv"]
    unfolding strong_replacement_def by auto
  with \<open>_ \<Longrightarrow> _ \<Longrightarrow> sats(M,?f_fm,_) \<longleftrightarrow> least(_,_,_)\<close> \<open>least(_,QQ(_),f(_))\<close> \<open>f(_) \<in> M\<close> \<open>\<pi>\<in>M\<close>
  have "\<rho>p\<in>\<pi> \<Longrightarrow> f(\<rho>p)\<in>Y" for \<rho>p
    using Transset_intf[OF trans_M] by auto
  moreover
  have "{y\<in>Y. Ord(y)} \<in> M"
    sorry
  then
  have "\<Union> {y\<in>Y. Ord(y)} \<in> M" (is "?sup \<in> M")
    using Union_closed by simp
  then
  have "{x\<in>Vset(?sup). x \<in> M} \<in> M"
    using Vset_closed by simp
  moreover
  have "{one} \<in> M" 
    using one_in_M singletonM by simp
  ultimately
  have "{x\<in>Vset(?sup). x \<in> M} \<times> {one} \<in> M" 
    using cartprod_closed by simp
  then
  have "val(G,{x\<in>Vset(?sup). x \<in> M} \<times> {one}) \<in> M[G]"
    (is "val(G,?big_name) \<in> M[G]")
    by (blast intro:GenExtI)
  {
    fix v x
    assume "x\<in>c" "v\<in>M[G]" "sats(M[G], \<phi>, [x,v] @ env)"
    (* We have to use univalence for the next one *)
    have "v \<in> val(G,{x\<in>Vset(?sup). x \<in> M} \<times> {one})" sorry
  }
  then
  have "{v. x\<in>c, v\<in>M[G] \<and> sats(M[G], \<phi>, [x,v] @ env)} \<subseteq> val(G,{x\<in>Vset(?sup). x \<in> M} \<times> {one})"
    (is "?repl \<subseteq> ?big") by blast
  with \<open>?big_name\<in>M\<close> 
  have "?repl = {v\<in>?big. \<exists>x\<in>c. sats(M[G], \<phi>, [x,v] @ env)}"
    apply (intro equality_iffI, subst Replace_iff)
    apply (auto intro:Transset_intf[OF Transset_MG _ GenExtI, of _ G ?big_name])
    using assms(5) unfolding univalent_def
    apply (rule_tac x=xa in bexI; simp)
    apply (frule Transset_intf[OF Transset_MG _ \<open>c\<in>M[G]\<close>])
    apply (drule bspec, assumption, drule mp, assumption, clarify)
    apply (drule_tac x=y in bspec, assumption)
    by (drule_tac y=x in Transset_intf[OF Transset_MG _ GenExtI], auto)
  moreover
  obtain \<psi> where "v\<in>M[G] \<Longrightarrow> (\<exists>x\<in>c. sats(M[G], \<phi>, [x,v] @ env)) \<longleftrightarrow> sats(M[G], \<psi>, [v,c] @ env)"
    "arity(\<psi>) \<le> 2 #+ length(env)" "\<psi>\<in>formula"
    for v sorry
  moreover from this
  have "{v\<in>?big. \<exists>x\<in>c. sats(M[G], \<phi>, [x,v] @ env)} = {v\<in>?big. sats(M[G], \<psi>, [v,c] @ env)}"
    using Transset_intf[OF Transset_MG _ GenExtI]
    apply (intro equality_iffI, simp, auto) sorry
  moreover from calculation and \<open>env\<in>_\<close> \<open>c\<in>_\<close> \<open>?big\<in>M[G]\<close>
  have "{v\<in>?big. sats(M[G], \<psi>, [v,c] @ env)} \<in> M[G]"
    using Collect_sats_in_MG by auto
  ultimately
  show ?thesis by simp 
qed

theorem strong_replacement_in_MG:
  assumes 
    "\<phi>\<in>formula" and "arity(\<phi>) \<le> 2 #+ length(env)" "env \<in> list(M[G])"
  shows  
    "strong_replacement(##M[G],\<lambda>x v. sats(M[G],\<phi>,[x,v] @ env))"
proof -
  from assms
  have "{v . x \<in> c, v \<in> M[G] \<and> sats(M[G], \<phi>, [x,v] @ env)} \<in> M[G]"
    if "c \<in> M[G]" "univalent(##M[G], c, \<lambda>x v. sats(M[G], \<phi>, [x, v] @ env))" for c
    using that Replace_sats_in_MG by auto
  then
  show ?thesis
    unfolding strong_replacement_def univalent_def using Transset_intf[OF Transset_MG]
    apply (intro ballI rallI impI)
    apply (rule_tac x="{v . x \<in> A, v\<in>M[G] \<and> sats(M[G], \<phi>, [x, v] @ env)}" in rexI)
     apply (auto)
     apply (drule_tac x=x in bspec; simp_all)
     by (blast)
    (* 34secs *)
qed

end (* context sep_rename *)

end