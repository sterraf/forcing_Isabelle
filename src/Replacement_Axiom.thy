theory Replacement_Axiom
  imports
    Least Relative_Univ Separation_Axiom Renaming
begin

local_setup\<open>
let val rho  = @{term "[P,leq,o,p,\<rho>,\<tau>,\<pi>]"}
    val rho' = @{term "[V,\<tau>,\<rho>,p,\<alpha>,P,leq,o,\<pi>]"}
    val (fvs,r,tc_lemma,action_lemma) = sum_rename rho rho'
    val (tc_lemma,action_lemma) = (fix_vars tc_lemma fvs , fix_vars action_lemma fvs)
in
Local_Theory.note   ((@{binding "renrep_thm"}, []), [tc_lemma,action_lemma]) #> snd #>
Local_Theory.define ((@{binding "renrep1_fn"}, NoSyn),
  ((@{binding "renrep1_def"}, []), r)) #> snd
end\<close>


definition renrep_fn :: "i \<Rightarrow> i" where
  "renrep_fn(env) == sum(renrep1_fn,id(length(env)),7,9,length(env))"

definition 
  renrep :: "[i,i] \<Rightarrow> i" where
  "renrep(\<phi>,env) = ren(\<phi>)`(7#+length(env))`(9#+length(env))`renrep_fn(env)" 

lemma renrep_type [TC]: 
  assumes "\<phi>\<in>formula" "env \<in> list(M)"
    shows "renrep(\<phi>,env) \<in> formula"
  unfolding renrep_def renrep_fn_def renrep1_def
  using assms
  apply(rule_tac ren_tc,simp_all)
  apply(insert renrep_thm(1)[simplified,of P M leq o p \<rho> \<tau> \<pi> v \<alpha> env],simp)
  
lemma arity_renrep: 
  assumes "n\<in>nat" "\<phi>\<in>formula" "arity(\<phi>)\<le> 6#+n"
    shows "arity(renrep(\<phi>,n)) \<le> 8#+n"
 unfolding renrep_def
    using renrep_fn_type[OF assms(1)] ren_arity assms
    by simp

lemma renrep_sats :
  assumes
    "arity(\<phi>) \<le> 6 #+ length(env)"
    "[P,leq,o,p,\<rho>,\<tau>] @ env \<in> list(M)"
    "V \<in> M" "\<alpha> \<in> M"
    "\<phi>\<in>formula"
  shows "sats(M, \<phi>, [P,leq,o,p,\<rho>,\<tau>] @ env) \<longleftrightarrow> sats(M, renrep(\<phi>,length(env)), [V,\<tau>,\<rho>,p,\<alpha>,P,leq,o] @ env)"
proof -
  let ?env0 = "[P,leq,o,p,\<rho>,\<tau>]"
  let ?env' = "[V,\<tau>,\<rho>,p,\<alpha>,P,leq,o] @ env"
  let ?env1 = "[V,\<tau>,\<rho>,p,\<alpha>,P,leq,o]"
  from \<open>[P,leq,o,p,\<rho>,\<tau>] @ env \<in> list(M)\<close> \<open>V \<in> M\<close> \<open>\<alpha> \<in> M\<close>
  have 1:"6 #+ length(env) \<in> nat" "8 #+ length(env) \<in> nat"  "env \<in> list(M)" "?env0 \<in> list(M)" 
        "?env1 \<in> list(M)"
    by simp_all
  with assms 
  have 2:"length(env) \<in> nat" "?env' \<in> list(M)" by simp_all
  from assms
  have "[V,\<tau>,\<rho>,p,\<alpha>,P,leq,o] @ env \<in> list(M)" by simp
  show ?thesis
    unfolding renrep_def 
    using renrep_fn_action[OF \<open>?env0 \<in> list(M)\<close> \<open>env\<in>list(M)\<close> \<open>V\<in>M\<close> \<open>\<alpha>\<in>M\<close>]
    sats_iff_sats_ren[OF \<open>\<phi> \<in> formula\<close> 1(1) 1(2)  \<open>[P,leq,o,p,\<rho>,\<tau>] @ env \<in> list(M)\<close> 2(2)]
      renrep_fn_type[OF 2(1)] \<open>arity(\<phi>) \<le> 6#+length(env)\<close>      
    by simp
qed

locale rep_rename = sep_rename +
  fixes renpbdy :: "[i,i] \<Rightarrow> i" and renbody :: "[i,i] \<Rightarrow> i"
  assumes
  sats_renpbdy: "arity(\<phi>) \<le> 6 #+ length(nenv) \<Longrightarrow> [\<rho>,p,x,\<alpha>,P,leq,one,\<pi>] @ nenv \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> 
       sats(M, \<phi>, [\<rho>,p,\<alpha>,P,leq,one] @ nenv) \<longleftrightarrow> sats(M, renpbdy(\<phi>,length(env)), [\<rho>,p,x,\<alpha>,P,leq,one] @ nenv)"
  and
  renpbdy_type [TC]: "\<phi>\<in>formula \<Longrightarrow> m\<in>nat \<Longrightarrow> renpbdy(\<phi>,m) \<in> formula"
  and
  arity_renpbdy: "\<phi>\<in>formula \<Longrightarrow> m\<in>nat \<Longrightarrow> arity(renpbdy(\<phi>,m)) \<le> 8 #+ m"
  and
  sats_renbody: "arity(\<phi>) \<le> 6 #+ length(nenv) \<Longrightarrow> [\<alpha>,x,m,P,leq,one] @ nenv \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> 
       sats(M, \<phi>, [x,\<alpha>,P,leq,one] @ nenv) \<longleftrightarrow> sats(M, renbody(\<phi>,length(env)), [\<alpha>,x,m,P,leq,one] @ nenv)"
  and
  renbody_type [TC]: "\<phi>\<in>formula \<Longrightarrow> m \<in> nat \<Longrightarrow> renbody(\<phi>,m) \<in> formula"
  and
  arity_renbody: "\<phi>\<in>formula \<Longrightarrow> m \<in> nat \<Longrightarrow> arity(renbody(\<phi>,m)) = arity(\<phi>)"
begin

lemma pow_inter_M:
  assumes
    "x\<in>M" "y\<in>M"
  shows
    "powerset(##M,x,y) \<longleftrightarrow> y = Pow(x) \<inter> M"
  using assms by auto

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

schematic_goal sats_prebody_fm_auto:
  assumes
    "[P,leq,one,p,\<rho>,\<pi>] @ nenv \<in>list(M)" "\<phi>\<in>formula" "\<alpha>\<in>M" "arity(\<phi>) \<le> 2 #+ length(nenv)"
  shows 
    "(\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(##M,\<alpha>,V) \<and> \<tau>\<in>V \<and> sats(M,forces(\<phi>),[P,leq,one,p,\<rho>,\<tau>] @ nenv))
   \<longleftrightarrow> sats(M,?prebody_fm,[\<rho>,p,\<alpha>,P,leq,one] @ nenv)"
  apply (insert assms; (rule sep_rules is_Vset_iff_sats[OF _ _ _ _ _ M_inhabit[simplified]] | simp))
   apply (rule sep_rules is_Vset_iff_sats is_Vset_iff_sats[OF _ _ _ _ _ M_inhabit[simplified]] | simp)+
  apply (rule M_inhabit[simplified])
       apply (simp_all)
     apply (rule length_type[THEN nat_into_Ord], blast)+
  apply ((rule sep_rules | simp))
  apply ((rule sep_rules | simp))
  apply ((rule sep_rules | simp))
  apply ((rule sep_rules | simp))
  apply ((rule sep_rules | simp))
  apply ((rule sep_rules | simp))
     apply ((rule sep_rules | simp))
    apply (rule renrep_sats[simplified])
      apply (insert assms; force simp add:  arity_forces renrep_type definability)+
  done (* 10 secs *)

(* The formula synthesized above *)
definition
  prebody_fm :: "[i,i]\<Rightarrow>i" where
  "prebody_fm(\<phi>,n) \<equiv> Exists
          (Exists
            (And(Exists
                  (And(empty_fm(0),
                       is_transrec_fm
                        (Exists
                          (And(union_fm(9, 0, 1),
                               Exists
                                (And(big_union_fm(0, 1),
                                     And(Equal(0, 0),
                                         is_Replace_fm
                                          (4, Exists
                                               (And(fun_apply_fm(6, 1, 0),
                                                    Forall(Iff(Member(0, 3), Forall(Implies(Member(0, 1), Member(0, 2))))))),
                                           0)))))),
                         5, 1))),
                 And(Member(1, 0), renrep(forces(\<phi>), n)))))"

lemma sats_prebody_fm:
  assumes
    "[P,leq,one,p,\<rho>] @ nenv \<in>list(M)" "\<phi>\<in>formula" "\<alpha>\<in>M" "arity(\<phi>) \<le> 2 #+ length(nenv)"
  shows 
    "sats(M,prebody_fm(\<phi>,length(nenv)),[\<rho>,p,\<alpha>,P,leq,one] @ nenv) \<longleftrightarrow>
     (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(##M,\<alpha>,V) \<and> \<tau>\<in>V \<and> sats(M,forces(\<phi>),[P,leq,one,p,\<rho>,\<tau>] @ nenv))"
  unfolding prebody_fm_def using assms sats_prebody_fm_auto by force

lemma prebody_fm_type [TC]:
  "\<phi>\<in>formula \<Longrightarrow> n \<in> nat \<Longrightarrow> prebody_fm(\<phi>,n)\<in>formula"
  unfolding prebody_fm_def by simp

lemmas new_fm_defs = fm_defs is_transrec_fm_def  is_Replace_fm_def is_eclose_fm_def mem_eclose_fm_def 
   finite_ordinal_fm_def is_wfrec_fm_def  Memrel_fm_def eclose_n_fm_def is_recfun_fm_def is_iterates_fm_def
   iterates_MH_fm_def is_nat_case_fm_def quasinat_fm_def pre_image_fm_def restriction_fm_def

lemma arity_prebody_fm:
  assumes
    "\<phi>\<in>formula" "\<alpha>\<in>M" "m \<in> nat" "arity(\<phi>) \<le> 2 #+ m"
  shows
    "arity(prebody_fm(\<phi>,m))\<le>6 #+ m"
  unfolding prebody_fm_def using assms
  apply(simp add:  new_fm_defs )
  apply(simp add: nat_simp_union,rule, rule, (rule pred_le,simp+)+)
  apply(subgoal_tac "arity(forces(\<phi>)) \<le> 6 #+m ")
  apply(subgoal_tac "forces(\<phi>)\<in> formula")
  apply(drule arity_renrep[of _ "forces(\<phi>)",OF \<open>m\<in>nat\<close>],simp_all add:arity_forces)
  done
  

definition
  body_fm' :: "[i,i]\<Rightarrow>i" where
  "body_fm'(\<phi>,n) \<equiv> Exists(Exists(And(pair_fm(0,1,2),renpbdy(prebody_fm(\<phi>,n),n))))"

lemma body_fm'_type[TC]: "\<phi>\<in>formula \<Longrightarrow> m\<in>nat \<Longrightarrow> body_fm'(\<phi>,m)\<in>formula"
  unfolding body_fm'_def prebody_fm_def 
  by simp

(* This might be false! Might be 2 if that changes in sats_body_fm *)
lemma arity_body_fm':
  assumes
    "\<phi>\<in>formula" "\<alpha>\<in>M" "m\<in>nat" "arity(\<phi>) \<le> 2 #+ m"
  shows
    "arity(body_fm'(\<phi>,m))\<le> 6 #+ m"
  unfolding body_fm'_def using assms
  apply(simp add:  new_fm_defs )
  apply(simp add: nat_simp_union)
  apply( rule, (rule pred_le,simp+)+)
  apply(frule arity_prebody_fm,simp_all,simp)
  apply(subgoal_tac "prebody_fm(\<phi>,m)\<in>formula")
  apply(frule arity_renpbdy[of "prebody_fm(\<phi>,m)"],simp_all+)
  done

lemma sats_body_fm':
  assumes
    "\<exists>t p. x=<t,p>" "x\<in>M" "[\<alpha>,P,leq,one,p,\<rho>] @ nenv \<in>list(M)" "\<phi>\<in>formula" "arity(\<phi>) \<le> 2 #+ length(nenv)"
  shows 
    "sats(M,body_fm'(\<phi>,length(nenv)),[x,\<alpha>,P,leq,one] @ nenv) \<longleftrightarrow> 
     sats(M,renpbdy(prebody_fm(\<phi>,length(nenv)),length(nenv)),[fst(x),snd(x),x,\<alpha>,P,leq,one] @ nenv)"
  using assms comp_in_M[OF \<open>x\<in>M\<close>] unfolding body_fm'_def
  by (auto)

definition
  body_fm :: "[i,i]\<Rightarrow>i" where
  "body_fm(\<phi>,n) \<equiv> renbody(body_fm'(\<phi>,n),n)"

lemma body_fm_type [TC]: "m \<in> nat \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow>  body_fm(\<phi>,m)\<in>formula"
  unfolding body_fm_def by simp

lemma sats_body_fm:
  assumes
    "\<exists>t p. x=<t,p>" "[\<alpha>,x,m,P,leq,one] @ nenv \<in>list(M)"
    "\<phi>\<in>formula" "arity(\<phi>) \<le> 2 #+ length(nenv)"
  shows 
    "sats(M,body_fm(\<phi>,length(nenv)),[\<alpha>,x,m,P,leq,one] @ nenv) \<longleftrightarrow> 
     sats(M,renpbdy(prebody_fm(\<phi>,length(nenv)),length(nenv)),[fst(x),snd(x),x,\<alpha>,P,leq,one] @ nenv)"
  using assms sats_body_fm' sats_renbody[OF arity_body_fm' assms(2), symmetric]
  unfolding body_fm_def
  by auto

lemma sats_renpbdy_prebody_fm:
  assumes
    "\<exists>t p. x=<t,p>" "x\<in>M" "[\<alpha>,m,P,leq,one] @ nenv \<in>list(M)"
    "\<phi>\<in>formula" "arity(\<phi>) \<le> 2 #+ length(nenv)"
  shows 
    "sats(M,renpbdy(prebody_fm(\<phi>,length(nenv)),length(nenv)),[fst(x),snd(x),x,\<alpha>,P,leq,one] @ nenv) \<longleftrightarrow>
     sats(M,prebody_fm(\<phi>,length(nenv)),[fst(x),snd(x),\<alpha>,P,leq,one] @ nenv)"
  using assms comp_in_M[OF \<open>x\<in>M\<close>] 
    sats_renpbdy[OF arity_prebody_fm _ prebody_fm_type, of concl:\<phi>, symmetric]
  by force

lemma body_lemma:
  assumes
    "\<exists>t p. x=<t,p>" "x\<in>M" "[x,\<alpha>,m,P,leq,one] @ nenv \<in>list(M)"
    "\<phi>\<in>formula" "arity(\<phi>) \<le> 2 #+ length(nenv)"
  shows 
  "sats(M,body_fm(\<phi>,length(nenv)),[\<alpha>,x,m,P,leq,one] @ nenv) \<longleftrightarrow> 
  (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(\<lambda>a. (##M)(a),\<alpha>,V) \<and> \<tau> \<in> V \<and> sats(M,forces(\<phi>),[P,leq,one,snd(x),fst(x),\<tau>] @ nenv))"
  using assms sats_body_fm[of x \<alpha> m nenv] sats_renpbdy_prebody_fm[of x \<alpha>]
    sats_prebody_fm[of "snd(x)" "fst(x)"] comp_in_M[OF \<open>x\<in>M\<close>]
  by (simp, simp del:setclass_iff add:setclass_iff[symmetric],simp)

(* Sorrying this until the interface is ready *)
lemma (in M_eclose) Vset_abs: "\<lbrakk> M(i); M(V); Ord(i)\<rbrakk> \<Longrightarrow> is_Vset(M,i,V) \<longleftrightarrow> V = {x\<in>Vset(i). M(x)}"
  sorry

lemma (in M_eclose) Vset_closed: "\<lbrakk> M(i); Ord(i)\<rbrakk> \<Longrightarrow> M({x\<in>Vset(i). M(x)})"
  sorry

lemma (in M_eclose) rank_closed: "M(a) \<Longrightarrow> M(rank(a))"
  sorry

lemma Replace_sats_in_MG:
  assumes
    "c\<in>M[G]" "env \<in> list(M[G])"
    "\<phi> \<in> formula" "arity(\<phi>) \<le> 2 #+ length(env)"
    "univalent(##M[G], c, \<lambda>x v. sats(M[G], \<phi>, [x, v] @ env))"
  shows
    "{v. x\<in>c, v\<in>M[G] \<and> sats(M[G], \<phi>, [x,v] @ env)} \<in> M[G]"
proof -
  from \<open>c\<in>M[G]\<close>
  obtain \<pi>' where "val(G, \<pi>') = c" "\<pi>' \<in> M"
    using GenExt_def by auto
  then
  have "domain(\<pi>')\<times>P\<in>M" (is "?\<pi>\<in>M")
    using cartprod_closed P_in_M domain_closed by simp
  from \<open>val(G, \<pi>') = c\<close>
  have "c \<subseteq> val(G,?\<pi>)" 
    using def_val[of G ?\<pi>] one_in_P one_in_G[OF generic] elem_of_val
      domain_of_prod[OF one_in_P, of "domain(\<pi>')"] by force
  from \<open>env \<in> _\<close>
  obtain nenv where "nenv\<in>list(M)" "env = map(val(G),nenv)"
    using map_val by auto
  then
  have "length(nenv) = length(env)" by simp
  define f where "f(\<rho>p) \<equiv> \<mu> \<alpha>. \<alpha>\<in>M \<and> (\<exists>\<tau>\<in>M. \<tau> \<in> Vset(\<alpha>) \<and> 
        sats(M,forces(\<phi>),[P,leq,one,snd(\<rho>p),fst(\<rho>p),\<tau>] @ nenv))" (is "_ \<equiv> \<mu> \<alpha>. ?P(\<rho>p,\<alpha>)") for \<rho>p
  have "f(\<rho>p) = (\<mu> \<alpha>. \<alpha>\<in>M \<and> (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(##M,\<alpha>,V) \<and> \<tau>\<in>V \<and> 
        sats(M,forces(\<phi>),[P,leq,one,snd(\<rho>p),fst(\<rho>p),\<tau>] @ nenv)))" (is "_ = (\<mu> \<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>))") for \<rho>p
    unfolding f_def using Vset_abs Vset_closed Ord_Least_cong[of "?P(\<rho>p)" "\<lambda> \<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>)"]
    by (simp, simp del:setclass_iff)
  moreover
  have "f(\<rho>p) \<in> M" for \<rho>p
    unfolding f_def using Least_closed[of "?P(\<rho>p)"] by simp
  ultimately
  have 1:"least(##M,\<lambda>\<alpha>. ?Q(\<rho>p,\<alpha>),f(\<rho>p))" for \<rho>p
    using least_abs[of "\<lambda>\<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>)" "f(\<rho>p)"] least_conj 
    by (simp del:setclass_iff add:setclass_iff[symmetric])
  have "Ord(f(\<rho>p))" for \<rho>p unfolding f_def by simp
  define QQ where "QQ\<equiv>?Q"
  from 1
  have "least(##M,\<lambda>\<alpha>. QQ(\<rho>p,\<alpha>),f(\<rho>p))" for \<rho>p
    unfolding QQ_def .
  from \<open>arity(\<phi>) \<le> _\<close> \<open>length(nenv) = _\<close>
  have "arity(\<phi>) \<le> 2 #+ length(nenv)"
    by simp
  moreover
  note assms \<open>nenv\<in>list(M)\<close> \<open>?\<pi>\<in>M\<close>
  moreover
  have "\<rho>p\<in>?\<pi> \<Longrightarrow> \<exists>t p. \<rho>p=<t,p>" for \<rho>p
    by auto
  ultimately
  have body:"sats(M,body_fm(\<phi>,length(nenv)),[\<alpha>,\<rho>p,m,P,leq,one] @ nenv) \<longleftrightarrow> ?Q(\<rho>p,\<alpha>)" 
    if "\<rho>p\<in>?\<pi>" "\<rho>p\<in>M" "m\<in>M" "\<alpha>\<in>M" for \<alpha> \<rho>p m
    using that P_in_M leq_in_M one_in_M body_lemma[of \<rho>p _ _ nenv \<phi>] by simp
  let ?f_fm="least_fm(body_fm(\<phi>,length(nenv)),1)"
  {
    fix \<rho>p m
    assume asm: "\<rho>p\<in>M" "\<rho>p\<in>?\<pi>" "m\<in>M"
    note inM = this P_in_M leq_in_M one_in_M \<open>nenv\<in>list(M)\<close>
    with body
    have body':"\<And>\<alpha>. \<alpha> \<in> M \<Longrightarrow> (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(\<lambda>a. (##M)(a), \<alpha>, V) \<and> \<tau> \<in> V \<and> sats(M, forces(\<phi>), [P,leq,one,snd(\<rho>p),fst(\<rho>p),\<tau>] @ nenv)) \<longleftrightarrow>
          sats(M, body_fm(\<phi>,length(nenv)), Cons(\<alpha>, [\<rho>p, m, P, leq, one] @ nenv))" by simp
    from inM
    have "sats(M, ?f_fm,[\<rho>p,m,P,leq,one] @ nenv) \<longleftrightarrow> least(##M, QQ(\<rho>p), m)"
      using sats_least_fm[OF body', of 1] unfolding QQ_def 
      by (simp, simp del:setclass_iff add:setclass_iff[symmetric])
  }
  then
  have "sats(M, ?f_fm,[\<rho>p,m,P,leq,one] @ nenv) \<longleftrightarrow> least(##M, QQ(\<rho>p), m)" 
    if "\<rho>p\<in>M" "\<rho>p\<in>?\<pi>" "m\<in>M" for \<rho>p m using that by simp
  then
  have "univalent(##M, ?\<pi>, \<lambda>\<rho>p m. sats(M, ?f_fm, [\<rho>p,m] @ ([P,leq,one] @ nenv)))"
    unfolding univalent_def by (auto intro:unique_least)
  moreover from \<open>length(_) = _\<close> \<open>env \<in> _\<close>
  have "length([P,leq,one] @ nenv) = 3 #+ length(env)" by simp
  moreover from \<open>arity(_) \<le> 2 #+ length(nenv)\<close>
  have "arity(?f_fm) \<le> 5 #+ length(env)" (* or 8? *)
    unfolding body_fm_def using arity_forces arity_renrep sorry
  moreover from \<open>\<phi>\<in>formula\<close> \<open>nenv\<in>list(M)\<close>
  have "?f_fm\<in>formula" by simp
  moreover
  note inM = P_in_M leq_in_M one_in_M \<open>nenv\<in>list(M)\<close> \<open>?\<pi>\<in>M\<close>
  ultimately
  obtain Y where "Y\<in>M" "\<forall>m\<in>M. m \<in> Y \<longleftrightarrow> (\<exists>\<rho>p\<in>M. \<rho>p \<in> ?\<pi> \<and> 
          sats(M, ?f_fm, [\<rho>p,m] @ ([P,leq,one] @ nenv)))"
    using replacement_ax[of ?f_fm "[P,leq,one] @ nenv"]
    unfolding strong_replacement_def by auto
  with \<open>least(_,QQ(_),f(_))\<close> \<open>f(_) \<in> M\<close> \<open>?\<pi>\<in>M\<close> 
    \<open>_ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> sats(M,?f_fm,_) \<longleftrightarrow> least(_,_,_)\<close> 
  have "f(\<rho>p)\<in>Y" if "\<rho>p\<in>?\<pi>" for \<rho>p
    using that Transset_intf[OF trans_M _ \<open>?\<pi>\<in>M\<close>]
    by (clarsimp, rule_tac x="<x,y>" in bexI, auto)
  moreover
  have "{y\<in>Y. Ord(y)} \<in> M"
  proof -
    from \<open>Y\<in>M\<close>
    have "{y\<in>Y. Ord(y)} = {y\<in>Y. y\<in>M & Ord(y)}"
       using Transset_M[OF trans_M] by (simp)
    show ?thesis sorry
  qed
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
  have "{x\<in>Vset(?sup). x \<in> M} \<times> {one} \<in> M" (is "?big_name \<in> M")
    using cartprod_closed by simp
  then
  have "val(G,?big_name) \<in> M[G]"
    by (blast intro:GenExtI)
  {
    fix v x
    assume "x\<in>c"
    moreover
    note \<open>val(G,\<pi>')=c\<close> \<open>\<pi>'\<in>M\<close>
    moreover
    from calculation
    obtain \<rho> p where "<\<rho>,p>\<in>\<pi>'"  "val(G,\<rho>) = x" "p\<in>G" "\<rho>\<in>M"
      using elem_of_val_pair'[of \<pi>' x G] by blast
    moreover
    assume "v\<in>M[G]"
    then
    obtain \<sigma> where "val(G,\<sigma>) = v" "\<sigma>\<in>M"
      using GenExtD by blast
    moreover
    assume "sats(M[G], \<phi>, [x,v] @ env)"
    moreover
    note \<open>\<phi>\<in>_\<close> \<open>nenv\<in>_\<close> \<open>env = _\<close>
    ultimately
    obtain q where "q\<in>G" "sats(M, forces(\<phi>), [P,leq,one,q,\<rho>,\<sigma>] @ nenv)" 
      using truth_lemma[OF \<open>\<phi>\<in>_\<close> _ generic, symmetric, of "[\<rho>,\<sigma>] @ nenv"] by auto
    with \<open><\<rho>,p>\<in>\<pi>'\<close> \<open><\<rho>,q>\<in>?\<pi> \<Longrightarrow> f(<\<rho>,q>)\<in>Y\<close>
    have "f(<\<rho>,q>)\<in>Y" 
      using generic unfolding M_generic_def filter_def by blast
    let ?\<alpha>="succ(rank(\<sigma>))"
    (* Not sure if this encapsultation is really needed *)
    define PP where "PP(x) \<equiv> ?P(<\<rho>,q>,x)" for x
    note \<open>\<sigma>\<in>M\<close>
    moreover from this
    have "?\<alpha> \<in> M" 
      using rank_closed cons_closed by (simp del:setclass_iff add:setclass_iff[symmetric])
    moreover 
    have "\<sigma> \<in> Vset(?\<alpha>)"
      using Vset_Ord_rank_iff by auto
    moreover
    note \<open>sats(M, forces(\<phi>), [P,leq,one,q,\<rho>,\<sigma>] @ nenv)\<close>
    ultimately
    have "PP(?\<alpha>)" unfolding PP_def by (auto simp del: Vset_rank_iff)
    moreover
    have "Least(PP) = f(<\<rho>,q>)"
      unfolding PP_def f_def by simp
    ultimately
    obtain \<tau> where "\<tau>\<in>M" "\<tau> \<in> Vset(f(<\<rho>,q>))" "sats(M,forces(\<phi>),[P,leq,one,q,\<rho>,\<tau>] @ nenv)" 
      using LeastI[of PP ?\<alpha>] unfolding PP_def by auto
    with \<open>q\<in>G\<close> \<open>\<rho>\<in>M\<close> \<open>nenv\<in>_\<close>
    have "sats(M[G],\<phi>,map(val(G),[\<rho>,\<tau>] @ nenv))"
      using truth_lemma[OF \<open>\<phi>\<in>_\<close> _ generic, of "[\<rho>,\<tau>] @ nenv"] by auto
    moreover from \<open>x\<in>c\<close> \<open>c\<in>M[G]\<close>
    have "x\<in>M[G]" using Transset_intf[OF Transset_MG] by simp
    moreover
    note \<open>sats(M[G],\<phi>,[x,v] @ env)\<close> \<open>env = map(val(G),nenv)\<close> \<open>\<tau>\<in>M\<close> \<open>val(G,\<rho>)=x\<close>
      \<open>univalent(##M[G],_,_)\<close> \<open>x\<in>c\<close> \<open>v\<in>M[G]\<close>
    ultimately
    have "v=val(G,\<tau>)"
      using GenExtI[of \<tau> G] unfolding univalent_def by (auto)
    from \<open>\<tau> \<in> Vset(f(<\<rho>,q>))\<close> \<open>Ord(f(_))\<close>  \<open>f(<\<rho>,q>)\<in>Y\<close>
    have "\<tau> \<in> Vset(?sup)"  
      using Vset_Ord_rank_iff lt_Union_iff[of _ "rank(\<tau>)"] by auto
    with \<open>\<tau>\<in>M\<close>
    have "val(G,\<tau>) \<in> val(G,?big_name)"
      using domain_of_prod[of one "{one}" "{x\<in>Vset(?sup). x \<in> M}" ] def_val[of G ?big_name] 
        one_in_G[OF generic] one_in_P  by (auto simp del: Vset_rank_iff)
    with \<open>v=val(G,\<tau>)\<close>
    have "v \<in> val(G,{x\<in>Vset(?sup). x \<in> M} \<times> {one})"
      by simp
  }
  then
  have "{v. x\<in>c, v\<in>M[G]\<and>sats(M[G],\<phi>,[x,v]@env)} \<subseteq> val(G,?big_name)" (is "?repl\<subseteq>?big") 
    by blast
  with \<open>?big_name\<in>M\<close> 
  have "?repl = {v\<in>?big. \<exists>x\<in>c. sats(M[G], \<phi>, [x,v] @ env)}"
    apply (intro equality_iffI, subst Replace_iff)
    apply (auto intro:Transset_intf[OF Transset_MG _ GenExtI, of _ G ?big_name])
    using \<open>univalent(##M[G],_,_)\<close> unfolding univalent_def
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
    using Transset_intf[OF Transset_MG _ GenExtI, OF _ \<open>?big_name\<in>M\<close>]
    by (simp) 
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