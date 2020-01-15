theory Forcing_Main
  imports 
  (* minimum infrastructure to define the formulas *)
  Forcing_Data
  Synthetic_Definition
  (* Top elements of the development *)
  Choice_Axiom
  Ordinals_In_MG
  Succession_Poset

begin

schematic_goal ZF_union_auto:
    "Union_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?zfunion(i,j,h)))"
  unfolding Union_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_union_fm" from_schematic "ZF_union_auto"

schematic_goal ZF_power_auto:
    "power_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?zfpow(i,j,h)))"
  unfolding power_ax_def powerset_def subset_def
  by ((rule sep_rules | simp)+)

synthesize "ZF_power_fm" from_schematic "ZF_power_auto"

schematic_goal ZF_pairing_auto:
    "upair_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?zfpair(i,j,h)))"
  unfolding upair_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_pairing_fm" from_schematic "ZF_pairing_auto"

schematic_goal ZF_foundation_auto:
    "foundation_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?zfpow(i,j,h)))"
  unfolding foundation_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_foundation_fm" from_schematic "ZF_foundation_auto"

schematic_goal ZF_extensionality_auto:
    "extensionality(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?zfpow(i,j,h)))"
  unfolding extensionality_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_extensionality_fm" from_schematic "ZF_extensionality_auto"

schematic_goal ZF_infinity_auto:
    "infinity_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?\<phi>(i,j,h)))"
  unfolding infinity_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_infinity_fm" from_schematic "ZF_infinity_auto"

schematic_goal ZF_choice_auto:
    "choice_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?\<phi>(i,j,h)))"
  unfolding choice_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_choice_fm" from_schematic "ZF_choice_auto"

definition
  ZF_fin :: "i" where
  "ZF_fin \<equiv> {ZF_extensionality_fm,ZF_foundation_fm,ZF_pairing_fm,
              ZF_union_fm,ZF_infinity_fm,ZF_power_fm}"

(*
separation_ax:    "\<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> arity(\<phi>) \<le> 1 #+ length(env) \<Longrightarrow>
                    separation(##M,\<lambda>x. sats(M,\<phi>,[x] @ env))" 
replacement_ax:   "\<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> arity(\<phi>) \<le> 2 #+ length(env) \<Longrightarrow> 
                    strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,[x,y] @ env))" 
*)

(* fórmula compuesta por n veces Forall *)
consts 
  nForall :: "[i,i] \<Rightarrow> i"
primrec
  "nForall(0,p) = p"
  "nForall(succ(n),p) = Forall(nForall(n,p))" 


lemma nForall_type [TC]: 
      "[| n \<in> nat; p \<in> formula |] ==> nForall(n,p) \<in> formula"
  by (induct_tac "n",auto)

(*
  Esquema de separación
  Sea \<Phi> fórmula, donde 'y' no es libre.
  \<forall>a1...an\<forall>v\<exists>y\<forall>x. x\<in>y \<leftrightarrow> x\<in>v \<and> \<Phi>(x,v,a1,...,an)

  Ejemplo: Si \<Phi> = x=a \<or> x=b entonces
              p debe ser 0=2 \<or> 0=3
*)
definition
  ZF_separation_fm :: "i \<Rightarrow> i" where
  "ZF_separation_fm(p) == nForall(pred(arity(p)), 
                              Forall(Exists(Forall(
                              Iff(Member(0,1),And(Member(0,2),
                                              incr_bv1^2(p)))))))"
                                                
lemma ZF_separation_fm_type [TC]: "p \<in> formula \<Longrightarrow> ZF_separation_fm(p) \<in> formula"
  by (simp add: ZF_separation_fm_def)

notepad
begin
  fix M
  assume assms:"p \<in> formula \<Longrightarrow> M, [] \<Turnstile> (ZF_separation_fm(p))" for p
  have "\<phi>\<in>formula \<Longrightarrow> arity(\<phi>) \<le> 1 #+ length(env) \<Longrightarrow>
        separation(##M,\<lambda>x. sats(M,\<phi>,[x] @ env))" if "env\<in>list(M)" for \<phi> env
    using that
  proof (induct)
    case Nil
    moreover from this
    have "Arith.pred(arity(\<phi>)) = 0" 
      using pred_le[of _ 0] by (simp)
    moreover
    note assms[of \<phi>]
    ultimately
    show ?case 
      using formula_add_params1[of \<phi> 2 _ M "[_,_]" ]
      unfolding separation_def ZF_separation_fm_def
      by simp
  next
    case (Cons a l)
    then
    have "Arith.pred(arity(\<phi>)) \<le> 1 #+ length(l)" 
      using pred_le[of _ "succ(length(l))"] by (simp)
    have "Arith.pred(arity(\<phi>)) = n \<Longrightarrow> 
          separation(\<lambda>a. (##M)(a), \<lambda>x. (M, ([x] @ Cons(a, l)) \<Turnstile> \<phi>))"
      if "n \<in> nat" for n  using that
    proof (induct)
      case 0
      with assms[of \<phi>] and Cons
      show ?case 
        using formula_add_params1[of \<phi> 2 _ M "Cons(a,l)"  "[]"]
        unfolding separation_def ZF_separation_fm_def
        apply simp
        sorry
    next
      case (succ n)
      with assms[of \<phi>] and Cons
      show ?case 
      (*
      lemma sats_incr_bv_iff [rule_format]:
        "[| p \<in> formula; env \<in> list(A); x \<in> A |]
         ==> \<forall>bvs \<in> list(A).
                 sats(A, incr_bv(p) ` length(bvs), bvs @ Cons(x,env)) \<longleftrightarrow>
                 sats(A, p, bvs@env)"
      
      lemma formula_add_params1 [rule_format]:
        "[| p \<in> formula; n \<in> nat; x \<in> A |]
         ==> \<forall>bvs \<in> list(A). \<forall>env \<in> list(A).
                length(bvs) = n \<longrightarrow>
                sats(A, iterates(incr_bv1, n, p), Cons(x, bvs@env)) \<longleftrightarrow>
                sats(A, p, Cons(x,env))"
      *)
        using formula_add_params1[of \<phi> 2 _ M "Cons(a,l)"  "[]"]
        unfolding separation_def ZF_separation_fm_def
        apply simp
        sorry
    qed
    moreover from \<open>\<phi>\<in>_\<close>
    have "Arith.pred(arity(\<phi>)) \<in> nat" by simp
    ultimately
    show ?case by simp
  qed
   

end (* notepad *)




end