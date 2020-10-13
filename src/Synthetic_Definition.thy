section\<open>Automatic synthesis of formulas\<close>
theory Synthetic_Definition
  imports "ZF-Constructible.Formula"
  keywords
    "synthesize" :: thy_decl % "ML"
    and
    "synthesize_notc" :: thy_decl % "ML"
    and
    "from_schematic"

begin
ML_file\<open>Utils.ml\<close>
ML\<open>
structure Formulas = Named_Thms
  (val name = @{binding "fm_definitions"}
   val description = "Theorems for synthetising formulas.") 
\<close>
setup\<open>Formulas.setup\<close>

ML\<open>
val $` = curry ((op $) o swap)
infix $`

infix 6 &&&
val op &&& = Utils.&&&

infix 6 ***
val op *** = Utils.***

fun prove_tc_form goal thms ctxt =
  Goal.prove ctxt [] [] goal (K (rewrite_goal_tac ctxt thms 1 THEN TypeCheck.typecheck_tac ctxt))

fun prove_sats_tm goal thms thm_auto ctxt =
  let
    val ctxt' = ctxt |> Simplifier.add_simp (hd thm_auto)
  in
    Goal.prove ctxt [] [] goal
    (K (rewrite_goal_tac ctxt thms 1 THEN PARALLEL_ALLGOALS (asm_simp_tac ctxt')))
  end

fun prove_sats_iff goal ctxt = Goal.prove ctxt [] [] goal (K (asm_simp_tac ctxt 1))

fun is_mem (@{const mem} $ _ $  _) = true
  | is_mem _ = false

fun synth_thm_sats_iff def_name term lhs set env hyps vars vs pos lthy =
  let
    val (_,tm,ctxt1) = Utils.thm_concl_tm lthy term
    val (_,ctxt2) = Variable.import true [Proof_Context.get_thm lthy term] ctxt1 |>> #2
    val vs' = map (Thm.term_of o #2) vs
    val vars' = map (Thm.term_of o #2) vars
    val r_tm = tm |> Utils.dest_lhs_def |> fold (op $`) vs'
    val sats = @{const apply} $ (@{const satisfies} $ set $ r_tm) $ env
    val rhs = @{const IFOL.eq(i)} $ sats $ (@{const succ} $ @{const zero})
    val ctxt3 = fold Utils.add_to_context (map Utils.freeName vars') ctxt2
    fun var_i s = Free (s, @{typ "i"})
    val (new_vs, ctxt4) = Variable.variant_fixes (map Utils.freeName vs') ctxt3 |>> map var_i
    val new_hyps =
      Utils.zip_with (fn v => fn nv => Utils.eq_ (Utils.nth_ v env) nv) vs' new_vs
      |> map Utils.tp
    val subst = Utils.zip_with (curry (I *** I)) vs' new_vs
    fun from_option (SOME v) = v
      | from_option NONE = raise TERM ("from_option", [])
    fun subst_nth (@{const "nth"} $ v $ _) = AList.lookup (op =) subst v |> from_option
      | subst_nth (t1 $ t2) = (subst_nth t1) $ (subst_nth t2)
      | subst_nth (Abs (v, ty, t)) = Abs (v, ty, subst_nth t)
      | subst_nth t = t
    val concl = @{const IFOL.iff} $ (subst_nth lhs) $ rhs
    val g_iff = Logic.list_implies (hyps @ new_hyps, Utils.tp concl)
    val thm =  prove_sats_iff g_iff ctxt4
    val name = Binding.name (def_name ^ "_iff_sats")
    val thm = Utils.fix_vars thm (map Utils.freeName (vars' @ new_vs)) lthy
  in
    Local_Theory.note ((name, []), [thm]) lthy |> Utils.display "theorem" pos
  end

fun synth_thm_sats_fm def_name term lhs set env hyps vars vs pos thm_auto lthy =
  let
    val (_,tm,ctxt1) = Utils.thm_concl_tm lthy term
    val (thm_refs,ctxt2) = Variable.import true [Proof_Context.get_thm lthy term] ctxt1 |>> #2
    val vs' = map (Thm.term_of o #2) vs
    val vars' = map (Thm.term_of o #2) vars
    val r_tm = tm |> Utils.dest_lhs_def |> fold (op $`) vs'
    val sats = @{const apply} $ (@{const satisfies} $ set $ r_tm) $ env
    val rhs = @{const IFOL.eq(i)} $ sats $ (@{const succ} $ @{const zero})
    val concl = @{const IFOL.iff} $ rhs $ lhs
    val g_iff = Logic.list_implies (hyps, Utils.tp concl)
    val thm = prove_sats_tm g_iff thm_refs thm_auto ctxt2
    val name = Binding.name ("sats_" ^ def_name ^ "_fm")
    val thm = Utils.fix_vars thm (map Utils.freeName vars') lthy
    val simp_attrib = @{attributes [simp]}
  in
    Local_Theory.note ((name, simp_attrib), [thm]) lthy |> Utils.display "theorem" pos
  end

fun synth_thm_tc def_name term hyps vars pos lthy =
  let
    val (_,tm,ctxt1) = Utils.thm_concl_tm lthy term
    val (thm_refs,ctxt2) = Variable.import true [Proof_Context.get_thm lthy term] ctxt1
                    |>> #2
    val vars' = map (Thm.term_of o #2) vars
    val tc_attrib = @{attributes [TC]}
    val r_tm = tm |> Utils.dest_lhs_def |> fold (op $`) vars'
    val concl = @{const mem} $ r_tm $ @{const formula}
    val g = Logic.list_implies(hyps, Utils.tp concl)
    val thm = prove_tc_form g thm_refs ctxt2
    val name = Binding.name (def_name ^ "_type")
    val thm = Utils.fix_vars thm (map Utils.freeName vars') ctxt2
  in
   Local_Theory.note ((name, tc_attrib), [thm]) lthy |> Utils.display "theorem" pos
  end


fun synthetic_def def_name thmref pos tc auto thy =
  let
    val (thm_ref,_) = thmref |>> Facts.ref_name
    val (((_,vars),thm_tms),_) = Variable.import true [Proof_Context.get_thm thy thm_ref] thy
    val (tm,hyps) = thm_tms |> hd |> Thm.concl_of &&& Thm.prems_of
    val (lhs,rhs) = tm |> Utils.dest_iff_tms o Utils.dest_trueprop
    val ((set,t),env) = rhs |> Utils.dest_sats_frm
    fun olist t = Ord_List.make String.compare (Term.add_free_names t [])
    fun relevant ts (@{const mem} $ t $ _) = not (Term.is_Free t) orelse
        Ord_List.member String.compare ts (t |> Term.dest_Free |> #1)
      | relevant _ _ = false
    val t_vars = olist t
    val vs = List.filter (Utils.inList t_vars o #1 o #1 o #1) vars
    val at = List.foldr (fn ((_,var),t') => lambda (Thm.term_of var) t') t vs
    val hyps' = List.filter (relevant t_vars o Utils.dest_trueprop) hyps
    val def_attrs = @{attributes [fm_definitions]}
  in
    Local_Theory.define ((Binding.name (def_name ^ "_fm"), NoSyn),
                        ((Binding.name (def_name ^ "_fm_def"), def_attrs), at)) thy
    |>> (#2 #> I *** single) |> Utils.display "theorem" pos |>
    (if tc then synth_thm_tc def_name (def_name ^ "_fm_def") hyps' vs pos else I) |>
    (if auto then
      synth_thm_sats_fm def_name (def_name ^ "_fm_def") lhs set env hyps vars vs pos thm_tms
      #> synth_thm_sats_iff def_name (def_name ^ "_fm_def") lhs set env hyps vars vs pos
    else I)
  end
\<close>
ML\<open>

local
  val synth_constdecl =
       Parse.position (Parse.string -- ((Parse.$$$ "from_schematic" |-- Parse.thm)));

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>synthesize\<close> "ML setup for synthetic definitions"
       (synth_constdecl >> (fn ((bndg,thm),p) => synthetic_def bndg thm p true true))

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>synthesize_notc\<close> "ML setup for synthetic definitions"
       (synth_constdecl >> (fn ((bndg,thm),p) => synthetic_def bndg thm p false false))

in

end
\<close>
text\<open>The \<^ML>\<open>synthetic_def\<close> function extracts definitions from
schematic goals. A new definition is added to the context. \<close>

(* example of use *)
(*
schematic_goal mem_formula_ex :
  assumes "m\<in>nat" "n\<in> nat" "env \<in> list(M)"
  shows "nth(m,env) \<in> nth(n,env) \<longleftrightarrow> sats(M,?frm,env)"
  by (insert assms ; (rule sep_rules empty_iff_sats cartprod_iff_sats | simp del:sats_cartprod_fm)+)

synthesize "\<phi>" from_schematic mem_formula_ex
*)

end
