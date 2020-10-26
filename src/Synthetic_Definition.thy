section\<open>Automatic synthesis of formulas\<close>
theory Synthetic_Definition
  imports "ZF-Constructible.Formula"
  keywords
    "synthesize" :: thy_decl % "ML"
    and
    "synthesize_notc" :: thy_decl % "ML"
    and
    "generate_schematic" :: thy_decl % "ML"
    and
    "from_schematic"
    and
    "for"
    and
    "from_definition"

begin
ML_file\<open>Utils.ml\<close>

named_theorems fm_definitions "Definitions of synthetized formulas."

named_theorems iff_sats "Theorems for synthetising formulas."

ML\<open>
val $` = curry ((op $) o swap)
infix $`

infix 6 &&&
val op &&& = Utils.&&&

infix 6 ***
val op *** = Utils.***

fun prove_tc_form goal thms ctxt =
  Goal.prove ctxt [] [] goal (K (rewrite_goal_tac ctxt thms 1 THEN TypeCheck.typecheck_tac ctxt))

fun prove_sats_tm thm_auto thms goal ctxt =
  let
    val ctxt' = ctxt |> Simplifier.add_simp (hd thm_auto)
  in
    Goal.prove ctxt [] [] goal
    (K (rewrite_goal_tac ctxt thms 1 THEN PARALLEL_ALLGOALS (asm_simp_tac ctxt')))
  end

fun prove_sats_iff goal ctxt = Goal.prove ctxt [] [] goal (K (asm_simp_tac ctxt 1))

fun is_mem (@{const mem} $ _ $  _) = true
  | is_mem _ = false

fun pre_synth_thm_sats term set env vars vs lthy =
  let
    val (_, tm, ctxt1) = Utils.thm_concl_tm lthy term
    val (thm_refs, ctxt2) = Variable.import true [Proof_Context.get_thm lthy term] ctxt1 |>> #2
    val vs' = map (Thm.term_of o #2) vs
    val vars' = map (Thm.term_of o #2) vars
    val r_tm = tm |> Utils.dest_lhs_def |> fold (op $`) vs'
    val sats = @{const apply} $ (@{const satisfies} $ set $ r_tm) $ env
    val sats' = @{const IFOL.eq(i)} $ sats $ (@{const succ} $ @{const zero})
  in
    { vars = vars'
    , vs = vs'
    , sats = sats'
    , thm_refs = thm_refs
    , lthy = ctxt2
    , env = env
    , set = set
    }
  end

fun synth_thm_sats_gen name lhs hyps pos attribs aux_funs environment lthy =
  let
    val ctxt = (#prepare_ctxt aux_funs) lthy
    val ctxt = Utils.add_to_context (Utils.freeName (#set environment)) ctxt
    val (new_vs, ctxt') = (#create_variables aux_funs) (#vs environment, ctxt)
    val new_hyps = (#create_hyps aux_funs) (#vs environment, new_vs)
    val concl = (#make_concl aux_funs) (lhs, #sats environment, new_vs)
    val g_iff = Logic.list_implies (new_hyps @ hyps, Utils.tp concl)
    val thm = (#prover aux_funs) g_iff ctxt'
    val thm = Utils.fix_vars thm (map Utils.freeName ((#vars environment) @ new_vs)) lthy
  in
    Local_Theory.note ((name, attribs), [thm]) lthy |> Utils.display "theorem" pos
  end

fun synth_thm_sats_iff def_name lhs hyps pos environment =
  let
    val subst = Utils.zip_with (I *** I) (#vs environment)
    fun subst_nth (@{const "nth"} $ v $ _) new_vs = AList.lookup (op =) (subst new_vs) v |> the
      | subst_nth (t1 $ t2) new_vs = (subst_nth t1 new_vs) $ (subst_nth t2 new_vs)
      | subst_nth (Abs (v, ty, t)) new_vs = Abs (v, ty, subst_nth t new_vs)
      | subst_nth t _ = t
    val name = Binding.name (def_name ^ "_iff_sats")
    val iff_sats_attrib = @{attributes [iff_sats]}
    val aux_funs = { prepare_ctxt = fold Utils.add_to_context (map Utils.freeName (#vs environment))
                   , create_variables = fn (vs, ctxt) => Variable.variant_fixes (map Utils.freeName vs) ctxt |>> map Utils.var_i
                   , create_hyps = fn (vs, new_vs) => Utils.zip_with (fn (v, nv) => Utils.eq_ (Utils.nth_ v (#env environment)) nv) vs new_vs |> map Utils.tp
                   , make_concl = fn (lhs, rhs, new_vs) => @{const IFOL.iff} $ (subst_nth lhs new_vs) $ rhs
                   , prover = prove_sats_iff
                   }
  in
    synth_thm_sats_gen name lhs hyps pos iff_sats_attrib aux_funs environment
  end

fun synth_thm_sats_fm def_name lhs hyps pos thm_auto environment =
  let
    val name = Binding.name ("sats_" ^ def_name ^ "_fm")
    val simp_attrib = @{attributes [simp]}
    val aux_funs = { prepare_ctxt = I
                   , create_variables = K [] *** I
                   , create_hyps = K []
                   , make_concl = fn (rhs, lhs, _) => @{const IFOL.iff} $ lhs $ rhs
                   , prover = prove_sats_tm thm_auto (#thm_refs environment)
                   }
  in
    synth_thm_sats_gen name lhs hyps pos simp_attrib aux_funs environment
  end

fun synth_thm_tc def_name term hyps vars pos lthy =
  let
    val (_,tm,ctxt1) = Utils.thm_concl_tm lthy term
    val (thm_refs,ctxt2) = Variable.import true [Proof_Context.get_thm lthy term] ctxt1 |>> #2
    val vars' = map (Thm.term_of o #2) vars
    val tc_attrib = @{attributes [TC]}
    val r_tm = tm |> Utils.dest_lhs_def |> fold (op $`) vars'
    val concl = @{const mem} $ r_tm $ @{const formula}
    val g = Logic.list_implies(hyps, Utils.tp concl)
    val thm = prove_tc_form g thm_refs ctxt2
    val name = Binding.name (def_name ^ "_fm_type")
    val thm = Utils.fix_vars thm (map Utils.freeName vars') ctxt2
  in
    Local_Theory.note ((name, tc_attrib), [thm]) lthy |> Utils.display "theorem" pos
  end

fun synthetic_def def_name thm_ref pos tc auto thy =
  let
    val (((_,vars),thm_tms),_) = Variable.import true [Proof_Context.get_thm thy thm_ref] thy
    val (tm,hyps) = thm_tms |> hd |> Thm.concl_of &&& Thm.prems_of
    val (lhs,rhs) = tm |> Utils.dest_iff_tms o Utils.dest_trueprop
    val ((set,t),env) = rhs |> Utils.dest_sats_frm
    fun olist t = Ord_List.make String.compare (Term.add_free_names t [])
    fun relevant ts (@{const mem} $ t $ _) = (not (t = @{term "0"})) andalso (not (Term.is_Free t) orelse
        Ord_List.member String.compare ts (t |> Term.dest_Free |> #1))
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
      pre_synth_thm_sats (def_name ^ "_fm_def") set env vars vs
      #> I &&& #lthy
      #> #1 &&& uncurry (synth_thm_sats_fm def_name lhs hyps pos thm_tms)
      #> uncurry (synth_thm_sats_iff def_name lhs hyps pos)
    else I)
  end

fun prove_schematic thms goal ctxt =
  let
    val rules = Named_Theorems.get ctxt \<^named_theorems>\<open>iff_sats\<close>
  in
    Goal.prove ctxt [] [] goal
    (K (rewrite_goal_tac ctxt thms 1 THEN REPEAT1 (resolve_tac ctxt rules 1 ORELSE asm_simp_tac ctxt 1)))
  end

fun schematic_def def_name target pos lthy =
  let
    val thm = Proof_Context.get_thm lthy (target ^ "_def")
    val (vars, tm, ctxt1) = Utils.thm_concl_tm lthy (target ^ "_def")
    val (const, tm) = tm |> Utils.dest_eq_tms' o Utils.dest_trueprop |>> #1 o strip_comb
    val t_vars = Term.add_free_names tm []
    val vs = List.filter (#1 #> #1 #> #1 #> Utils.inList t_vars) vars
             |> List.filter ((curry op = @{typ "i"}) o #2 o #1)
             |> List.map (Utils.var_i o #1 o #1 o #1)
    fun first_lambdas (Abs (body as (_, ty, _))) =
        if ty = @{typ "i"}
          then (op ::) (Term.dest_abs body |>> Utils.var_i ||> first_lambdas)
          else Term.dest_abs body |> first_lambdas o #2
      | first_lambdas _ = []
    val vs = vs @ (first_lambdas tm)
    val ctxt1' = fold Utils.add_to_context (map Utils.freeName vs) ctxt1
    val (set, ctxt2) = Variable.variant_fixes ["A"] ctxt1' |>> Utils.var_i o hd
    val class = @{const "setclass"} $ set
    val (env, ctxt3) = Variable.variant_fixes ["env"] ctxt2 |>> Utils.var_i o hd
    val hyps = (List.map (fn v => Utils.tp (Utils.mem_ v Utils.nat_)) vs) @ [Utils.tp (Utils.mem_ env (Utils.list_ set))]
    val args = class :: map (fn v => Utils.nth_ v env) vs
    val (fm_name, ctxt4) = Variable.variant_fixes ["fm"] ctxt3 |>> hd
    val fm_type = fold (K (fn acc => Type ("fun", [@{typ "i"}, acc]))) vs @{typ "i"}
    val fm = Var ((fm_name, 0), fm_type)
    val lhs = fold (op $`) args const
    val fm_app = fold (op $`) vs fm
    val sats = @{const apply} $ (@{const satisfies} $ set $ fm_app) $ env
    val rhs = @{const IFOL.eq(i)} $ sats $ (@{const succ} $ @{const zero})
    val concl = @{const "IFOL.iff"} $ lhs $ rhs
    val schematic = Logic.list_implies (hyps, Utils.tp concl)
    val thm = prove_schematic [thm] schematic ctxt4
    val thm = Utils.fix_vars thm (map Utils.freeName (set :: env :: vs)) lthy
  in
    Local_Theory.note ((Binding.name def_name, []), [thm]) lthy |> Utils.display "theorem" pos
  end

fun schematic_synthetic_def def_name target pos tc auto =
    (synthetic_def def_name ("sats_" ^ def_name ^ "_fm_auto") pos tc auto)
    o (schematic_def ("sats_" ^ def_name ^ "_fm_auto") target pos)

  (* val dummy = Specification.theorem_cmd false Thm.theoremK NONE (K I) Binding.empty_atts []
  [Element.Fixes [], Element.Assumes []] (Element.Shows [((@{binding "dummy"}, []), [("0 = 0", [])])]) *)
\<close>
ML\<open>

local
  val simple_from_schematic_synth_constdecl =
       Parse.string --| (Parse.$$$ "from_schematic")
       >> (fn bndg => synthetic_def bndg ("sats_" ^ bndg ^ "fm_auto"))

  val full_from_schematic_synth_constdecl =
       Parse.string -- ((Parse.$$$ "from_schematic" |-- Parse.thm))
       >> (fn (bndg,thm) => synthetic_def bndg (#1 (thm |>> Facts.ref_name)))

  val full_from_definition_synth_constdecl =
       Parse.string -- ((Parse.$$$ "from_definition" |-- Parse.string))
       >> (fn (bndg,target) => schematic_synthetic_def bndg target)

  val simple_from_definition_synth_constdecl =
     Parse.string --| (Parse.$$$ "from_definition")
     >> (fn bndg => schematic_synthetic_def bndg bndg)

  val synth_constdecl =
       Parse.position (full_from_schematic_synth_constdecl || simple_from_schematic_synth_constdecl
                       || full_from_definition_synth_constdecl
                       || simple_from_definition_synth_constdecl)

  val full_schematic_decl =
       Parse.string -- ((Parse.$$$ "for" |-- Parse.string))

  val simple_schematic_decl =
       Parse.$$$ "for" |-- Parse.string >> (fn name => "sats_" ^ name ^ "_fm_auto") &&& I

  val schematic_decl = Parse.position (full_schematic_decl || simple_schematic_decl)

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>synthesize\<close> "ML setup for synthetic definitions"
       (synth_constdecl >> (fn (f,p) => f p true true))

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>synthesize_notc\<close> "ML setup for synthetic definitions"
       (synth_constdecl >> (fn (f,p) => f p false false))

  val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>generate_schematic\<close> "ML setup for schematic goals"
       (schematic_decl >> (fn ((bndg,target),p) => schematic_def bndg target p))

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
