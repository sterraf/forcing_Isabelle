section\<open>Automatic synthesis of formulas\<close>
theory Synthetic_Definition
  imports "ZF-Constructible.Formula" Internalizations
  keywords
    "synthesize" :: thy_decl % "ML"
    and
    "from_schematic"

begin
ML_file\<open>Utils.ml\<close>

ML\<open>
val $` = curry ((op $) o swap)
infix $`

fun pair f g x = (f x, g x)

fun prove_tc_form goal thms ctxt =
  Goal.prove ctxt [] [] goal
     (fn _ => rewrite_goal_tac ctxt thms 1
              THEN ALLGOALS (asm_full_simp_tac ctxt))

fun display kind pos (thms,thy) =
  let val _ = Proof_Display.print_results true pos thy ((kind,""),[thms])
  in thy
end

fun synth_thm_tc name term hyps vars pos lthy =
let val (_,tm,ctxt1) = Utils.thm_concl_tm lthy term
    val (thm_refs,ctxt2) = Variable.import true [Proof_Context.get_thm lthy term] ctxt1
                    |>> #2
    val vars' = map (Thm.term_of o #2) vars
    val tc_attrib = @{attributes [TC]}
    val tm = tm |> Utils.dest_lhs_def
    val r_tm = fold (op $`) vars' tm
    val concl = @{const mem} $ r_tm $ @{const formula}
    val g = Logic.list_implies(hyps, Utils.tp concl)
    val thm = prove_tc_form g thm_refs ctxt2
    val name = Binding.name (name ^ "_type")
    val thm = Utils.fix_vars thm (map (#1 o dest_Free) vars') ctxt2
 in
   Local_Theory.note ((name, tc_attrib), [thm]) lthy |> display "theorem" pos
 end


fun synthetic_def def_name thmref pos thy =
  let
    val (thm_ref,_) = thmref |>> Facts.ref_name
    val (((_,vars),thm_tms),_) = Variable.import true [Proof_Context.get_thm thy thm_ref] thy
    val (tm,hyps) = thm_tms |> hd |> pair Thm.concl_of Thm.prems_of
    val t = tm |> Utils.dest_tp_iff_rhs o Utils.dest_trueprop
    fun olist t = Ord_List.make String.compare (Term.add_free_names t [])
    fun relevant ts (@{const mem} $ t $ _) = Ord_List.member String.compare ts (t |> Term.dest_Free |> #1)
      | relevant _ _ = false
    val t_vars = olist t
    val vs = List.filter (fn (((v,_),_),_) => Utils.inList v t_vars) vars
    val at = List.foldr (fn ((_,var),t') => lambda (Thm.term_of var) t') t vs
    val hyps' = List.filter (relevant t_vars o Utils.dest_trueprop) hyps
  in
    Local_Theory.define ((Binding.name def_name, NoSyn),
                        ((Binding.name (def_name ^ "_def"), []), at)) thy |>
    (fn ((_,(s,t)),lthy') => display "definition" pos ((s,[t]),lthy')) |>
    synth_thm_tc def_name (def_name ^ "_def") hyps' vs pos
end
\<close>
ML\<open>

local
  val synth_constdecl =
       Parse.position (Parse.string -- ((Parse.$$$ "from_schematic" |-- Parse.thm)));

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>synthesize\<close> "ML setup for synthetic definitions"
       (synth_constdecl >> (fn ((bndg,thm),p) => synthetic_def bndg thm p))
in

end
\<close>
text\<open>The \<^ML>\<open>synthetic_def\<close> function extracts definitions from
schematic goals. A new definition is added to the context. \<close>

(* example of use *)

schematic_goal mem_formula_ex :
  assumes "m\<in>nat" "n\<in> nat" "env \<in> list(M)"
  shows "nth(m,env) \<in> nth(n,env) \<longleftrightarrow> sats(M,?frm,env)"
  by (insert assms ; (rule sep_rules empty_iff_sats cartprod_iff_sats | simp del:sats_cartprod_fm)+)
definition "me" :: "[i,i] \<Rightarrow> i" where
  "me(x,y) == Member(x,y)"

synthesize "\<phi>" from_schematic mem_formula_ex

end
