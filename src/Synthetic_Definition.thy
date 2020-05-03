section\<open>Automatic synthesis of formulas\<close>
theory Synthetic_Definition
  imports "ZF-Constructible.Formula"
  keywords
    "synthesize" :: thy_decl % "ML"
    and
    "from_schematic"

begin
ML_file\<open>Utils.ml\<close>

ML\<open>

fun display kind pos (thms,thy) =
  let val _ = Proof_Display.print_results true pos thy ((kind,""),[thms])
  in thy
end

fun synthetic_def def_name thmref pos thy =
  let
    val (thm_ref,_) = thmref |>> Facts.ref_name
    val (((_,vars),thm_tms),_) = Variable.import true [Proof_Context.get_thm thy thm_ref] thy
    val tm = thm_tms |> hd |> Thm.concl_of 
    val t = tm |> Utils.dest_tp_iff_rhs o Utils.dest_trueprop
    fun olist t = Ord_List.make String.compare (Term.add_free_names t [])
    val t_vars = olist t
    val vs = List.filter (fn (((v,_),_),_) => Utils.inList v t_vars) vars
    val at = List.foldr (fn ((_,var),t') => lambda (Thm.term_of var) t') t vs
  in
    Local_Theory.define ((Binding.name def_name, NoSyn),
                        ((Binding.name (def_name ^ "_def"), []), at)) thy |>
    (fn ((_,(s,t)),lthy') => display "definition" pos ((s,[t]),lthy'))
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
(*
schematic_goal mem_formula_ex :
  assumes "m\<in>nat" "n\<in> nat" "env \<in> list(M)"
  shows "nth(m,env) \<in> nth(n,env) \<longleftrightarrow> sats(M,?frm,env)"
  by (insert assms ; (rule sep_rules empty_iff_sats cartprod_iff_sats | simp del:sats_cartprod_fm)+)

synthesize "\<phi>" from_schematic mem_formula_ex
*)

end
