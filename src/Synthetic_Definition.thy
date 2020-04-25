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
open Utils

fun synthetic_def ctxt (def_bndg, thm_ref) =
  let 
    val tstr = def_bndg
    val defstr = tstr ^ "_def" 
    val (((_,vars),thm_tms),_) = Variable.import true [Proof_Context.get_thm ctxt thm_ref] ctxt
    val t = thm_tms |> hd |> dest_tp_iff_rhs o Thm.concl_of
    val t_vars = Term.add_free_names t []
    val vs = List.filter (fn (((v,_),_),_)  => inList v t_vars) vars
    val at = List.foldr (fn ((_,var),t') => lambda (Thm.term_of var) t') t vs
  in 
    Local_Theory.define ((Binding.name tstr, NoSyn), ((Binding.name defstr, []), at)) #> snd
  end;
\<close>
ML\<open>

local

val synth_constdecl = 
   Parse.position (Parse.string -- ((Parse.$$$ "from_schematic" |-- Parse.string)));

val _ =  
  Outer_Syntax.local_theory \<^command_keyword>\<open>synthesize\<close> "ML setup for synthetic definitions" 
 (synth_constdecl >> (fn ((bndg,thm),p) => ML_Context.expression p (
    ML_Lex.read ("Theory.local_setup ( (synthetic_def @{context} (\"" ^ bndg ^ "\",\"" ^ thm ^ "\")))"))
  |> Context.proof_map)
 )
in
end
\<close>
text\<open>The \<^ML>\<open>synthetic_def\<close> function extracts definitions from 
schematic goals. A new definition is added to the context. \<close>

(* example of use
schematic_goal mem_formula_ex :
  assumes "m\<in>nat" "n\<in> nat" "env \<in> list(M)"
  shows "nth(m,env) \<in> nth(n,env) \<longleftrightarrow> sats(M,?frm,env)"
  by (insert assms ; (rule sep_rules empty_iff_sats cartprod_iff_sats | simp del:sats_cartprod_fm)+)

synthesize "\<phi>" from_schematic "mem_formula_ex" 

lemma synth_mem_type : "m \<in> nat \<Longrightarrow> n\<in>nat \<Longrightarrow> \<phi>(n,m) \<in> formula"
  unfolding \<phi>_def by simp

*)

end
