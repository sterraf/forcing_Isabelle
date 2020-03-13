section\<open>Automatic synthesis of formulas\<close>
theory Synthetic_Definition
  imports "ZF-Constructible-Trans.Formula"
keywords
  "synthesize" :: thy_decl % "ML"
and
  "from_schematic"

begin
ML\<open>

fun dest_sats ctx ct = 
 case Thm.term_of ct of
   Const ("IFOL.eq",_) $ x $ y => (Thm.cterm_of ctx x,Thm.cterm_of ctx y)
  | _ => raise TERM ("dest_sats_lhs", [Thm.term_of ct]);

fun dest_applies_op ctx ct = 
 case Thm.term_of ct of
  Const ("ZF_Base.apply",_) $ x $ _  => Thm.cterm_of ctx x
  | _ => raise TERM ("dest_applies_op", [Thm.term_of ct]);

fun dest_satisfies_frm ctx ct = 
 case Thm.term_of ct of
  Const ("Formula.satisfies",_) $ _ $ frm  => Thm.cterm_of ctx frm
  | _ => raise TERM ("dest_satisfies_frm", [Thm.term_of ct]);


fun dest_sats_frm ctx = dest_satisfies_frm ctx o dest_applies_op ctx o #1 o dest_sats ctx ;

fun dest_trueprop ctx ct = 
 case Thm.term_of ct of
   Const ("IFOL.Trueprop",_) $ x  => Thm.cterm_of ctx x
  | _ => raise TERM ("dest_iff_rhs", [Thm.term_of ct]);

fun dest_iff_lhs ctx ct =
  (case Thm.term_of ct of
    Const ("IFOL.iff", _) $ x $ _ =>  Thm.cterm_of ctx x 
  | _ => raise TERM ("dest_iff_rhs", [Thm.term_of ct]));

fun dest_iff_rhs ctx ct =
  (case Thm.term_of ct of
    Const ("IFOL.iff", _) $ _ $ y =>  Thm.cterm_of ctx y
  | _ => raise TERM ("dest_iff_rhs", [Thm.term_of ct]));


fun dest_tp_iff_side func ctx = dest_sats_frm ctx o func ctx o dest_trueprop ctx ;

fun dest_tp_iff_rhs ctx = dest_sats_frm ctx o dest_iff_rhs ctx o dest_trueprop ctx ;


fun inList _ [] = false
  | inList a (b :: bs) = a = b orelse inList a bs

fun synthetic_def ctxt (def_bndg, thm_ref) =
  let 
    val tstr = def_bndg
    val defstr = tstr ^ "_def" 
  (* TODO: fix the fixed pattern [novar] (or not!) *)
    val (((_,vars),[novar]),ctxt1) = Variable.import true [Proof_Context.get_thm ctxt thm_ref] ctxt
    val t = (Thm.term_of o dest_tp_iff_rhs ctxt1 o Thm.cterm_of ctxt1 o Thm.concl_of) novar
    val t_vars = Term.add_free_names t []
    val vs = List.filter (fn (((v,_),_),_)  => inList v t_vars) vars
    val at = List.foldr (fn ((_,var),t') => lambda (Thm.term_of var) t') t vs
    val res = Local_Theory.define ((Binding.name tstr, NoSyn), ((Binding.name defstr, []), at)) #> snd
  in 
    res
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
