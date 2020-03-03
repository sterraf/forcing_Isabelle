theory Renaming_Auto
  imports 
    Renaming
    ZF.Finite
    ZF.List
keywords
  "rename" :: thy_decl % "ML"
and
  "simple_rename" :: thy_decl % "ML"
and
  "src" 
and 
  "tgt"
abbrevs
  "simple_rename" = ""

begin

lemmas app_fun = apply_iff[THEN iffD1]
lemmas nat_succI = nat_succ_iff[THEN iffD2]

ML_file\<open>Renaming_ML.ml\<close>

ML\<open>
  fun renaming_def ctxt (name, from, to) =
    let val to = to |> Syntax.read_term ctxt 
        val from = from |> Syntax.read_term ctxt 
        val (_, fvs,r,tc_lemma,action_lemma) = sum_rename from to
        val (tc_lemma,action_lemma) = (fix_vars tc_lemma fvs , fix_vars action_lemma fvs)
        val ren_fun_name = Binding.name (name ^ "_fn")
        val ren_fun_def =  Binding.name (name ^ "_fn_def")
        val ren_thm = Binding.name (name ^ "_thm")
    in
      Local_Theory.note   ((ren_thm, []), [tc_lemma,action_lemma]) #> snd #>
      Local_Theory.define ((ren_fun_name, NoSyn), ((ren_fun_def, []), r)) #> snd       
  end;
\<close>


ML\<open>
  fun simple_renaming_def ctxt (name, from, to) =
    let val to = to |> Syntax.read_term ctxt 
        val from = from |> Syntax.read_term ctxt 
        val (tc_lemma,action_lemma,fvs,r) = ren_thm from to
        val (tc_lemma,action_lemma) = (fix_vars tc_lemma fvs , fix_vars action_lemma fvs)
        val ren_fun_name = Binding.name (name ^ "_fn")
        val ren_fun_def =  Binding.name (name ^ "_fn_def")
        val ren_thm = Binding.name (name ^ "_thm")
    in
      Local_Theory.note   ((ren_thm, []), [tc_lemma,action_lemma]) #> snd #>
      Local_Theory.define ((ren_fun_name, NoSyn), ((ren_fun_def, []), r)) #> snd       
  end;
\<close>


ML\<open>
local
  val env_parser = Parse.string;

  val ren_parser = Parse.position (Parse.string -- 
      (Parse.$$$ "src" |-- env_parser --| Parse.$$$ "tgt" -- env_parser));

  val prs = (ren_parser >> (fn ((name,(from,to)),p) => ML_Context.expression p (
    ML_Lex.read ("Theory.local_setup (renaming_def @{context} (\"" ^ name ^ "\",\"" ^ from ^ "\",\"" ^ to ^ "\"))"))
  |> Context.proof_map)) ;

  val simple_prs = (ren_parser >> (fn ((name,(from,to)),p) => ML_Context.expression p (
    ML_Lex.read ("Theory.local_setup (simple_renaming_def @{context} (\"" ^ name ^ "\",\"" ^ from ^ "\",\"" ^ to ^ "\"))"))
  |> Context.proof_map)) ;


  val _ =
   Outer_Syntax.local_theory \<^command_keyword>\<open>rename\<close> "ML setup for synthetic definitions" 
   prs

  val _ =
   Outer_Syntax.local_theory \<^command_keyword>\<open>simple_rename\<close> "ML setup for synthetic definitions" 
   simple_prs

in 
end
\<close>
end