theory Forcing_Experiments 
  imports Interface Names 

keywords
"synth_def" :: thy_decl % "ML"

begin

ML\<open>
 fun synthetic_def ctxt thm tstr defstr = 
  let 
    val (((_,[(_,vct)]),[novar]),ctxt1) = Variable.import true [Proof_Context.get_thm ctxt thm] ctxt
    val t = Thm.dest_equals_rhs (Thm.cterm_of ctxt1 ( Thm.concl_of(novar))) |> Thm.term_of 
    val at = lambda (Thm.term_of vct) t 
  in
  Local_Theory.define ((Binding.name tstr, NoSyn), ((Binding.name defstr, []), at)) #> snd 
  end;

local
fun synth_def source =
  ML_Lex.read_source false source
  |> ML_Context.expression (Input.range_of source) "synth" "string * string"
    "Context.map_proof (synthetic_def @{context} (fst synth)  (snd synth) (snd synth ^ \"_def\"))"
  |> Context.proof_map;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>synth_def\<close> "ML setup for synthetic definitions"
    (Parse.ML_source >> synth_def);
in end
\<close>

(*
Version for two parameters 
ML\<open>
 fun synthetic_def ctxt thm tstr defstr = 
  let 
    val (((_,[(_,vct),(_,vct')]),[novar]),ctxt1) = Variable.import true [Proof_Context.get_thm ctxt thm] ctxt
    val t = Thm.dest_equals_rhs (Thm.cterm_of ctxt1 ( Thm.concl_of(novar))) |> Thm.term_of 
    val at = lambda (Thm.term_of vct) (lambda (Thm.term_of vct') t)
  in
  Local_Theory.define ((Binding.name tstr, NoSyn), ((Binding.name defstr, []), at)) #> snd 
  end;

local
fun synth_def source =
  ML_Lex.read_source false source
  |> ML_Context.expression (Input.range_of source) "synth" "string * string"
    "Context.map_proof (synthetic_def @{context} (fst synth)  (snd synth) (snd synth ^ \"_def\"))"
  |> Context.proof_map;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>synth_def\<close> "ML setup for synthetic definitions"
    (Parse.ML_source >> synth_def);
in end
\<close>
*)

consts height :: "[i\<Rightarrow>i,i] \<Rightarrow> i"
primrec 
   "height(f,Member(x,y)) =
      (f(0))"

  "height(f,Equal(x,y)) = f(0)"

  "height(f,Nand(p,q)) = succ(max(height(f,p), height(f,q)))"

  "height(f,Forall(p)) = succ(height(f,p))"

context M_basic
begin
schematic_goal ff : "n:nat ==> height(\<lambda> x. x#+n, Nand(Member(0,3),Equal(3,0))) == ?x"
  by (simp add: max_def)

schematic_goal fff : "n:nat \<Longrightarrow> m:nat \<Longrightarrow>  n #+ m == ?x"
  by (simp add: max_def)

(*ML\<open>
 val t = Thm.dest_equals_rhs (Thm.cterm_of @{context} ( Thm.concl_of @{thm h})) |> Thm.term_of
\<close>
*)

local_setup\<open>
let
 val (_,ctxt) = Variable.add_fixes ["n"] @{context}
 val t = Thm.dest_equals_rhs (Thm.cterm_of ctxt ( Thm.concl_of @{thm ff[no_vars]})) |> Thm.term_of 
 val at = lambda (Free ("n",@{typ "i"})) t 
 val d = Local_Theory.define ((@{binding "my_x"}, NoSyn), ((@{binding "my_x_def"}, []), at)) #> snd
in
  d
end
\<close>

lemma p : "my_x(2) = 3" unfolding my_x_def ..

(* 
local_setup\<open>
  synthetic_def @{context} "ff" "another_x" "another_x_def"
\<close>
*)

(* 
Two variables 
synth_def\<open>("fff",  "suma")\<close>

lemma "suma(3,5) = 8" unfolding suma_def apply simp
*)

synth_def\<open>("ff",  "another_x")\<close>

lemma "another_x(2) = 3" unfolding another_x_def ..

end  (* context M_basic *)

context M_basic
begin
schematic_goal quequeres : "True \<and> False \<equiv> ?b"
  by (simp add: max_def)

local_setup\<open>
let val t = Thm.rhs_of @{thm quequeres} |> Thm.term_of
in
Local_Theory.define ((@{binding "my_b"}, NoSyn), ((@{binding "my_b_def"}, []), t)) #> snd
end
\<close>

end  (* context M_basic *)

end
