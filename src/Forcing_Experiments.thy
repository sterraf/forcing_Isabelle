theory Forcing_Experiments imports Interface Names begin

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

find_theorems name:my_x 
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

find_theorems name:my_b
end  (* context M_basic *)

end
