section\<open>Examples and testing of automatic relativization of terms and formulas.\<close>
theory Relativization_Examples
  imports "ZF-Constructible.Formula"  "ZF-Constructible.Relative" Relativization
begin

definition test1 :: "i \<Rightarrow> i" where
  "test1(a) == <0,a>"

definition test2 :: "i \<Rightarrow> o" where
  "test2(a) == <0,1> \<in> a"

definition test2' :: "i \<Rightarrow> o" where
  "test2'(a) == <{0},{0,1}> \<in> a"

definition test3 :: "i" where
  "test3 == {x \<in> 0 . x = x}"


ML\<open>
structure Ex = struct

  open Relativization
  fun test_relativ tm ctxt cls_pred db = 
  let val pp = Pretty.writeln o Syntax.pretty_term ctxt o Thm.term_of o Thm.cterm_of ctxt
  in 
   case fastype_of tm of
      @{typ i} => (pp tm, relativ_tm_frm cls_pred db ctxt tm |> pp)
    | @{typ o} => (pp tm, relativ_fm cls_pred db ([],ctxt) tm |> pp)
    | ty => raise TYPE ("We can relativize only terms of types i and o",[ty],[tm])
  end 

  fun relativiz_def ctxt def_name cls_pred db =
  let 
    val (_,t,ctxt1) = Utils.thm_concl_tm ctxt (def_name ^ "_def")
    val t = Utils.dest_lhs_def t
  in writeln def_name ; test_relativ t ctxt1 cls_pred db
  end

  fun relativiz_defs ctxt cls_pred db = map (fn d => relativiz_def ctxt d cls_pred db)

  (* relativization db of term constructors *)
  val ls = [ (@{const Pair}, @{const Relative.pair})
           , (@{const zero}, @{const Relative.empty})
           , (@{const succ}, @{const Relative.successor})
           , (@{const cons}, @{const Relative.is_cons})
           , (@{const Collect}, @{const Relative.is_Collect})
           ]

  (* relativization db of relation constructors *)
  val rs = [ (@{const relation}, @{const Relative.is_relation})
           , (@{const mem}, @{const mem})
           , (@{const IFOL.eq(i)}, @{const IFOL.eq(i)})
           , (@{const Subset}, @{const Relative.subset})
           ]
  val db = ls @ rs

  (* the class predicate*)
end
(*in
  relativiz_defs @{context} @{term "M :: i \<Rightarrow> o"} db ["test1","test2","test2'","test3"]
  
end*)
\<close>
local_setup\<open>
  let
  fun relativized_def ctxt (def_name, thm_ref, cls_pred) =
  let                                                    
    val (vars,tm,ctxt1) = Utils.thm_concl_tm ctxt (thm_ref ^ "_def")
    val (v,t) = tm |> Utils.dest_lhs_def |> Relativization.relativ_tm_frm' cls_pred Ex.db ctxt1
    val t_vars = Term.add_free_names t []
    val vs = List.filter (fn (((v,_),_),_)  => Utils.inList v t_vars) vars
    val vs = [Thm.cterm_of ctxt cls_pred] @ map (op #2) vs @ [Thm.cterm_of ctxt v]
    val at = List.foldr (fn (var,t') => lambda (Thm.term_of var) t') t vs
  in
    Local_Theory.define ((Binding.name def_name, NoSyn), 
                        ((Binding.name (def_name ^ "_def"), []), at)) #> #2
  end;
  in
    relativized_def @{context} ("is_test", "test1", @{term "M :: i => o"})
  end
\<close>
lemma (in M_trans) test1_abs : "M(a) \<Longrightarrow> M(t) \<Longrightarrow> t = test1(a) \<longleftrightarrow> is_test(M,a,t)"
  unfolding is_test_def test1_def empty_abs pair_abs by simp

end
