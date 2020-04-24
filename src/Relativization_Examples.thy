section\<open>Examples and testing of automatic relativization of terms and formulas.\<close>
theory Relativization_Examples
  imports "ZF-Constructible.Formula"  "ZF-Constructible.Relative" Relativization
begin

definition test1 :: "i \<Rightarrow> i" where
  "test1(a) == <0,a>"

definition test2 :: "o" where
  "test2 == <{0},{0,1}> \<in> 1"

definition test3 :: "i" where
  "test3 == {x \<in> 0 . x = x}"


ML\<open>
let 
  open Relativization

  fun lhs_def _ t =
   case t of 
      Const ("Pure.eq",_) $ _ $ y => y
    | _ => raise TERM ("dest_sats_lhs", [t]);

  fun test_relativ tm ctxt cls_pred db = 
  let val pp = Pretty.writeln o Syntax.pretty_term ctxt o Thm.term_of o Thm.cterm_of ctxt
  in 
   case fastype_of tm of
      @{typ i} => (pp tm, relativ_tm_frm tm cls_pred db ctxt |> pp)
    | @{typ o} => (pp tm, relativ_fm tm cls_pred db ([],ctxt) |> pp)
    | ty => raise TYPE ("We can relativize only terms of types i and o",[ty],[tm])
  end 

  fun relativiz_def ctxt def_bndg cls_pred db =
  let 
    val tstr = def_bndg
    val defstr = tstr ^ "_def" 
    val (((_,_),novars),ctxt1) = Variable.import true [Proof_Context.get_thm ctxt defstr] ctxt
    val thm = hd novars
    val t = (lhs_def ctxt o Thm.term_of o Thm.cterm_of ctxt o Thm.concl_of) thm
  in writeln def_bndg  ; test_relativ t ctxt1 cls_pred db
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
  val cls_pred = @{term "M:: i \<Rightarrow> o"}
in
  relativiz_defs @{context} cls_pred db ["test1","test2","test3"]
end
\<close>
end