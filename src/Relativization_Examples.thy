section\<open>Examples and testing of automatic relativization of terms and formulas.\<close>
theory Relativization_Examples
  imports "ZF-Constructible.Formula"  "ZF-Constructible.Relative" Relativization
begin

definition test1 :: "i \<Rightarrow> i" where
  "test1(a) \<equiv> <0,a>"

definition test2 :: "i \<Rightarrow> o" where
  "test2(a) \<equiv> <0,1> \<in> a"

definition test2' :: "i \<Rightarrow> o" where
  "test2'(a) \<equiv> <{0},{0,1}> \<in> a"

definition test3 :: "i" where
  "test3 \<equiv> {x \<in> 0 . x = x}"

definition test4 :: "o" where
  "test4 \<equiv> \<exists>x\<in>1. x = 0"

definition test5 :: "o" where
  "test5 \<equiv> \<forall>x\<in>1. x = 0"

definition test6 :: "i \<Rightarrow> i" where
  "test6(a) = {x \<in> 2 . test2(a)}"

ML\<open>
structure Ex = struct
  val db = Relativization.db
  fun test_relativ tm ctxt cls_pred db =
  let val pp = Pretty.writeln o Syntax.pretty_term ctxt o Thm.term_of o Thm.cterm_of ctxt

  in
   case fastype_of tm of
      @{typ i} => (pp tm, Relativization.relativ_tm_frm cls_pred db ctxt tm |> pp)
    | @{typ o} => (pp tm, Relativization.relativ_fm cls_pred db ([],ctxt) tm |> pp)
    | ty => raise TYPE ("We can relativize only terms of types i and o",[ty],[tm])
  end

  fun relativiz_def ctxt def_name cls_pred db =
  let
    val (_,t,ctxt1) = Utils.thm_concl_tm ctxt (def_name ^ "_def")
    val t = Utils.dest_rhs_def t
  in writeln def_name ; test_relativ t ctxt1 cls_pred db
  end

  fun relativiz_defs ctxt cls_pred db = map (fn d => relativiz_def ctxt d cls_pred db)

  (* the class predicate*)
end ;

  Ex.relativiz_defs @{context} @{term "M :: i \<Rightarrow> o"} Ex.db
    ["test4","test5","test1","test2","test2'","test3"]

\<close>

relativize "test6" "is_test6" "M"

lemma (in M_trivial) test6_abs : "M(a) \<Longrightarrow> M(t) \<Longrightarrow> t = test6(a) \<longleftrightarrow> is_test6(M,a,t)"
  unfolding test6_def is_test6_def 
  using successor_abs empty_abs by simp

end
