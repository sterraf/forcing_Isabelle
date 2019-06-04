theory Renaming_Auto
  imports 
    Renaming
    ZF.Finite
    ZF.List
begin

abbreviation
  digit3 :: i   ("3") where "3 == succ(2)"

abbreviation
  digit4 :: i   ("4") where "4 == succ(3)"

abbreviation
  digit5 :: i   ("5") where "5 == succ(4)"

abbreviation
  digit6 :: i   ("6") where "6 == succ(5)"

abbreviation
  digit7 :: i   ("7") where "7 == succ(6)"

abbreviation
  digit8 :: i   ("8") where "8 == succ(7)"

abbreviation
  digit9 :: i   ("9") where "9 == succ(8)"

lemmas app_fun = apply_iff[THEN iffD1]
lemma le_natI : "j \<le> n \<Longrightarrow> n \<in> nat \<Longrightarrow> j\<in>nat"
  by(drule ltD,rule in_n_in_nat,rule nat_succ_iff[THEN iffD2,of n],simp_all)
lemmas nat_succI = nat_succ_iff[THEN iffD2]

ML\<open>
fun mk_Pair t t' = Const (@{const_name Pair},@{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ t $ t'

fun mk_FinSet nil = Const (@{const_name zero},@{typ i})
  | mk_FinSet (e :: es) = Const (@{const_name cons},@{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ e $ mk_FinSet es


fun mk_ZFnat 0 = Const (@{const_name zero},@{typ i})
  | mk_ZFnat n = Const (@{const_name succ},@{typ "i\<Rightarrow>i"}) $ mk_ZFnat (n-1)

fun mk_ZFlist _ nil = Const (@{const_name "Nil"}, @{typ "i"})
  | mk_ZFlist f (t :: ts) = Const (@{const_name "Cons"}, @{typ "i \<Rightarrow> i \<Rightarrow>i"}) $ f t $ mk_ZFlist f ts

fun to_ML_list (Const (@{const_name "Nil"}, _)) = nil
  | to_ML_list (Const (@{const_name "Cons"}, _) $ t $ ts) = t :: to_ML_list ts
  | to_ML_list _ = nil

fun index(item, xs) =
  let
    fun index'(_, nil) = NONE
      | index'(m, x::xr) = if x = item then SOME m else index'(m + 1, xr)
  in
    index'(0, xs)
  end

fun find_f rho rho' i = index(nth rho i,rho')
fun tp x = Const (@{const_name Trueprop},@{typ "o \<Rightarrow> prop"}) $ x

fun mk_ren rho rho' =
  let val rs  = to_ML_list rho
      val rs' = to_ML_list rho'
      val n = length rs-1
      val ixs = 0 upto n
      fun err t = "The element " ^ Syntax.string_of_term @{context} t ^ " is missing in the target environment"
      fun mkp i =
          case find_f rs rs' i of
            NONE => nth rs i |> err |> error
          | SOME j => mk_Pair (mk_ZFnat i) (mk_ZFnat j) 
  in  map mkp ixs |> mk_FinSet
  end                                                         

fun mk_dom_lemma ren rho =
  let val n = rho |> to_ML_list |> length |> mk_ZFnat
  in Const (@{const_name IFOL.eq},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ n $
      (Const (@{const_name "domain"},@{typ "i \<Rightarrow> i"}) $ ren) |> tp
end

fun mk_tc_lemma fin ren rho rho' =
  let val n = rho |> to_ML_list |> length
      val m = rho' |> to_ML_list |> length
      val fun_ty = if fin then @{const_name "FiniteFun"} else @{const_abbrev "function_space"}
      val ty = Const (fun_ty,@{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ mk_ZFnat n $ mk_ZFnat m
  in  Const (@{const_name "mem"},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ ren $ ty |> tp
end

fun mk_action_lemma ren rho rho'  =
  let val ctxt = @{context}
      val setV = Variable.variant_frees ctxt [] [("A",@{typ i})] |> hd |> Free
      val j = Variable.variant_frees ctxt [] [("j",@{typ i})] |> hd |> Free 
      val vs = rho |> to_ML_list        
      val n = length vs
      val h1 = Const (@{const_name Subset},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ (vs|> mk_FinSet) $ setV
      val h2 = Const (@{const_name lt},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ j $ mk_ZFnat n
      val nth_ = Const (@{const_name nth},@{typ "i \<Rightarrow> i \<Rightarrow> i"})

      val lhs = nth_ $ j $ rho
      val rhs = nth_ $ 
                  (Const (@{const_name apply}, @{typ "i\<Rightarrow>i\<Rightarrow>i"}) $ ren $ j) $ rho'
      val concl = Const (@{const_name IFOL.eq},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ lhs $ rhs
   in Logic.list_implies([tp h1,tp h2],tp concl)
  end

  val my_thm = 
   let  val e = @{term "[b,c,a]"} 
        val e' = @{term "[c,b,a,q,z,ew,e]"}
        val ctxt = @{context}
        val r = mk_ren e e'
        val goal = mk_tc_lemma true r e e'
        val goal2 =  mk_dom_lemma r e
        val goal3 = mk_tc_lemma false r e e'
        val goal4 = mk_action_lemma r e e'
        val thm = Goal.prove ctxt [] [] goal 
      (fn _ => REPEAT (
      resolve_tac ctxt [@{thm consI}] 1
      THEN resolve_tac ctxt [@{thm ltD}] 1
      THEN simp_tac ctxt 1
      THEN resolve_tac ctxt [@{thm ltD}] 1
      THEN simp_tac ctxt 1)
      THEN resolve_tac ctxt [@{thm emptyI}] 1
      THEN REPEAT (simp_tac ctxt 1))
       val thm2 = Goal.prove ctxt [] [] goal2
            (fn _ => blast_tac ctxt 1) 
    val thm3 =  Goal.prove ctxt [] [] goal3
            (fn _ =>  EqSubst.eqsubst_tac ctxt [1] [thm2] 1
              THEN resolve_tac ctxt [@{thm FiniteFun_is_fun}] 1
              THEN resolve_tac ctxt [thm] 1)
    val thm4 = Goal.prove ctxt [] [] goal4
              (fn _ => 
                   let 
                   fun fin ctx = 
                          REPEAT (resolve_tac ctx [@{thm nat_succI}] 1)
                          THEN   resolve_tac ctx [@{thm nat_0I}] 1
                   fun step ctx = asm_full_simp_tac ctx 1
                                  THEN asm_full_simp_tac ctx 1
                                  THEN EqSubst.eqsubst_tac ctx [1] [@{thm app_fun} OF [thm3]] 1
                                  THEN simp_tac ctx 1
                                  THEN simp_tac ctx 1
                   fun tact ctx = resolve_tac ctx [@{thm natE}] 1
                                  THEN step ctx                                  
                 in
                  forward_tac ctxt [@{thm le_natI}] 1
                  THEN fin ctxt
                  THEN REPEAT (tact ctxt)
                  THEN (step ctxt)
                end)
    in thm4
  end
\<close>