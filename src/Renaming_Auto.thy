theory Renaming_Auto
  imports 
    Renaming
    ZF.Finite
    ZF.List
begin

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

fun isFree (Free (_,_)) = true
  | isFree _ = false

fun freeName (Free (n,_)) = n
  | freeName _ = error "Not a free variable"

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
      val vs = rho  |> to_ML_list
      val ws = rho' |> to_ML_list |> filter isFree 
      val n = length vs
      val h1 = Const (@{const_name Subset},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ (vs|> mk_FinSet) $ setV
      val h2 = Const (@{const_name lt},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ j $ mk_ZFnat n
      val nth_ = Const (@{const_name nth},@{typ "i \<Rightarrow> i \<Rightarrow> i"})

      val fvs = ([j,setV ] @ ws |> filter isFree) |> map freeName

      val lhs = nth_ $ j $ rho
      val rhs = nth_ $ 
                  (Const (@{const_name apply}, @{typ "i\<Rightarrow>i\<Rightarrow>i"}) $ ren $ j) $ rho'
      val concl = Const (@{const_name IFOL.eq},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ lhs $ rhs
   in (Logic.list_implies([tp h1,tp h2],tp concl),fvs)
  end

  fun mk_sum_rename f m n p= 
    let val id_fun = Const (@{const_name id},@{typ "i\<Rightarrow>i"}) $ p
        val sum_const = Const (@{const_name sum},@{typ "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i"})
    in sum_const $ f $ id_fun $ m $ n $ p
  end

  fun ren_Thm e e' = 
   let  val ctxt = @{context}
        val r = mk_ren e e'
        val goal = mk_tc_lemma true r e e'
        val goal2 =  mk_dom_lemma r e
        val goal3 = mk_tc_lemma false r e e'
        val (goal4,fvs) = mk_action_lemma r e e'
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
    in (thm4,thm3,fvs,r)
  end

 fun fix_vars thm vars =
    let
      val ctxt0 = @{context}
      val (_, ctxt1) = Variable.add_fixes vars ctxt0
    in singleton (Proof_Context.export ctxt1 ctxt0) thm
  end

\<close>

local_setup\<open>
let val rho  = @{term "[P,leq,o,p,\<rho>,\<tau>,\<pi>]"}
    val rho' = @{term "[V,\<tau>,\<rho>,p,\<alpha>,P,leq,o,\<pi>]"}
    val (r,t,fvs,ren) = ren_Thm rho rho'
    val (r',t') = (fix_vars r fvs , fix_vars t fvs)
in
Local_Theory.note   ((@{binding "renrep_thm"}, []), [r',t']) #> snd #>
Local_Theory.define ((@{binding "renrep1_fn"}, NoSyn),
  ((@{binding "renrep1_def"}, []), ren)) #> snd
end\<close>

(*

mk_sum_rename f m n p: dado el renombre f : m \<rightarrow> n construye el renombre f+id(p)


definition renrep_fn :: "i \<Rightarrow> i" where
  "renrep_fn(n) == sum(renrep1_fn,id(n),7,9,n)"

lemma renrep_fn_type :
  assumes "n\<in>nat"
  shows "renrep_fn(n) \<in> 7#+n \<rightarrow> 9#+n"
  unfolding renrep_fn_def renrep1_def 
  using \<open>n\<in>nat\<close> sum_type[OF _ _ _ _ renrep_thm(2)] id_fn_type
  by simp

lemma renrep_fn_action : 
  assumes 
    "[P,leq,o,p,\<rho>,\<tau>,\<pi>] \<in> list(M)" 
    "env \<in> list(M)"
    "V \<in> M" "\<alpha> \<in> M"
  shows "\<And> i . i < 7 #+ length(env) \<Longrightarrow>
    nth(i, [P,leq,o,p,\<rho>,\<tau>,\<pi>] @ env) = nth(renrep_fn(length(env))`i, [V,\<tau>,\<rho>,p,\<alpha>,P,leq,o,\<pi>] @ env)"
proof - 
  from assms
  have 2:"[V,\<tau>,\<rho>,p,\<alpha>,P,leq,o,\<pi>] \<in> list(M)" 
       " {P, leq, o, p, \<rho>, \<tau>, \<pi>} \<subseteq> M " by simp_all
  let ?env1 = "[P,leq,o,p,\<rho>,\<tau>,\<pi>]"
  let ?env2 = "[V,\<tau>,\<rho>,p,\<alpha>,P,leq,o,\<pi>]" 
  let ?n = "length(env)"
  from \<open>env\<in>list(M)\<close> 
  have "length(env)\<in>nat" by simp
  then show "nth(i, [P,leq,o,p,\<rho>,\<tau>,\<pi>] @ env) = nth(renrep_fn(length(env))`i, [V,\<tau>,\<rho>,p,\<alpha>,P,leq,o,\<pi>] @ env)"
    if "i < 7 #+ length(env)" for i
     unfolding renrep_fn_def renrep1_def
     using \<open>?n\<in>nat\<close> that
       sum_action[OF _ _ \<open>?n\<in>nat\<close> \<open>?n\<in>nat\<close> renrep_thm(2)  id_fn_type
                        \<open>?env1 \<in> list(M)\<close> \<open>?env2 \<in> list(M)\<close> \<open>env\<in>list(M)\<close> \<open>env\<in>list(M)\<close>]
                         renrep_thm(1)[of P leq o p \<rho> \<tau> \<pi> M,OF 2(2)]
                         id_fn_action
     by simp
qed

definition 
  renrep :: "[i,i] \<Rightarrow> i" where
  "renrep(\<phi>,n) = ren(\<phi>)`(7#+n)`(9#+n)`renrep_fn(n)" 

lemma renrep_type [TC]: 
  assumes "\<phi>\<in>formula" "n \<in> nat"
    shows "renrep(\<phi>,n) \<in> formula"
 unfolding renrep_def
    using renrep_fn_type[OF assms(2)] ren_tc assms(1)
    by simp

lemma arity_renrep: 
  assumes "n\<in>nat" "\<phi>\<in>formula" "arity(\<phi>)\<le> 7#+n"
    shows "arity(renrep(\<phi>,n)) \<le> 9#+n"
 unfolding renrep_def
    using renrep_fn_type[OF assms(1)] ren_arity assms
    by simp

lemma renrep_sats :
  assumes
    "arity(\<phi>) \<le> 7 #+ length(env)"
    "[P,leq,o,p,\<rho>,\<tau>,\<pi>] @ env \<in> list(M)"
    "V \<in> M" "\<alpha> \<in> M"
    "\<phi>\<in>formula"
  shows "sats(M, \<phi>, [P,leq,o,p,\<rho>,\<tau>,\<pi>] @ env) \<longleftrightarrow> sats(M, renrep(\<phi>,length(env)), [V,\<tau>,\<rho>,p,\<alpha>,P,leq,o,\<pi>] @ env)"
proof -
  let ?env0 = "[P,leq,o,p,\<rho>,\<tau>,\<pi>]"
  let ?env' = "[V,\<tau>,\<rho>,p,\<alpha>,P,leq,o,\<pi>] @ env"
  let ?env1 = "[V,\<tau>,\<rho>,p,\<alpha>,P,leq,o,\<pi>]"
  from \<open>[P,leq,o,p,\<rho>,\<tau>,\<pi>] @ env \<in> list(M)\<close> \<open>V \<in> M\<close> \<open>\<alpha> \<in> M\<close>
  have 1:"7 #+ length(env) \<in> nat" "9 #+ length(env) \<in> nat"  "env \<in> list(M)" "?env0 \<in> list(M)" 
        "?env1 \<in> list(M)"
    by simp_all
  with assms 
  have 2:"length(env) \<in> nat" "?env' \<in> list(M)" by simp_all
  from assms
  have "[V,\<tau>,\<rho>,p,\<alpha>,P,leq,o,\<pi>] @ env \<in> list(M)" by simp
  show ?thesis
    unfolding renrep_def 
    using renrep_fn_action[OF \<open>?env0 \<in> list(M)\<close> \<open>env\<in>list(M)\<close> \<open>V\<in>M\<close> \<open>\<alpha>\<in>M\<close>]
    sats_iff_sats_ren[OF \<open>\<phi> \<in> formula\<close> 1(1) 1(2)  \<open>[P,leq,o,p,\<rho>,\<tau>,\<pi>] @ env \<in> list(M)\<close> 2(2)]
      renrep_fn_type[OF 2(1)] \<open>arity(\<phi>) \<le> 7#+length(env)\<close>      
   by simp
qed

*)
end