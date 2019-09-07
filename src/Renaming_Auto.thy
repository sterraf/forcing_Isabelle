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
(* Smart constructors for ZF-terms *)
fun mk_Pair t t' = Const (@{const_name Pair},@{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ t $ t'

fun lengthZF p = Const (@{const_name length},@{typ "i \<Rightarrow> i"}) $ p

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

fun tp x = Const (@{const_name Trueprop},@{typ "o \<Rightarrow> prop"}) $ x

fun mk_ren rho rho' =
  let val rs  = to_ML_list rho
      val rs' = to_ML_list rho'
      val ixs = 0 upto (length rs-1)
      fun err t = "The element " ^ Syntax.string_of_term @{context} t ^ " is missing in the target environment"
      fun mkp i =
          case find_index (fn x => x = nth rs i) rs' of
            ~1 => nth rs i |> err |> error
          |  j => mk_Pair (mk_ZFnat i) (mk_ZFnat j) 
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

  fun mk_sum_rename f m n p = 
    let val id_fun = Const (@{const_name id},@{typ "i\<Rightarrow>i"}) $ p
        val sum_const = Const (@{const_name sum},@{typ "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i"})
    in sum_const $ f $ id_fun $ m $ n $ p
  end

  fun mk_sum_tc f m n p = 
    let val m_length = m |> lengthZF (* to_ML_list |> length |> *)
        val n_length = n |> lengthZF (* to_ML_list |> length |> to_ZF *)
        val p_length = p |> lengthZF
        val sum_fun = mk_sum_rename f m_length n_length p_length
        val dom = Const (@{const_name "add"}, @{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ m_length $ p_length
        val codom = Const (@{const_name "add"}, @{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ n_length $ p_length
        val fun_ty = @{const_abbrev "function_space"}
        val ty = Const (fun_ty,@{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ dom $ codom
  in  (sum_fun, Const (@{const_name "mem"},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ sum_fun $ ty |> tp)
  end

fun mk_sum_action_lemma ren rho rho' =
  let val ctxt = @{context}
      val setV = Variable.variant_frees ctxt [] [("A",@{typ i})] |> hd |> Free
      val envV = Variable.variant_frees ctxt [] [("env",@{typ i})] |> hd |> Free
      val j = Variable.variant_frees ctxt [] [("j",@{typ i})] |> hd |> Free 
      val vs = rho  |> to_ML_list
      val ws = rho' |> to_ML_list |> filter isFree 
      val envL = envV |> lengthZF
      val rhoL = rho |> lengthZF
      val h1 = Const (@{const_name Subset},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ (append vs ws |> mk_FinSet) $ setV
      val h2 = Const (@{const_name lt},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ j $ 
                (Const (@{const_name add},@{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ rhoL $ envL)
      val h3 = Const (@{const_name mem},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ envV $ (Const (@{const_name list},@{typ "i\<Rightarrow>i"}) $ setV)
      val nth_ = Const (@{const_name nth},@{typ "i \<Rightarrow> i \<Rightarrow> i"})
      val fvs = ([j,setV,envV] @ ws |> filter isFree) |> map freeName
      val lhs = nth_ $ j $ (Const (@{const_name app},@{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ rho $ envV)
      val rhs = nth_ $ 
                  (Const (@{const_name apply}, @{typ "i\<Rightarrow>i\<Rightarrow>i"}) $ ren $ j) $ 
                  (Const (@{const_name app},@{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ rho' $ envV)
      val concl = Const (@{const_name IFOL.eq},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ lhs $ rhs
   in (Logic.list_implies([tp h1,tp h2,tp h3],tp concl),fvs)
  end

  (* Tactics *)
  fun fin ctx = 
         REPEAT (resolve_tac ctx [@{thm nat_succI}] 1)
         THEN   resolve_tac ctx [@{thm nat_0I}] 1

  fun step ctx thm = 
    asm_full_simp_tac ctx 1
    THEN asm_full_simp_tac ctx 1
    THEN EqSubst.eqsubst_tac ctx [1] [@{thm app_fun} OF [thm]] 1
    THEN simp_tac ctx 1
    THEN simp_tac ctx 1

  fun fin_fun_tac ctxt = 
  REPEAT (
      resolve_tac ctxt [@{thm consI}] 1
      THEN resolve_tac ctxt [@{thm ltD}] 1
      THEN simp_tac ctxt 1
      THEN resolve_tac ctxt [@{thm ltD}] 1
      THEN simp_tac ctxt 1)
  THEN resolve_tac ctxt [@{thm emptyI}] 1
  THEN REPEAT (simp_tac ctxt 1)

  fun ren_Thm e e' = 
   let
    val ctxt = @{context}
    val r = mk_ren e e'
    val fin_tc_goal = mk_tc_lemma true r e e'
    val dom_goal =  mk_dom_lemma r e
    val tc_goal = mk_tc_lemma false r e e'
    val (action_goal,fvs) = mk_action_lemma r e e'
    val fin_tc_lemma = Goal.prove ctxt [] [] fin_tc_goal (fn _ => fin_fun_tac ctxt)
    val dom_lemma = Goal.prove ctxt [] [] dom_goal (fn _ => blast_tac ctxt 1) 
    val tc_lemma =  Goal.prove ctxt [] [] tc_goal
            (fn _ =>  EqSubst.eqsubst_tac ctxt [1] [dom_lemma] 1
              THEN resolve_tac ctxt [@{thm FiniteFun_is_fun}] 1
              THEN resolve_tac ctxt [fin_tc_lemma] 1)
    val action_lemma = Goal.prove ctxt [] [] action_goal
              (fn _ => 
                  forward_tac ctxt [@{thm le_natI}] 1
                  THEN fin ctxt
                  THEN REPEAT (resolve_tac ctxt [@{thm natE}] 1
                               THEN step ctxt tc_lemma)
                  THEN (step ctxt tc_lemma)
              )
    in (action_lemma, tc_lemma, fvs, r)
  end

 fun sumRen_Thm e e' = 
  let val ctxt = @{context}
      val env = Variable.variant_frees ctxt [] [("env",@{typ i})] |> hd |> Free
      val (action_lemma,tc_lemma,fvs,r) = ren_Thm e e'
      val (sum_ren,goal_tc) = mk_sum_tc r e e' env
      val setV = Variable.variant_frees ctxt [] [("A",@{typ i})] |> hd |> Free      
      fun hyp en = Const (@{const_name mem},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ en
                $ (Const (@{const_name "list"}, @{typ "i\<Rightarrow>i"}) $ setV)
  in (sum_ren,Logic.list_implies (map (fn e => e |> hyp |> tp) [e,e',env], goal_tc),tc_lemma,action_lemma)
end

fun mk_sum_thm_tc rho rho' =
  let val (r,g,t1,t2) = sumRen_Thm rho rho'
      val (goal,fvs) = mk_sum_action_lemma r rho rho'
      val r = mk_ren rho rho'
      val ctx = @{context}
  in (goal,r,t1,t2,fvs,Goal.prove ctx [] [] g
      (fn _ =>
            resolve_tac ctx [@{thm sum_type_id}] 1
            THEN asm_full_simp_tac ctx 3
            THEN asm_full_simp_tac ctx 1
            THEN asm_full_simp_tac ctx 1
            THEN simp_tac ctx  1
            THEN resolve_tac ctx [t1] 1
  ))
  end

 fun fix_vars thm vars =
    let
      val ctxt0 = @{context}
      val (_, ctxt1) = Variable.add_fixes vars ctxt0
    in singleton (Proof_Context.export ctxt1 ctxt0) thm
  end 

fun sum_rename rho rho' = 
  let
    val (goal, r, t1, t2, fvs, sum_tc_lemma) = mk_sum_thm_tc rho rho'
    val ctx = @{context}
    val action_lemma = fix_vars t2 fvs
  in (fvs, r, sum_tc_lemma, Goal.prove ctx [] [] goal
    (fn _ => resolve_tac ctx [@{thm sum_action_id}] 1
            THEN (simp_tac ctx 4)
            THEN (asm_full_simp_tac ctx 1) 
            THEN (asm_full_simp_tac ctx 1)
            THEN (asm_full_simp_tac ctx 3)
            THEN (simp_tac ctx 1)
            THEN (resolve_tac ctx [t1]  1)
            THEN (resolve_tac ctx [action_lemma] 1)
            THEN (blast_tac ctx  1)
            THEN (full_simp_tac ctx  1)
   ))
end
\<close>

(*
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