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
fun length_ env = Const (@{const_name length},@{typ "i \<Rightarrow> i"}) $ env
fun nth_ i env = Const (@{const_name nth},@{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ i $ env
fun sum_ f g m n p = Const (@{const_name sum},@{typ "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i"}) $ f $ g $ m $ n $ p
fun add_ m n = Const (@{const_name "add"}, @{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ m $ n
fun mem_ el set = Const (@{const_name "mem"},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ el $ set
fun eq_ a b = Const (@{const_name IFOL.eq},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ a $ b
fun subset_ a b = Const (@{const_name Subset},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ a $ b
fun lt_ a b = Const (@{const_name lt},@{typ "i \<Rightarrow> i \<Rightarrow> o"}) $ a $ b
fun app_ f x = Const (@{const_name apply}, @{typ "i\<Rightarrow>i\<Rightarrow>i"}) $ f $ x
fun concat_ xs ys = Const (@{const_name app}, @{typ "i\<Rightarrow>i\<Rightarrow>i"}) $ xs $ ys
fun list_ set = Const (@{const_name list}, @{typ "i\<Rightarrow>i"}) $ set

(* Builds the finite mapping. *)
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
  in eq_ n (Const (@{const_name "domain"},@{typ "i \<Rightarrow> i"}) $ ren) |> tp
end

fun ren_tc_goal fin ren rho rho' =
  let val n = rho |> to_ML_list |> length
      val m = rho' |> to_ML_list |> length
      val fun_ty = if fin then @{const_name "FiniteFun"} else @{const_abbrev "function_space"}
      val ty = Const (fun_ty,@{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ mk_ZFnat n $ mk_ZFnat m
  in  mem_ ren ty |> tp
end

fun ren_action_goal ren rho rho'  =
  let val ctxt = @{context}
      val setV = Variable.variant_frees ctxt [] [("A",@{typ i})] |> hd |> Free
      val j = Variable.variant_frees ctxt [] [("j",@{typ i})] |> hd |> Free 
      val vs = rho  |> to_ML_list
      val ws = rho' |> to_ML_list |> filter isFree 
      val h1 = subset_ (vs|> mk_FinSet) setV
      val h2 = lt_ j (mk_ZFnat (length vs))
      val fvs = ([j,setV ] @ ws |> filter isFree) |> map freeName
      val lhs = nth_ j rho
      val rhs = nth_ (app_ ren j)  rho'
      val concl = eq_ lhs rhs
   in (Logic.list_implies([tp h1,tp h2],tp concl),fvs)
  end

  fun sum_tc_goal f m n p = 
    let val m_length = m |> to_ML_list |> length |> mk_ZFnat
        val n_length = n |> to_ML_list |> length |> mk_ZFnat
        val p_length = p |> lengthZF
        val id_fun = Const (@{const_name id},@{typ "i\<Rightarrow>i"}) $ p_length
        val sum_fun = sum_ f id_fun m_length n_length p_length
        val dom = add_ m_length p_length
        val codom = add_ n_length p_length
        val fun_ty = @{const_abbrev "function_space"}
        val ty = Const (fun_ty,@{typ "i \<Rightarrow> i \<Rightarrow> i"}) $ dom $ codom
  in  (sum_fun, mem_ sum_fun ty |> tp)
  end

fun sum_action_goal ren rho rho' =
  let val ctxt = @{context}
      val setV = Variable.variant_frees ctxt [] [("A",@{typ i})] |> hd |> Free
      val envV = Variable.variant_frees ctxt [] [("env",@{typ i})] |> hd |> Free
      val j = Variable.variant_frees ctxt [] [("j",@{typ i})] |> hd |> Free 
      val vs = rho  |> to_ML_list
      val ws = rho' |> to_ML_list |> filter isFree 
      val envL =  envV |> lengthZF
      val rhoL = vs |> length |> mk_ZFnat
      val h1 = subset_ (append vs ws |> mk_FinSet) setV
      val h2 = lt_ j (add_ rhoL envL)
      val h3 = mem_ envV (list_ setV)
      val fvs = ([j,setV,envV] @ ws |> filter isFree) |> map freeName
      val lhs = nth_ j (concat_ rho envV)
      val rhs = nth_ (app_ ren j) (concat_ rho' envV)
      val concl = eq_ lhs rhs
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

  fun ren_thm e e' = 
   let
    val ctxt = @{context}
    val r = mk_ren e e'
    val fin_tc_goal = ren_tc_goal true r e e'
    val dom_goal =  mk_dom_lemma r e
    val tc_goal = ren_tc_goal false r e e'
    val (action_goal,fvs) = ren_action_goal r e e'
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

(* 
Returns the sum renaming, the goal for type_checking, and the actual lemmas 
for the left part of the sum.
*)
 fun sum_ren_aux e e' = 
  let val ctxt = @{context}
      val env = Variable.variant_frees ctxt [] [("env",@{typ i})] |> hd |> Free
      val (left_action_lemma,left_tc_lemma,_,r) = ren_thm e e'
      val (sum_ren,sum_goal_tc) = sum_tc_goal r e e' env
      val setV = Variable.variant_frees ctxt [] [("A",@{typ i})] |> hd |> Free      
      fun hyp en = mem_ en (list_ setV)
  in (sum_ren,
      freeName env,
      Logic.list_implies (map (fn e => e |> hyp |> tp) [env], sum_goal_tc),
      left_tc_lemma,
      left_action_lemma)
end

fun sum_tc_lemma rho rho' =
  let val (sum_ren, envVar, tc_goal, left_tc_lemma, left_action_lemma) = sum_ren_aux rho rho'
      val (goal,fvs) = sum_action_goal sum_ren rho rho'
      val r = mk_ren rho rho'
      val ctx = @{context}
  in (sum_ren, goal,envVar, r,left_tc_lemma, left_action_lemma ,fvs, Goal.prove ctx [] [] tc_goal
               (fn _ =>
            resolve_tac ctx [@{thm sum_type_id_aux2}] 1
            THEN asm_simp_tac ctx 4
            THEN simp_tac ctx 1
            THEN resolve_tac ctx [left_tc_lemma] 1            
            THEN (fin ctx)
            THEN (fin ctx)
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
    val (sum_ren, goal, envVar, left_rename, left_tc_lemma, left_action_lemma, fvs, sum_tc_lemma) = sum_tc_lemma rho rho'
    val ctx = @{context}
    val action_lemma = fix_vars left_action_lemma fvs
  in (envVar, fvs, left_rename, sum_tc_lemma, Goal.prove ctx [] [] goal
    (fn _ => resolve_tac ctx [@{thm sum_action_id_aux}] 1
            THEN (simp_tac ctx 4)
            THEN (simp_tac ctx 1)
            THEN (resolve_tac ctx [left_tc_lemma]  1)
            THEN (asm_full_simp_tac ctx 1) 
            THEN (asm_full_simp_tac ctx 1)
            THEN (simp_tac ctx 1)
            THEN (simp_tac ctx 1)
            THEN (simp_tac ctx 1)
            THEN (full_simp_tac ctx 1)
            THEN (resolve_tac ctx [action_lemma] 1)
            THEN (blast_tac ctx  1)
            THEN (full_simp_tac ctx  1)
            THEN (full_simp_tac ctx  1)
    
   )
   )
end ;