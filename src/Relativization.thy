section\<open>Automatic relativization of terms.\<close>
theory Relativization
  imports "ZF-Constructible.Formula"  "ZF-Constructible.Relative"
keywords
  "relativize" :: thy_decl % "ML"

begin
ML_file\<open>Utils.ml\<close>
ML\<open>@{term "0\<rightarrow>0"}\<close>

ML\<open>
structure Relativization  = struct
  (* For formulas like "t\<in>nat", we don't handle this yet. *)
  val db_rels_strange = [ (@{const nat} , @{const Relative.finite_ordinal})
                   , (@{const inj} , @{const Relative.injection})
                   , (@{const surj} , @{const Relative.surjection})
                   , (@{const bij} , @{const Relative.bijection})
                   ]

  (* relativization db of term constructors *)
  val db_tm_rels = [ (@{const Upair}, @{const Relative.upair})
           , (@{const Pair}, @{const Relative.pair})
           , (@{const zero}, @{const Relative.empty})
           , (@{const succ}, @{const Relative.successor})
           , (@{const cons}, @{const Relative.is_cons})
           , (@{const Collect}, @{const Relative.is_Collect})
           , (@{const Un}, @{const Relative.union})
           , (@{const Int}, @{const Relative.inter})
           , (@{const Union}, @{const Relative.big_union})
           , (@{const Int}, @{const Relative.inter})
           , (@{const Diff}, @{const Relative.setdiff})
           , (@{const Image}, @{const Relative.setdiff})
           , (@{const Sum.sum}, @{const Relative.is_sum})
           , (@{const Sum.Inl}, @{const Relative.is_Inl})
           , (@{const Sum.Inr}, @{const Relative.is_Inr})
           , (@{const domain}, @{const Relative.is_domain})
           , (@{const range}, @{const Relative.is_range})
           , (@{const field}, @{const Relative.is_field})
           , (@{const vimage}, @{const Relative.pre_image})
           , (@{const apply}, @{const Relative.fun_apply})
           , (@{const Perm.comp}, @{const Relative.composition})
           , (@{const Inter}, @{const Relative.big_inter})
           , (@{const bool_of_o}, @{const Relative.is_bool_of_o})
           , (@{const Bool.not}, @{const Relative.is_not})
           , (@{const Bool.and}, @{const Relative.is_and})
           , (@{const Bool.or}, @{const Relative.is_or})
           , (@{const List.Nil}, @{const Relative.is_Nil})
           , (@{const List.Cons}, @{const Relative.is_Cons})
           , (@{const Relative.is_hd}, @{const Relative.hd'})
           , (@{const Relative.is_tl}, @{const Relative.tl'})
           ]

  (* relativization db of relation constructors *)
  val db_rels = [ (@{const relation}, @{const Relative.is_relation})
           , (@{const mem}, @{const mem})
           , (@{const IFOL.eq(i)}, @{const IFOL.eq(i)})
           , (@{const Subset}, @{const Relative.subset})
           , (@{const quasinat}, @{const Relative.is_quasinat})
           , (@{const Transset}, @{const Relative.transitive_set})
           , (@{const quasinat}, @{const Relative.is_quasinat})
           , (@{const Ord}, @{const Relative.ordinal})
           , (@{const Limit}, @{const Relative.limit_ordinal})
           , (@{const relation}, @{const Relative.is_relation})
           , (@{const function}, @{const Relative.is_function})
           , (@{const quasinat}, @{const Relative.is_quasinat})
           , (@{const Relative.quasilist}, @{const Relative.is_quasilist})
           ]
  val db = db_tm_rels @ db_rels

(* t $` u = u $ t*)
val $` = curry ((op $) o swap)
infix $`

fun var_i v = Free (v, @{typ i})
fun var_io v = Free (v, @{typ "i \<Rightarrow> o"})
fun var_d v = Free (v, dummyT)
val const_name = #1 o dest_Const

fun lookup f = AList.lookup (fn (x, y) => x = f y)
val lookup_tm  = AList.lookup (op aconv)
val update_tm  =  AList.update (op aconv)
val join_tm = AList.join (op aconv) (fn _ => #1)

(* instantiated with diferent types than lookup_tm *)
val lookup_rel=  AList.lookup (op aconv)

val conj_ = Utils.binop @{const "IFOL.conj"}

(* Conjunction of a list of terms; avoids a superflous conjunction
with True if the last argument is SOME *)
fun conjs [] _ = @{term IFOL.True}
  | conjs (f :: []) NONE = f
  | conjs (f :: []) (SOME f') = conj_ f f'
  | conjs (f :: fs) f' = conj_ f (conjs fs f')

(* Produces a relativized existential quantification of the term t *)
fun rex p t (Free v) = @{const rex} $ p $ lambda (Free v) t
  | rex _ t (Bound _) = t
  | rex _ t tm = raise TERM ("rex shouldn't handle this.",[tm,t])

(* Constants that do not take the class predicate *)
val absolute_rels = [ @{const ZF_Base.mem}
                    , @{const IFOL.eq(i)}
                    ]

(* Creates the relational term corresponding to a term of type i. If the last
  argument is (SOME v) then that variable is not bound by an existential
  quantifier.
*)
fun close_rel_tm pred tm tm_var rs =
      let val news = filter (not o (fn x => is_Free x orelse is_Bound x) o #1) rs
          val (vars, tms) = split_list (map (op #2) news)
          val vars = case tm_var of
              SOME w => filter (fn v => not (v = w)) vars
            | NONE => vars
      in fold (fn v => fn t => rex pred (incr_boundvars 1 t) v) vars (conjs tms tm)
      end

fun relativ_tms _ _ _ ctxt' [] = ([], [], ctxt')
  | relativ_tms pred rel_db rs' ctxt' (u :: us) =
      let val (w_u, rs_u, ctxt_u) = relativ_tm pred rel_db (rs', ctxt') u
          val (w_us, rs_us, ctxt_us) = relativ_tms pred rel_db rs_u ctxt_u us
      in (w_u :: w_us, join_tm (rs_u , rs_us), ctxt_us)
      end
and
    (* The result of the relativization of a term is a triple consisting of
      a. the relativized term (it can be a free or a bound variable but also a Collect)
      b. a list of (term * (term, term)), taken as a map, which is used
         to reuse relativization of different occurrences of the same term. The
         first element is the original term, the second its relativized version,
         and the last one is the predicate corresponding to it.
      c. the resulting context of creating variables.
    *)
    relativ_tm pred rel_db (rs,ctxt) tm =
      let
      (* relativization of a fully applied constant *)
      fun relativ_fapp c args abs_args ctxt = case lookup_rel rel_db c of
                 SOME p => let
                    val (v, ctxt1) = Variable.variant_fixes [""] ctxt |>> var_i o hd
                    val r_tm = fold (op $`) (pred :: args @ abs_args @ [v]) p
                    in (v, r_tm, ctxt1)
                    end
               | NONE   =>
                  raise TERM ("Constant " ^ const_name c ^ " is not present in the db." , nil)

      (* relativization of a partially applied constant *)
      fun relativ_papp tm (t $ u) args abs_args rs' ctxt' = relativ_papp tm t (u :: args) abs_args rs' ctxt'
        | relativ_papp tm (Const c) args abs_args rs' ctxt' =
            let val (w_ts, rs_ts, ctxt_ts) = relativ_tms pred rel_db rs' ctxt' args
                val (w_tm, r_tm, ctxt_tm) = relativ_fapp (Const c) w_ts abs_args ctxt_ts
                val rs_ts' = update_tm (tm, (w_tm, r_tm)) rs_ts
            in  (w_tm, rs_ts', ctxt_tm)
            end
        | relativ_papp _ t _ _ _ _ =
            raise TERM ("Tried to relativize an application with a non-constant in head position",[t])

      fun go (Var _) _ _ = raise TERM ("Var: Is this possible?",[])
        | go (@{const Collect} $ t $ pc) rs ctxt =
            relativ_papp tm @{const Collect} [t] [pc] rs ctxt
        | go (tm as Const _) rs ctxt = relativ_papp tm tm [] [] rs ctxt
        | go (tm as t $ u) rs ctxt = relativ_papp tm t [u] [] rs ctxt
        | go tm rs ctxt = (tm, update_tm (tm,(tm,tm)) rs, ctxt)

      (* we first check if the term has been already relativized as a variable *)
      in case lookup_tm rs tm of
           NONE => go tm rs ctxt
         | SOME (w, _) => (w, rs, ctxt)
      end

fun relativ_tm_frm' cls_pred db ctxt tm =
      let val (w, rs, _) = relativ_tm cls_pred db ([],ctxt) tm
      in (w, close_rel_tm cls_pred NONE (SOME w) rs)
      end

fun relativ_tm_frm cls_pred db ctxt = #2 o relativ_tm_frm' cls_pred db ctxt

fun relativ_fm pred rel_db (rs,ctxt) fm =
  let

  (* relativization of a fully applied constant *)
  fun relativ_fapp c args = case lookup_rel rel_db c of
         SOME p => let
                   val flag = not (exists (curry op aconv c) absolute_rels)
                   in fold (op $`) (if flag then pred :: args else args) p
                   end
       | NONE   => raise TERM ("Constant " ^ const_name c ^ " is not present in the db." , nil)

  (* Relativization of partially applied constants; once we collected all the arguments
     we create as many relativized existentials as variables we had created while
     relativizing terms.
   *)
  fun relativ_papp (p $ t) args = relativ_papp p (t :: args)
    | relativ_papp (Const c) args =
        let val (w_ts, rs_ts, _) = relativ_tms pred rel_db rs ctxt args
            val tm = relativ_fapp (Const c) w_ts
        in close_rel_tm pred (SOME tm) NONE rs_ts
        end
    | relativ_papp tm _ =
        raise TERM ("Tried to relativize an application with a no-constant in head position",[tm])

  (* Handling of bounded quantifiers. *)
  fun bquant quant conn dom pred =
    let val (v,pred') = Term.dest_abs pred |>> var_i
    in
      go (quant $ lambda v (conn $ (@{const mem} $ v $ dom) $ pred'))
    end
  and
  (* We could share relativizations of terms occuring inside propositional connectives. *)
      go (@{const IFOL.conj} $ f $ f') = @{const IFOL.conj} $ go f $ go f'
    | go (@{const IFOL.disj} $ f $ f') = @{const IFOL.disj} $ go f $ go f'
    | go (@{const IFOL.Not} $ f) = @{const IFOL.Not} $ go f
    | go (@{const IFOL.iff} $ f $ f') = @{const IFOL.iff} $ go f $ go f'
    | go (@{const IFOL.imp} $ f $ f') = @{const IFOL.imp} $ go f $ go f'
    | go (@{const IFOL.All(i)} $ f) = @{const OrdQuant.rall} $ pred $ go f
    | go (@{const IFOL.Ex(i)} $ f) = @{const OrdQuant.rex} $ pred $ go f
    | go (@{const Bex} $ f $ Abs p) = bquant @{const Ex(i)} @{const IFOL.conj} f p
    | go (@{const Ball} $ f $ Abs p) = bquant @{const All(i)} @{const IFOL.imp} f p
    | go (Const c) = relativ_fapp (Const c) []
    | go (p $ t) = relativ_papp p [t]
    | go (Abs body) = body |> Term.dest_abs ||> go |>> var_i |> uncurry lambda
    | go t = raise TERM ("Relativization of formulas cannot handle this case.",[t])
  in go fm
  end


fun relativize_def ctxt cls_pred def_name thm_ref lthy =
  let
    val (cls_pred, ctxt1) = Variable.variant_fixes [cls_pred] ctxt |>> var_io o hd
    val (vars,tm,ctxt1) = Utils.thm_concl_tm ctxt1 (thm_ref ^ "_def")
    val (v,t) = tm |> #2 o Utils.dest_eq_tms' o Utils.dest_trueprop
                   |> relativ_tm_frm' cls_pred db ctxt1
    val t_vars = Term.add_free_names t []
    val vs = List.filter (fn (((v,_),_),_)  => Utils.inList v t_vars) vars
    val vs = [Thm.cterm_of ctxt cls_pred] @ map (op #2) vs @ [Thm.cterm_of ctxt v]
    val at = List.foldr (fn (var,t') => lambda (Thm.term_of var) t') t vs
  in
   lthy |>
   Local_Theory.define ((Binding.name def_name, NoSyn),
                        ((Binding.name (def_name ^ "_def"), []), at)) |>>
   Pretty.writeln o Syntax.pretty_term ctxt1 o Thm.concl_of o #2 o #2  |> #2
  end
end
\<close>

ML\<open>

local
  val relativize_parser =
       Parse.position (Parse.string -- Parse.string -- Parse.string);

  fun in_quote str = "\"" ^ str ^ "\""
  fun str xs = String.concatWith " " xs
  val prefix = "Theory.local_setup ((Relativization.relativize_def @{context}"
  val suffix = "))"
  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>relativize\<close> "ML setup for relativizing definitions"
       (relativize_parser >> (fn (((bndg,thm),pred),p) => ML_Context.expression p (
        ML_Lex.read (str (prefix :: (map in_quote [pred,thm,bndg]) @ [suffix])))
        |> Context.proof_map)
       )
in
end
\<close>
end