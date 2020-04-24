section\<open>Automatic relativization of terms.\<close>
theory Relativization
  imports "ZF-Constructible.Formula"  "ZF-Constructible.Relative"
  FrecR
begin

ML_file\<open>ZF_terms.ml\<close>

ML\<open>
structure Relativization  = struct

val $` = curry ((op $) o swap)
infix $`

fun var_i v = Free (v, @{typ i})
val const_name = #1 o dest_Const

fun lookup f = AList.lookup (fn (x, y) => x = f y)
val lookup_tm  = AList.lookup (op aconv)
val update_tm  =  AList.update (op aconv)
val join_tm = AList.join (op aconv) (fn _ => #1)
fun lookup_rel c ls =  AList.lookup (op aconv) ls c

fun fold1 _ [] = @{term IFOL.True}
  | fold1 _ (x :: []) = x
  | fold1 f (x :: xs) = f x (fold1 f xs)

fun conj_ t u = @{const IFOL.conj} $ t $ u
fun exB p t (Free v) = @{const rex} $ p $ lambda (Free v) t
  | exB _ t (Bound _) = t
  | exB _ t tm = raise TERM ("exB shouldn't handle this.",[tm,t])

(* constants that do not take the class predicate *)
val absolute_rels = [ @{const mem}
                    , @{const IFOL.eq(i)}
                    ]
fun need_cls_pred c = not (exists (fn t => c aconv t) absolute_rels)


fun relativ_tms _ _ [] _ ctxt' = ([], [], ctxt') 
  | relativ_tms pred ls (u :: us) rs' ctxt' = 
      let val (w_u, rs_u, ctxt_u) = relativ_tm u pred ls (rs', ctxt')
          val (w_us, rs_us, ctxt_us) = relativ_tms pred ls us rs_u ctxt_u
      in (w_u :: w_us, join_tm (rs_u , rs_us), ctxt_us)
      end
and 
    (* The result of the relativization of a term is a triple consisting of
      a. the relativized term (it can be a free or a bound variable but also a Collect)
      b. a list of (term * (term, term)), taken as a map, which is used to see
         to reuse relativization of different occurrences of the same term. The
         first element is the original term, the second its relativized version, 
         and the last one is the predicate corresponding to it.
      c. the resulting context of creating variables.
    *)
    relativ_tm tm pred ls (rs,ctxt) = 
      let 
      (* relativization of a fully applied constant *)
      fun relativ_fapp c args abs_args ctxt = case lookup_rel c ls of
                 SOME p => let 
                    val (vs, ctxt1) = Variable.variant_fixes [""] ctxt
                    val v = var_i (hd vs)
                    val r_tm = fold (op $`) (pred :: args @ abs_args @ [v]) p
                    in (v, r_tm, ctxt1)
                    end
               | NONE   => 
                  raise TERM ("Constant " ^ const_name c ^ " is not present in the db." , nil)

      (* relativization of a partially applied constant *)
      fun relativ_papp tm (t $ u) args abs_args rs' ctxt' = relativ_papp tm t (u :: args) abs_args rs' ctxt'
        | relativ_papp tm (Const c) args abs_args rs' ctxt' =
            let val (w_ts, rs_ts, ctxt_ts) = relativ_tms pred ls args rs' ctxt'
                val (w_tm, r_tm, ctxt_tm) = relativ_fapp (Const c) w_ts abs_args ctxt_ts
            in  (w_tm, update_tm (tm, (w_tm, r_tm)) rs_ts, ctxt_tm)
            end
        | relativ_papp _ t _ _ _ _ = 
            raise TERM ("Tried to relativize an application with a no-constant in head position",[t])

      fun go (Var _) _ _ = raise TERM ("Var: Is this possible?",[])
        | go (@{const Collect} $ t $ pc) rs ctxt = 
            relativ_papp tm @{const Collect} [t] [pc] rs ctxt
        | go (tm as Const _) rs ctxt = relativ_papp tm tm [] [] rs ctxt
        | go (tm as t $ u) rs ctxt = relativ_papp tm t [u] [] rs ctxt
        | go tm rs ctxt = (tm, update_tm (tm,(tm,tm)) rs, ctxt)

      (* we first check if the term has been already relativized as a variable *)
      in case lookup_tm rs tm  of
           NONE => go tm rs ctxt
         | SOME (w, _) => (w, rs, ctxt)
      end

fun relativ_fm fm pred rel_db (rs,ctxt) = 
  let 

  (* relativization of a fully applied constant *)
  fun relativ_fapp c args = case lookup_rel c rel_db of
         SOME p => let val flag = need_cls_pred c
                   in fold (op $`) (if flag then pred :: args else args) p
                   end
       | NONE   => raise TERM ("Constant " ^ const_name c ^ " is not present in the db." , nil)

  (* Relativization of partially applied constants; once we collected all the arguments
     we create as many relativized existentials as variables we had created while
     relativizing terms.
   *)
  fun relativ_papp (p $ t) args = relativ_papp p (t :: args)
    | relativ_papp (Const c) args = 
        let val (w_ts, rs_ts, _) = relativ_tms pred rel_db args rs ctxt
            val news = filter (not o (fn x => is_Free x orelse is_Bound x) o #1) rs_ts
            val (vars, tms) = split_list (map (op #2) news)
            val cnjs = fold conj_ tms (relativ_fapp (Const c) w_ts)
        in fold (fn v => fn t => exB pred (incr_boundvars 1 t) v) vars cnjs
        end
    | relativ_papp tm _ =
        raise TERM ("Tried to relativize an application with a no-constant in head position",[tm])

   fun go (@{const IFOL.conj} $ f $ f') = @{const IFOL.conj} $ go f $ go f'
        | go (@{const IFOL.disj} $ f $ f') = @{const IFOL.disj} $ go f $ go f'
        | go (@{const IFOL.Not} $ f) = @{const IFOL.Not} $ go f
        | go (@{const IFOL.iff} $ f $ f') = @{const IFOL.iff} $ go f $ go f'
        | go (@{const IFOL.imp} $ f $ f') = @{const IFOL.imp} $ go f $ go f'
        | go (@{const IFOL.All(i)} $ f) = @{const rall} $ pred $ go f
        | go (@{const IFOL.Ex(i)} $ f) = @{const rex} $ pred $ go f
        | go (Const c) = relativ_fapp (Const c) []
        | go (p $ t) = relativ_papp p [t]
        | go (Abs (v,ty,t)) = lambda (Free (v,ty)) (go t)
        | go t = raise TERM ("Relativization of formulas cannot handle this case.",[t])
  in  go fm
  end

  (* *)
  fun close_rel_tm pred (_, rs, _) = 
      let
          val news = filter (not o (fn x => is_Free x orelse is_Bound x) o #1) rs
          val (vars, tms) = split_list (map (op #2) news)
          val cnjs = fold1 conj_ tms
      in fold (fn v => fn t => exB pred (incr_boundvars 1 t) v) vars cnjs
      end

  fun relativ_tm_frm tm cls_pred db ctxt = 
    close_rel_tm cls_pred (relativ_tm tm cls_pred db ([],ctxt)) 

end;
\<close>
end