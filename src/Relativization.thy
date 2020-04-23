section\<open>Automatic relativization of terms.\<close>
theory Relativization
  imports "ZF-Constructible.Formula"  "ZF-Constructible.Relative"

begin
ML_file\<open>ZF_terms.ml\<close>

ML\<open>
structure Relativization  = struct

fun var_i v = Free (v, @{typ i})
val const_name = #1 o dest_Const
fun lookup f = AList.lookup (fn (x, y) => x = f y)
val lookup_tm  = AList.lookup (op aconv)
val update_tm  =  AList.update (op aconv)
fun lookup_rel c ls =  lookup const_name ls c
fun conj_ t u = @{const IFOL.conj} $ t $ u
fun exB p t (Free v) = @{const rex} $ p $ lambda (Free v) t
  | exB _ t (Bound _) = t
  | exB _ t tm = raise TERM ("exB shouldn't handle this.",[tm,t])
fun debug t = writeln (Pretty.string_of (Syntax.pretty_term @{context} t))
(*
Relativization of the term tm with respect of the predicate pred. The already relativized constants
are given in the list ls; the argument rs is the list of terms already relativized and ctxt is used
to generate fresh names.
*)
fun relativ_tms _ _ [] _ ctxt' = ([], [], ctxt') 
 |  relativ_tms pred ls (u :: us) rs' ctxt' = 
           let val (w_u, rs_u, ctxt_u) = relativ_tm u pred ls (rs', ctxt')
               val (w_us, rs_us, ctxt_us) = relativ_tms pred ls us rs_u ctxt_u
          in (w_u :: w_us, rs_u @ rs_us, ctxt_us)
          end
and 
relativ_tm tm pred ls (rs,ctxt) = 
  let 
  fun relativ_const c args ctxt = case lookup_rel c ls of
     SOME p => let 
             val (vs, ctxt1) = Variable.variant_fixes [""] ctxt
             val v = var_i (hd vs)
             val r_tm = fold (fn t => fn a => a $ t) (pred :: args @ [v]) p
             in (v, r_tm, ctxt1)
             end
   | NONE   => raise TERM ("Constant " ^ c ^ " is not present in the db." , nil)

  fun relativ_app tm (t $ u) args rs' ctxt' = relativ_app tm t (u :: args) rs' ctxt'
  |   relativ_app tm (Const (c, _)) args rs' ctxt' =
        let val (w_ts, rs_ts, ctxt_ts) = relativ_tms pred ls ( args) rs' ctxt'
            val (w_tm, r_tm, ctxt_tm) = relativ_const c w_ts ctxt_ts
        in  (w_tm, update_tm (tm, (w_tm, r_tm)) rs_ts, ctxt_tm)
        end
  |   relativ_app _ t _ _ _ = raise TERM ("Is this possible?",[t])
  
  fun go (Var _) _ _ = raise TERM ("Var: Is this possible?",[])
   | go (Const c) rs ctxt = relativ_app (Const c) (Const c) [] rs ctxt
   | go (t $ u) rs ctxt = relativ_app (t $ u) t [u] rs ctxt
   | go tm rs ctxt = (tm, update_tm (tm,(tm,tm)) rs, ctxt)
   
  in case lookup_tm rs tm  of
      NONE => go tm rs ctxt
    | SOME (w, _) => (w, rs, ctxt)
  end

fun relativ_fm fm pred rel_db (rs,ctxt) = 
  let fun
   relativ_const flag c args = case lookup_rel c rel_db of
     SOME p => let 
             val args' = if flag then args else pred :: args
             in fold (fn t => fn a => a $ t) args' p
             end
   | NONE   => raise TERM ("Constan " ^ c ^ " is not present in the db." , nil)
   
    fun fm_app (p $ t) args = fm_app p (t :: args)
      | fm_app (Const (c,t)) args = 
        let val (w_ts, rs_ts, _) = relativ_tms pred rel_db args rs ctxt
            val news = filter (not o (fn x => is_Free x orelse is_Bound x) o #1) rs_ts
            val (_,ts) = split_list news
            val flag = (Const (c,t)) aconv @{const mem} orelse 
                       (Const (c,t)) aconv @{const IFOL.eq(i)}
            val cnjs = fold conj_ (map #2 ts) (relativ_const flag c w_ts)
        in fold (fn v => fn t => exB pred (incr_boundvars 1 t) v) (map #1 ts) cnjs

        end
      | fm_app tm _ = raise TERM ("fm_app shouldn't handle this case.", [tm])

   fun go (@{const IFOL.conj} $ f $ f') = @{const IFOL.conj} $ go f $ go f'
        | go (@{const IFOL.disj} $ f $ f') = @{const IFOL.disj} $ go f $ go f'
        | go (@{const IFOL.Not} $ f) = @{const IFOL.Not} $ go f
        | go (@{const IFOL.iff} $ f $ f') = @{const IFOL.iff} $ go f $ go f'
        | go (@{const IFOL.imp} $ f $ f') = @{const IFOL.imp} $ go f $ go f'
        | go (@{const IFOL.All(i)} $ f) = @{const rall} $ pred $ go f
        | go (@{const IFOL.Ex(i)} $ f) = @{const rex} $ pred $ go f
        | go (Const c) = fm_app (Const c) []
        | go (p $ t) = fm_app p [t]
        | go (Abs (v,ty,t)) = lambda (Free (v,ty)) (go t)
        | go t = raise TERM ("",[t])
  in  go fm
  end

end;

let 

(*  val f =  @{term "relation({<x,y> . x\<in>A})"}
    val f1 =  @{term "relation({<x,y> \<in> A . True})"}
*)
  val f =  @{term "relation({<x,y>})"}
  val c = @{term "##M"}
  val ls = [ (@{const Pair}, @{const Relative.pair})
           , (@{const zero}, @{const Relative.empty})
           , (@{const succ}, @{const Relative.successor})
           , (@{const Collect}, @{const Relative.is_Collect})
           , (@{const cons}, @{const Relative.is_cons})
           ]
  val rs = [ (@{const relation}, @{const Relative.is_relation})
           , (@{const mem}, @{const mem})
           , (@{const Subset}, @{const Relative.subset})
           ]
  val db = ls @ rs
  open Relativization
  val r_fm = relativ_fm f c db ([], @{context})  

in
(debug f , debug r_fm)
end
\<close>

end
