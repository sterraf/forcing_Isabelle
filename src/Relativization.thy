section\<open>Automatic relativization of terms.\<close>
theory Relativization
  imports "ZF-Constructible.Formula"  "ZF-Constructible.Relative"

begin
ML_file\<open>ZF_terms.ml\<close>

ML\<open>
structure Relativization  = struct

fun var_i v = Free (v, @{typ i})
fun const_name (Const (c,_)) = c
fun lookup f = AList.lookup (fn (x, y) => x = f y)
val lookup_tm  = AList.lookup (op aconv)
fun lookup_rel c ls =  lookup const_name ls c
fun conj_ t u = @{const IFOL.conj} $ t $ u
fun exB p t v = @{const rex} $ p $ lambda v t
fun debug t = writeln (Pretty.string_of (Syntax.pretty_term @{context} t))
(*
Relativization of the term tm with respect of the predicate pred. The already relativized constants
are given in the list ls; the argument rs is the list of terms already relativized and ctxt is used
to generate fresh names.
*)
fun relativ_tms pred ls [] _ ctxt' = ([], [], ctxt') 
 |  relativ_tms pred ls (u :: us) rs' ctxt' = 
           let val (w_u, rs_u, ctxt_u) = relativ_tm u pred ls (rs', ctxt')
               val (w_us, rs_us, ctxt_us) = relativ_tms pred ls us rs_u ctxt_u
          in debug w_u ; (w_u :: w_us, rs_u , ctxt_us)
          end
and 
  relativ_tm tm pred ls (rs,ctxt) = 
  let 
  fun relativ_const c args ctxt = case lookup_rel c ls of
     SOME p => let 
             val ([v], ctxt1) = Variable.variant_fixes [""] ctxt
             val r_tm = fold (fn t => fn a => a $ t) (pred :: args @ [var_i v]) p
             in debug (Const (c,@{typ i})) ; (var_i v, r_tm, ctxt1)
             end
   | NONE   => raise TERM ("Constant " ^ c ^ " is not present in the db." , nil)

  fun relativ_app tm (t $ u) args rs' ctxt' = relativ_app tm t (u :: args) rs' ctxt'
  |   relativ_app tm (Const (c, _)) args rs' ctxt' =
        let val (w_ts, rs_ts, ctxt_ts) = relativ_tms pred ls (rev args) rs' ctxt'
            val (w_tm, r_tm, ctxt_tm) = relativ_const c w_ts ctxt_ts
        in  (w_tm, AList.update (op aconv) (tm, (w_tm, r_tm)) rs_ts, ctxt_tm)
        end
  |   relativ_app _ t _ _ _ = raise TERM ("Is this possible?",[t])
  
  fun go (Var _) _ _ = raise TERM ("Var: Is this possible?",[])
   | go (Abs _) _ _ = raise TERM ("Bound: Is this possible?",[])
   | go (Const c) rs ctxt = relativ_app (Const c) (Const c) [] rs ctxt
   | go (t $ u) rs ctxt = relativ_app (t $ u) t [u] rs ctxt
   | go tm rs ctxt = (tm, AList.update (op aconv) (tm,(tm,tm)) rs, ctxt)
   
  in case lookup_tm rs tm  of
      NONE => go tm rs ctxt
    | SOME (w, _) => (w, rs, ctxt)
  end

fun relativ_fm fm pred rel_db (rs,ctxt) = 
  let fun
   relativ_const flag c args ctxt = case lookup_rel c rel_db of
     SOME p => let 
             val args' = if flag then args else pred :: args
             val r_tm = fold (fn t => fn a => a $ t) args' p
             in r_tm
             end
   | NONE   => raise TERM ("Constan " ^ c ^ " is not present in the db." , nil)
   
    fun fm_app (p $ t) args = fm_app p (t :: args)
      | fm_app (Const (c,t)) args = 
        let val (w_ts, rs_ts, ctxt_ts) = relativ_tms pred rel_db (rev args) rs ctxt
            val news = filter (not o is_Free o #1) rs_ts
            val (vs,ts) = split_list news
            val flag = (Const (c,t)) aconv @{const mem} orelse 
                       (Const (c,t)) aconv @{const IFOL.eq(i)}
            val cnjs = fold conj_ (map #2 ts) (relativ_const flag c w_ts ctxt)
        in fold (fn v => fn t => exB pred (incr_boundvars 1 t) v) (map #1 ts) cnjs
        end
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
  in  go fm
  end

end;

let 
  val t = @{const zero}
  fun p t = (@{const Pair}) $ t $ t
  fun cr f g (a,b) = (f a, g b)
  val f =  @{term "(\<forall> x. x\<in>y) \<and> (\<forall> y . relation(<y,x>))"}
  val t' = p t (* @{term "{<x,y> . x \<in> A}"}  p (p (@{const succ} $ t)) *)
  val c = @{term "##M"}
  val ls = [ (@{const Pair}, @{const Relative.pair})
           , (@{const zero}, @{const Relative.empty})
           , (@{const succ}, @{const Relative.successor})
           ]
  val rs = [ (@{const relation}, @{const Relative.is_relation})
           , (@{const mem}, @{const mem})
           ]
  val db = ls @ rs
  open Relativization
  val r_tm = relativ_tm t' c ls ([], @{context})
   val r_fm = relativ_fm f c (rs @ ls) ([], @{context})  
  val test_tm = ( Syntax.pretty_term @{context}  t' , 
    r_tm |> #2 |> map (cr (Syntax.pretty_term @{context}) (cr (fn i => i) (Syntax.pretty_term @{context}))))

in
( debug f , debug r_fm)
end
\<close>

end
