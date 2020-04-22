section\<open>Automatic relativization of terms.\<close>
theory Relativization
  imports "ZF-Constructible.Formula"  "ZF-Constructible.Relative"

begin
ML_file\<open>ZF_terms.ml\<close>

ML\<open>
structure Relativization  = struct

fun var_i v = Free (v, @{typ i})
fun lookup f = AList.lookup (fn (x, y) => x = f y)
val lookup_tm  = AList.lookup (op aconv)
fun lookup_rel c ls =  lookup (#1 o dest_Const) ls c


(* 
Relativization of the term tm with respect of the predicate pred. The already relativized constants
are given in the list ls; the argument rs is the list of terms already relativized and ctxt is used
to generate fresh names.
*)

fun relativ_tm tm pred ls (rs,ctxt) = 
  let 
  fun relativ_const c args ctxt = case lookup_rel c ls of
     SOME p => let 
             val ([v], ctxt1) = Variable.variant_fixes [""] ctxt
             val r_tm = fold (fn t => fn a => a $ t) (pred :: args @ [var_i v]) p
             in (v, r_tm, ctxt1)
             end
   | NONE   => raise TERM ("Constant " ^ c ^ " is not present in the db." , nil)

  fun apply [] _ ctxt' = ([], [], ctxt')
   |  apply (u :: us) rs' ctxt' = 
           let val (w_u, rs_u, ctxt_u) = relativ_tm u pred ls (rs', ctxt')
               val (w_us, rs_us, ctxt_us) = apply us rs_u ctxt_u
          in (var_i w_u :: w_us, rs_u @ rs_us, ctxt_us)
          end
  fun relativ_app tm (t $ u) args rs' ctxt' = relativ_app tm t (u :: args) rs' ctxt'
  |   relativ_app tm (Const (c, _)) args rs' ctxt' =
        let val (w_ts, rs_ts, ctxt_ts) = apply (rev args) rs' ctxt'
            val (w_tm, r_tm, ctxt_tm) = relativ_const c w_ts ctxt_ts
        in (w_tm, AList.update (op aconv) (tm, (w_tm, r_tm)) rs_ts, ctxt_tm)
        end
  |   relativ_app _ t _ _ _ = raise TERM ("Is this possible?",[t])
  
  fun go (Var _) _ _ = raise TERM ("Var: Is this possible?",[])
    | go (Bound _) _ _ = raise TERM ("Bound: Is this possible?",[])
    | go (Abs _) _ _ = raise TERM ("Bound: Is this possible?",[])
    | go (Free v) rs ctxt = 
        let val vs = v |> #1 
        in (vs, AList.update (op aconv) (Free v,(vs,Free v)) rs, ctxt)
        end
   | go (Const c) rs ctxt = relativ_app (Const c) (Const c) [] rs ctxt
   | go (t $ u) rs ctxt = relativ_app (t $ u) t [u] rs ctxt
   
  in case lookup_tm rs tm  of
      NONE => go tm rs ctxt
    | SOME (w, _) => (w, rs, ctxt)
end
end;

let 
  val t = @{const zero}
  fun p t = (@{const Pair}) $ t $ t
  fun cr f g (a,b) = (f a, g b)
  val t' = p (p (@{const succ} $ t))
  val c = @{term "##M"}
  open Relativization
  val r = relativ_tm t' c 
              [ (@{const Pair}, @{const Relative.pair})
              , (@{const zero}, @{const Relative.empty})
              , (@{const succ}, @{const Relative.successor})
              ] ([], @{context})
in
  ( Syntax.pretty_term @{context} t' , 
    r |> #2 |> map (cr (Syntax.pretty_term @{context}) (cr (fn i => i) (Syntax.pretty_term @{context}))))
end
\<close>

end
