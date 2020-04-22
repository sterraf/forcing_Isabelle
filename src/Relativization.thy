section\<open>Automatic relativization of terms.\<close>
theory Relativization
  imports "ZF-Constructible.Formula"  "ZF-Constructible.Relative"

begin
ML_file\<open>ZF_terms.ml\<close>

ML\<open>
signature Relativization =  sig
  val relativ_tm : term -> term -> (term * term) list -> 
                   (string * term) list -> Proof.context -> 
                   (string * (string * term) list * Proof.context)
  val relativ_const : term -> (term * term) list -> string ->
                       term list -> (string * term) list ->
                       Proof.context -> 
                       (string * (string * term) list * Proof.context)
end
structure Relativization : Relativization = struct

fun var_i v = Free (v, @{typ i})
fun lookup f = AList.lookup (fn (x, y) => x = f y)
fun lookup_rel c ls =  lookup (#1 o dest_Const) ls c


fun relativ_const pred ls c rs ctx' ctxt = case lookup_rel c ls of
     SOME p => let 
             val ([v], ctxt1) = Variable.variant_fixes [""] ctxt
             val r_tm = fold (fn t => fn a => a $ t) (pred :: rs @ [var_i v]) p
             in (v, AList.update (fn (w,w') => w = w')  (v, r_tm) ctx', ctxt1)
             end
   | NONE   => raise TERM ("Constant " ^ c ^ " is not present in the db." , nil)


(* 
Relativization of the term tm with respect of the predicate pred. The already relativized constants
are given in the list ls; the argument rs is the list of terms already relativized and ctxt is used
to generate fresh names.
*)
fun relativ_tm tm pred ls rs ctxt =
  case tm of
      Var _ => raise TERM ("Var: Is this possible?",[])
    | Bound _ => raise TERM ("Bound: Is this possible?",[])
    | Abs _ => raise TERM ("Bound: Is this possible?",[])
    | Free v => let val vs = v |> #1 
                in (vs, AList.update (fn (w,w') => w = w')  (vs, Free v) rs, ctxt)
                end
   | Const (c, _) $ t $ u => 
        let val (w_t, rs_t, ctxt_t) = relativ_tm t pred ls rs ctxt
            val (w_u, rs_u, ctxt_u) = relativ_tm u pred ls rs_t ctxt_t
        in relativ_const pred ls c (var_i w_t :: var_i w_u :: []) rs_u ctxt_u
        end
   | Const (c, _) => relativ_const pred ls c [] rs ctxt
   | _ $ _ => raise TERM ("App: Is this possible?",[])

end
;
let 
  val t = @{const zero}
  fun p t = (@{const Pair}) $ t $ @{term "v"}
  val t' = p (p t)
  val c = @{term "##M"}
  open Relativization
  val r = relativ_tm t' c 
              [ (@{const Pair}, @{const Relative.pair})
              , (@{const zero}, @{const Relative.empty})  
              ] [] @{context}
in
  ( Syntax.pretty_term @{context} t' , 
    r |> #2 |> map (fn s => s |> #2 |> Syntax.pretty_term @{context}))
end
\<close>

end
