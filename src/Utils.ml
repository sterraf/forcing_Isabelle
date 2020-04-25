signature Utils =
 sig
    val $$ : term -> term -> term -> term
    val add_: term -> term -> term
    val app_: term -> term -> term
    val concat_: term -> term -> term
    val dest_apply_op: term -> term
    val dest_iff_lhs: term -> term
    val dest_iff_rhs: term -> term
    val dest_satisfies_frm: term -> term
    val dest_eq_tms: term -> term * term
    val dest_sats_frm: term -> term
    val dest_tp_iff_rhs: term -> term
    val dest_trueprop: term -> term
    val eq_: term -> term -> term
    val export_thm: thm -> Proof.context -> Proof.context -> thm
    val fix_vars: thm -> string list -> Proof.context -> thm
    val formula_: term
    val freeName: term -> string
    val inList: ''a -> ''a list -> bool
    val isFree: term -> bool
    val length_: term -> term
    val list_: term -> term
    val lt_: term -> term -> term
    val mem_: term -> term -> term
    val mk_FinSet: term list -> term
    val mk_Pair: term -> term -> term
    val mk_ZFlist: ('a -> term) -> 'a list -> term
    val mk_ZFnat: int -> term
    val nat_: term
    val nth_: term -> term -> term
    val subset_: term -> term -> term
    val to_ML_list: term -> term list
    val tp: term -> term
  end

structure Utils : Utils =
struct 
(* Smart constructors for ZF-terms *)

fun inList a = exists (fn b => a = b)

fun $$ h t u = h $ t $ u
val mk_Pair  = $$ @{const Pair}

fun mk_FinSet nil = @{const zero}
  | mk_FinSet (e :: es) = @{const cons} $ e $ mk_FinSet es

fun mk_ZFnat 0 = @{const zero}
  | mk_ZFnat n = @{const succ} $ mk_ZFnat (n-1)

fun mk_ZFlist _ nil = @{const "Nil"}
  | mk_ZFlist f (t :: ts) = @{const "Cons"} $ f t $ mk_ZFlist f ts

fun to_ML_list (@{const Nil}) = nil
  | to_ML_list (@{const Cons} $ t $ ts) = t :: to_ML_list ts
|   to_ML_list _ = nil

fun isFree (Free (_,_)) = true
  | isFree _ = false

fun freeName (Free (n,_)) = n
  | freeName _ = error "Not a free variable"

val app_ = $$ @{const apply}

fun tp x = @{const Trueprop} $ x
fun length_ env = @{const length} $ env
val nth_ = $$ @{const nth}
val add_ = $$ @{const add}
val mem_ = $$ @{const mem}
val subset_ = $$ @{const Subset}
val lt_ = $$ @{const lt}
val concat_ = $$ @{const app}
val eq_ = $$ @{const IFOL.eq(i)}

(* Abbreviation for sets *)
fun list_ set = @{const list} $ set 
val nat_ = @{const nat}
val formula_ = @{const formula}

(** Destructors of terms **)
fun dest_eq_tms (Const (@{const_name IFOL.eq},_) $ t $ u) = (t, u)
  | dest_eq_tms t = raise TERM ("dest_eq_tms", [t])

fun dest_apply_op (@{const apply} $ t $ _) = t
  | dest_apply_op t = raise TERM ("dest_applies_op", [t])

fun dest_satisfies_frm (@{const Formula.satisfies} $ _ $ f) = f
  | dest_satisfies_frm t = raise TERM ("dest_satisfies_frm", [t]);

val dest_sats_frm = dest_satisfies_frm o dest_apply_op o #1 o dest_eq_tms ;

fun dest_trueprop (@{const IFOL.Trueprop} $ t) = t
  | dest_trueprop t = raise TERM ("dest_trueprop", [t])

fun dest_iff_tms (@{const IFOL.iff} $ t $ u) = (t, u)
  | dest_iff_tms t = raise TERM ("dest_iff_rhs", [t])

val dest_iff_lhs = #1 o dest_iff_tms
val dest_iff_rhs = #2 o dest_iff_tms

(* Given a term of the form "P \<longleftrightarrow> sats(M,env,f)" returns f *)
val dest_tp_iff_rhs = dest_sats_frm o dest_iff_rhs o dest_trueprop

fun fix_vars thm vars ctx = let
  val (_, ctxt1) = Variable.add_fixes vars ctx
  in singleton (Proof_Context.export ctxt1 ctx) thm
end

fun export_thm thm ctx ctx' = 
  singleton (Proof_Context.export ctx ctx') thm

end ;