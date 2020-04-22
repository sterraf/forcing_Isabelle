signature ZF_terms =
  sig
    val add_: term -> term -> term
    val app_: term -> term -> term
    val concat_: term -> term -> term
    val eq_: term -> term -> term
    val freeName: term -> string
    val isFree: term -> bool
    val length_: term -> term
    val list_: term -> term
    val lt_: term -> term -> term
    val mem_: term -> term -> term
    val mk_FinSet: term list -> term
    val mk_Pair: term -> term -> term
    val mk_ZFlist: ('a -> term) -> 'a list -> term
    val mk_ZFnat: int -> term
    val nth_: term -> term -> term
    val subset_: term -> term -> term
    val sum_: term -> term -> term -> term -> term -> term
    val to_ML_list: term -> term list
    val tp: term -> term
    val nat_: term
    val formula_: term
    val fix_vars : thm -> string list -> Proof.context -> thm
    val export_thm : thm -> Proof.context -> Proof.context -> thm
  end

structure ZF_terms : ZF_terms =
struct 
(* Smart constructors for ZF-terms *)

fun mk_Pair t t' = @{const Pair} $ t $ t'

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

fun app_ f x = @{const "apply"} $ f $ x

fun tp x = @{const Trueprop} $ x
fun length_ env = @{const length} $ env
fun nth_ i env = @{const nth} $ i $ env
fun sum_ f g m n p = @{const sum} $ f $ g $ m $ n $ p
fun add_ m n = @{const "add"} $ m $ n
fun mem_ el set = @{const "mem"} $ el $ set
fun eq_ a b = Const (@{const_name IFOL.eq},@{typ "[i, i] \<Rightarrow> o"}) $ a $ b
fun subset_ a b = @{const Subset} $ a $ b
fun lt_ a b = @{const lt} $ a $ b
fun concat_ xs ys = @{const app} $ xs $ ys
fun list_ set = @{const list} $ set 
val nat_ = @{const nat}
val formula_ = @{const formula}

fun fix_vars thm vars ctx = let
  val (_, ctxt1) = Variable.add_fixes vars ctx
  in singleton (Proof_Context.export ctxt1 ctx) thm
end

fun export_thm thm ctx ctx' = 
  singleton (Proof_Context.export ctx ctx') thm

end ;