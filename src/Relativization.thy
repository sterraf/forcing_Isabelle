section\<open>Automatic relativization of terms.\<close>
theory Relativization
  imports "ZF-Constructible.Formula" 
    "ZF-Constructible.Relative"
    "ZF-Constructible.Datatype_absolute"
  keywords
    "relativize" :: thy_decl % "ML"
    and
    "relativize_tm" :: thy_decl % "ML"

begin
ML_file\<open>Utils.ml\<close>
ML\<open>
structure Absoluteness = Named_Thms
  (val name = @{binding "absolut"}
   val description = "Theorems of absoulte terms and predicates.") 
\<close>
setup\<open>Absoluteness.setup\<close>

lemmas relative_abs = 
  M_trans.empty_abs
  M_trans.upair_abs
  M_trans.pair_abs
  M_trivial.cartprod_abs
  M_trans.union_abs
  M_trans.inter_abs
  M_trans.setdiff_abs
  M_trans.Union_abs
  (*M_trivial.cons_abs*)
  (*M_trivial.successor_abs*)
  M_trans.Collect_abs
  M_trans.Replace_abs
  M_trivial.lambda_abs2
  M_trans.image_abs
(*M_trans.powerset_abs*)
  M_trivial.nat_case_abs
(*
  M_trans.transitive_set_abs
  M_trans.ordinal_abs
  M_trivial.limit_ordinal_abs
  M_trivial.successor_ordinal_abs
  M_trivial.finite_ordinal_abs
  M_trivial.omega_abs
  M_trivial.number1_abs
  M_trivial.number2_abs
  M_trivial.number3_abs
*)
  M_basic.sum_abs
  M_trivial.Inl_abs
  M_trivial.Inr_abs
  M_basic.converse_abs
  M_basic.vimage_abs
  M_trans.domain_abs
  M_trans.range_abs
  M_basic.field_abs
  (*M_trans.relation_abs*)
  (*M_trivial.function_abs*)
  M_basic.apply_abs
  (*M_trivial.typed_function_abs*)
  M_basic.injection_abs
  M_basic.surjection_abs
  M_basic.bijection_abs
  M_basic.composition_abs
  M_trans.restriction_abs
  M_trans.Inter_abs
  M_trivial.is_funspace_abs
  M_trivial.bool_of_o_abs
  M_trivial.not_abs
  M_trivial.and_abs
  M_trivial.or_abs
  M_trivial.Nil_abs
  M_trivial.Cons_abs
  (*M_trivial.quasilist_abs*)
  M_trivial.list_case_abs
  M_trivial.hd_abs
  M_trivial.tl_abs

lemmas datatype_abs = M_basic.iterates_MH_abs
  M_basic.list_functor_abs
  M_trancl.formula_functor_abs
  M_datatypes.list_N_abs
  M_datatypes.mem_list_abs
  M_datatypes.list_abs
  M_datatypes.formula_N_abs
  M_datatypes.mem_formula_abs
  M_datatypes.formula_abs
  M_eclose.is_eclose_n_abs
  M_eclose.mem_eclose_abs
  M_eclose.eclose_abs
  M_datatypes.length_abs
  M_datatypes.nth_abs
  M_trivial.Member_abs
  M_trivial.Equal_abs
  M_trivial.Nand_abs
  M_trivial.Forall_abs
  M_datatypes.depth_abs
  M_datatypes.formula_case_abs

declare relative_abs[absolut]
declare datatype_abs[absolut]

ML\<open>
signature Relativization =
  sig
    structure Data: GENERIC_DATA
    val Rel_add: attribute
    val Rel_del: attribute
    val add_rel_const : string -> term -> term -> Proof.context -> Data.T -> Data.T
    val db: (term * term) list
    val init_db : (term * term) list -> theory -> theory
    val get_db : Proof.context -> (term * term) list
    val relativ_fm: term -> (term * term) list -> (term * (term * term)) list * Proof.context -> term -> term
    val relativ_tm:
       term ->
         (term * term) list ->
           (term * (term * term)) list * Proof.context -> term ->
       term * (term * (term * term)) list * Proof.context
    (*val relativ_tm_frm: term -> (term * term) list -> Proof.context -> term -> term*)
    val read_new_const : string -> Proof.context -> term
    val relativ_tm_frm': term -> (term * term) list -> Proof.context -> term -> term * term
    val relativize_def: bstring -> string -> Position.T -> Proof.context -> Proof.context
    val relativize_tm: bstring -> string -> Position.T -> Proof.context -> Proof.context
  end

structure Relativization : Relativization = struct
type relset = { db_rels: (term * term) list};   (*  *)

  (* relativization db of term constructors *)

  (* relativization db of relation constructors *)
  val db = 
           [ (@{const relation}, @{const Relative.is_relation})
           , (@{const mem}, @{const mem})
           , (@{const Memrel}, @{const membership})
           , (@{const trancl}, @{const tran_closure})
           , (@{const IFOL.eq(i)}, @{const IFOL.eq(i)})
           , (@{const Subset}, @{const Relative.subset})
           , (@{const quasinat}, @{const Relative.is_quasinat})
           , (@{const Upair}, @{const Relative.upair})
           ]

fun var_i v = Free (v, @{typ i})
fun var_io v = Free (v, @{typ "i \<Rightarrow> o"})
val const_name = #1 o dest_Const

val lookup_tm  = AList.lookup (op aconv)
val update_tm  =  AList.update (op aconv)
val join_tm = AList.join (op aconv) (K #1)

(* instantiated with diferent types than lookup_tm *)
val lookup_rel=  AList.lookup (op aconv)

val conj_ = Utils.binop @{const "IFOL.conj"}

(* generic data *)
structure Data = Generic_Data
(
  type T = relset;
  val empty = {db_rels = []}; (* Should we initialize this outside this file? *)
  val extend = I;
  fun merge ({db_rels = db},  {db_rels = db'}) =
     {db_rels = AList.join (op aconv) (K #1) (db', db)};
);

fun init_db db = Context.theory_map (Data.put {db_rels = db })
fun get_db thy = let val db = Data.get (Context.Proof thy)
                 in #db_rels db
                 end


fun read_new_const cname ctxt' = Proof_Context.read_term_pattern ctxt' cname

fun add_rel_const thm_name c t ctxt (rs as {db_rels = db}) =
  case lookup_rel db c of
    SOME t' =>
    (warning ("Ignoring duplicate relativization rule" ^
              const_name c ^ " " ^ Syntax.string_of_term ctxt t ^ 
              "(" ^  Syntax.string_of_term ctxt t' ^ " in " ^ thm_name ^ ")"); rs)
  | NONE => {db_rels = (c, t) :: db};

fun get_consts thm =
  let val (c_rel, rhs) = Thm.concl_of thm |> Utils.dest_trueprop |> Utils.dest_iff_tms |>> head_of
  in case try Utils.dest_eq_tms rhs of
       SOME tm => (c_rel, tm |> #2 |> head_of)
     | NONE => (c_rel, rhs |> Utils.dest_mem_tms |> #2 |> head_of)
  end

fun add_rule ctxt thm rs =
  let val (c_rel,c_abs) = get_consts thm
      val thm_name = Proof_Context.pretty_fact ctxt ("" , [thm]) |> Pretty.string_of
  in add_rel_const thm_name c_abs c_rel ctxt rs
end

fun del_rel_const c (rs as {db_rels = db}) =
  case lookup_rel db c of
    SOME c' =>
    { db_rels = AList.delete (fn (_,b) => b = c) c' db}
  | NONE => (warning ("The constant " ^
              const_name c ^ " doesn't have a relativization rule associated"); rs) ;

fun del_rule thm = del_rel_const (thm |> get_consts |> #2)


val Rel_add =
  Thm.declaration_attribute (fn thm => fn context =>
    Data.map (add_rule (Context.proof_of context) (Thm.trim_context thm)) context);

val Rel_del =
  Thm.declaration_attribute (fn thm => fn context =>
    Data.map (del_rule (Thm.trim_context thm)) context);

(* *)


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
                    , @{const Memrel}
                    ]

(* Creates the relational term corresponding to a term of type i. If the last
  argument is (SOME v) then that variable is not bound by an existential
  quantifier.
*)
fun close_rel_tm pred tm tm_var rs =
  let val news = filter (not o (fn x => is_Free x orelse is_Bound x) o #1) rs
      val (vars, tms) = split_list (map #2 news)
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
      c. the resulting context of created variables.
    *)
    relativ_tm pred rel_db (rs,ctxt) tm =
      let
      (* relativization of a fully applied constant *)
      fun mk_rel_const c args abs_args ctxt =
        case lookup_rel rel_db c of
          SOME p =>
            let val frees = fold_aterms (fn t => if is_Free t then cons t else I) p []
                val args' = List.filter (not o Utils.inList frees) args
                val (v, ctxt1) = Variable.variant_fixes [""] ctxt |>> var_i o hd
                val r_tm = list_comb (p, pred :: args' @ abs_args @ [v])
            in (v, r_tm, ctxt1)
            end
        | NONE => raise TERM ("Constant " ^ const_name c ^ " is not present in the db." , nil)

      (* relativization of a partially applied constant *)
      fun relativ_app tm abs_args (Const c) args =
            let val (w_ts, rs_ts, ctxt_ts) = relativ_tms pred rel_db rs ctxt args
                val (w_tm, r_tm, ctxt_tm) = mk_rel_const (Const c) w_ts abs_args ctxt_ts
                val rs_ts' = update_tm (tm, (w_tm, r_tm)) rs_ts
            in (w_tm, rs_ts', ctxt_tm)
            end
        | relativ_app _ _ t _ =
            raise TERM ("Tried to relativize an application with a non-constant in head position",[t])

      fun go (Var _) = raise TERM ("Var: Is this possible?",[])
        | go (@{const Collect} $ t $ pc) =
            relativ_app tm [pc] @{const Collect} [t]
        | go (tm as Const _) = relativ_app tm [] tm []
        | go (tm as _ $ _) = strip_comb tm |> uncurry (relativ_app tm [])
        | go tm = (tm, update_tm (tm,(tm,tm)) rs, ctxt)

      (* we first check if the term has been already relativized as a variable *)
      in case lookup_tm rs tm of
           NONE => go tm
         | SOME (w, _) => (w, rs, ctxt)
      end

fun relativ_tm_frm' cls_pred db ctxt tm =
      let val (w, rs, _) = relativ_tm cls_pred db ([],ctxt) tm
      in (w, close_rel_tm cls_pred NONE (SOME w) rs)
      end

fun relativ_fm pred rel_db (rs,ctxt) fm =
  let

  (* relativization of a fully applied constant *)
  fun relativ_app c args = case lookup_rel rel_db c of
    SOME p =>
      let (* flag indicates whether the relativized constant is absolute or not. *)
        val flag = not (exists (curry op aconv c) absolute_rels)
        val frees = fold_aterms (fn t => if is_Free t then cons t else I) p []
        val (args, rs_ts, _) = relativ_tms pred rel_db rs ctxt args
        val args' = List.filter (not o Utils.inList frees) args
        val tm = list_comb (p, if flag then pred :: args' else args')
       in close_rel_tm pred (SOME tm) NONE rs_ts
       end
   | NONE   => raise TERM ("Constant " ^ const_name c ^ " is not present in the db." , nil)

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
    | go (Const c) = relativ_app (Const c) []
    | go (tm as _ $ _) = strip_comb tm |> uncurry relativ_app
    | go (Abs body) = body |> Term.dest_abs ||> go |>> var_i |> uncurry lambda
    | go t = raise TERM ("Relativization of formulas cannot handle this case.",[t])
  in go fm
  end

fun read_const cname ctxt' = Proof_Context.read_const {proper = false, strict = false} ctxt' cname

fun relativize_def def_name thm_ref pos lthy =
  let
    val ctxt = lthy
    val (vars,tm,ctxt1) = Utils.thm_concl_tm ctxt (thm_ref ^ "_def")
    val ({db_rels = db'}) = Data.get (Context.Proof lthy)
    val tm = tm |> #2 o Utils.dest_eq_tms' o Utils.dest_trueprop
    val (cls_pred, ctxt1) = Variable.variant_fixes ["N"] ctxt1 |>> var_io o hd
    val (v,t) = relativ_tm_frm' cls_pred db' ctxt1 tm
    val t_vars = Term.add_free_names t []
    val vs' = List.filter (#1 #> #1 #> #1 #> Utils.inList t_vars) vars
    val vs = cls_pred :: map (Thm.term_of o #2) vs'
    val at = List.foldr (uncurry lambda) t (vs @ [v])
    fun lname ctxt = Local_Theory.full_name ctxt o Binding.name
    val abs_const = read_const (lname lthy thm_ref) lthy
in
   lthy |>
   Local_Theory.define ((Binding.name def_name, NoSyn),
                         ((Binding.name (def_name ^ "_def"), []), at)) |>>
   (#2 #> (fn (s,t) => (s,[t]))) |> Utils.display "theorem" pos |>
   Local_Theory.target (
       fn ctxt' => Context.proof_map
        (Data.map (add_rel_const "" abs_const (read_new_const def_name ctxt') ctxt')) ctxt')
  end

fun relativize_tm def_name term pos lthy =
  let
    val ctxt = lthy
    val (cls_pred, ctxt1) = Variable.variant_fixes ["N"] ctxt |>> var_io o hd
    val tm = Syntax.read_term ctxt1 term
    val ({db_rels = db'}) = Data.get (Context.Proof lthy)
    val (v,t) = relativ_tm_frm' cls_pred db' ctxt1 tm
    val vs' = Term.add_frees t []
    val vs = cls_pred :: map Free vs'
    val at = List.foldr (uncurry lambda) t (vs @ [v])
in
   lthy |>
    Local_Theory.define ((Binding.name def_name, NoSyn),
                        ((Binding.name (def_name ^ "_def"), []), at)) |>>
  (#2 #> (fn (s,t) => (s,[t]))) |> Utils.display "theorem" pos
  end


end
\<close>

ML\<open>
local
  val relativize_parser =
       Parse.position (Parse.string -- Parse.string);

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>relativize\<close> "ML setup for relativizing definitions"
       (relativize_parser >> (fn ((bndg,thm),pos) =>
          Relativization.relativize_def thm bndg pos))

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>relativize_tm\<close> "ML setup for relativizing definitions"
       (relativize_parser >> (fn ((bndg,term),pos) =>
          Relativization.relativize_tm term bndg pos))
val _ =
  Theory.setup
   (Attrib.setup \<^binding>\<open>Rel\<close> (Attrib.add_del Relativization.Rel_add Relativization.Rel_del)
      "declaration of type-checking rule") ;
in
end
\<close>
setup\<open>Relativization.init_db Relativization.db \<close>

declare relative_abs[Rel]
(*todo: check all the duplicate cases here.*)
(*declare datatype_abs[Rel]*)


end