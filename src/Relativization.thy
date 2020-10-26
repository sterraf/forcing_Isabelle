section\<open>Automatic relativization of terms and formulas.\<close>
text\<open>Relativization of terms and formulas. Relativization of formulas shares relativized terms as
far as possible; assuming that the witnesses for the relativized terms are always unique.\<close>
theory Relativization
  imports "ZF-Constructible.Formula"
    "ZF-Constructible.Relative"
    "ZF-Constructible.Datatype_absolute"
  keywords
    "relativize" :: thy_decl % "ML"
    and
    "relativize_tm" :: thy_decl % "ML"
    and
    "reldb_add" :: thy_decl % "ML"

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
  M_trans.pair_abs
  M_trivial.cartprod_abs
  M_trans.union_abs
  M_trans.inter_abs
  M_trans.setdiff_abs
  M_trans.Union_abs
  M_trivial.cons_abs
  (*M_trans.upair_abs*)
  M_trivial.successor_abs
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
*)
  M_trivial.omega_abs
  M_basic.sum_abs
  M_trivial.Inl_abs
  M_trivial.Inr_abs
  M_basic.converse_abs
  M_basic.vimage_abs
  M_trans.domain_abs
  M_trans.range_abs
  M_basic.field_abs
  M_basic.apply_abs
  (*
  M_trivial.typed_function_abs
  M_basic.injection_abs
  M_basic.surjection_abs
  M_basic.bijection_abs
  *)
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

lemmas datatype_abs =
  M_datatypes.list_N_abs
  M_datatypes.list_abs
  M_datatypes.formula_N_abs
  M_datatypes.formula_abs
  M_eclose.is_eclose_n_abs
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
    val add_constant : string -> string -> Proof.context -> Proof.context
    val db: (term * term) list
    val init_db : (term * term) list -> theory -> theory
    val get_db : Proof.context -> (term * term) list
    val relativ_fm: term -> (term * term) list ->  (term * (term * term)) list * Proof.context * term option -> term -> term * ((term * (term * term)) list * term list * term list * Proof.context)
    val relativ_tm: term option -> term -> (term * term) list ->  (term * (term * term)) list * Proof.context -> term -> term * (term * (term * term)) list * Proof.context
    val read_new_const : Proof.context -> string -> term
    val relativ_tm_frm': term -> (term * term) list -> Proof.context -> term -> term option * term
    val relativize_def: bstring -> string -> Position.T -> Proof.context -> Proof.context
    val relativize_tm: bstring -> string -> Position.T -> Proof.context -> Proof.context
  end

structure Relativization : Relativization = struct
type relset = { db_rels: (term * term) list};

(* relativization db of relation constructors *)
val db =
         [ (@{const relation}, @{const Relative.is_relation})
         , (@{const function}, @{const Relative.is_function})
         , (@{const mem}, @{const mem})
         , (@{const True}, @{const True})
         , (@{const False}, @{const False})
         , (@{const Memrel}, @{const membership})
         , (@{const trancl}, @{const tran_closure})
         , (@{const IFOL.eq(i)}, @{const IFOL.eq(i)})
         , (@{const Subset}, @{const Relative.subset})
         , (@{const quasinat}, @{const Relative.is_quasinat})
         , (@{const apply}, @{const Relative.fun_apply})
         , (@{const Upair}, @{const Relative.upair})
         ]

fun var_i v = Free (v, @{typ i})
fun var_io v = Free (v, @{typ "i \<Rightarrow> o"})
val const_name = #1 o dest_Const

val lookup_tm  = AList.lookup (op aconv)
val update_tm  =  AList.update (op aconv)
val join_tm = AList.join (op aconv) (K #1)

(* instantiated with diferent types than lookup_tm *)
val lookup_rel = AList.lookup (op aconv)

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

fun init_db db = Context.theory_map (Data.put {db_rels = db})

fun get_db thy =
  let
    val db = Data.get (Context.Proof thy)
 in
    #db_rels db
end

val read_const = Proof_Context.read_const {proper = true, strict = true}
val read_new_const = Proof_Context.read_term_pattern

fun add_rel_const thm_name c t ctxt (rs as {db_rels = db}) =
  case lookup_rel db c of
    SOME t' =>
    (warning ("Ignoring duplicate relativization rule" ^
              const_name c ^ " " ^ Syntax.string_of_term ctxt t ^
              "(" ^  Syntax.string_of_term ctxt t' ^ " in " ^ thm_name ^ ")"); rs)
  | NONE => {db_rels = (c, t) :: db}

fun get_consts thm =
  let val (c_rel, rhs) = Thm.concl_of thm |> Utils.dest_trueprop |>
                          Utils.dest_iff_tms |>> head_of
  in case try Utils.dest_eq_tms rhs of
       SOME tm => (c_rel, tm |> #2 |> head_of)
     | NONE => (c_rel, rhs |> Utils.dest_mem_tms |> #2 |> head_of)
  end

fun add_rule ctxt thm rs =
  let val (c_rel,c_abs) = get_consts thm
      val thm_name = Proof_Context.pretty_fact ctxt ("" , [thm]) |> Pretty.string_of
  in add_rel_const thm_name c_abs c_rel ctxt rs
end


fun add_constant rel abs thy =
  let
    val c_abs = read_new_const thy abs
    val c_rel = read_new_const thy rel
    val db_map = Data.map (fn db => {db_rels = (c_rel,c_abs) :: #db_rels db})
    fun add_to_context ctxt' = Context.proof_map db_map ctxt'
    fun add_to_theory ctxt' = Local_Theory.raw_theory (Context.theory_map db_map) ctxt'
  in
    Local_Theory.target (add_to_theory o add_to_context) thy
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

infix 6 &&&
val op &&& = Utils.&&&

infix 6 @@
val op @@ = Utils.@@

infix 6 ---
val op --- = Utils.---

(* Conjunction of a list of terms *)
fun conjs [] = @{term IFOL.True}
  | conjs (fs as _ :: _) = foldr1 (uncurry conj_) fs

(* Produces a relativized existential quantification of the term t *)
fun rex p t (Free v) = @{const rex} $ p $ lambda (Free v) t
  | rex _ t (Bound _) = t
  | rex _ t tm = raise TERM ("rex shouldn't handle this.",[tm,t])

(* Constants that do not take the class predicate *)
val absolute_rels = [ @{const ZF_Base.mem}
                    , @{const IFOL.eq(i)}
                    , @{const Memrel}
                    , @{const True}
                    , @{const False}
                    ]

(* Creates the relational term corresponding to a term of type i. If the last
  argument is (SOME v) then that variable is not bound by an existential
  quantifier.
*)
fun close_rel_tm pred tm tm_var rs =
  let val news = filter (not o (fn x => is_Free x orelse is_Bound x) o #1) rs
      val (vars, tms) = split_list (map #2 news) ||> (curry op @) (the_list tm)
      val vars = case tm_var of
        SOME w => filter (fn v => not (v = w)) vars
      | NONE => vars
  in fold (fn v => fn t => rex pred (incr_boundvars 1 t) v) vars (conjs tms)
  end

fun relativ_tms _ _ _ ctxt' [] = ([], [], ctxt')
  | relativ_tms pred rel_db rs' ctxt' (u :: us) =
      let val (w_u, rs_u, ctxt_u) = relativ_tm NONE pred rel_db (rs', ctxt') u
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
    relativ_tm mv pred rel_db (rs,ctxt) tm =
      let
      (* relativization of a fully applied constant *)
      fun mk_rel_const mv c args abs_args ctxt =
        case lookup_rel rel_db c of
          SOME p =>
            let
              val args' = List.filter (not o Utils.inList (Utils.frees p)) args
              val (v, ctxt1) =
                the_default
                  (Variable.variant_fixes [""] ctxt |>> var_i o hd)
                  (Utils.map_option (I &&& K ctxt) mv)
              val r_tm = list_comb (p, pred :: args' @ abs_args @ [v])
            in
              (v, r_tm, ctxt1)
            end
        | NONE => raise TERM ("Constant " ^ const_name c ^ " is not present in the db." , nil)
      (* relativization of a partially applied constant *)
      fun relativ_app mv mctxt tm abs_args (Const c) args rs =
            let
              val (w_ts, rs_ts, ctxt_ts) = relativ_tms pred rel_db rs (the_default ctxt mctxt) args
              val (w_tm, r_tm, ctxt_tm) = mk_rel_const mv (Const c) w_ts abs_args ctxt_ts
              val rs_ts' = update_tm (tm, (w_tm, r_tm)) rs_ts
            in
              (w_tm, rs_ts', ctxt_tm)
            end
        | relativ_app _ _ _ _ t _ _ =
            raise TERM ("Tried to relativize an application with a non-constant in head position",[t])

      (* relativization of non dependent product and sum *)
      fun relativ_app_no_dep mv tm c t t' rs =
          if loose_bvar1 (t', 0)
          then
            raise TERM("A dependency was found when trying to relativize", [tm])
          else
            relativ_app mv NONE tm [] c [t, incr_boundvars ~1 t'] rs

      fun relativ_replace mv t body after ctxt' =
        let
          val (v, b) = Term.dest_abs body |>> var_i ||> after
          val (b', (rs', ctxt'')) =
            relativ_fm pred rel_db (rs, ctxt', SOME v) b |>> incr_boundvars 1 ||> #1 &&& #4
        in
          relativ_app mv (SOME ctxt'') tm [lambda v b'] @{const Replace} [t] rs'
        end

      fun go _ (Var _) = raise TERM ("Var: Is this possible?",[])
        | go mv (@{const Replace} $ t $ Abs body) = relativ_replace mv t body I ctxt
        (* It is easier to rewrite RepFun as Replace before relativizing,
           since { f(x) . x \<in> t } = { y . x \<in> t, y = f(x) } *)
        | go mv (@{const RepFun} $ t $ Abs body) =
            let
              val (y, ctxt') = Variable.variant_fixes [""] ctxt |>> var_i o hd
            in
              relativ_replace mv t body (lambda y o Utils.eq_ y o incr_boundvars 1) ctxt'
            end
        | go mv (@{const Collect} $ t $ pc) =
            let
              val (pc', (rs', ctxt')) = relativ_fm pred rel_db (rs,ctxt, NONE) pc ||> #1 &&& #4
            in
              relativ_app mv (SOME ctxt') tm [pc'] @{const Collect} [t] rs'
            end
        | go mv (tm as @{const Sigma} $ t $ Abs (_,_,t')) =
            relativ_app_no_dep mv tm @{const Sigma} t t' rs
        | go mv (tm as @{const Pi} $ t $ Abs (_,_,t')) =
            relativ_app_no_dep mv tm @{const Pi} t t' rs
        | go mv (tm as @{const bool_of_o} $ t) =
            let
              val (t', (rs', ctxt')) = relativ_fm pred rel_db (rs, ctxt, NONE) t ||> #1 &&& #4
            in
              relativ_app mv (SOME ctxt') tm [t'] @{const bool_of_o} [] rs'
            end
        | go mv (tm as Const _) = relativ_app mv NONE tm [] tm [] rs
        | go mv (tm as _ $ _) = (strip_comb tm |> uncurry (relativ_app mv NONE tm [])) rs
        | go _ tm = (tm, update_tm (tm,(tm,tm)) rs, ctxt)

      (* we first check if the term has been already relativized as a variable *)
      in case lookup_tm rs tm of
           NONE => go mv tm
         | SOME (w, _) => (w, rs, ctxt)
      end
and
  relativ_fm pred rel_db (rs, ctxt, v) fm =
  let

  (* relativization of a fully applied constant *)
  fun relativ_app (ctxt, rs) c args = case lookup_rel rel_db c of
    SOME p =>
      let (* flag indicates whether the relativized constant is absolute or not. *)
        val flag = not (exists (curry op aconv c) absolute_rels)
        val (args, rs_ts, ctxt') = relativ_tms pred rel_db rs ctxt args
        (* TODO: Verify if next line takes care of locales' definitions *)
        val args' = List.filter (not o Utils.inList (Utils.frees p)) args
        val tm = list_comb (p, if flag then pred :: args' else args')
        (* TODO: Verify if next line is necessary *)
        val news = filter (not o (fn x => is_Free x orelse is_Bound x) o #1) rs_ts
        val (vars, tms) = split_list (map #2 news)
        (* val vars = filter (fn v => not (v = tm)) vars *) (* Verify if this line is necessary *)
       in (tm, (rs_ts, vars, tms, ctxt'))
       end
   | NONE   => raise TERM ("Constant " ^ const_name c ^ " is not present in the db." , nil)

  fun close_fm (f, (rs, vars, tms, ctxt)) =
    let
      fun contains_b0 t = loose_bvar1 (t, 0)

      fun contains_extra_var t =
        case v of
          SOME v => fold_aterms (fn t => fn acc => t = v orelse acc) t false
        | NONE => false

      fun contains_b0_extra t = contains_b0 t orelse contains_extra_var t

      (* t1 $ v \<hookrightarrow> t2 iff v \<in> FV(t2) *)
      fun chained_frees (_ $ v) t2 = Utils.inList (Utils.frees t2) v
        | chained_frees t _ = raise TERM ("Malformed term", [t])

      val tms_to_close = filter contains_b0_extra tms |> Utils.reachable chained_frees tms
      val tms_to_keep = map (incr_boundvars ~1) (tms --- tms_to_close)          
      val vars_to_close = inter (op =) (map (List.last o #2 o strip_comb) tms_to_close) vars
      val vars_to_keep = vars --- vars_to_close
      val new_rs =
        rs
        |> filter (fn (k, (v, rel)) => not (contains_b0_extra k orelse contains_b0_extra v orelse contains_b0_extra rel))
        |> map (fn (k, (v, rel)) => (incr_boundvars ~1 k, (incr_boundvars ~1 v, incr_boundvars ~1 rel)))
    in
      (fold (fn v => fn t => rex pred (incr_boundvars 1 t) v) vars_to_close (conjs (f :: tms_to_close)),
       (new_rs, vars_to_keep, tms_to_keep, ctxt))
    end

  (* Handling of bounded quantifiers. *)
  fun bquant (ctxt, rs) quant conn dom pred =
    let val (v,pred') = Term.dest_abs pred |>> var_i
    in
      go (ctxt, rs) (quant $ lambda v (conn $ (@{const mem} $ v $ dom) $ pred'))
    end
  and
  bind_go (ctxt, rs) const f f' =
    let
      val (r , (rs1, vars1, tms1, ctxt1)) = go (ctxt, rs) f
      val (r', (rs2, vars2, tms2, ctxt2)) = go (ctxt1, rs1) f'
    in
      (const $ r $ r', (rs2, vars1 @@ vars2, tms1 @@ tms2, ctxt2))
    end
  and
      relativ_eq_var (ctxt, rs) v t =
        let
          val (_, rs', ctxt') = relativ_tm (SOME v) pred rel_db (rs, ctxt) t
          val f = lookup_tm rs' t |> #2 o the
          val rs'' = filter (not o (curry (op =) t) o #1) rs'
          val news = filter (not o (fn x => is_Free x orelse is_Bound x) o #1) rs''
          val (vars, tms) = split_list (map #2 news)
        in
          (f, (rs'', vars, tms, ctxt'))
        end
  and
      relativ_eq (ctxt, rs) t1 t2 =
        if (is_Free t1 orelse is_Bound t1) andalso (is_Free t2 orelse is_Bound t2) then
          relativ_app (ctxt, rs) @{const IFOL.eq(i)} [t1, t2]
        else if is_Free t1 orelse is_Bound t1 then
          relativ_eq_var (ctxt, rs) t1 t2
        else if is_Free t2 orelse is_Bound t2 then
          relativ_eq_var (ctxt, rs) t2 t1
        else
          relativ_app (ctxt, rs) @{const IFOL.eq(i)} [t1, t2]
  and
      go (ctxt, rs) (@{const IFOL.conj} $ f $ f') = bind_go (ctxt, rs) @{const IFOL.conj} f f'
    | go (ctxt, rs) (@{const IFOL.disj} $ f $ f') = bind_go (ctxt, rs) @{const IFOL.disj} f f'
    | go (ctxt, rs) (@{const IFOL.Not} $ f) = go (ctxt, rs) f |>> ((curry op $) @{const IFOL.Not})
    | go (ctxt, rs) (@{const IFOL.iff} $ f $ f') = bind_go (ctxt, rs) @{const IFOL.iff} f f'
    | go (ctxt, rs) (@{const IFOL.imp} $ f $ f') = bind_go (ctxt, rs) @{const IFOL.imp} f f'
    | go (ctxt, rs) (@{const IFOL.All(i)} $ f) = go (ctxt, rs) f |>> ((curry op $) (@{const OrdQuant.rall} $ pred))
    | go (ctxt, rs) (@{const IFOL.Ex(i)} $ f) = go (ctxt, rs) f |>> ((curry op $) (@{const OrdQuant.rex} $ pred))
    | go (ctxt, rs) (@{const Bex} $ f $ Abs p) = bquant (ctxt, rs) @{const Ex(i)} @{const IFOL.conj} f p
    | go (ctxt, rs) (@{const Ball} $ f $ Abs p) = bquant (ctxt, rs) @{const All(i)} @{const IFOL.imp} f p
    | go (ctxt, rs) (@{const IFOL.eq(i)} $ t1 $ t2) = relativ_eq (ctxt, rs) t1 t2
    | go (ctxt, rs) (Const c) = relativ_app (ctxt, rs) (Const c) []
    | go (ctxt, rs) (tm as _ $ _) = strip_comb tm |> uncurry (relativ_app (ctxt, rs))
    | go (ctxt, rs) (Abs (v, _, t)) =
      let
        val new_rs = map (fn (k, (v, rel)) => (incr_boundvars 1 k, (incr_boundvars 1 v, incr_boundvars 1 rel))) rs
      in
        go (ctxt, new_rs) t |> close_fm |>> lambda (var_i v)
      end
    | go _ t = raise TERM ("Relativization of formulas cannot handle this case.",[t])
  in
    go (ctxt, rs) fm
  end


fun relativ_tm_frm' cls_pred db ctxt tm =
  let
    fun get_bounds (l as Abs _) = op @@ (strip_abs l |>> map (op #1) ||> get_bounds)
      | get_bounds (t as _$_) = strip_comb t |> op :: |> map get_bounds |> flat
      | get_bounds _ = []

    val ty = fastype_of tm
    val initial_ctxt = fold Utils.add_to_context (get_bounds tm) ctxt
  in
    case ty of
        @{typ i} =>
          let
            val (w, rs, _) =  relativ_tm NONE cls_pred db ([], initial_ctxt) tm
          in
            (SOME w, close_rel_tm cls_pred NONE (SOME w) rs)
          end
      | @{typ o} =>
          let
            fun close_fm (f, (_, vars, tms, _)) =
              fold (fn  v => fn t => rex cls_pred (incr_boundvars 1 t) v) vars (conjs (f :: tms))
          in
            (NONE, relativ_fm cls_pred db ([], initial_ctxt, NONE) tm |> close_fm)
          end
      | ty' => raise TYPE ("We can relativize only terms of types i and o", [ty'], [tm])
  end

fun lname ctxt = Local_Theory.full_name ctxt o Binding.name

fun relativize_def def_name thm_ref pos lthy =
  let
    val ctxt = lthy
    val (vars,tm,ctxt1) = Utils.thm_concl_tm ctxt (thm_ref ^ "_def")
    val ({db_rels = db'}) = Data.get (Context.Proof lthy)
    val tm = tm |> #2 o Utils.dest_eq_tms' o Utils.dest_trueprop
    val (cls_pred, ctxt1) = Variable.variant_fixes ["N"] ctxt1 |>> var_io o hd
    val (v,t) = relativ_tm_frm' cls_pred db' ctxt1 tm
    val t_vars = Term.add_free_names tm []
    val vs' = List.filter (#1 #> #1 #> #1 #> Utils.inList t_vars) vars
    val vs = cls_pred :: map (Thm.term_of o #2) vs' @ the_list v
    val at = List.foldr (uncurry lambda) t vs
    val abs_const = read_const lthy (lname lthy thm_ref)
    fun db_map ctxt' = Data.map (add_rel_const "" abs_const (read_new_const ctxt' def_name) ctxt')
    fun add_to_context ctxt' = Context.proof_map (db_map ctxt') ctxt'
    fun add_to_theory ctxt' = Local_Theory.raw_theory (Context.theory_map (db_map ctxt')) ctxt'
  in
    lthy
    |> Local_Theory.define ((Binding.name def_name, NoSyn), ((Binding.name (def_name ^ "_def"), []), at))
    |>> (#2 #> (fn (s,t) => (s,[t])))
    |> Utils.display "theorem" pos
    |> Local_Theory.target (add_to_theory o add_to_context)
  end

fun relativize_tm def_name term pos lthy =
  let
    val ctxt = lthy
    val (cls_pred, ctxt1) = Variable.variant_fixes ["N"] ctxt |>> var_io o hd
    val tm = Syntax.read_term ctxt1 term
    val ({db_rels = db'}) = Data.get (Context.Proof lthy)
    val vs' = Variable.add_frees ctxt1 tm []
    val ctxt2 = fold Utils.add_to_context (map #1 vs') ctxt1
    val (v,t) = relativ_tm_frm' cls_pred db' ctxt2 tm
    val vs = cls_pred :: map Free vs' @ the_list v
    val at = List.foldr (uncurry lambda) t vs
  in
    lthy
    |> Local_Theory.define ((Binding.name def_name, NoSyn), ((Binding.name (def_name ^ "_def"), []), at))
    |>> (#2 #> (fn (s,t) => (s,[t])))
    |> Utils.display "theorem" pos
  end

end
\<close>

ML\<open>
local
  val relativize_parser =
       Parse.position (Parse.string -- Parse.string);

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>reldb_add\<close> "ML setup for adding relativized/absolute pairs"
       (relativize_parser >> (fn ((rel_term,abs_term),_) =>
          Relativization.add_constant rel_term abs_term))

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
      "declaration of relativization rule") ;
in
end
\<close>
setup\<open>Relativization.init_db Relativization.db \<close>

declare relative_abs[Rel]
(*todo: check all the duplicate cases here.*)
declare datatype_abs[Rel]

end
