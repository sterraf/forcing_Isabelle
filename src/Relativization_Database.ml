signature Database =
  sig
    type db
    val empty : db
    type mode
    val abs2is : mode
    val abs2rel : mode
    val rel2is : mode
    val lookup : mode -> term -> db -> term option
    val insert : mode -> term * term -> db -> db
    val remove : mode -> term -> db -> db
    val merge : db * db -> db

    (* INVARIANTS *)
    (* \<forall> db : db, \<forall> t, t' : term, \<forall> m : mode, lookup m t db = lookup m t' db \<noteq> NONE \<Longrightarrow> t = t' *)
    (* \<forall> db : db, \<forall> t, u, v : term, lookup abs2rel t db = SOME v \<and> lookup rel2is v db = SOME u \<Longrightarrow> lookup abs2is t db = SOME u *)
    (* \<forall> db : db, \<forall> t, u, v : term, lookup abs2is t db = SOME u \<and> lookup rel2is v db = SOME u \<Longrightarrow> lookup abs2rel t db = SOME v *)
    (* \<forall> db : db, \<forall> t, u, v : term, lookup abs2rel t db = SOME u \<and> lookup abs2is t db = SOME v \<Longrightarrow> lookup rel2is u db = SOME v *)
  end

structure Database : Database = struct
  type db = { ar : (term * term) list
            , af : (term * term) list
            , fr : (term * term) list
            }

  val empty = { ar = []
              , af = []
              , fr = []
              }

  datatype singlemode = Absolute | Relational | Functional

  type mode = singlemode * singlemode

  val abs2is = (Absolute, Relational)

  val abs2rel = (Absolute, Functional)

  val rel2is = (Functional, Relational)

  infix 6 &&&
  val op &&& = Utils.&&&

  infix 5 |||
  fun op ||| (x, y) = fn t =>
    case x t of
      SOME a => SOME a
    | NONE => y t

  infix 5 >>=
  fun op >>= (m, f) =
    case m of
      SOME x => f x
    | NONE => NONE

  infix 6 COMP
  fun op COMP (xs, ys) = fn t => AList.lookup (op aconv) ys t >>= AList.lookup (op aconv) xs

  val transpose = map (#2 &&& #1)

  fun lookup (Absolute, Relational) t db = (#fr db COMP #af db ||| AList.lookup (op aconv) (#ar db)) t
    | lookup (Absolute, Functional) t db = AList.lookup (op aconv) (#af db) t
    | lookup (Functional, Relational) t db = AList.lookup (op aconv) (#fr db) t
    | lookup (Relational, Absolute) t db = (transpose (#af db) COMP transpose (#fr db) ||| AList.lookup (op aconv) (transpose (#ar db))) t
    | lookup (Functional, Absolute) t db = AList.lookup (op aconv) (transpose (#af db)) t
    | lookup (Relational, Functional) t db = AList.lookup (op aconv) (transpose (#fr db)) t
    | lookup _ _ _ = error "lookup: unreachable clause"

  fun insert (mode as (Absolute, Relational)) (t, u) db =
      (case lookup mode t db of
        SOME _ => (warning ("duplicate entry for " ^ (@{make_string} t)); db)
      | NONE => case lookup (Relational, Functional) u db of
                  SOME v => if is_none (lookup (Relational, Absolute) v db)
                              then { ar = #ar db
                                   , af = AList.update (op aconv) (t, v) (#af db)
                                   , fr = #fr db
                                   }
                              else error "invariant violation, insert abs2is"
                | NONE => { ar = AList.update (op aconv) (t, u) (#ar db)
                          , af = #af db
                          , fr = #fr db
                          }
      )
    | insert (mode as (Absolute, Functional)) (t, u) db =
      (case lookup mode t db of
        SOME _ => (warning ("duplicate entry for " ^ (@{make_string} t)); db)
      | NONE => case (transpose (#ar db) COMP #fr db) u of
                  SOME v => if v = t
                              then { ar = AList.delete (op aconv) t (#ar db)
                                   , af = AList.update (op aconv) (t, u) (#af db)
                                   , fr = #fr db
                                   }
                              else error "invariant violation, insert abs2rel "
                | NONE => { ar = #ar db
                          , af = AList.update (op aconv) (t, u) (#af db)
                          , fr = #fr db
                          }
      )
    | insert (mode as (Functional, Relational)) (t, u) db =
      (case lookup mode t db of
        SOME _ => (warning ("duplicate entry for " ^ (@{make_string} t)); db)
      | NONE => case (lookup (Functional, Absolute) t db, lookup (Relational, Absolute) u db) of
                  (SOME v, SOME v') => if v = v'
                                         then { ar = AList.delete (op aconv) v (#ar db)
                                              , af = #af db
                                              , fr = AList.update (op aconv) (t, u) (#fr db)
                                              }
                                         else error "invariant violation, insert rel2is"
                | (SOME _, NONE) => { ar = #ar db
                                    , af = #af db
                                    , fr = AList.update (op aconv) (t, u) (#fr db)
                                    }
                | (NONE, SOME v') => { ar = AList.delete (op aconv) v' (#ar db)
                                     , af = AList.update (op aconv) (v', t) (#af db)
                                     , fr = AList.update (op aconv) (t, u) (#fr db)
                                     }
                | (NONE, NONE) => { ar = #ar db
                                  , af = #af db
                                  , fr = AList.update (op aconv) (t, u) (#fr db)
                                  }
      )
    | insert _ _ _ = error "insert: unreachable clause"

  fun remove (Absolute, Relational) t db = { ar = AList.delete (op aconv) t (#ar db)
                                           , af = AList.delete (op aconv) t (#af db)
                                           , fr = #fr db
                                           }
    | remove (Absolute, Functional) t db = { ar = AList.delete (op aconv) t (#ar db)
                                           , af = AList.delete (op aconv) t (#af db)
                                           , fr = #fr db
                                           }
    | remove (mode as (Functional, Relational)) t db =
      (case lookup mode t db of
        SOME u => if is_none (lookup (Relational, Absolute) u db)
                    then { ar = #ar db
                         , af = #af db
                         , fr = AList.delete (op aconv) t (#fr db)
                         }
                    else error "invariant violation, remove rel2is"
      | NONE => db
      )
    | remove _ _ _ = error "remove: unreachable clause"

    fun merge (db, db') = { ar = AList.join (op aconv) (K #1) (#ar db, #ar db')
                          , af = AList.join (op aconv) (K #1) (#af db, #af db')
                          , fr = AList.join (op aconv) (K #1) (#fr db, #fr db')
                          }
end (* structure Database : Database *)