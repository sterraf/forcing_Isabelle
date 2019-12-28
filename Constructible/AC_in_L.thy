(*  Title:      ZF/Constructible/AC_in_L.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>The Axiom of Choice Holds in L!\<close>

theory AC_in_L imports Formula Separation begin

subsection\<open>Extending a Wellordering over a List -- Lexicographic Power\<close>

text\<open>This could be moved into a library.\<close>

consts
  rlist   :: "[i,i]=>i"

inductive
  domains "rlist(A,r)" \<subseteq> "list(A) * list(A)"
  intros
    shorterI:
      "[| length(l') < length(l); l' \<in> list(A); l \<in> list(A) |]
       ==> <l', l> \<in> rlist(A,r)"

    sameI:
      "[| <l',l> \<in> rlist(A,r); a \<in> A |]
       ==> <Cons(a,l'), Cons(a,l)> \<in> rlist(A,r)"

    diffI:
      "[| length(l') = length(l); <a',a> \<in> r;
          l' \<in> list(A); l \<in> list(A); a' \<in> A; a \<in> A |]
       ==> <Cons(a',l'), Cons(a,l)> \<in> rlist(A,r)"
  type_intros list.intros


subsubsection\<open>Type checking\<close>

lemmas rlist_type = rlist.dom_subset

lemmas field_rlist = rlist_type [THEN field_rel_subset]

subsubsection\<open>Linearity\<close>

lemma rlist_Nil_Cons [intro]:
    "[|a \<in> A; l \<in> list(A)|] ==> <[], Cons(a,l)> \<in> rlist(A, r)"
by (simp add: shorterI)

lemma linear_rlist:
  assumes r: "linear(A,r)" shows "linear(list(A),rlist(A,r))"
proof -
  { fix xs ys
    have "xs \<in> list(A) \<Longrightarrow> ys \<in> list(A) \<Longrightarrow> \<langle>xs,ys\<rangle> \<in> rlist(A,r) \<or> xs = ys \<or> \<langle>ys,xs\<rangle> \<in> rlist(A, r) "
    proof (induct xs arbitrary: ys rule: list.induct)
      case Nil 
      thus ?case by (induct ys rule: list.induct) (auto simp add: shorterI)
    next
      case (Cons x xs)
      { fix y ys
        assume "y \<in> A" and "ys \<in> list(A)"
        with Cons
        have "\<langle>Cons(x,xs),Cons(y,ys)\<rangle> \<in> rlist(A,r) \<or> x=y & xs = ys \<or> \<langle>Cons(y,ys), Cons(x,xs)\<rangle> \<in> rlist(A,r)" 
          apply (rule_tac i = "length(xs)" and j = "length(ys)" in Ord_linear_lt)
          apply (simp_all add: shorterI)
          apply (rule linearE [OF r, of x y]) 
          apply (auto simp add: diffI intro: sameI) 
          done
      }
      note yConsCase = this
      show ?case using \<open>ys \<in> list(A)\<close>
        by (cases rule: list.cases) (simp_all add: Cons rlist_Nil_Cons yConsCase) 
    qed
  }
  thus ?thesis by (simp add: linear_def) 
qed


subsubsection\<open>Well-foundedness\<close>

text\<open>Nothing preceeds Nil in this ordering.\<close>
inductive_cases rlist_NilE: " <l,[]> \<in> rlist(A,r)"

inductive_cases rlist_ConsE: " <l', Cons(x,l)> \<in> rlist(A,r)"

lemma not_rlist_Nil [simp]: " <l,[]> \<notin> rlist(A,r)"
by (blast intro: elim: rlist_NilE)

lemma rlist_imp_length_le: "<l',l> \<in> rlist(A,r) ==> length(l') \<le> length(l)"
apply (erule rlist.induct)
apply (simp_all add: leI)
done

lemma wf_on_rlist_n:
  "[| n \<in> nat; wf[A](r) |] ==> wf[{l \<in> list(A). length(l) = n}](rlist(A,r))"
apply (induct_tac n)
 apply (rule wf_onI2, simp)
apply (rule wf_onI2, clarify)
apply (erule_tac a=y in list.cases, clarify)
 apply (simp (no_asm_use))
apply clarify
apply (simp (no_asm_use))
apply (subgoal_tac "\<forall>l2 \<in> list(A). length(l2) = x \<longrightarrow> Cons(a,l2) \<in> B", blast)
apply (erule_tac a=a in wf_on_induct, assumption)
apply (rule ballI)
apply (rule impI)
apply (erule_tac a=l2 in wf_on_induct, blast, clarify)
apply (rename_tac a' l2 l')
apply (drule_tac x="Cons(a',l')" in bspec, typecheck)
apply simp
apply (erule mp, clarify)
apply (erule rlist_ConsE, auto)
done

lemma list_eq_UN_length: "list(A) = (\<Union>n\<in>nat. {l \<in> list(A). length(l) = n})"
by (blast intro: length_type)


lemma wf_on_rlist: "wf[A](r) ==> wf[list(A)](rlist(A,r))"
apply (subst list_eq_UN_length)
apply (rule wf_on_Union)
  apply (rule wf_imp_wf_on [OF wf_Memrel [of nat]])
 apply (simp add: wf_on_rlist_n)
apply (frule rlist_type [THEN subsetD])
apply (simp add: length_type)
apply (drule rlist_imp_length_le)
apply (erule leE)
apply (simp_all add: lt_def)
done


lemma wf_rlist: "wf(r) ==> wf(rlist(field(r),r))"
apply (simp add: wf_iff_wf_on_field)
apply (rule wf_on_subset_A [OF _ field_rlist])
apply (blast intro: wf_on_rlist)
done

lemma well_ord_rlist:
     "well_ord(A,r) ==> well_ord(list(A), rlist(A,r))"
apply (rule well_ordI)
apply (simp add: well_ord_def wf_on_rlist)
apply (simp add: well_ord_def tot_ord_def linear_rlist)
done


subsection\<open>An Injection from Formulas into the Natural Numbers\<close>

text\<open>There is a well-known bijection between \<^term>\<open>nat*nat\<close> and \<^term>\<open>nat\<close> given by the expression f(m,n) = triangle(m+n) + m, where triangle(k)
enumerates the triangular numbers and can be defined by triangle(0)=0,
triangle(succ(k)) = succ(k + triangle(k)).  Some small amount of effort is
needed to show that f is a bijection.  We already know that such a bijection exists by the theorem \<open>well_ord_InfCard_square_eq\<close>:
@{thm[display] well_ord_InfCard_square_eq[no_vars]}

However, this result merely states that there is a bijection between the two
sets.  It provides no means of naming a specific bijection.  Therefore, we
conduct the proofs under the assumption that a bijection exists.  The simplest
way to organize this is to use a locale.\<close>

text\<open>Locale for any arbitrary injection between \<^term>\<open>nat*nat\<close>
      and \<^term>\<open>nat\<close>\<close>
locale Nat_Times_Nat =
  fixes fn
  assumes fn_inj: "fn \<in> inj(nat*nat, nat)"


consts   enum :: "[i,i]=>i"
primrec
  "enum(f, Member(x,y)) = f ` <0, f ` <x,y>>"
  "enum(f, Equal(x,y)) = f ` <1, f ` <x,y>>"
  "enum(f, Nand(p,q)) = f ` <2, f ` <enum(f,p), enum(f,q)>>"
  "enum(f, Forall(p)) = f ` <succ(2), enum(f,p)>"

lemma (in Nat_Times_Nat) fn_type [TC,simp]:
    "[|x \<in> nat; y \<in> nat|] ==> fn`<x,y> \<in> nat"
by (blast intro: inj_is_fun [OF fn_inj] apply_funtype)

lemma (in Nat_Times_Nat) fn_iff:
    "[|x \<in> nat; y \<in> nat; u \<in> nat; v \<in> nat|]
     ==> (fn`<x,y> = fn`<u,v>) \<longleftrightarrow> (x=u & y=v)"
by (blast dest: inj_apply_equality [OF fn_inj])

lemma (in Nat_Times_Nat) enum_type [TC,simp]:
    "p \<in> formula ==> enum(fn,p) \<in> nat"
by (induct_tac p, simp_all)

lemma (in Nat_Times_Nat) enum_inject [rule_format]:
    "p \<in> formula ==> \<forall>q\<in>formula. enum(fn,p) = enum(fn,q) \<longrightarrow> p=q"
apply (induct_tac p, simp_all)
   apply (rule ballI)
   apply (erule formula.cases)
   apply (simp_all add: fn_iff)
  apply (rule ballI)
  apply (erule formula.cases)
  apply (simp_all add: fn_iff)
 apply (rule ballI)
 apply (erule_tac a=qa in formula.cases)
 apply (simp_all add: fn_iff)
 apply blast
apply (rule ballI)
apply (erule_tac a=q in formula.cases)
apply (simp_all add: fn_iff, blast)
done

lemma (in Nat_Times_Nat) inj_formula_nat:
    "(\<lambda>p \<in> formula. enum(fn,p)) \<in> inj(formula, nat)"
apply (simp add: inj_def lam_type)
apply (blast intro: enum_inject)
done

lemma (in Nat_Times_Nat) well_ord_formula:
    "well_ord(formula, measure(formula, enum(fn)))"
apply (rule well_ord_measure, simp)
apply (blast intro: enum_inject)
done

lemmas nat_times_nat_lepoll_nat =
    InfCard_nat [THEN InfCard_square_eqpoll, THEN eqpoll_imp_lepoll]


text\<open>Not needed--but interesting?\<close>
theorem formula_lepoll_nat: "formula \<lesssim> nat"
apply (insert nat_times_nat_lepoll_nat)
apply (unfold lepoll_def)
apply (blast intro: Nat_Times_Nat.inj_formula_nat Nat_Times_Nat.intro)
done


subsection\<open>Defining the Wellordering on \<^term>\<open>DPow(A)\<close>\<close>

text\<open>The objective is to build a wellordering on \<^term>\<open>DPow(A)\<close> from a
given one on \<^term>\<open>A\<close>.  We first introduce wellorderings for environments,
which are lists built over \<^term>\<open>A\<close>.  We combine it with the enumeration of
formulas.  The order type of the resulting wellordering gives us a map from
(environment, formula) pairs into the ordinals.  For each member of \<^term>\<open>DPow(A)\<close>, we take the minimum such ordinal.\<close>

definition
  env_form_r :: "[i,i,i]=>i" where
    \<comment> \<open>wellordering on (environment, formula) pairs\<close>
   "env_form_r(f,r,A) ==
      rmult(list(A), rlist(A, r),
            formula, measure(formula, enum(f)))"

definition
  env_form_map :: "[i,i,i,i]=>i" where
    \<comment> \<open>map from (environment, formula) pairs to ordinals\<close>
   "env_form_map(f,r,A,z)
      == ordermap(list(A) * formula, env_form_r(f,r,A)) ` z"

definition
  DPow_ord :: "[i,i,i,i,i]=>o" where
    \<comment> \<open>predicate that holds if \<^term>\<open>k\<close> is a valid index for \<^term>\<open>X\<close>\<close>
   "DPow_ord(f,r,A,X,k) ==
           \<exists>env \<in> list(A). \<exists>p \<in> formula.
             arity(p) \<le> succ(length(env)) &
             X = {x\<in>A. sats(A, p, Cons(x,env))} &
             env_form_map(f,r,A,<env,p>) = k"

definition
  DPow_least :: "[i,i,i,i]=>i" where
    \<comment> \<open>function yielding the smallest index for \<^term>\<open>X\<close>\<close>
   "DPow_least(f,r,A,X) == \<mu> k. DPow_ord(f,r,A,X,k)"

definition
  DPow_r :: "[i,i,i]=>i" where
    \<comment> \<open>a wellordering on \<^term>\<open>DPow(A)\<close>\<close>
   "DPow_r(f,r,A) == measure(DPow(A), DPow_least(f,r,A))"


lemma (in Nat_Times_Nat) well_ord_env_form_r:
    "well_ord(A,r)
     ==> well_ord(list(A) * formula, env_form_r(fn,r,A))"
by (simp add: env_form_r_def well_ord_rmult well_ord_rlist well_ord_formula)

lemma (in Nat_Times_Nat) Ord_env_form_map:
    "[|well_ord(A,r); z \<in> list(A) * formula|]
     ==> Ord(env_form_map(fn,r,A,z))"
by (simp add: env_form_map_def Ord_ordermap well_ord_env_form_r)

lemma DPow_imp_ex_DPow_ord:
    "X \<in> DPow(A) ==> \<exists>k. DPow_ord(fn,r,A,X,k)"
apply (simp add: DPow_ord_def)
apply (blast dest!: DPowD)
done

lemma (in Nat_Times_Nat) DPow_ord_imp_Ord:
     "[|DPow_ord(fn,r,A,X,k); well_ord(A,r)|] ==> Ord(k)"
apply (simp add: DPow_ord_def, clarify)
apply (simp add: Ord_env_form_map)
done

lemma (in Nat_Times_Nat) DPow_imp_DPow_least:
    "[|X \<in> DPow(A); well_ord(A,r)|]
     ==> DPow_ord(fn, r, A, X, DPow_least(fn,r,A,X))"
apply (simp add: DPow_least_def)
apply (blast dest: DPow_imp_ex_DPow_ord intro: DPow_ord_imp_Ord LeastI)
done

lemma (in Nat_Times_Nat) env_form_map_inject:
    "[|env_form_map(fn,r,A,u) = env_form_map(fn,r,A,v); well_ord(A,r);
       u \<in> list(A) * formula;  v \<in> list(A) * formula|]
     ==> u=v"
apply (simp add: env_form_map_def)
apply (rule inj_apply_equality [OF bij_is_inj, OF ordermap_bij,
                                OF well_ord_env_form_r], assumption+)
done

lemma (in Nat_Times_Nat) DPow_ord_unique:
    "[|DPow_ord(fn,r,A,X,k); DPow_ord(fn,r,A,Y,k); well_ord(A,r)|]
     ==> X=Y"
apply (simp add: DPow_ord_def, clarify)
apply (drule env_form_map_inject, auto)
done

lemma (in Nat_Times_Nat) well_ord_DPow_r:
    "well_ord(A,r) ==> well_ord(DPow(A), DPow_r(fn,r,A))"
apply (simp add: DPow_r_def)
apply (rule well_ord_measure)
 apply (simp add: DPow_least_def Ord_Least)
apply (drule DPow_imp_DPow_least, assumption)+
apply simp
apply (blast intro: DPow_ord_unique)
done

lemma (in Nat_Times_Nat) DPow_r_type:
    "DPow_r(fn,r,A) \<subseteq> DPow(A) * DPow(A)"
by (simp add: DPow_r_def measure_def, blast)


subsection\<open>Limit Construction for Well-Orderings\<close>

text\<open>Now we work towards the transfinite definition of wellorderings for
\<^term>\<open>Lset(i)\<close>.  We assume as an inductive hypothesis that there is a family
of wellorderings for smaller ordinals.\<close>

definition
  rlimit :: "[i,i=>i]=>i" where
  \<comment> \<open>Expresses the wellordering at limit ordinals.  The conditional
      lets us remove the premise \<^term>\<open>Limit(i)\<close> from some theorems.\<close>
    "rlimit(i,r) ==
       if Limit(i) then 
         {z: Lset(i) * Lset(i).
          \<exists>x' x. z = <x',x> &
                 (lrank(x') < lrank(x) |
                  (lrank(x') = lrank(x) & <x',x> \<in> r(succ(lrank(x)))))}
       else 0"

definition
  Lset_new :: "i=>i" where
  \<comment> \<open>This constant denotes the set of elements introduced at level
      \<^term>\<open>succ(i)\<close>\<close>
    "Lset_new(i) == {x \<in> Lset(succ(i)). lrank(x) = i}"

lemma Limit_Lset_eq2:
    "Limit(i) ==> Lset(i) = (\<Union>j\<in>i. Lset_new(j))"
apply (simp add: Limit_Lset_eq)
apply (rule equalityI)
 apply safe
 apply (subgoal_tac "Ord(y)")
  prefer 2 apply (blast intro: Ord_in_Ord Limit_is_Ord)
 apply (simp_all add: Limit_is_Ord Lset_iff_lrank_lt Lset_new_def
                      Ord_mem_iff_lt)
 apply (blast intro: lt_trans)
apply (rule_tac x = "succ(lrank(x))" in bexI)
 apply (simp add: Lset_succ_lrank_iff)
apply (blast intro: Limit_has_succ ltD)
done

lemma wf_on_Lset:
    "wf[Lset(succ(j))](r(succ(j))) ==> wf[Lset_new(j)](rlimit(i,r))"
apply (simp add: wf_on_def Lset_new_def)
apply (erule wf_subset)
apply (simp add: rlimit_def, force)
done

lemma wf_on_rlimit:
    "(\<forall>j<i. wf[Lset(j)](r(j))) ==> wf[Lset(i)](rlimit(i,r))"
apply (case_tac "Limit(i)") 
 prefer 2
 apply (simp add: rlimit_def wf_on_any_0)
apply (simp add: Limit_Lset_eq2)
apply (rule wf_on_Union)
  apply (rule wf_imp_wf_on [OF wf_Memrel [of i]])
 apply (blast intro: wf_on_Lset Limit_has_succ Limit_is_Ord ltI)
apply (force simp add: rlimit_def Limit_is_Ord Lset_iff_lrank_lt Lset_new_def
                       Ord_mem_iff_lt)
done

lemma linear_rlimit:
    "[|Limit(i); \<forall>j<i. linear(Lset(j), r(j)) |]
     ==> linear(Lset(i), rlimit(i,r))"
apply (frule Limit_is_Ord)
apply (simp add: Limit_Lset_eq2 Lset_new_def)
apply (simp add: linear_def rlimit_def Ball_def lt_Ord Lset_iff_lrank_lt)
apply (simp add: ltI, clarify)
apply (rename_tac u v)
apply (rule_tac i="lrank(u)" and j="lrank(v)" in Ord_linear_lt, simp_all) 
apply (drule_tac x="succ(lrank(u) \<union> lrank(v))" in ospec)
 apply (simp add: ltI)
apply (drule_tac x=u in spec, simp)
apply (drule_tac x=v in spec, simp)
done

lemma well_ord_rlimit:
    "[|Limit(i); \<forall>j<i. well_ord(Lset(j), r(j)) |]
     ==> well_ord(Lset(i), rlimit(i,r))"
by (blast intro: well_ordI wf_on_rlimit well_ord_is_wf
                           linear_rlimit well_ord_is_linear)

lemma rlimit_cong:
     "(!!j. j<i ==> r'(j) = r(j)) ==> rlimit(i,r) = rlimit(i,r')"
apply (simp add: rlimit_def, clarify) 
apply (rule refl iff_refl Collect_cong ex_cong conj_cong)+
apply (simp add: Limit_is_Ord Lset_lrank_lt)
done


subsection\<open>Transfinite Definition of the Wellordering on \<^term>\<open>L\<close>\<close>

definition
  L_r :: "[i, i] => i" where
  "L_r(f) == %i.
      transrec3(i, 0, \<lambda>x r. DPow_r(f, r, Lset(x)), 
                \<lambda>x r. rlimit(x, \<lambda>y. r`y))"

subsubsection\<open>The Corresponding Recursion Equations\<close>
lemma [simp]: "L_r(f,0) = 0"
by (simp add: L_r_def)

lemma [simp]: "L_r(f, succ(i)) = DPow_r(f, L_r(f,i), Lset(i))"
by (simp add: L_r_def)

text\<open>The limit case is non-trivial because of the distinction between
object-level and meta-level abstraction.\<close>
lemma [simp]: "Limit(i) ==> L_r(f,i) = rlimit(i, L_r(f))"
by (simp cong: rlimit_cong add: transrec3_Limit L_r_def ltD)

lemma (in Nat_Times_Nat) L_r_type:
    "Ord(i) ==> L_r(fn,i) \<subseteq> Lset(i) * Lset(i)"
apply (induct i rule: trans_induct3)
  apply (simp_all add: Lset_succ DPow_r_type well_ord_DPow_r rlimit_def
                       Transset_subset_DPow [OF Transset_Lset], blast)
done

lemma (in Nat_Times_Nat) well_ord_L_r:
    "Ord(i) ==> well_ord(Lset(i), L_r(fn,i))"
apply (induct i rule: trans_induct3)
apply (simp_all add: well_ord0 Lset_succ L_r_type well_ord_DPow_r
                     well_ord_rlimit ltD)
done

lemma well_ord_L_r:
    "Ord(i) ==> \<exists>r. well_ord(Lset(i), r)"
apply (insert nat_times_nat_lepoll_nat)
apply (unfold lepoll_def)
apply (blast intro: Nat_Times_Nat.well_ord_L_r Nat_Times_Nat.intro)
done


text\<open>Every constructible set is well-ordered! Therefore the Wellordering Theorem and
      the Axiom of Choice hold in \<^term>\<open>L\<close>!!\<close>
theorem L_implies_AC: assumes x: "L(x)" shows "\<exists>r. well_ord(x,r)"
  using Transset_Lset x
apply (simp add: Transset_def L_def)
apply (blast dest!: well_ord_L_r intro: well_ord_subset)
done

interpretation L?: M_basic L by (rule M_basic_L)

theorem "\<forall>x[L]. \<exists>r. wellordered(L,x,r)"
proof 
  fix x
  assume "L(x)"
  then obtain r where "well_ord(x,r)" 
    by (blast dest: L_implies_AC) 
  thus "\<exists>r. wellordered(L,x,r)" 
    by (blast intro: well_ord_imp_relativized)
qed

text\<open>In order to prove \<^term>\<open> \<exists>r[L]. wellordered(L,x,r)\<close>, it's necessary to know 
that \<^term>\<open>r\<close> is actually constructible. It follows from the assumption ``\<^term>\<open>V\<close> equals \<^term>\<open>L''\<close>, 
but this reasoning doesn't appear to work in Isabelle.\<close>

end