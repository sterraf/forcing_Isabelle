(*  Title:      ZF/Constructible/DPow_absolute.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>Absoluteness for the Definable Powerset Function\<close>


theory DPow_absolute imports Rec_Separation begin


subsubsection\<open>The Operator \<^term>\<open>is_Collect\<close>\<close>

text\<open>The formula \<^term>\<open>is_P\<close> has one free variable, 0, and it is
enclosed within a single quantifier.\<close>

(* is_Collect :: "[i=>o,i,i=>o,i] => o"
    "is_Collect(M,A,P,z) == \<forall>x[M]. x \<in> z \<longleftrightarrow> x \<in> A & P(x)" *)

definition
  Collect_fm :: "[i, i, i]=>i" where
 "Collect_fm(A,is_P,z) == 
        Forall(Iff(Member(0,succ(z)),
                   And(Member(0,succ(A)), is_P)))"

lemma is_Collect_type [TC]:
     "[| is_P \<in> formula; x \<in> nat; y \<in> nat |] 
      ==> Collect_fm(x,is_P,y) \<in> formula"
by (simp add: Collect_fm_def)

lemma sats_Collect_fm:
  assumes is_P_iff_sats: 
      "!!a. a \<in> A ==> is_P(a) \<longleftrightarrow> sats(A, p, Cons(a, env))"
  shows 
      "[|x \<in> nat; y \<in> nat; env \<in> list(A)|]
       ==> sats(A, Collect_fm(x,p,y), env) \<longleftrightarrow>
           is_Collect(##A, nth(x,env), is_P, nth(y,env))"
by (simp add: Collect_fm_def is_Collect_def is_P_iff_sats [THEN iff_sym])

lemma Collect_iff_sats:
  assumes is_P_iff_sats: 
      "!!a. a \<in> A ==> is_P(a) \<longleftrightarrow> sats(A, p, Cons(a, env))"
  shows 
  "[| nth(i,env) = x; nth(j,env) = y;
      i \<in> nat; j \<in> nat; env \<in> list(A)|]
   ==> is_Collect(##A, x, is_P, y) \<longleftrightarrow> sats(A, Collect_fm(i,p,j), env)"
by (simp add: sats_Collect_fm [OF is_P_iff_sats])


text\<open>The second argument of \<^term>\<open>is_P\<close> gives it direct access to \<^term>\<open>x\<close>,
  which is essential for handling free variable references.\<close>
theorem Collect_reflection:
  assumes is_P_reflection:
    "!!h f g. REFLECTS[\<lambda>x. is_P(L, f(x), g(x)),
                     \<lambda>i x. is_P(##Lset(i), f(x), g(x))]"
  shows "REFLECTS[\<lambda>x. is_Collect(L, f(x), is_P(L,x), g(x)),
               \<lambda>i x. is_Collect(##Lset(i), f(x), is_P(##Lset(i), x), g(x))]"
apply (simp (no_asm_use) only: is_Collect_def)
apply (intro FOL_reflections is_P_reflection)
done


subsubsection\<open>The Operator \<^term>\<open>is_Replace\<close>\<close>

text\<open>BEWARE!  The formula \<^term>\<open>is_P\<close> has free variables 0, 1
 and not the usual 1, 0!  It is enclosed within two quantifiers.\<close>

(*  is_Replace :: "[i=>o,i,[i,i]=>o,i] => o"
    "is_Replace(M,A,P,z) == \<forall>u[M]. u \<in> z \<longleftrightarrow> (\<exists>x[M]. x\<in>A & P(x,u))" *)

definition
  Replace_fm :: "[i, i, i]=>i" where
  "Replace_fm(A,is_P,z) == 
        Forall(Iff(Member(0,succ(z)),
                   Exists(And(Member(0,A#+2), is_P))))"

lemma is_Replace_type [TC]:
     "[| is_P \<in> formula; x \<in> nat; y \<in> nat |] 
      ==> Replace_fm(x,is_P,y) \<in> formula"
by (simp add: Replace_fm_def)

lemma sats_Replace_fm:
  assumes is_P_iff_sats: 
      "!!a b. [|a \<in> A; b \<in> A|] 
              ==> is_P(a,b) \<longleftrightarrow> sats(A, p, Cons(a,Cons(b,env)))"
  shows 
      "[|x \<in> nat; y \<in> nat; env \<in> list(A)|]
       ==> sats(A, Replace_fm(x,p,y), env) \<longleftrightarrow>
           is_Replace(##A, nth(x,env), is_P, nth(y,env))"
by (simp add: Replace_fm_def is_Replace_def is_P_iff_sats [THEN iff_sym])

lemma Replace_iff_sats:
  assumes is_P_iff_sats: 
      "!!a b. [|a \<in> A; b \<in> A|] 
              ==> is_P(a,b) \<longleftrightarrow> sats(A, p, Cons(a,Cons(b,env)))"
  shows 
  "[| nth(i,env) = x; nth(j,env) = y;
      i \<in> nat; j \<in> nat; env \<in> list(A)|]
   ==> is_Replace(##A, x, is_P, y) \<longleftrightarrow> sats(A, Replace_fm(i,p,j), env)"
by (simp add: sats_Replace_fm [OF is_P_iff_sats])


text\<open>The second argument of \<^term>\<open>is_P\<close> gives it direct access to \<^term>\<open>x\<close>,
  which is essential for handling free variable references.\<close>
theorem Replace_reflection:
  assumes is_P_reflection:
    "!!h f g. REFLECTS[\<lambda>x. is_P(L, f(x), g(x), h(x)),
                     \<lambda>i x. is_P(##Lset(i), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. is_Replace(L, f(x), is_P(L,x), g(x)),
               \<lambda>i x. is_Replace(##Lset(i), f(x), is_P(##Lset(i), x), g(x))]"
apply (simp (no_asm_use) only: is_Replace_def)
apply (intro FOL_reflections is_P_reflection)
done


end
