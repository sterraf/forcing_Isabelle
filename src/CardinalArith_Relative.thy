section\<open>Relative, Choice-less Cardinal Arithmetic\<close>

theory CardinalArith_Relative 
  imports 
    Cardinal_Relative

begin

definition
  less :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "less(M,a,b) \<equiv> a\<in>b \<and> ordinal(M,b)"

lemma (in M_trans) less_abs[simp]: "M(a) \<Longrightarrow> M(b) \<Longrightarrow> less(M,a,b) \<longleftrightarrow> a<b"
  unfolding less_def lt_def by auto

(******************************************************)
subsection\<open>Discipline for \<^term>\<open>InfCard\<close>\<close>

\<comment> \<open>Next definition expands the abbreviation for \<^term>\<open>(\<le>)\<close>\<close>
definition (* completely relational *)
  InfCard_rel   :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
  "InfCard_rel(M,A) \<equiv> \<exists>om[M]. \<exists>sA[M]. omega(M,om) \<and> Card_rel(M,A) \<and> 
    successor(M,A,sA) \<and> less(M,om,sA)"

context M_cardinals
begin

\<comment> \<open>NOTE: using a shorter suffix in place of "_rel"\<close> 
abbreviation
  InfCard_r     :: "i=>o"  where
  "InfCard_r(i) \<equiv> InfCard_rel(M,i)"

lemma def_InfCard_rel:
  assumes
    "M(i)"
  shows
    "InfCard_r(i) \<longleftrightarrow> Card_rel(i) \<and> nat \<le> i"
  using assms 
  unfolding InfCard_rel_def Card_rel_def by simp

end (* M_cardinals *)

(******************  end Discipline  ******************)

(******************************************************)
subsection\<open>Discipline for \<^term>\<open>cadd\<close>\<close>

text\<open>Cardinal addition \<^term>\<open>cadd\<close> is a composition of the unary
\<^term>\<open>cardinal\<close> and the binary \<^term>\<open>(+)\<close>. By using appropriate
projections we can express its relational version using
\<^term>\<open>is_hcomp2_2\<close>.\<close>

definition (* completely relational *)
  is_cadd   :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o"  where
  "is_cadd(M,A,B,bj) \<equiv> is_hcomp2_2(M,\<lambda>M _. is_cardinal(M),\<lambda>_ _. (=),is_sum,A,B,bj)"

context M_cardinals
begin

lemma is_cadd_uniqueness:
  assumes
    "M(A)" "M(B)" "M(d)" "M(d')"
    "is_cadd(M,A,B,d)" "is_cadd(M,A,B,d')"
  shows
    "d=d'"
  using assms \<comment> \<open>using projections (\<^term>\<open>\<lambda>_ _. (=)\<close>)
                  requires more instantiations\<close>
    is_cardinal_uniqueness hcomp2_2_uniqueness[of
      M "\<lambda>M _. is_cardinal(M)" "\<lambda>_ _. (=)" is_sum A B d d']
  unfolding is_cadd_def
  by auto

lemma is_cadd_witness: "M(A) \<Longrightarrow> M(B)\<Longrightarrow> \<exists>d[M]. is_cadd(M,A,B,d)"
  using hcomp2_2_witness[of M "\<lambda>M _. is_cardinal(M)" "\<lambda>_ _. (=)" is_sum A B]
    is_cardinal_witness
  unfolding is_cadd_def by simp

definition
  cadd_rel :: "i \<Rightarrow> i \<Rightarrow> i"  where
  "cadd_rel(A,B) \<equiv> THE d. M(d) \<and> is_cadd(M,A,B,d)"

lemma cadd_rel_closed[intro,simp]: "M(x) \<Longrightarrow> M(y) \<Longrightarrow> M(cadd_rel(x,y))"
  unfolding cadd_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_cadd(M,x,y,d)"], OF _ is_cadd_uniqueness[of x y]]
    is_cadd_witness by auto

lemma cadd_rel_iff:
  assumes "M(x)" "M(y)" "M(d)"
  shows "is_cadd(M,x,y,d) \<longleftrightarrow> d = cadd_rel(x,y)"
proof (intro iffI)
  assume "d = cadd_rel(x,y)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_cadd(M,x,y,e)"
    using is_cadd_witness by blast
  ultimately
  show "is_cadd(M, x, y, d)"
    using is_cadd_uniqueness[of x y] is_cadd_witness
      theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_cadd(M,x,y,d)"], OF _ is_cadd_uniqueness[of x y], of e]
    unfolding cadd_rel_def
    by auto
next
  assume "is_cadd(M, x, y, d)"
  with assms
  show "d = cadd_rel(x,y)"
    using is_cadd_uniqueness unfolding cadd_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_cadd_rel:
  assumes "M(A)" "M(B)"
  shows "cadd_rel(A,B) = |A+B|r"
  using assms cadd_rel_iff
    cardinal_rel_iff
    hcomp2_2_abs[of "\<lambda>M _. is_cardinal(M)" "\<lambda>_.cardinal_rel"
      "\<lambda>_ _. (=)" "\<lambda>x y. y" is_sum "(+)" A B "cadd_rel(A,B)"]
  unfolding is_cadd_def by force

notation cadd_rel (infixl \<open>\<oplus>r\<close> 65)

end (* M_cardinals *)

(***************  end Discipline  *********************)

(******************************************************)
subsection\<open>Discipline for \<^term>\<open>cmult\<close>\<close>

definition (* completely relational *)
  is_cmult   :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o"  where
  "is_cmult(M,A,B,bj) \<equiv> is_hcomp2_2(M,\<lambda>M _. is_cardinal(M),\<lambda>_ _. (=),cartprod,A,B,bj)"

context M_cardinals
begin

lemma is_cmult_uniqueness:
  assumes
    "M(A)" "M(B)" "M(d)" "M(d')"
    "is_cmult(M,A,B,d)" "is_cmult(M,A,B,d')"
  shows
    "d=d'"
  using assms \<comment> \<open>using projections (\<^term>\<open>\<lambda>_ _. (=)\<close>)
                  requires more instantiations\<close>
    is_cardinal_uniqueness hcomp2_2_uniqueness[of
      M "\<lambda>M _. is_cardinal(M)" "\<lambda>_ _. (=)" cartprod A B d d']
  unfolding is_cmult_def
  by auto

lemma is_cmult_witness: "M(A) \<Longrightarrow> M(B)\<Longrightarrow> \<exists>d[M]. is_cmult(M,A,B,d)"
  using hcomp2_2_witness[of M "\<lambda>M _. is_cardinal(M)" "\<lambda>_ _. (=)" cartprod A B]
    is_cardinal_witness
  unfolding is_cmult_def by simp

definition
  cmult_rel :: "i \<Rightarrow> i \<Rightarrow> i"  where
  "cmult_rel(A,B) \<equiv> THE d. M(d) \<and> is_cmult(M,A,B,d)"

lemma cmult_rel_closed[intro,simp]: "M(x) \<Longrightarrow> M(y) \<Longrightarrow> M(cmult_rel(x,y))"
  unfolding cmult_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_cmult(M,x,y,d)"], OF _ is_cmult_uniqueness[of x y]]
    is_cmult_witness by auto

lemma cmult_rel_iff:
  assumes "M(x)" "M(y)" "M(d)"
  shows "is_cmult(M,x,y,d) \<longleftrightarrow> d = cmult_rel(x,y)"
proof (intro iffI)
  assume "d = cmult_rel(x,y)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_cmult(M,x,y,e)"
    using is_cmult_witness by blast
  ultimately
  show "is_cmult(M, x, y, d)"
    using is_cmult_uniqueness[of x y] is_cmult_witness
      theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_cmult(M,x,y,d)"], OF _ is_cmult_uniqueness[of x y], of e]
    unfolding cmult_rel_def
    by auto
next
  assume "is_cmult(M, x, y, d)"
  with assms
  show "d = cmult_rel(x,y)"
    using is_cmult_uniqueness unfolding cmult_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_cmult_rel:
  assumes "M(A)" "M(B)"
  shows "cmult_rel(A,B) = |A\<times>B|r"
  using assms cmult_rel_iff
    cardinal_rel_iff
    hcomp2_2_abs[of "\<lambda>M _. is_cardinal(M)" "\<lambda>_.cardinal_rel"
      "\<lambda>_ _. (=)" "\<lambda>x y. y" cartprod "(\<times>)" A B "cmult_rel(A,B)"]
  unfolding is_cmult_def by force

notation cmult_rel (infixl \<open>\<otimes>r\<close> 70)

end (* M_cardinals *)

(***************  end Discipline  *********************)

(* FIXME: these definitions already appear in FrecR.thy ! *)
definition
  is_fst :: "(i\<Rightarrow>o)\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "is_fst(M,x,t) \<equiv> (\<exists>z[M]. pair(M,t,z,x)) \<or>
                       (\<not>(\<exists>z[M]. \<exists>w[M]. pair(M,w,z,x)) \<and> empty(M,t))"

definition
  is_snd :: "(i\<Rightarrow>o)\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "is_snd(M,x,t) \<equiv> (\<exists>z[M]. pair(M,z,t,x)) \<or>
                       (\<not>(\<exists>z[M]. \<exists>w[M]. pair(M,z,w,x)) \<and> empty(M,t))"

context M_trans
begin
\<comment> \<open>Using attribute "absolut" instead of overpopulating the simpset\<close>
lemma fst_abs[absolut]: "M(a) \<Longrightarrow> M(z) \<Longrightarrow> is_fst(M,a,z) \<longleftrightarrow> z = fst(a)"
  unfolding is_fst_def fst_def the_def
  by (cases "\<exists>b c. a = \<langle>b, c\<rangle>"; auto)
    (auto simp add: Pair_def dest:transM)

lemma snd_abs[absolut]: "M(a) \<Longrightarrow> M(z) \<Longrightarrow> is_snd(M,a,z) \<longleftrightarrow> z = snd(a)"
  unfolding is_snd_def snd_def the_def
  by (cases "\<exists>b c. a = \<langle>b, c\<rangle>"; auto)
    (auto simp add: Pair_def dest:transM)
end (* M_trans *)

(* rvimage(?A, ?f, ?r) \<equiv> {z \<in> ?A \<times> ?A . \<exists>x y. z = \<langle>x, y\<rangle> \<and> \<langle>?f ` x, ?f ` y\<rangle> \<in> ?r} *)
definition
  rvimageP :: "[i,i,i] \<Rightarrow> o" where
  "rvimageP(f,r,z) \<equiv> \<exists>x y. z = \<langle>x, y\<rangle> \<and> \<langle>f ` x, f ` y\<rangle> \<in> r"

definition
  is_rvimageP :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_rvimageP(M,f,r,z) \<equiv> \<exists>x[M]. \<exists>y[M]. \<exists>fx[M]. \<exists>fy[M]. \<exists>fxfy[M].
      pair(M,x,y,z) \<and> is_apply(M,f,x,fx) \<and> is_apply(M,f,y,fy) \<and>
      pair(M,fx,fy,fxfy) \<and> fxfy \<in> r"

definition
  is_rvimage :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_rvimage(M,A,f,r,rvi) \<equiv> \<exists>A2[M]. cartprod(M,A,A,A2) \<and>
        is_Collect(M,A2,is_rvimageP(M,f,r),rvi)"

definition
  csquare_lam :: "i\<Rightarrow>i" where
  "csquare_lam(K) \<equiv> \<lambda>\<langle>x,y\<rangle>\<in>K\<times>K. \<langle>x \<union> y, x, y\<rangle>"

context M_trans
begin

(* FIXME: move the following two to an appropriate place. Should be
used for @{thm fst_snd_closed} in Names.thy *)
lemma fst_closed[intro,simp]: "M(x) \<Longrightarrow> M(fst(x))"
  unfolding fst_def by (auto intro:theI2)

lemma (in M_basic) snd_closed[intro,simp]: "M(x) \<Longrightarrow> M(snd(x))"
  unfolding snd_def by (auto intro:theI2)

end (* M_trans *)

(* FIXME: Remove these after fixing relativize_tm *)
lemma fst_abs[Rel]: "is_fst(M,a,z) \<longleftrightarrow> z = fst(a) \<Longrightarrow> is_fst(M,a,z) \<longleftrightarrow> z = fst(a)" .
lemma snd_abs[Rel]: "is_snd(M,a,z) \<longleftrightarrow> z = snd(a) \<Longrightarrow> is_snd(M,a,z) \<longleftrightarrow> z = snd(a)" .

relativize_tm "<fst(x) \<union> snd(x), fst(x), snd(x)>" "is_csquare_lam_body"

definition
  is_csquare_lam :: "[i\<Rightarrow>o,i,i]\<Rightarrow>o" where
  "is_csquare_lam(M,K,l) \<equiv> \<exists>K2[M]. cartprod(M,K,K,K2) \<and>
        is_lambda(M,K2,is_csquare_lam_body(M),l)"

lemma (in M_cardinals) csquare_lam_closed[intro,simp]: "M(K) \<Longrightarrow> M(csquare_lam(K))" sorry

relativize_tm "\<exists>x' y' x y. z = \<langle>\<langle>x', y'\<rangle>, x, y\<rangle> \<and> (\<langle>x', x\<rangle> \<in> r \<or> x' = x \<and> \<langle>y', y\<rangle> \<in> s)" 
  "is_rmultP"

definition
  is_rmult:: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_rmult(M,A,r,B,s,rm) \<equiv> \<exists>AB[M]. \<exists>AB2[M]. cartprod(M,A,B,AB) \<and>
        cartprod(M,AB,AB,AB2) \<and> is_Collect(M,AB2,is_rmultP(M,s,r),rm)"

context M_trivial
begin

lemma rmultP_abs [absolut]: "\<lbrakk> M(r); M(s); M(z) \<rbrakk> \<Longrightarrow> is_rmultP(M,s,r,z) \<longleftrightarrow>
    (\<exists>x' y' x y. z = \<langle>\<langle>x', y'\<rangle>, x, y\<rangle> \<and> (\<langle>x', x\<rangle> \<in> r \<or> x' = x \<and> \<langle>y', y\<rangle> \<in> s))"
  unfolding is_rmultP_def by (auto dest:transM)

end (* M_trivial *)


definition
  is_csquare_rel :: "[i\<Rightarrow>o,i,i]\<Rightarrow>o"  where
    "is_csquare_rel(M,K,cs) \<equiv> \<exists>K2[M]. \<exists>la[M]. \<exists>memK[M].
      \<exists>rmKK[M]. \<exists>rmKK2[M].
        cartprod(M,K,K,K2) \<and> is_csquare_lam(M,K,la) \<and>
        membership(M,K,memK) \<and> is_rmult(M,K,memK,K,memK,rmKK) \<and>
        is_rmult(M,K,memK,K2,rmKK,rmKK2) \<and> is_rvimage(M,K2,la,rmKK2,cs)"

context M_basic
begin

lemma rvimage_abs[absolut]:
  assumes "M(A)" "M(f)" "M(r)" "M(z)"
  shows "is_rvimage(M,A,f,r,z) \<longleftrightarrow> z = rvimage(A,f,r)"
  using assms transM[OF _ \<open>M(A)\<close>]
  unfolding is_rvimage_def rvimage_def is_rvimageP_def
  by auto

lemma rmult_abs [absolut]: "\<lbrakk> M(A); M(r); M(B); M(s); M(z) \<rbrakk> \<Longrightarrow>
    is_rmult(M,A,r,B,s,z) \<longleftrightarrow> z=rmult(A,r,B,s)"
  unfolding is_rmult_def rmult_def using transM[of _ "(A \<times> B) \<times> A \<times> B"] 
  by (auto simp add:absolut del: iffI)

lemma csquare_lam_body_abs[absolut]: "M(x) \<Longrightarrow> M(z) \<Longrightarrow> 
  is_csquare_lam_body(M,x,z) \<longleftrightarrow> z = <fst(x) \<union> snd(x), fst(x), snd(x)>"
  unfolding is_csquare_lam_body_def by (simp add:absolut)

lemma csquare_lam_abs[absolut]: "M(K) \<Longrightarrow> M(l) \<Longrightarrow>
  is_csquare_lam(M,K,l) \<longleftrightarrow> l = (\<lambda>x\<in>K\<times>K. \<langle>fst(x) \<union> snd(x), fst(x), snd(x)\<rangle>)"
  unfolding is_csquare_lam_def 
  using lambda_abs2[of "K\<times>K" "is_csquare_lam_body(M)"
      "\<lambda>x. \<langle>fst(x) \<union> snd(x), fst(x), snd(x)\<rangle>"] 
  unfolding Relation1_def by (simp add:absolut)

lemma csquare_lam_eq_lam:"csquare_lam(K) = (\<lambda>z\<in>K\<times>K. <fst(z) \<union> snd(z), fst(z), snd(z)>)"
proof -
  have "(\<lambda>\<langle>x,y\<rangle>\<in>K \<times> K. \<langle>x \<union> y, x, y\<rangle>)`z =
      (\<lambda>z\<in>K\<times>K. <fst(z) \<union> snd(z), fst(z), snd(z)>)`z" if "z\<in>K\<times>K" for z
    using that by auto
  then
  show ?thesis
    unfolding csquare_lam_def
    by simp
qed

end (* M_basic *)

lemma (in M_cardinals) csquare_rel_closed[intro,simp]: "M(K) \<Longrightarrow> M(csquare_rel(K))" sorry

(* Ugly proof ahead, please enhance *)
lemma (in M_cardinals) csquare_rel_abs[absolut]: "\<lbrakk> M(K); M(cs)\<rbrakk> \<Longrightarrow>
     is_csquare_rel(M,K,cs) \<longleftrightarrow> cs = csquare_rel(K)"
  unfolding is_csquare_rel_def csquare_rel_def
  using csquare_lam_closed[unfolded csquare_lam_eq_lam] 
  by (simp add:absolut csquare_lam_eq_lam[unfolded csquare_lam_def])

(*
definition
  jump_cardinal :: "i=>i"  where
    \<comment> \<open>This definition is more complex than Kunen's but it more easily proved to
        be a cardinal\<close>
    "jump_cardinal(K) ==
         \<Union>X\<in>Pow(K). {z. r \<in> Pow(K*K), well_ord(X,r) & z = ordertype(X,r)}"

definition
  csucc         :: "i=>i"  where
    \<comment> \<open>needed because \<^term>\<open>jump_cardinal(K)\<close> might not be the successor
        of \<^term>\<open>K\<close>\<close>
    "csucc(K) == \<mu> L. Card(L) & K<L"
*)

locale M_cardinal_arith = M_cardinals +
  assumes
    case_replacement1:"strong_replacement(M, \<lambda>z y. y = \<langle>z, case(Inr, Inl, z)\<rangle>)"
    and
    case_replacement2:"strong_replacement(M,
      \<lambda>z y. y = \<langle>z, case(case(Inl, \<lambda>y. Inr(Inl(y))), \<lambda>y. Inr(Inr(y)), z)\<rangle>)"
    and
    case_replacement3:"strong_replacement(M,
      \<lambda>z y. y = \<langle>z, case(\<lambda>x. x, \<lambda>y. y, z)\<rangle>)"
    and
    case_replacement4:"M(f) \<Longrightarrow> M(g) \<Longrightarrow> strong_replacement(M,
      \<lambda>z y. y = \<langle>z, case(\<lambda>w. Inl(f ` w), \<lambda>y. Inr(g ` y), z)\<rangle>)"
    and
    case_replacement5:"strong_replacement(M,
      \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,z\<rangle>. case(\<lambda>y. Inl(\<langle>y, z\<rangle>), \<lambda>y. Inr(\<langle>y, z\<rangle>), x))(x)\<rangle>)"
    and
    Inl_replacement1:"strong_replacement(M, \<lambda>x y. y = \<langle>x, Inl(x)\<rangle>)"
    and
    Inl_replacement2:"M(A) \<Longrightarrow> strong_replacement(M,
       \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,y\<rangle>. if x = A then Inl(y) else Inr(\<langle>x, y\<rangle>))(x)\<rangle>)"
    and
    if_then_range_replacement:"M(f) \<Longrightarrow> strong_replacement(M, 
      \<lambda>z y. y = \<langle>z, if z = u then f ` 0 else 
        if z \<in> range(f) then f ` succ(converse(f) ` z) else z\<rangle>)"
    and
    if_then_range_replacement2:"M(A) \<Longrightarrow> M(C)\<Longrightarrow> strong_replacement(M,
      \<lambda>x y. y = \<langle>x, if x = Inl(A) then C else x\<rangle>)"
    and
    swap_replacement:"strong_replacement(M,
      \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,y\<rangle>. \<langle>y, x\<rangle>)(x)\<rangle>)"
    and
    assoc_replacement:"strong_replacement(M,
      \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>. \<langle>x, y, z\<rangle>)(x)\<rangle>)"
    and
    prepend_replacement:"M(x) \<Longrightarrow> strong_replacement(M, \<lambda>z y. y = \<langle>z, x, z\<rangle>)"
    and
    pospend_replacement:"M(b) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, x, b\<rangle>)"
    and
    id_replacement:"strong_replacement(M, \<lambda>x y. y = \<langle>x, x, x\<rangle>)"
    and
    prod_fun_replacement:"M(f) \<Longrightarrow> M(g) \<Longrightarrow> strong_replacement(M, 
      \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>w,y\<rangle>. \<langle>f ` w, g ` y\<rangle>)(x)\<rangle>)"
begin

lemma Card_Union [simp,intro,TC]:
  assumes A: "\<And>x. x\<in>A \<Longrightarrow> Card_rel(x)" and
    types:"M(A)"
  shows "Card_rel(\<Union>(A))"
proof (rule Card_relI)
  show "Ord(\<Union>A)" using A
    by (simp add: Card_rel_is_Ord types transM)
next
  fix j
  assume j: "j < \<Union>A"
  moreover from this
  have "M(j)" unfolding lt_def by (auto simp add:types dest:transM)
  from j
  have "\<exists>c\<in>A. j \<in> c \<and> Card_rel(c)" using A types
    unfolding lt_def
    by (simp)
  then
  obtain c where c: "c\<in>A" "j < c" "Card_rel(c)" "M(c)"
    using Card_rel_is_Ord types unfolding lt_def
    by (auto dest:transM)
  with \<open>M(j)\<close>
  have jls: "j \<prec>r c"
    by (simp add: lt_Card_rel_imp_lesspoll_rel types)
  { assume eqp: "j \<approx>r \<Union>A"
    have  "c \<lesssim>r \<Union>A" using c
      by (blast intro: subset_imp_lepoll_rel types)
    also from types \<open>M(j)\<close>
    have "... \<approx>r j"  by (rule_tac eqpoll_rel_sym [OF eqp]) (simp_all add:types)
    also have "... \<prec>r c"  by (rule jls)
    finally have "c \<prec>r c" by (simp_all add:\<open>M(c)\<close> \<open>M(j)\<close> types)
    with \<open>M(c)\<close>
    have False
      by auto
  } thus "\<not> j \<approx>r \<Union>A" by blast
qed (simp_all add:types)

(*
lemma Card_UN: "(!!x. x \<in> A ==> Card(K(x))) ==> Card(\<Union>x\<in>A. K(x))"
  by blast


lemma Card_OUN [simp,intro,TC]:
     "(!!x. x \<in> A ==> Card(K(x))) ==> Card(\<Union>x<A. K(x))"
  by (auto simp add: OUnion_def Card_0)
*)

lemma in_Card_imp_lesspoll: "[| Card_rel(K); b \<in> K; M(K); M(b) |] ==> b \<prec>r K"
apply (unfold def_lesspoll_rel)
apply (simp add: Card_rel_iff_initial)
apply (fast intro!: le_imp_lepoll_rel ltI leI)
done


subsection\<open>Cardinal addition\<close>

text\<open>Note (Paulson): Could omit proving the algebraic laws for cardinal addition and
multiplication.  On finite cardinals these operations coincide with
addition and multiplication of natural numbers; on infinite cardinals they
coincide with union (maximum).  Either way we get most laws for free.\<close>

subsubsection\<open>Cardinal addition is commutative\<close>

lemma sum_commute_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> A+B \<approx>r B+A"
proof (simp add: def_eqpoll_rel, rule rexI)
  show "(\<lambda>z\<in>A+B. case(Inr,Inl,z)) \<in> bij(A+B, B+A)"
    by (auto intro: lam_bijective [where d = "case(Inr,Inl)"])
  assume "M(A)" "M(B)"
  then
  show "M(\<lambda>z\<in>A + B. case(Inr, Inl, z))"
    using case_replacement1
    by (rule_tac lam_closed) (auto dest:transM)
qed

lemma cadd_rel_commute: "M(i) \<Longrightarrow> M(j) \<Longrightarrow> i \<oplus>r j = j \<oplus>r i"
apply (unfold def_cadd_rel)
apply (auto intro: sum_commute_eqpoll_rel [THEN cardinal_rel_cong])
done

subsubsection\<open>Cardinal addition is associative\<close>

lemma sum_assoc_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> M(C) \<Longrightarrow> (A+B)+C \<approx>r A+(B+C)"
  apply (simp add: def_eqpoll_rel)
  apply (rule rexI)
   apply (rule sum_assoc_bij)
  using case_replacement2 
    by (rule_tac lam_closed) (auto dest:transM)

text\<open>Unconditional version requires AC\<close>
lemma well_ord_cadd_rel_assoc:
  assumes i: "well_ord(i,ri)" and j: "well_ord(j,rj)" and k: "well_ord(k,rk)"
    and
    types: "M(i)" "M(ri)" "M(j)" "M(rj)" "M(k)" "M(rk)"
  shows "(i \<oplus>r j) \<oplus>r k = i \<oplus>r (j \<oplus>r k)"
proof (simp add: assms def_cadd_rel, rule cardinal_rel_cong)
  from types
  have "|i + j|r + k \<approx>r (i + j) + k"
    by (auto intro!: sum_eqpoll_rel_cong well_ord_cardinal_rel_eqpoll_rel eqpoll_rel_refl well_ord_radd i j)
  also have "...  \<approx>r i + (j + k)"
    by (rule sum_assoc_eqpoll_rel) (simp_all add:types)
  also
  have "...  \<approx>r i + |j + k|r"
  proof (auto intro!: sum_eqpoll_rel_cong intro:eqpoll_rel_refl simp add:types)
    from types
    have "|j + k|r \<approx>r j + k"
      using well_ord_cardinal_rel_eqpoll_rel[OF well_ord_radd, OF j k]
      by (simp)
    with types
    show "j + k \<approx>r |j + k|r"
      using eqpoll_rel_sym by simp
  qed
  finally show "|i + j|r + k \<approx>r i + |j + k|r" by (simp_all add:types)
qed (simp_all add:types)


subsubsection\<open>0 is the identity for addition\<close>

lemma sum_0_eqpoll_rel: "M(A) \<Longrightarrow> 0+A \<approx>r A"
  apply (simp add:def_eqpoll_rel)
  apply (rule rexI)
   apply (rule bij_0_sum)
  using case_replacement3
  by (rule lam_closed)
    (auto simp add:case_def cond_def Inr_def dest:transM)

lemma cadd_rel_0 [simp]: "Card_rel(K) \<Longrightarrow> M(K) \<Longrightarrow> 0 \<oplus>r K = K"
apply (simp add: def_cadd_rel)
apply (simp add: sum_0_eqpoll_rel [THEN cardinal_rel_cong] Card_rel_cardinal_rel_eq)
done

subsubsection\<open>Addition by another cardinal\<close>

lemma sum_lepoll_rel_self: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> A \<lesssim>r A+B"
proof (simp add: def_lepoll_rel, rule rexI)
  show "(\<lambda>x\<in>A. Inl (x)) \<in> inj(A, A + B)"
    by (simp add: inj_def)
  assume "M(A)" "M(B)"
  then
  show "M(\<lambda>x\<in>A. Inl(x))"
    using Inl_replacement1 transM[OF _ \<open>M(A)\<close>]
    by (rule_tac lam_closed) (auto simp add: Inl_def)
qed

(*Could probably weaken the premises to well_ord(K,r), or removing using AC*)

lemma cadd_rel_le_self:
  assumes K: "Card_rel(K)" and L: "Ord(L)" and
    types:"M(K)" "M(L)"
  shows "K \<le> (K \<oplus>r L)"
proof (simp add:types def_cadd_rel)
  have "K \<le> |K|r"
    by (rule Card_rel_cardinal_rel_le [OF K]) (simp add:types)
  moreover have "|K|r \<le> |K + L|r" using K L
    by (blast intro: well_ord_lepoll_rel_imp_Card_rel_le sum_lepoll_rel_self
                     well_ord_radd well_ord_Memrel Card_rel_is_Ord types)
  ultimately show "K \<le> |K + L|r"
    by (blast intro: le_trans)
qed

subsubsection\<open>Monotonicity of addition\<close>

lemma sum_lepoll_rel_mono:
     "[| A \<lesssim>r C;  B \<lesssim>r D; M(A); M(B); M(C); M(D) |] ==> A + B \<lesssim>r C + D"
apply (simp add: def_lepoll_rel)
apply (elim rexE)
apply (rule_tac x = "\<lambda>z\<in>A+B. case (%w. Inl(f`w), %y. Inr(fa`y), z)" in rexI)
apply (rule_tac d = "case (%w. Inl(converse(f) `w), %y. Inr(converse(fa) ` y))"
       in lam_injective)
    apply (typecheck add: inj_is_fun, auto)
  apply (rule_tac lam_closed, auto dest:transM intro:case_replacement4)
done

lemma cadd_le_mono:
    "[| K' \<le> K;  L' \<le> L;M(K');M(K);M(L');M(L) |] ==> (K' \<oplus>r L') \<le> (K \<oplus>r L)"
apply (unfold def_cadd_rel)
apply (safe dest!: le_subset_iff [THEN iffD1])
apply (rule well_ord_lepoll_rel_imp_Card_rel_le)
apply (blast intro: well_ord_radd well_ord_Memrel)
apply (auto intro: sum_lepoll_rel_mono subset_imp_lepoll_rel)
done

subsubsection\<open>Addition of finite cardinals is "ordinary" addition\<close>

lemma sum_succ_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> succ(A)+B \<approx>r succ(A+B)"
apply (simp add:def_eqpoll_rel)
apply (rule rexI)
apply (rule_tac c = "%z. if z=Inl (A) then A+B else z"
            and d = "%z. if z=A+B then Inl (A) else z" in lam_bijective)
   apply simp_all
      apply (blast dest: sym [THEN eq_imp_not_mem] elim: mem_irrefl)+
  apply(rule_tac lam_closed, auto dest:transM intro:if_then_range_replacement2)
done

(*Pulling the  succ(...)  outside the |...| requires m, n \<in> nat  *)
(*Unconditional version requires AC*)
lemma cadd_succ_lemma:
  assumes "Ord(m)" "Ord(n)" and
    types: "M(m)" "M(n)"
  shows "succ(m) \<oplus>r n = |succ(m \<oplus>r n)|r"
  using types
proof (simp add: def_cadd_rel)
  have [intro]: "m + n \<approx>r |m + n|r" using assms
    by (blast intro: eqpoll_rel_sym well_ord_cardinal_rel_eqpoll_rel well_ord_radd well_ord_Memrel)

  have "|succ(m) + n|r = |succ(m + n)|r"
    by (rule sum_succ_eqpoll_rel [THEN cardinal_rel_cong]) (simp_all add:types)
  also have "... = |succ(|m + n|r)|r"
    by (blast intro: succ_eqpoll_rel_cong cardinal_rel_cong types)
  finally show "|succ(m) + n|r = |succ(|m + n|r)|r" .
qed

lemma nat_cadd_rel_eq_add:
  assumes m: "m \<in> nat" and [simp]: "n \<in> nat" shows"m \<oplus>r n = m #+ n"
  using m
proof (induct m)
  case 0 thus ?case 
    using transM[OF _ M_nat] 
    by (auto simp add: nat_into_Card_rel)
next
  case (succ m) thus ?case 
    using transM[OF _ M_nat]
    by (simp add: cadd_succ_lemma nat_into_Card_rel Card_rel_cardinal_rel_eq)
qed


subsection\<open>Cardinal multiplication\<close>

subsubsection\<open>Cardinal multiplication is commutative\<close>

lemma prod_commute_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> A*B \<approx>r B*A"
apply (simp add: def_eqpoll_rel)
apply (rule rexI)
apply (rule_tac c = "%<x,y>.<y,x>" and d = "%<x,y>.<y,x>" in lam_bijective,
       auto)
  apply(rule_tac lam_closed, auto intro:swap_replacement dest:transM)
done

lemma cmult_commute: "M(i) \<Longrightarrow> M(j) \<Longrightarrow> i \<otimes>r j = j \<otimes>r i"
apply (unfold def_cmult_rel)
  apply (rule prod_commute_eqpoll_rel [THEN cardinal_rel_cong], simp_all)
done

subsubsection\<open>Cardinal multiplication is associative\<close>

lemma prod_assoc_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> M(C) \<Longrightarrow> (A*B)*C \<approx>r A*(B*C)"
apply (simp add: def_eqpoll_rel)
apply (rule rexI)
apply (rule prod_assoc_bij)
  apply(rule_tac lam_closed, auto intro:assoc_replacement dest:transM)
done


text\<open>Unconditional version requires AC\<close>
lemma well_ord_cmult_rel_assoc:
  assumes i: "well_ord(i,ri)" and j: "well_ord(j,rj)" and k: "well_ord(k,rk)"
    and
    types: "M(i)" "M(ri)" "M(j)" "M(rj)" "M(k)" "M(rk)"
  shows "(i \<otimes>r j) \<otimes>r k = i \<otimes>r (j \<otimes>r k)"
proof (simp add: assms def_cmult_rel, rule cardinal_rel_cong)
  have "|i * j|r * k \<approx>r (i * j) * k"
    by (auto intro!: prod_eqpoll_rel_cong 
        well_ord_cardinal_rel_eqpoll_rel eqpoll_rel_refl 
        well_ord_rmult i j simp add:types) 
  also have "...  \<approx>r i * (j * k)"
    by (rule prod_assoc_eqpoll_rel, simp_all add:types)
  also have "...  \<approx>r i * |j * k|r"
    by (blast intro: prod_eqpoll_rel_cong well_ord_cardinal_rel_eqpoll_rel 
        eqpoll_rel_refl well_ord_rmult j k eqpoll_rel_sym types)
  finally show "|i * j|r * k \<approx>r i * |j * k|r" by (simp add:types)
qed (simp_all add:types)


subsubsection\<open>Cardinal multiplication distributes over addition\<close>

lemma sum_prod_distrib_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> M(C) \<Longrightarrow> (A+B)*C \<approx>r (A*C)+(B*C)"
apply (simp add: def_eqpoll_rel)
apply (rule rexI)
   apply (rule sum_prod_distrib_bij)
  apply(rule_tac lam_closed, auto intro:case_replacement5 dest:transM)
done


lemma well_ord_cadd_cmult_distrib:
  assumes i: "well_ord(i,ri)" and j: "well_ord(j,rj)" and k: "well_ord(k,rk)"
    and
    types: "M(i)" "M(ri)" "M(j)" "M(rj)" "M(k)" "M(rk)"
  shows "(i \<oplus>r j) \<otimes>r k = (i \<otimes>r k) \<oplus>r (j \<otimes>r k)"
proof (simp add: assms def_cadd_rel def_cmult_rel, rule cardinal_rel_cong)
  have "|i + j|r * k \<approx>r (i + j) * k"
    by (blast intro: prod_eqpoll_rel_cong well_ord_cardinal_rel_eqpoll_rel
        eqpoll_rel_refl well_ord_radd i j types)
  also have "...  \<approx>r i * k + j * k"
    by (rule sum_prod_distrib_eqpoll_rel) (simp_all add:types)
  also have "...  \<approx>r |i * k|r + |j * k|r"
    by (blast intro: sum_eqpoll_rel_cong well_ord_cardinal_rel_eqpoll_rel
        well_ord_rmult i j k eqpoll_rel_sym types)
  finally show "|i + j|r * k \<approx>r |i * k|r + |j * k|r" by (simp add:types)
qed (simp_all add:types)


subsubsection\<open>Multiplication by 0 yields 0\<close>

lemma prod_0_eqpoll_rel: "M(A) \<Longrightarrow> 0*A \<approx>r 0"
apply (simp add: def_eqpoll_rel)
apply (rule rexI)
apply (rule lam_bijective, auto)
done

lemma cmult_rel_0 [simp]: "M(i) \<Longrightarrow> 0 \<otimes>r i = 0"
by (simp add: def_cmult_rel prod_0_eqpoll_rel [THEN cardinal_rel_cong])

subsubsection\<open>1 is the identity for multiplication\<close>

lemma prod_singleton_eqpoll_rel: "M(x) \<Longrightarrow> M(A) \<Longrightarrow> {x}*A \<approx>r A"
apply (simp add: def_eqpoll_rel)
apply (rule rexI)
   apply (rule singleton_prod_bij [THEN bij_converse_bij])
  apply (rule converse_closed)
  apply(rule_tac lam_closed, auto intro:prepend_replacement dest:transM)
done

lemma cmult_rel_1 [simp]: "Card_rel(K) \<Longrightarrow> M(K) \<Longrightarrow> 1 \<otimes>r K = K"
apply (simp add: def_cmult_rel succ_def)
apply (simp add: prod_singleton_eqpoll_rel[THEN cardinal_rel_cong] Card_rel_cardinal_rel_eq)
done

subsection\<open>Some inequalities for multiplication\<close>

lemma prod_square_lepoll_rel: "M(A) \<Longrightarrow> A \<lesssim>r A*A"
apply (simp add:def_lepoll_rel inj_def)
apply (rule_tac x = "\<lambda>x\<in>A. <x,x>" in rexI, simp)
  apply(rule_tac lam_closed, auto intro:id_replacement dest:transM)
done

(*Could probably weaken the premise to well_ord(K,r), or remove using AC*)
lemma cmult_rel_square_le: "Card_rel(K) \<Longrightarrow> M(K) \<Longrightarrow> K \<le> K \<otimes>r K"
apply (unfold def_cmult_rel)
apply (rule le_trans)
apply (rule_tac [2] well_ord_lepoll_rel_imp_Card_rel_le)
       apply (rule_tac [3] prod_square_lepoll_rel)
apply (simp add: le_refl Card_rel_is_Ord Card_rel_cardinal_rel_eq)
      apply (blast intro: well_ord_rmult well_ord_Memrel Card_rel_is_Ord)
  apply simp_all
done

subsubsection\<open>Multiplication by a non-zero cardinal\<close>

lemma prod_lepoll_rel_self: "b \<in> B \<Longrightarrow> M(b) \<Longrightarrow> M(B) \<Longrightarrow> M(A) \<Longrightarrow> A \<lesssim>r A*B"
apply (simp add: def_lepoll_rel inj_def)
apply (rule_tac x = "\<lambda>x\<in>A. <x,b>" in rexI, simp)
  apply(rule_tac lam_closed, auto intro:pospend_replacement dest:transM)
done

(*Could probably weaken the premises to well_ord(K,r), or removing using AC*)
lemma cmult_rel_le_self:
    "[| Card_rel(K);  Ord(L);  0<L; M(K);M(L) |] ==> K \<le> (K \<otimes>r L)"
apply (unfold def_cmult_rel)
apply (rule le_trans [OF Card_rel_cardinal_rel_le well_ord_lepoll_rel_imp_Card_rel_le])
  apply assumption apply simp
 apply (blast intro: well_ord_rmult well_ord_Memrel Card_rel_is_Ord)
apply (auto intro: prod_lepoll_rel_self ltD)
done

subsubsection\<open>Monotonicity of multiplication\<close>

lemma prod_lepoll_rel_mono:
     "[| A \<lesssim>r C;  B \<lesssim>r D; M(A); M(B); M(C); M(D)|] ==> A * B  \<lesssim>r  C * D"
apply (simp add:def_lepoll_rel)
apply (elim rexE)
apply (rule_tac x = "lam <w,y>:A*B. <f`w, fa`y>" in rexI)
apply (rule_tac d = "%<w,y>. <converse (f) `w, converse (fa) `y>"
       in lam_injective)
    apply (typecheck add: inj_is_fun, auto)
  apply(rule_tac lam_closed, auto intro:prod_fun_replacement dest:transM)
done

lemma cmult_rel_le_mono:
    "[| K' \<le> K;  L' \<le> L;M(K');M(K);M(L');M(L) |] ==> (K' \<otimes>r L') \<le> (K \<otimes>r L)"
apply (unfold def_cmult_rel)
apply (safe dest!: le_subset_iff [THEN iffD1])
apply (rule well_ord_lepoll_rel_imp_Card_rel_le)
 apply (blast intro: well_ord_rmult well_ord_Memrel)
apply (auto intro: prod_lepoll_rel_mono subset_imp_lepoll_rel)
done

subsection\<open>Multiplication of finite cardinals is "ordinary" multiplication\<close>

lemma prod_succ_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> succ(A)*B \<approx>r B + A*B"
apply (simp add: def_eqpoll_rel)
apply (rule rexI)
apply (rule_tac c = "%<x,y>. if x=A then Inl (y) else Inr (<x,y>)"
            and d = "case (%y. <A,y>, %z. z)" in lam_bijective)
apply safe
          apply (simp_all add: succI2 if_type mem_imp_not_eq)
  apply(rule_tac lam_closed, auto intro:Inl_replacement2 dest:transM)
done

(*Unconditional version requires AC*)
lemma cmult_rel_succ_lemma:
    "[| Ord(m);  Ord(n) ; M(m); M(n) |] ==> succ(m) \<otimes>r n = n \<oplus>r (m \<otimes>r n)"
apply (simp add: def_cmult_rel def_cadd_rel)
apply (rule prod_succ_eqpoll_rel [THEN cardinal_rel_cong, THEN trans], simp_all)
apply (rule cardinal_rel_cong [symmetric], simp_all)
apply (rule sum_eqpoll_rel_cong [OF eqpoll_rel_refl well_ord_cardinal_rel_eqpoll_rel], assumption)
        apply (blast intro: well_ord_rmult well_ord_Memrel)
  apply simp_all
done

lemma nat_cmult_rel_eq_mult: "[| m \<in> nat;  n \<in> nat |] ==> m \<otimes>r n = m#*n"
  using transM[OF _ M_nat]
apply (induct_tac m)
apply (simp_all add: cmult_rel_succ_lemma nat_cadd_rel_eq_add)
done

lemma cmult_rel_2: "Card_rel(n) \<Longrightarrow> M(n) \<Longrightarrow> 2 \<otimes>r n = n \<oplus>r n"
  by (simp add: cmult_rel_succ_lemma Card_rel_is_Ord cadd_rel_commute [of _ 0])

lemma sum_lepoll_rel_prod:
  assumes C: "2 \<lesssim>r C" and
    types:"M(C)" "M(B)"
  shows "B+B \<lesssim>r C*B"
proof -
  have "B+B \<lesssim>r 2*B"
    by (simp add: sum_eq_2_times types)
  also have "... \<lesssim>r C*B"
    by (blast intro: prod_lepoll_rel_mono lepoll_rel_refl C types)
  finally show "B+B \<lesssim>r C*B" by (simp_all add:types)
qed

lemma lepoll_imp_sum_lepoll_prod: "[| A \<lesssim>r B; 2 \<lesssim>r A; M(A) ;M(B) |] ==> A+B \<lesssim>r A*B"
by (blast intro: sum_lepoll_rel_mono sum_lepoll_rel_prod lepoll_rel_trans lepoll_rel_refl)

end (* M_cardinals *)

subsection\<open>Infinite Cardinals are Limit Ordinals\<close>

(*This proof is modelled upon one assuming nat<=A, with injection
  \<lambda>z\<in>cons(u,A). if z=u then 0 else if z \<in> nat then succ(z) else z
  and inverse %y. if y \<in> nat then nat_case(u, %z. z, y) else y.  \
  If f \<in> inj(nat,A) then range(f) behaves like the natural numbers.*)


context M_cardinal_arith
begin

lemma nat_cons_lepoll_rel: "nat \<lesssim>r A \<Longrightarrow> M(A) \<Longrightarrow> M(u) ==> cons(u,A) \<lesssim>r A"
apply (simp add: def_lepoll_rel)
apply (erule rexE)
apply (rule_tac x =
          "\<lambda>z\<in>cons (u,A).
             if z=u then f`0
             else if z \<in> range (f) then f`succ (converse (f) `z) else z"
       in rexI)
apply (rule_tac d =
          "%y. if y \<in> range(f) then nat_case (u, %z. f`z, converse(f) `y)
                              else y"
       in lam_injective)
apply (fast intro!: if_type apply_type intro: inj_is_fun inj_converse_fun)
apply (simp add: inj_is_fun [THEN apply_rangeI]
                 inj_converse_fun [THEN apply_rangeI]
                 inj_converse_fun [THEN apply_funtype])
proof -
  fix f
  assume "M(A)" "M(f)" "M(u)"
  then
  show "M(\<lambda>z\<in>cons(u, A). if z = u then f ` 0 else if z \<in> range(f) then f ` succ(converse(f) ` z) else z)"
  using if_then_range_replacement transM[OF _ \<open>M(A)\<close>]
  by (rule_tac lam_closed, auto)
qed

lemma nat_cons_eqpoll_rel: "nat \<lesssim>r A ==> M(A) \<Longrightarrow> M(u) \<Longrightarrow> cons(u,A) \<approx>r A"
apply (erule nat_cons_lepoll_rel [THEN eqpoll_relI], assumption+)
apply (rule subset_consI [THEN subset_imp_lepoll_rel], simp_all)
done

lemma nat_succ_eqpoll_rel: "nat \<subseteq> A ==> M(A) \<Longrightarrow> succ(A) \<approx>r A"
apply (unfold succ_def)
apply (erule subset_imp_lepoll_rel [THEN nat_cons_eqpoll_rel], simp_all)
done

lemma InfCard_rel_nat: "InfCard_r(nat)"
apply (simp add: def_InfCard_rel)
apply (blast intro: Card_rel_nat Card_rel_is_Ord)
done

lemma InfCard_rel_is_Card_rel: "M(K) \<Longrightarrow> InfCard_r(K) \<Longrightarrow> Card_rel(K)"
apply (simp add: def_InfCard_rel)
done

lemma InfCard_rel_Un:
    "[| InfCard_r(K);  Card_rel(L); M(K); M(L) |] ==> InfCard_r(K \<union> L)"
apply (simp add: def_InfCard_rel)
apply (simp add: Card_rel_Un Un_upper1_le [THEN [2] le_trans]  Card_rel_is_Ord)
done

lemma InfCard_is_Limit: "InfCard_r(K) ==> M(K) \<Longrightarrow> Limit(K)"
apply (simp add: def_InfCard_rel)
apply (erule conjE)
apply (frule Card_rel_is_Ord, assumption)
apply (rule ltI [THEN non_succ_LimitI])
apply (erule le_imp_subset [THEN subsetD])
apply (safe dest!: Limit_nat [THEN Limit_le_succD])
  apply (unfold Card_rel_def)
  apply (simp add: def_Card_rel[unfolded Card_rel_def])
  apply (drule trans)
apply (erule le_imp_subset [THEN nat_succ_eqpoll_rel, THEN cardinal_rel_cong], simp_all)
apply (erule Ord_cardinal_rel_le [THEN lt_trans2, THEN lt_irrefl], assumption)
apply (rule le_eqI) prefer 2
apply (rule Ord_cardinal_rel, assumption+)
done

(*
(*** An infinite cardinal equals its square (Kunen, Thm 10.12, page 29) ***)

(*A general fact about ordermap*)
lemma ordermap_eqpoll_pred:
    "[| well_ord(A,r);  x \<in> A |] ==> ordermap(A,r)`x \<approx>r Order.pred(A,x,r)"
apply (unfold eqpoll_def)
apply (rule exI)
apply (simp add: ordermap_eq_image well_ord_is_wf)
apply (erule ordermap_bij [THEN bij_is_inj, THEN restrict_bij,
                           THEN bij_converse_bij])
apply (rule pred_subset)
done

subsubsection\<open>Establishing the well-ordering\<close>

lemma well_ord_csquare:
  assumes K: "Ord(K)" shows "well_ord(K*K, csquare_rel(K))"
proof (unfold csquare_rel_def, rule well_ord_rvimage)
  show "(\<lambda>\<langle>x,y\<rangle>\<in>K \<times> K. \<langle>x \<union> y, x, y\<rangle>) \<in> inj(K \<times> K, K \<times> K \<times> K)" using K
    by (force simp add: inj_def intro: lam_type Un_least_lt [THEN ltD] ltI)
next
  show "well_ord(K \<times> K \<times> K, rmult(K, Memrel(K), K \<times> K, rmult(K, Memrel(K), K, Memrel(K))))"
    using K by (blast intro: well_ord_rmult well_ord_Memrel)
qed

subsubsection\<open>Characterising initial segments of the well-ordering\<close>

lemma csquareD:
 "[| <<x,y>, <z,z>> \<in> csquare_rel(K);  x<K;  y<K;  z<K |] ==> x \<le> z & y \<le> z"
apply (unfold csquare_rel_def)
apply (erule rev_mp)
apply (elim ltE)
apply (simp add: rvimage_iff Un_absorb Un_least_mem_iff ltD)
apply (safe elim!: mem_irrefl intro!: Un_upper1_le Un_upper2_le)
apply (simp_all add: lt_def succI2)
done

lemma pred_csquare_subset:
    "z<K ==> Order.pred(K*K, <z,z>, csquare_rel(K)) \<subseteq> succ(z)*succ(z)"
apply (unfold Order.pred_def)
apply (safe del: SigmaI dest!: csquareD)
apply (unfold lt_def, auto)
done

lemma csquare_ltI:
 "[| x<z;  y<z;  z<K |] ==>  <<x,y>, <z,z>> \<in> csquare_rel(K)"
apply (unfold csquare_rel_def)
apply (subgoal_tac "x<K & y<K")
 prefer 2 apply (blast intro: lt_trans)
apply (elim ltE)
apply (simp add: rvimage_iff Un_absorb Un_least_mem_iff ltD)
done

(*Part of the traditional proof.  UNUSED since it's harder to prove & apply *)
lemma csquare_or_eqI:
 "[| x \<le> z;  y \<le> z;  z<K |] ==> <<x,y>, <z,z>> \<in> csquare_rel(K) | x=z & y=z"
apply (unfold csquare_rel_def)
apply (subgoal_tac "x<K & y<K")
 prefer 2 apply (blast intro: lt_trans1)
apply (elim ltE)
apply (simp add: rvimage_iff Un_absorb Un_least_mem_iff ltD)
apply (elim succE)
apply (simp_all add: subset_Un_iff [THEN iff_sym]
                     subset_Un_iff2 [THEN iff_sym] OrdmemD)
done

subsubsection\<open>The cardinality of initial segments\<close>

lemma ordermap_z_lt:
      "[| Limit(K);  x<K;  y<K;  z=succ(x \<union> y) |] ==>
          ordermap(K*K, csquare_rel(K)) ` <x,y> <
          ordermap(K*K, csquare_rel(K)) ` <z,z>"
apply (subgoal_tac "z<K & well_ord (K*K, csquare_rel (K))")
prefer 2 apply (blast intro!: Un_least_lt Limit_has_succ
                              Limit_is_Ord [THEN well_ord_csquare], clarify)
apply (rule csquare_ltI [THEN ordermap_mono, THEN ltI])
apply (erule_tac [4] well_ord_is_wf)
apply (blast intro!: Un_upper1_le Un_upper2_le Ord_ordermap elim!: ltE)+
done

text\<open>Kunen: "each \<^term>\<open>\<langle>x,y\<rangle> \<in> K \<times> K\<close> has no more than \<^term>\<open>z \<times> z\<close> predecessors..." (page 29)\<close>
lemma ordermap_csquare_le:
  assumes K: "Limit(K)" and x: "x<K" and y: " y<K"
  defines "z \<equiv> succ(x \<union> y)"
  shows "|ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x,y\<rangle>| \<le> |succ(z)| \<otimes> |succ(z)|"
proof (unfold cmult_def, rule well_ord_lepoll_imp_Card_le)
  show "well_ord(|succ(z)| \<times> |succ(z)|,
                 rmult(|succ(z)|, Memrel(|succ(z)|), |succ(z)|, Memrel(|succ(z)|)))"
    by (blast intro: Ord_cardinal well_ord_Memrel well_ord_rmult)
next
  have zK: "z<K" using x y K z_def
    by (blast intro: Un_least_lt Limit_has_succ)
  hence oz: "Ord(z)" by (elim ltE)
  have "ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x,y\<rangle> \<lesssim>r ordermap(K \<times> K, csquare_rel(K)) ` \<langle>z,z\<rangle>"
    using z_def
    by (blast intro: ordermap_z_lt leI le_imp_lepoll K x y)
  also have "... \<approx>r  Order.pred(K \<times> K, \<langle>z,z\<rangle>, csquare_rel(K))"
    proof (rule ordermap_eqpoll_pred)
      show "well_ord(K \<times> K, csquare_rel(K))" using K
        by (rule Limit_is_Ord [THEN well_ord_csquare])
    next
      show "\<langle>z, z\<rangle> \<in> K \<times> K" using zK
        by (blast intro: ltD)
    qed
  also have "...  \<lesssim>r succ(z) \<times> succ(z)" using zK
    by (rule pred_csquare_subset [THEN subset_imp_lepoll])
  also have "... \<approx>r |succ(z)| \<times> |succ(z)|" using oz
    by (blast intro: prod_eqpoll_cong Ord_succ Ord_cardinal_eqpoll eqpoll_sym)
  finally show "ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x,y\<rangle> \<lesssim>r |succ(z)| \<times> |succ(z)|" .
qed

text\<open>Kunen: "... so the order type is \<open>\<le>\<close> K"\<close>
lemma ordertype_csquare_le:
  assumes IK: "InfCard(K)" and eq: "\<And>y. y\<in>K \<Longrightarrow> InfCard(y) \<Longrightarrow> y \<otimes> y = y"
  shows "ordertype(K*K, csquare_rel(K)) \<le> K"
proof -
  have  CK: "Card(K)" using IK by (rule InfCard_is_Card)
  hence OK: "Ord(K)"  by (rule Card_is_Ord)
  moreover have "Ord(ordertype(K \<times> K, csquare_rel(K)))" using OK
    by (rule well_ord_csquare [THEN Ord_ordertype])
  ultimately show ?thesis
  proof (rule all_lt_imp_le)
    fix i
    assume i: "i < ordertype(K \<times> K, csquare_rel(K))"
    hence Oi: "Ord(i)" by (elim ltE)
    obtain x y where x: "x \<in> K" and y: "y \<in> K"
                 and ieq: "i = ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x,y\<rangle>"
      using i by (auto simp add: ordertype_unfold elim: ltE)
    hence xy: "Ord(x)" "Ord(y)" "x < K" "y < K" using OK
      by (blast intro: Ord_in_Ord ltI)+
    hence ou: "Ord(x \<union> y)"
      by (simp add: Ord_Un)
    show "i < K"
      proof (rule Card_lt_imp_lt [OF _ Oi CK])
        have "|i| \<le> |succ(succ(x \<union> y))| \<otimes> |succ(succ(x \<union> y))|" using IK xy
          by (auto simp add: ieq intro: InfCard_is_Limit [THEN ordermap_csquare_le])
        moreover have "|succ(succ(x \<union> y))| \<otimes> |succ(succ(x \<union> y))| < K"
          proof (cases rule: Ord_linear2 [OF ou Ord_nat])
            assume "x \<union> y < nat"
            hence "|succ(succ(x \<union> y))| \<otimes> |succ(succ(x \<union> y))| \<in> nat"
              by (simp add: lt_def nat_cmult_eq_mult nat_succI mult_type
                         nat_into_Card [THEN Card_cardinal_eq]  Ord_nat)
            also have "... \<subseteq> K" using IK
              by (simp add: InfCard_def le_imp_subset)
            finally show "|succ(succ(x \<union> y))| \<otimes> |succ(succ(x \<union> y))| < K"
              by (simp add: ltI OK)
          next
            assume natxy: "nat \<le> x \<union> y"
            hence seq: "|succ(succ(x \<union> y))| = |x \<union> y|" using xy
              by (simp add: le_imp_subset nat_succ_eqpoll [THEN cardinal_cong] le_succ_iff)
            also have "... < K" using xy
              by (simp add: Un_least_lt Ord_cardinal_le [THEN lt_trans1])
            finally have "|succ(succ(x \<union> y))| < K" .
            moreover have "InfCard(|succ(succ(x \<union> y))|)" using xy natxy
              by (simp add: seq InfCard_def Card_cardinal nat_le_cardinal)
            ultimately show ?thesis  by (simp add: eq ltD)
          qed
        ultimately show "|i| < K" by (blast intro: lt_trans1)
    qed
  qed
qed

(*Main result: Kunen's Theorem 10.12*)
lemma InfCard_csquare_eq:
  assumes IK: "InfCard(K)" shows "InfCard(K) ==> K \<otimes> K = K"
proof -
  have  OK: "Ord(K)" using IK by (simp add: Card_is_Ord InfCard_is_Card)
  show "InfCard(K) ==> K \<otimes> K = K" using OK
  proof (induct rule: trans_induct)
    case (step i)
    show "i \<otimes> i = i"
    proof (rule le_anti_sym)
      have "|i \<times> i| = |ordertype(i \<times> i, csquare_rel(i))|"
        by (rule cardinal_cong,
          simp add: step.hyps well_ord_csquare [THEN ordermap_bij, THEN bij_imp_eqpoll])
      hence "i \<otimes> i \<le> ordertype(i \<times> i, csquare_rel(i))"
        by (simp add: step.hyps cmult_def Ord_cardinal_le well_ord_csquare [THEN Ord_ordertype])
      moreover
      have "ordertype(i \<times> i, csquare_rel(i)) \<le> i" using step
        by (simp add: ordertype_csquare_le)
      ultimately show "i \<otimes> i \<le> i" by (rule le_trans)
    next
      show "i \<le> i \<otimes> i" using step
        by (blast intro: cmult_square_le InfCard_is_Card)
    qed
  qed
qed

(*Corollary for arbitrary well-ordered sets (all sets, assuming AC)*)
lemma well_ord_InfCard_square_eq:
  assumes r: "well_ord(A,r)" and I: "InfCard(|A|)" shows "A \<times> A \<approx>r A"
proof -
  have "A \<times> A \<approx>r |A| \<times> |A|"
    by (blast intro: prod_eqpoll_cong well_ord_cardinal_eqpoll eqpoll_sym r)
  also have "... \<approx>r A"
    proof (rule well_ord_cardinal_eqE [OF _ r])
      show "well_ord(|A| \<times> |A|, rmult(|A|, Memrel(|A|), |A|, Memrel(|A|)))"
        by (blast intro: Ord_cardinal well_ord_rmult well_ord_Memrel r)
    next
      show "||A| \<times> |A|| = |A|" using InfCard_csquare_eq I
        by (simp add: cmult_def)
    qed
  finally show ?thesis .
qed

lemma InfCard_square_eqpoll: "InfCard(K) ==> K \<times> K \<approx>r K"
apply (rule well_ord_InfCard_square_eq)
 apply (erule InfCard_is_Card [THEN Card_is_Ord, THEN well_ord_Memrel])
apply (simp add: InfCard_is_Card [THEN Card_cardinal_eq])
done

lemma Inf_Card_is_InfCard: "[| Card(i); ~ Finite(i) |] ==> InfCard(i)"
by (simp add: InfCard_def Card_is_Ord [THEN nat_le_infinite_Ord])

subsubsection\<open>Toward's Kunen's Corollary 10.13 (1)\<close>

lemma InfCard_le_cmult_eq: "[| InfCard(K);  L \<le> K;  0<L |] ==> K \<otimes> L = K"
apply (rule le_anti_sym)
 prefer 2
 apply (erule ltE, blast intro: cmult_le_self InfCard_is_Card)
apply (frule InfCard_is_Card [THEN Card_is_Ord, THEN le_refl])
apply (rule cmult_le_mono [THEN le_trans], assumption+)
apply (simp add: InfCard_csquare_eq)
done

(*Corollary 10.13 (1), for cardinal multiplication*)
lemma InfCard_cmult_eq: "[| InfCard(K);  InfCard(L) |] ==> K \<otimes> L = K \<union> L"
apply (rule_tac i = K and j = L in Ord_linear_le)
apply (typecheck add: InfCard_is_Card Card_is_Ord)
apply (rule cmult_commute [THEN ssubst])
apply (rule Un_commute [THEN ssubst])
apply (simp_all add: InfCard_is_Limit [THEN Limit_has_0] InfCard_le_cmult_eq
                     subset_Un_iff2 [THEN iffD1] le_imp_subset)
done

lemma InfCard_cdouble_eq: "InfCard(K) ==> K \<oplus>r K = K"
apply (simp add: cmult_2 [symmetric] InfCard_is_Card cmult_commute)
apply (simp add: InfCard_le_cmult_eq InfCard_is_Limit Limit_has_0 Limit_has_succ)
done

(*Corollary 10.13 (1), for cardinal addition*)
lemma InfCard_le_cadd_eq: "[| InfCard(K);  L \<le> K |] ==> K \<oplus>r L = K"
apply (rule le_anti_sym)
 prefer 2
 apply (erule ltE, blast intro: cadd_le_self InfCard_is_Card)
apply (frule InfCard_is_Card [THEN Card_is_Ord, THEN le_refl])
apply (rule cadd_le_mono [THEN le_trans], assumption+)
apply (simp add: InfCard_cdouble_eq)
done

lemma InfCard_cadd_eq: "[| InfCard(K);  InfCard(L) |] ==> K \<oplus>r L = K \<union> L"
apply (rule_tac i = K and j = L in Ord_linear_le)
apply (typecheck add: InfCard_is_Card Card_is_Ord)
apply (rule cadd_commute [THEN ssubst])
apply (rule Un_commute [THEN ssubst])
apply (simp_all add: InfCard_le_cadd_eq subset_Un_iff2 [THEN iffD1] le_imp_subset)
done

(*The other part, Corollary 10.13 (2), refers to the cardinality of the set
  of all n-tuples of elements of K.  A better version for the Isabelle theory
  might be  InfCard(K) ==> |list(K)| = K.
*)

subsection\<open>For Every Cardinal Number There Exists A Greater One\<close>

text\<open>This result is Kunen's Theorem 10.16, which would be trivial using AC\<close>

lemma Ord_jump_cardinal: "Ord(jump_cardinal(K))"
apply (unfold jump_cardinal_def)
apply (rule Ord_is_Transset [THEN [2] OrdI])
 prefer 2 apply (blast intro!: Ord_ordertype)
apply (unfold Transset_def)
apply (safe del: subsetI)
apply (simp add: ordertype_pred_unfold, safe)
apply (rule UN_I)
apply (rule_tac [2] ReplaceI)
   prefer 4 apply (blast intro: well_ord_subset elim!: predE)+
done

(*Allows selective unfolding.  Less work than deriving intro/elim rules*)
lemma jump_cardinal_iff:
     "i \<in> jump_cardinal(K) \<longleftrightarrow>
      (\<exists>r X. r \<subseteq> K*K & X \<subseteq> K & well_ord(X,r) & i = ordertype(X,r))"
apply (unfold jump_cardinal_def)
apply (blast del: subsetI)
done

(*The easy part of Theorem 10.16: jump_cardinal(K) exceeds K*)
lemma K_lt_jump_cardinal: "Ord(K) ==> K < jump_cardinal(K)"
apply (rule Ord_jump_cardinal [THEN [2] ltI])
apply (rule jump_cardinal_iff [THEN iffD2])
apply (rule_tac x="Memrel(K)" in exI)
apply (rule_tac x=K in exI)
apply (simp add: ordertype_Memrel well_ord_Memrel)
apply (simp add: Memrel_def subset_iff)
done

(*The proof by contradiction: the bijection f yields a wellordering of X
  whose ordertype is jump_cardinal(K).  *)
lemma Card_jump_cardinal_lemma:
     "[| well_ord(X,r);  r \<subseteq> K * K;  X \<subseteq> K;
         f \<in> bij(ordertype(X,r), jump_cardinal(K)) |]
      ==> jump_cardinal(K) \<in> jump_cardinal(K)"
apply (subgoal_tac "f O ordermap (X,r) \<in> bij (X, jump_cardinal (K))")
 prefer 2 apply (blast intro: comp_bij ordermap_bij)
apply (rule jump_cardinal_iff [THEN iffD2])
apply (intro exI conjI)
apply (rule subset_trans [OF rvimage_type Sigma_mono], assumption+)
apply (erule bij_is_inj [THEN well_ord_rvimage])
apply (rule Ord_jump_cardinal [THEN well_ord_Memrel])
apply (simp add: well_ord_Memrel [THEN [2] bij_ordertype_vimage]
                 ordertype_Memrel Ord_jump_cardinal)
done

(*The hard part of Theorem 10.16: jump_cardinal(K) is itself a cardinal*)
lemma Card_jump_cardinal: "Card(jump_cardinal(K))"
apply (rule Ord_jump_cardinal [THEN CardI])
apply (unfold eqpoll_def)
apply (safe dest!: ltD jump_cardinal_iff [THEN iffD1])
apply (blast intro: Card_jump_cardinal_lemma [THEN mem_irrefl])
done

subsection\<open>Basic Properties of Successor Cardinals\<close>

lemma csucc_basic: "Ord(K) ==> Card(csucc(K)) & K < csucc(K)"
apply (unfold csucc_def)
apply (rule LeastI)
apply (blast intro: Card_jump_cardinal K_lt_jump_cardinal Ord_jump_cardinal)+
done

lemmas Card_csucc = csucc_basic [THEN conjunct1]

lemmas lt_csucc = csucc_basic [THEN conjunct2]

lemma Ord_0_lt_csucc: "Ord(K) ==> 0 < csucc(K)"
by (blast intro: Ord_0_le lt_csucc lt_trans1)

lemma csucc_le: "[| Card(L);  K<L |] ==> csucc(K) \<le> L"
apply (unfold csucc_def)
apply (rule Least_le)
apply (blast intro: Card_is_Ord)+
done

lemma lt_csucc_iff: "[| Ord(i); Card(K) |] ==> i < csucc(K) \<longleftrightarrow> |i| \<le> K"
apply (rule iffI)
apply (rule_tac [2] Card_lt_imp_lt)
apply (erule_tac [2] lt_trans1)
apply (simp_all add: lt_csucc Card_csucc Card_is_Ord)
apply (rule notI [THEN not_lt_imp_le])
apply (rule Card_cardinal [THEN csucc_le, THEN lt_trans1, THEN lt_irrefl], assumption)
apply (rule Ord_cardinal_le [THEN lt_trans1])
apply (simp_all add: Ord_cardinal Card_is_Ord)
done

lemma Card_lt_csucc_iff:
     "[| Card(K'); Card(K) |] ==> K' < csucc(K) \<longleftrightarrow> K' \<le> K"
by (simp add: lt_csucc_iff Card_cardinal_eq Card_is_Ord)

lemma InfCard_csucc: "InfCard(K) ==> InfCard(csucc(K))"
by (simp add: InfCard_def Card_csucc Card_is_Ord
              lt_csucc [THEN leI, THEN [2] le_trans])


subsubsection\<open>Removing elements from a finite set decreases its cardinality\<close>

lemma Finite_imp_cardinal_cons [simp]:
  assumes FA: "Finite(A)" and a: "a\<notin>A" shows "|cons(a,A)| = succ(|A|)"
proof -
  { fix X
    have "Finite(X) ==> a \<notin> X \<Longrightarrow> cons(a,X) \<lesssim>r X \<Longrightarrow> False"
      proof (induct X rule: Finite_induct)
        case 0 thus False  by (simp add: lepoll_0_iff)
      next
        case (cons x Y)
        hence "cons(x, cons(a, Y)) \<lesssim>r cons(x, Y)" by (simp add: cons_commute)
        hence "cons(a, Y) \<lesssim>r Y" using cons        by (blast dest: cons_lepoll_consD)
        thus False using cons by auto
      qed
  }
  hence [simp]: "~ cons(a,A) \<lesssim>r A" using a FA by auto
  have [simp]: "|A| \<approx>r A" using Finite_imp_well_ord [OF FA]
    by (blast intro: well_ord_cardinal_eqpoll)
  have "(\<mu> i. i \<approx>r cons(a, A)) = succ(|A|)"
    proof (rule Least_equality [OF _ _ notI])
      show "succ(|A|) \<approx>r cons(a, A)"
        by (simp add: succ_def cons_eqpoll_cong mem_not_refl a)
    next
      show "Ord(succ(|A|))" by simp
    next
      fix i
      assume i: "i \<le> |A|" "i \<approx>r cons(a, A)"
      have "cons(a, A) \<approx>r i" by (rule eqpoll_sym) (rule i)
      also have "... \<lesssim>r |A|" by (rule le_imp_lepoll) (rule i)
      also have "... \<approx>r A"   by simp
      finally have "cons(a, A) \<lesssim>r A" .
      thus False by simp
    qed
  thus ?thesis by (simp add: cardinal_def)
qed

lemma Finite_imp_succ_cardinal_Diff:
     "[| Finite(A);  a \<in> A |] ==> succ(|A-{a}|) = |A|"
apply (rule_tac b = A in cons_Diff [THEN subst], assumption)
apply (simp add: Finite_imp_cardinal_cons Diff_subset [THEN subset_Finite])
apply (simp add: cons_Diff)
done

lemma Finite_imp_cardinal_Diff: "[| Finite(A);  a \<in> A |] ==> |A-{a}| < |A|"
apply (rule succ_leE)
apply (simp add: Finite_imp_succ_cardinal_Diff)
done

lemma Finite_cardinal_in_nat [simp]: "Finite(A) ==> |A| \<in> nat"
proof (induct rule: Finite_induct)
  case 0 thus ?case by (simp add: cardinal_0)
next
  case (cons x A) thus ?case by (simp add: Finite_imp_cardinal_cons)
qed

lemma card_Un_Int:
     "[|Finite(A); Finite(B)|] ==> |A| #+ |B| = |A \<union> B| #+ |A \<inter> B|"
apply (erule Finite_induct, simp)
apply (simp add: Finite_Int cons_absorb Un_cons Int_cons_left)
done

lemma card_Un_disjoint:
     "[|Finite(A); Finite(B); A \<inter> B = 0|] ==> |A \<union> B| = |A| #+ |B|"
by (simp add: Finite_Un card_Un_Int)

lemma card_partition:
  assumes FC: "Finite(C)"
  shows
     "Finite (\<Union> C) \<Longrightarrow>
        (\<forall>c\<in>C. |c| = k) \<Longrightarrow>
        (\<forall>c1 \<in> C. \<forall>c2 \<in> C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = 0) \<Longrightarrow>
        k #* |C| = |\<Union> C|"
using FC
proof (induct rule: Finite_induct)
  case 0 thus ?case by simp
next
  case (cons x B)
  hence "x \<inter> \<Union>B = 0" by auto
  thus ?case using cons
    by (auto simp add: card_Un_disjoint)
qed
*)

subsubsection\<open>Theorems by Krzysztof Grabczewski, proofs by lcp\<close>

lemma nat_sum_eqpoll_rel_sum:
  assumes m: "m \<in> nat" and n: "n \<in> nat" shows "m + n \<approx>r m #+ n"
proof -
  have "m + n \<approx>r |m+n|r" using m n
    by (blast intro: nat_implies_well_ord well_ord_radd well_ord_cardinal_rel_eqpoll_rel eqpoll_rel_sym)
  also have "... = m #+ n" using m n
    by (simp add: nat_cadd_rel_eq_add [symmetric] def_cadd_rel transM[OF _ M_nat])
  finally show ?thesis .
qed

lemma Ord_nat_subset_into_Card_rel: "[| Ord(i); i \<subseteq> nat |] ==> Card_rel(i)"
by (blast dest: Ord_subset_natD intro: Card_rel_nat nat_into_Card_rel)

end (* M_cardinal_arith *)
end
