section\<open>Interface between set models and Constructibility\<close>

text\<open>This theory provides an interface between Paulson's
relativization results and set models of ZFC. In particular,
it is used to prove that the locale \<^term>\<open>forcing_data\<close> is
a sublocale of all relevant locales in ZF-Constructibility
(\<^term>\<open>M_trivial\<close>, \<^term>\<open>M_basic\<close>, \<^term>\<open>M_eclose\<close>, etc).\<close>

theory Interface
  imports
    Univ_Relative
    Renaming_Auto
    Discipline_Function
begin

declare arity_subset_fm [simp del] arity_ordinal_fm[simp del, arity] arity_transset_fm[simp del]
  FOL_arities[simp del]

abbreviation
  dec10  :: i   ("10") where "10 \<equiv> succ(9)"

abbreviation
  dec11  :: i   ("11") where "11 \<equiv> succ(10)"

abbreviation
  dec12  :: i   ("12") where "12 \<equiv> succ(11)"

abbreviation
  dec13  :: i   ("13") where "13 \<equiv> succ(12)"

abbreviation
  dec14  :: i   ("14") where "14 \<equiv> succ(13)"

definition
  wellfounded_trancl :: "[i=>o,i,i,i] => o" where
  "wellfounded_trancl(M,Z,r,p) \<equiv>
      \<exists>w[M]. \<exists>wx[M]. \<exists>rp[M].
               w \<in> Z & pair(M,w,p,wx) & tran_closure(M,r,rp) & wx \<in> rp"

lemma empty_intf :
  "infinity_ax(M) \<Longrightarrow>
  (\<exists>z[M]. empty(M,z))"
  by (auto simp add: empty_def infinity_ax_def)

lemma Transset_intf :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)

locale M_ZF =
  fixes M
  assumes
    upair_ax:      "upair_ax(##M)" and
    Union_ax:      "Union_ax(##M)" and
    power_ax:      "power_ax(##M)" and
    extensionality:"extensionality(##M)" and
    foundation_ax: "foundation_ax(##M)" and
    infinity_ax:   "infinity_ax(##M)" and
    separation_ax: "\<phi> \<in> formula \<Longrightarrow> env \<in> list(M) \<Longrightarrow>
                    arity(\<phi>) \<le> 1 #+ length(env) \<Longrightarrow>
                    separation(##M,\<lambda>x. sats(M,\<phi>,[x] @ env))" and
    replacement_ax:"\<phi> \<in> formula \<Longrightarrow> env \<in> list(M) \<Longrightarrow>
                    arity(\<phi>) \<le> 2 #+ length(env) \<Longrightarrow>
                    strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,[x,y] @ env))"

locale M_ZF_trans = M_ZF +
  assumes
    trans_M:       "Transset(M)"
begin

lemmas transitivity = Transset_intf[OF trans_M]

subsection\<open>Interface with \<^term>\<open>M_trivial\<close>\<close>

lemma zero_in_M:  "0 \<in> M"
proof -
  from infinity_ax
  have "(\<exists>z[##M]. empty(##M,z))"
    by (rule empty_intf)
  then obtain z where
    zm: "empty(##M,z)"  "z\<in>M"
    by auto
  then
  have "z=0"
    using transitivity empty_def by auto
  with zm show ?thesis
    by simp
qed

lemma separation_in_ctm :
  assumes
    "\<phi> \<in> formula" "env\<in>list(M)"
    "arity(\<phi>) \<le> 1 #+ length(env)" and
    satsQ: "\<And>x. x\<in>M \<Longrightarrow> sats(M,\<phi>,[x]@env) \<longleftrightarrow> Q(x)"
  shows
    "separation(##M,Q)"
  using assms separation_ax
    satsQ trans_M
    separation_cong[of "##M" "\<lambda>y. sats(M,\<phi>,[y]@env)" "Q"]
  by simp

end \<comment> \<open>\<^locale>\<open>M_ZF_trans\<close>\<close>

locale M_ZFC = M_ZF +
  assumes
    choice_ax:"choice_ax(##M)"

locale M_ZFC_trans = M_ZF_trans + M_ZFC

sublocale M_ZF_trans \<subseteq> M_trans "##M"
  using transitivity zero_in_M exI[of "\<lambda>x. x\<in>M"]
  by unfold_locales simp_all

sublocale M_ZF_trans \<subseteq> M_trivial "##M"
  using trans_M upair_ax Union_ax by unfold_locales

subsection\<open>Interface with \<^term>\<open>M_basic\<close>\<close>

definition Intersection where
 "Intersection(N,B,x) \<equiv> (\<forall>y[N]. y\<in>B \<longrightarrow> x\<in>y)"

synthesize "Intersection" from_definition "Intersection" assuming "nonempty"
arity_theorem for "Intersection_fm"

definition CartProd where
 "CartProd(N,B,C,z) \<equiv> (\<exists>x[N]. x\<in>B \<and> (\<exists>y[N]. y\<in>C \<and> pair(N,x,y,z)))"

synthesize "CartProd" from_definition "CartProd" assuming "nonempty"
arity_theorem for "CartProd_fm"

definition Image where
 "Image(N,B,r,y) \<equiv> (\<exists>p[N]. p\<in>r & (\<exists>x[N]. x\<in>B & pair(N,x,y,p)))"

synthesize "Image" from_definition "Image" assuming "nonempty"
arity_theorem for "Image_fm"

definition Converse where
 "Converse(N,R,z) \<equiv> \<exists>p[N]. p\<in>R & (\<exists>x[N].\<exists>y[N]. pair(N,x,y,p) & pair(N,y,x,z))"

synthesize "Converse" from_definition "Converse" assuming "nonempty"
arity_theorem for "Converse_fm"

definition Restrict where
 "Restrict(N,A,z) \<equiv> \<exists>x[N]. x\<in>A & (\<exists>y[N]. pair(N,x,y,z))"

synthesize "Restrict" from_definition "Restrict" assuming "nonempty"
arity_theorem for "Restrict_fm"

definition Comp where
 "Comp(N,R,S,xz) \<equiv> \<exists>x[N]. \<exists>y[N]. \<exists>z[N]. \<exists>xy[N]. \<exists>yz[N].
              pair(N,x,z,xz) & pair(N,x,y,xy) & pair(N,y,z,yz) & xy\<in>S & yz\<in>R"

synthesize "Comp" from_definition "Comp" assuming "nonempty"
arity_theorem for "Comp_fm"

definition Pred where
 "Pred(N,R,X,y) \<equiv> \<exists>p[N]. p\<in>R & pair(N,y,X,p)"

synthesize "Pred" from_definition "Pred" assuming "nonempty"
arity_theorem for "Pred_fm"

definition is_Memrel where
 "is_Memrel(N,z) \<equiv> \<exists>x[N]. \<exists>y[N]. pair(N,x,y,z) & x \<in> y"

synthesize "is_Memrel" from_definition "is_Memrel" assuming "nonempty"
arity_theorem for "is_Memrel_fm"

definition RecFun where
 "RecFun(N,r,f,g,a,b,x) \<equiv> \<exists>xa[N]. \<exists>xb[N].
                    pair(N,x,a,xa) & xa \<in> r & pair(N,x,b,xb) & xb \<in> r &
                    (\<exists>fx[N]. \<exists>gx[N]. fun_apply(N,f,x,fx) & fun_apply(N,g,x,gx) &
                                     fx \<noteq> gx)"

synthesize "RecFun" from_definition "RecFun" assuming "nonempty"
arity_theorem for "RecFun_fm"

arity_theorem for "rtran_closure_mem_fm"

context M_ZF_trans
begin

lemma inter_sep_intf :
  assumes "A\<in>M"
  shows "separation(##M,\<lambda>x . \<forall>y\<in>M . y\<in>A \<longrightarrow> x\<in>y)"
  using assms separation_in_ctm[of "Intersection_fm(1,0)" "[A]" "Intersection(##M,A)"]
   Intersection_iff_sats[of 1 "[_,A]" A 0 _ M] arity_Intersection_fm Intersection_fm_type
   ord_simp_union nonempty
  unfolding Intersection_def
  by simp

lemma diff_sep_intf :
  assumes "B\<in>M"
  shows "separation(##M,\<lambda>x . x\<notin>B)"
  using assms separation_in_ctm[of "Neg(Member(0,1))" "[B]" "\<lambda>x . x\<notin>B"] ord_simp_union
  by simp

lemma cartprod_sep_intf :
  assumes "A\<in>M" and "B\<in>M"
  shows "separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A \<and> (\<exists>y\<in>M. y\<in>B \<and> pair(##M,x,y,z)))"
  using assms separation_in_ctm[of "CartProd_fm(1,2,0)" "[A,B]" "CartProd(##M,A,B)"]
   CartProd_iff_sats[of 1 "[_,A,B]" A 2 B 0 _ M] arity_CartProd_fm  CartProd_fm_type
   ord_simp_union nonempty
  unfolding CartProd_def
  by simp

lemma image_sep_intf :
  assumes "A\<in>M" and "B\<in>M"
  shows "separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>B & (\<exists>x\<in>M. x\<in>A & pair(##M,x,y,p)))"
  using assms separation_in_ctm[of "Image_fm(1,2,0)" "[A,B]" "Image(##M,A,B)"]
   Image_iff_sats[of 1 "[_,A,B]" _ 2 _ 0 _ M] arity_Image_fm Image_fm_type
   ord_simp_union nonempty
  unfolding Image_def
  by simp

lemma converse_sep_intf :
  assumes "R\<in>M"
  shows "separation(##M,\<lambda>z. \<exists>p\<in>M. p\<in>R & (\<exists>x\<in>M.\<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,z)))"
  using assms separation_in_ctm[of "Converse_fm(1,0)" "[R]" "Converse(##M,R)"]
   Converse_iff_sats[of 1 "[_,R]" _ 0 _ M] arity_Converse_fm Converse_fm_type
   ord_simp_union nonempty
  unfolding Converse_def
  by simp

lemma restrict_sep_intf :
  assumes "A\<in>M"
  shows "separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A & (\<exists>y\<in>M. pair(##M,x,y,z)))"
  using assms separation_in_ctm[of "Restrict_fm(1,0)" "[A]" "Restrict(##M,A)"]
   Restrict_iff_sats[of 1 "[_,A]" _ 0 _ M] arity_Restrict_fm Restrict_fm_type
   ord_simp_union nonempty
  unfolding Restrict_def
  by simp

lemma comp_sep_intf :
  assumes "R\<in>M" and "S\<in>M"
  shows "separation(##M,\<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
           pair(##M,x,z,xz) & pair(##M,x,y,xy) & pair(##M,y,z,yz) & xy\<in>S & yz\<in>R)"
  using assms separation_in_ctm[of "Comp_fm(1,2,0)" "[R,S]" "Comp(##M,R,S)"]
    Comp_iff_sats[of 1 "[_,R,S]" _ 2 _ 0 _ M] arity_Comp_fm Comp_fm_type
    ord_simp_union nonempty
  unfolding Comp_def
  by simp

lemma pred_sep_intf:
  assumes "R\<in>M" and "X\<in>M"
  shows "separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>R & pair(##M,y,X,p))"
  using assms separation_in_ctm[of "Pred_fm(1,2,0)" "[R,X]" "Pred(##M,R,X)"]
    Pred_iff_sats[of 1 "[_,R,X]" _ 2 _ 0 _ M] arity_Pred_fm Pred_fm_type
    ord_simp_union nonempty
  unfolding Pred_def
  by simp

lemma memrel_sep_intf:
  "separation(##M, \<lambda>z. \<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) & x \<in> y)"
  using separation_in_ctm[of "is_Memrel_fm(0)" "[]" "is_Memrel(##M)"]
    is_Memrel_iff_sats[of 0 "[_]" _ M] arity_is_Memrel_fm is_Memrel_fm_type
    ord_simp_union nonempty
  unfolding is_Memrel_def
  by simp

lemma is_recfun_sep_intf :
  assumes "r\<in>M" "f\<in>M" "g\<in>M" "a\<in>M" "b\<in>M"
  shows "separation(##M,\<lambda>x. \<exists>xa\<in>M. \<exists>xb\<in>M.
                    pair(##M,x,a,xa) & xa \<in> r & pair(##M,x,b,xb) & xb \<in> r &
                    (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M,f,x,fx) & fun_apply(##M,g,x,gx) &
                                     fx \<noteq> gx))"
  using assms separation_in_ctm[of "RecFun_fm(1,2,3,4,5,0)" "[r,f,g,a,b]" "RecFun(##M,r,f,g,a,b)"]
    RecFun_iff_sats[of 1 "[_,r,f,g,a,b]" _ 2 _ 3 _ 4 _ 5 _ 0 _ M] arity_RecFun_fm RecFun_fm_type
    ord_simp_union nonempty
  unfolding RecFun_def
  by simp

(* Instance of Replacement for M_basic *)

schematic_goal funsp_fm_auto:
  assumes
    "nth(i,env) = p" "nth(j,env) = z" "nth(h,env) = n"
    "i \<in> nat" "j \<in> nat" "h \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>f\<in>A. \<exists>b\<in>A. \<exists>nb\<in>A. \<exists>cnbf\<in>A. pair(##A,f,b,p) & pair(##A,n,b,nb) & is_cons(##A,nb,f,cnbf) &
    upair(##A,cnbf,cnbf,z)) \<longleftrightarrow> sats(A,?fsfm(i,j,h),env)"
  by (insert assms ; (rule sep_rules | simp)+)

lemma funspace_succ_rep_intf :
  assumes
    "n\<in>M"
  shows
    "strong_replacement(##M,
          \<lambda>p z. \<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M.
                pair(##M,f,b,p) & pair(##M,n,b,nb) & is_cons(##M,nb,f,cnbf) &
                upair(##M,cnbf,cnbf,z))"
proof -
  obtain fsfm where
    fmsats:"env\<in>list(M) \<Longrightarrow>
    (\<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M. pair(##M,f,b,nth(0,env)) & pair(##M,nth(2,env),b,nb)
      & is_cons(##M,nb,f,cnbf) & upair(##M,cnbf,cnbf,nth(1,env)))
    \<longleftrightarrow> sats(M,fsfm(0,1,2),env)"
    and "fsfm(0,1,2) \<in> formula" and "arity(fsfm(0,1,2)) = 3" for env
    using funsp_fm_auto[of concl:M] by (simp del:FOL_sats_iff pair_abs add:arity ord_simp_union)
  (* "fsfm(0,1,2)\<equiv>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>\<cdot>pair_fm(3, 2, 4) \<and> \<cdot>pair_fm(6, 2, 1) \<and> \<cdot>cons_fm(1, 3, 0) \<and> \<cdot>{0,0} is 5 \<cdot>\<cdot>\<cdot>\<cdot>\<cdot>)\<cdot>)\<cdot>)\<cdot>)" for i j k *)
  then
  have "\<forall>n0\<in>M. strong_replacement(##M, \<lambda>p z. sats(M,fsfm(0,1,2) , [p,z,n0]))"
    using replacement_ax[of "fsfm(0,1,2)"] by simp
  moreover
  have "(\<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M. pair(##M,f,b,p) & pair(##M,n0,b,nb) &
          is_cons(##M,nb,f,cnbf) & upair(##M,cnbf,cnbf,z))
          \<longleftrightarrow> sats(M,fsfm(0,1,2) , [p,z,n0])"
    if "p\<in>M" "z\<in>M" "n0\<in>M" for p z n0
    using that fmsats[of "[p,z,n0]"] by simp
  ultimately
  have "\<forall>n0\<in>M. strong_replacement(##M, \<lambda> p z.
          \<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M. pair(##M,f,b,p) & pair(##M,n0,b,nb) &
          is_cons(##M,nb,f,cnbf) & upair(##M,cnbf,cnbf,z))"
    unfolding strong_replacement_def univalent_def by simp
  with \<open>n\<in>M\<close> show ?thesis by simp
qed


(* Interface with M_basic *)

lemmas M_basic_sep_instances =
  inter_sep_intf diff_sep_intf cartprod_sep_intf
  image_sep_intf converse_sep_intf restrict_sep_intf
  pred_sep_intf memrel_sep_intf comp_sep_intf is_recfun_sep_intf

end \<comment> \<open>\<^locale>\<open>M_ZF_trans\<close>\<close>

sublocale M_ZF_trans \<subseteq> M_basic "##M"
  using trans_M zero_in_M power_ax M_basic_sep_instances funspace_succ_rep_intf
  by unfold_locales auto

subsection\<open>Interface with \<^term>\<open>M_trancl\<close>\<close>

lemma (in M_ZF_trans) rtrancl_separation_intf:
  assumes "r\<in>M" "A\<in>M"
  shows "separation (##M, rtran_closure_mem(##M,A,r))"
  using assms separation_in_ctm[of "rtran_closure_mem_fm(1,2,0)" "[A,r]" "rtran_closure_mem(##M,A,r)"]
    arity_rtran_closure_mem_fm
    ord_simp_union nonempty
  by simp

schematic_goal sats_wellfounded_trancl_fm_auto:
  assumes
    "nth(i,env) = p" "nth(j,env) = r"  "nth(k,env) = B"
    "i \<in> nat" "j \<in> nat" "k \<in> nat" "env \<in> list(A)"
  shows
    "wellfounded_trancl(##A,B,r,p) \<longleftrightarrow> sats(A,?wtf(i,j,k),env)"
  unfolding  wellfounded_trancl_def
  by (insert assms ; (rule sep_rules tran_closure_iff_sats | simp)+)

arity_theorem for "rtran_closure_fm"
arity_theorem for "tran_closure_fm"

context M_ZF_trans
begin

lemma wftrancl_separation_intf:
  assumes
    "r\<in>M" and "Z\<in>M"
  shows
    "separation (##M, wellfounded_trancl(##M,Z,r))"
proof -
  obtain rcfm where
    fmsats:"\<And>env. env\<in>list(M) \<Longrightarrow>
    (wellfounded_trancl(##M,nth(2,env),nth(1,env),nth(0,env))) \<longleftrightarrow> sats(M,rcfm(0,1,2),env)"
    and
    "rcfm(0,1,2) \<in> formula"
    and
    "arity(rcfm(0,1,2)) = 3"
    using sats_wellfounded_trancl_fm_auto[of concl:M "nth(2,_)"]
    by (simp del:FOL_sats_iff pair_abs add: arity ord_simp_union)
  then
  show ?thesis
  using assms separation_in_ctm[of "rcfm(0,1,2)" "[r,Z]" "wellfounded_trancl(##M,Z,r)"]
    ord_simp_union nonempty fmsats[of "[_,r,Z]"]
  by simp
qed

text\<open>Proof that \<^term>\<open>nat \<in> M\<close>\<close>

lemma finite_sep_intf: "separation(##M, \<lambda>x. x\<in>nat)"
proof -
  have "(\<forall>v\<in>M. separation(##M,\<lambda>x. sats(M,finite_ordinal_fm(0),[x,v])))"
    using separation_ax by (simp add:arity)
  then
  have "(\<forall>v\<in>M. separation(##M,finite_ordinal(##M)))"
    unfolding separation_def by simp
  then
  have "separation(##M,finite_ordinal(##M))"
    using separation_in_ctm
      zero_in_M by auto
  then
  show ?thesis unfolding separation_def by simp
qed

lemma nat_subset_I':
  "\<lbrakk> I\<in>M ; 0\<in>I ; \<And>x. x\<in>I \<Longrightarrow> succ(x)\<in>I \<rbrakk> \<Longrightarrow> nat \<subseteq> I"
  by (rule subsetI,induct_tac x,simp+)

lemma nat_subset_I: "\<exists>I\<in>M. nat \<subseteq> I"
proof -
  have "\<exists>I\<in>M. 0\<in>I \<and> (\<forall>x\<in>M. x\<in>I \<longrightarrow> succ(x)\<in>I)"
    using infinity_ax
    unfolding infinity_ax_def by auto
  then
  obtain I where
    "I\<in>M" "0\<in>I" "(\<forall>x\<in>M. x\<in>I \<longrightarrow> succ(x)\<in>I)"
    by auto
  then
  have "\<And>x. x\<in>I \<Longrightarrow> succ(x)\<in>I"
    using transitivity by simp
  then
  have "nat\<subseteq>I"
    using  \<open>I\<in>M\<close> \<open>0\<in>I\<close> nat_subset_I' by simp
  then
  show ?thesis using \<open>I\<in>M\<close> by auto
qed

lemma nat_in_M: "nat \<in> M"
proof -
  have 1:"{x\<in>B . x\<in>A}=A" if "A\<subseteq>B" for A B
    using that by auto
  obtain I where
    "I\<in>M" "nat\<subseteq>I"
    using nat_subset_I by auto
  then
  have "{x\<in>I . x\<in>nat} \<in> M"
    using finite_sep_intf separation_closed[of "\<lambda>x . x\<in>nat"] by simp
  then
  show ?thesis
    using \<open>nat\<subseteq>I\<close> 1 by simp
qed

end \<comment> \<open>\<^locale>\<open>M_ZF_trans\<close>\<close>

sublocale M_ZF_trans \<subseteq> M_trancl "##M"
  using rtrancl_separation_intf wftrancl_separation_intf nat_in_M
    wellfounded_trancl_def by unfold_locales auto

subsection\<open>Interface with \<^term>\<open>M_eclose\<close>\<close>

lemma repl_sats:
  assumes
    sat:"\<And>x z. x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> sats(M,\<phi>,Cons(x,Cons(z,env))) \<longleftrightarrow> P(x,z)"
  shows
    "strong_replacement(##M,\<lambda>x z. sats(M,\<phi>,Cons(x,Cons(z,env)))) \<longleftrightarrow>
   strong_replacement(##M,P)"
  by (rule strong_replacement_cong,simp add:sat)

lemma (in M_ZF_trans) list_repl1_intf:
  assumes
    "A\<in>M"
  shows
    "iterates_replacement(##M, is_list_functor(##M,A), 0)"
proof -
  {
    fix n
    assume "n\<in>nat"
    have "succ(n)\<in>M"
      using \<open>n\<in>nat\<close> nat_into_M by simp
    then have 1:"Memrel(succ(n))\<in>M"
      using \<open>n\<in>nat\<close> Memrel_closed by simp
    have "0\<in>M"
      using  nat_0I nat_into_M by simp
    then have "is_list_functor(##M, A, a, b)
       \<longleftrightarrow> sats(M, list_functor_fm(13,1,0), [b,a,c,d,a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),A,0])"
      if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "a0\<in>M" "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" "y\<in>M" "x\<in>M" "z\<in>M"
      for a b c d a0 a1 a2 a3 a4 y x z
      using that 1 \<open>A\<in>M\<close> list_functor_iff_sats by simp
    then have "sats(M, iterates_MH_fm(list_functor_fm(13,1,0),10,2,1,0), [a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),A,0])
        \<longleftrightarrow> iterates_MH(##M,is_list_functor(##M,A),0,a2, a1, a0)"
      if "a0\<in>M" "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" "y\<in>M" "x\<in>M" "z\<in>M"
      for a0 a1 a2 a3 a4 y x z
      using that sats_iterates_MH_fm[of M "is_list_functor(##M,A)" _] 1 \<open>0\<in>M\<close> \<open>A\<in>M\<close>  by simp
    then have 2:"sats(M, is_wfrec_fm(iterates_MH_fm(list_functor_fm(13,1,0),10,2,1,0),3,1,0),
                            [y,x,z,Memrel(succ(n)),A,0])
        \<longleftrightarrow>
        is_wfrec(##M, iterates_MH(##M,is_list_functor(##M,A),0) , Memrel(succ(n)), x, y)"
      if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
      using  that sats_is_wfrec_fm 1 \<open>0\<in>M\<close> \<open>A\<in>M\<close> by simp
    let
      ?f="Exists(And(pair_fm(1,0,2),
               is_wfrec_fm(iterates_MH_fm(list_functor_fm(13,1,0),10,2,1,0),3,1,0)))"
    have satsf:"sats(M, ?f, [x,z,Memrel(succ(n)),A,0])
        \<longleftrightarrow>
        (\<exists>y\<in>M. pair(##M,x,y,z) &
        is_wfrec(##M, iterates_MH(##M,is_list_functor(##M,A),0) , Memrel(succ(n)), x, y))"
      if "x\<in>M" "z\<in>M" for x z
      using that 2 1 \<open>0\<in>M\<close> \<open>A\<in>M\<close> by (simp del:pair_abs)
    have "arity(?f) = 5"
      unfolding fm_definitions
      by (simp add:arity ord_simp_union)
    then
    have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,Memrel(succ(n)),A,0]))"
      using replacement_ax[of ?f] 1 \<open>A\<in>M\<close> \<open>0\<in>M\<close> by simp
    then
    have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, iterates_MH(##M,is_list_functor(##M,A),0) ,
                Memrel(succ(n)), x, y))"
      using repl_sats[of M ?f "[Memrel(succ(n)),A,0]"]  satsf by (simp del:pair_abs)
  }
  then
  show ?thesis unfolding iterates_replacement_def wfrec_replacement_def by simp
qed



(* Iterates_replacement para predicados sin parámetros *)
lemma (in M_ZF_trans) iterates_repl_intf :
  assumes
    "v\<in>M" and
    isfm:"is_F_fm \<in> formula" and
    arty:"arity(is_F_fm)=2" and
    satsf: "\<And>a b env'. \<lbrakk> a\<in>M ; b\<in>M ; env'\<in>list(M) \<rbrakk>
              \<Longrightarrow> is_F(a,b) \<longleftrightarrow> sats(M, is_F_fm, [b,a]@env')"
  shows
    "iterates_replacement(##M,is_F,v)"
proof -
  {
    fix n
    assume "n\<in>nat"
    have "succ(n)\<in>M"
      using \<open>n\<in>nat\<close> nat_into_M by simp
    then have 1:"Memrel(succ(n))\<in>M"
      using \<open>n\<in>nat\<close> Memrel_closed by simp
    {
      fix a0 a1 a2 a3 a4 y x z
      assume as:"a0\<in>M" "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" "y\<in>M" "x\<in>M" "z\<in>M"
      have "sats(M, is_F_fm, Cons(b,Cons(a,Cons(c,Cons(d,[a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),v])))))
          \<longleftrightarrow> is_F(a,b)"
        if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" for a b c d
        using as that 1 satsf[of a b "[c,d,a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),v]"] \<open>v\<in>M\<close> by simp
      then
      have "sats(M, iterates_MH_fm(is_F_fm,9,2,1,0), [a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),v])
          \<longleftrightarrow> iterates_MH(##M,is_F,v,a2, a1, a0)"
        using as
          sats_iterates_MH_fm[of M "is_F" "is_F_fm"] 1 \<open>v\<in>M\<close> by simp
    }
    then have 2:"sats(M, is_wfrec_fm(iterates_MH_fm(is_F_fm,9,2,1,0),3,1,0),
                            [y,x,z,Memrel(succ(n)),v])
        \<longleftrightarrow>
        is_wfrec(##M, iterates_MH(##M,is_F,v),Memrel(succ(n)), x, y)"
      if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
      using  that sats_is_wfrec_fm 1 \<open>v\<in>M\<close> by simp
    let
      ?f="Exists(And(pair_fm(1,0,2),
               is_wfrec_fm(iterates_MH_fm(is_F_fm,9,2,1,0),3,1,0)))"
    have satsf:"sats(M, ?f, [x,z,Memrel(succ(n)),v])
        \<longleftrightarrow>
        (\<exists>y\<in>M. pair(##M,x,y,z) &
        is_wfrec(##M, iterates_MH(##M,is_F,v) , Memrel(succ(n)), x, y))"
      if "x\<in>M" "z\<in>M" for x z
      using that 2 1 \<open>v\<in>M\<close> by (simp del:pair_abs)
    have "arity(?f) = 4"
      unfolding fm_definitions
      using arty by (simp add:arity ord_simp_union)
    then
    have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,Memrel(succ(n)),v]))"
      using replacement_ax[of ?f] 1 \<open>v\<in>M\<close> \<open>is_F_fm\<in>formula\<close> by simp
    then
    have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, iterates_MH(##M,is_F,v) ,
                Memrel(succ(n)), x, y))"
      using repl_sats[of M ?f "[Memrel(succ(n)),v]"]  satsf by (simp del:pair_abs)
  }
  then
  show ?thesis unfolding iterates_replacement_def wfrec_replacement_def by simp
qed

lemma (in M_ZF_trans) formula_repl1_intf :
  "iterates_replacement(##M, is_formula_functor(##M), 0)"
proof -
  have "0\<in>M"
    using  nat_0I nat_into_M by simp
  have 1:"arity(formula_functor_fm(1,0)) = 2"
    unfolding fm_definitions
    by (simp add:arity ord_simp_union)
  have 2:"formula_functor_fm(1,0)\<in>formula" by simp
  have "is_formula_functor(##M,a,b) \<longleftrightarrow>
        sats(M, formula_functor_fm(1,0), [b,a])"
    if "a\<in>M" "b\<in>M"  for a b
    using that by simp
  then show ?thesis using \<open>0\<in>M\<close> 1 2
      iterates_repl_intf[where is_F_fm="formula_functor_fm(1,0)"] by simp
qed

lemma (in M_ZF_trans) nth_repl_intf:
  assumes
    "l \<in> M"
  shows
    "iterates_replacement(##M,\<lambda>l' t. is_tl(##M,l',t),l)"
proof -
  have 1:"arity(tl_fm(1,0)) = 2"
    unfolding fm_definitions by (simp add:arity ord_simp_union)
  have 2:"tl_fm(1,0)\<in>formula" by simp
  have "is_tl(##M,a,b) \<longleftrightarrow> sats(M, tl_fm(1,0), [b,a])"
    if "a\<in>M" "b\<in>M" for a b
    using that by simp
  then show ?thesis using \<open>l\<in>M\<close> 1 2
      iterates_repl_intf[where is_F_fm="tl_fm(1,0)"] by simp
qed


lemma (in M_ZF_trans) eclose_repl1_intf:
  assumes
    "A\<in>M"
  shows
    "iterates_replacement(##M, big_union(##M), A)"
proof -
  have 1:"arity(big_union_fm(1,0)) = 2"
    unfolding fm_definitions by (simp add:arity ord_simp_union)
  have 2:"big_union_fm(1,0)\<in>formula" by simp
  have "big_union(##M,a,b) \<longleftrightarrow> sats(M, big_union_fm(1,0), [b,a])"
    if "a\<in>M" "b\<in>M" for a b
    using that by simp
  then show ?thesis using \<open>A\<in>M\<close> 1 2
      iterates_repl_intf[where is_F_fm="big_union_fm(1,0)"] by simp
qed

(*
    and list_replacement2:
   "M(A) \<Longrightarrow> strong_replacement(M,
         \<lambda>n y. n\<in>nat & is_iterates(M, is_list_functor(M,A), 0, n, y))"

*)
lemma (in M_ZF_trans) list_repl2_intf:
  assumes
    "A\<in>M"
  shows
    "strong_replacement(##M,\<lambda>n y. n\<in>nat & is_iterates(##M, is_list_functor(##M,A), 0, n, y))"
proof -
  have "0\<in>M"
    using  nat_0I nat_into_M by simp
  have "is_list_functor(##M,A,a,b) \<longleftrightarrow>
        sats(M,list_functor_fm(13,1,0),[b,a,c,d,e,f,g,h,i,j,k,n,y,A,0,nat])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "f\<in>M""g\<in>M""h\<in>M""i\<in>M""j\<in>M" "k\<in>M" "n\<in>M" "y\<in>M"
    for a b c d e f g h i j k n y
    using that \<open>0\<in>M\<close> nat_in_M \<open>A\<in>M\<close> by simp
  then
  have 1:"sats(M, is_iterates_fm(list_functor_fm(13,1,0),3,0,1),[n,y,A,0,nat] ) \<longleftrightarrow>
           is_iterates(##M, is_list_functor(##M,A), 0, n , y)"
    if "n\<in>M" "y\<in>M" for n y
    using that \<open>0\<in>M\<close> \<open>A\<in>M\<close> nat_in_M
      sats_is_iterates_fm[of M "is_list_functor(##M,A)"] by simp
  let ?f = "And(Member(0,4),is_iterates_fm(list_functor_fm(13,1,0),3,0,1))"
  have satsf:"sats(M, ?f,[n,y,A,0,nat] ) \<longleftrightarrow>
        n\<in>nat & is_iterates(##M, is_list_functor(##M,A), 0, n, y)"
    if "n\<in>M" "y\<in>M" for n y
    using that \<open>0\<in>M\<close> \<open>A\<in>M\<close> nat_in_M 1 by simp
  have "arity(?f) = 5"
    unfolding fm_definitions
    by (simp add:arity ord_simp_union)
  then
  have "strong_replacement(##M,\<lambda>n y. sats(M,?f,[n,y,A,0,nat]))"
    using replacement_ax[of ?f] 1 nat_in_M \<open>A\<in>M\<close> \<open>0\<in>M\<close> by simp
  then
  show ?thesis using repl_sats[of M ?f "[A,0,nat]"]  satsf  by simp
qed

lemma (in M_ZF_trans) formula_repl2_intf:
  "strong_replacement(##M,\<lambda>n y. n\<in>nat & is_iterates(##M, is_formula_functor(##M), 0, n, y))"
proof -
  have "0\<in>M"
    using  nat_0I nat_into_M by simp
  have "is_formula_functor(##M,a,b) \<longleftrightarrow>
        sats(M,formula_functor_fm(1,0),[b,a,c,d,e,f,g,h,i,j,k,n,y,0,nat])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "f\<in>M""g\<in>M""h\<in>M""i\<in>M""j\<in>M" "k\<in>M" "n\<in>M" "y\<in>M"
    for a b c d e f g h i j k n y
    using that \<open>0\<in>M\<close> nat_in_M by simp
  then
  have 1:"sats(M, is_iterates_fm(formula_functor_fm(1,0),2,0,1),[n,y,0,nat] ) \<longleftrightarrow>
           is_iterates(##M, is_formula_functor(##M), 0, n , y)"
    if "n\<in>M" "y\<in>M" for n y
    using that \<open>0\<in>M\<close> nat_in_M
      sats_is_iterates_fm[of M "is_formula_functor(##M)"] by simp
  let ?f = "And(Member(0,3),is_iterates_fm(formula_functor_fm(1,0),2,0,1))"
  have satsf:"sats(M, ?f,[n,y,0,nat] ) \<longleftrightarrow>
        n\<in>nat & is_iterates(##M, is_formula_functor(##M), 0, n, y)"
    if "n\<in>M" "y\<in>M" for n y
    using that \<open>0\<in>M\<close> nat_in_M 1 by simp
  have artyf:"arity(?f) = 4"
    unfolding fm_definitions
    by (simp add:arity ord_simp_union)
  then
  have "strong_replacement(##M,\<lambda>n y. sats(M,?f,[n,y,0,nat]))"
    using replacement_ax[of ?f] 1 artyf \<open>0\<in>M\<close> nat_in_M by simp
  then
  show ?thesis using repl_sats[of M ?f "[0,nat]"]  satsf  by simp
qed


(*
   "M(A) \<Longrightarrow> strong_replacement(M,
         \<lambda>n y. n\<in>nat & is_iterates(M, big_union(M), A, n, y))"
*)

lemma (in M_ZF_trans) eclose_repl2_intf:
  assumes
    "A\<in>M"
  shows
    "strong_replacement(##M,\<lambda>n y. n\<in>nat & is_iterates(##M, big_union(##M), A, n, y))"
proof -
  have "big_union(##M,a,b) \<longleftrightarrow>
        sats(M,big_union_fm(1,0),[b,a,c,d,e,f,g,h,i,j,k,n,y,A,nat])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "f\<in>M""g\<in>M""h\<in>M""i\<in>M""j\<in>M" "k\<in>M" "n\<in>M" "y\<in>M"
    for a b c d e f g h i j k n y
    using that \<open>A\<in>M\<close> nat_in_M by simp
  then
  have 1:"sats(M, is_iterates_fm(big_union_fm(1,0),2,0,1),[n,y,A,nat] ) \<longleftrightarrow>
           is_iterates(##M, big_union(##M), A, n , y)"
    if "n\<in>M" "y\<in>M" for n y
    using that \<open>A\<in>M\<close> nat_in_M
      sats_is_iterates_fm[of M "big_union(##M)"] by simp
  let ?f = "And(Member(0,3),is_iterates_fm(big_union_fm(1,0),2,0,1))"
  have satsf:"sats(M, ?f,[n,y,A,nat] ) \<longleftrightarrow>
        n\<in>nat & is_iterates(##M, big_union(##M), A, n, y)"
    if "n\<in>M" "y\<in>M" for n y
    using that \<open>A\<in>M\<close> nat_in_M 1 by simp
  have artyf:"arity(?f) = 4"
    unfolding fm_definitions
    by (simp add:arity ord_simp_union)
  then
  have "strong_replacement(##M,\<lambda>n y. sats(M,?f,[n,y,A,nat]))"
    using replacement_ax[of ?f] 1 artyf \<open>A\<in>M\<close> nat_in_M by simp
  then
  show ?thesis using repl_sats[of M ?f "[A,nat]"]  satsf  by simp
qed

sublocale M_ZF_trans \<subseteq> M_datatypes "##M"
  using list_repl1_intf list_repl2_intf formula_repl1_intf
    formula_repl2_intf nth_repl_intf
  by unfold_locales auto

sublocale M_ZF_trans \<subseteq> M_eclose "##M"
  using eclose_repl1_intf eclose_repl2_intf
  by unfold_locales auto

(* Interface with locale M_eclose_pow *)

lemma (in M_ZF_trans) Powapply_repl :
  assumes "f\<in>M"
  shows "strong_replacement(##M,\<lambda>x y. y=Powapply_rel(##M,f,x))"
proof -
  note assms
  moreover
  have "arity(is_Powapply_fm(2,0,1)) = 3"
    unfolding is_Powapply_fm_def
    by (simp add:arity ord_simp_union)
  moreover from calculation
  have iff:"z=Powapply_rel(##M,f,p) \<longleftrightarrow> sats(M,is_Powapply_fm(2,0,1) , [p,z,f])"
    if "p\<in>M" "z\<in>M" for p z
    using that zero_in_M sats_is_Powapply_fm[of 2 0 1 "[p,z,f]" M] is_Powapply_iff
      replacement_ax[of "is_Powapply_fm(2,0,1)"]
    by simp
  ultimately
  show ?thesis
    using replacement_ax[of "is_Powapply_fm(2,0,1)"]
    by (rule_tac strong_replacement_cong[THEN iffD2,OF iff],simp_all)
qed

definition
  PHrank :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "PHrank(M,f,y,z) \<equiv> (\<exists>fy[M]. fun_apply(M,f,y,fy) \<and> successor(M,fy,z))"

synthesize "PHrank" from_definition assuming "nonempty"
lemma (in M_ZF_trans) phrank_repl :
  assumes
    "f\<in>M"
  shows
    "strong_replacement(##M, \<lambda>x y. y = succ(f`x))"
proof -
  note assms
  moreover from this
  have iff:"y = succ(f ` x) \<longleftrightarrow> M, [x, y, f] \<Turnstile> PHrank_fm(2, 0, 1)" if "x\<in>M" "y\<in>M" for x y
    using PHrank_iff_sats[of 2 "[x,y,f]" f 0 _ 1 _ M] zero_in_M that
    apply_closed
    unfolding PHrank_def
    by simp
  moreover
  have "arity(PHrank_fm(2,0,1)) = 3"
    unfolding PHrank_fm_def
    by (simp add:arity ord_simp_union)
  ultimately
  show ?thesis
    using replacement_ax[of "PHrank_fm(2,0,1)"]
    unfolding PHrank_def
    by(rule_tac strong_replacement_cong[THEN iffD2,OF iff],simp_all)
qed

declare is_Hrank_fm_def[fm_definitions add]
declare PHrank_fm_def[fm_definitions add]

lemma (in M_ZF_trans) wfrec_rank :
  assumes
    "X\<in>M"
  shows
    "wfrec_replacement(##M,is_Hrank(##M),rrank(X))"
proof -
  have
    "is_Hrank(##M,a2, a1, a0) \<longleftrightarrow>
             sats(M, is_Hrank_fm(2,1,0), [a0,a1,a2,a3,a4,y,x,z,rrank(X)])"
    if "a4\<in>M" "a3\<in>M" "a2\<in>M" "a1\<in>M" "a0\<in>M" "y\<in>M" "x\<in>M" "z\<in>M" for a4 a3 a2 a1 a0 y x z
    using that rrank_in_M \<open>X\<in>M\<close> zero_in_M is_Hrank_iff_sats
    by simp
  then
  have
    1:"sats(M, is_wfrec_fm(is_Hrank_fm(2,1,0),3,1,0),[y,x,z,rrank(X)])
  \<longleftrightarrow> is_wfrec(##M, is_Hrank(##M) ,rrank(X), x, y)"
    if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
    using that \<open>X\<in>M\<close> rrank_in_M sats_is_wfrec_fm zero_in_M
    by simp
  let
    ?f="Exists(And(pair_fm(1,0,2),is_wfrec_fm(is_Hrank_fm(2,1,0),3,1,0)))"
  have satsf:"sats(M, ?f, [x,z,rrank(X)])
              \<longleftrightarrow> (\<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hrank(##M) , rrank(X), x, y))"
    if "x\<in>M" "z\<in>M" for x z
    using that 1 \<open>X\<in>M\<close> rrank_in_M by (simp del:pair_abs)
  have "arity(?f) = 3"
    unfolding fm_definitions
    by (simp add:arity ord_simp_union)
  then
  have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,rrank(X)]))"
    using replacement_ax[of ?f] 1 \<open>X\<in>M\<close> rrank_in_M
    by simp
  then
  have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hrank(##M) , rrank(X), x, y))"
    using repl_sats[of M ?f "[rrank(X)]"]  satsf
    by (simp del:pair_abs)
  then
  show ?thesis
    unfolding wfrec_replacement_def
    by simp
qed

(* FIX US *)
schematic_goal sats_is_Vset_fm_auto:
  assumes
    "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "0\<in>A"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vset(##A,nth(i, env),nth(v, env))
    \<longleftrightarrow> sats(A,?ivs_fm(i,v),env)"
  unfolding is_Vset_def is_Vfrom_def
  by (insert assms; (rule sep_rules is_HVfrom_iff_sats is_transrec_iff_sats | simp)+)

synthesize "is_Vset" from_schematic "sats_is_Vset_fm_auto"

arity_theorem for "is_Vset_fm"

lemma (in M_ZF_trans) memrel_eclose_sing :
  "a\<in>M \<Longrightarrow> \<exists>sa\<in>M. \<exists>esa\<in>M. \<exists>mesa\<in>M.
       upair(##M,a,a,sa) & is_eclose(##M,sa,esa) & membership(##M,esa,mesa)"
  using upair_ax eclose_closed Memrel_closed unfolding upair_ax_def
  by (simp del:upair_abs)


lemma (in M_ZF_trans) trans_repl_HVFrom :
  assumes
    "A\<in>M" "i\<in>M"
  shows
    "transrec_replacement(##M,is_HVfrom(##M,A),i)"
proof -
  { fix mesa
    assume "mesa\<in>M"
    have
      0:"is_HVfrom(##M,A,a2, a1, a0) \<longleftrightarrow>
      sats(M, is_HVfrom_fm(8,2,1,0), [a0,a1,a2,a3,a4,y,x,z,A,mesa])"
      if "a4\<in>M" "a3\<in>M" "a2\<in>M" "a1\<in>M" "a0\<in>M" "y\<in>M" "x\<in>M" "z\<in>M" for a4 a3 a2 a1 a0 y x z
      using that zero_in_M sats_is_HVfrom_fm \<open>mesa\<in>M\<close> \<open>A\<in>M\<close> by simp
    have
      1:"sats(M, is_wfrec_fm(is_HVfrom_fm(8,2,1,0),4,1,0),[y,x,z,A,mesa])
        \<longleftrightarrow> is_wfrec(##M, is_HVfrom(##M,A),mesa, x, y)"
      if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
      using that \<open>A\<in>M\<close> \<open>mesa\<in>M\<close> sats_is_wfrec_fm[OF 0] by simp
    let
      ?f="Exists(And(pair_fm(1,0,2),is_wfrec_fm(is_HVfrom_fm(8,2,1,0),4,1,0)))"
    have satsf:"sats(M, ?f, [x,z,A,mesa])
              \<longleftrightarrow> (\<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_HVfrom(##M,A) , mesa, x, y))"
      if "x\<in>M" "z\<in>M" for x z
      using that 1 \<open>A\<in>M\<close> \<open>mesa\<in>M\<close> by (simp del:pair_abs)
    have "arity(?f) = 4"
      unfolding fm_definitions
      by (simp add:arity ord_simp_union)
    then
    have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,A,mesa]))"
      using replacement_ax[of ?f] 1 \<open>A\<in>M\<close> \<open>mesa\<in>M\<close> by simp
    then
    have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_HVfrom(##M,A) , mesa, x, y))"
      using repl_sats[of M ?f "[A,mesa]"]  satsf by (simp del:pair_abs)
    then
    have "wfrec_replacement(##M,is_HVfrom(##M,A),mesa)"
      unfolding wfrec_replacement_def  by simp
  }
  then show ?thesis unfolding transrec_replacement_def
    using \<open>i\<in>M\<close> memrel_eclose_sing by simp
qed

sublocale M_ZF_trans \<subseteq> M_Vfrom "##M"
  using power_ax Powapply_repl phrank_repl trans_repl_HVFrom wfrec_rank
  by unfold_locales auto


subsection\<open>Interface for proving Collects and Replace in M.\<close>
context M_ZF_trans
begin

lemma Collect_in_M :
  assumes
    "\<phi> \<in> formula" "env\<in>list(M)"
    "arity(\<phi>) \<le> 1 #+ length(env)" "A\<in>M" and
    satsQ: "\<And>x. x\<in>M \<Longrightarrow> sats(M,\<phi>,[x]@env) \<longleftrightarrow> Q(x)"
  shows
    "{y\<in>A . Q(y)}\<in>M"
proof -
  have "separation(##M,\<lambda>x. sats(M,\<phi>,[x] @ env))"
    using assms separation_ax by simp
  then show ?thesis using
      \<open>A\<in>M\<close> satsQ trans_M
      separation_cong[of "##M" "\<lambda>y. sats(M,\<phi>,[y]@env)" "Q"]
      separation_closed by simp
qed

\<comment> \<open>This version has a weaker assumption.\<close>
lemma separation_in_M :
  assumes
    "\<phi> \<in> formula" "env\<in>list(M)"
    "arity(\<phi>) \<le> 1 #+ length(env)" "A\<in>M" and
    satsQ: "\<And>x. x\<in>A \<Longrightarrow> sats(M,\<phi>,[x]@env) \<longleftrightarrow> Q(x)"
  shows
    "{y\<in>A . Q(y)} \<in> M"
proof -
  let ?\<phi>' = "And(\<phi>,Member(0,length(env)#+1))"
  have "arity(?\<phi>') \<le> 1 #+ length(env@[A])"
    using assms Un_le
      le_trans[of "arity(\<phi>)" "1#+length(env)" "2#+length(env)"]
    by (force simp:FOL_arities)
  moreover from assms
  have "?\<phi>'\<in>formula"
    "nth(length(env), env @ [A]) = A" using assms nth_append by auto
  moreover from calculation
  have "\<And> x . x \<in> M \<Longrightarrow> sats(M,?\<phi>',[x]@env@[A]) \<longleftrightarrow> Q(x) \<and> x\<in>A"
    using arity_sats_iff[of _ "[A]" _ "[_]@env"] assms
    by auto
  ultimately
  show ?thesis using assms
      Collect_in_M[of ?\<phi>' "env@[A]" _ "\<lambda>x . Q(x) \<and> x\<in>A", OF _ _ _ \<open>A\<in>M\<close>]
    by auto
qed

lemma strong_replacement_in_ctm :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 #+ length(env)" and
    fsats: "\<And>x y. x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> \<phi>) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>M \<Longrightarrow> f(x) \<in> M" and "env\<in>list(M)"
  shows "strong_replacement(##M, \<lambda>x y . y = f(x))"
    using assms
      strong_replacement_cong[of "##M" "\<lambda>x y. M,[x,y]@env\<Turnstile>\<phi>" "\<lambda>x y. y = f(x)"]
      replacement_ax[of \<phi>]
    by auto

lemma strong_replacement_rel_in_ctm :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 #+ length(env)" and
    fsats: "\<And>x y. x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> \<phi>) \<longleftrightarrow> f(x,y)" and
     "env\<in>list(M)"
  shows "strong_replacement(##M, f)"
    using assms
      strong_replacement_cong[of "##M" "\<lambda>x y. M,[x,y]@env\<Turnstile>\<phi>" "f"]
      replacement_ax[of \<phi>]
    by auto

lemma Replace_in_M :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 #+ length(env)" and
    fsats: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> \<phi>) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>A \<Longrightarrow> f(x) \<in> M"  and
    "A\<in>M" "env\<in>list(M)"
  shows "{f(x) . x\<in>A}\<in>M"
proof -
  let ?\<phi>' = "And(\<phi>,Member(0,length(env)#+2))"
  have "arity(?\<phi>') \<le> 2 #+ length(env@[A])"
    using assms Un_le
      le_trans[of "arity(\<phi>)" "2#+(length(env))" "3#+length(env)"]
    by (force simp:FOL_arities)
  moreover from assms
  have "?\<phi>'\<in>formula" "nth(length(env), env @ [A]) = A"
    using assms nth_append by auto
  moreover from calculation
  have "\<And> x y. x \<in> M \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env@[A]\<Turnstile>?\<phi>') \<longleftrightarrow> y=f(x) \<and>x\<in>A"
    using arity_sats_iff[of _ "[A]" _ "[_,_]@env"] assms
    by auto
  moreover from calculation
  have "strong_replacement(##M, \<lambda>x y. M,[x,y]@env@[A] \<Turnstile> ?\<phi>')"
    using replacement_ax[of ?\<phi>'] \<open>env\<in>list(M)\<close> assms by simp
  ultimately
  have 4:"strong_replacement(##M, \<lambda>x y. y = f(x) \<and> x\<in>A)"
    using
      strong_replacement_cong[of "##M" "\<lambda>x y. M,[x,y]@env@[A]\<Turnstile>?\<phi>'" "\<lambda>x y. y = f(x) \<and> x\<in>A"]
    by simp
  then
  have "{y . x\<in>A , y = f(x)} \<in> M"
    using \<open>A\<in>M\<close> strong_replacement_closed[OF 4,of A] fclosed by simp
  moreover
  have "{f(x). x\<in>A} = { y . x\<in>A , y = f(x)}"
    by auto
  ultimately show ?thesis by simp
qed

lemma Replace_relativized_in_M :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 #+ length(env)" and
    fsats: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> \<phi>) \<longleftrightarrow> is_f(x,y)" and
    fabs:  "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> is_f(x,y) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>A \<Longrightarrow> f(x) \<in> M"  and
    "A\<in>M" "env\<in>list(M)"
  shows "{f(x) . x\<in>A}\<in>M"
  using assms Replace_in_M[of \<phi>] by auto

definition \<rho>_repl :: "i\<Rightarrow>i" where
  "\<rho>_repl(l) \<equiv> rsum({\<langle>0, 1\<rangle>, \<langle>1, 0\<rangle>}, id(l), 2, 3, l)"

lemma f_type : "{\<langle>0, 1\<rangle>, \<langle>1, 0\<rangle>} \<in> 2 \<rightarrow> 3"
  using Pi_iff unfolding function_def by auto

lemma ren_type :
  assumes "l\<in>nat"
  shows "\<rho>_repl(l) : 2#+l \<rightarrow> 3#+l"
  using sum_type[of 2 3 l l "{\<langle>0, 1\<rangle>, \<langle>1, 0\<rangle>}" "id(l)"] f_type assms id_type
  unfolding \<rho>_repl_def by auto

lemma ren_action :
  assumes
    "env\<in>list(M)" "x\<in>M" "y\<in>M" "z\<in>M"
  shows "\<forall> i . i < 2#+length(env) \<longrightarrow>
          nth(i,[x,z]@env) = nth(\<rho>_repl(length(env))`i,[z,x,y]@env)"
proof -
  let ?f="{\<langle>0, 1\<rangle>, \<langle>1, 0\<rangle>}"
  have 1:"(\<And>j. j < length(env) \<Longrightarrow> nth(j, env) = nth(id(length(env)) ` j, env))"
    using assms ltD by simp
  have 2:"nth(j, [x,z]) = nth(?f ` j, [z,x,y])" if "j<2" for j
  proof -
    consider "j=0" | "j=1" using  ltD[OF \<open>j<2\<close>] by auto
    then show ?thesis
    proof(cases)
      case 1
      then show ?thesis using apply_equality f_type by simp
    next
      case 2
      then show ?thesis using apply_equality f_type by simp
    qed
  qed
  show ?thesis
    using sum_action[OF _ _ _ _ f_type id_type _ _ _ _ _ _ _ 2 1,simplified] assms
    unfolding \<rho>_repl_def by simp
qed

lemma Lambda_in_M :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 #+ length(env)" and
    fsats: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> \<phi>) \<longleftrightarrow> is_f(x,y)" and
    fabs:  "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> is_f(x,y) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>A \<Longrightarrow> f(x) \<in> M" and
    "A\<in>M" "env\<in>list(M)"
  shows "(\<lambda>x\<in>A . f(x)) \<in>M"
  unfolding lam_def
proof -
  let ?ren="\<rho>_repl(length(env))"
  let ?j="2#+length(env)"
  let ?k="3#+length(env)"
  let ?\<psi>="ren(\<phi>)`?j`?k`?ren"
  let ?\<phi>'="Exists(And(pair_fm(1,0,2),?\<psi>))"
  let ?p="\<lambda>x y. \<exists>z\<in>M. pair(##M,x,z,y) \<and> is_f(x,z)"
  have "?\<phi>'\<in>formula" "?\<psi>\<in>formula"
    using \<open>env\<in>_\<close> length_type f_fm ren_type ren_tc[of \<phi> "2#+length(env)" "3#+length(env)" ?ren]
    by simp_all
  moreover from this
  have "arity(?\<psi>)\<le>3#+(length(env))" "arity(?\<psi>)\<in>nat"
    using assms arity_ren[OF f_fm _ _ ren_type,of "length(env)"] by simp_all
  then
  have "arity(?\<phi>') \<le> 2#+(length(env))"
    using Un_le pred_Un_distrib assms pred_le
    by (simp add:arity)
  moreover from this calculation
  have "x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> ?\<phi>') \<longleftrightarrow> ?p(x,y)" for x y
    using \<open>env\<in>_\<close> length_type[OF \<open>env\<in>_\<close>] assms transitivity[OF _ \<open>A\<in>M\<close>]
      sats_iff_sats_ren[OF f_fm _ _ _ _ ren_type f_ar ren_action[rule_format,of _ x y],of _ M ]
    by auto
  moreover
  have "x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> ?p(x,y) \<longleftrightarrow> y = <x,f(x)>" for x y
    using assms transitivity[OF _ \<open>A\<in>_\<close>] fclosed
    by simp
  moreover
  have "\<And> x . x\<in>A \<Longrightarrow> <x,f(x)> \<in> M"
    using transitivity[OF _ \<open>A\<in>M\<close>] pair_in_M_iff fclosed by simp
  ultimately
  show "{\<langle>x,f(x)\<rangle> . x\<in>A } \<in> M"
    using Replace_in_M[of ?\<phi>'] \<open>A\<in>M\<close> \<open>env\<in>_\<close>
    by simp
qed

definition \<rho>_pair_repl :: "i\<Rightarrow>i" where
  "\<rho>_pair_repl(l) \<equiv> rsum({\<langle>0, 0\<rangle>, \<langle>1, 1\<rangle>, \<langle>2, 3\<rangle>}, id(l), 3, 4, l)"

lemma f_type' : "{\<langle>0,0 \<rangle>, \<langle>1, 1\<rangle>, \<langle>2, 3\<rangle>} \<in> 3 \<rightarrow> 4"
  using Pi_iff unfolding function_def by auto

lemma ren_type' :
  assumes "l\<in>nat"
  shows "\<rho>_pair_repl(l) : 3#+l \<rightarrow> 4#+l"
  using sum_type[of 3 4 l l "{\<langle>0, 0\<rangle>, \<langle>1, 1\<rangle>, \<langle>2, 3\<rangle>}" "id(l)"] f_type' assms id_type
  unfolding \<rho>_pair_repl_def by auto

lemma ren_action' :
  assumes
    "env\<in>list(M)" "x\<in>M" "y\<in>M" "z\<in>M" "u\<in>M"
  shows "\<forall> i . i < 3#+length(env) \<longrightarrow>
          nth(i,[x,z,u]@env) = nth(\<rho>_pair_repl(length(env))`i,[x,z,y,u]@env)"
proof -
  let ?f="{\<langle>0, 0\<rangle>, \<langle>1, 1\<rangle>, \<langle>2,3\<rangle>}"
  have 1:"(\<And>j. j < length(env) \<Longrightarrow> nth(j, env) = nth(id(length(env)) ` j, env))"
    using assms ltD by simp
  have 2:"nth(j, [x,z,u]) = nth(?f ` j, [x,z,y,u])" if "j<3" for j
  proof -
    consider "j=0" | "j=1" | "j=2" using  ltD[OF \<open>j<3\<close>] by auto
    then show ?thesis
    proof(cases)
      case 1
      then show ?thesis using apply_equality f_type' by simp
    next
      case 2
      then show ?thesis using apply_equality f_type' by simp
    next
      case 3
      then show ?thesis using apply_equality f_type' by simp
    qed
  qed
  show ?thesis
    using sum_action[OF _ _ _ _ f_type' id_type _ _ _ _ _ _ _ 2 1,simplified] assms
    unfolding \<rho>_pair_repl_def by simp
qed

lemma LambdaPair_in_M :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 3 #+ length(env)" and
    fsats: "\<And>x z r. x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> (M,[x,z,r]@env \<Turnstile> \<phi>) \<longleftrightarrow> is_f(x,z,r)" and
    fabs:  "\<And>x z r. x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> is_f(x,z,r) \<longleftrightarrow> r = f(x,z)" and
    fclosed: "\<And>x z. x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> f(x,z) \<in> M" and
    "A\<in>M" "env\<in>list(M)"
  shows "(\<lambda>x\<in>A . f(fst(x),snd(x))) \<in>M"
proof -
  let ?ren="\<rho>_pair_repl(length(env))"
  let ?j="3#+length(env)"
  let ?k="4#+length(env)"
  let ?\<psi>="ren(\<phi>)`?j`?k`?ren"
  let ?\<phi>'="Exists(Exists(And(fst_fm(2,0),(And(snd_fm(2,1),?\<psi>)))))"
  let ?p="\<lambda>x y. is_f(fst(x),snd(x),y)"
  have "?\<phi>'\<in>formula" "?\<psi>\<in>formula"
    using \<open>env\<in>_\<close> length_type f_fm ren_type' ren_tc[of \<phi> ?j ?k ?ren]
    by simp_all
  moreover from this
  have "arity(?\<psi>)\<le>4#+(length(env))" "arity(?\<psi>)\<in>nat"
    using assms arity_ren[OF f_fm _ _ ren_type',of "length(env)"] by simp_all
  moreover from calculation
  have 1:"arity(?\<phi>') \<le> 2#+(length(env))" "?\<phi>'\<in>formula"
    using Un_le pred_Un_distrib assms pred_le
    by (simp_all add:arity)
  moreover from this calculation
  have 2:"x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> ?\<phi>') \<longleftrightarrow> ?p(x,y)" for x y
    using
      sats_iff_sats_ren[OF f_fm _ _ _ _ ren_type' f_ar
         ren_action'[rule_format,of _ "fst(x)" x "snd(x)" y],simplified]
       \<open>env\<in>_\<close> length_type[OF \<open>env\<in>_\<close>] transitivity[OF _ \<open>A\<in>M\<close>]
      fst_snd_closed pair_in_M_iff fsats[of "fst(x)" "snd(x)" y,symmetric]
      fst_abs snd_abs
    by auto
  moreover from assms
  have 3:"x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> ?p(x,y) \<longleftrightarrow> y = f(fst(x),snd(x))" for x y
    using fclosed fst_snd_closed pair_in_M_iff fabs transitivity
    by auto
  moreover
  have 4:"\<And> x . x\<in>A \<Longrightarrow> <x,f(fst(x),snd(x))> \<in> M" "\<And> x . x\<in>A \<Longrightarrow> f(fst(x),snd(x)) \<in> M"
    using transitivity[OF _ \<open>A\<in>M\<close>] pair_in_M_iff fclosed fst_snd_closed
    by simp_all
  ultimately
  show ?thesis
    using Lambda_in_M[of ?\<phi>'] \<open>env\<in>_\<close> \<open>A\<in>_\<close> by simp
qed

simple_rename "ren_U" src "[z1,x_P, x_leq, x_o, x_t, z2_c]"
  tgt "[z2_c,z1,z,x_P, x_leq, x_o, x_t]"

simple_rename "ren_V" src "[fz,x_P, x_leq, x_o,x_f, x_t, gz]"
  tgt "[gz,fz,z,x_P, x_leq, x_o,x_f, x_t]"

simple_rename "ren_V3" src "[fz,x_P, x_leq, x_o,x_f, gz, hz]"
  tgt "[hz,gz,fz,z,x_P, x_leq, x_o,x_f]"

lemma separation_sat_after_function_1:
  assumes "[a,b,c,d]\<in>list(M)" and  "\<chi>\<in>formula" and "arity(\<chi>) \<le> 6"
  and
    f_fm:  "f_fm \<in> formula" and
    f_ar:  "arity(f_fm) \<le> 6" and
    fsats: "\<And> fx x. fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[fx,x]@[a, b, c, d] \<Turnstile> f_fm) \<longleftrightarrow> fx=f(x)" and
    fclosed: "\<And>x . x\<in>M \<Longrightarrow> f(x) \<in> M" and
    g_fm:  "g_fm \<in> formula" and
    g_ar:  "arity(g_fm) \<le> 7" and
    gsats: "\<And> gx fx x. gx\<in>M \<Longrightarrow>  fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[gx,fx,x]@[a, b, c, d] \<Turnstile> g_fm) \<longleftrightarrow> gx=g(x)" and
    gclosed: "\<And>x . x\<in>M \<Longrightarrow> g(x) \<in> M"
  shows  "separation(##M, \<lambda>r. M, [f(r), a, b, c, d, g(r)] \<Turnstile> \<chi>)"
proof -
  note types = assms(1-4)
  let ?\<psi>="ren(\<chi>)`6`7`ren_U_fn"
  let  ?\<psi>'="Exists(And(f_fm,Exists(And(g_fm,?\<psi>))))"
  let ?\<rho>="\<lambda>z.[f(z), a, b, c, d, g(z)]"
  let ?env="[a, b, c, d]"
  let ?\<eta>="\<lambda>z.[g(z),f(z),z]@?env"
  note types
  moreover from this
  have "arity(\<chi>) \<le> 7" "?\<psi>\<in>formula"
    using ord_simp_union ren_tc ren_U_thm(2)[folded ren_U_fn_def] le_trans[of "arity(\<chi>)" 6]
      by simp_all
  moreover from calculation
  have "arity(?\<psi>) \<le> 7" "?\<psi>'\<in>formula"
    using arity_ren ren_U_thm(2)[folded ren_U_fn_def] f_fm g_fm
     by simp_all
  moreover from calculation f_ar g_ar f_fm g_fm
  have "arity(?\<psi>') \<le> 5"
    using ord_simp_union pred_le arity_type
    by (simp add:arity)
  moreover from calculation fclosed gclosed
  have 0:"(M, [f(z), a, b, c, d,  g(z)] \<Turnstile> \<chi>) \<longleftrightarrow> (M,?\<eta>(z)\<Turnstile> ?\<psi>)" if "(##M)(z)" for z
    using sats_iff_sats_ren[of \<chi> 6 7 _ _ "?\<eta>(z)"]
      ren_U_thm(1)[where A=M,folded ren_U_fn_def] ren_U_thm(2)[folded ren_U_fn_def] that
    by simp
  moreover from calculation
  have 1:"(M,?\<eta>(z)\<Turnstile> ?\<psi>) \<longleftrightarrow> M,[z]@?env\<Turnstile>?\<psi>'" if "(##M)(z)" for z
    using that fsats[OF fclosed[of z],of z]  gsats[of "g(z)" "f(z)" z] fclosed gclosed f_fm g_fm
  proof(rule_tac iffI,simp,rule_tac rev_bexI[where x="f(z)"],simp,(auto)[1])
    assume "M, [z] @ [a, b, c, d] \<Turnstile> (\<cdot>\<exists>\<cdot>f_fm \<and> (\<cdot>\<exists>\<cdot>g_fm \<and> ren(\<chi>) ` 6 ` 7 ` ren_U_fn\<cdot>\<cdot>)\<cdot>\<cdot>)"
    then
    have "\<exists>xa\<in>M. (M, [xa, z, a, b, c, d] \<Turnstile> f_fm) \<and>
          (\<exists>x\<in>M. (M, [x, xa, z, a, b, c, d] \<Turnstile> g_fm) \<and>
            (M, [x, xa, z, a, b, c, d] \<Turnstile> ren(\<chi>) ` 6 ` 7 ` ren_U_fn))"
      using that calculation by auto
    then
    obtain xa x where "x\<in>M" "xa\<in>M" "M, [xa, z, a, b, c, d] \<Turnstile> f_fm"
        "(M, [x, xa, z, a, b, c, d] \<Turnstile> g_fm)"
        "(M, [x, xa, z, a, b, c, d] \<Turnstile> ren(\<chi>) ` 6 ` 7 ` ren_U_fn)"
      using that calculation by auto
    moreover from this
    have "xa=f(z)" "x=g(z)" using fsats[of xa]  gsats[of x xa] that by simp_all
    ultimately
    show "M, [g(z), f(z), z] @ [a, b, c, d] \<Turnstile> ren(\<chi>) ` 6 ` 7 ` ren_U_fn"
      by auto
  qed
  moreover from calculation
  have "separation(##M, \<lambda>z. (M,[z]@?env \<Turnstile> ?\<psi>'))"
    using separation_ax
      by simp_all
  ultimately
  show ?thesis
    by(rule_tac separation_cong[THEN iffD2,OF iff_trans[OF 0 1]],clarify,force)
qed

lemma separation_sat_after_function3:
  assumes "[a, b, c, d]\<in>list(M)" and  "\<chi>\<in>formula" and "arity(\<chi>) \<le> 7"
  and
    f_fm:  "f_fm \<in> formula" and
    f_ar:  "arity(f_fm) \<le> 6" and
    fsats: "\<And> fx x. fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[fx,x]@[a, b, c, d] \<Turnstile> f_fm) \<longleftrightarrow> fx=f(x)" and
    fclosed: "\<And>x . x\<in>M \<Longrightarrow> f(x) \<in> M" and
    g_fm:  "g_fm \<in> formula" and
    g_ar:  "arity(g_fm) \<le> 7" and
    gsats: "\<And> gx fx x. gx\<in>M \<Longrightarrow> fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[gx,fx,x]@[a, b, c, d] \<Turnstile> g_fm) \<longleftrightarrow> gx=g(x)" and
    gclosed: "\<And>x . x\<in>M \<Longrightarrow> g(x) \<in> M" and
    h_fm:  "h_fm \<in> formula" and
    h_ar:  "arity(h_fm) \<le> 8" and
    hsats: "\<And> hx gx fx x. hx\<in>M \<Longrightarrow> gx\<in>M \<Longrightarrow> fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[hx,gx,fx,x]@[a, b, c, d] \<Turnstile> h_fm) \<longleftrightarrow> hx=h(x)" and
    hclosed: "\<And>x . x\<in>M \<Longrightarrow> h(x) \<in> M"
shows  "separation(##M, \<lambda>r. M, [f(r), a, b, c, d, g(r), h(r)] \<Turnstile> \<chi>)"
proof -
  note types = assms(1-3)
  let ?\<phi>="\<chi>"
  let ?\<psi>="ren(?\<phi>)`7`8`ren_V3_fn"
  let ?\<psi>'="Exists(And(f_fm,Exists(And(g_fm,Exists(And(h_fm,?\<psi>))))))"
  let ?\<rho>="\<lambda>z.[f(z), a, b, c, d,g(z), h(z)]"
  let ?env="[a, b, c, d]"
  let ?\<eta>="\<lambda>z.[h(z),g(z),f(z),z]@?env"
  note types
  moreover from this
  have "?\<phi>\<in>formula" by simp
  moreover from calculation
  have "arity(?\<phi>) \<le> 9" "?\<psi>\<in>formula"
    using ord_simp_union ren_tc ren_V3_thm(2)[folded ren_V3_fn_def] le_trans[of "arity(\<chi>)" 7]
      by simp_all
  moreover from calculation
  have "arity(?\<psi>) \<le> 8" "?\<psi>'\<in>formula"
    using arity_ren ren_V3_thm(2)[folded ren_V3_fn_def] f_fm g_fm h_fm
    by (simp_all)
  moreover from this f_ar g_ar f_fm g_fm h_fm h_ar \<open>?\<psi>'\<in>_\<close>
  have "arity(?\<psi>') \<le> 5"
    using ord_simp_union arity_type nat_into_Ord
    by (simp add:arity,(rule_tac pred_le,simp,rule_tac Un_le,simp)+,simp_all add: \<open>?\<psi>\<in>_\<close>)
  moreover from calculation fclosed gclosed hclosed
  have 0:"(M, ?\<rho>(z) \<Turnstile> ?\<phi>) \<longleftrightarrow> (M,?\<eta>(z)\<Turnstile> ?\<psi>)" if "(##M)(z)" for z
    using sats_iff_sats_ren[of ?\<phi> 7 8 "?\<rho>(z)" M "?\<eta>(z)"]
      ren_V3_thm(1)[where A=M,folded ren_V3_fn_def,simplified] ren_V3_thm(2)[folded ren_V3_fn_def] that
    by simp
  moreover from calculation
  have 1:"(M,?\<eta>(z)\<Turnstile> ?\<psi>) \<longleftrightarrow> M,[z]@?env\<Turnstile>?\<psi>'" if "(##M)(z)" for z
    using that fsats[OF fclosed[of z],of z] gsats[of "g(z)" "f(z)" z]
      hsats[of "h(z)" "g(z)" "f(z)" z]
      fclosed gclosed hclosed f_fm g_fm h_fm
    apply(rule_tac iffI,simp,rule_tac rev_bexI[where x="f(z)"],simp)
     apply(rule_tac conjI,simp,rule_tac rev_bexI[where x="g(z)"],simp)
    apply(rule_tac conjI,simp,rule_tac rev_bexI[where x="h(z)"],simp,rule_tac conjI,simp,simp)
  proof -
    assume "M, [z] @ [a, b, c, d] \<Turnstile> (\<cdot>\<exists>\<cdot>f_fm \<and> (\<cdot>\<exists>\<cdot>g_fm \<and> (\<cdot>\<exists>\<cdot>h_fm \<and> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn\<cdot>\<cdot>)\<cdot>\<cdot>)\<cdot>\<cdot>)"
    with calculation that
    have "\<exists>x\<in>M. (M, [x, z, a, b, c, d] \<Turnstile> f_fm) \<and>
           (\<exists>xa\<in>M. (M, [xa, x, z, a, b, c, d] \<Turnstile> g_fm) \<and> (\<exists>xb\<in>M. (M, [xb, xa, x, z, a, b, c, d] \<Turnstile> h_fm) \<and> (M, [xb, xa, x, z, a, b, c, d] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn)))"
      by auto
    with calculation
    obtain x where "x\<in>M" "(M, [x, z, a, b, c, d] \<Turnstile> f_fm)"
        "(\<exists>xa\<in>M. (M, [xa, x, z, a, b, c, d] \<Turnstile> g_fm) \<and> (\<exists>xb\<in>M. (M, [xb, xa, x, z, a, b, c, d] \<Turnstile> h_fm) \<and> (M, [xb, xa, x, z, a, b, c, d] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn)))"
      by force
    moreover from this
    have "x=f(z)" using fsats[of x] that by simp
    moreover from calculation
    obtain xa where "xa\<in>M" "(M, [xa, x, z, a, b, c, d] \<Turnstile> g_fm)"
      "(\<exists>xb\<in>M. (M, [xb, xa, x, z, a, b, c, d] \<Turnstile> h_fm) \<and> (M, [xb, xa, x, z, a, b, c, d] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn))"
      by auto
    moreover from calculation
    have "xa=g(z)" using gsats[of xa x] that by simp
    moreover from calculation
    obtain xb where "xb\<in>M" "(M, [xb, xa, x, z, a, b, c, d] \<Turnstile> h_fm)"
      "(M, [xb, xa, x, z, a, b, c, d] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn)"
      by auto
    moreover from calculation
    have "xb=h(z)" using hsats[of xb xa x] that by simp
    ultimately
    show "M, [h(z), g(z), f(z), z] @ [a, b, c, d] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn"
      by auto
  qed
  moreover from calculation \<open>?\<psi>'\<in>_\<close>
  have 2:"separation(##M, \<lambda>z. (M,[z]@?env \<Turnstile> ?\<psi>'))"
    using separation_ax
    by simp
  ultimately
  show ?thesis
    by(rule_tac separation_cong[THEN iffD2,OF iff_trans[OF 0 1]],clarify,force)
qed

lemma separation_sat_after_function:
  assumes "[a, b, c, d, \<tau>]\<in>list(M)" and  "\<chi>\<in>formula" and "arity(\<chi>) \<le> 7"
  and
    f_fm:  "f_fm \<in> formula" and
    f_ar:  "arity(f_fm) \<le> 7" and
    fsats: "\<And> fx x. fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[fx,x]@[a, b, c, d, \<tau>] \<Turnstile> f_fm) \<longleftrightarrow> fx=f(x)" and
    fclosed: "\<And>x . x\<in>M \<Longrightarrow> f(x) \<in> M" and
    g_fm:  "g_fm \<in> formula" and
    g_ar:  "arity(g_fm) \<le> 8" and
    gsats: "\<And> gx fx x. gx\<in>M \<Longrightarrow>  fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[gx,fx,x]@[a, b, c, d, \<tau>] \<Turnstile> g_fm) \<longleftrightarrow> gx=g(x)" and
    gclosed: "\<And>x . x\<in>M \<Longrightarrow> g(x) \<in> M"
  shows  "separation(##M, \<lambda>r. M, [f(r), a, b, c, d, \<tau>, g(r)] \<Turnstile> \<chi>)"
proof -
  note types = assms(1-3)
  let ?\<phi>="\<chi>"
  let ?\<psi>="ren(?\<phi>)`7`8`ren_V_fn"
  let  ?\<psi>'="Exists(And(f_fm,Exists(And(g_fm,?\<psi>))))"
  let ?\<rho>="\<lambda>z.[f(z), a, b, c, d, \<tau>, g(z)]"
  let ?env="[a, b, c, d, \<tau>]"
  let ?\<eta>="\<lambda>z.[g(z),f(z),z]@?env"
  note types
  moreover from this
  have "?\<phi>\<in>formula" by simp
  moreover from calculation
  have "arity(?\<phi>) \<le> 8" "?\<psi>\<in>formula"
    using ord_simp_union ren_tc ren_V_thm(2)[folded ren_V_fn_def] le_trans[of "arity(\<chi>)" 7]
      by simp_all
  moreover from calculation
  have "arity(?\<psi>) \<le> 8" "?\<psi>'\<in>formula"
    using arity_ren ren_V_thm(2)[folded ren_V_fn_def] f_fm g_fm
     by (simp_all)
  moreover from calculation f_ar g_ar f_fm g_fm
  have "arity(?\<psi>') \<le> 6"
    using ord_simp_union pred_le arity_type
    by (simp add:arity)
  moreover from calculation fclosed gclosed
  have 0:"(M, ?\<rho>(z) \<Turnstile> ?\<phi>) \<longleftrightarrow> (M,?\<eta>(z)\<Turnstile> ?\<psi>)" if "(##M)(z)" for z
    using sats_iff_sats_ren[of ?\<phi> 7 8 "?\<rho>(z)" _ "?\<eta>(z)"]
      ren_V_thm(1)[where A=M,folded ren_V_fn_def] ren_V_thm(2)[folded ren_V_fn_def] that
    by simp
  moreover from calculation
  have 1:"(M,?\<eta>(z)\<Turnstile> ?\<psi>) \<longleftrightarrow> M,[z]@?env\<Turnstile>?\<psi>'" if "(##M)(z)" for z
    using that fsats[OF fclosed[of z],of z]  gsats[of "g(z)" "f(z)" z]
      fclosed gclosed f_fm g_fm
    apply(rule_tac iffI,simp,rule_tac rev_bexI[where x="f(z)"],simp)
    apply(auto)[1]
  proof -
    assume "M, [z] @ [a, b, c, d, \<tau>] \<Turnstile> (\<cdot>\<exists>\<cdot>f_fm \<and> (\<cdot>\<exists>\<cdot>g_fm \<and> ren(\<chi>) ` 7 ` 8 ` ren_V_fn\<cdot>\<cdot>)\<cdot>\<cdot>)"
    then have "\<exists>xa\<in>M. (M, [xa, z, a, b, c, d, \<tau>] \<Turnstile> f_fm) \<and>
       (\<exists>x\<in>M. (M, [x, xa, z, a, b, c, d, \<tau>] \<Turnstile> g_fm) \<and> (M, [x, xa, z, a, b, c, d, \<tau>] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V_fn))"
      using that calculation by auto
    then
    obtain xa where "xa\<in>M" "M, [xa, z, a, b, c, d, \<tau>] \<Turnstile> f_fm"
        "(\<exists>x\<in>M. (M, [x, xa, z, a, b, c, d, \<tau>] \<Turnstile> g_fm) \<and> (M, [x, xa, z, a, b, c, d, \<tau>] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V_fn))"
      by auto
    moreover from this
    have "xa=f(z)" using fsats[of xa] that by simp
    moreover from calculation
    obtain x where "x\<in>M" "M, [x, xa, z, a, b, c, d, \<tau>] \<Turnstile> g_fm" "M, [x, xa, z, a, b, c, d, \<tau>] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V_fn"
      by auto
    moreover from calculation
    have "x=g(z)" using gsats[of x xa] that by simp
    ultimately
    show "M, [g(z), f(z), z] @ [a, b, c, d, \<tau>] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V_fn"
      by auto
  qed
  moreover from calculation
  have 2:"separation(##M, \<lambda>z. (M,[z]@?env \<Turnstile> ?\<psi>'))"
    using separation_ax
      by simp_all
  ultimately
  show ?thesis
    by(rule_tac separation_cong[THEN iffD2,OF iff_trans[OF 0 1]],clarify,force)
qed

end \<comment> \<open>\<^locale>\<open>M_ZF_trans\<close>\<close>

end