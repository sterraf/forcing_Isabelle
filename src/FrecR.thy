theory FrecR imports Interface Names begin


(* Preliminary *)
definition
  ftype :: "i\<Rightarrow>i" where
  "ftype == fst"

definition
  name1 :: "i\<Rightarrow>i" where
  "name1(x) == fst(snd(x))"

definition
  name2 :: "i\<Rightarrow>i" where
  "name2(x) == fst(snd(snd(x)))"

definition
   cond_of :: "i\<Rightarrow>i" where
  "cond_of(x) == snd(snd(snd((x))))"

lemma components_simp [simp]:
  "ftype(<f,n1,n2,c>) = f"
  "name1(<f,n1,n2,c>) = n1"
  "name2(<f,n1,n2,c>) = n2"
  "cond_of(<f,n1,n2,c>) = c"
  unfolding ftype_def name1_def name2_def cond_of_def
  by simp_all


lemma trans_eclose :
  " x \<in> eclose(A) \<Longrightarrow> y \<in> x \<Longrightarrow> y \<in> eclose(A)"
  using Transset_intf[OF Transset_eclose]
  by simp


lemma arg_into_eclose2 :
  assumes
    "n\<notin>A \<Longrightarrow> B\<in>eclose(A)" "n\<notin>A \<Longrightarrow> n\<in>B" 
  shows
    "n\<in>eclose(A)" 
  using assms trans_eclose arg_into_eclose by blast

lemma components_in_eclose : 
  "n1 \<in> eclose(<f,n1,n2,c>)"
  "n2 \<in> eclose(<f,n1,n2,c>)"
  unfolding Pair_def 
  by (rule arg_into_eclose2 ; auto)+

definition
  is_ftype :: "(i\<Rightarrow>o)\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "is_ftype(M,x,t1) == \<exists>z[M]. pair(M,t1,z,x)"

definition
  is_name1 :: "(i\<Rightarrow>o)\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "is_name1(M,x,t2) == \<exists>t1[M]. \<exists>z[M]. \<exists>w[M]. pair(M,t1,z,x) \<and> pair(M,t2,w,z)"

definition
  is_name2 :: "(i\<Rightarrow>o)\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "is_name2(M,x,t3) == \<exists>t1[M]. \<exists>z[M]. \<exists>t2[M]. \<exists>w[M]. \<exists>t4[M].
                           pair(M,t1,z,x) \<and> pair(M,t2,w,z) \<and> pair(M,t3,t4,w)"

definition
  is_cond_of :: "(i\<Rightarrow>o)\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "is_cond_of(M,x,t4) == \<exists>t1[M]. \<exists>z[M]. \<exists>t2[M]. \<exists>w[M]. \<exists>t3[M].
                           pair(M,t1,z,x) \<and> pair(M,t2,w,z) \<and> pair(M,t3,t4,w)"

definition
  is_one :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
  "is_one(M,o) == \<forall>z[M]. z\<in>o \<longleftrightarrow> empty(M,z)"

lemma (in M_trivial) is_one_abs [simp]:
     "M(o) ==> is_one(M,o) \<longleftrightarrow> o=1"
  by (simp add: is_one_def,blast intro: transM)

(* Already in Constructible, under "number1_fm" but with 
  an unnecessary, harmful assumption *)
schematic_goal sats_is_one_fm_auto:
  assumes 
    "z\<in>nat" "env\<in>list(A)"
  shows
    "is_one(##A,nth(z, env))
    \<longleftrightarrow> sats(A,?io_fm(z),env)"
    and
    "(?io_fm(z) \<in> formula)"
   unfolding is_one_def  
   by (insert assms ; (rule sep_rules | simp))+

schematic_goal is_one_iff_sats :
  assumes
    "nth(i,env) = x" "i \<in> nat"  "env \<in> list(A)"
  shows
       "is_one(##A, x) \<longleftrightarrow> sats(A, ?is_one_fm(i), env)"
  unfolding \<open>nth(i,env) = x\<close>[symmetric] 
  by (rule sats_is_one_fm_auto(1); simp add:assms)

(* Relation of forces *)
definition
  frecR :: "i \<Rightarrow> i \<Rightarrow> o" where
  "frecR(x,y) \<equiv>
    (ftype(x) = 1 \<and> ftype(y) = 0 
      \<and> (name1(x) \<in> domain(name1(y)) \<union> domain(name2(y)) \<and> (name2(x) = name1(y) \<or> name2(x) = name2(y))))
   \<or> (ftype(x) = 0 \<and> ftype(y) =  1 \<and> name1(x) = name1(y) \<and> name2(x) \<in> domain(name2(y)))"

lemma frecR_ftypeD :
  assumes "frecR(x,y)"
  shows "(ftype(x) = 0 \<and> ftype(y) = 1) \<or> (ftype(x) = 1 \<and> ftype(y) = 0)"
  using assms unfolding frecR_def by auto

lemma frecRI1: "s \<in> domain(n1) \<or> s \<in> domain(n2) \<Longrightarrow> frecR(\<langle>1, s, n1, q\<rangle>, \<langle>0, n1, n2, q'\<rangle>)"
  unfolding frecR_def by simp

lemma frecRI1': "s \<in> domain(n1) \<union> domain(n2) \<Longrightarrow> frecR(\<langle>1, s, n1, q\<rangle>, \<langle>0, n1, n2, q'\<rangle>)"
  unfolding frecR_def by simp

lemma frecRI2: "s \<in> domain(n1) \<or> s \<in> domain(n2) \<Longrightarrow> frecR(\<langle>1, s, n2, q\<rangle>, \<langle>0, n1, n2, q'\<rangle>)"
  unfolding frecR_def by simp

lemma frecRI2': "s \<in> domain(n1) \<union> domain(n2) \<Longrightarrow> frecR(\<langle>1, s, n2, q\<rangle>, \<langle>0, n1, n2, q'\<rangle>)"
  unfolding frecR_def by simp


lemma frecRI3: "\<langle>s, r\<rangle> \<in> n2 \<Longrightarrow> frecR(\<langle>0, n1, s, q\<rangle>, \<langle>1, n1, n2, q'\<rangle>)"
  unfolding frecR_def by auto

lemma frecRI3': "s \<in> domain(n2) \<Longrightarrow> frecR(\<langle>0, n1, s, q\<rangle>, \<langle>1, n1, n2, q'\<rangle>)"
  unfolding frecR_def by auto


lemma frecR_iff [iff] :
  "frecR(x,y) \<longleftrightarrow>
    (ftype(x) = 1 \<and> ftype(y) = 0 
      \<and> (name1(x) \<in> domain(name1(y)) \<union> domain(name2(y)) \<and> (name2(x) = name1(y) \<or> name2(x) = name2(y))))
   \<or> (ftype(x) = 0 \<and> ftype(y) =  1 \<and> name1(x) = name1(y) \<and> name2(x) \<in> domain(name2(y)))"
  unfolding frecR_def ..

lemma frecR_D1 :
  "frecR(x,y) \<Longrightarrow> ftype(y) = 0 \<Longrightarrow> ftype(x) = 1 \<and> 
      (name1(x) \<in> domain(name1(y)) \<union> domain(name2(y)) \<and> (name2(x) = name1(y) \<or> name2(x) = name2(y)))"
  by auto

lemma frecR_D2 :
  "frecR(x,y) \<Longrightarrow> ftype(y) = 1 \<Longrightarrow> ftype(x) = 0 \<and> 
      ftype(x) = 0 \<and> ftype(y) =  1 \<and> name1(x) = name1(y) \<and> name2(x) \<in> domain(name2(y))"
  by auto

lemma frecR_DI : 
  assumes "frecR(<a,b,c,d>,<ftype(y),name1(y),name2(y),cond_of(y)>)"
  shows "frecR(<a,b,c,d>,y)"
  using assms unfolding frecR_def by force

(* Punto 3 de p. 257 de Kunen *)
lemma eq_ftypep_not_frecrR:
  assumes "ftype(x) = ftype(y)"
  shows "\<not> frecR(x,y)"
  using assms frecR_ftypeD by force


definition
  rank_names :: "i \<Rightarrow> i" where
  "rank_names(x) == max(rank(name1(x)),rank(name2(x)))"

lemma rank_names_types [TC]: 
  shows "Ord(rank_names(x))"
  unfolding rank_names_def max_def using Ord_rank Ord_Un by auto

definition
  mtype_form :: "i \<Rightarrow> i" where
  "mtype_form(x) == if rank(name1(x)) < rank(name2(x)) then 0 else 2"

definition
  type_form :: "i \<Rightarrow> i" where
  "type_form(x) == if ftype(x) = 0 then 1 else mtype_form(x)"

lemma type_form_tc [TC]: 
  shows "type_form(x) \<in> 3"
  unfolding type_form_def mtype_form_def by auto

lemma frecR_le_rnk_names :
  assumes  "frecR(x,y)"
  shows "rank_names(x)\<le>rank_names(y)"
proof -
  obtain a b c d  where
    H: "a = name1(x)" "b = name2(x)"
    "c = name1(y)" "d = name2(y)"
    "(a \<in> domain(c)\<union>domain(d) \<and> (b=c \<or> b = d)) \<or> (a = c \<and> b \<in> domain(d))"
    using assms unfolding frecR_def by force
  then 
  consider
    (m) "a \<in> domain(c) \<and> (b = c \<or> b = d) "
    | (n) "a \<in> domain(d) \<and> (b = c \<or> b = d)" 
    | (o) "b \<in> domain(d) \<and> a = c"
    by auto
  then show ?thesis proof(cases)
    case m
    then 
    have "rank(a) < rank(c)" 
      using eclose_rank_lt  in_dom_in_eclose  by simp
    with \<open>rank(a) < rank(c)\<close> H m
    show ?thesis unfolding rank_names_def using Ord_rank max_cong max_cong2 leI by auto
  next
    case n
    then
    have "rank(a) < rank(d)"
      using eclose_rank_lt in_dom_in_eclose  by simp
    with \<open>rank(a) < rank(d)\<close> H n
    show ?thesis unfolding rank_names_def 
      using Ord_rank max_cong2 max_cong max_commutes[of "rank(c)" "rank(d)"] leI by auto
  next
    case o
    then
    have "rank(b) < rank(d)" (is "?b < ?d") "rank(a) = rank(c)" (is "?a = _")
      using eclose_rank_lt in_dom_in_eclose  by simp_all
    with H
    show ?thesis unfolding rank_names_def
      using Ord_rank max_commutes max_cong2[OF leI[OF \<open>?b < ?d\<close>], of ?a] by simp
  qed
qed


definition 
  \<Gamma> :: "i \<Rightarrow> i" where
  "\<Gamma>(x) = 3 ** rank_names(x) ++ type_form(x)"

lemma \<Gamma>_type [TC]: 
  shows "Ord(\<Gamma>(x))"
  unfolding \<Gamma>_def by simp


lemma \<Gamma>_mono : 
  assumes "frecR(x,y)"
  shows "\<Gamma>(x) < \<Gamma>(y)"
proof -
  have F: "type_form(x) < 3" "type_form(y) < 3"
    using ltI by simp_all
  from assms 
  have A: "rank_names(x) \<le> rank_names(y)" (is "?x \<le> ?y")
    using frecR_le_rnk_names by simp
  then
  have "Ord(?y)" unfolding rank_names_def using Ord_rank max_def by simp
  note leE[OF \<open>?x\<le>?y\<close>] 
  then
  show ?thesis
  proof(cases)
    case 1
    then 
    show ?thesis unfolding \<Gamma>_def using oadd_lt_mono2 \<open>?x < ?y\<close> F by auto
  next
    case 2
    consider (a) "ftype(x) = 0 \<and> ftype(y) = 1" | (b) "ftype(x) = 1 \<and> ftype(y) = 0"
      using  frecR_ftypeD[OF \<open>frecR(x,y)\<close>] by auto
    then show ?thesis proof(cases)
      case b
      then 
      have "type_form(y) = 1" 
        using type_form_def by simp
      from b
      have H: "name2(x) = name1(y) \<or> name2(x) = name2(y) " (is "?\<tau> = ?\<sigma>' \<or> ?\<tau> = ?\<tau>'")
           "name1(x) \<in> domain(name1(y)) \<union> domain(name2(y))" 
              (is "?\<sigma> \<in> domain(?\<sigma>') \<union> domain(?\<tau>')")
        using assms unfolding type_form_def frecR_def by auto
      then 
      have E: "rank(?\<tau>) = rank(?\<sigma>') \<or> rank(?\<tau>) = rank(?\<tau>')" by auto
      from H
      consider (a) "rank(?\<sigma>) < rank(?\<sigma>')" |  (b) "rank(?\<sigma>) < rank(?\<tau>')"
          using eclose_rank_lt in_dom_in_eclose by force
        then
        have "rank(?\<sigma>) < rank(?\<tau>)" proof (cases)
          case a
          with \<open>rank_names(x) = rank_names(y) \<close>
          show ?thesis unfolding rank_names_def mtype_form_def type_form_def using max_D2[OF E a]
                E assms Ord_rank by simp
        next
          case b
          with \<open>rank_names(x) = rank_names(y) \<close>
          show ?thesis unfolding rank_names_def mtype_form_def type_form_def 
            using max_D2[OF _ b] max_commutes E assms Ord_rank disj_commute by auto
        qed
        with b
        have "type_form(x) = 0" unfolding type_form_def mtype_form_def by simp
      with \<open>rank_names(x) = rank_names(y) \<close> \<open>type_form(y) = 1\<close> \<open>type_form(x) = 0\<close>
       show ?thesis 
         unfolding \<Gamma>_def by auto
    next
      case a
      then 
      have "name1(x) = name1(y)" (is "?\<sigma> = ?\<sigma>'") 
           "name2(x) \<in> domain(name2(y))" (is "?\<tau> \<in> domain(?\<tau>')")
           "type_form(x) = 1"
        using assms unfolding type_form_def frecR_def by auto
      then
      have "rank(?\<sigma>) = rank(?\<sigma>')" "rank(?\<tau>) < rank(?\<tau>')" 
        using  eclose_rank_lt in_dom_in_eclose by simp_all
       with \<open>rank_names(x) = rank_names(y) \<close> 
       have "rank(?\<tau>') \<le> rank(?\<sigma>')" 
         unfolding rank_names_def using Ord_rank max_D1 by simp
      with a
      have "type_form(y) = 2"
        unfolding type_form_def mtype_form_def using not_lt_iff_le assms by simp
      with \<open>rank_names(x) = rank_names(y) \<close> \<open>type_form(y) = 2\<close> \<open>type_form(x) = 1\<close>
       show ?thesis 
         unfolding \<Gamma>_def by auto
    qed
  qed
qed


definition
  frecrel :: "i \<Rightarrow> i" where
  "frecrel(A) \<equiv> Rrel(frecR,A)"

lemma frecrelI : 
  assumes "x \<in> A" "y\<in>A" "frecR(x,y)"
  shows "<x,y>\<in>frecrel(A)"
  using assms unfolding frecrel_def Rrel_def by auto

lemma frecrelD :
  assumes "<x,y> \<in> frecrel(A1\<times>A2\<times>A3\<times>A4)"
  shows "ftype(x) \<in> A1" "ftype(x) \<in> A1"
    "name1(x) \<in> A2" "name1(y) \<in> A2" "name2(x) \<in> A3" "name2(x) \<in> A3" 
    "cond_of(x) \<in> A4" "cond_of(y) \<in> A4" 
    "frecR(x,y)"
  using assms unfolding frecrel_def Rrel_def ftype_def by auto

lemma wf_frecrel : 
  shows "wf(frecrel(A))"
proof -
  have "frecrel(A) \<subseteq> measure(A,\<Gamma>)"
    unfolding frecrel_def Rrel_def measure_def
    using \<Gamma>_mono by force
  then show ?thesis using wf_subset wf_measure by auto
qed

lemma core_induction_aux:
  fixes A1 A2 :: "i"
  assumes
    "Transset(A1)"
    "\<And>\<tau> \<theta> p.  p \<in> A2 \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk> q\<in>A2 ; \<sigma>\<in>domain(\<theta>)\<rbrakk> \<Longrightarrow> Q(0,\<tau>,\<sigma>,q)\<rbrakk> \<Longrightarrow> Q(1,\<tau>,\<theta>,p)"
    "\<And>\<tau> \<theta> p.  p \<in> A2 \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk> q\<in>A2 ; \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)\<rbrakk> \<Longrightarrow> Q(1,\<sigma>,\<tau>,q) \<and> Q(1,\<sigma>,\<theta>,q)\<rbrakk> \<Longrightarrow> Q(0,\<tau>,\<theta>,p)"
  shows "a\<in>2\<times>A1\<times>A1\<times>A2 \<Longrightarrow> Q(ftype(a),name1(a),name2(a),cond_of(a))"
proof (induct a rule:wf_induct[OF wf_frecrel[of "2\<times>A1\<times>A1\<times>A2"]])
   case (1 x)
   let ?\<tau> = "name1(x)" 
   let ?\<theta> = "name2(x)"
   let ?D = "2\<times>A1\<times>A1\<times>A2"
   assume "x \<in> ?D"
   then
   have "cond_of(x)\<in>A2" 
     by auto
   from \<open>x\<in>?D\<close>
   consider (eq) "ftype(x)=0" | (mem) "ftype(x)=1"
     by auto
   then 
   show ?case 
   proof cases
     case eq
     then 
     have "Q(1, \<sigma>, ?\<tau>, q) \<and> Q(1, \<sigma>, ?\<theta>, q)" if "\<sigma> \<in> domain(?\<tau>) \<union> domain(?\<theta>)" and "q\<in>A2" for q \<sigma>
     proof -
       from 1
       have A: "?\<tau>\<in>A1" "?\<theta>\<in>A1" "?\<tau>\<in>eclose(A1)" "?\<theta>\<in>eclose(A1)"
         using  arg_into_eclose by auto
       with  \<open>Transset(A1)\<close> that(1)
       have "\<sigma>\<in>eclose(?\<tau>) \<union> eclose(?\<theta>)" 
         using in_dom_in_eclose  by auto
       then
       have "\<sigma>\<in>A1"
         using mem_eclose_subset[OF \<open>?\<tau>\<in>A1\<close>] mem_eclose_subset[OF \<open>?\<theta>\<in>A1\<close>] 
           Transset_eclose_eq_arg[OF \<open>Transset(A1)\<close>] 
         by auto         
       with \<open>q\<in>A2\<close> \<open>?\<theta> \<in> A1\<close> \<open>cond_of(x)\<in>A2\<close> \<open>?\<tau>\<in>A1\<close>
       have "frecR(<1, \<sigma>, ?\<tau>, q>, x)" (is "frecR(?T,_)")
            "frecR(<1, \<sigma>, ?\<theta>, q>, x)" (is "frecR(?U,_)")
        using  frecRI1'[OF that(1)] frecR_DI  \<open>ftype(x) = 0\<close> 
                frecRI2'[OF that(1)] 
         by auto
       with \<open>x\<in>?D\<close> \<open>\<sigma>\<in>A1\<close> \<open>q\<in>A2\<close>
       have "<?T,x>\<in> frecrel(?D)" "<?U,x>\<in> frecrel(?D)" 
         using frecrelI[of ?T ?D x]  frecrelI[of ?U ?D x] by auto
       with \<open>q\<in>A2\<close> \<open>\<sigma>\<in>A1\<close> \<open>?\<tau>\<in>A1\<close> \<open>?\<theta>\<in>A1\<close>
       have A:"Q(1, \<sigma>, ?\<tau>, q)" using 1 by force
       from \<open>q\<in>A2\<close> \<open>\<sigma>\<in>A1\<close> \<open>?\<tau>\<in>A1\<close> \<open>?\<theta>\<in>A1\<close> \<open><?U,x>\<in> frecrel(?D)\<close>
       have "Q(1, \<sigma>, ?\<theta>, q)" using 1 by force
       then
       show ?thesis using A by simp
     qed
     then show ?thesis using assms(3) \<open>ftype(x) = 0\<close> \<open>cond_of(x)\<in>A2\<close> by auto
   next
     case mem
     have "Q(0, ?\<tau>,  \<sigma>, q)" if "\<sigma> \<in> domain(?\<theta>)" and "q\<in>A2" for q \<sigma>
     proof -
       from 1 assms
       have A: "?\<tau>\<in>A1" "?\<theta>\<in>A1" "cond_of(x)\<in>A2" "?\<tau>\<in>eclose(A1)" "?\<theta>\<in>eclose(A1)"
         using  arg_into_eclose by auto
       with  \<open>Transset(A1)\<close> that(1)
       have "\<sigma>\<in> eclose(?\<theta>)" 
         using in_dom_in_eclose  by auto
       then
       have "\<sigma>\<in>A1"
         using mem_eclose_subset[OF \<open>?\<theta>\<in>A1\<close>] Transset_eclose_eq_arg[OF \<open>Transset(A1)\<close>] 
         by auto         
       with \<open>q\<in>A2\<close> \<open>?\<theta> \<in> A1\<close> \<open>cond_of(x)\<in>A2\<close> \<open>?\<tau>\<in>A1\<close>
       have "frecR(<0, ?\<tau>, \<sigma>, q>, x)" (is "frecR(?T,_)")
        using  frecRI3'[OF that(1)] frecR_DI  \<open>ftype(x) = 1\<close>                 
         by auto
       with \<open>x\<in>?D\<close> \<open>\<sigma>\<in>A1\<close> \<open>q\<in>A2\<close> \<open>?\<tau>\<in>A1\<close>
       have "<?T,x>\<in> frecrel(?D)" "?T\<in>?D"
         using frecrelI[of ?T ?D x] by auto
       with \<open>q\<in>A2\<close> \<open>\<sigma>\<in>A1\<close> \<open>?\<tau>\<in>A1\<close> \<open>?\<theta>\<in>A1\<close>
       show ?thesis using 1 by force
     qed
     then show ?thesis using assms(2) \<open>ftype(x) = 1\<close> \<open>cond_of(x)\<in>A2\<close>  by auto
   qed
 qed

lemma def_frecrel : "frecrel(A) = {z\<in>A\<times>A. \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x,y)}"
  unfolding frecrel_def Rrel_def ..

lemma frecrel_fst_snd:
  "frecrel(A) = {z \<in> A\<times>A . 
            ftype(fst(z)) = 1 \<and> 
        ftype(snd(z)) = 0 \<and> name1(fst(z)) \<in> domain(name1(snd(z))) \<union> domain(name2(snd(z))) \<and> 
            (name2(fst(z)) = name1(snd(z)) \<or> name2(fst(z)) = name2(snd(z))) 
          \<or> (ftype(fst(z)) = 0 \<and> 
        ftype(snd(z)) = 1 \<and>  name1(fst(z)) = name1(snd(z)) \<and> name2(fst(z)) \<in> domain(name2(snd(z))))}"
  unfolding def_frecrel frecR_def
  by (intro equalityI subsetI CollectI; elim CollectE; auto)


end
