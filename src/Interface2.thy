theory Interface2 imports Forcing_data Relative_no_repl Internalize_no_repl begin

lemma Transset_intf :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)

    
lemma empty_intf :
  "infinity_ax(M) \<Longrightarrow>
  (\<exists>z[M]. empty(M,z))"
  by (auto simp add: empty_def infinity_ax_def)

lemma zero_in_M:  "\<lbrakk> infinity_ax(##M) ; Transset(M) \<rbrakk> \<Longrightarrow> 0 \<in> M"
proof -
  assume inf: "infinity_ax(##M)" and
         trans: "Transset(M)"
  from inf have
        "(\<exists>z[##M]. empty(##M,z))"
    by (rule empty_intf)
  then obtain z where
        zm: "empty(##M,z)"  "z\<in>M"
    by auto
  with trans have "z=0"
    by (simp  add: empty_def, blast intro: Transset_intf )
  with zm show ?thesis 
      by simp
qed

lemma nat_union_abs : 
  "\<lbrakk> Ord(i) ; Ord(j) ; i \<le> j \<rbrakk> \<Longrightarrow> i \<union> j = j"
  by (rule Un_absorb1,erule le_imp_subset)
  
(* Interface with M_trivial *)
lemma (in forcing_data) mtriv :  
  "M_trivial_no_repl(##M)"
  apply (insert trans_M upair_ax Union_ax power_ax infinity_ax)
  apply (rule M_trivial_no_repl.intro)
  apply (simp_all add: zero_in_M)
  apply (rule Transset_intf,simp+)
done

  
(* tupling *)
  
lemma uniq_dec_2p: "<C,D> \<in> M \<Longrightarrow> 
             \<forall>A\<in>M. \<forall>B\<in>M. <C,D> = \<langle>A, B\<rangle> \<longrightarrow> P(x, A, B)
            \<longleftrightarrow>
              P(x, C, D)"
  by simp
    
lemma (in forcing_data) tupling_sep_2p :
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>A\<in>M. \<forall>B\<in>M. pair(##M,A,B,v) \<longrightarrow> Q(x,A,B))))
    \<longleftrightarrow>
     (\<forall>A\<in>M. \<forall>B\<in>M. separation(##M,\<lambda>x. Q(x,A,B)))"
  apply (simp add: separation_def)
proof (intro ballI iffI)
  fix A B z
  assume
        Eq1:  "\<forall>v\<in>M. \<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and> (\<forall>A\<in>M. \<forall>B\<in>M. v = \<langle>A, B\<rangle> \<longrightarrow> Q(x, A, B))"
     and
        Eq2:  "A\<in>M" "B\<in>M" "z\<in>M"  (* no puedo poner la conjunción *)
  then have 
        Eq3:  "<A,B>\<in>M"
    by (simp del:setclass_iff add:setclass_iff[symmetric])
  with Eq1 have 
              "\<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and> (\<forall>C\<in>M. \<forall>D\<in>M. <A,B> = \<langle>C, D\<rangle> \<longrightarrow> Q(x, C, D))"
    by (rule bspec)
  with uniq_dec_2p and Eq3 and Eq2 show
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and>  Q(x, A, B)"
    by simp
next
  fix v z
  assume
       asms:  "v\<in>M"   "z\<in>M"
              "\<forall>A\<in>M. \<forall>B\<in>M. \<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> Q(x, A, B)"
  consider (a) "\<exists>A\<in>M. \<exists>B\<in>M. v = \<langle>A, B\<rangle>" | (b) "\<forall>A\<in>M. \<forall>B\<in>M. v \<noteq> \<langle>A, B\<rangle>" by auto
  then show                (* "then" is important here *)
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> 
                    (\<forall>A\<in>M. \<forall>B\<in>M. v = \<langle>A, B\<rangle> \<longrightarrow> Q(x, A, B))"
  proof cases
    case a
    then obtain A B where  (* also here *)
        Eq4:  "A\<in>M" "B\<in>M" "v = \<langle>A, B\<rangle>"
      by auto
    then have
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> Q(x, A, B)"
      using asms by simp
    then show ?thesis using Eq4 and uniq_dec_2p by simp
  next
    case b
    then have
              "\<forall>x\<in>M. x \<in> z \<longleftrightarrow> x \<in> z \<and> (\<forall>A\<in>M. \<forall>B\<in>M. v = \<langle>A, B\<rangle> \<longrightarrow> Q(x, A, B))"
      by simp
    then show ?thesis using b and asms by auto
  qed
qed
  
lemma uniq_dec_5p: "<A',B',C',D',E'> \<in> M \<Longrightarrow> 
             \<forall>A\<in>M. \<forall>B\<in>M. \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. <A',B',C',D',E'> = <A,B,C,D,E> \<longrightarrow> 
                  P(x,A,B,C,D,E)
                \<longleftrightarrow>
                  P(x,A',B',C',D',E')"
  by simp

lemma (in forcing_data) tupling_sep_5p : 
"(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. 
                  v = \<langle>A1, \<langle>A2, \<langle>A3, \<langle>A4, A5\<rangle>\<rangle>\<rangle>\<rangle> \<longrightarrow> Q(x,A1,A2,A3,A4,A5))))
    \<longleftrightarrow>
 (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. separation(##M,\<lambda>x. Q(x,A1,A2,A3,A4,A5)))"
  apply (simp add: separation_def)
proof (intro ballI iffI)
  fix A B C D E z
  assume
        Eq1:  "\<forall>v\<in>M. \<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and> (\<forall>A\<in>M. \<forall>B\<in>M.  \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. v = \<langle>A, B,C,D,E\<rangle> 
                   \<longrightarrow> Q(x, A, B, C, D, E))"
     and
        Eq2:  "A\<in>M" "B\<in>M" "C\<in>M" "D\<in>M" "E\<in>M" "z\<in>M"  (* no puedo poner la conjunción *)
  then have 
        Eq3:  "<A,B,C,D,E>\<in>M"
    by (simp del:setclass_iff add:setclass_iff[symmetric])
  with Eq1 have 
              "\<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and> (\<forall>A'\<in>M. \<forall>B'\<in>M.  \<forall>C'\<in>M. \<forall>D'\<in>M. \<forall>E'\<in>M. <A,B,C,D,E> = \<langle>A',B',C',D',E'\<rangle> 
                   \<longrightarrow> Q(x, A', B', C', D', E'))"
    by (rule bspec)
  with uniq_dec_5p and Eq3 and Eq2 show
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and>  Q(x,A,B,C,D,E)"
    by simp
next
  fix v z
  assume
       asms:  "v\<in>M"   "z\<in>M"
              "\<forall>A\<in>M. \<forall>B\<in>M. \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. \<forall>z\<in>M. \<exists>y\<in>M. 
                  \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> Q(x, A,B,C,D,E)"
  consider (a) "\<exists>A\<in>M. \<exists>B\<in>M. \<exists>C\<in>M. \<exists>D\<in>M. \<exists>E\<in>M. v = \<langle>A,B,C,D,E\<rangle>" | 
           (b) "\<forall>A\<in>M. \<forall>B\<in>M. \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. v \<noteq> \<langle>A,B,C,D,E\<rangle>" by blast
  then show               
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> 
                    (\<forall>A\<in>M. \<forall>B\<in>M. \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. v = \<langle>A,B,C,D,E\<rangle> \<longrightarrow> Q(x,A,B,C,D,E))"
  proof cases
    case a
    then obtain A B C D E where 
        Eq4:  "A\<in>M" "B\<in>M" "C\<in>M" "D\<in>M" "E\<in>M" "v = \<langle>A,B,C,D,E\<rangle>"
      by auto
    then have
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> Q(x,A,B,C,D,E)"
      using asms by simp
    then show ?thesis using Eq4 by simp
  next
    case b
    then have
              "\<forall>x\<in>M. x \<in> z \<longleftrightarrow> x \<in> z \<and> 
                (\<forall>A\<in>M. \<forall>B\<in>M.  \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. v = \<langle>A,B,C,D,E\<rangle> \<longrightarrow> Q(x,A,B,C,D,E))"
      by simp
    then show ?thesis using b and asms by auto
  qed
qed

(* Internalized tupling *) 
definition 
  tupling_fm_2p :: "i \<Rightarrow> i" where
  "tupling_fm_2p(\<phi>) = Forall(Forall(Implies(pair_fm(1,0,3),\<phi>)))"
  
lemma [TC] :  "\<lbrakk> \<phi> \<in> formula \<rbrakk> \<Longrightarrow> tupling_fm_2p(\<phi>) \<in> formula"
  by (simp add: tupling_fm_2p_def)
    
lemma arity_tup2p :  
  "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>) = 3 \<rbrakk> \<Longrightarrow> arity(tupling_fm_2p(\<phi>)) = 2"
  by (simp add: tupling_fm_2p_def arity_incr_bv_lemma pair_fm_def 
                upair_fm_def Un_commute nat_union_abs)

  
  
(* Instances of separation of M_basic *)

(* Inter_separation: "M(A) ==> separation(M, \<lambda>x. \<forall>y[M]. y\<in>A \<longrightarrow> x\<in>y)" *)
              
lemma arity_inter_fm :
  "arity(Forall(Implies(Member(0,2),Member(1,0)))) = 2"
  by (simp add: Un_commute nat_union_abs)
  
lemma (in forcing_data) inter_sep_intf :
  assumes
      1: "A\<in>M"
  shows
      "separation(##M,\<lambda>x . \<forall>y\<in>M . y\<in>A \<longrightarrow> x\<in>y)"
proof -
    have 
        "\<forall>a\<in>M. separation(##M, \<lambda>x. sats(M, Forall(Implies(Member(0,2),Member(1,0))), [x, a]))"
    by (rule separation_ax,simp,rule disjI2,rule arity_inter_fm)
  then have 
        "separation(##M, \<lambda>x. sats(M, Forall(Implies(Member(0,2),Member(1,0))), [x, A]))"
    by (simp add: 1)
  then show ?thesis by (simp add: separation_def 1)
qed

  
(* Diff_separation: "M(B) ==> separation(M, \<lambda>x. x \<notin> B)" *)
lemma arity_diff_fm: 
  "arity(Neg(Member(0,1))) = 2"
by (simp add: nat_union_abs)
    
lemma (in forcing_data) diff_sep_intf :
  assumes
      1: "B\<in>M"
  shows
      "separation(##M,\<lambda>x . x\<notin>B)"
proof -
  have 
        "\<forall>a\<in>M. separation(##M, \<lambda>x. sats(M, Neg(Member(0,1)), [x, a]))"
    by (rule separation_ax,simp,rule disjI2,rule arity_diff_fm)
  then have 
        "separation(##M, \<lambda>x. sats(M, Neg(Member(0,1)), [x, B]))"
    by (simp add: 1)
  then show ?thesis by (simp add: separation_def 1)
qed
  
  
(* cartprod_separation: 
   "[| M(A); M(B) |] ==> separation(M, \<lambda>z. \<exists>x[M]. x\<in>A & (\<exists>y[M]. y\<in>B & pair(M,x,y,z)))" *)
definition
  cartprod_sep_fm :: "i" where
  "cartprod_sep_fm == 
              Exists(And(Member(0,2),
                     Exists(And(Member(0,2),pair_fm(1,0,4)))))"

lemma cartprof_sep_fm_type [TC] : 
  "cartprod_sep_fm \<in> formula"
  by (simp add: cartprod_sep_fm_def)
    
lemma arity_cartprod_fm [simp] : "arity(cartprod_sep_fm) = 3" 
  by (simp add: cartprod_sep_fm_def pair_fm_def upair_fm_def 
                Un_commute nat_union_abs)
              
lemma (in forcing_data) cartprod_sep_intf :
  assumes
        1:  "A\<in>M"
            and
        2:  "B\<in>M"
   shows
            "separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A \<and> (\<exists>y\<in>M. y\<in>B \<and> pair(##M,x,y,z)))"
proof -
  have
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. sats(M,tupling_fm_2p(cartprod_sep_fm),[x,v])))"
  by (rule separation_ax,simp,rule disjI2,rule arity_tup2p,simp_all)
  then have
    "(\<forall>v\<in>M. separation(##M, \<lambda>x. \<forall>A\<in>M. \<forall>B\<in>M. pair(##M, A, B, v) \<longrightarrow> 
                      (\<exists>xa\<in>M. xa \<in> A \<and> (\<exists>y\<in>M. y \<in> B \<and> pair(##M, xa, y, x)))))"
  by (simp add: separation_def tupling_fm_2p_def cartprod_sep_fm_def del: pair_abs)
  then have 
    "(\<forall>A\<in>M. \<forall>B\<in>M. separation(##M, \<lambda>z. \<exists>x\<in>M. x \<in> A \<and> (\<exists>y\<in>M. y \<in> B \<and> pair(##M, x, y, z))))"
  by (rule tupling_sep_2p [THEN iffD1])
  then show ?thesis by (simp add: 1 2)
qed

(*image_separation: 
   "[| M(A); M(r) |] ==> separation(M, \<lambda>y. \<exists>p[M]. p\<in>r & (\<exists>x[M]. x\<in>A & pair(M,x,y,p)))" *)
definition
  image_sep_fm :: "i" where
  "image_sep_fm == 
    Exists(And(Member(0,1),
          Exists(And(Member(0,3),pair_fm(0,4,1)))))"
  
lemma image_sep_fm_type [TC] : 
  "image_sep_fm \<in> formula"
  by (simp add: image_sep_fm_def)

    
lemma [simp] : "arity(image_sep_fm) = 3" 
  by (simp add: image_sep_fm_def pair_fm_def upair_fm_def 
                Un_commute nat_union_abs)
  
lemma (in forcing_data) image_sep_intf :
  assumes
        1:  "A\<in>M"
            and
        2:  "r\<in>M"
   shows
            "separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M. x\<in>A & pair(##M,x,y,p)))"
proof -
  have
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. sats(M,tupling_fm_2p(image_sep_fm),[x,v])))"
  by (rule separation_ax,simp,rule disjI2,rule arity_tup2p,simp_all)
  then have
    "(\<forall>v\<in>M. separation(##M, \<lambda>x. \<forall>A\<in>M. \<forall>B\<in>M. pair(##M, A, B, v) \<longrightarrow> 
          (\<exists>p\<in>M. p \<in> B \<and> (\<exists>xa\<in>M. xa \<in> A \<and> pair(##M, xa, x, p)))))"
  by (simp add: separation_def tupling_fm_2p_def image_sep_fm_def del: pair_abs)
  then have 
    "(\<forall>A\<in>M. \<forall>r\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M. x\<in>A & pair(##M,x,y,p))))"
  by (rule tupling_sep_2p [THEN iffD1])
  then show ?thesis by (simp add: 1 2)
qed
   
(* converse_separation:
 "M(r) ==> separation(M,\<lambda>z. \<exists>p[M]. p\<in>r & (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,p) & pair(M,y,x,z)))" *)
definition
  converse_sep_fm :: "i" where
  "converse_sep_fm == 
    Exists(And(Member(0,2),
      Exists(Exists(And(pair_fm(1,0,2),pair_fm(0,1,3))))))"
  
lemma converse_sep_fm_type [TC] : "converse_sep_fm \<in> formula"
  by (simp add: converse_sep_fm_def)

lemma [simp] : "arity(converse_sep_fm) = 2"
  by (simp add: converse_sep_fm_def pair_fm_def upair_fm_def 
                Un_commute nat_union_abs)
       
lemma (in forcing_data) converse_sep_intf :
  assumes
      1: "R\<in>M"
  shows
         "separation(##M,\<lambda>z. \<exists>p\<in>M. p\<in>R & (\<exists>x\<in>M.\<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,z)))"
proof -
  have 
        "\<forall>r\<in>M. separation(##M, \<lambda>x. sats(M,converse_sep_fm, [x, r]))"
    by (rule separation_ax,simp,rule disjI2,simp)
  then have 
        "separation(##M, \<lambda>x. sats(M,converse_sep_fm, [x, R]))"
    by (simp add: 1)
  then show ?thesis by (simp add: separation_def converse_sep_fm_def 1 del: pair_abs)
qed
              
(* restrict_separation:
     "M(A) ==> separation(M, \<lambda>z. \<exists>x[M]. x\<in>A & (\<exists>y[M]. pair(M,x,y,z)))" *)
definition
  restrict_sep_fm :: "i" where
  "restrict_sep_fm == Exists(And(Member(0,2),Exists(pair_fm(1,0,2))))"

lemma restrict_sep_fm_type [TC] : "restrict_sep_fm \<in> formula"
  by (simp add: restrict_sep_fm_def)
    
lemma [simp] : "arity(restrict_sep_fm) = 2"
  by (simp add: restrict_sep_fm_def pair_fm_def upair_fm_def 
                Un_commute nat_union_abs)

lemma (in forcing_data) restrict_sep_intf :
  assumes
      1: "A\<in>M"
  shows
         "separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A & (\<exists>y\<in>M. pair(##M,x,y,z)))"
proof -
  have 
        "\<forall>a\<in>M. separation(##M, \<lambda>x. sats(M,restrict_sep_fm, [x, a]))"
    by (rule separation_ax,simp,rule disjI2,simp)
  then have 
        "separation(##M, \<lambda>x. sats(M,restrict_sep_fm, [x, A]))"
    by (simp add: 1)
  then show ?thesis by (simp add: separation_def restrict_sep_fm_def 1 del: pair_abs)
qed
  
(* comp_separation:
    "[| M(r); M(s) |]
      ==> separation(M, \<lambda>xz. \<exists>x[M]. \<exists>y[M]. \<exists>z[M]. \<exists>xy[M]. \<exists>yz[M].
                  pair(M,x,z,xz) & pair(M,x,y,xy) & pair(M,y,z,yz) & xy\<in>s & yz\<in>r)"*)
definition 
  comp_sep_fm :: "i" where
  "comp_sep_fm ==
    Exists(Exists(Exists(Exists(Exists
      (And(pair_fm(4,2,7),And(pair_fm(4,3,1),
          And(pair_fm(3,2,0),And(Member(1,5),Member(0,6))))))))))"

lemma comp_sep_fm_type [TC] : "comp_sep_fm \<in> formula"
  by (simp add: comp_sep_fm_def)

lemma [simp] : "arity(comp_sep_fm) = 3"
  by (simp add: comp_sep_fm_def pair_fm_def upair_fm_def Un_commute nat_union_abs)

lemma (in forcing_data) comp_sep_intf :
  assumes
        1:  "R\<in>M"
            and
        2:  "S\<in>M"
   shows
            "separation(##M,\<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
              pair(##M,x,z,xz) & pair(##M,x,y,xy) & pair(##M,y,z,yz) & xy\<in>S & yz\<in>R)"
proof -
  have
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. sats(M,tupling_fm_2p(comp_sep_fm),[x,v])))"
  by (rule separation_ax,simp,rule disjI2,rule arity_tup2p,simp_all)
  then have
    "(\<forall>v\<in>M. separation
             (##M, \<lambda>x. \<forall>A\<in>M. \<forall>B\<in>M. pair(##M, A, B, v) \<longrightarrow>
                                    (\<exists>xa\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M. pair(##M, xa, z, x) \<and>
              pair(##M, xa, y, xy) \<and> pair(##M, y, z, yz) \<and> xy \<in> B \<and> yz \<in> A)))"
  by (simp add: separation_def tupling_fm_2p_def comp_sep_fm_def del: pair_abs)
  then have 
    "(\<forall>r\<in>M. \<forall>s\<in>M. separation
         (##M, \<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M. pair(##M, x, z, xz) \<and>
                                    pair(##M, x, y, xy) \<and> pair(##M, y, z, yz) \<and> xy \<in> s \<and> yz \<in> r))"
  by (rule tupling_sep_2p [THEN iffD1])
  then show ?thesis by (simp add: 1 2)
qed
  
end