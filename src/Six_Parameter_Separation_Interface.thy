theory Six_Parameter_Separation_Interface 
  imports Interface
begin

(* Six-parameter separation auxiliary results *)

lemma uniq_dec_6p: "<A',B',C',D',E',F'> \<in> M \<Longrightarrow> 
             \<forall>A\<in>M. \<forall>B\<in>M. \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. \<forall>F\<in>M. <A',B',C',D',E',F'> = <A,B,C,D,E,F> \<longrightarrow> 
                  P(x,A,B,C,D,E,F)
                \<longleftrightarrow>
                  P(x,A',B',C',D',E',F')"
  by simp
  
lemma (in forcing_data) tupling_sep_6p_aux :
              "(\<forall>A1\<in>M. \<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
                \<langle>A5, A6\<rangle> \<in> M \<and> \<langle>A4, A5, A6\<rangle> \<in> M \<and> \<langle>A3, A4, A5, A6\<rangle> \<in> M \<and> \<langle>A2, A3, A4, A5, A6\<rangle> \<in> M \<and> 
                v = \<langle>A1, A2, A3, A4, A5, A6\<rangle> \<longrightarrow>
                Q(x, A1, A2, A3, A4, A5, A6))
               \<longleftrightarrow>
               (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. \<forall>A6\<in>M.
                v = \<langle>A1, A2, A3, A4, A5, A6\<rangle> \<longrightarrow>
                Q(x, A1, A2, A3, A4, A5, A6))" for x v
 by (auto simp add:tuples_in_M)

lemma (in forcing_data) tupling_sep_6p : 
"(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. \<forall>A6\<in>M.
                  v = \<langle>A1, \<langle>A2, \<langle>A3, \<langle>A4, \<langle>A5, A6\<rangle>\<rangle>\<rangle>\<rangle>\<rangle> \<longrightarrow> Q(x,A1,A2,A3,A4,A5,A6))))
    \<longleftrightarrow>
 (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. \<forall>A6\<in>M. separation(##M,\<lambda>x. Q(x,A1,A2,A3,A4,A5,A6)))"
proof (simp add: separation_def, intro ballI iffI)
  fix A B C D E F z
  assume
        Eq1:  "\<forall>v\<in>M. \<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and> (\<forall>A\<in>M. \<forall>B\<in>M.  \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. \<forall>F\<in>M. v = \<langle>A, B,C,D,E,F\<rangle> 
                   \<longrightarrow> Q(x, A, B, C, D, E, F))"
     and
        Eq2:  "A\<in>M" "B\<in>M" "C\<in>M" "D\<in>M" "E\<in>M" "F\<in>M" "z\<in>M"  (* no puedo poner la conjunción *)
  then have 
        Eq3:  "<A,B,C,D,E,F>\<in>M"
    by (simp del:setclass_iff add:setclass_iff[symmetric])
  with Eq1 have 
              "\<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and> (\<forall>A'\<in>M. \<forall>B'\<in>M.  \<forall>C'\<in>M. \<forall>D'\<in>M. \<forall>E'\<in>M.  \<forall>F'\<in>M. <A,B,C,D,E,F> = \<langle>A',B',C',D',E',F'\<rangle> 
                   \<longrightarrow> Q(x, A', B', C', D', E',F'))"
    by (rule bspec)
  with Eq3 and Eq2 show
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and>  Q(x,A,B,C,D,E,F)"
    by simp
next
  fix v z
  assume
       asms:  "v\<in>M"   "z\<in>M"
              "\<forall>A\<in>M. \<forall>B\<in>M. \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. \<forall>F\<in>M. \<forall>z\<in>M. \<exists>y\<in>M. 
                  \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> Q(x, A,B,C,D,E,F)"
  consider (a) "\<exists>A\<in>M. \<exists>B\<in>M. \<exists>C\<in>M. \<exists>D\<in>M. \<exists>E\<in>M. \<exists>F\<in>M. v = \<langle>A,B,C,D,E,F\<rangle>" | 
           (b) "\<forall>A\<in>M. \<forall>B\<in>M. \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. \<forall>F\<in>M. v \<noteq> \<langle>A,B,C,D,E,F\<rangle>" by blast
  then show               
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> 
                    (\<forall>A\<in>M. \<forall>B\<in>M. \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. \<forall>F\<in>M. v = \<langle>A,B,C,D,E,F\<rangle> \<longrightarrow> Q(x,A,B,C,D,E,F))"
  proof cases
    case a
    then obtain A B C D E F where 
        Eq4:  "A\<in>M" "B\<in>M" "C\<in>M" "D\<in>M" "E\<in>M" "F\<in>M" "v = \<langle>A,B,C,D,E,F\<rangle>"
      by auto
    then have
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> Q(x,A,B,C,D,E,F)"
      using asms by simp
    then show ?thesis using Eq4 by simp
  next
    case b
    then have
              "\<forall>x\<in>M. x \<in> z \<longleftrightarrow> x \<in> z \<and> 
                (\<forall>A\<in>M. \<forall>B\<in>M.  \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. \<forall>F\<in>M. v = \<langle>A,B,C,D,E,F\<rangle> \<longrightarrow> Q(x,A,B,C,D,E,F))"
      by simp
    then show ?thesis using b and asms by auto
  qed
qed

   
lemma (in forcing_data) tupling_sep_6p_rel : 
"(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>A1\<in>M. \<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. 
                    \<forall>B0\<in>M. \<forall>B1\<in>M. \<forall>B2\<in>M. \<forall>B3\<in>M.   
                    pair(##M,A5,A6,B0) & 
                    pair(##M,A4,B0,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> Q(x,A1,A2,A3,A4,A5,A6))))
    \<longleftrightarrow>
 (\<forall>A1\<in>M. \<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. separation(##M,\<lambda>x. Q(x,A1,A2,A3,A4,A5,A6)))"
proof (simp)
  have
      "(\<forall>A1\<in>M. \<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
         \<langle>A5, A6\<rangle> \<in> M \<and> \<langle>A4, A5, A6\<rangle> \<in> M \<and> \<langle>A3, A4, A5, A6\<rangle> \<in> M \<and> \<langle>A2, A3, A4, A5, A6\<rangle> \<in> M \<and> v = \<langle>A1, A2, A3, A4, A5, A6\<rangle> \<longrightarrow>
        Q(x, A1, A2, A3, A4, A5, A6))
      \<longleftrightarrow>
      (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. \<forall>A6\<in>M.
        v = \<langle>A1, A2, A3, A4, A5, A6\<rangle> \<longrightarrow>
        Q(x, A1, A2, A3, A4, A5, A6))" for x v
    by (rule tupling_sep_6p_aux)
  then have
      "(\<forall>v\<in>M. separation
             (##M,
              \<lambda>x. \<forall>A1\<in>M. \<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
         \<langle>A5, A6\<rangle> \<in> M \<and> \<langle>A4, A5, A6\<rangle> \<in> M \<and> \<langle>A3, A4, A5, A6\<rangle> \<in> M \<and> \<langle>A2, A3, A4, A5, A6\<rangle> \<in> M \<and> v = \<langle>A1, A2, A3, A4, A5, A6\<rangle> \<longrightarrow>
        Q(x, A1, A2, A3, A4, A5, A6)))
      \<longleftrightarrow>
      (\<forall>v\<in>M. separation
             (##M,
              \<lambda>x. \<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. \<forall>A6\<in>M. 
        v = \<langle>A1, A2, A3, A4, A5, A6\<rangle> \<longrightarrow>
        Q(x, A1, A2, A3, A4, A5, A6)))"
    by simp
  also have
     "...   \<longleftrightarrow>
 (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. \<forall>A6\<in>M. separation(##M,\<lambda>x. Q(x,A1,A2,A3,A4,A5,A6)))"
    using tupling_sep_6p by simp
  finally  show
    "(\<forall>v\<in>M. separation
             (##M,
              \<lambda>x. \<forall>A1\<in>M. \<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
\<langle>A5, A6\<rangle> \<in> M \<and> \<langle>A4, A5, A6\<rangle> \<in> M \<and> \<langle>A3, A4, A5, A6\<rangle> \<in> M \<and> \<langle>A2, A3, A4, A5, A6\<rangle> \<in> M \<and> v = \<langle>A1, A2, A3, A4, A5, A6\<rangle> \<longrightarrow>
Q(x, A1, A2, A3, A4, A5, A6))) \<longleftrightarrow>
    (\<forall>A1\<in>M. \<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. separation(##M, \<lambda>x. Q(x, A1, A2, A3, A4, A5, A6)))"
    by auto
qed

lemma (in forcing_data) tupling_sep_6p_rel2 : 
"(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>B3\<in>M. \<forall>B2\<in>M. \<forall>B1\<in>M. \<forall>B0\<in>M.
                    \<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. \<forall>A1\<in>M.  
                    pair(##M,A5,A6,B0) & 
                    pair(##M,A4,B0,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> Q(x,A1,A2,A3,A4,A5,A6))))
    \<longleftrightarrow>
 (\<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. \<forall>A1\<in>M. separation(##M,\<lambda>x. Q(x,A1,A2,A3,A4,A5,A6)))"
proof -
  have
        "(\<forall>B3\<in>M. \<forall>B2\<in>M. \<forall>B1\<in>M. \<forall>B0\<in>M.
                    \<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. \<forall>A1\<in>M.  
                    pair(##M,A5,A6,B0) & 
                    pair(##M,A4,B0,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> Q(x,A1,A2,A3,A4,A5,A6))
          \<longleftrightarrow>
         (\<forall>A1\<in>M. \<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. 
                 \<forall>B0\<in>M. \<forall>B1\<in>M. \<forall>B2\<in>M. \<forall>B3\<in>M.   
                    pair(##M,A5,A6,B0) & 
                    pair(##M,A4,B0,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> Q(x,A1,A2,A3,A4,A5,A6))" 
        (is "?P\<longleftrightarrow>?Q") for x v 
        (* This can't be proved right away by the automatic tools.
           At least one instance is necessary*)
    by (intro iffI ballI, drule_tac x="B3" in bspec, auto)
  then have
        "separation(##M,\<lambda>x. ?P(x,v)) \<longleftrightarrow> separation(##M,\<lambda>x. ?Q(x,v))" for v
    by auto
  then have
        "(\<forall>v\<in>M. separation(##M,\<lambda>x. ?P(x,v)))
         \<longleftrightarrow> 
         (\<forall>v\<in>M. separation(##M,\<lambda>x. ?Q(x,v)))"
    by blast
  also have
    " ... \<longleftrightarrow> (\<forall>A1\<in>M. \<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. separation(##M,\<lambda>x. Q(x,A1,A2,A3,A4,A5,A6)))"
    using tupling_sep_6p_rel by simp
  finally show ?thesis by auto
qed

definition
  tupling_fm_6p :: "i \<Rightarrow> i" where
  "tupling_fm_6p(\<phi>) = 
      Forall(Forall(Forall(Forall(Forall(Forall(Forall(Forall(Forall(Forall(
        Implies(And(pair_fm(4,5,6),
                And(pair_fm(3,6,7),
                And(pair_fm(2,7,8),
                And(pair_fm(1,8,9),
                    pair_fm(0,9,11))))),\<phi>)))))))))))"

(* "(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>A1\<in>M. \<forall>A6\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. 
                    \<forall>B0\<in>M. \<forall>B1\<in>M. \<forall>B2\<in>M. \<forall>B3\<in>M.   
                    pair(##M,A5,A6,B0) & 
                    pair(##M,A4,B0,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> Q(x,A1,A2,A3,A4,A5,A6))))
*)
  
lemma [TC] :  "\<lbrakk> \<phi> \<in> formula \<rbrakk> \<Longrightarrow> tupling_fm_6p(\<phi>) \<in> formula"
  by (simp add: tupling_fm_6p_def)

lemma arity_tup6p :
  "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>) = 10 \<rbrakk> \<Longrightarrow> arity(tupling_fm_6p(\<phi>)) = 2"
  by (simp add: tupling_fm_6p_def arity_incr_bv_lemma pair_fm_def 
                upair_fm_def Un_commute nat_union_abs1)
