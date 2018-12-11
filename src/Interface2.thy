theory Interface2 imports Forcing_data Relative_no_repl Internalize_no_repl Renaming begin

lemma Transset_intf :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)

lemma TranssetI :
  "(\<And>y x. y\<in>x \<Longrightarrow> x\<in>M \<Longrightarrow> y\<in>M) \<Longrightarrow> Transset(M)"
  by (auto simp add: Transset_def)
    
lemma empty_intf :
  "infinity_ax(M) \<Longrightarrow>
  (\<exists>z[M]. empty(M,z))"
  by (auto simp add: empty_def infinity_ax_def)

lemma (in forcing_data) zero_in_M:  "0 \<in> M"
proof -
  from infinity_ax have
        "(\<exists>z[##M]. empty(##M,z))"
    by (rule empty_intf)
  then obtain z where
        zm: "empty(##M,z)"  "z\<in>M"
    by auto
  with trans_M have "z=0"
    by (simp  add: empty_def, blast intro: Transset_intf )
  with zm show ?thesis 
      by simp
qed

lemma nat_union_abs1 : 
  "\<lbrakk> Ord(i) ; Ord(j) ; i \<le> j \<rbrakk> \<Longrightarrow> i \<union> j = j"
  by (rule Un_absorb1,erule le_imp_subset)

lemma nat_union_abs2 : 
  "\<lbrakk> Ord(i) ; Ord(j) ; i \<le> j \<rbrakk> \<Longrightarrow> j \<union> i = j"
  by (rule Un_absorb2,erule le_imp_subset)
    
(* Interface with M_trivial *)
    
lemma (in forcing_data) mtriv :  
  "M_trivial_no_repl(##M)"
  apply (insert trans_M upair_ax Union_ax)
  apply (rule M_trivial_no_repl.intro)
  apply (simp_all add: zero_in_M)
  apply (rule Transset_intf,simp+)
done

sublocale forcing_data \<subseteq> M_trivial_no_repl "##M"
  by (rule mtriv)
  
(* tupling *)
abbreviation
 dec10  :: i   ("10") where "10 == succ(9)"
    
abbreviation
 dec11  :: i   ("11") where "11 == succ(10)"

abbreviation
 dec12  :: i   ("12") where "12 == succ(11)"

abbreviation
 dec13  :: i   ("13") where "13 == succ(12)"

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
  

lemma (in forcing_data) tuples_in_M: "A\<in>M \<Longrightarrow> B\<in>M \<Longrightarrow> <A,B>\<in>M" 
   by (simp del:setclass_iff add:setclass_iff[symmetric])

(* Five-parameter separation auxiliary results *)
     
lemma uniq_dec_5p: "<A',B',C',D',E'> \<in> M \<Longrightarrow> 
             \<forall>A\<in>M. \<forall>B\<in>M. \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. <A',B',C',D',E'> = <A,B,C,D,E> \<longrightarrow> 
                  P(x,A,B,C,D,E)
                \<longleftrightarrow>
                  P(x,A',B',C',D',E')"
  by simp

lemma (in forcing_data) tupling_sep_5p_aux :
              "(\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
                \<langle>A4, A5\<rangle> \<in> M \<and> \<langle>A3, A4, A5\<rangle> \<in> M \<and> \<langle>A2, A3, A4, A5\<rangle> \<in> M \<and> 
                v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
                Q(x, A1, A2, A3, A4, A5))
               \<longleftrightarrow>
               (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M.
                v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
                Q(x, A1, A2, A3, A4, A5))" for x v
 by (auto simp add:tuples_in_M)


lemma (in forcing_data) tupling_sep_5p : 
"(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. 
                  v = \<langle>A1, \<langle>A2, \<langle>A3, \<langle>A4, A5\<rangle>\<rangle>\<rangle>\<rangle> \<longrightarrow> Q(x,A1,A2,A3,A4,A5))))
    \<longleftrightarrow>
 (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. separation(##M,\<lambda>x. Q(x,A1,A2,A3,A4,A5)))"
proof (simp add: separation_def, intro ballI iffI)
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

   
lemma (in forcing_data) tupling_sep_5p_rel : 
"(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. 
                    \<forall>B1\<in>M. \<forall>B2\<in>M. \<forall>B3\<in>M.   
                    pair(##M,A4,A5,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> Q(x,A1,A2,A3,A4,A5))))
    \<longleftrightarrow>
 (\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. separation(##M,\<lambda>x. Q(x,A1,A2,A3,A4,A5)))"
proof (simp)
  have
      "(\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
        \<langle>A4, A5\<rangle> \<in> M \<and> \<langle>A3, A4, A5\<rangle> \<in> M \<and> \<langle>A2, A3, A4, A5\<rangle> \<in> M \<and> v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
        Q(x, A1, A2, A3, A4, A5))
      \<longleftrightarrow>
      (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M.
        v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
        Q(x, A1, A2, A3, A4, A5))" for x v
    by (rule tupling_sep_5p_aux)
  then have
      "(\<forall>v\<in>M. separation
             (##M,
              \<lambda>x. \<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
        \<langle>A4, A5\<rangle> \<in> M \<and> \<langle>A3, A4, A5\<rangle> \<in> M \<and> \<langle>A2, A3, A4, A5\<rangle> \<in> M \<and> v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
        Q(x, A1, A2, A3, A4, A5)))
      \<longleftrightarrow>
      (\<forall>v\<in>M. separation
             (##M,
              \<lambda>x. \<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M.
        v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
        Q(x, A1, A2, A3, A4, A5)))"
    by simp
  also have
     "...   \<longleftrightarrow>
 (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. separation(##M,\<lambda>x. Q(x,A1,A2,A3,A4,A5)))"
    using tupling_sep_5p by simp
  finally  show
    "(\<forall>v\<in>M. separation
             (##M,
              \<lambda>x. \<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
\<langle>A4, A5\<rangle> \<in> M \<and> \<langle>A3, A4, A5\<rangle> \<in> M \<and> \<langle>A2, A3, A4, A5\<rangle> \<in> M \<and> v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
Q(x, A1, A2, A3, A4, A5))) \<longleftrightarrow>
    (\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. separation(##M, \<lambda>x. Q(x, A1, A2, A3, A4, A5)))"
    by auto
qed

lemma (in forcing_data) tupling_sep_5p_rel2 : 
"(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>B3\<in>M. \<forall>B2\<in>M. \<forall>B1\<in>M. 
                    \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. \<forall>A1\<in>M.  
                    pair(##M,A4,A5,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> Q(x,A1,A2,A3,A4,A5))))
    \<longleftrightarrow>
 (\<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. \<forall>A1\<in>M. separation(##M,\<lambda>x. Q(x,A1,A2,A3,A4,A5)))"
proof -
  have
        "(\<forall>B3\<in>M. \<forall>B2\<in>M. \<forall>B1\<in>M. 
                    \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. \<forall>A1\<in>M.  
                    pair(##M,A4,A5,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> Q(x,A1,A2,A3,A4,A5))
          \<longleftrightarrow>
         (\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. 
                    \<forall>B1\<in>M. \<forall>B2\<in>M. \<forall>B3\<in>M.   
                    pair(##M,A4,A5,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> Q(x,A1,A2,A3,A4,A5))" 
        (is "?P\<longleftrightarrow>?Q") for x v 
    by auto
  then have
        "separation(##M,\<lambda>x. ?P(x,v)) \<longleftrightarrow> separation(##M,\<lambda>x. ?Q(x,v))" for v
    by auto
  then have
        "(\<forall>v\<in>M. separation(##M,\<lambda>x. ?P(x,v)))
         \<longleftrightarrow> 
         (\<forall>v\<in>M. separation(##M,\<lambda>x. ?Q(x,v)))"
    by blast
  also have
    " ... \<longleftrightarrow> (\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. separation(##M,\<lambda>x. Q(x,A1,A2,A3,A4,A5)))"
    using tupling_sep_5p_rel by simp
  finally show ?thesis by auto
qed

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

(* Internalized tupling *) 
definition 
  tupling_fm_2p :: "i \<Rightarrow> i" where
  "tupling_fm_2p(\<phi>) = Forall(Forall(Implies(pair_fm(1,0,3),\<phi>)))"
  
lemma [TC] :  "\<lbrakk> \<phi> \<in> formula \<rbrakk> \<Longrightarrow> tupling_fm_2p(\<phi>) \<in> formula"
  by (simp add: tupling_fm_2p_def)
    
lemma arity_tup2p :  
  "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>) = 3 \<rbrakk> \<Longrightarrow> arity(tupling_fm_2p(\<phi>)) = 2"
  by (simp add: tupling_fm_2p_def arity_incr_bv_lemma pair_fm_def 
                upair_fm_def Un_commute nat_union_abs1)

definition
  tupling_fm_5p :: "i \<Rightarrow> i" where
  "tupling_fm_5p(\<phi>) = 
      Forall(Forall(Forall(Forall(Forall(Forall(Forall(Forall(
        Implies(And(pair_fm(3,4,5),
                And(pair_fm(2,5,6),
                And(pair_fm(1,6,7),
                    pair_fm(0,7,9)))),\<phi>)))))))))"

  
lemma [TC] :  "\<lbrakk> \<phi> \<in> formula \<rbrakk> \<Longrightarrow> tupling_fm_5p(\<phi>) \<in> formula"
  by (simp add: tupling_fm_5p_def)

lemma arity_tup5p :
  "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>) = 9 \<rbrakk> \<Longrightarrow> arity(tupling_fm_5p(\<phi>)) = 2"
  by (simp add: tupling_fm_5p_def arity_incr_bv_lemma pair_fm_def 
                upair_fm_def Un_commute nat_union_abs1)

lemma leq_9:
  "n\<le>9 \<Longrightarrow> n=0 | n=1 | n=2 | n=3 | n=4 | n=5 | n=6| n=7 | n=8 | n=9"
  by (clarsimp simp add:not_lt_iff_le, auto simp add:lt_def)

lemma arity_tup5p_leq :
  "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>) \<le> 9 \<rbrakk> \<Longrightarrow> arity(tupling_fm_5p(\<phi>)) = 2"
  by (drule leq_9, elim disjE, simp_all add:tupling_fm_5p_def arity_incr_bv_lemma pair_fm_def 
                upair_fm_def Un_commute nat_union_abs1)

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

(* end tupling *)

(* Instances of separation of M_basic *)

(* Inter_separation: "M(A) ==> separation(M, \<lambda>x. \<forall>y[M]. y\<in>A \<longrightarrow> x\<in>y)" *)
              
lemma arity_inter_fm :
  "arity(Forall(Implies(Member(0,2),Member(1,0)))) = 2"
  by (simp add: Un_commute nat_union_abs1)
  
lemma (in forcing_data) inter_sep_intf :
  assumes
      "A\<in>M"
  shows
      "separation(##M,\<lambda>x . \<forall>y\<in>M . y\<in>A \<longrightarrow> x\<in>y)"
proof -
    from separation_ax arity_inter_fm have 
        "\<forall>a\<in>M. separation(##M, \<lambda>x. sats(M, Forall(Implies(Member(0,2),Member(1,0))), [x, a]))"
    by simp
  with \<open>A\<in>M\<close> have 
        "separation(##M, \<lambda>x. sats(M, Forall(Implies(Member(0,2),Member(1,0))), [x, A]))"
    by simp
  with \<open>A\<in>M\<close> show ?thesis unfolding separation_def by simp
qed

  
(* Diff_separation: "M(B) ==> separation(M, \<lambda>x. x \<notin> B)" *)
lemma arity_diff_fm: 
  "arity(Neg(Member(0,1))) = 2"
by (simp add: nat_union_abs1)
    
lemma (in forcing_data) diff_sep_intf :
  assumes
      "B\<in>M"
  shows
      "separation(##M,\<lambda>x . x\<notin>B)"
proof -
  from separation_ax arity_diff_fm have 
        "\<forall>a\<in>M. separation(##M, \<lambda>x. sats(M, Neg(Member(0,1)), [x, a]))"
    by simp
  with \<open>B\<in>M\<close> have 
        "separation(##M, \<lambda>x. sats(M, Neg(Member(0,1)), [x, B]))"
    by simp
  with \<open>B\<in>M\<close> show ?thesis unfolding separation_def by simp
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
                Un_commute nat_union_abs1)
              
lemma (in forcing_data) cartprod_sep_intf :
  assumes
            "A\<in>M"
            and
            "B\<in>M"
   shows
            "separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A \<and> (\<exists>y\<in>M. y\<in>B \<and> pair(##M,x,y,z)))"
proof -
  from separation_ax arity_tup2p have
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. sats(M,tupling_fm_2p(cartprod_sep_fm),[x,v])))"
  by simp
  then have
    "(\<forall>v\<in>M. separation(##M, \<lambda>x. \<forall>A\<in>M. \<forall>B\<in>M. pair(##M, A, B, v) \<longrightarrow> 
                      (\<exists>xa\<in>M. xa \<in> A \<and> (\<exists>y\<in>M. y \<in> B \<and> pair(##M, xa, y, x)))))"
  unfolding separation_def tupling_fm_2p_def cartprod_sep_fm_def by (simp del: pair_abs)
  with tupling_sep_2p have 
    "(\<forall>A\<in>M. \<forall>B\<in>M. separation(##M, \<lambda>z. \<exists>x\<in>M. x \<in> A \<and> (\<exists>y\<in>M. y \<in> B \<and> pair(##M, x, y, z))))"
  by simp
  with \<open>A\<in>M\<close> \<open>B\<in>M\<close> show ?thesis by simp
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
                Un_commute nat_union_abs1)
  
lemma (in forcing_data) image_sep_intf :
  assumes
            "A\<in>M"
            and
            "r\<in>M"
   shows
            "separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M. x\<in>A & pair(##M,x,y,p)))"
proof -
  from separation_ax arity_tup2p have
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. sats(M,tupling_fm_2p(image_sep_fm),[x,v])))"
  by simp
  then have
    "(\<forall>v\<in>M. separation(##M, \<lambda>x. \<forall>A\<in>M. \<forall>B\<in>M. pair(##M, A, B, v) \<longrightarrow> 
          (\<exists>p\<in>M. p \<in> B \<and> (\<exists>xa\<in>M. xa \<in> A \<and> pair(##M, xa, x, p)))))"
  unfolding separation_def tupling_fm_2p_def image_sep_fm_def by (simp del: pair_abs)
  with tupling_sep_2p have 
    "(\<forall>A\<in>M. \<forall>r\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M. x\<in>A & pair(##M,x,y,p))))"
  by simp
  with \<open>A\<in>M\<close> \<open>r\<in>M\<close> show ?thesis by simp
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
                Un_commute nat_union_abs1)
       
lemma (in forcing_data) converse_sep_intf :
  assumes
         "R\<in>M"
  shows
         "separation(##M,\<lambda>z. \<exists>p\<in>M. p\<in>R & (\<exists>x\<in>M.\<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,z)))"
proof -
  from separation_ax have 
        "\<forall>r\<in>M. separation(##M, \<lambda>x. sats(M,converse_sep_fm, [x, r]))"
    by simp
  with \<open>R\<in>M\<close> have 
        "separation(##M, \<lambda>x. sats(M,converse_sep_fm, [x, R]))"
    by simp
  with \<open>R\<in>M\<close> show ?thesis unfolding separation_def converse_sep_fm_def  by (simp del: pair_abs)
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
                Un_commute nat_union_abs1)

lemma (in forcing_data) restrict_sep_intf :
  assumes
         "A\<in>M"
  shows
         "separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A & (\<exists>y\<in>M. pair(##M,x,y,z)))"
proof -
  from separation_ax have 
        "\<forall>a\<in>M. separation(##M, \<lambda>x. sats(M,restrict_sep_fm, [x, a]))"
    by simp
  with \<open>A\<in>M\<close> have 
        "separation(##M, \<lambda>x. sats(M,restrict_sep_fm, [x, A]))"
    by simp
  with \<open>A\<in>M\<close> show ?thesis unfolding separation_def restrict_sep_fm_def by (simp del: pair_abs)
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
  by (simp add: comp_sep_fm_def pair_fm_def upair_fm_def Un_commute nat_union_abs1)

lemma (in forcing_data) comp_sep_intf :
  assumes
    "R\<in>M"
    and
    "S\<in>M"
  shows
    "separation(##M,\<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
              pair(##M,x,z,xz) & pair(##M,x,y,xy) & pair(##M,y,z,yz) & xy\<in>S & yz\<in>R)"
proof -
  from separation_ax arity_tup2p have
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. sats(M,tupling_fm_2p(comp_sep_fm),[x,v])))"
    by simp
  then have
    "(\<forall>v\<in>M. separation
             (##M, \<lambda>x. \<forall>A\<in>M. \<forall>B\<in>M. pair(##M, A, B, v) \<longrightarrow>
                                    (\<exists>xa\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M. pair(##M, xa, z, x) \<and>
              pair(##M, xa, y, xy) \<and> pair(##M, y, z, yz) \<and> xy \<in> B \<and> yz \<in> A)))"
  unfolding separation_def tupling_fm_2p_def comp_sep_fm_def by (simp del: pair_abs)
  with tupling_sep_2p have 
    "(\<forall>r\<in>M. \<forall>s\<in>M. separation
         (##M, \<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M. pair(##M, x, z, xz) \<and>
                                    pair(##M, x, y, xy) \<and> pair(##M, y, z, yz) \<and> xy \<in> s \<and> yz \<in> r))"
    by simp
  with \<open>S\<in>M\<close> \<open>R\<in>M\<close> show ?thesis by simp
qed
 
(* pred_separation:
   "[| M(r); M(x) |] ==> separation(M, \<lambda>y. \<exists>p[M]. p\<in>r & pair(M,y,x,p))"
*)
  
lemma arity_pred_fm [simp] : 
  "arity(Exists(And(Member(0,2),pair_fm(3,1,0)))) = 3"
  by (simp add: pair_fm_def upair_fm_def Un_commute nat_union_abs1)

lemma (in forcing_data) pred_sep_intf:
    assumes
      "R\<in>M"
    and
      "X\<in>M"
    shows
      "separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>R & pair(##M,y,X,p))"
proof -
  from separation_ax arity_tup2p arity_pred_fm have
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. sats(M,tupling_fm_2p(Exists(And(Member(0,2),
                                                                  pair_fm(3,1,0)))),[x,v])))"
  by simp
  then have
    "(\<forall>v\<in>M. separation(##M, \<lambda>x. \<forall>A\<in>M. \<forall>B\<in>M. pair(##M, A, B, v) \<longrightarrow> 
                                                        (\<exists>p\<in>M. p \<in> A \<and> pair(##M, x, B, p))))"
  unfolding separation_def tupling_fm_2p_def by (simp del: pair_abs)
  with tupling_sep_2p have
    "\<forall>r\<in>M. \<forall>x\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & pair(##M,y,x,p))"
  by simp
  with \<open>R\<in>M\<close> \<open>X\<in>M\<close> show ?thesis by simp
qed
  
  
   
(* Memrel_separation:
     "separation(M, \<lambda>z. \<exists>x[M]. \<exists>y[M]. pair(M,x,y,z) & x \<in> y)"
*)
definition
  memrel_fm :: "i" where
  "memrel_fm == Exists(Exists(And(pair_fm(1,0,2),Member(1,0))))"
    
lemma [TC] : "memrel_fm \<in> formula"
  by (simp add: memrel_fm_def)
  
lemma [simp] : "arity(memrel_fm) = 1"
  by (simp add: memrel_fm_def pair_fm_def upair_fm_def Un_commute nat_union_abs1)

lemma (in forcing_data) memrel_sep_intf:
  "separation(##M, \<lambda>z. \<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) & x \<in> y)"
proof -
  from separation_ax have
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. sats(M,memrel_fm,[x,v])))"
    by simp
  then have      
    "(\<forall>v\<in>M. separation(##M, \<lambda>z. \<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) & x \<in> y))"
    unfolding separation_def memrel_fm_def by (simp del: pair_abs)
  with zero_in_M show ?thesis by auto
qed

(*is_recfun_separation:
     \<comment>\<open>for well-founded recursion: used to prove \<open>is_recfun_equal\<close>\<close>
     "[| M(r); M(f); M(g); M(a); M(b) |]
     ==> separation(M,
            \<lambda>x. \<exists>xa[M]. \<exists>xb[M].
                pair(M,x,a,xa) & xa \<in> r & pair(M,x,b,xb) & xb \<in> r &
                (\<exists>fx[M]. \<exists>gx[M]. fun_apply(M,f,x,fx) & fun_apply(M,g,x,gx) &
                                   fx \<noteq> gx))"
*)
  
definition
  is_recfun_sep_fm :: "i" where
  "is_recfun_sep_fm == 
  Exists(Exists(And(pair_fm(10,3,1),And(Member(1,6),And(pair_fm(10,2,0),And(Member(0,6),
                Exists(Exists(And(fun_apply_fm(7,12,1),
                And(fun_apply_fm(6,12,0),Neg(Equal(1,0))))))))))))"
  
lemma is_recfun_sep_fm [TC] : "is_recfun_sep_fm \<in> formula"
  by (simp add: is_recfun_sep_fm_def)

lemma [simp] : "arity(is_recfun_sep_fm) = 9"
  by (simp add: is_recfun_sep_fm_def fun_apply_fm_def upair_fm_def
                image_fm_def big_union_fm_def pair_fm_def Un_commute nat_union_abs1)


lemma (in forcing_data) is_recfun_sep_intf :
  assumes
        "r\<in>M" "f\<in>M" "g\<in>M" "a\<in>M" "b\<in>M"
   shows
      "separation(##M,\<lambda>x. \<exists>xa\<in>M. \<exists>xb\<in>M.
                    pair(##M,x,a,xa) & xa \<in> r & pair(##M,x,b,xb) & xb \<in> r &
                    (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M,f,x,fx) & fun_apply(##M,g,x,gx) &
                                     fx \<noteq> gx))"
proof -
  from separation_ax arity_tup5p have
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. sats(M,tupling_fm_5p(is_recfun_sep_fm),[x,v])))"
    by simp
  then have
      "(\<forall>v\<in>M. separation
             (##M, \<lambda>x. \<forall>B3\<in>M. \<forall>B2\<in>M. \<forall>B1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
                    \<forall>A1\<in>M. pair(##M, A4, A5, B1) \<and> pair(##M, A3, B1, B2) \<and> pair(##M, A2, B2, B3) \<and> 
                            pair(##M, A1, B3, v) \<longrightarrow>
         (\<exists>xa\<in>M. \<exists>xb\<in>M. pair(##M, x, A2, xa) \<and> xa \<in> A5 \<and> pair(##M, x, A1, xb) \<and> xb \<in> A5 \<and> 
              (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M, A4, x, fx) \<and> fun_apply(##M, A3, x, gx) \<and> fx \<noteq> gx))))" 
    unfolding separation_def tupling_fm_5p_def is_recfun_sep_fm_def by (simp del: pair_abs)
  with tupling_sep_5p_rel2 have
    "(\<forall>r\<in>M. \<forall>f\<in>M. \<forall>g\<in>M. \<forall>a\<in>M. \<forall>b\<in>M. 
    separation(##M,\<lambda>x. \<exists>xa\<in>M. \<exists>xb\<in>M.
                    pair(##M,x,a,xa) & xa \<in> r & pair(##M,x,b,xb) & xb \<in> r &
                    (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M,f,x,fx) & fun_apply(##M,g,x,gx) &
                                     fx \<noteq> gx)))"
  by simp 
  with \<open>r\<in>M\<close> \<open>f\<in>M\<close> \<open>g\<in>M\<close> \<open>a\<in>M\<close> \<open>b\<in>M\<close> show ?thesis by simp
qed

definition 
  sixp_sep_perm :: "i" where
  "sixp_sep_perm == {<0,8>,<1,0>,<2,1>,<3,2>,<4,3>,<5,4>}" 

lemma sixp_perm_ftc : "sixp_sep_perm \<in> 6 -||> 9"
  by(unfold sixp_sep_perm_def,(rule consI,auto)+,rule emptyI)

lemma dom_sixp_perm : "domain(sixp_sep_perm) = 6"
  by(unfold sixp_sep_perm_def,auto)
  
lemma sixp_perm_tc : "sixp_sep_perm \<in> 6 \<rightarrow> 9"
  by(subst dom_sixp_perm[symmetric],rule FiniteFun_is_fun,rule sixp_perm_ftc)

lemma apply_fun: "f \<in> Pi(A,B) ==> <a,b>: f \<Longrightarrow> f`a = b"
  by(auto simp add: apply_iff)

lemma sixp_perm_env : 
  "{x,a1,a2,a3,a4,a5} \<subseteq> A \<Longrightarrow> j<6 \<Longrightarrow>
  nth(j,[x,a1,a2,a3,a4,a5]) = nth(sixp_sep_perm`j,[a1,a2,a3,a4,a5,b1,b2,b3,x,v])"
  apply(subgoal_tac "j\<in>nat")
  apply(rule natE,simp,subst apply_fun,rule sixp_perm_tc,simp add:sixp_sep_perm_def,simp+)+
  apply(subst apply_fun,rule sixp_perm_tc,simp add:sixp_sep_perm_def,simp+,drule ltD,auto)
  done
    
lemma arity_sixp_perm: "True"
  oops
    
lemma (in forcing_data) sixp_sep: 
  assumes
    "\<phi> \<in> formula" "arity(\<phi>)\<le>6" "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" "a5\<in>M"
  shows 
    "separation(##M,\<lambda>x. sats(M,\<phi>,[x,a1,a2,a3,a4,a5]))"
proof -
  let 
    ?f="sixp_sep_perm"
  let
    ?\<phi>'="ren(\<phi>)`6`9`?f"
  from assms have
    "arity(?\<phi>')\<le>9" "?\<phi>' \<in> formula"
    using sixp_perm_tc ren_arity ren_tc by simp_all
  then have
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. sats(M,tupling_fm_5p(?\<phi>'),[x,v])))"
    using separation_ax arity_tup5p_leq by simp
  then have
    Eq1: "(\<forall>v\<in>M. separation
             (##M, \<lambda>x. \<forall>B3\<in>M. \<forall>B2\<in>M. \<forall>B1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
                    \<forall>A1\<in>M. pair(##M, A4, A5, B1) \<and> pair(##M, A3, B1, B2) \<and> pair(##M, A2, B2, B3) \<and> 
                            pair(##M, A1, B3, v) \<longrightarrow>
               sats(M,?\<phi>',[A1,A2,A3,A4,A5,B1,B2,B3,x,v])))" 
    (is "\<forall>v\<in>M. separation(_ , \<lambda>x. ?P(x,v))")
    unfolding separation_def tupling_fm_5p_def by (simp del: pair_abs)
  {
    fix B1 B2 B3 A1 A2 A3 A4 A5 x v
    assume
      "x\<in>M" "v\<in>M"
      "B3\<in>M" "B2\<in>M" "B1\<in>M" "A5\<in>M" "A4\<in>M" "A3\<in>M" "A2\<in>M" "A1\<in>M"
      (* "sats(M,?\<phi>',[A1,A2,A3,A4,A5,B1,B2,B3,x,v])" is "sats(_,_,?env1)"*)
    with assms have
      "sats(M,?\<phi>',[A1,A2,A3,A4,A5,B1,B2,B3,x,v]) \<longleftrightarrow> sats(M,\<phi>,[x,A1,A2,A3,A4,A5])" 
      (is "sats(_,_,?env1) \<longleftrightarrow> sats(_,_,?env2)")
      using renSat[of \<phi> 6 9 ?env2 M ?env1 ?f] sixp_perm_tc sixp_perm_env [of _ _ _ _ _ _ "M"]  
      by auto
  }
  then have
    Eq2: "x\<in>M \<Longrightarrow> v\<in>M \<Longrightarrow> ?P(x,v) \<longleftrightarrow> (\<forall>B3\<in>M. \<forall>B2\<in>M. \<forall>B1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
                    \<forall>A1\<in>M. pair(##M, A4, A5, B1) \<and> pair(##M, A3, B1, B2) \<and> pair(##M, A2, B2, B3) \<and> 
                            pair(##M, A1, B3, v) \<longrightarrow>
               sats(M,\<phi>,[x,A1,A2,A3,A4,A5]))" (is "_ \<Longrightarrow> _\<Longrightarrow> _ \<longleftrightarrow> ?Q(x,v)") for x v 
    by (simp del: pair_abs)
  define PP where "PP \<equiv> ?P"
  define QQ where "QQ \<equiv> ?Q"
  from Eq2 have
      "x\<in>M \<Longrightarrow> v\<in>M \<Longrightarrow> PP(x,v) \<longleftrightarrow> QQ(x,v)" for x v 
      unfolding PP_def QQ_def .
  then have
    "v\<in>M \<Longrightarrow> 
     (\<forall>z[##M]. \<exists>y[##M]. \<forall>x[##M]. x \<in> y \<longleftrightarrow> x \<in> z \<and> PP(x,v)) \<longleftrightarrow>
     (\<forall>z[##M]. \<exists>y[##M]. \<forall>x[##M]. x \<in> y \<longleftrightarrow> x \<in> z \<and> QQ(x,v))" for v by (simp del: pair_abs)
  with Eq1 have
    "(\<forall>v\<in>M. separation (##M, \<lambda>x. QQ(x,v)))"
    unfolding separation_def PP_def by (simp del: pair_abs)
  with assms show ?thesis unfolding QQ_def using tupling_sep_5p_rel2  by simp
qed 
  
(* Instance of Replacement for M_basic *)
  
(* funspace_succ_replacement:
     "M(n) ==>
      strong_replacement(M, \<lambda>p z. \<exists>f[M]. \<exists>b[M]. \<exists>nb[M]. \<exists>cnbf[M].
                pair(M,f,b,p) & pair(M,n,b,nb) & is_cons(M,nb,f,cnbf) &
                upair(M,cnbf,cnbf,z))" 
*)
definition 
  is_cons_fm :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
 "is_cons_fm(a,b,z) == Exists(And(upair_fm(succ(a),succ(a),0),union_fm(0,succ(b),succ(z))))"

lemma is_cons_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> is_cons_fm(x,y,z) \<in> formula"
by (simp add: is_cons_fm_def)

lemma is_cons_fm [simp] :
  "\<lbrakk> a \<in> nat ; b \<in> nat ; z \<in> nat ; env \<in> list(A) \<rbrakk> \<Longrightarrow> 
    sats(A,is_cons_fm(a,b,z),env) \<longleftrightarrow> 
    is_cons(##A,nth(a,env),nth(b,env),nth(z,env))"
  by (simp add: is_cons_fm_def is_cons_def)

definition 
  funspace_succ_fm :: "i" where
  "funspace_succ_fm == 
    Exists(Exists(Exists(Exists(And(pair_fm(3,2,4),And(pair_fm(6,2,1),
        And(is_cons_fm(1,3,0),upair_fm(0,0,5))))))))"
  
lemma funspace_succ_fm_type [TC] : 
  "funspace_succ_fm \<in> formula"
  by (simp add: funspace_succ_fm_def)

lemma [simp] : "arity(funspace_succ_fm) = 3" 
  by (simp add: funspace_succ_fm_def pair_fm_def upair_fm_def is_cons_fm_def 
                    union_fm_def Un_commute nat_union_abs1)

lemma (in forcing_data) funspace_succ_rep_intf :
  assumes
      "n\<in>M"
  shows
     "strong_replacement(##M,
          \<lambda>p z. \<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M.
                pair(##M,f,b,p) & pair(##M,n,b,nb) & is_cons(##M,nb,f,cnbf) &
                upair(##M,cnbf,cnbf,z))"
proof -
  from replacement_ax have 
       "(\<forall>a\<in>M. strong_replacement(##M,\<lambda>x y. sats(M,funspace_succ_fm,[x,y,a])))"      
    by simp
  then have
    "(\<forall>n\<in>M. strong_replacement(##M,
          \<lambda>p z. \<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M.
                pair(##M,f,b,p) & pair(##M,n,b,nb) & is_cons(##M,nb,f,cnbf) &
                upair(##M,cnbf,cnbf,z)))"
    unfolding funspace_succ_fm_def strong_replacement_def univalent_def by (simp del: pair_abs)
  with \<open>n\<in>M\<close> show ?thesis by simp
qed


(* Interface with M_basic *)
  
lemmas (in forcing_data) M_basic_sep_instances = 
                inter_sep_intf diff_sep_intf cartprod_sep_intf
                image_sep_intf converse_sep_intf restrict_sep_intf
                pred_sep_intf memrel_sep_intf comp_sep_intf is_recfun_sep_intf
  
sublocale forcing_data \<subseteq> M_basic_no_repl "##M"
  apply (insert trans_M zero_in_M power_ax)
  apply (rule M_basic_no_repl.intro,rule mtriv)
  apply (rule M_basic_no_repl_axioms.intro)
  apply (insert M_basic_sep_instances funspace_succ_rep_intf)
  apply (simp_all)
done
  
end