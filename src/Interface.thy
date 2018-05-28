(* Interface between internalized axiom formulas and 
   ZF axioms *)
theory Interface imports ZFCAxioms_formula Relative_no_repl Names begin

(* Extensionality *)
lemma extension_intf :
   "sats(A,extension_ax_fm,[])
   \<longleftrightarrow>
   extensionality(##A)"
  by (simp add: extension_ax_fm_def extensionality_def)

(* Foundation *)
lemma foundation_intf :
  "sats(A,foundation_ax_fm,[])
   \<longleftrightarrow>
   foundation_ax(##A)"
  by (simp add: foundation_ax_fm_def foundation_ax_def)

(* Pairing *)
lemma pairing_intf :
  "sats(A,pairing_ax_fm,[])
   \<longleftrightarrow>
   upair_ax(##A)"
  by (simp add: pairing_ax_fm_def upair_ax_def)

(* Union *)
lemma union_intf :
  "sats(A,union_ax_fm,[])
  \<longleftrightarrow>
  Union_ax(##A)"
  by (simp add: union_ax_fm_def Union_ax_def)

(* Powerset *)
lemma power_intf :
  "sats(A,powerset_ax_fm,[])
  \<longleftrightarrow>
  power_ax(##A)"
  by (simp add: powerset_ax_fm_def power_ax_def powerset_def subset_def subset_fm_def)

(* Interface for Transset *)
lemma Transset_intf :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)
    
locale M_ZF =  
  fixes M
  assumes trans_M:          "Transset(M)"
      and M_model_ZF:       "satT(M,ZFTh,[])"
      and M_nempty:         "0 \<in> M"

begin  (*************** CONTEXT: M_ZF  ************************)
lemma intf_M_trivial :
  "M_trivial_no_repl(##M)"
  apply (insert trans_M M_model_ZF M_nempty)
  apply (rule M_trivial_no_repl.intro)
  apply (simp,rule Transset_intf,assumption+)
  apply (simp_all add: pairing_intf[symmetric] union_intf[symmetric] 
                       power_intf[symmetric] ZFTh_def ZF_fin_def satT_sats)
done
    
interpretation Mtriv : M_trivial_no_repl "##M" by (rule intf_M_trivial)
  

(* Separation *)
lemma uniq_dec_2p: "<C,D> \<in> M \<Longrightarrow> 
             \<forall>A\<in>M. \<forall>B\<in>M. <C,D> = \<langle>A, B\<rangle> \<longrightarrow> P(x, A, B)
            \<longleftrightarrow>
              P(x, C, D)"
  by simp
    
lemma tupling_sep_2p :
    "(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>A\<in>M. \<forall>B\<in>M. pair(##M,A,B,v) \<longrightarrow> P(x,A,B))))
    \<longleftrightarrow>
     (\<forall>A\<in>M. \<forall>B\<in>M. separation(##M,\<lambda>x. P(x,A,B)))"
  apply (simp add: separation_def)
proof (intro ballI iffI)
  fix A B z
  assume
        Eq1:  "\<forall>v\<in>M. \<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and> (\<forall>A\<in>M. \<forall>B\<in>M. v = \<langle>A, B\<rangle> \<longrightarrow> P(x, A, B))"
     and
        Eq2:  "A\<in>M" "B\<in>M" "z\<in>M"  (* no puedo poner la conjunción *)
  then have 
        Eq3:  "<A,B>\<in>M"
    by (simp del:setclass_iff add:setclass_iff[symmetric])
  with Eq1 have 
              "\<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and> (\<forall>C\<in>M. \<forall>D\<in>M. <A,B> = \<langle>C, D\<rangle> \<longrightarrow> P(x, C, D))"
    by (rule bspec)
  with uniq_dec_2p and Eq3 and Eq2 show
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and>  P(x, A, B)"
    by simp
next
  fix v z
  assume
       asms:  "v\<in>M"   "z\<in>M"
              "\<forall>A\<in>M. \<forall>B\<in>M. \<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> P(x, A, B)"
  consider (a) "\<exists>A\<in>M. \<exists>B\<in>M. v = \<langle>A, B\<rangle>" | (b) "\<forall>A\<in>M. \<forall>B\<in>M. v \<noteq> \<langle>A, B\<rangle>" by auto
  then show                (* "then" is important here *)
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> 
                    (\<forall>A\<in>M. \<forall>B\<in>M. v = \<langle>A, B\<rangle> \<longrightarrow> P(x, A, B))"
  proof cases
    case a
    then obtain A B where  (* also here *)
        Eq4:  "A\<in>M" "B\<in>M" "v = \<langle>A, B\<rangle>"
      by auto
    then have
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> P(x, A, B)"
      using asms by simp
    then show ?thesis using Eq4 and uniq_dec_2p by simp
  next
    case b
    then have
              "\<forall>x\<in>M. x \<in> z \<longleftrightarrow> x \<in> z \<and> (\<forall>A\<in>M. \<forall>B\<in>M. v = \<langle>A, B\<rangle> \<longrightarrow> P(x, A, B))"
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

lemma tupling_sep_5p : 
"(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. 
                  v = \<langle>A1, \<langle>A2, \<langle>A3, \<langle>A4, A5\<rangle>\<rangle>\<rangle>\<rangle> \<longrightarrow> P(x,A1,A2,A3,A4,A5))))
    \<longleftrightarrow>
 (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. separation(##M,\<lambda>x. P(x,A1,A2,A3,A4,A5)))"
  apply (simp add: separation_def)
proof (intro ballI iffI)
  fix A B C D E z
  assume
        Eq1:  "\<forall>v\<in>M. \<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and> (\<forall>A\<in>M. \<forall>B\<in>M.  \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. v = \<langle>A, B,C,D,E\<rangle> 
                   \<longrightarrow> P(x, A, B, C, D, E))"
     and
        Eq2:  "A\<in>M" "B\<in>M" "C\<in>M" "D\<in>M" "E\<in>M" "z\<in>M"  (* no puedo poner la conjunción *)
  then have 
        Eq3:  "<A,B,C,D,E>\<in>M"
    by (simp del:setclass_iff add:setclass_iff[symmetric])
  with Eq1 have 
              "\<forall>z\<in>M. \<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and> (\<forall>A'\<in>M. \<forall>B'\<in>M.  \<forall>C'\<in>M. \<forall>D'\<in>M. \<forall>E'\<in>M. <A,B,C,D,E> = \<langle>A',B',C',D',E'\<rangle> 
                   \<longrightarrow> P(x, A', B', C', D', E'))"
    by (rule bspec)
  with uniq_dec_5p and Eq3 and Eq2 show
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> 
               x \<in> z \<and>  P(x,A,B,C,D,E)"
    by simp
next
  fix v z
  assume
       asms:  "v\<in>M"   "z\<in>M"
              "\<forall>A\<in>M. \<forall>B\<in>M. \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. \<forall>z\<in>M. \<exists>y\<in>M. 
                  \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> P(x, A,B,C,D,E)"
  consider (a) "\<exists>A\<in>M. \<exists>B\<in>M. \<exists>C\<in>M. \<exists>D\<in>M. \<exists>E\<in>M. v = \<langle>A,B,C,D,E\<rangle>" | 
           (b) "\<forall>A\<in>M. \<forall>B\<in>M. \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. v \<noteq> \<langle>A,B,C,D,E\<rangle>" by blast
  then show               
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> 
                    (\<forall>A\<in>M. \<forall>B\<in>M. \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. v = \<langle>A,B,C,D,E\<rangle> \<longrightarrow> P(x,A,B,C,D,E))"
  proof cases
    case a
    then obtain A B C D E where 
        Eq4:  "A\<in>M" "B\<in>M" "C\<in>M" "D\<in>M" "E\<in>M" "v = \<langle>A,B,C,D,E\<rangle>"
      by auto
    then have
              "\<exists>y\<in>M. \<forall>x\<in>M. x \<in> y \<longleftrightarrow> x \<in> z \<and> P(x,A,B,C,D,E)"
      using asms by simp
    then show ?thesis using Eq4 by simp
  next
    case b
    then have
              "\<forall>x\<in>M. x \<in> z \<longleftrightarrow> x \<in> z \<and> 
                (\<forall>A\<in>M. \<forall>B\<in>M.  \<forall>C\<in>M. \<forall>D\<in>M. \<forall>E\<in>M. v = \<langle>A,B,C,D,E\<rangle> \<longrightarrow> P(x,A,B,C,D,E))"
      by simp
    then show ?thesis using b and asms by auto
  qed
qed

(*  Misma prueba que el lema siguiente. 
 *
lemma tupling_simp2 :
        "(\<forall>B\<in>M. \<forall>A\<in>M. 
          \<langle>A, B\<rangle> \<in> M \<and> Q(A,B) \<longrightarrow> P(A,B))
       \<longleftrightarrow>
         (\<forall>B\<in>M. \<forall>A\<in>M. 
          Q(A,B) \<longrightarrow> P(A,B))"
proof (intro iffI ballI impI)
  fix A B
  assume 
       asms:  "\<forall>B\<in>M. \<forall>A\<in>M. \<langle>A, B\<rangle> \<in> M \<and> Q(A, B) \<longrightarrow> P(A, B)"
              "B \<in> M"
              "A \<in> M" 
              "Q(A, B)"
  then have
              "\<langle>A, B\<rangle> \<in> M \<and> Q(A, B) \<longrightarrow> P(A, B)"
    by simp
  with asms and Mtriv.pair_in_M_iff show "P(A,B)" 
      by simp
  next
  fix A B
  assume 
       asms:  "\<forall>B\<in>M. \<forall>A\<in>M. Q(A, B) \<longrightarrow> P(A, B)"
              "A \<in> M" 
              "B \<in> M"
              "\<langle>A, B\<rangle> \<in> M \<and> Q(A, B)"
  then show               
              "P(A,B)" 
    by simp
qed
*)  
lemma tupling_simp2_rule:
         "B \<in> M \<Longrightarrow> 
          (\<forall>A\<in>M. 
          \<langle>A, B\<rangle> \<in> M \<and> Q(A,B) \<longrightarrow> P(A,B))
       \<longleftrightarrow>
         (\<forall>A\<in>M. 
          Q(A,B) \<longrightarrow> P(A,B))"
proof (intro iffI ballI impI)
  fix A B
  assume 
       asms:  "\<forall>A\<in>M. \<langle>A, B\<rangle> \<in> M \<and> Q(A, B) \<longrightarrow> P(A, B)"
              "B \<in> M"
              "A \<in> M" 
              "Q(A, B)"
  then have
              "\<langle>A, B\<rangle> \<in> M \<and> Q(A, B) \<longrightarrow> P(A, B)"
    by simp
  with asms and Mtriv.pair_in_M_iff show "P(A,B)" 
      by simp
  next
  fix A B
  assume 
       asms:  "\<forall>A\<in>M. Q(A, B) \<longrightarrow> P(A, B)"
              "A \<in> M" 
              "B \<in> M"
              "\<langle>A, B\<rangle> \<in> M \<and> Q(A, B)"
  then show               
              "P(A,B)" 
    by simp
qed
    
lemma tupling_simp3 :
        "(\<forall>C\<in>M. \<forall>B\<in>M. \<forall>A\<in>M. 
          \<langle>A, B, C\<rangle> \<in> M \<and> Q(A,B,C) \<longrightarrow> P(A,B,C))
       \<longleftrightarrow>
         (\<forall>C\<in>M. \<forall>B\<in>M. \<forall>A\<in>M. 
          Q(A,B,C) \<longrightarrow> P(A,B,C))"
proof (auto)
  fix C B A
  assume
       asms:  "\<forall>C\<in>M. \<forall>B\<in>M. \<forall>A\<in>M. \<langle>A, B, C\<rangle> \<in> M \<and> Q(A, B, C) \<longrightarrow> P(A, B, C)"
              "C \<in> M"
              "B \<in> M"
              "A \<in> M"
              "Q(A, B, C)"
  then have 
          1:  "\<forall>A\<in>M. \<langle>A, B, C\<rangle> \<in> M \<and> Q(A, B, C) \<longrightarrow> P(A, B, C)"
    by simp
  from asms and Mtriv.pair_in_M_iff have
              "<B,C> \<in> M"
    by simp
  with 1 and tupling_simp2_rule have
              "\<forall>A\<in>M. \<langle>A, B, C\<rangle> \<in> M \<and> Q(A, B, C) \<longrightarrow> P(A, B, C)"
    by simp
  with asms and Mtriv.pair_in_M_iff show "P(A,B,C)" by simp
qed
  
lemma tuples_in_M: "A\<in>M \<Longrightarrow> B\<in>M \<Longrightarrow> <A,B>\<in>M" 
   by (simp del:setclass_iff add:setclass_iff[symmetric])

lemma tupling_sep_5p_aux :
              "(\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
                \<langle>A4, A5\<rangle> \<in> M \<and> \<langle>A3, A4, A5\<rangle> \<in> M \<and> \<langle>A2, A3, A4, A5\<rangle> \<in> M \<and> 
                v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
                P(x, A1, A2, A3, A4, A5))
               \<longleftrightarrow>
               (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M.
                v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
                P(x, A1, A2, A3, A4, A5))" for x v
 by (auto simp add:tuples_in_M)

declare iff_trans [trans]
  
lemma tupling_sep_5p_rel : 
"(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. 
                    \<forall>B1\<in>M. \<forall>B2\<in>M. \<forall>B3\<in>M.   
                    pair(##M,A4,A5,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> P(x,A1,A2,A3,A4,A5))))
    \<longleftrightarrow>
 (\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. separation(##M,\<lambda>x. P(x,A1,A2,A3,A4,A5)))"
proof (simp)
  have
      "(\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
        \<langle>A4, A5\<rangle> \<in> M \<and> \<langle>A3, A4, A5\<rangle> \<in> M \<and> \<langle>A2, A3, A4, A5\<rangle> \<in> M \<and> v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
        P(x, A1, A2, A3, A4, A5))
      \<longleftrightarrow>
      (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M.
        v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
        P(x, A1, A2, A3, A4, A5))" for x v
    by (rule tupling_sep_5p_aux)
  then have
      "(\<forall>v\<in>M. separation
             (##M,
              \<lambda>x. \<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
        \<langle>A4, A5\<rangle> \<in> M \<and> \<langle>A3, A4, A5\<rangle> \<in> M \<and> \<langle>A2, A3, A4, A5\<rangle> \<in> M \<and> v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
        P(x, A1, A2, A3, A4, A5)))
      \<longleftrightarrow>
      (\<forall>v\<in>M. separation
             (##M,
              \<lambda>x. \<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M.
        v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
        P(x, A1, A2, A3, A4, A5)))"
    by simp
  also have
     "...   \<longleftrightarrow>
 (\<forall>A1\<in>M. \<forall>A2\<in>M. \<forall>A3\<in>M. \<forall>A4\<in>M. \<forall>A5\<in>M. separation(##M,\<lambda>x. P(x,A1,A2,A3,A4,A5)))"
    using tupling_sep_5p by simp
  finally  show
    "(\<forall>v\<in>M. separation
             (##M,
              \<lambda>x. \<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M.
\<langle>A4, A5\<rangle> \<in> M \<and> \<langle>A3, A4, A5\<rangle> \<in> M \<and> \<langle>A2, A3, A4, A5\<rangle> \<in> M \<and> v = \<langle>A1, A2, A3, A4, A5\<rangle> \<longrightarrow>
P(x, A1, A2, A3, A4, A5))) \<longleftrightarrow>
    (\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. separation(##M, \<lambda>x. P(x, A1, A2, A3, A4, A5)))"
    by auto
qed

lemma tupling_sep_5p_rel2 : 
"(\<forall>v\<in>M. separation(##M,\<lambda>x. (\<forall>B3\<in>M. \<forall>B2\<in>M. \<forall>B1\<in>M. 
                    \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. \<forall>A1\<in>M.  
                    pair(##M,A4,A5,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> P(x,A1,A2,A3,A4,A5))))
    \<longleftrightarrow>
 (\<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. \<forall>A1\<in>M. separation(##M,\<lambda>x. P(x,A1,A2,A3,A4,A5)))"
proof -
  have
        "(\<forall>B3\<in>M. \<forall>B2\<in>M. \<forall>B1\<in>M. 
                    \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. \<forall>A1\<in>M.  
                    pair(##M,A4,A5,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> P(x,A1,A2,A3,A4,A5))
          \<longleftrightarrow>
         (\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. 
                    \<forall>B1\<in>M. \<forall>B2\<in>M. \<forall>B3\<in>M.   
                    pair(##M,A4,A5,B1) & 
                    pair(##M,A3,B1,B2) & 
                    pair(##M,A2,B2,B3) & 
                    pair(##M,A1,B3,v)  
               \<longrightarrow> P(x,A1,A2,A3,A4,A5))" 
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
    " ... \<longleftrightarrow> (\<forall>A1\<in>M. \<forall>A5\<in>M. \<forall>A4\<in>M. \<forall>A3\<in>M. \<forall>A2\<in>M. separation(##M,\<lambda>x. P(x,A1,A2,A3,A4,A5)))"
    using tupling_sep_5p_rel by simp
  finally show ?thesis by auto
qed

end    (*************** CONTEXT: M_ZF  ************************)
  
(* Tupling para fórmula para instancia de separación.
   Se asume que la aridad es 3: las dos primeras variables son los
   parámetros que se van a tuplear, la siguiente es el x de separación*)

definition 
  tupling_fm_2p :: "i \<Rightarrow> i" where
  "tupling_fm_2p(\<phi>) = Forall(Forall(Implies(pair_fm(1,0,3),\<phi>)))"
  
lemma [TC] :  "\<lbrakk> \<phi> \<in> formula \<rbrakk> \<Longrightarrow> tupling_fm_2p(\<phi>) \<in> formula"
  by (simp add: tupling_fm_2p_def)
    
    
lemma arity_tup2p :  
  "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>) = 3 \<rbrakk> \<Longrightarrow> arity(tupling_fm_2p(\<phi>)) = 2"
  by (simp add: tupling_fm_2p_def arity_incr_bv_lemma pair_fm_def 
                upair_fm_def Un_commute nat_union_abs1)

              
(* quisiera que me salga esto, pero no me sale:
consts incrn_bv :: "i=>i"
primrec
  "incrn_bv(0) =
      (\<lambda>p \<in> formula. \<lambda> nq\<in>nat. p)"
  
  "incrn_bv(succ(n)) = 
      (\<lambda>p \<in> formula. \<lambda> nq\<in>nat. (incrn_bv(n)`(incr_bv(p)`nq))`nq)"

lemma incrn_bv_type [TC]: "n \<in> nat ==> incrn_bv(n) \<in> formula \<rightarrow> nat \<rightarrow> formula"
  by (induct_tac n, simp_all)
    
lemma [TC] :"\<lbrakk> n\<in>nat ; \<phi>\<in>formula \<rbrakk> \<Longrightarrow> incrn_bv(n)`\<phi> \<in> nat \<rightarrow> formula"
  by (simp)
    
lemma [TC] :"\<lbrakk> n\<in>nat ; \<phi>\<in>formula ; m\<in>nat \<rbrakk> \<Longrightarrow> (incrn_bv(n)`\<phi>)`m \<in> formula"
  by (simp)
    
    
lemma sats_incrn_bv_iff [rule_format]:
  "[| p \<in> formula; env \<in> list(A) ; bvs' \<in> list(A) |]
   ==> \<forall>bvs \<in> list(A).
           sats(A, (incrn_bv(length(bvs'))`p)`(length(bvs)), 
                          bvs@(bvs'@env)) \<longleftrightarrow>
           sats(A, p, bvs@env)"
  sorry

*)

(*
0 \<longrightarrow> A1
..
4 \<longrightarrow> A5
8 \<longrightarrow> x

*)
              
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
    
          
lemma separation_intf : 
      "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>)=1 \<or> arity(\<phi>)=2 \<rbrakk> \<Longrightarrow> 
        sats(M,separation_ax_fm(\<phi>),[]) \<longleftrightarrow> 
       (\<forall>a\<in>M. separation(##M,\<lambda>x. sats(M,\<phi>,[x,a])))"
  by (simp add: separation_ax_fm_def separation_def sats_incr_bv1_iff)
    

lemma [simp] :
  "arity(Forall(Implies(Member(0,2),Member(1,0)))) = 2"
  by (simp add: Un_commute nat_union_abs1)
    
(* Instances of separation for interface with M_basic *)
lemma (in M_ZF) inter_sep_intf :
  "sats(M,separation_ax_fm(Forall(Implies(Member(0,2),Member(1,0)))),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. separation(##M,\<lambda>x . \<forall>y\<in>M . y\<in>A \<longrightarrow> x\<in>y))"
  by (simp add: separation_def separation_intf separation_ax_fm_def sats_incr_bv1_iff)

    
lemma [simp] : 
  "arity(Neg(Member(0,1))) = 2"
  by (simp add: nat_union_abs1)
    
lemma (in M_ZF) diff_sep_intf :
  "sats(M,separation_ax_fm(Neg(Member(0,1))),[])
  \<longleftrightarrow>
  (\<forall>B\<in>M. separation(##M,\<lambda>x . x\<notin>B))"
  by (simp add: separation_def separation_intf separation_ax_fm_def sats_incr_bv1_iff)
    
  (* cartprod_sep_fm vars:
     0 \<longrightarrow> B
     1 \<longrightarrow> A
     2 \<longrightarrow> x *)
definition
  cartprod_sep_fm :: "i" where
  "cartprod_sep_fm == 
              Exists(And(Member(0,2),
                     Exists(And(Member(0,2),pair_fm(1,0,4)))))"

lemma cartprof_sep_fm_type [TC] : 
  "cartprod_sep_fm \<in> formula"
  by (simp add: cartprod_sep_fm_def)
    
lemma [simp] : "arity(cartprod_sep_fm) = 3" 
  by (simp add: cartprod_sep_fm_def pair_fm_def upair_fm_def 
                Un_commute nat_union_abs1)


lemma (in M_ZF) cartprod_sep_intf :
  "sats(M,separation_ax_fm(tupling_fm_2p(cartprod_sep_fm)),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. \<forall>B\<in>M. separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A \<and> (\<exists>y\<in>M. y\<in>B \<and> pair(##M,x,y,z))))"
  apply (rule iff_trans)
   apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp+)
  apply (rule iff_trans) 
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2p_def cartprod_sep_fm_def)
  done
  
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
               

lemma (in M_ZF) image_sep_intf :
  "sats(M,separation_ax_fm(tupling_fm_2p(image_sep_fm)),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. \<forall>r\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M. x\<in>A & pair(##M,x,y,p))))"
  apply (rule iff_trans)
   apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp+)
  apply (rule iff_trans)
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2p_def image_sep_fm_def)
  done

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
    
lemma (in M_ZF) converse_sep_intf : 
  "sats(M,separation_ax_fm(converse_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. separation(##M,\<lambda>z. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M.
                      \<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,z))))"
  by (simp add: separation_def separation_intf separation_ax_fm_def 
                     sats_incr_bv1_iff converse_sep_fm_def)
  
definition
  restrict_sep_fm :: "i" where
  "restrict_sep_fm == Exists(And(Member(0,2),Exists(pair_fm(1,0,2))))"

lemma restrict_sep_fm_type [TC] : "restrict_sep_fm \<in> formula"
  by (simp add: restrict_sep_fm_def)
    
lemma [simp] : "arity(restrict_sep_fm) = 2"
  by (simp add: restrict_sep_fm_def pair_fm_def upair_fm_def 
                Un_commute nat_union_abs1)

lemma (in M_ZF) restrict_sep_intf :
  "sats(M,separation_ax_fm(restrict_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A & (\<exists>y\<in>M. pair(##M,x,y,z))))"
  by (simp add: separation_def separation_intf separation_ax_fm_def 
                     sats_incr_bv1_iff restrict_sep_fm_def)

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

lemma (in M_ZF) comp_sep_intf :
  "sats(M,separation_ax_fm(tupling_fm_2p(comp_sep_fm)),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>s\<in>M. 
    separation(##M,\<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
              pair(##M,x,z,xz) & pair(##M,x,y,xy) & pair(##M,y,z,yz) &
              xy\<in>s & yz\<in>r))"
  apply (rule iff_trans)
   apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp+)
  apply (rule iff_trans)
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2p_def comp_sep_fm_def)
  done

lemma [simp] : 
  "arity(Exists(And(Member(0,2),pair_fm(3,1,0)))) = 3"
  by (simp add: pair_fm_def upair_fm_def Un_commute nat_union_abs1)
    
lemma (in M_ZF) pred_sep_intf :
  "sats(M,separation_ax_fm(
       tupling_fm_2p(Exists(And(Member(0,2),pair_fm(3,1,0))))),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>x\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & pair(##M,y,x,p)))"
   apply (rule iff_trans)
   apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp+)
   apply (simp add: pair_fm_def upair_fm_def Un_commute nat_union_abs1)
  apply (rule iff_trans)
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2p_def comp_sep_fm_def)
  done

definition
  memrel_fm :: "i" where
  "memrel_fm == Exists(Exists(And(pair_fm(1,0,2),Member(1,0))))"
    
lemma [TC] : "memrel_fm \<in> formula"
  by (simp add: memrel_fm_def)
  
lemma [simp] : "arity(memrel_fm) = 1"
  by (simp add: memrel_fm_def pair_fm_def upair_fm_def Un_commute nat_union_abs1)
    
lemma sats_memrel :
   "\<lbrakk> a\<in>M ; x\<in>M  \<rbrakk>  \<Longrightarrow> 
    sats(M,memrel_fm,[x,a]) \<longleftrightarrow> 
    (\<exists>z\<in>M. \<exists>y\<in>M. pair(##M,z,y,x) & z \<in> y)"
   by (simp add: memrel_fm_def)

lemma (in M_ZF) memrel_sep_intf :
  "sats(M,separation_ax_fm(memrel_fm),[])
  \<longleftrightarrow>
  separation(##M, \<lambda>z. \<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) & x \<in> y)"
  apply (simp add: separation_def separation_intf sats_memrel)
  apply (insert M_nempty,auto)
  done


abbreviation
 dec10  :: i   ("10") where "10 == succ(9)"
    
abbreviation
 dec11  :: i   ("11") where "11 == succ(10)"

abbreviation
 dec12  :: i   ("12") where "12 == succ(11)"

abbreviation
 dec13  :: i   ("13") where "13 == succ(12)"


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
              
              
lemma (in M_ZF) is_recfun_sep_intf :
  "sats(M,separation_ax_fm(tupling_fm_5p(is_recfun_sep_fm)),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>f\<in>M. \<forall>g\<in>M. \<forall>a\<in>M. \<forall>b\<in>M. 
    separation(##M,\<lambda>x. \<exists>xa\<in>M. \<exists>xb\<in>M.
                    pair(##M,x,a,xa) & xa \<in> r & pair(##M,x,b,xb) & xb \<in> r &
                    (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M,f,x,fx) & fun_apply(##M,g,x,gx) &
                                     fx \<noteq> gx)))"
  apply (rule iff_trans)
  apply (rule separation_intf,simp,rule disjI2,rule arity_tup5p,simp+)
  apply (rule iff_trans)
  prefer 2
   apply (rule tupling_sep_5p_rel2)
  apply (simp add: separation_def tupling_fm_5p_def is_recfun_sep_fm_def)
    done


(* Instances of replacement for interface with M_basic *)

lemma sats_incr_bv0_iff:
  "[| p \<in> formula; env \<in> list(A); x \<in> A |]
   ==> sats(A, incr_bv(p)`0, Cons(x, env)) \<longleftrightarrow>
       sats(A, p, env)"
  by(insert sats_incr_bv_iff [of p env A x "[]"],simp)


lemma sats_incr_bv3_iff:
  "[| p \<in> formula; env \<in> list(A); x \<in> A ; y \<in> A ; z \<in> A ; w \<in> A|]
   ==> sats(A, incr_bv(p)`3, Cons(x, Cons(y,Cons(z,Cons(w,env))))) \<longleftrightarrow>
       sats(A, p, Cons(x,Cons(y,Cons(z,env))))"
  by (insert sats_incr_bv_iff [of p env A w "[x,y,z]"],simp)


lemma nth_cons : 
  "\<lbrakk>env\<in>list(A) ; env'\<in>list(A) ; x\<in>A \<rbrakk> \<Longrightarrow> 
   nth(length(env),env@(Cons(x,env'))) = x"
  apply (induct_tac env)
  apply (simp+)
  done
    
lemma sats_incr_n_bv2 :
  "\<lbrakk> \<phi>\<in>formula ; a\<in>A ; b\<in>A ; c\<in>A ; d\<in>A ; e\<in>A  \<rbrakk> \<Longrightarrow> 
     sats(A, incr_n_bv(\<phi>, 2, 2), [a, b, c, d, e]) \<longleftrightarrow>
     sats(A,\<phi>,[a,b,e])"
  apply (insert sats_incr_n_bv_iff [of "[a,b]" A "[c,d]" "[e]" \<phi>])
  apply simp
  done

lemma (in M_ZF) replacement_intf : 
      "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>)=2 \<or> arity(\<phi>)=3 \<rbrakk> \<Longrightarrow> 
        sats(M,strong_replacement_ax_fm(\<phi>),[]) \<longleftrightarrow> 
       (\<forall>a\<in>M. strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,[x,y,a])))"
  by (simp add: strong_replacement_ax_fm_def strong_replacement_def 
                 univalent_fm_def univalent_def sats_incr_bv3_iff
                 sats_incr_bv0_iff sats_swap_0_1 sats_incr_bv1_iff sats_incr_n_bv2)
                  
    
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

    
lemma (in M_ZF) funspace_succ_rep_intf : 
  "sats(M,strong_replacement_ax_fm(funspace_succ_fm),[])
  \<longleftrightarrow>
  (\<forall>n\<in>M. strong_replacement(##M,
          \<lambda>p z. \<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M.
                pair(##M,f,b,p) & pair(##M,n,b,nb) & is_cons(##M,nb,f,cnbf) &
                upair(##M,cnbf,cnbf,z)))"
  apply (simp add: replacement_intf)
  apply (simp add: funspace_succ_fm_def strong_replacement_def univalent_def) 
  done
    
lemmas (in M_ZF) M_basic_sep_instances = 
                inter_sep_intf diff_sep_intf cartprod_sep_intf
                image_sep_intf converse_sep_intf restrict_sep_intf
                pred_sep_intf memrel_sep_intf comp_sep_intf is_recfun_sep_intf
    

lemma (in M_ZF) interface_M_basic : 
  "M_basic_no_repl(##M)"
  apply (insert trans_M M_model_ZF M_nempty)
  apply (rule M_basic_no_repl.intro,rule intf_M_trivial)
  apply (insert M_basic_sep_instances funspace_succ_rep_intf)
  apply (rule M_basic_no_repl_axioms.intro)
  apply (simp_all add: sep_spec repl_spec)
  done

end