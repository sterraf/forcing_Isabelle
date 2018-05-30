(* Interface between internalized axiom formulas and 
   ZF axioms *)
theory Interface imports ZFCAxioms_formula Relative_no_repl Names WF_absolute_no_repl begin

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

(* Infinite *)
lemma infinite_intf : 
  "sats(A,infinity_ax_fm,[]) \<longleftrightarrow>
   (\<exists>I\<in>A. (\<exists>z\<in>A. empty(##A,z) \<and> z\<in>I) \<and>  (\<forall>y\<in>A. y\<in>I \<longrightarrow> (\<exists>sy\<in>A. successor(##A,y,sy) \<and> sy\<in>I)))"
  by (simp add: infinity_ax_fm_def)
  
(* Emptyset  *)
lemma empty_intf :
  "sats(A,infinity_ax_fm,[])
  \<longrightarrow>
  (\<exists>z\<in>A . empty(##A,z))"
  by (auto simp add: infinity_ax_fm_def empty_def)

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

begin  (*************** CONTEXT: M_ZF  ************************)
    
lemma zero_in_M:         "0 \<in> M"
proof -
  have 
        "sats(M,infinity_ax_fm,[])"
    by (rule satT_sats, rule M_model_ZF, simp add: ZFTh_def ZF_fin_def)
  then have
        "(\<exists>z\<in>M . empty(##M,z))"
    by (simp add: empty_intf)      
  then obtain z where
        zm: "empty(##M,z)"  "z\<in>M"
    by auto
  with trans_M have "z=0"
    by (simp  add: empty_def, blast intro: Transset_intf )
  with zm show ?thesis 
      by simp
  qed
  
lemma intf_M_trivial :
  "M_trivial_no_repl(##M)"
  apply (insert trans_M M_model_ZF zero_in_M)
  apply (rule M_trivial_no_repl.intro)
  apply (simp,rule Transset_intf,assumption+)
  apply (simp_all add: pairing_intf[symmetric] union_intf[symmetric] 
                       power_intf[symmetric] ZFTh_def ZF_fin_def satT_sats)
done
end
  
sublocale M_ZF \<subseteq> M_trivial_no_repl "##M" 
  by (rule intf_M_trivial)
  
(* interpretation Mtriv : M_trivial_no_repl "##M" by (rule intf_M_trivial) *)


context M_ZF
begin
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
  with asms and pair_in_M_iff show "P(A,B)" 
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
  from asms and pair_in_M_iff have
              "<B,C> \<in> M"
    by simp
  with 1 and tupling_simp2_rule have
              "\<forall>A\<in>M. \<langle>A, B, C\<rangle> \<in> M \<and> Q(A, B, C) \<longrightarrow> P(A, B, C)"
    by simp
  with asms and pair_in_M_iff show "P(A,B,C)" by simp
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
    
          
lemma (in M_ZF) separation_intf : 
      "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>)=1 \<or> arity(\<phi>)=2 \<rbrakk> \<Longrightarrow> 
        sats(M,separation_ax_fm(\<phi>),[]) \<longleftrightarrow> 
       (\<forall>a\<in>M. separation(##M,\<lambda>x. sats(M,\<phi>,[x,a])))"
  by (simp add: separation_ax_fm_def separation_def sats_incr_bv1_iff)
    
    
lemma (in M_ZF) separation_intf2:
    "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>)=1 \<or> arity(\<phi>)=2 ; a\<in>M \<rbrakk> \<Longrightarrow>
      separation(##M,\<lambda>x. sats(M,\<phi>,[x,a]))"
  apply (rule_tac A=M and P="\<lambda>b. separation(##M,\<lambda>x. sats(M,\<phi>,[x,b]))" in bspec)
   apply (rule iffD1,rule separation_intf)
  apply (insert M_model_ZF)
  apply (simp_all add: sep_spec)
done  

lemma arity_inter_fm :
  "arity(Forall(Implies(Member(0,2),Member(1,0)))) = 2"
  by (simp add: Un_commute nat_union_abs1)
    
(* Instances of separation for interface with M_basic *)
lemma (in M_ZF) inter_sep_intf :
  "\<lbrakk> A\<in>M \<rbrakk> \<Longrightarrow> separation(##M,\<lambda>x . \<forall>y\<in>M . y\<in>A \<longrightarrow> x\<in>y)"
  apply (rule iffD1)
   prefer 2
   apply (rule_tac \<phi>="Forall(Implies(Member(0,2),Member(1,0)))" in separation_intf2)
   apply (simp,rule disjI2,rule arity_inter_fm,simp)
   apply (simp add: separation_def)
done

lemma arity_diff_fm: 
  "arity(Neg(Member(0,1))) = 2"
  by (simp add: nat_union_abs1)
    
lemma (in M_ZF) diff_sep_intf :
    "\<lbrakk> B\<in>M \<rbrakk> \<Longrightarrow> separation(##M,\<lambda>x . x\<notin>B)"
  apply (rule iffD1)
   prefer 2
   apply (rule_tac \<phi>="Neg(Member(0,1))" in separation_intf2)
   apply (simp,rule disjI2,rule arity_diff_fm,simp)
  apply (simp add: separation_def)
  done
    
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
    
lemma arity_cartprod_fm [simp] : "arity(cartprod_sep_fm) = 3" 
  by (simp add: cartprod_sep_fm_def pair_fm_def upair_fm_def 
                Un_commute nat_union_abs1)

lemma (in M_ZF) cartprod_sep_intf' :
  "sats(M,separation_ax_fm(tupling_fm_2p(cartprod_sep_fm)),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. \<forall>B\<in>M. separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A \<and> (\<exists>y\<in>M. y\<in>B \<and> pair(##M,x,y,z))))"
  apply (rule iff_trans)
   apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp+)
  apply (rule iff_trans) 
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2p_def cartprod_sep_fm_def del: pair_abs)
  done

lemma (in M_ZF) cartprod_sep_intf :
  "\<lbrakk> A\<in>M ; B\<in>M \<rbrakk> \<Longrightarrow> 
    separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A \<and> (\<exists>y\<in>M. y\<in>B \<and> pair(##M,x,y,z)))"
  apply (rule_tac x=B and A=M in bspec,rule_tac x=A and A=M in bspec)
    apply (rule iffD1,rule cartprod_sep_intf')
  apply (insert M_model_ZF)
  apply (rule sep_spec,simp+,rule disjI2,rule arity_tup2p,simp+)
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
               

lemma (in M_ZF) image_sep_intf' :
  "sats(M,separation_ax_fm(tupling_fm_2p(image_sep_fm)),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. \<forall>r\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M. x\<in>A & pair(##M,x,y,p))))"
  apply (rule iff_trans)
   apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp,simp)
  apply (rule iff_trans)
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2p_def image_sep_fm_def del: pair_abs)
  done
    
lemma (in M_ZF) image_sep_intf :
  "\<lbrakk> A\<in>M ; r\<in>M \<rbrakk> \<Longrightarrow> 
    separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M. x\<in>A & pair(##M,x,y,p)))"
  apply (rule_tac x=r and A=M in bspec,rule_tac x=A and A=M in bspec)
    apply (rule iffD1,rule image_sep_intf')
  apply (insert M_model_ZF)
  apply (rule sep_spec,simp+,rule disjI2,rule arity_tup2p,simp+)
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
    
lemma (in M_ZF) converse_sep_intf' : 
  "sats(M,separation_ax_fm(converse_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. separation(##M,\<lambda>z. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M.
                      \<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,z))))"
  by (simp add: separation_def separation_intf separation_ax_fm_def 
                     sats_incr_bv1_iff converse_sep_fm_def del: pair_abs)
  
lemma (in M_ZF) converse_sep_intf :
"\<lbrakk> r\<in>M \<rbrakk> \<Longrightarrow> 
    separation(##M,\<lambda>z. \<exists>p\<in>M. p\<in>r & (\<exists>x\<in>M.
                      \<exists>y\<in>M. pair(##M,x,y,p) & pair(##M,y,x,z)))"
  apply (rule_tac x=r and A=M in bspec)
    apply (rule iffD1,rule converse_sep_intf')
  apply (insert M_model_ZF)
  apply (rule sep_spec,simp+)
done
                   
definition
  restrict_sep_fm :: "i" where
  "restrict_sep_fm == Exists(And(Member(0,2),Exists(pair_fm(1,0,2))))"

lemma restrict_sep_fm_type [TC] : "restrict_sep_fm \<in> formula"
  by (simp add: restrict_sep_fm_def)
    
lemma [simp] : "arity(restrict_sep_fm) = 2"
  by (simp add: restrict_sep_fm_def pair_fm_def upair_fm_def 
                Un_commute nat_union_abs1)

lemma (in M_ZF) restrict_sep_intf' :
  "sats(M,separation_ax_fm(restrict_sep_fm),[])
  \<longleftrightarrow>
  (\<forall>A\<in>M. separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A & (\<exists>y\<in>M. pair(##M,x,y,z))))"
  by (simp add: separation_def separation_intf separation_ax_fm_def 
                     sats_incr_bv1_iff restrict_sep_fm_def)

lemma (in M_ZF) restrict_sep_intf :
  "\<lbrakk> A\<in>M \<rbrakk> \<Longrightarrow> 
    separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A & (\<exists>y\<in>M. pair(##M,x,y,z)))"
  apply (rule_tac x=A and A=M in bspec)
    apply (rule iffD1,rule restrict_sep_intf')
  apply (insert M_model_ZF)
  apply (rule sep_spec,simp+)
done
                   
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

lemma (in M_ZF) comp_sep_intf' :
  "sats(M,separation_ax_fm(tupling_fm_2p(comp_sep_fm)),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>s\<in>M. 
    separation(##M,\<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
              pair(##M,x,z,xz) & pair(##M,x,y,xy) & pair(##M,y,z,yz) &
              xy\<in>s & yz\<in>r))"
  apply (rule iff_trans)
   apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp,simp)
  apply (rule iff_trans)
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2p_def comp_sep_fm_def del: pair_abs)
  done

lemma (in M_ZF) comp_sep_intf :
    "\<lbrakk> r\<in>M ; s\<in>M \<rbrakk> \<Longrightarrow> 
    separation(##M,\<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
              pair(##M,x,z,xz) & pair(##M,x,y,xy) & pair(##M,y,z,yz) &
              xy\<in>s & yz\<in>r)"
  apply (rule_tac x=s and A=M in bspec,rule_tac x=r and A=M in bspec)
    apply (rule iffD1,rule comp_sep_intf')
  apply (insert M_model_ZF)
  apply (rule sep_spec,simp+,rule disjI2,rule arity_tup2p,simp+)
done
    
lemma arity_pred_fm [simp] : 
  "arity(Exists(And(Member(0,2),pair_fm(3,1,0)))) = 3"
  by (simp add: pair_fm_def upair_fm_def Un_commute nat_union_abs1)
    
lemma (in M_ZF) pred_sep_intf' :
  "sats(M,separation_ax_fm(
       tupling_fm_2p(Exists(And(Member(0,2),pair_fm(3,1,0))))),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>x\<in>M. separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & pair(##M,y,x,p)))"
   apply (rule iff_trans)
   apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp,simp)
   apply (simp add: pair_fm_def upair_fm_def Un_commute nat_union_abs1)
  apply (rule iff_trans)
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2p_def del: pair_abs)
  done

lemma (in M_ZF) pred_sep_intf :
    "\<lbrakk> r\<in>M ; x\<in>M \<rbrakk> \<Longrightarrow> separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>r & pair(##M,y,x,p))"
  apply (rule_tac x=x and A=M in bspec,rule_tac x=r and A=M in bspec)
  apply (rule iffD1,rule pred_sep_intf')
  apply (insert M_model_ZF)
  apply (rule sep_spec,simp+,rule disjI2,rule arity_tup2p,simp,rule arity_pred_fm,simp+)
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

lemma (in M_ZF) memrel_sep_intf' :
  "sats(M,separation_ax_fm(memrel_fm),[])
  \<longleftrightarrow>
  separation(##M, \<lambda>z. \<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) & x \<in> y)"
  apply (simp add: separation_def separation_intf sats_memrel)
  apply (insert zero_in_M,auto)
  done
    
lemma (in M_ZF) memrel_sep_intf :
  "separation(##M, \<lambda>z. \<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) & x \<in> y)"
  apply (rule iffD1,rule memrel_sep_intf')
  apply (insert M_model_ZF,simp add: sep_spec)
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
              
              
lemma (in M_ZF) is_recfun_sep_intf' :
  "sats(M,separation_ax_fm(tupling_fm_5p(is_recfun_sep_fm)),[])
  \<longleftrightarrow>
  (\<forall>r\<in>M. \<forall>f\<in>M. \<forall>g\<in>M. \<forall>a\<in>M. \<forall>b\<in>M. 
    separation(##M,\<lambda>x. \<exists>xa\<in>M. \<exists>xb\<in>M.
                    pair(##M,x,a,xa) & xa \<in> r & pair(##M,x,b,xb) & xb \<in> r &
                    (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M,f,x,fx) & fun_apply(##M,g,x,gx) &
                                     fx \<noteq> gx)))"
  apply (rule iff_trans)
  apply (rule separation_intf,simp,rule disjI2,rule arity_tup5p,simp,simp)
  apply (rule iff_trans)
  prefer 2
   apply (rule tupling_sep_5p_rel2)
  apply (simp add: separation_def tupling_fm_5p_def is_recfun_sep_fm_def del: pair_abs)
    done

lemma (in M_ZF) is_recfun_sep_intf :
  "\<lbrakk> r\<in>M ; f\<in>M ; g\<in>M ; a\<in>M ; b\<in>M \<rbrakk> \<Longrightarrow> 
      separation(##M,\<lambda>x. \<exists>xa\<in>M. \<exists>xb\<in>M.
                    pair(##M,x,a,xa) & xa \<in> r & pair(##M,x,b,xb) & xb \<in> r &
                    (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M,f,x,fx) & fun_apply(##M,g,x,gx) &
                                     fx \<noteq> gx))"
  apply (rule_tac x=b and A=M in bspec,rule_tac x=a and A=M in bspec,rule_tac x=g and A=M in bspec)
  apply (rule_tac x=f and A=M in bspec,rule_tac x=r and A=M in bspec)
  apply (rule iffD1,rule is_recfun_sep_intf')
  apply (insert M_model_ZF)
  apply (rule sep_spec,simp+,rule disjI2,rule arity_tup5p,simp+)
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

    
lemma (in M_ZF) funspace_succ_rep_intf' : 
  "sats(M,strong_replacement_ax_fm(funspace_succ_fm),[])
  \<longleftrightarrow>
  (\<forall>n\<in>M. strong_replacement(##M,
          \<lambda>p z. \<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M.
                pair(##M,f,b,p) & pair(##M,n,b,nb) & is_cons(##M,nb,f,cnbf) &
                upair(##M,cnbf,cnbf,z)))"
  apply (simp add: replacement_intf del: pair_abs)
  apply (simp add: funspace_succ_fm_def strong_replacement_def univalent_def del: pair_abs)
  done
    
lemma (in M_ZF) funspace_succ_rep_intf :
    "\<lbrakk> n\<in>M \<rbrakk> \<Longrightarrow> 
     strong_replacement(##M,
          \<lambda>p z. \<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M.
                pair(##M,f,b,p) & pair(##M,n,b,nb) & is_cons(##M,nb,f,cnbf) &
                upair(##M,cnbf,cnbf,z))"
  apply (rule_tac x=n and A=M in bspec)
   apply (rule iffD1,rule funspace_succ_rep_intf')
  apply (insert M_model_ZF)
   apply (rule repl_spec,simp+)
done
    
lemmas (in M_ZF) M_basic_sep_instances = 
                inter_sep_intf diff_sep_intf cartprod_sep_intf
                image_sep_intf converse_sep_intf restrict_sep_intf
                pred_sep_intf memrel_sep_intf comp_sep_intf is_recfun_sep_intf

                
context M_ZF
begin 
lemma interface_M_basic : 
  "M_basic_no_repl(##M)"
  apply (insert trans_M M_model_ZF zero_in_M)
  apply (rule M_basic_no_repl.intro,rule intf_M_trivial)
  apply (rule M_basic_no_repl_axioms.intro)
  apply (insert M_basic_sep_instances funspace_succ_rep_intf)
  apply (simp_all)
done

end (* End context M_ZF *)

sublocale M_ZF \<subseteq> M_basic_no_repl "##M" by (rule interface_M_basic)
  
(* interface with M_trancl *)
    
definition 
  rtran_closure_mem_fm :: "[i,i,i] \<Rightarrow> i" where
  "rtran_closure_mem_fm(A,r,p) == 
    Exists(Exists(Exists(
      And(omega_fm(2),And(Member(1,2),And(succ_fm(1,0),
          Exists(And(typed_function_fm(1,4#+A,0),
                 And(Exists(Exists(Exists(And(pair_fm(2,1,7#+p),And(empty_fm(0),
                                          And(fun_apply_fm(3,0,2),fun_apply_fm(3,5,1))))))),
            Forall(Implies(Member(0,3),Exists(Exists(Exists(Exists(
                And(fun_apply_fm(5,4,3),And(succ_fm(4,2),And(fun_apply_fm(5,2,1),
                And(pair_fm(3,1,0),Member(0,9#+r))))))))))))))))))))"

lemma rtran_closure_mem_fm_type [TC] :
  "\<lbrakk> A\<in>nat ; r\<in>nat ; p\<in>nat \<rbrakk> \<Longrightarrow> rtran_closure_mem_fm(A,r,p) \<in> formula" 
  by (simp add: rtran_closure_mem_fm_def)
  
lemma arity_rtran_closure_mem_fm0 [simp] : 
  "arity(rtran_closure_mem_fm(0,1,2)) = 3" 
  by (simp add: rtran_closure_mem_fm_def succ_fm_def omega_fm_def limit_ordinal_fm_def
                empty_fm_def is_cons_fm_def typed_function_fm_def fun_apply_fm_def
                cons_fm_def image_fm_def upair_fm_def big_union_fm_def union_fm_def pair_fm_def
                relation_fm_def domain_fm_def function_fm_def Un_commute nat_union_abs1)

lemma sats_rtran_closure_mem_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, rtran_closure_mem_fm(x,y,z), env) \<longleftrightarrow>
        rtran_closure_mem(##A, nth(x,env), nth(y,env), nth(z,env))"
  by (simp add: rtran_closure_mem_fm_def rtran_closure_mem_def)

(*"is_domain(M,r,z) == \<forall>x[M]. x \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r & (\<exists>y[M]. pair(M,x,y,w)))"*)
definition 
  is_domain_fm :: "[i,i] \<Rightarrow> i" where
  "is_domain_fm(r,z) == Forall(Iff(Member(0,succ(z)),
                          Exists(And(Member(0,succ(succ(r))),
                                     Exists(pair_fm(2,0,1))))))"
  
lemma is_domain_type [TC]:
  "\<lbrakk> r\<in>nat ; z\<in>nat \<rbrakk> \<Longrightarrow> is_domain_fm(r,z) \<in> formula"
  by (simp add: is_domain_fm_def)
    
lemma sats_is_domain_fm [simp] :
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, is_domain_fm(x,y), env) \<longleftrightarrow>
        is_domain(##A, nth(x,env), nth(y,env))"
  by (simp add: is_domain_fm_def is_domain_def)
    
(*"is_range(M,r,z) == \<forall>y[M]. y \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r & (\<exists>x[M]. pair(M,x,y,w)))"*)
definition
  is_range_fm :: "[i,i] \<Rightarrow> i" where
  "is_range_fm(x,y) == Forall(Iff(Member(0,succ(y)),
                              Exists(And(Member(0,succ(succ(x))),
                                     Exists(pair_fm(0,2,1))))))"
  
lemma is_range_type [TC]:
  "\<lbrakk> r\<in>nat ; z\<in>nat \<rbrakk> \<Longrightarrow> is_range_fm(r,z) \<in> formula"
  by (simp add: is_range_fm_def)
    
lemma sats_is_range_fm [simp] :
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, is_range_fm(x,y), env) \<longleftrightarrow>
        is_range(##A, nth(x,env), nth(y,env))"
  by (simp add: is_range_fm_def is_range_def)
  
  
    
(*"is_field(M,r,z) == \<exists>dr[M]. \<exists>rr[M]. is_domain(M,r,dr) & is_range(M,r,rr) & union(M,dr,rr,z)"*)
definition
  is_field_fm :: "[i,i] \<Rightarrow> i" where
  "is_field_fm(r,z) == Exists(Exists(And(is_domain_fm(succ(succ(r)),1),
                                     And(is_range_fm(succ(succ(r)),0),
                                         union_fm(1,0,succ(succ(z)))))))"
    
lemma is_field_type [TC]:
  "\<lbrakk> r\<in>nat ; z\<in>nat \<rbrakk> \<Longrightarrow> is_field_fm(r,z) \<in> formula"
  by (simp add: is_field_fm_def)
    
lemma sats_is_field_fm [simp] :
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, is_field_fm(x,y), env) \<longleftrightarrow>
        is_field(##A, nth(x,env), nth(y,env))"
  by (simp add: is_field_fm_def is_field_def)
    
(*"rtran_closure(M,r,s) == \<forall>A[M]. is_field(M,r,A) \<longrightarrow> 
                                  (\<forall>p[M]. p \<in> s \<longleftrightarrow> rtran_closure_mem(M,A,r,p))"*)
definition
  rtran_closure_fm :: "[i,i] \<Rightarrow> i" where
  "rtran_closure_fm(r,s) == Forall(Implies(is_field_fm(succ(r),0),
                                  Forall(Iff(Member(0,succ(succ(s))),
                                         rtran_closure_mem_fm(1,succ(succ(r)),0)))))"
  
lemma rtran_closure_type [TC]:
  "\<lbrakk> r\<in>nat ; z\<in>nat \<rbrakk> \<Longrightarrow> rtran_closure_fm(r,z) \<in> formula"
  by (simp add: rtran_closure_fm_def)
    
lemma sats_rtran_closure_fm [simp] :
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, rtran_closure_fm(x,y), env) \<longleftrightarrow>
        rtran_closure(##A, nth(x,env), nth(y,env))"
  by (simp add: rtran_closure_fm_def rtran_closure_def)

(*"tran_closure(M,r,t) == \<exists>s[M]. rtran_closure(M,r,s) & composition(M,r,s,t)"*)

definition
  tran_closure_fm :: "[i,i] \<Rightarrow> i" where
  "tran_closure_fm(r,t) == Exists(And(rtran_closure_fm(succ(r),0),
                                      composition_fm(succ(r),0,succ(t))))"

lemma tran_closure_type [TC]:
  "\<lbrakk> r\<in>nat ; t\<in>nat \<rbrakk> \<Longrightarrow> tran_closure_fm(r,t) \<in> formula"
  by (simp add: tran_closure_fm_def)
    
lemma sats_tran_closure_fm [simp] :
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, tran_closure_fm(x,y), env) \<longleftrightarrow>
        tran_closure(##A, nth(x,env), nth(y,env))"
  by (simp add: tran_closure_fm_def tran_closure_def)
  
    
lemma (in M_ZF) rtrancl_sep_intf' :
  "sats(M,separation_ax_fm(tupling_fm_2p(rtran_closure_mem_fm(0,1,2))),[]) \<longleftrightarrow> 
   (\<forall>r\<in>M. \<forall>A\<in>M. separation(##M,rtran_closure_mem(##M,A,r)))"
  apply (rule iff_trans)
  apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp+)
  apply (rule iff_trans)
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2p_def del: pair_abs)
done

lemma (in M_ZF) rtrancl_sep_intf :
    "\<lbrakk> r\<in>M ; A\<in>M \<rbrakk> \<Longrightarrow> separation(##M,rtran_closure_mem(##M,A,r))"
  apply (rule_tac x=A and A=M in bspec,rule_tac x=r and A=M in bspec)
  apply (rule iffD1,rule rtrancl_sep_intf')
  apply (insert M_model_ZF)
  apply (rule sep_spec,simp+,rule disjI2,rule arity_tup2p,simp,rule arity_rtran_closure_mem_fm0,simp+)
done

  
definition
  wf_trancl_fm :: "i" where
  "wf_trancl_fm == Exists(Exists(Exists(And(Member(2,3),
                                        And(pair_fm(2,5,1),
                                        And(tran_closure_fm(4,0),
                                            Member(1,0)))))))"
  
lemma wf_trancl_fm_type [TC] :
  "wf_trancl_fm \<in> formula"
  by (simp add: wf_trancl_fm_def)
    
lemma arity_wf_trancl_fm_type [simp] :
  "arity(wf_trancl_fm) = 3"
  by (simp add: wf_trancl_fm_def pair_fm_def upair_fm_def tran_closure_fm_def 
                rtran_closure_fm_def is_field_fm_def rtran_closure_mem_fm_def fun_apply_fm_def
                image_fm_def empty_fm_def big_union_fm_def composition_fm_def
                is_cons_fm_def union_fm_def is_domain_fm_def is_range_fm_def 
                typed_function_fm_def function_fm_def relation_fm_def omega_fm_def 
                limit_ordinal_fm_def succ_fm_def cons_fm_def domain_fm_def Un_commute nat_union_abs1)

  
lemma (in M_ZF) wf_trancl_sep_intf' :
  "sats(M,separation_ax_fm(tupling_fm_2p(wf_trancl_fm)),[]) \<longleftrightarrow> 
   (\<forall>r\<in>M. \<forall>Z\<in>M. separation (##M, \<lambda>x. 
              \<exists>w\<in>M. \<exists>wx\<in>M. \<exists>rp\<in>M. 
               w \<in> Z & pair(##M,w,x,wx) & tran_closure(##M,r,rp) & wx \<in> rp))"
  apply (rule iff_trans)
  apply (rule separation_intf,simp,rule disjI2,rule arity_tup2p,simp,simp)
  apply (rule iff_trans)
   prefer 2
   apply (rule tupling_sep_2p)
  apply (simp add: separation_def tupling_fm_2p_def wf_trancl_fm_def del: pair_abs)
done

lemma (in M_ZF) wf_trancl_sep_intf :
    "\<lbrakk> r\<in>M ; Z\<in>M \<rbrakk> \<Longrightarrow> separation (##M, \<lambda>x. 
              \<exists>w\<in>M. \<exists>wx\<in>M. \<exists>rp\<in>M. 
               w \<in> Z & pair(##M,w,x,wx) & tran_closure(##M,r,rp) & wx \<in> rp)"
  apply (rule_tac x=Z and A=M in bspec,rule_tac x=r and A=M in bspec)
  apply (rule iffD1,rule wf_trancl_sep_intf')
  apply (insert M_model_ZF)
  apply (rule sep_spec,simp+,rule disjI2,rule arity_tup2p,simp,rule arity_wf_trancl_fm_type,simp+)
done

(* nat \<in> M *)
     
lemma (in M_ZF) inf_zero:
  "\<lbrakk> I\<in>M ; z\<in>M ; empty(##M, z) ; z\<in>I \<rbrakk> \<Longrightarrow> 0 \<in> I"
  by (simp)
  
lemma (in M_ZF) inf_suc:
  "\<lbrakk> I\<in>M ; y\<in>M ; sy\<in>M ; y\<in>I ; successor(##M,y,sy) ; sy\<in>I \<rbrakk> \<Longrightarrow> succ(y) \<in> I" 
  by simp
  
lemma (in M_ZF) inf_abs :
  "\<exists>I\<in>M. 0\<in>I \<and> (\<forall>x\<in>M. x\<in>I \<longrightarrow> succ(x)\<in>I)"
  apply (subgoal_tac "(\<exists>I\<in>M. (\<exists>z\<in>M. empty(##M,z) \<and> z\<in>I) \<and>  (\<forall>y\<in>M. y\<in>I \<longrightarrow> 
                                                            (\<exists>sy\<in>M. successor(##M,y,sy) \<and> sy\<in>I)))")
   prefer 2
   apply (rule infinite_intf[THEN iffD1])
   apply (insert M_model_ZF,rule satT_sats,simp add: ZFTh_def ZF_fin_def,simp)
   apply auto
  done
  
  
lemma (in M_ZF) nat_subset_I' : 
  "\<lbrakk> I\<in>M ; 0\<in>I ; \<And>x. x\<in>I \<Longrightarrow> succ(x)\<in>I \<rbrakk> \<Longrightarrow> nat \<subseteq> I"
  by (rule subsetI,induct_tac x,simp+)
  
lemma (in M_ZF) nat_subset_I :
  "\<exists>I\<in>M. nat \<subseteq> I" 
  apply (insert inf_abs)
  apply (rule bexE,assumption,rename_tac I)  
  apply (rule bexI)
   prefer 2
   apply (assumption)
  apply (rule nat_subset_I',simp+)
  apply (drule conjunct2)
  apply (rule mp,rule_tac x=x in bspec,assumption)
   apply (insert trans_M,rule Transset_intf,simp+)
  done
    
lemma [simp] : "arity(finite_ordinal_fm(0)) = 1"
  by (simp add: finite_ordinal_fm_def limit_ordinal_fm_def empty_fm_def succ_fm_def
                   cons_fm_def union_fm_def upair_fm_def Un_commute nat_union_abs1)
    
lemma (in M_ZF) finite_sep_intf':
  "sats(M,separation_ax_fm(finite_ordinal_fm(0)),[]) \<longleftrightarrow>
  separation(##M,\<lambda>x. x\<in>nat)"
  apply (simp add: separation_def separation_intf)
  apply (insert zero_in_M,auto)
  done
    
lemma (in M_ZF) finite_sep_intf :
  "separation(##M,\<lambda>x. x\<in>nat)"
  apply (rule iffD1,rule finite_sep_intf')
  apply (insert M_model_ZF,simp add: sep_spec)
  done

lemma collect_subset [simp]:
  " A\<subseteq>B \<Longrightarrow> {x \<in> B . x \<in> A} = A" 
  by auto
    
lemma (in M_ZF) nat_in_M:
  "nat \<in> M"
  apply (insert nat_subset_I,rule bexE,assumption,rename_tac I)
  apply (insert finite_sep_intf)
  apply (subgoal_tac "{x\<in>I. x\<in>nat} \<in> M")
   prefer 2
   apply (simp add: setclass_iff[symmetric] del: setclass_iff)
   apply (rule_tac a="{x \<in> I . x \<in> nat}" and b="nat" in subst,simp+)
  done

sublocale M_ZF \<subseteq> M_trancl_no_repl "##M" 
  apply (insert trans_M M_model_ZF zero_in_M)
  apply (rule M_trancl_no_repl.intro,rule interface_M_basic)
  apply (insert rtrancl_sep_intf wf_trancl_sep_intf nat_in_M)
  apply (rule M_trancl_no_repl_axioms.intro)
    apply simp_all
  done
    
end