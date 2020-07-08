section\<open>Relative, Cardinal Arithmetic Using AC\<close>

theory Cardinal_AC_Relative 
  imports 
    Interface
    CardinalArith_Relative 
begin

context M_ordertype
begin

lemma surj_imp_well_ord_M:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
    and
  types: "M(A)" "M(r)" "M(h)" "M(B)"
  shows "\<exists>s[M]. well_ord(B,s)"
  sorry

end (* M_ordertype *)

locale M_choice = M_ordertype +
  assumes
  choice_ax: "choice_ax(M)"
begin

lemma choice_ax_well_ord: "M(S) \<Longrightarrow> \<exists>r[M]. well_ord(S,r)"
  using choice_ax well_ord_Memrel[THEN surj_imp_well_ord_M]
  unfolding choice_ax_def by auto

end (* M_choice *)

locale M_cardinals_choice = M_cardinal_arith + M_choice
begin

subsection\<open>Strengthened Forms of Existing Theorems on Cardinals\<close>

lemma cardinal_rel_eqpoll_rel: "M(A) \<Longrightarrow> |A|r \<approx>r A"
apply (rule choice_ax_well_ord [THEN rexE])
apply (auto intro:well_ord_cardinal_rel_eqpoll_rel)
done

lemmas cardinal_rel_idem = cardinal_rel_eqpoll_rel [THEN cardinal_rel_cong, simp]

lemma cardinal_rel_eqE: "|X|r = |Y|r ==> M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<approx>r Y"
apply (rule choice_ax_well_ord [THEN rexE], assumption)
   apply (rule choice_ax_well_ord [THEN rexE, of Y], assumption)
    apply (rule well_ord_cardinal_rel_eqE, assumption+)
done

lemma cardinal_rel_eqpoll_rel_iff: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> |X|r = |Y|r \<longleftrightarrow> X \<approx>r Y"
by (blast intro: cardinal_rel_cong cardinal_rel_eqE)

lemma cardinal_rel_disjoint_Un:
     "[| |A|r=|B|r;  |C|r=|D|r;  A \<inter> C = 0;  B \<inter> D = 0; M(A); M(B); M(C); M(D)|]
      ==> |A \<union> C|r = |B \<union> D|r"
by (simp add: cardinal_rel_eqpoll_rel_iff eqpoll_rel_disjoint_Un)

lemma lepoll_rel_imp_Card_rel_le: "A \<lesssim>r B ==> M(A) \<Longrightarrow> M(B) \<Longrightarrow> |A|r \<le> |B|r"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (erule well_ord_lepoll_rel_imp_Card_rel_le, assumption+)
  done

lemma cadd_rel_assoc: "\<lbrakk>M(i); M(j); M(k)\<rbrakk> \<Longrightarrow> (i \<oplus>r j) \<oplus>r k = i \<oplus>r (j \<oplus>r k)"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
    apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
     apply (rule well_ord_cadd_rel_assoc, assumption+)
done

lemma cmult_rel_assoc: "\<lbrakk>M(i); M(j); M(k)\<rbrakk> \<Longrightarrow> (i \<otimes>r j) \<otimes>r k = i \<otimes>r (j \<otimes>r k)"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
    apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
     apply (rule well_ord_cmult_rel_assoc, assumption+)
  done

lemma cadd_cmult_distrib: "\<lbrakk>M(i); M(j); M(k)\<rbrakk> \<Longrightarrow> (i \<oplus>r j) \<otimes>r k = (i \<otimes>r k) \<oplus>r (j \<otimes>r k)"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
    apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
     apply (rule well_ord_cadd_cmult_distrib, assumption+)
  done

(*
lemma InfCard_rel_square_eq: "InfCard_r(|A|r) \<Longrightarrow> M(A) \<Longrightarrow> A\<times>A \<approx>r A"
apply (rule choice_ax_well_ord [THEN rexE])
apply (erule well_ord_InfCard_rel_square_eq, assumption)
done

*)

subsection \<open>The relationship between cardinality and le-pollence\<close>

lemma Card_rel_le_imp_lepoll_rel:
  assumes "|A|r \<le> |B|r"
    and types: "M(A)" "M(B)"
  shows "A \<lesssim>r B"
proof -
  have "A \<approx>r |A|r" 
    by (rule cardinal_rel_eqpoll_rel [THEN eqpoll_rel_sym], simp_all add:types)
  also have "... \<lesssim>r |B|r"
    by (rule le_imp_subset [THEN subset_imp_lepoll_rel]) (rule assms, simp_all add:types)
  also have "... \<approx>r B" 
    by (rule cardinal_rel_eqpoll_rel, simp_all add:types)
  finally show ?thesis by (simp_all add:types)
qed

lemma le_Card_rel_iff: "Card_rel(K) ==> M(K) \<Longrightarrow> M(A) \<Longrightarrow> |A|r \<le> K \<longleftrightarrow> A \<lesssim>r K"
apply (erule Card_rel_cardinal_rel_eq [THEN subst], assumption, rule iffI,
       erule Card_rel_le_imp_lepoll_rel, assumption+)
apply (erule lepoll_rel_imp_Card_rel_le, assumption+)
done

lemma cardinal_rel_0_iff_0 [simp]: "M(A) \<Longrightarrow> |A|r = 0 \<longleftrightarrow> A = 0"
  using cardinal_rel_0 eqpoll_rel_0_iff [THEN iffD1] 
    cardinal_rel_eqpoll_rel_iff [THEN iffD1, OF _ nonempty]
  by auto

lemma cardinal_rel_lt_iff_lesspoll_rel:
  assumes i: "Ord(i)" and
    types: "M(i)" "M(A)" 
  shows "i < |A|r \<longleftrightarrow> i \<prec>r A"
proof
  assume "i < |A|r"
  hence  "i \<prec>r |A|r" 
    by (blast intro: lt_Card_rel_imp_lesspoll_rel types) 
  also have "...  \<approx>r A" 
    by (rule cardinal_rel_eqpoll_rel) (simp_all add:types)
  finally show "i \<prec>r A" by (simp_all add:types)
next
  assume "i \<prec>r A"
  also have "...  \<approx>r |A|r" 
    by (blast intro: cardinal_rel_eqpoll_rel eqpoll_rel_sym types) 
  finally have "i \<prec>r |A|r" by (simp_all add:types)
  thus  "i < |A|r" using i types
    by (force intro: cardinal_rel_lt_imp_lt lesspoll_rel_cardinal_rel_lt)
qed

lemma cardinal_rel_le_imp_lepoll_rel: " i \<le> |A|r ==> M(i) \<Longrightarrow> M(A) \<Longrightarrow>i \<lesssim>r A"
  by (blast intro: lt_Ord Card_rel_le_imp_lepoll_rel Ord_cardinal_rel_le le_trans)

(*

subsection\<open>Other Applications of AC\<close>

lemma surj_implies_inj:
  assumes f: "f \<in> surj(X,Y)" and
    types: "M(f)" "M(X)" "M(Y)"
  shows "\<exists>g. g \<in> inj(Y,X)"
proof -
  from f AC_Pi [of Y "%y. f-``{y}"]
  obtain z where z: "z \<in> (\<Prod>y\<in>Y. f -`` {y})"  
    by (auto simp add: surj_def) (fast dest: apply_Pair)
  show ?thesis
    proof
      show "z \<in> inj(Y, X)" using z surj_is_fun [OF f]
        by (blast dest: apply_type Pi_memberD
                  intro: apply_equality Pi_type f_imp_injective)
    qed
qed

text\<open>Kunen's Lemma 10.20\<close>
lemma surj_implies_cardinal_rel_le: 
  assumes f: "f \<in> surj(X,Y)" shows "|Y|r \<le> |X|r"
proof (rule lepoll_rel_imp_Card_rel_le)
  from f [THEN surj_implies_inj] obtain g where "g \<in> inj(Y,X)" ..
  thus "Y \<lesssim>r X"
    by (auto simp add: lepoll_rel_def)
qed

text\<open>Kunen's Lemma 10.21\<close>
lemma cardinal_UN_le:
  assumes K: "InfCard_r(K)" 
    and types: "M(K)" "M(\<Union>i\<in>K. X(i))"
      "\<And>f. M(f) \<Longrightarrow> M(\<lambda>x\<in>(\<Union>x\<in>K. X(x)). \<langle>\<mu> i. x \<in> X(i), f ` (\<mu> i. x \<in> X(i)) ` x\<rangle>)"
  shows "(\<And>i. i\<in>K \<Longrightarrow> M(X(i)) \<and> |X(i)|r \<le> K) \<Longrightarrow> |\<Union>i\<in>K. X(i)|r \<le> K"
proof (simp add: K InfCard_rel_is_Card_rel le_Card_rel_iff types)
  have "i\<in>K \<Longrightarrow> M(i)" for i
    using transM[OF _ \<open>M(K)\<close>] by simp
  have [intro]: "Ord(K)" by (blast intro: InfCard_rel_is_Card_rel Card_rel_is_Ord K types) 
  assume "\<And>i. i\<in>K \<Longrightarrow> M(X(i)) \<and> X(i) \<lesssim>r K"
  moreover from this
  have "\<And>i. i\<in>K \<Longrightarrow> \<exists>f[M]. f \<in> inj_rel(X(i), K)" by (simp add: types def_lepoll_rel) 
  moreover from \<open>\<And>i. i\<in>K \<Longrightarrow> M(X(i)) \<and> X(i) \<lesssim>r K\<close>
  have "\<And>i. i\<in>K \<Longrightarrow> M(inj_rel(X(i), K))"
    by (auto simp add: types)
  ultimately
  obtain f where f: "f \<in> (\<Prod>i\<in>K. inj_rel(X(i), K))" "M(f)"
    using AC_Pi_rel[OF _ \<open>M(K)\<close>, of "\<lambda>i. inj_rel(X(i), K)"] by force
  { fix z
    assume z: "z \<in> (\<Union>i\<in>K. X(i))"
    then obtain i where i: "i \<in> K" "Ord(i)" "z \<in> X(i)"
      by (blast intro: Ord_in_Ord [of K]) 
    hence "(\<mu> i. z \<in> X(i)) \<le> i" by (fast intro: Least_le) 
    hence "(\<mu> i. z \<in> X(i)) < K" by (best intro: lt_trans1 ltI i) 
    hence "(\<mu> i. z \<in> X(i)) \<in> K" and "z \<in> X(\<mu> i. z \<in> X(i))"  
      by (auto intro: LeastI ltD i) 
  } note mems = this
  have "(\<Union>i\<in>K. X(i)) \<lesssim>r K \<times> K" 
    proof (simp add:types def_lepoll_rel)
      show "\<exists>f[M]. f \<in> inj(\<Union>RepFun(K, X), K \<times> K)"
        apply (rule rexI)
        apply (rule_tac c = "\<lambda>z. \<langle>\<mu> i. z \<in> X(i), f ` (\<mu> i. z \<in> X(i)) ` z\<rangle>"
                    and d = "\<lambda>\<langle>i,j\<rangle>. converse (f`i) ` j" in lam_injective) 
          apply (force intro: f inj_is_fun mems apply_type Perm.left_inverse .)+
        apply (simp add:types \<open>M(f)\<close>)
        done
    qed
  also have "... \<approx>r K" 
    by (simp add: K InfCard_rel_square_eq InfCard_rel_is_Card_rel
        Card_rel_cardinal_rel_eq types)
  finally show "(\<Union>i\<in>K. X(i)) \<lesssim>r K" by (simp_all add:types)
qed

text\<open>The same again, using \<^term>\<open>csucc\<close>\<close>
lemma cardinal_UN_lt_csucc:
     "[| InfCard(K);  \<And>i. i\<in>K \<Longrightarrow> |X(i)| < csucc(K) |]
      ==> |\<Union>i\<in>K. X(i)| < csucc(K)"
by (simp add: Card_lt_csucc_iff cardinal_UN_le InfCard_is_Card Card_cardinal)

text\<open>The same again, for a union of ordinals.  In use, j(i) is a bit like rank(i),
  the least ordinal j such that i:Vfrom(A,j).\<close>
lemma cardinal_UN_Ord_lt_csucc:
     "[| InfCard(K);  \<And>i. i\<in>K \<Longrightarrow> j(i) < csucc(K) |]
      ==> (\<Union>i\<in>K. j(i)) < csucc(K)"
apply (rule cardinal_UN_lt_csucc [THEN Card_lt_imp_lt], assumption)
apply (blast intro: Ord_cardinal_le [THEN lt_trans1] elim: ltE)
apply (blast intro!: Ord_UN elim: ltE)
apply (erule InfCard_is_Card [THEN Card_is_Ord, THEN Card_csucc])
done


subsection\<open>The Main Result for Infinite-Branching Datatypes\<close>

text\<open>As above, but the index set need not be a cardinal. Work
backwards along the injection from \<^term>\<open>W\<close> into \<^term>\<open>K\<close>, given
that \<^term>\<open>W\<noteq>0\<close>.\<close>

lemma inj_UN_subset:
  assumes f: "f \<in> inj(A,B)" and a: "a \<in> A"
  shows "(\<Union>x\<in>A. C(x)) \<subseteq> (\<Union>y\<in>B. C(if y \<in> range(f) then converse(f)`y else a))"
proof (rule UN_least)
  fix x
  assume x: "x \<in> A"
  hence fx: "f ` x \<in> B" by (blast intro: f inj_is_fun [THEN apply_type])
  have "C(x) \<subseteq> C(if f ` x \<in> range(f) then converse(f) ` (f ` x) else a)" 
    using f x by (simp add: inj_is_fun [THEN apply_rangeI])
  also have "... \<subseteq> (\<Union>y\<in>B. C(if y \<in> range(f) then converse(f) ` y else a))"
    by (rule UN_upper [OF fx]) 
  finally show "C(x) \<subseteq> (\<Union>y\<in>B. C(if y \<in> range(f) then converse(f)`y else a))" .
qed

theorem le_UN_Ord_lt_csucc:
  assumes IK: "InfCard(K)" and WK: "|W| \<le> K" and j: "\<And>w. w\<in>W \<Longrightarrow> j(w) < csucc(K)"
  shows "(\<Union>w\<in>W. j(w)) < csucc(K)"
proof -
  have CK: "Card(K)" 
    by (simp add: InfCard_is_Card IK)
  then obtain f where f: "f \<in> inj(W, K)" using WK
    by(auto simp add: le_Card_iff lepoll_def)
  have OU: "Ord(\<Union>w\<in>W. j(w))" using j
    by (blast elim: ltE)
  note lt_subset_trans [OF _ _ OU, trans]
  show ?thesis
    proof (cases "W=0")
      case True  \<comment> \<open>solve the easy 0 case\<close>
      thus ?thesis by (simp add: CK Card_is_Ord Card_csucc Ord_0_lt_csucc)
    next
      case False
        then obtain x where x: "x \<in> W" by blast
        have "(\<Union>x\<in>W. j(x)) \<subseteq> (\<Union>k\<in>K. j(if k \<in> range(f) then converse(f) ` k else x))"
          by (rule inj_UN_subset [OF f x]) 
        also have "... < csucc(K)" using IK
          proof (rule cardinal_UN_Ord_lt_csucc)
            fix k
            assume "k \<in> K"
            thus "j(if k \<in> range(f) then converse(f) ` k else x) < csucc(K)" using f x j
              by (simp add: inj_converse_fun [THEN apply_type])
          qed
        finally show ?thesis .
    qed
qed
*)

end (* M_cardinals_choice *)

end