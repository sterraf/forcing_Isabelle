section\<open>Main definitions of the development\<close>

theory Demonstrations
  imports
    Definitions_Main
begin

(* MOVE THIS to an appropriate place, if it is to stay *)
abbreviation
  dec15  :: i   ("15") where "15 \<equiv> succ(14)"
abbreviation
  dec16  :: i   ("16") where "16 \<equiv> succ(15)"
abbreviation
  dec17  :: i   ("17") where "17 \<equiv> succ(16)"
abbreviation
  dec18  :: i   ("18") where "18 \<equiv> succ(17)"
abbreviation
  dec19  :: i   ("19") where "19 \<equiv> succ(18)"
abbreviation
  dec20  :: i   ("20") where "20 \<equiv> succ(19)"
abbreviation
  dec21  :: i   ("21") where "21 \<equiv> succ(20)"
abbreviation
  dec22  :: i   ("22") where "22 \<equiv> succ(21)"
abbreviation
  dec23  :: i   ("23") where "23 \<equiv> succ(22)"
abbreviation
  dec24  :: i   ("24") where "24 \<equiv> succ(23)"
abbreviation
  dec25  :: i   ("25") where "25 \<equiv> succ(24)"
abbreviation
  dec26  :: i   ("26") where "26 \<equiv> succ(25)"
abbreviation
  dec27  :: i   ("27") where "27 \<equiv> succ(26)"
abbreviation
  dec28  :: i   ("28") where "28 \<equiv> succ(27)"
abbreviation
  dec29  :: i   ("29") where "29 \<equiv> succ(28)"


locale Demo = M_trivial + M_AC +
  fixes t\<^sub>1 t\<^sub>2
  assumes 
    ts_in_nat[simp]: "t\<^sub>1\<in>\<omega>" "t\<^sub>2\<in>\<omega>"
    and
    power_infty: "power_ax(M)" "M(\<omega>)"
begin

lemma 
  assumes 
    sorried_replacements:
    "\<And>P. strong_replacement(M,P)"
    "\<And>F. lam_replacement(M,F)"
    "\<And>Q S. iterates_replacement(M,Q,S)"
    "\<And>Q S. wfrec_replacement(M,Q,S)"
    "\<And>Q S. transrec_replacement(M,Q,S)"
    and
    sorried_separations:
    "\<And>Q. separation(M,Q)"shows "M_master(M)"
  apply unfold_locales apply 
    (simp_all add:
      sorried_replacements(1-2)
      sorried_separations
      power_infty)
  \<comment> \<open>We obtain two goals of the form \<^term>\<open>rall(M,\<V>)\<close> because of 
  instances of the form \<^term>\<open>\<forall>x[M]. separation(M,P)\<close>\<close> 
  oops

(* NOTE: Only for pretty-printing purposes, overrides previous
  basic notations  *)
no_notation mem (infixl \<open>\<in>\<close> 50)
no_notation conj  (infixr \<open>\<and>\<close> 35)
no_notation disj (infixr \<open>\<or>\<close> 30)
no_notation iff (infixr \<open>\<longleftrightarrow>\<close> 25)
no_notation imp (infixr \<open>\<longrightarrow>\<close> 25)
no_notation not (\<open>\<not> _\<close> [40] 40)
no_notation All (\<open>'(\<forall>_')\<close>)
no_notation Ex (\<open>'(\<exists>_')\<close>)

no_notation Member (\<open>\<cdot>_ \<in>/ _\<cdot>\<close>)
no_notation Equal (\<open>\<cdot>_ =/ _\<cdot>\<close>)
no_notation Nand (\<open>\<cdot>\<not>'(_ \<and>/ _')\<cdot>\<close>)
no_notation And (\<open>\<cdot>_ \<and>/ _\<cdot>\<close>)
no_notation Or (\<open>\<cdot>_ \<or>/ _\<cdot>\<close>)
no_notation Iff (\<open>\<cdot>_ \<leftrightarrow>/ _\<cdot>\<close>)
no_notation Implies (\<open>\<cdot>_ \<rightarrow>/ _\<cdot>\<close>)
no_notation Neg (\<open>\<cdot>\<not>_\<cdot>\<close>)
no_notation Forall (\<open>'(\<cdot>\<forall>(/_)\<cdot>')\<close>)
no_notation Exists (\<open>'(\<cdot>\<exists>(/_)\<cdot>')\<close>)

notation Member (infixl \<open>\<in>\<close> 50)
notation Equal (infixl \<open>\<equiv>\<close> 50)
notation Nand (\<open>\<not>'(_ \<and>/ _')\<close>)
notation And  (infixr \<open>\<and>\<close> 35)
notation Or (infixr \<open>\<or>\<close> 30)
notation Iff (infixr \<open>\<longleftrightarrow>\<close> 25)
notation Implies (infixr \<open>\<longrightarrow>\<close> 25)
notation Neg (\<open>\<not> _\<close> [40] 40)
notation Forall (\<open>'(\<forall>_')\<close>)
notation Exists (\<open>'(\<exists>_')\<close>)

lemma "forces(t\<^sub>1\<in>t\<^sub>2) = (0 \<in> 1 \<and> forces_mem_fm(1, 2, 0, t\<^sub>1+\<^sub>\<omega>4, t\<^sub>2+\<^sub>\<omega>4))"
  unfolding forces_def by simp

(*
\<comment> \<open>Prefix abbreviated notation\<close>
notation Member (\<open>M\<close>)
notation Equal (\<open>Eq\<close>)
notation Nand (\<open>Na\<close>)
notation And  (\<open>A\<close>)
notation Or (\<open>O\<close>)
notation Iff (\<open>If\<close>)
notation Implies (\<open>Im\<close>)
notation Neg (\<open>Ne\<close>)
notation Forall (\<open>Fo\<close>)
notation Exists (\<open>Ex\<close>)
*)

(* forces_mem_fm(1, 2, 0, t\<^sub>1+\<^sub>\<omega>4, t\<^sub>1+\<^sub>\<omega>4)
   = forces_mem_fm(1, 2, 0, succ(succ(succ(succ(t\<^sub>1)))), succ(succ(succ(succ(t\<^sub>2))))) 
   = \<dots> *)
thm forces_mem_fm_def[of 1 2 0 "t\<^sub>1+\<^sub>\<omega>4" "t\<^sub>2+\<^sub>\<omega>4",
    unfolded frc_at_fm_def forcerel_fm_def ftype_fm_def
    name1_fm_def name2_fm_def snd_snd_fm_def hcomp_fm_def
    ecloseN_fm_def eclose_n1_fm_def eclose_n2_fm_def
    is_eclose_fm_def mem_eclose_fm_def eclose_n_fm_def
    is_If_fm_def least_fm_def Replace_fm_def Collect_fm_def
    fm_definitions, simplified]
  (* NOTE: in view of the above, @{thm fm_definitions} might be incomplete *)

named_theorems incr_bv_new_simps

schematic_goal incr_bv_Neg(* [incr_bv_new_simps] *):
  "mem(n,\<omega>) \<Longrightarrow> mem(\<phi>,formula) \<Longrightarrow> incr_bv(Neg(\<phi>))`n = ?x"
  unfolding Neg_def by simp

schematic_goal incr_bv_Exists [incr_bv_new_simps]:
  "mem(n,\<omega>) \<Longrightarrow> mem(\<phi>,formula) \<Longrightarrow> incr_bv(Exists(\<phi>))`n = ?x"
  unfolding Exists_def by (simp add: incr_bv_Neg)
(*
schematic_goal incr_bv_And [incr_bv_new_simps]:
  "mem(n,\<omega>) \<Longrightarrow> mem(\<phi>,formula) \<Longrightarrow>mem(\<psi>,formula)\<Longrightarrow> incr_bv(And(\<phi>,\<psi>))`n = ?x"
  unfolding And_def by (simp add: incr_bv_Neg)

schematic_goal incr_bv_Or [incr_bv_new_simps]:
  "mem(n,\<omega>) \<Longrightarrow> mem(\<phi>,formula) \<Longrightarrow>mem(\<psi>,formula)\<Longrightarrow> incr_bv(Or(\<phi>,\<psi>))`n = ?x"
  unfolding Or_def by (simp add: incr_bv_Neg)

schematic_goal incr_bv_Implies [incr_bv_new_simps]:
  "mem(n,\<omega>) \<Longrightarrow> mem(\<phi>,formula) \<Longrightarrow>mem(\<psi>,formula)\<Longrightarrow> incr_bv(Implies(\<phi>,\<psi>))`n = ?x"
  unfolding Implies_def by (simp add: incr_bv_Neg)
*)

\<comment> \<open>The two renamings involved in the definition of \<^term>\<open>forces\<close> depend on
the recursive function \<^term>\<open>incr_bv\<close>. Here we have an apparently
exponential bottleneck, since all the propositional connectives (even \<^term>\<open>Neg\<close>)
duplicate the appearances of \<^term>\<open>incr_bv\<close>.

Not even the negation of an atomic formula can be managed by the system\<close>
(* exception Size raised (line 183 of "./basis/LibrarySupport.sml") *)
schematic_goal "forces(\<not>0\<in>1) = ?x"
  unfolding forces_def Neg_def
  (* by (simp add:ren_forces_nand_def ren_forces_forall_def leq_fm_def
      forces_mem_fm_def frc_at_fm_def forcerel_fm_def ftype_fm_def
      name1_fm_def name2_fm_def snd_snd_fm_def hcomp_fm_def
      ecloseN_fm_def eclose_n1_fm_def eclose_n2_fm_def
      is_eclose_fm_def mem_eclose_fm_def eclose_n_fm_def
      is_If_fm_def least_fm_def Collect_fm_def
      fm_definitions incr_bv_Neg incr_bv_Exists) *)
  oops

(*
declare is_ContHyp_fm_def[fm_definitions del]

thm is_ContHyp_fm_def[unfolded is_eclose_fm_def mem_eclose_fm_def eclose_n_fm_def
   is_If_fm_def least_fm_def Replace_fm_def Collect_fm_def
   fm_definitions, simplified] *)

end \<comment> \<open>\<^locale>\<open>Demo\<close>\<close>


end