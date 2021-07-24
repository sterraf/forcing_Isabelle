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


locale Demo = 
  fixes t\<^sub>1 t\<^sub>2
  assumes ts_in_nat[simp]: "t\<^sub>1\<in>\<omega>" "t\<^sub>2\<in>\<omega>"
begin

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

(* thm is_ContHyp_fm_def[unfolded is_eclose_fm_def mem_eclose_fm_def eclose_n_fm_def
   is_If_fm_def least_fm_def Replace_fm_def Collect_fm_def
   fm_definitions, simplified] *)

end (* Demo *)


end