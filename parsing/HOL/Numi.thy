(*  Title:      HOL/Num.thy
    Author:     Florian Haftmann
    Author:     Brian Huffman
*)

section \<open>Binary Numerals\<close>

theory Numi
  imports BNF_Least_Fixpoint Transfer
begin

subsection \<open>The \<open>num\<close> type\<close>

datatype num = One | Bit0 num | Bit1 num

text \<open>Increment function for type @{typ num}\<close>

primrec inc :: "num \<Rightarrow> num"
  where
    "inc One = Bit0 One"
  | "inc (Bit0 x) = Bit1 x"
  | "inc (Bit1 x) = Bit0 (inc x)"

text \<open>Converting between type @{typ num} and type @{typ nat}\<close>

primrec nat_of_num :: "num \<Rightarrow> nat"
  where
    "nat_of_num One = Suc 0"
  | "nat_of_num (Bit0 x) = nat_of_num x + nat_of_num x"
  | "nat_of_num (Bit1 x) = Suc (nat_of_num x + nat_of_num x)"

primrec num_of_nat :: "nat \<Rightarrow> num"
  where
    "num_of_nat 0 = One"
  | "num_of_nat (Suc n) = (if 0 < n then inc (num_of_nat n) else One)"

lemma nat_of_num_pos: "0 < nat_of_num x"
  by (induct x) simp_all

lemma nat_of_num_neq_0: " nat_of_num x \<noteq> 0"
  by (induct x) simp_all

lemma nat_of_num_inc: "nat_of_num (inc x) = Suc (nat_of_num x)"
  by (induct x) simp_all

lemma num_of_nat_double: "0 < n \<Longrightarrow> num_of_nat (n + n) = Bit0 (num_of_nat n)"
  by (induct n) simp_all

text \<open>Type @{typ num} is isomorphic to the strictly positive natural numbers.\<close>

lemma nat_of_num_inverse: "num_of_nat (nat_of_num x) = x"
  by (induct x) (simp_all add: num_of_nat_double nat_of_num_pos)

lemma num_of_nat_inverse: "0 < n \<Longrightarrow> nat_of_num (num_of_nat n) = n"
  by (induct n) (simp_all add: nat_of_num_inc)

lemma num_eq_iff: "x = y \<longleftrightarrow> nat_of_num x = nat_of_num y"
  apply safe
  apply (drule arg_cong [where f=num_of_nat])
  apply (simp add: nat_of_num_inverse)
  done

lemma num_induct [case_names One inc]:
  fixes P :: "num \<Rightarrow> bool"
  assumes One: "P One"
    and inc: "\<And>x. P x \<Longrightarrow> P (inc x)"
  shows "P x"
proof -
  obtain n where n: "Suc n = nat_of_num x"
    by (cases "nat_of_num x") (simp_all add: nat_of_num_neq_0)
  have "P (num_of_nat (Suc n))"
  proof (induct n)
    case 0
    from One show ?case by simp
  next
    case (Suc n)
    then have "P (inc (num_of_nat (Suc n)))" by (rule inc)
    then show "P (num_of_nat (Suc (Suc n)))" by simp
  qed
  with n show "P x"
    by (simp add: nat_of_num_inverse)
qed

text \<open>
  From now on, there are two possible models for @{typ num}: as positive
  naturals (rule \<open>num_induct\<close>) and as digit representation (rules
  \<open>num.induct\<close>, \<open>num.cases\<close>).
\<close>


subsection \<open>Numeral operations\<close>

instantiation num :: "{plus,times,linorder}"
begin

definition  "m + n = num_of_nat (nat_of_num m + nat_of_num n)"

definition  "m * n = num_of_nat (nat_of_num m * nat_of_num n)"

definition  "m \<le> n \<longleftrightarrow> nat_of_num m \<le> nat_of_num n"

definition  "m < n \<longleftrightarrow> nat_of_num m < nat_of_num n"

instance
  by standard (auto simp add: less_num_def less_eq_num_def num_eq_iff)

end

lemma nat_of_num_add: "nat_of_num (x + y) = nat_of_num x + nat_of_num y"
  unfolding plus_num_def
  by (intro num_of_nat_inverse add_pos_pos nat_of_num_pos)

lemma nat_of_num_mult: "nat_of_num (x * y) = nat_of_num x * nat_of_num y"
  unfolding times_num_def
  by (intro num_of_nat_inverse mult_pos_pos nat_of_num_pos)

lemma add_num_simps [simp]:
  "One + One = Bit0 One"
  "One + Bit0 n = Bit1 n"
  "One + Bit1 n = Bit0 (n + One)"
  "Bit0 m + One = Bit1 m"
  "Bit0 m + Bit0 n = Bit0 (m + n)"
  "Bit0 m + Bit1 n = Bit1 (m + n)"
  "Bit1 m + One = Bit0 (m + One)"
  "Bit1 m + Bit0 n = Bit1 (m + n)"
  "Bit1 m + Bit1 n = Bit0 (m + n + One)"
  by (simp_all add: num_eq_iff nat_of_num_add)

lemma mult_num_simps [simp]:
  "m * One = m"
  "One * n = n"
  "Bit0 m * Bit0 n = Bit0 (Bit0 (m * n))"
  "Bit0 m * Bit1 n = Bit0 (m * Bit1 n)"
  "Bit1 m * Bit0 n = Bit0 (Bit1 m * n)"
  "Bit1 m * Bit1 n = Bit1 (m + n + Bit0 (m * n))"
  by (simp_all add: num_eq_iff nat_of_num_add nat_of_num_mult distrib_right distrib_left)

lemma eq_num_simps:
  "One = One \<longleftrightarrow> True"
  "One = Bit0 n \<longleftrightarrow> False"
  "One = Bit1 n \<longleftrightarrow> False"
  "Bit0 m = One \<longleftrightarrow> False"
  "Bit1 m = One \<longleftrightarrow> False"
  "Bit0 m = Bit0 n \<longleftrightarrow> m = n"
  "Bit0 m = Bit1 n \<longleftrightarrow> False"
  "Bit1 m = Bit0 n \<longleftrightarrow> False"
  "Bit1 m = Bit1 n \<longleftrightarrow> m = n"
  by simp_all

lemma le_num_simps [simp]:
  "One \<le> n \<longleftrightarrow> True"
  "Bit0 m \<le> One \<longleftrightarrow> False"
  "Bit1 m \<le> One \<longleftrightarrow> False"
  "Bit0 m \<le> Bit0 n \<longleftrightarrow> m \<le> n"
  "Bit0 m \<le> Bit1 n \<longleftrightarrow> m \<le> n"
  "Bit1 m \<le> Bit1 n \<longleftrightarrow> m \<le> n"
  "Bit1 m \<le> Bit0 n \<longleftrightarrow> m < n"
  using nat_of_num_pos [of n] nat_of_num_pos [of m]
  by (auto simp add: less_eq_num_def less_num_def)

lemma less_num_simps [simp]:
  "m < One \<longleftrightarrow> False"
  "One < Bit0 n \<longleftrightarrow> True"
  "One < Bit1 n \<longleftrightarrow> True"
  "Bit0 m < Bit0 n \<longleftrightarrow> m < n"
  "Bit0 m < Bit1 n \<longleftrightarrow> m \<le> n"
  "Bit1 m < Bit1 n \<longleftrightarrow> m < n"
  "Bit1 m < Bit0 n \<longleftrightarrow> m < n"
  using nat_of_num_pos [of n] nat_of_num_pos [of m]
  by (auto simp add: less_eq_num_def less_num_def)

lemma le_num_One_iff: "x \<le> num.One \<longleftrightarrow> x = num.One"
  by (simp add: antisym_conv)

text \<open>Rules using \<open>One\<close> and \<open>inc\<close> as constructors.\<close>

lemma add_One: "x + One = inc x"
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma add_One_commute: "One + n = n + One"
  by (induct n) simp_all

lemma add_inc: "x + inc y = inc (x + y)"
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma mult_inc: "x * inc y = x * y + x"
  by (simp add: num_eq_iff nat_of_num_mult nat_of_num_add nat_of_num_inc)

text \<open>The @{const num_of_nat} conversion.\<close>

lemma num_of_nat_One: "n \<le> 1 \<Longrightarrow> num_of_nat n = One"
  by (cases n) simp_all

lemma num_of_nat_plus_distrib:
  "0 < m \<Longrightarrow> 0 < n \<Longrightarrow> num_of_nat (m + n) = num_of_nat m + num_of_nat n"
  by (induct n) (auto simp add: add_One add_One_commute add_inc)

text \<open>A double-and-decrement function.\<close>

primrec BitM :: "num \<Rightarrow> num"
  where
    "BitM One = One"
  | "BitM (Bit0 n) = Bit1 (BitM n)"
  | "BitM (Bit1 n) = Bit1 (Bit0 n)"

lemma BitM_plus_one: "BitM n + One = Bit0 n"
  by (induct n) simp_all

lemma one_plus_BitM: "One + BitM n = Bit0 n"
  unfolding add_One_commute BitM_plus_one ..

subsection \<open>Binary numerals\<close>

text \<open>
  We embed binary representations into a generic algebraic
  structure using \<open>numeral\<close>.
\<close>

class numeral = one + semigroup_add
begin

primrec numeral :: "num \<Rightarrow> 'a"
  where
    numeral_One: "numeral One = 1"
  | numeral_Bit0: "numeral (Bit0 n) = numeral n + numeral n"
  | numeral_Bit1: "numeral (Bit1 n) = numeral n + numeral n + 1"


lemma one_plus_numeral_commute: "1 + numeral x = numeral x + 1"
proof (induct x)
  case One
  then show ?case by simp
next
  case Bit0
  then show ?case by (simp add: add.assoc [symmetric]) (simp add: add.assoc)
next
  case Bit1
  then show ?case by (simp add: add.assoc [symmetric]) (simp add: add.assoc)
qed

lemma numeral_inc: "numeral (inc x) = numeral x + 1"
proof (induct x)
  case One
  then show ?case by simp
next
  case Bit0
  then show ?case by simp
next
  case (Bit1 x)
  have "numeral x + (1 + numeral x) + 1 = numeral x + (numeral x + 1) + 1"
    by (simp only: one_plus_numeral_commute)
  with Bit1 show ?case
    by (simp add: add.assoc)
qed

declare numeral.simps [simp del]

end

text \<open>Numeral syntax.\<close>

syntax
  "_Numeral" :: "num_const \<Rightarrow> 'a"    ("_")

ML_file "numeral.ML"

parse_translation \<open>
  let
    fun numeral_tr [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u] =
          c $ numeral_tr [t] $ u
      | numeral_tr [Const (num, _)] =
          (Numeral.mk_number_syntax o #value o Lexicon.read_num) num
      | numeral_tr ts = raise TERM ("numeral_tr", ts);
  in [(@{syntax_const "_Numeral"}, K numeral_tr)] end
\<close>

typed_print_translation \<open>
  let
    fun num_tr' ctxt T [n] =
      let
        val k = Numeral.dest_num_syntax n;
        val t' =
          Syntax.const @{syntax_const "_Numeral"} $
            Syntax.free (string_of_int k);
      in
        (case T of
          Type (@{type_name fun}, [_, T']) =>
            if Printer.type_emphasis ctxt T' then
              Syntax.const @{syntax_const "_constrain"} $ t' $
                Syntax_Phases.term_of_typ ctxt T'
            else t'
        | _ => if T = dummyT then t' else raise Match)
      end;
  in
   [(@{const_syntax numeral}, num_tr')]
  end
\<close>


subsection \<open>Class-specific numeral rules\<close>

text \<open>@{const numeral} is a morphism.\<close>


subsubsection \<open>Structures with addition: class \<open>numeral\<close>\<close>

context numeral
begin

lemma numeral_add: "numeral (m + n) = numeral m + numeral n"
  by (induct n rule: num_induct)
    (simp_all only: numeral_One add_One add_inc numeral_inc add.assoc)

lemma numeral_plus_numeral: "numeral m + numeral n = numeral (m + n)"
  by (rule numeral_add [symmetric])

schematic_goal  "15 + 23  = ?K"
  by (simp add:numeral_plus_numeral)

end
