(*  Title:      HOL/Num.thy
    Author:     Florian Haftmann
    Author:     Brian Huffman
*)

section \<open>Binary Numerals\<close>

theory Num
  imports ZF "src/Nat_Miscellanea"
begin

subsection \<open>The \<open>num\<close> type\<close>

consts num :: "i"
datatype "num" = One | Bit0 ("x\<in>num") | Bit1 ("x\<in>num")

text \<open>Increment function for type @{const num}\<close>

consts inc :: "i \<Rightarrow> i"
primrec 
  "inc(One) = Bit0(One)"
  "inc (Bit0(x)) = Bit1(x)"
  "inc (Bit1(x)) = Bit0 (inc(x))"

lemma inc_type [TC]: "x\<in>num \<Longrightarrow> inc(x) \<in> num"
  by (induct x rule:num.induct; auto)

text \<open>Converting between type @{const num} and type @{const nat}\<close>

consts nat_of_num :: "i \<Rightarrow> i"
primrec 
   "nat_of_num(One) = succ (0)"
   "nat_of_num (Bit0(x)) = nat_of_num(x) #+ nat_of_num(x)"
   "nat_of_num (Bit1(x)) = succ (nat_of_num(x) #+ nat_of_num(x))"

lemma nat_of_num_type [TC]: "x\<in>num \<Longrightarrow> nat_of_num(x) \<in> nat"
  by (induct x rule:num.induct, simp_all)

consts num_of_nat :: "i \<Rightarrow> i"
primrec
  "num_of_nat (0) = One"
  "num_of_nat (succ(n)) = (if 0 < n then inc (num_of_nat(n)) else One)"

lemma num_of_nat_type [TC]: "x\<in>nat \<Longrightarrow> num_of_nat(x) \<in> num"
  by (induct x rule:nat_induct; auto)

lemma nat_of_num_pos: "x\<in>num \<Longrightarrow> 0 < nat_of_num(x)"
  by (induct x rule:num.induct) (simp_all add:zero_less_add)

lemma nat_of_num_neq_0: "x\<in>num \<Longrightarrow> nat_of_num(x) \<noteq> 0"
  by (induct x rule:num.induct) simp_all

lemma nat_of_num_inc: "x\<in>num \<Longrightarrow> nat_of_num (inc(x)) = succ (nat_of_num(x))"
  by (induct x rule:num.induct) simp_all

lemma num_of_nat_double: "n\<in>nat \<Longrightarrow> 0 < n \<Longrightarrow> num_of_nat (n #+ n) = Bit0 (num_of_nat(n))"
  apply (induct n rule:nat_induct)
   apply (auto)
  apply (drule le0D[OF div_rls(10), rotated 2]; simp)+
  done

text \<open>Type @{const num} is isomorphic to the strictly positive natural numbers.\<close>

lemma nat_of_num_inverse: "x\<in>num \<Longrightarrow> num_of_nat (nat_of_num(x)) = x"
  apply (induct x rule:num.induct) 
    apply (simp_all add: num_of_nat_double nat_of_num_pos;auto)
 apply (subgoal_tac "nat_of_num(Bit0(x))\<in>nat"; simp)
 apply (subgoal_tac "nat_of_num(x) #+ nat_of_num(x) \<in>nat"; auto)
  sorry

lemma num_of_nat_inverse: "n\<in>nat \<Longrightarrow> 0 < n \<Longrightarrow> nat_of_num (num_of_nat(n)) = n"
  by (induct n rule:nat_induct) (auto dest: le0D[OF div_rls(10), rotated 2] simp add: nat_of_num_inc)
  
lemma num_eq_iff: "x\<in>num \<Longrightarrow> y \<in> num \<Longrightarrow> x = y \<longleftrightarrow> nat_of_num(x) = nat_of_num(y)"
  apply safe
  apply (drule subst_context [where t=num_of_nat])
  apply (simp add: nat_of_num_inverse)
  done

lemma num_induct [case_names One inc]:
  fixes P 
  assumes One: "P (One)"
    and inc: "\<And>x. P (x) \<Longrightarrow> P (inc(x))"
  shows "x\<in>num \<Longrightarrow> P(x)"
proof -
  obtain n where n: "succ(n) = nat_of_num(x)" "n\<in>nat"
    by (cases "nat_of_num(x)") (simp_all add: nat_of_num_neq_0)
  have "n\<in>nat \<Longrightarrow> P (num_of_nat (succ(n)))" for n
  proof (induct n rule:nat_induct)
    case 0
    from One show ?case by simp
  next
    case (succ n)
    then have "n\<in>nat \<Longrightarrow> P (inc (num_of_nat (succ(n))))" by (rule_tac inc)
    then show "n\<in>nat \<Longrightarrow> P (num_of_nat (succ (succ(n))))" by simp
  qed
  with n(1)[symmetric] n(2) 
  have "P(num_of_nat(nat_of_num(x)))" by simp
  then show "x\<in>num \<Longrightarrow> P(x)"
    by (simp add: nat_of_num_inverse)
qed

text \<open>
  From now on, there are two possible models for @{const num}: as positive
  naturals (rule \<open>num_induct\<close>) and as digit representation (rules
  \<open>num.induct\<close>, \<open>num.cases\<close>).
\<close>


subsection \<open>Numeral operations\<close>

definition  
  plus_num :: "[i,i] \<Rightarrow> i" (infixl "+#" 65) where 
  "m +# n = num_of_nat (nat_of_num(m) #+ nat_of_num(n))"

definition 
  times_num:: "[i,i] \<Rightarrow> i" (infixl "*#" 65) where
  "m *# n = num_of_nat (nat_of_num(m) #* nat_of_num(n))"

definition  
  less_eq_num :: "[i,i] \<Rightarrow> o" (infixl "\<le>#" 65) where
  "m \<le># n \<longleftrightarrow> nat_of_num(m) \<le> nat_of_num(n)"

definition  
  less_num :: "[i,i] \<Rightarrow> o" (infixl "<#" 65) where
  "m <# n \<longleftrightarrow> nat_of_num(m) < nat_of_num(n)"

lemma [TC]:
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> m +# n \<in> num"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> m *# n \<in> num"
  unfolding plus_num_def times_num_def by simp_all

lemma add_pos_pos: "a\<in>nat \<Longrightarrow> b \<in> nat \<Longrightarrow> 0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a #+ b"
  sorry

lemma nat_of_num_add: "x\<in>num \<Longrightarrow> y \<in> num \<Longrightarrow> nat_of_num (x +# y) = nat_of_num(x) #+ nat_of_num(y)"
  unfolding plus_num_def 
  by (simp add:num_of_nat_inverse add_pos_pos nat_of_num_pos)

lemma mult_pos_pos: "a\<in>nat \<Longrightarrow> b \<in> nat \<Longrightarrow> 0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a #* b"
  sorry

lemma nat_of_num_mult: "x\<in>num \<Longrightarrow> y \<in> num \<Longrightarrow> nat_of_num (x *# y) = nat_of_num(x) #* nat_of_num(y)"
  unfolding times_num_def
  by (simp add:num_of_nat_inverse mult_pos_pos nat_of_num_pos)

lemma add_num_simps [simp]:
  "One +# One = Bit0(One)"
  "n\<in>num \<Longrightarrow> One +# Bit0(n) = Bit1(n)"
  "n\<in>num \<Longrightarrow> One +# Bit1(n) = Bit0 (n +# One)"
  "m\<in>num \<Longrightarrow> Bit0(m) +# One = Bit1(m)"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit0(m) +# Bit0(n) = Bit0 (m +# n)"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit0(m) +# Bit1(n) = Bit1 (m +# n)"
  "m\<in>num \<Longrightarrow> Bit1(m) +# One = Bit0 (m +# One)"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit1(m) +# Bit0(n) = Bit1 (m +# n)"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit1(m) +# Bit1(n) = Bit0 (m +# n +# One)"
          apply (simp_all add: num_eq_iff[symmetric] nat_of_num_add)
  sorry

lemma distrib_right: "a\<in>nat \<Longrightarrow> b\<in>nat \<Longrightarrow> c\<in>nat \<Longrightarrow> (a #+ b) #* c = a #* c #+ b #* c"
  sorry

lemma distrib_left: "a\<in>nat \<Longrightarrow> b\<in>nat \<Longrightarrow> c\<in>nat \<Longrightarrow> c #* (a #+ b)  = c #* a #+ c #* b"
  sorry

lemma mult_num_simps [simp]:
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> m *# One = m"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> One *# n = n"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit0(m) *# Bit0(n) = Bit0 (Bit0 (m *# n))"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit0(m) *# Bit1(n) = Bit0 (m *# Bit1(n))"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit1(m) *# Bit0(n) = Bit0 (Bit1(m) *# n)"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit1(m) *# Bit1(n) = Bit1 (m +# n +# Bit0 (m *# n))"
   apply (simp_all add: num_eq_iff nat_of_num_add nat_of_num_mult distrib_right distrib_left)
  sorry

lemma eq_num_simps:
  "One = One \<longleftrightarrow> True"
  "One = Bit0(n) \<longleftrightarrow> False"
  "One = Bit1(n) \<longleftrightarrow> False"
  "Bit0(m) = One \<longleftrightarrow> False"
  "Bit1(m) = One \<longleftrightarrow> False"
  "Bit0(m) = Bit0(n) \<longleftrightarrow> m = n"
  "Bit0(m) = Bit1(n) \<longleftrightarrow> False"
  "Bit1(m) = Bit0(n) \<longleftrightarrow> False"
  "Bit1(m) = Bit1(n) \<longleftrightarrow> m = n"
  by simp_all

lemma le_num_simps [simp]:
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> One \<le># n \<longleftrightarrow> True"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit0(m) \<le># One \<longleftrightarrow> False"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit1(m) \<le># One \<longleftrightarrow> False"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit0(m) \<le># Bit0(n) \<longleftrightarrow> m \<le># n"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit0(m) \<le># Bit1(n) \<longleftrightarrow> m \<le># n"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit1(m) \<le># Bit1(n) \<longleftrightarrow> m \<le># n"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit1(m) \<le># Bit0(n) \<longleftrightarrow> m <# n"
  using nat_of_num_pos [of n] nat_of_num_pos [of m]
        apply (auto simp add: less_eq_num_def less_num_def)
  sorry

lemma less_num_simps [simp]:
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> m <# One \<longleftrightarrow> False"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> One <# Bit0(n) \<longleftrightarrow> True"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> One <# Bit1(n) \<longleftrightarrow> True"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit0(m) <# Bit0(n) \<longleftrightarrow> m <# n"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit0(m) <# Bit1(n) \<longleftrightarrow> m \<le># n"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit1(m) <# Bit1(n) \<longleftrightarrow> m <# n"
  "m\<in>num \<Longrightarrow> n\<in>num \<Longrightarrow> Bit1(m) <# Bit0(n) \<longleftrightarrow> m <# n"
  using nat_of_num_pos [of n] nat_of_num_pos [of m]
  apply (auto simp add: less_eq_num_def less_num_def)
  sorry

lemma le_num_One_iff: "x\<in>num \<Longrightarrow> x \<le># num.One \<longleftrightarrow> x = num.One"
  unfolding less_eq_num_def
  apply (simp add:le_anti_sym)
  sorry

text \<open>Rules using \<open>One\<close> and \<open>inc\<close> as constructors.\<close>

lemma add_One: "x\<in>num \<Longrightarrow> x +# One = inc(x)"
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma add_One_commute: "n\<in>num \<Longrightarrow> One +# n = n +# One"
  by (induct n) simp_all

lemma add_inc: "x\<in>num \<Longrightarrow> y\<in>num \<Longrightarrow> x #+ inc(y) = inc (x #+ y)"
  by (simp add: num_eq_iff nat_of_num_add nat_of_num_inc)

lemma mult_inc: "x\<in>num \<Longrightarrow> y\<in>num \<Longrightarrow> x * inc(y) = x * y #+ x"
  by (simp add: num_eq_iff nat_of_num_mult nat_of_num_add nat_of_num_inc)

text \<open>The @{const num_of_nat} conversion.\<close>

lemma num_of_nat_One: "n \<le> 1 \<Longrightarrow> num_of_nat(n) = One"
  apply (cases "n=1")
   apply simp_all
  sorry

lemma num_of_nat_plus_distrib:
  "n\<in>nat \<Longrightarrow> m\<in>nat \<Longrightarrow> 0 < m \<Longrightarrow> 0 < n \<Longrightarrow> num_of_nat (m #+ n) = num_of_nat(m) #+ num_of_nat(n)"
  apply (induct n rule:nat_induct) 
   apply (auto simp add: add_One add_One_commute add_inc)
  sorry

text \<open>A double-and-decrement function.\<close>

consts  BitM :: "i \<Rightarrow> i"
primrec
  "BitM (One) = One"
  "BitM (Bit0(n)) = Bit1 (BitM (n))"
  "BitM (Bit1(n)) = Bit1 (Bit0(n))"

lemma BitM_type [TC] : "n\<in>num \<Longrightarrow> BitM(n)\<in>num"
   by (induct n rule:num.induct; auto)

lemma BitM_plus_one: "n\<in>num \<Longrightarrow> BitM (n) +# One = Bit0(n)"
proof (induct n rule:num.induct; simp_all)
  fix x
  assume "x\<in>num" "BitM(x) +# One = Bit0(x)"
  then 
  have "Bit0(x)\<in>num" by auto
  then
  have "Bit1(Bit0(x)) +# One = Bit0(Bit0(x) +# One)"
    using add_num_simps(7)[of "Bit0(x)"] by simp
  also from \<open>x\<in>num\<close>
  have "... = Bit0(Bit1(x))"
    using add_num_simps(4)[of x] by simp
  finally
  show "Bit1(Bit0(x)) +# One = Bit0(Bit1(x))" .
qed

lemma one_plus_BitM: "n\<in>num \<Longrightarrow> One +# BitM(n) = Bit0(n)"
  using add_One_commute BitM_plus_one by simp


subsection \<open>Binary numerals\<close>

text \<open>
  We embed binary representations into a generic algebraic
  structure using \<open>numeral\<close>.
\<close>

class numeral = one #+ semigroup_add
begin

primrec numeral :: "num \<Rightarrow> 'a"
  where
    numeral_One: "numeral One = 1"
  | numeral_Bit0: "numeral (Bit0(n) = numeral n #+ numeral n"
  | numeral_Bit1: "numeral (Bit1(n) = numeral n #+ numeral n #+ 1"

lemma one_plus_numeral_commute: "1 #+ numeral x = numeral x #+ 1"
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

lemma numeral_inc: "numeral (inc(x)) = numeral (x) #+ 1"
proof (induct x)
  case One
  then show ?case by simp
next
  case Bit0
  then show ?case by simp
next
  case (Bit1(x)
  have "numeral x #+ (1 #+ numeral x) #+ 1 = numeral x #+ (numeral x #+ 1) #+ 1"
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

lemma numeral_add: "numeral (m #+ n) = numeral m #+ numeral n"
  by (induct n rule: num_induct)
    (simp_all only: numeral_One add_One add_inc numeral_inc add.assoc)

lemma numeral_plus_numeral: "numeral m #+ numeral n = numeral (m #+ n)"
  by (rule numeral_add [symmetric])

schematic_goal  "15 #+ 23  = K"
  by (simp add:numeral_plus_numeral)

end
