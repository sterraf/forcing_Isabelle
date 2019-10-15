(*  Title:      HOL/Tools/numeral.ML
    Author:     Makarius

Logical and syntactic operations on numerals (see also HOL/Tools/hologic.ML).
*)

signature NUMERAL =
sig
  val mk_cnumber: ctyp -> int -> cterm
  val mk_number_syntax: int -> term
  val dest_num_syntax: term -> int
end;

structure Numeral: NUMERAL =
struct

(* numeral *)

fun dest_num_syntax (Const (@{const_syntax Numi.Bit0}, _) $ t) = 2 * dest_num_syntax t
  | dest_num_syntax (Const (@{const_syntax Numi.Bit1}, _) $ t) = 2 * dest_num_syntax t + 1
  | dest_num_syntax (Const (@{const_syntax Numi.One}, _)) = 1;

fun mk_num_syntax n =
  if n > 0 then
    (case IntInf.quotRem (n, 2) of
      (0, 1) => Syntax.const @{const_syntax One}
    | (n, 0) => Syntax.const @{const_syntax Bit0} $ mk_num_syntax n
    | (n, 1) => Syntax.const @{const_syntax Bit1} $ mk_num_syntax n)
  else raise Match

fun mk_cbit 0 = @{cterm "Numi.Bit0"}
  | mk_cbit 1 = @{cterm "Numi.Bit1"}
  | mk_cbit _ = raise CTERM ("mk_cbit", []);

fun mk_cnumeral i =
  let
    fun mk 1 = @{cterm "Numi.One"}
      | mk i =
      let val (q, r) = Integer.div_mod i 2 in
        Thm.apply (mk_cbit r) (mk q)
      end
  in
    if i > 0 then mk i else raise CTERM ("mk_cnumeral: negative input", [])
  end


(* number *)

local

val cterm_of = Thm.cterm_of @{context};
fun tvar S = (("'a", 0), S);

val zero_tvar = tvar @{sort zero};
val zero = cterm_of (Const (@{const_name zero_class.zero}, TVar zero_tvar));

val one_tvar = tvar @{sort one};
val one = cterm_of (Const (@{const_name one_class.one}, TVar one_tvar));

val numeral_tvar = tvar @{sort numeral};
val numeral = cterm_of (Const (@{const_name numeral}, @{typ num} --> TVar numeral_tvar));

val uminus_tvar = tvar @{sort uminus};
val uminus = cterm_of (Const (@{const_name uminus}, TVar uminus_tvar --> TVar uminus_tvar));

fun instT T v = Thm.instantiate_cterm ([(v, T)], []);

in

fun mk_cnumber T 0 = instT T zero_tvar zero
  | mk_cnumber T 1 = instT T one_tvar one
  | mk_cnumber T i =
      if i > 0 then
        Thm.apply (instT T numeral_tvar numeral) (mk_cnumeral i)
      else
        Thm.apply (instT T uminus_tvar uminus)
          (Thm.apply (instT T numeral_tvar numeral) (mk_cnumeral (~ i)));

end;

fun mk_number_syntax n =
  if n = 0 then Syntax.const @{const_syntax Groups.zero}
  else if n = 1 then Syntax.const @{const_syntax Groups.one}
  else Syntax.const @{const_syntax numeral} $ mk_num_syntax n;

end;
