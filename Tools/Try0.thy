section \<open>Auto methods imported from HOL\<close>

theory Try0
imports Pure 
keywords
  "try" "solve_direct" "try0" :: diag 
begin

ML_file \<open>~~/src/Tools/try.ML\<close>
ML_file \<open>~~/src/Tools/solve_direct.ML\<close>

subsection\<open>Try0\<close>

ML_file \<open>try0.ML\<close>

setup Pure_Thy.old_appl_syntax_setup

end
