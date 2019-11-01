theory Renaming_Auto
  imports 
    Renaming
    ZF.Finite
    ZF.List
begin

lemmas app_fun = apply_iff[THEN iffD1]
lemmas nat_succI = nat_succ_iff[THEN iffD2]

ML_file\<open>Renaming_ML.ml\<close>

end