theory Forces_locale imports Forcing_data Names begin

definition
  SepReplace :: "[i, i\<Rightarrow>i, i\<Rightarrow> o] \<Rightarrow>i" where
  "SepReplace(A,b,Q) == {y . x\<in>A, y=b(x) \<and> Q(x)}"
  
syntax
  "_SepReplace"  :: "[i, pttrn, i, o] => i"  ("(1{_ ../ _ \<in> _, _})")
translations
  "{b .. x\<in>A, Q}" => "CONST SepReplace(A, \<lambda>x. b, \<lambda>x. Q)"

lemma Sep_and_Replace: "{b(x) .. x\<in>A, P(x) } = {b(x) . x\<in>{y\<in>A. P(y)}}"
  by (auto simp add:SepReplace_def)

lemma SepReplace_subset : "A\<subseteq>A'\<Longrightarrow> {b .. x\<in>A, Q}\<subseteq>{b .. x\<in>A', Q}"
  by (auto simp add:SepReplace_def)

(*
lemma SepReplace_cong1 : "(\<And>x. b(x) = b'(x))\<Longrightarrow> {b(x) .. x\<in>A, Q(x)}={b'(x) .. x\<in>A, Q(x)}"
  by (auto simp add:SepReplace_def)
*)
    
lemma SepReplace_dom_implies :
   "\<forall>x\<in>A. b(x) = b'(x)\<Longrightarrow> {b(x) .. x\<in>A, Q(x)}={b'(x) .. x\<in>A, Q(x)}"
  by  (simp add:SepReplace_def)
    
lemma SepReplace_pred_implies :
   "\<forall>x. Q(x)\<longrightarrow> b(x) = b'(x)\<Longrightarrow> {b(x) .. x\<in>A, Q(x)}={b'(x) .. x\<in>A, Q(x)}"
  by  (force simp add:SepReplace_def)
   
lemma aux_VoN : "N\<in>M \<Longrightarrow>  domain(N) \<subseteq> trancl(Memrel(eclose(M)))-``{N}"
  apply clarify
  apply (rule vimageI [of _ N], simp_all)
   apply (rule_tac b="\<langle> x,y\<rangle>" in rtrancl_into_trancl1, rule trancl_into_rtrancl)
   apply (rule_tac b="{x}" in rtrancl_into_trancl1, rule trancl_into_rtrancl)
    apply (rule MemrelI [THEN r_into_trancl], simp)
       prefer 3 apply (rule  MemrelI)
         prefer 6 apply (rule  MemrelI)
      apply (tactic {* distinct_subgoals_tac *})
       apply auto
      prefer 5  apply (rule_tac A="{x}" in ecloseD)
       apply (tactic {* distinct_subgoals_tac *})
       apply (rule_tac A="\langle x,y\rangle" in ecloseD)
       apply (tactic {* distinct_subgoals_tac *})
     apply (rule_tac A="N" in ecloseD)
      apply (tactic {* distinct_subgoals_tac *})
     apply (rule arg_into_eclose)
     apply (simp_all add:Pair_def)
  done
  
lemma [trans] : "x=y \<Longrightarrow> y\<subseteq>z \<Longrightarrow> x\<subseteq>z"
                "x\<subseteq>y \<Longrightarrow> y=z \<Longrightarrow> x\<subseteq>z"
  by simp_all
    
    
lemma SepReplace_iff [simp]: "y\<in>{b(x) .. x\<in>A, P(x)} \<longleftrightarrow> (\<exists>x\<in>A. y=b(x) & P(x))"
   by (auto simp add:SepReplace_def)
 
    
context forcing_data
begin  (*************** CONTEXT: forcing_data *****************)
definition
  val :: "i\<Rightarrow>i\<Rightarrow>i" where
  "val == valR(M,P)"

definition
  Hv :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i" where
  "Hv == Hval(P)"

definition
    GenExt :: "i\<Rightarrow>i"     ("M[_]" 90)
    where "GenExt(G)== {val(G,\<tau>). \<tau> \<in> M}"
      

lemma aux2: "Hv(G,x,f) = { f`y .. y\<in> domain(x), \<exists>p\<in>P. \langle y,p\rangle \<in> x \<and> p \<in> G }"
  by (simp add:Sep_and_Replace Hv_def Hval_def)  

    
lemma val_of_name : "{x\<in>A\<times>P. Q(x)}\<in>M \<Longrightarrow> 
       val(G,{x\<in>A\<times>P. Q(x)}) = {val(G,t) .. t\<in>A , \<exists>p\<in>P .  Q(\langle t,p\rangle) \<and> p \<in> G }"
proof -
  let
              ?n="{x\<in>A\<times>P. Q(x)}" and
              ?r="trancl(Memrel(eclose(M)))"
  assume
         asm:    "?n\<in>M"
  let
              ?f="\<lambda>z\<in>?r-``{?n}. val(G,z)"
  have
              "wf(?r)"
    by (rule wf_Memrel [THEN wf_trancl])
  with val_def have
              "val(G,?n) = Hv(G,?n,?f)"
    unfolding Hv_def 
    apply (simp)
    apply (rule def_wfrec [of  _ _ "Hval(P,G)"], simp_all add: valR_def)
    done
  also have
              "... = {?f`t .. t\<in>domain(?n), \<exists>p\<in>P . \langle t,p\rangle\<in>?n \<and> p\<in>G}"
    using aux2 by simp
  also have
              "... = { (if t\<in>?r-``{?n} then val(G,t) else 0) .. t\<in>domain(?n), \<exists>p\<in>P . \langle t,p\rangle\<in>?n \<and> p\<in>G}"
    by (simp)
  also have
        Eq1:  "... = { val(G,t) .. t\<in>domain(?n), \<exists>p\<in>P . \langle t,p\rangle\<in>?n \<and> p\<in>G}"
  proof -
    from asm and aux_VoN have
              "domain(?n) \<subseteq> ?r-``{?n}"
      by simp
    then have
              "\<forall>t\<in>domain(?n). (if t\<in>?r-``{?n} then val(G,t) else 0) = val(G,t)"
      by auto
    then show 
              "{ (if t\<in>?r-``{?n} then val(G,t) else 0) .. t\<in>domain(?n), \<exists>p\<in>P . \langle t,p\rangle\<in>?n \<and> p\<in>G} =
               { val(G,t) .. t\<in>domain(?n), \<exists>p\<in>P . \langle t,p\rangle\<in>?n \<and> p\<in>G}"
      by auto
  qed
  also have
              " ... = { val(G,t) .. t\<in>A, \<exists>p\<in>P . \langle t,p\rangle\<in>?n \<and> p\<in>G}"
    by force
  finally show
              " val(G,?n)  = { val(G,t) .. t\<in>A, \<exists>p\<in>P . Q(\langle t,p\rangle) \<and> p\<in>G}"
    by auto
qed

  
end    (*************** CONTEXT: forcing_data *****************)


end