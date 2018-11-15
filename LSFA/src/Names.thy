(*
----------------------------------------------
First steps towards a formalization of Forcing
---------------------------------------------

Definition of Generic extension of a model M of ZFC: M[G].
Definition of function val and check, and properties about them.

*)

theory Names imports Forcing_data begin

lemma transD : "Transset(M) \<Longrightarrow> y \<in> M \<Longrightarrow> y \<subseteq> M" 
  by (unfold Transset_def, blast) 

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

    
lemma SepReplace_dom_implies :
   "\<forall>x\<in>A. b(x) = b'(x)\<Longrightarrow> {b(x) .. x\<in>A, Q(x)}={b'(x) .. x\<in>A, Q(x)}"
  by  (simp add:SepReplace_def)
    
lemma SepReplace_pred_implies :
   "\<forall>x. Q(x)\<longrightarrow> b(x) = b'(x)\<Longrightarrow> {b(x) .. x\<in>A, Q(x)}={b'(x) .. x\<in>A, Q(x)}"
  by  (force simp add:SepReplace_def)
   
text\<open>The well founded relation on which @{term val} is defined\<close>

definition
  ed :: "[i,i] \<Rightarrow> o" where
  "ed(x,y) == x \<in> domain(y)"
  
definition
  edrel :: "i \<Rightarrow> i" where
  "edrel(A) == {<x,y> \<in> A*A . x \<in> domain(y)}"

lemma edrelI [intro!]: "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> <x,y>\<in>edrel(A)"
  by (simp add:edrel_def)
    
lemma edrelD [dest] : "<x,y>\<in>edrel(A)\<Longrightarrow> x \<in> domain(y)"
  by (simp add:edrel_def)
    
lemma edrel_trans: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> <x,y>\<in>edrel(A)"
   by (rule edrelI, auto simp add:Transset_def domain_def Pair_def)

lemma edrel_trans_iff: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<longleftrightarrow> <x,y>\<in>edrel(A)"
  by (auto simp add: edrel_trans, auto simp add:Transset_def Pair_def)

lemma edrel_domain: "x\<in> M \<Longrightarrow> edrel(eclose(M)) -`` {x} = domain(x)"
  apply (rule equalityI, auto , subgoal_tac "Transset(eclose(M))", rule vimageI)
    apply (auto simp add: edrelI Transset_eclose)
   apply (rename_tac y z)
   apply (rule_tac A="{y}" in ecloseD)
    apply (rule_tac A="\<langle>y, z\<rangle>" in ecloseD)
    apply (rule_tac A="x" in ecloseD)
     apply (tactic {* distinct_subgoals_tac *})
    apply (auto simp add: Pair_def arg_into_eclose)
  done

lemma domain_trans: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> x\<in>A"
  by (auto simp add: Transset_def domain_def Pair_def)
    
lemma edrel_sub_memrel: "edrel(A) \<subseteq> trancl(Memrel(eclose(A)))" 
proof
  fix z
  assume
              "z\<in>edrel(A)"
  then obtain x y where
       Eq1:   "x\<in>A" "y\<in>A" "z=<x,y>" "x\<in>domain(y)"
    by (auto simp add: edrel_def)
  then obtain u v where
       Eq2:   "x\<in>u" "u\<in>v" "v\<in>y"
    unfolding domain_def Pair_def by auto
  with Eq1 have
       Eq3:   "x\<in>eclose(A)" "y\<in>eclose(A)" "u\<in>eclose(A)" "v\<in>eclose(A)"
    by (auto, rule_tac [3-4] ecloseD, rule_tac [3] ecloseD, simp_all add:arg_into_eclose)
  let
              ?r="trancl(Memrel(eclose(A)))"
  from Eq2 and Eq3 have
              "<x,u>\<in>?r" "<u,v>\<in>?r" "<v,y>\<in>?r"
    by (auto simp add: r_into_trancl)
  then  have
              "<x,y>\<in>?r"
    by (rule_tac trancl_trans, rule_tac [2] trancl_trans, simp)
  with Eq1 show "z\<in>?r" by simp
qed
  
lemma wf_edrel : "wf(edrel(A))"
  apply (rule_tac wf_subset [of "trancl(Memrel(eclose(A)))"])
  apply (auto simp add:edrel_sub_memrel wf_trancl wf_Memrel)
  done
    
lemma eq_sub_trans :  "x=y \<Longrightarrow> y\<subseteq>z \<Longrightarrow> x\<subseteq>z"
                "x\<subseteq>y \<Longrightarrow> y=z \<Longrightarrow> x\<subseteq>z"
  by simp_all
    
    
lemma SepReplace_iff [simp]: "y\<in>{b(x) .. x\<in>A, P(x)} \<longleftrightarrow> (\<exists>x\<in>A. y=b(x) & P(x))"
   by (auto simp add:SepReplace_def)

    
context forcing_data
begin  (*************** CONTEXT: forcing_data *****************)

definition 
  Hcheck :: "[i,i] \<Rightarrow> i" where
  "Hcheck(z,f)  == { <f`y,one> . y \<in> z}"

definition
  check :: "i \<Rightarrow> i" where
  "check(x) == wfrec(Memrel(eclose({x})), x , Hcheck)"

lemma  aux_def_check:
  "(\<lambda>x\<in>y. wfrec(Memrel(eclose({y})), x, Hcheck)) = 
   (\<lambda>x\<in>y. wfrec(Memrel(eclose({x})), x, Hcheck))"
  apply (rule lam_cong)
   defer 1 apply (rule wfrec_eclose_eq)
    defer 1 apply (rule ecloseD, auto simp add: arg_into_eclose)
  done
    
lemma def_check : "check(y) = { <check(w),one> . w \<in> y}"
proof -
  let 
              ?r="\<lambda>y. Memrel(eclose({y}))"
  from wf_Memrel have
       wfr:   "\<forall>w . wf(?r(w))" ..
  with wfrec [of "?r(y)" y "Hcheck"] have
              "check(y)= 
               Hcheck( y, \<lambda>x\<in>?r(y) -`` {y}. wfrec(?r(y), x, Hcheck))"
    by (simp add:check_def)
  also have 
              " ... = Hcheck( y, \<lambda>x\<in>y. wfrec(?r(y), x, Hcheck))"
    by (simp add:under_Memrel_eclose arg_into_eclose)
  also have 
              " ... = Hcheck( y, \<lambda>x\<in>y. check(x))"
    using aux_def_check by (simp add:check_def)
  finally show ?thesis by (simp add:Hcheck_def)
qed

definition
  Hv :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i" where
  "Hv(G,x,f) == { f`y .. y\<in> domain(x), \<exists>p\<in>P. <y,p> \<in> x \<and> p \<in> G }"

definition
  val :: "i\<Rightarrow>i\<Rightarrow>i" where
  "val(G,\<tau>) == wfrec(edrel(eclose(M)), \<tau> ,Hv(G))"

definition
  GenExt :: "i\<Rightarrow>i"     ("M[_]" 90)
  where "GenExt(G)== {val(G,\<tau>). \<tau> \<in> M}"
  
lemma def_val:  "x\<in>M \<Longrightarrow> val(G,x) = {val(G,t) .. t\<in>domain(x) , \<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>x \<and> p \<in> G }"
proof -
  assume
      asm:  "x\<in>M"
  let
            ?r="edrel(eclose(M))"
  let
            ?f="\<lambda>z\<in>?r-``{x}. wfrec(?r,z,Hv(G))"
  have
            "\<forall>\<tau>. wf(?r)"
    by (simp add: wf_edrel)
  with wfrec [of "?r" x "Hv(G)"] have
            "val(G,x) = Hv(G,x,?f)"
    by (simp add:val_def)
  also have
            " ... = Hv(G,x,\<lambda>z\<in>domain(x). wfrec(?r,z,Hv(G)))"
    using asm and edrel_domain by (simp) 
  also have
            " ... = Hv(G,x,\<lambda>z\<in>domain(x). val(G,z))"
    by (simp add:val_def)
  finally show ?thesis by (simp add:Hv_def SepReplace_def)
qed

lemma elem_of_val: "\<lbrakk> x\<in>val(G,\<pi>) ; \<pi> \<in> M \<rbrakk> \<Longrightarrow> \<exists>\<theta>\<in>domain(\<pi>). val(G,\<theta>) = x"
  by (subst (asm) def_val,auto)

lemma elem_of_val_pair: "\<lbrakk> x\<in>val(G,\<pi>) ; \<pi> \<in> M \<rbrakk> \<Longrightarrow> \<exists>\<theta>. \<exists>p\<in>G.  <\<theta>,p>\<in>\<pi> \<and> val(G,\<theta>) = x"
  by (subst (asm) def_val,auto)
  
lemma GenExtD: 
  "x \<in> M[G] \<Longrightarrow> \<exists>\<tau>\<in>M. x = val(G,\<tau>)"
  by (simp add:GenExt_def)
    
lemma GenExtI: 
  "x \<in> M \<Longrightarrow> val(G,x) \<in> M[G]"
  by (auto simp add: GenExt_def)
  
lemma val_of_name : 
  "{x\<in>A\<times>P. Q(x)} \<in> M \<Longrightarrow>
   val(G,{x\<in>A\<times>P. Q(x)}) = {val(G,t) .. t\<in>A , \<exists>p\<in>P .  Q(<t,p>) \<and> p \<in> G }"
proof -
  let
              ?n="{x\<in>A\<times>P. Q(x)}" and
              ?r="edrel(eclose(M))"
  assume
        asm:  "?n \<in> M"
  let
              ?f="\<lambda>z\<in>?r-``{?n}. val(G,z)"
  have
              "\<forall>\<tau>. wf(?r)"
    by (simp add: wf_edrel)
  with val_def have
              "val(G,?n) = Hv(G,?n,?f)"
    by (rule_tac def_wfrec [of _ "?r" "Hv(G)"], simp_all)
  also have
              "... = {?f`t .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
    unfolding Hv_def by simp
  also have
              "... = { (if t\<in>?r-``{?n} then val(G,t) else 0) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
    by (simp)
  also have
        Eq1:  "... = { val(G,t) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
  proof -
    from edrel_domain and asm have
              "domain(?n) \<subseteq> ?r-``{?n}" 
      by simp
    then have
              "\<forall>t\<in>domain(?n). (if t\<in>?r-``{?n} then val(G,t) else 0) = val(G,t)"
      by auto
    then show 
              "{ (if t\<in>?r-``{?n} then val(G,t) else 0) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G} =
               { val(G,t) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
      by auto
  qed
  also have
              " ... = { val(G,t) .. t\<in>A, \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
   by force 
  finally show
              " val(G,?n)  = { val(G,t) .. t\<in>A, \<exists>p\<in>P . Q(<t,p>) \<and> p\<in>G}"
    by auto
qed

lemma valcheck : "y \<in> M \<Longrightarrow> one \<in> G \<Longrightarrow> \<forall>x\<in>M. check(x) \<in> M \<Longrightarrow> val(G,check(y))  = y"
proof (induct rule:eps_induct)
  case (1 y)
  then show ?case
  proof -
    from def_check have
          Eq1: "check(y) = { \<langle>check(w), one\<rangle> . w \<in> y}"  (is "_ = ?C") .
    with 1 have
          Eq2: "?C\<in>M" 
      by auto
    with 1 transD subsetD trans_M have 
        w_in_M : "\<forall> w \<in> y . w \<in> M" by force
    from Eq1 have
               "val(G,check(y)) = val(G, {\<langle>check(w), one\<rangle> . w \<in> y})"
      by simp
    also have
                " ...  = {val(G,t) .. t\<in>domain(?C) , \<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>?C \<and> p \<in> G }"
      using def_val and Eq2 by simp
    also have
                " ... =  {val(G,t) .. t\<in>domain(?C) , \<exists>w\<in>y. t=check(w) }"
      using 1 and one_in_P by simp
    also have
                " ... = {val(G,check(w)) . w\<in>y }"
      by force
    also have
                " ... = y"
      using 1 and w_in_M by simp        
    finally show "val(G,check(y)) = y" 
      using 1 by simp
  qed
qed
  
(* M[G] is transitive *)
lemma trans_Gen_Ext' :
  assumes "vc \<in> M[G]"
    "y \<in> vc" 
  shows
    "y \<in> M[G]" 
proof -
  from \<open>vc\<in>M[G]\<close> have
    "\<exists>c\<in>M. vc = val(G,c)"
    by (blast dest:GenExtD)
  then obtain c where
    "c\<in>M" "vc = val(G,c)" by auto
  with \<open>vc \<in> M[G]\<close> have
    "val(G,c)\<in>M[G]" by simp
  from \<open>y \<in> vc\<close> and \<open>vc = val(G,c)\<close> have
    "y \<in> val(G,c)" by simp
  with \<open>c\<in>M\<close> and elem_of_val have
    "\<exists>\<theta>\<in>domain(c). val(G,\<theta>) = y" by simp
  then obtain \<theta> where
    "\<theta>\<in>domain(c)" "val(G,\<theta>) = y" by auto
  from \<open>\<theta>\<in>domain(c)\<close> trans_M \<open>c\<in>M\<close> domain_trans have
    "\<theta>\<in>M" by simp
  then have
    "val(G,\<theta>) \<in> M[G]" 
    by (blast intro:GenExtI)
  with \<open>val(G,\<theta>) = y\<close> show ?thesis by simp
qed
  
lemma trans_Gen_Ext:
  "Transset(M[G])"
  by (auto simp add: Transset_def trans_Gen_Ext')

lemma val_of_elem: 
  assumes 
    "<\<theta>,p> \<in> \<pi>" "\<pi>\<in>M" "p\<in>G" "p\<in>P"
  shows
    "val(G,\<theta>) \<in> val(G,\<pi>)"
proof - 
  from \<open>\<pi>\<in>M\<close> have 
    1:"val(G,\<pi>) = {val(G,t) .. t\<in>domain(\<pi>) , \<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>\<pi> \<and> p \<in> G }"
    using def_val by simp
  from \<open><\<theta>,p> \<in> \<pi>\<close> have "\<theta>\<in>domain(\<pi>)" by auto
  with \<open>p\<in>G\<close> \<open>p\<in>P\<close> \<open>\<theta>\<in>domain(\<pi>)\<close> \<open><\<theta>,p> \<in> \<pi>\<close> have
    "val(G,\<theta>) \<in> {val(G,t) .. t\<in>domain(\<pi>) , \<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>\<pi> \<and> p \<in> G }"
    by auto
  with 1 show ?thesis by simp
qed

end

(* definitions from Relative by Paulson *)
definition
  upair :: "[i=>o,i,i,i] => o" where
    "upair(M,a,b,z) == a \<in> z & b \<in> z & (\<forall>x[M]. x\<in>z \<longrightarrow> x = a | x = b)"
  
definition
  upair_ax :: "(i=>o) => o" where
    "upair_ax(M) == \<forall>x[M]. \<forall>y[M]. \<exists>z[M]. upair(M,x,y,z)"

definition
  univalent :: "[i=>o, i, [i,i]=>o] => o" where
    "univalent(M,A,P) ==
        \<forall>x[M]. x\<in>A \<longrightarrow> (\<forall>y[M]. \<forall>z[M]. P(x,y) & P(x,z) \<longrightarrow> y=z)"

definition
  strong_replacement :: "[i=>o, [i,i]=>o] => o" where
    "strong_replacement(M,P) ==
      \<forall>A[M]. univalent(M,A,P) \<longrightarrow>
      (\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x\<in>A & P(x,b)))"

lemma univalent_triv [intro,simp]:
     "univalent(M, A, \<lambda>x y. y = f(x))"
by (simp add: univalent_def)

    
(* G \<in> M[G] *)
locale M_extra_assms = forcing_data +
  assumes
        check_in_M : "\<And>x. x \<in> M \<Longrightarrow> check(x) \<in> M"
    and upair_ax:         "upair_ax(##M)"
    and repl_check_pair : "strong_replacement(##M,\<lambda>p y. y =<check(p),p>)"
    
begin
  
lemma Transset_intf :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)


lemma upair_abs [simp]:
     "z\<in>M ==> upair(##M,a,b,z) \<longleftrightarrow> z={a,b}"
  apply (simp add: upair_def)
  apply (insert trans_M)
  apply (blast intro: Transset_intf)
done

lemma upairM : "x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> {x,y} \<in> M"
  by(insert upair_ax, auto simp add: upair_ax_def)
    
lemma pairM : "x \<in>  M \<Longrightarrow> y \<in> M \<Longrightarrow> <x,y> \<in> M"
  by(unfold Pair_def, rule upairM,(rule upairM,simp+)+)

lemma univalent_Replace_iff:
     "[| A\<in>M; univalent(##M,A,Q);
         !!x y. [| x\<in>A; Q(x,y) |] ==> y\<in>M |]
      ==> u \<in> Replace(A,Q) \<longleftrightarrow> (\<exists>x. x\<in>A & Q(x,u))"
  apply (simp add: Replace_iff univalent_def)
  apply (insert trans_M)
  apply (blast dest: Transset_intf)
done

lemma strong_replacement_closed [intro,simp]:
     "[| strong_replacement(##M,Q); A\<in>M; univalent(##M,A,Q);
         !!x y. [| x\<in>A; Q(x,y) |] ==> y\<in>M |] ==> (Replace(A,Q)\<in>M)"
  apply (simp add: strong_replacement_def)
  apply (drule_tac x=A in bspec, safe)
  apply (subgoal_tac "Replace(A,Q) = Y")
   apply simp
  apply (rule equality_iffI)
  apply (simp add: univalent_Replace_iff)
  apply (insert trans_M)
  apply (blast dest: Transset_intf)
done
    
lemma P_sub_M : "P \<subseteq> M"
  by (simp add: P_in_M trans_M transD)

    
definition
  G_dot :: "i" where
  "G_dot == {<check(p),p> . p\<in>P}"
  
lemma G_dot_in_M :
    "G_dot \<in> M" 
proof -
  have 0:"G_dot = { y . p\<in>P , y = <check(p),p> }"
    unfolding G_dot_def by auto
  from P_in_M check_in_M pairM P_sub_M have "\<And> p . p\<in>P \<Longrightarrow> <check(p),p> \<in> M" 
    by auto
  then have
    1:"\<And>x y. \<lbrakk> x\<in>P ; y = <check(x),x> \<rbrakk> \<Longrightarrow> y\<in>M"
    by simp
  then have
    "\<forall>A\<in>M.(\<exists>Y\<in>M. \<forall>b\<in>M. b \<in> Y \<longleftrightarrow> (\<exists>x\<in>M. x\<in>A & b = <check(x),x>))"
    using repl_check_pair unfolding strong_replacement_def by simp
  then have
    "(\<exists>Y\<in>M. \<forall>b\<in>M. b \<in> Y \<longleftrightarrow> (\<exists>x\<in>M. x\<in>P & b = <check(x),x>))"
    using P_in_M by simp
  with 1 repl_check_pair P_in_M strong_replacement_closed have
    "{ y . p\<in>P , y = <check(p),p> } \<in> M" by simp
  then show ?thesis using 0 by simp
qed
  
lemma val_G_dot :
  assumes "G \<subseteq> P"
    "one \<in> G" 
  shows "val(G,G_dot) = G"
proof (intro equalityI subsetI) 
  fix x
  assume "x\<in>val(G,G_dot)"
  then have 
      "\<exists>\<theta>. \<exists>p\<in>G.  <\<theta>,p>\<in>G_dot \<and> val(G,\<theta>) = x"
    using G_dot_in_M elem_of_val_pair by simp
  then obtain r p where 
    "p\<in>G" "<r,p> \<in> G_dot" "val(G,r) = x" 
    by auto
  then have
    "r = check(p)" 
    unfolding G_dot_def by simp
  with \<open>one\<in>G\<close> \<open>G\<subseteq>P\<close> \<open>p\<in>G\<close> \<open>val(G,r) = x\<close> show
      "x \<in> G" 
    using valcheck P_sub_M  check_in_M by auto
next
  fix p
  assume "p\<in>G" 
  have "\<forall>q\<in>P. <check(q),q> \<in> G_dot" 
    unfolding G_dot_def by simp
  with \<open>p\<in>G\<close> \<open>G\<subseteq>P\<close> have
    "val(G,check(p)) \<in> val(G,G_dot)"
    using val_of_elem G_dot_in_M by blast
  with \<open>p\<in>G\<close> \<open>G\<subseteq>P\<close> \<open>one\<in>G\<close> show
    "p \<in> val(G,G_dot)" 
    using P_sub_M check_in_M valcheck by auto
qed
  
  
lemma G_in_Gen_Ext :
  assumes "G \<subseteq> P"
    "one \<in> G"
  shows   "G \<in> M[G]" 
proof -
  from G_dot_in_M have
    "val(G,G_dot) \<in> M[G]" 
    by (auto intro:GenExtI)
  with assms val_G_dot 
  show ?thesis by simp
qed

  
end    (*************** CONTEXT: forcing_data *****************)

end