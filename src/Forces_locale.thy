theory Forces_locale imports Interface Forcing_data Names begin

definition
  SepReplace :: "[i, i\<Rightarrow>i, i\<Rightarrow> o] \<Rightarrow>i" where
  "SepReplace(A,b,Q) == {y . x\<in>A, y=b(x) \<and> Q(x)}"
  
syntax
  "_SepReplace"  :: "[i, pttrn, i, o] => i"  ("(1{_ ../ _ \<in> _, _})")
translations
  "{b .. x\<in>A, Q}" => "CONST SepReplace(A, \<lambda>x. b, \<lambda>x. Q)"

lemma Sep_and_Replace: "{b(x) .. x\<in>A, P(x) } = {b(x) . x\<in>{y\<in>A. P(y)}}"
  by (auto simp add:SepReplace_def)

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

    
lemma "Hv(G,x,f) = { f`y .. y\<in> domain(x), \<exists>p\<in>P. <y,p> \<in> x \<and> p \<in> G }"
  by (simp add:Sep_and_Replace Hv_def Hval_def)  
    
lemma "val(G,{<t,p> .. <t,p>\<in>A\<times>B, Q(t,p)}) = {val(G,t) .. t\<in>A , p\<in>B & Q(t,p)}"
apply (simp add:SepReplace_def)
  oops
    
end    (*************** CONTEXT: forcing_data *****************)


  
(* Prototyping Forcing relation and theorems as a locale*)
locale forcing_thms = forcing_data +
  fixes forces :: "i \<Rightarrow> i"
  assumes definition_of_forces: "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                  sats(M,forces(\<phi>), [P,leq,uno,p] @ env) \<longleftrightarrow>
                  (\<forall>G.(generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],\<phi>,map(val(G),env)))"
      and  definability:     "\<phi>\<in>formula \<Longrightarrow> forces(\<phi>) \<in> formula"
      and   truth_lemma:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                 \<forall>G.(generic(G) \<and> p\<in>G)\<longrightarrow>
                  ((\<exists>p\<in>P.(sats(M,forces(\<phi>), [P,leq,uno,p] @ env))) \<longleftrightarrow>
                  (sats(M[G],\<phi>,map(val(G),env))))"
      and  streghtening:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> q\<in>P \<Longrightarrow> <q,p>\<in>leq \<Longrightarrow>
                               sats(M,forces(\<phi>), [P,leq,uno,p] @ env) \<Longrightarrow>
                               sats(M,forces(\<phi>), [P,leq,uno,q] @ env)"
      and density_lemma:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                    sats(M,forces(\<phi>), [P,leq,uno,p] @ env) \<longleftrightarrow> 
                    dense_below({q\<in>P. sats(M,forces(\<phi>), [P,leq,uno,q] @ env)},p)"

begin  (*************** CONTEXT: forcing_thms *****************)
  
lemma
  "a\<in>M \<Longrightarrow> b\<in>M \<Longrightarrow> env\<in>list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow>
  val(G,{x\<in>domain(\<pi>)\<times>P. \<exists>\<theta> p. x=<\<theta>,p> \<and> (\<forall>F. M_generic(F) \<and> p\<in>F \<longrightarrow>
         sats(M[F],\<phi>,[val(F,\<theta>),val(F,\<pi>),val(F,\<sigma>)]))})
 \<subseteq>
  {x\<in>val(G,\<pi>). sats(M[F],\<phi>,[val(F,\<theta>),val(F,\<pi>),val(F,\<sigma>)])} "
proof -
  have
              "val(G,{x\<in>domain(\<pi>)\<times>P. \<exists>\<theta> p. x=<\<theta>,p> \<and> (\<forall>F. M_generic(F) \<and> p\<in>F \<longrightarrow> 
               sats(M[F],\<phi>,[val(F,\<theta>),val(F,\<pi>),val(F,\<sigma>)]))}) = 
               {val(G,x) .. x\<in>domain(\<pi>)\<times>P, \<exists>\<theta> p. x=<\<theta>,p> \<and> (\<forall>F. M_generic(F) \<and> p\<in>F \<longrightarrow> 
               sats(M[F],\<phi>,[val(F,\<theta>),val(F,\<pi>),val(F,\<sigma>)]))}"  
              (is  "val(G,{x\<in>_. \<exists>\<theta> p. ?R(x,\<theta>,p) \<and> (\<forall>F. ?Q(F,p) \<longrightarrow> ?P(F,\<phi>,\<theta>,\<pi>,\<sigma>))}) = ?x")
  proof -
    have
              "val(G,{x\<in>domain(\<pi>)\<times>P. \<exists>\<theta> p. ?R(x,\<theta>,p) \<and> (\<forall>F. ?Q(F,p) \<longrightarrow> ?P(F,\<phi>,\<theta>,\<pi>,\<sigma>))}) =
                "
    
  oops
end    (*************** CONTEXT: forcing_thms *****************)

end