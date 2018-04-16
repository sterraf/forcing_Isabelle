theory forces_locale imports Formula val_check ZFCaxioms begin

locale forcing_poset =
  fixes P leq uno
  assumes uno_in_P:         "uno \<in> P"
      and leq_preord:       "preorder_on(P,leq)"
      and uno_max:          "\<forall>p\<in>P. <p,uno>\<in>leq"

definition (in forcing_poset)
  dense :: "i\<Rightarrow>o" where
  "dense(D) == \<forall>p\<in>P. \<exists>d\<in>D . <d,p>\<in>leq"
    
definition (in forcing_poset)
  increasing :: "i\<Rightarrow>o" where
  "increasing(F) == \<forall>p\<in>P. \<forall>x\<in>P. x\<in>F \<and> <x,p>\<in>leq \<longrightarrow> p\<in>F"

definition (in forcing_poset)
  compat_in :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "compat_in(p,q,G) == \<exists>d\<in>G . <d,p>\<in>leq \<and> <d,q>\<in>leq" 
  
definition (in forcing_poset)
  compat :: "i\<Rightarrow>i\<Rightarrow>o" where
  "compat(p,q) == compat_in(p,q,P)"

definition (in forcing_poset)
  antichain :: "i\<Rightarrow>o" where
  "antichain(A) == A\<subseteq>P \<and> (\<forall>p\<in>A.\<forall>q\<in>A.(\<not>compat(p,q)))"

definition (in forcing_poset)
  filter :: "i\<Rightarrow>o" where
  "filter(G) == G\<subseteq>P \<and> increasing(G) \<and> (\<forall>p\<in>G. \<forall>q\<in>G. compat_in(p,q,G))"

definition (in forcing_poset) 
  up_closure :: "i\<Rightarrow>i" where
  "up_closure(A) == {p\<in>P.\<exists>a\<in>A.<a,p>\<in>leq}"

lemma (in forcing_poset) closure_compat_filter:
  "A\<subseteq>P \<Longrightarrow> (\<forall>p\<in>A.\<forall>q\<in>A. compat(p,q)) \<Longrightarrow> filter(up_closure(A))"
oops
    
lemma  (in forcing_poset) chain_compat:
  "A\<subseteq>P \<Longrightarrow> linear(A,leq) \<Longrightarrow>  (\<forall>p\<in>A.\<forall>q\<in>A. compat(p,q))"
oops

theorem Ord_dependent_choice:
    "Ord(A) \<Longrightarrow> \<forall>a\<in>A.\<exists>b\<in>A. <b,a> \<in> s  \<Longrightarrow>
     \<forall>x\<in>A.\<exists>f\<in>(nat\<rightarrow>A).f`0=x \<and> (\<forall>n\<in>nat.(<f`n,f`(n+1)>\<in> s))"
  apply (rule ballI)
  apply (rule bexI)
   apply (rule conjI)
  oops
    
theorem wo_dependent_choice:
    "well_ord(A,r) \<Longrightarrow> \<forall>a\<in>A.\<exists>b\<in>A. <b,a> \<in> s  \<Longrightarrow>
     \<forall>x\<in>A.\<exists>f\<in>(nat\<rightarrow>A).f`0=x \<and> (\<forall>n\<in>nat.(<f`n,f`(n+1)>\<in> s))"
  apply(drule well_ord_cardinal_eqpoll)
    subgoal 
  oops
    
locale countable_generic = forcing_poset +
  fixes \<D>
  assumes countable_subs_of_P:  "\<D> \<in> nat\<rightarrow>\<P>(P)"
  and     seq_of_denses:        "dense(\<D>`n)"

definition (in countable_generic)
  D_generic :: "i\<Rightarrow>o" where
  "D_generic(G) == filter(G) \<and> (\<forall>n\<in>nat.(\<D>`n)\<inter>G\<noteq>0)"

 
theorem (in countable_generic) rasiowa_sikorski: 
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> D_generic(G)"
oops
  
locale forcing_data = forcing_poset +
  fixes M enum
  assumes trans_M:          "Transset(M)"
      and M_model_ZF:       "satT(M,ZFTh,[])"
      and M_countable:      "enum\<in>bij(nat,M)"
      and P_in_M:           "P \<in> M"

definition (in forcing_data)
  generic :: "i\<Rightarrow>o" where
  "generic(G) == filter(G) \<and> (\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"
      
(* Prototyping Forcing relation and theorems as a locale*)
locale forcing_thms = forcing_poset + forcing_data +
  fixes forces :: "i \<Rightarrow> i"
  assumes definition_of_forces: "\<forall>env\<in>list(M).
                  sats(M,forces(\<phi>), [P,leq,uno,p] @ env) \<longleftrightarrow>
                  (\<forall>G.(generic(G)\<and> p\<in>G)\<longrightarrow>sats(gen_ext(M,P,G),\<phi>,map(valR(M,P,G),env)))"
      and definability:      "forces(\<phi>) \<in> formula"
      and truth_lemma:      "\<forall>env\<in>list(M).\<forall>G.(generic(G) \<and> p\<in>G)\<longrightarrow>
                  ((\<exists>p\<in>P.(sats(M,forces(\<phi>), [P,leq,uno,p] @ env))) \<longleftrightarrow>
                  (sats(gen_ext(M,P,G),\<phi>,map(valR(M,P,G),env))))"

lemma (in forcing_thms) bounded_separation_in_genext:
    "\<forall>p\<in>formula. arity(p)<5 \<longrightarrow> sats(gen_ext(M,P,G),ZFSeparation(p),[])"
oops

theorem (in forcing_thms) separation_in_genext:
    "\<forall>p\<in>formula. sats(gen_ext(M,P,G),ZFSeparation(p),[])"
oops
end