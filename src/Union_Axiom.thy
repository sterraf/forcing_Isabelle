theory Union_Axiom 
  imports Forcing_data Names  
begin

context forcing_data
begin


  (*
to  prove  that  whenever  a \<in> M[G),  there  is  b \<in>  M[G)  such  that  \<union> a  \<subseteq>  b. 
 Fix \<tau> \<in> M^P  such  that  a  = val(G,\<tau>),  let  \<pi> =  \<union> dom(\<tau>),  and  let  b = val(G,\<pi>). 

Note  that  \<tau>  is  a  set  of  pairs  of  the  form  (a,p),  and  dom(\<tau>)  is  just  the 
set  of  all  these  a's.  Then,  our  Definition  IV.2.5  (of  "name")  implies  that  the 
union  of  any  family  of  names  is  also  a  name,  so  \<pi> is a P-name,  and \<pi> \<in> M  by 
absoluteness  of \<union>,  so  b \<in>  M[G]. 

If  c \<in> a =  val(G,\<tau>),  then  c = val(G,\<sigma>) for  some  \<sigma> \<in> dom(\<tau>).  Then  \<sigma> \<subseteq> \<pi>,  
so,  applying Definition  IV.2.7,  c = val(G,\<sigma>) \<subseteq> val(G,\<pi>) = b.  Thus, \<union> a \<subseteq> b. 

Alternatively: \<pi>  ==  {(\<theta>,p)  : \<exists>(\<sigma>, q) \<in> \<tau> . \<exists> r. [(\<theta>,r) \<in> \<sigma> \<and> p \<le> r \<and> p  \<le> q}
And prove \<union>a=val(G,\<pi>)

*)
    
lemma Union_aux : 
  assumes "a \<in> M[G]"
  shows "\<exists> b \<in> M[G] . \<Union> a \<subseteq> b"
proof - 
    from \<open>a \<in> M[G]\<close> obtain \<tau> where
    "\<tau> \<in> M" "a = val(G,\<tau>)" "domain(\<tau>) \<in> M" and "\<Union> (domain(\<tau>)) \<in> M" (is "?\<pi> \<in> M")
    using GenExtD  domain_closed Union_closed by force
  then have "val(G,?\<pi>) \<in> M[G]" using GenExtI by simp
  {
    fix x
    assume "x \<in> val(G,\<tau>)"
    then obtain \<theta> p where
      "p \<in> G" "<\<theta>,p> \<in> \<tau>" "val(G,\<theta>) = x"
      using elem_of_val_pair by blast
    then have "\<theta> \<in> domain(\<tau>)" "\<theta> \<subseteq> ?\<pi>" using Union_upper by auto
    then have "val(G,\<theta>) \<subseteq> val(G,?\<pi>)" using val_mono by simp
    with \<open>val(G,\<theta>)=x\<close> have "x \<subseteq> val(G,?\<pi>)" by simp
  }
  with \<open>a=val(G,\<tau>)\<close> have "\<Union> a \<subseteq> val(G,?\<pi>)" (is "_ \<subseteq> ?b") using Union_subset_iff by auto
  with \<open>val(G,?\<pi>) \<in> M[G]\<close> show ?thesis by auto
qed

definition Union_name :: "i \<Rightarrow> i" where
  "Union_name(\<tau>) == 
    {<\<theta>,p> \<in> M \<times> P . \<exists> <\<sigma>,q> \<in> \<tau> . (\<exists> r \<in> P. <\<theta>,r> \<in> \<sigma> \<and> <p,r> \<in> leq \<and> <p,q> \<in> leq) }"

lemma Union_nameD : "<\<theta>,p> \<in> Union_name(\<tau>) \<Longrightarrow> 
   \<theta> \<in> M \<and> p \<in> P \<and> (\<exists> <\<sigma>,q> \<in> \<tau> . (\<exists> r \<in> P. <\<theta>,r> \<in> \<sigma> \<and> <p,r> \<in> leq \<and> <p,q> \<in> leq))"
  by(simp add:Union_name_def)
  
lemma Union_name_M : assumes "\<tau> \<in> M"
  shows "Union_name(\<tau>) \<in> M"
    (* We need to internalize the poset in order to use separation_closed. *)
  sorry 

lemma domD : assumes "\<tau> \<in> M" and "\<sigma> \<in> domain(\<tau>)"
  shows "\<sigma> \<in> M"
 proof - 
  from \<open>\<tau> \<in> M\<close> have "domain(\<tau>) \<in> M"
    using domain_closed by simp
  with \<open>\<sigma> \<in> domain(\<tau>)\<close> have "\<sigma> \<in> M" 
    using Transset_M trans_M by blast
  then show ?thesis by simp
qed
  
lemma Union_MG : 
  assumes "a \<in> M[G]" and "a = val(G,\<tau>)" and "filter(G)" and "\<tau> \<in> M"
  shows "\<Union> a = val(G,Union_name(\<tau>))"
proof -
  {
    fix x
    assume "x \<in> \<Union> (val(G,\<tau>))"
    then obtain i where "i \<in> val(G,\<tau>)" "x \<in> i" by blast
    with \<open>\<tau> \<in> M\<close> obtain \<sigma> q where
      "q \<in> G" "<\<sigma>,q> \<in> \<tau>" "val(G,\<sigma>) = i" "\<sigma> \<in> M" 
      using elem_of_val_pair domD by blast    
    with \<open>x \<in> i\<close> obtain \<theta> r where
      "r \<in> G" "<\<theta>,r> \<in> \<sigma>" "val(G,\<theta>) = x" "\<theta> \<in> M"
      using elem_of_val_pair domD by blast
    with \<open>filter(G)\<close> \<open>q\<in>G\<close> \<open>r\<in>G\<close> obtain p where
      "p \<in> G" "<p,r> \<in> leq" "<p,q> \<in> leq" "p \<in> P" "r \<in> P" "q \<in> P"
      using low_bound_filter filterD by blast    
    with \<open><\<theta>,r> \<in> \<sigma>\<close> \<open><\<sigma>,q> \<in> \<tau>\<close> \<open>\<sigma> \<in> M\<close> \<open>\<theta> \<in> M\<close> 
    have "<\<theta>,p> \<in> Union_name(\<tau>)" unfolding Union_name_def by force
    with \<open>p\<in>P\<close> \<open>p\<in>G\<close> have "val(G,\<theta>) \<in> val(G,Union_name(\<tau>))" 
      using val_of_elem by simp
    with \<open>val(G,\<theta>)=x\<close> have "x \<in> val(G,Union_name(\<tau>))" by simp
  }
  with \<open>a=val(G,\<tau>)\<close> have 1: "x \<in> \<Union> a \<Longrightarrow> x \<in> val(G,Union_name(\<tau>))" for x by simp
  from \<open>\<tau> \<in> M\<close> have U:"Union_name(\<tau>) \<in> M" using Union_name_M by simp
  {
    fix x
    assume "x \<in> (val(G,Union_name(\<tau>)))"
    then obtain \<theta> p where
      "p \<in> G" "<\<theta>,p> \<in> Union_name(\<tau>)" "val(G,\<theta>) = x"
      using elem_of_val_pair by blast
    from \<open><\<theta>,p> \<in> Union_name(\<tau>)\<close> have
      " \<exists> <\<sigma>,q> \<in> \<tau> . (\<exists> r \<in> P. <\<theta>,r> \<in> \<sigma> \<and> <p,r> \<in> leq \<and> <p,q> \<in> leq)"
      using Union_nameD by simp
    (* cómo sigue de acá? 
      tenemos (a) <\<sigma>,q> \<in> \<tau>
              (b) <\<theta>,r> \<in> \<sigma>
              (c) p \<le> r
              (d) p \<le> q
     de los últimos puntos sacamos (creciente,G\<subseteq>P) (e) r\<in>G,r\<in>P, q\<in>G,q\<in>P
     de (a) y (e) sacamos val(G,\<sigma>) \<in> val(G,\<tau>)
     de (b) y (e) sacamos val(G,\<theta>) \<in> val(G,\<sigma>)
     por lo tanto tenemos val(G,\<theta>) \<in> \<Union> val(G,\<tau>) = \<Union> a
    *)
  }
  oops     
        
lemma union_in_MG : "M_generic(G) \<Longrightarrow> Union_ax(##M[G])"
  sorry

end
end