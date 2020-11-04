theory New_Discipline_Draft
  imports
    "Discipline_Base"
    "Discipline_Function"
    Least
begin

declare [[syntax_ambiguity_warning = false]]


text\<open>
Disciplina de Relativización.

En la teoría de conjuntos pura no podemos construir términos, sino
que cada concepto sobre conjuntos está caracterizado por una fórmula de
primer orden. Trabajar de esa manera es por demás impráctico, por lo que
en la teoría Isabelle/ZF se definen algunos términos básicos a partir de los
cuales se pueden construir otros. Los términos "viven" en el universo "i", que
está implementado como un tipo de datos de Isabelle. 


Cuando Paulson necesitó probar resultados relativos a una clase, lo hizo
del modo full relacional, es decir, sin términos, sino que expresando cada
concepto con una fórmula de primer orden. Consideremos como ejemplo los pares
ordenados, que en Isabelle/ZF están definidos mediante

definition Pair :: "[i, i] => i"
  where "Pair(a,b) == {{a,a}, {a,b}}"

y la versión relativa definida por Paulson:

definition
  pair :: "[i=>o,i,i,i] => o" where
    "pair(M,a,b,z) == \<exists>x[M]. upair(M,a,a,x) &
                     (\<exists>y[M]. upair(M,a,b,y) & upair(M,x,y,z))"

Cuando un concepto es *absoluto*, podemos utilizar equivalentemente
la versión definida originalmente en I/ZF y la full-relacional. Por lo
tanto los resultados dentro y fuera del modelo se obtienen de la misma manera.

Sin embargo cuando tenemos conceptos que no son equivalentes dentro y 
fuera del modelo, tenemos problemas para obtener resultados. 
Consideremos f :: i => i, y alguna propiedad P(f) :: o. Si queremos obtener
la versión de P relativa a M, en el diseño de Paulson deberíamos dar la
versión full-relacional relativa de f, is_f :: [i=>o,i,i] => o, y luego
traducir la prueba de P(f), en una P'(is_f). No queremos hacer ese trabajo.

La idea de la "disciplina de relativización consiste en obtener para cada
término f :: i => i, un término f_rel :: [i=>o,i] => i que se corresponda con
f, obteniendo el mismo resultado pero restringido a una clase M :: i=>o.

Para ello, partimos de un core de relativizaciones de conceptos básicos
donde para cada concepto 

   f = t(h)

tenemos su correspondiente is_f, tal como lo
hace Paulson, y luego obtenemos f_rel a partir de este último, probando
la equivalencia

     is_f(M,x,y) <--> y = f_rel(M,x)

y un lema de definición
     f_rel(M,x) = t_rel(h_rel)

Una vez que tenemos ese core de definiciones básicas, podemos obtener
nuevos términos relativos simplemente definiendo cada nuevo término
de la misma manera en que está definido el término original, aplicando
la versión relativa de cada uno de los subtérminos. 
De esta manera podemos copiar todas las pruebas hechas para los términos
originales, reemplazando aquellos que no sean absolutos por sus
versiones _rel.

Debemos además dar la versión full-relacional de cada término ya que
en nuestro diseño de forcing tenemos que utilizar fórmulas internalizadas
y ahí no escapamos del problema. 

La nueva disciplina obtiene la versión full-relacional a partir
de la definición f_rel.
A continuación un ejemplo.
\<close>



text\<open>Consideremos el término \<^term>\<open>cardinal\<close>.


Lo que debemos hacer es definir su versión relativa simplemente
"mapeando" la _función de relativización_ sobre todos los subtérminos
que no sean absolutos:
\<close>

definition
  cardinal_rel :: "[i\<Rightarrow>o,i] \<Rightarrow> i" where
  "cardinal_rel(M,x) \<equiv> (\<mu> i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> x)"

abbreviation
  cardinal_r :: "[i,i\<Rightarrow>o] \<Rightarrow> i" (\<open>|_|\<^bsup>_\<^esup>\<close>) where
  "|x|\<^bsup>M\<^esup> \<equiv> cardinal_rel(M,x)"

abbreviation
  cardinal_r_set :: "[i,i]\<Rightarrow>i"  (\<open>|_|\<^bsup>_\<^esup>\<close>) where
  "|x|\<^bsup>M\<^esup> \<equiv> cardinal_rel(##M,x)"


text\<open>Probamos el lema closed\<close>

lemma (in M_trivial) cardinal_rel_closed: "M(x) \<Longrightarrow> M(|x|\<^bsup>M\<^esup>)"
  using Least_closed'[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> x"]
  unfolding cardinal_rel_def
  by simp

text\<open>Damos la versión full-relacional (se podrá calcular
automáticamente)\<close>
definition
  is_cardinal :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_cardinal(M,x,c) \<equiv> least(M, \<lambda>i. M(i) \<and> eqpoll_rel(M,i,x), c)"


text\<open>Y probamos la equivalencia entre la versión full-relacional
y el concepto relativo\<close>
lemma (in M_trivial) is_cardinal_iff :
  assumes "M(x)" "M(c)"
  shows "is_cardinal(M,x,c) \<longleftrightarrow> c = |x|\<^bsup>M\<^esup>"
  using assms least_abs'[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> x"]
  unfolding is_cardinal_def cardinal_rel_def
  by simp

text\<open>Esa es toda la disciplina.\<close>


definition
  Card_rel     :: "[i\<Rightarrow>o,i]\<Rightarrow>o"  (\<open>Card\<^bsup>_\<^esup>'(_')\<close>) where
  "Card\<^bsup>M\<^esup>(i) \<equiv> i = |i|\<^bsup>M\<^esup>"

definition 
  InfCard_rel   :: "[i\<Rightarrow>o,i] \<Rightarrow> o" (\<open>InfCard\<^bsup>_\<^esup>'(_')\<close>) where
  "InfCard_rel(M,i) \<equiv> Card\<^bsup>M\<^esup>(i) \<and> nat \<le> i"

definition
  cadd_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i"  where
  "cadd_rel(M,A,B) \<equiv> |A+B|\<^bsup>M\<^esup>"

abbreviation
  cadd_r :: "[i,i\<Rightarrow>o,i] \<Rightarrow> i" (\<open>_ \<oplus>\<^bsup>_\<^esup> _\<close> [66,1,66] 65) where
  "A \<oplus>\<^bsup>M\<^esup> B \<equiv> cadd_rel(M,A,B)"

lemma (in M_basic) cadd_rel_closed: 
  "\<lbrakk> M(A);M(B) \<rbrakk> \<Longrightarrow> M(A \<oplus>\<^bsup>M\<^esup> B)"
  using cardinal_rel_closed
  unfolding cadd_rel_def
  by simp


(* relativization *)
definition
  is_cadd :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_cadd(M,A,B,a) \<equiv> \<exists>s[M]. is_sum(M,A,B,s) \<and> is_cardinal(M,s,a)"

lemma (in M_basic) is_cadd_iff :
  assumes "M(A)" "M(B)" "M(a)"
  shows "is_cadd(M,A,B,a) \<longleftrightarrow> a = A \<oplus>\<^bsup>M\<^esup> B"
  using is_cardinal_iff assms 
  unfolding is_cadd_def cadd_rel_def
  by simp

definition
  cmult_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i"  where
  "cmult_rel(M,A,B) \<equiv> |A\<times>B|\<^bsup>M\<^esup>"

abbreviation
  cmult_r :: "[i,i\<Rightarrow>o,i] \<Rightarrow> i" (\<open>_ \<otimes>\<^bsup>_\<^esup> _\<close> [66,1,66] 65) where
  "A \<otimes>\<^bsup>M\<^esup> B \<equiv> cmult_rel(M,A,B)"

lemma (in M_basic) cmult_rel_closed: 
  "\<lbrakk> M(A);M(B) \<rbrakk> \<Longrightarrow> M(A \<otimes>\<^bsup>M\<^esup> B)"
  using cardinal_rel_closed
  unfolding cmult_rel_def
  by simp

(* relativization *)
definition
  is_cmult :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_cmult(M,A,B,m) \<equiv> \<exists>p[M]. cartprod(M,A,B,p) \<and> is_cardinal(M,p,m)"

lemma (in M_basic) is_cmult_iff :
  assumes "M(A)" "M(B)" "M(a)"
  shows "is_cmult(M,A,B,a) \<longleftrightarrow> a = A \<otimes>\<^bsup>M\<^esup> B"
  using is_cardinal_iff assms 
  unfolding is_cmult_def cmult_rel_def
  by simp

definition
  Powapply_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" (\<open>Powapply\<^bsup>_\<^esup>'(_,_')\<close>) where
  "Powapply\<^bsup>M\<^esup>(f,y) \<equiv> Pow\<^bsup>M\<^esup>(f`y)"

lemma (in M_basic) Powapply_rel_closed: 
  "\<lbrakk> M(f);M(y) \<rbrakk> \<Longrightarrow> M(Powapply\<^bsup>M\<^esup>(f,y))"
  using Pow_rel_closed
  unfolding Powapply_rel_def
  by simp

(* relativization *)
definition
  is_Powapply :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_Powapply(M,f,y,p) \<equiv> \<exists>fy[M]. fun_apply(M,f,y,fy) \<and> is_Pow(M,fy,p)"

lemma (in M_basic) is_Powapply_iff :
  assumes "M(f)" "M(y)" "M(p)"
  shows "is_Powapply(M,f,y,p) \<longleftrightarrow> p = Powapply\<^bsup>M\<^esup>(f,y)"
  using Pow_rel_iff assms 
  unfolding is_Powapply_def Powapply_rel_def
  by simp

definition
  HVfrom_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" (\<open>HVfrom\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "HVfrom\<^bsup>M\<^esup>(A,x,f) \<equiv> A \<union> (\<Union>y\<in>x. Powapply\<^bsup>M\<^esup>(f,y))"

(* relativization *)
definition
  is_HVfrom :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_HVfrom(M,A,x,f,z) \<equiv> (\<exists>u[M]. \<exists>hr[M]. is_Replace(M,x,is_Powapply(M,f),hr) \<and> 
                          big_union(M,hr,u) \<and> union(M,A,u,z))"

locale M_HVfrom = M_eclose + 
  assumes 
    Powapply_replacement : 
      "M(K) \<Longrightarrow> strong_replacement(M,\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y))"

begin

lemma univalent_is_Powapply:
  assumes "M(A)" "M(K)"
  shows "univalent(M,A,is_Powapply(M,K))"
  using assms is_Powapply_iff  unfolding univalent_def
  by simp

lemma is_HVfrom_iff :
  assumes "M(A)" "M(x)" "M(f)" "M(z)"
  shows "is_HVfrom(M,A,x,f,z) \<longleftrightarrow> z = HVfrom\<^bsup>M\<^esup>(A,x,f)"
proof -
  have "is_Replace(M,x,\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y),r) \<longleftrightarrow> r = {z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}"
    if "M(r)" for r
    using assms that Powapply_rel_closed 
          Replace_abs[of x r "\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y)"] transM[of _ x]
    by simp
  moreover
  have "is_Replace(M,x,is_Powapply(M,f),r) \<longleftrightarrow> 
        is_Replace(M,x,\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y),r)" if "M(r)" for r
    using assms that is_Powapply_iff is_Replace_cong 
    by simp
  ultimately
  have "is_Replace(M,x,is_Powapply(M,f),r) \<longleftrightarrow> r = {z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}"
    if "M(r)" for r
    using that assms 
    by simp
  moreover
  have "M({z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)})" 
    using assms strong_replacement_closed[OF Powapply_replacement] 
          Powapply_rel_closed transM[of _ x]
    by simp
  ultimately
  show ?thesis
  using assms 
  unfolding is_HVfrom_def HVfrom_rel_def
  by auto
qed


lemma HVfrom_rel_closed: 
  assumes "M(A)" "M(x)" "M(f)"
  shows "M(HVfrom\<^bsup>M\<^esup>(A,x,f))"
proof -
  have "M({z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)})" 
    using assms strong_replacement_closed[OF Powapply_replacement] 
          Powapply_rel_closed transM[of _ x]
    by simp
  then 
  have "M(A \<union> \<Union>({z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}))"
    using assms
    by simp
  moreover
  have "A \<union> \<Union>({z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}) =
        HVfrom\<^bsup>M\<^esup>(A,x,f)" 
    unfolding HVfrom_rel_def
    by auto
  ultimately
  show ?thesis
    using assms
    unfolding HVfrom_rel_def 
    by simp    
qed

end (* context M_HVfrom *)

definition
  Vfrom_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" (\<open>Vfrom\<^bsup>_\<^esup>'(_,_')\<close>) where
  "Vfrom\<^bsup>M\<^esup>(A,i) = transrec(i, HVfrom_rel(M,A))"

(* relativization *)
definition
  is_Vfrom :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_Vfrom(M,A,i,z) \<equiv> is_transrec(M,is_HVfrom(M,A),i,z)"

locale M_Vfrom = M_HVfrom +
  assumes
    trepl_HVfrom : "\<lbrakk> M(A);M(i) \<rbrakk> \<Longrightarrow> transrec_replacement(M,is_HVfrom(M,A),i)"

begin

lemma  Vfrom_rel_iff : 
  assumes "M(A)" "M(i)" "M(z)" "Ord(i)"
  shows "is_Vfrom(M,A,i,z) \<longleftrightarrow> z = Vfrom\<^bsup>M\<^esup>(A,i)"
proof -
  have "relation2(M, is_HVfrom(M, A), HVfrom_rel(M, A))"
    using assms is_HVfrom_iff
    unfolding relation2_def
    by simp
  then
  show ?thesis
  using assms HVfrom_rel_closed trepl_HVfrom 
              transrec_abs[of "is_HVfrom(M,A)" i "HVfrom_rel(M,A)" z]
  unfolding is_Vfrom_def Vfrom_rel_def
  by simp
qed

end

