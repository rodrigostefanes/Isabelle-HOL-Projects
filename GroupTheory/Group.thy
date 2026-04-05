theory Group
  imports Main "HOL-Library.FuncSet"
begin


(*This formalization is based on 
https://lawrencecpaulson.github.io/2022/03/23/Locales.html and
 https://www.isa-afp.org/entries/Jacobson_Basic_Algebra.html*)

(*Since we want to give examples of the structures we are going to work, like naturals and integers,
we need to import Main. But groups and monoids are already defined in Main. Hence, we need to give
another name to monoids and groups.*)

(*Remember that infixl tells us that we should parse the strings by the left. So x \<cdot> y \<cdot> z is parsed as (x\<cdot>y)\<cdot>z*)
(* "70" tells us the priority of \<cdot> relative to others symbols*)
locale mmonoid = 
  fixes M and op (infixl "\<cdot>" 70) and id ("\<e>") (*parameters*)
  assumes op_closed : "((x \<in> M) \<and> (y \<in> M)) \<Longrightarrow> ((x\<cdot>y) \<in> M)" (*assumptions*)
  and id_closed : "\<e> \<in> M"
  and assoc :  "((x \<in> M) \<and> (y \<in> M)\<and>(z\<in>M)) \<Longrightarrow> ((x\<cdot>y)\<cdot>z=x\<cdot>(y\<cdot>z))"
  and idr : "x \<in> M \<Longrightarrow> x\<cdot>\<e>=x"
  and idl : "x \<in> M \<Longrightarrow> \<e>\<cdot>x=x"

locale submmonoid = mmonoid M "(\<cdot>)" \<e>
  for M and op (infixl "\<cdot>" 70) and id ("\<e>") + (*+ sign tells us that we are importing those things before + from a previous definition and defining something new based on that*)
  fixes N
assumes subset: "N \<subseteq> M"
and sub_composition_closed:  "((x \<in> N) \<and> (y \<in> N)) \<Longrightarrow> ((x\<cdot>y) \<in> N)"
and sub_unit_closed: "\<e> \<in> N" 
(*Notice that the for clause acts just like fixes, but in the imports section*)

(*Notice that the type of inv is given by the assumption clause inv_closed:*)

locale ggroup = mmonoid G "(\<cdot>)" \<e>
  for G and op (infixl "\<cdot>" 70) and id ("\<e>") +
  fixes inv
  assumes inv_closed : "(x\<in>G ) \<Longrightarrow> (( inv x) \<in> G)"
    and invr : "(x\<in> G) \<Longrightarrow> ((x \<cdot> (inv x)) = \<e>)"
    and invl : "(x \<in> G) \<Longrightarrow> (((inv x) \<cdot> x)= \<e> )"

(*Another possible way of defining a group is:*)
locale gggroup = mmonoid G "(\<cdot>)" \<e>
  for G and op (infixl "\<cdot>" 70) and id ("\<e>") +
  assumes inv: "((x \<in> G ) \<Longrightarrow> \<exists>y.((y \<in> G) \<and> ((y \<cdot> x) = \<e>) \<and> ((x\<cdot> y) = \<e>)))"

context mmonoid 
begin
lemma id_uniq :
  fixes y
  assumes 0: "y \<in> M"
    and 1: "\<And>x.((x \<in> M ) \<Longrightarrow> ((y\<cdot> x = x) \<and> (x\<cdot> y = x)))"
  shows "y=\<e>"
proof -
  have 2: "\<e> \<in> M" by (simp add:id_closed)
  have 3:  "(\<e> \<in> M ) \<Longrightarrow> ((y\<cdot> \<e> = \<e>) \<and> (\<e>\<cdot> y = \<e>))" using 1 by simp
  have 4: "(y\<cdot> \<e> = \<e>) \<and> (\<e>\<cdot> y = \<e>)" using 2 and 3 by blast (*blast is an automated proof tool for classical reasoning*)
  have 5: "y\<cdot> \<e> = \<e>" using 4 by blast
  have 6: "y=y \<cdot> \<e>" using 0 by (simp add: idr) (*Notice that we had to use 0: check the definition of idr*)
  from 5 and 6 show "y=\<e>" by simp
qed
end
context ggroup
begin
lemma inv_uniq :
  fixes x y
  assumes 0: "y \<in> G"
    and 1: "x \<in> G"
    and 2: "x\<cdot>y = \<e> \<and> y \<cdot> x = \<e>"
  shows "y=inv x"
proof -
  have 3: "y=y \<cdot> \<e>" using 0 by (simp add:idr)
  have 4 : "y\<cdot> \<e> = y \<cdot> (x\<cdot> inv x)" using 1 by (simp add: invr)
  have 5 : "inv x \<in> G" using 1 by (simp add: inv_closed)
  have 6 : " y \<cdot> (x\<cdot> inv x) = (y\<cdot> x) \<cdot> inv x" using 0 and 1 and 5 by (simp add: assoc)
  have 7 : "(y\<cdot>x)\<cdot> inv x = \<e> \<cdot> inv x" using 2 by simp
  have 8 : "\<e>\<cdot> inv x = inv x " using 5 by (simp add: idl)
  from 3 4 6 7 8 show "y=inv x" by simp
qed
end

locale ggroup_homomorphism =
source: ggroup G "(\<cdot>)" \<e> inv  + target: ggroup G' "(\<cdot>')" \<e>' inv' 
for G and op (infixl "\<cdot>" 70) and id ("\<e>") and inv
    and G' and op' (infixl "\<cdot>''" 70) and id' ("\<e>''") and inv' +
fixes \<alpha>
assumes op_fun : "\<alpha> \<in> G\<rightarrow>\<^sub>E G'"
  assumes op_pres: "( x \<in> G \<and> y \<in> G ) \<Longrightarrow> \<alpha> (x \<cdot> y) = \<alpha> x \<cdot>' \<alpha> y"

(*Another possible definition for a homomorphism is to define the locale map and after that, call
the locale as we called the mmonoids. Doing this, we will have something like it is done in the
site https://lawrencecpaulson.github.io/2022/03/23/Locales.html*)

context ggroup_homomorphism 
begin

lemma id_preserved : "\<alpha> \<e> = \<e>'"
proof -
  have 0 : "\<e> \<in> G" by (simp add:source.id_closed)
  have 1: "\<e>= \<e>\<cdot>\<e>" using 0 by (simp add: source.idr) 
(*Notice the importance of labelling the two different groups. If we had not labelled them, then it 
 would have failed to simply write"by (simp add: idr)" because it wouldn't be referring to the 
ggroup G (in fact, it would be referring to the group G')*)
  have 2 : "\<alpha> \<e> = \<alpha> (\<e> \<cdot> \<e>)" using 1 by simp
(*3 is missing because my first try on this prove I used an arbitrary x wih the commands:
fix x
assume x \<in> G
but this didn't work because I used "assumed". Thus, I thought it would be better to work with
\<alpha>(e)  = \<alpha>(e\<cdot> e) = \<alpha>(e) \<cdot>' \<alpha>(e)
instead of working with
\<alpha>(x) = \<alpha>(x\<cdot> e) = \<alpha>(x) \<cdot>' \<alpha>(e)
*)
  have 4 : "\<e> \<in> G \<and> \<e> \<in> G" using 0 by simp
  have 5 : "\<alpha>(\<e>\<cdot>\<e>) = \<alpha> \<e> \<cdot>' \<alpha> \<e> " using 4 by (simp add:op_pres)
  have 6 : "\<alpha> \<e> = \<alpha> \<e> \<cdot>' \<alpha> \<e>" using 2 and 5 by simp
  have 7 : "(inv' (\<alpha> \<e>)) \<cdot>'(\<alpha> \<e>) = (inv' (\<alpha> \<e>)) \<cdot>'(\<alpha> \<e> \<cdot>' \<alpha> \<e>)" using 6 by simp
  have 8 : "\<alpha> \<e> \<in> G'" using 0 and op_fun by auto (*simp didn't work*)
  have 9 : "inv' (\<alpha> \<e>) \<in> G'" using 8 by (simp add: target.inv_closed)
  have 10 : "\<alpha> \<e> \<in> G'" using 0 and op_fun by auto
  have 11 : "(inv' (\<alpha> \<e>)) \<cdot>'(\<alpha> \<e> \<cdot>' \<alpha> \<e>) = ((inv' (\<alpha> \<e>)) \<cdot>'(\<alpha> \<e>)) \<cdot>' \<alpha> \<e>" using 9 and 8 and 10 by (simp add:target.assoc)
  have 12 : "(inv' (\<alpha> \<e>)) \<cdot>'(\<alpha> \<e>) = \<e>'" using 8 and 9 by (simp add:target.invl)
  have 13 :  "((inv' (\<alpha> \<e>)) \<cdot>'(\<alpha> \<e>)) \<cdot>' \<alpha> \<e> = \<e>'\<cdot>'\<alpha> \<e>"  using 12 by simp
  have 14 : "\<e>'\<cdot>'\<alpha> \<e> = \<alpha> \<e>" using 10 by (simp add:target.idl)
  have 15 : "(inv' (\<alpha> \<e>)) \<cdot>'(\<alpha> \<e>) =  \<alpha> \<e>" using 7 and 11 and 13 and 14 by simp
  have 16 : "\<e>' = \<alpha> \<e> " using 15 and 12 by simp
  from 16 show "\<alpha> \<e> = \<e>'" by simp
qed
end

definition inverse_int :: "int \<Rightarrow> int" where
  "inverse_int x = -x"


interpretation ints : ggroup \<int> plus 0 inverse_int
proof
  show "\<And>x y. x \<in> \<int> \<and> y \<in> \<int> \<Longrightarrow> x + y \<in> \<int>" by simp
  show "0 \<in> \<int>" by simp
  show "\<And>x y z. x \<in> \<int> \<and> y \<in> \<int> \<and> z \<in> \<int> \<Longrightarrow> x + y + z = x + (y + z)" by simp
  show "\<And>x. x \<in> \<int> \<Longrightarrow> x + 0 = x" by simp
  show "\<And>x. x \<in> \<int> \<Longrightarrow> 0 + x = x" by simp
  show "\<And>x. x \<in> \<int> \<Longrightarrow> inverse_int x \<in> \<int>" by (simp add: inverse_int_def)
  show "\<And>x. x \<in> \<int> \<Longrightarrow> x + inverse_int x = 0" by (simp add: inverse_int_def)
  show "\<And>x. x \<in> \<int> \<Longrightarrow> inverse_int x + x = 0" by (simp add: inverse_int_def)
qed






end
