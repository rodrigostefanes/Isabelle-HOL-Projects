theory Groups
  imports Main
begin

locale ssemigroup =
  fixes G :: "'a set"
  fixes op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqdot>" 80)
  assumes assoc[simp] : "x\<sqdot>y\<sqdot>z=x\<sqdot>(y\<sqdot>z)"

locale mmonoid = ssemigroup +
  fixes id :: "'a" ("\<e>")
  assumes idl : "\<e>\<sqdot>x = x"
  assumes idr : "x\<sqdot> \<e>=x"

locale ggroup = mmonoid +
  fixes inv :: "'a \<Rightarrow> 'a"  
  assumes invl : "inv x \<sqdot> x = \<e>"
  assumes invr : "x \<sqdot> inv x = \<e>"


(*We could also define a group in the following way:*)

locale ggroupe = mmonoid +
  assumes inv : "\<exists>y. x\<sqdot>y=\<e>\<and>y\<sqdot>x=\<e>"

(*Let us now see examples of those structures*)

interpretation nat : mmonoid 
  where
op = "(+) :: nat \<Rightarrow> nat \<Rightarrow> nat" and
id = "(0) :: nat"
proof
  fix x y z::nat
  show "(x+y)+z=x+(y+z)" by simp
  show "x+0=x" by simp
  show "0+x=x" by simp
qed

definition inverse_int :: "int \<Rightarrow> int" where
  "inverse_int x = -x"

interpretation int : ggroup
  where
op = "(+)::int \<Rightarrow> int \<Rightarrow> int" and
id = "(0) :: int"  and
inv = "inverse_int :: int \<Rightarrow> int"
proof
  fix x y z :: int
  show "(x+y)+z=x+(y+z)" by simp
  show "x+0=x" by simp
  show "0+x=x" by simp
  show "inverse_int x + x =0 " by (simp add: inverse_int_def)
  show " x + inverse_int x =0 " by (simp add: inverse_int_def)
qed

(*Instead of having to define a function for the inverse, we could also prove the existence of the 
inverse by the definition of ggroupe.*)

interpretation int : ggroupe
  where
op = "(+)::int \<Rightarrow> int \<Rightarrow> int" and
id = "(0) :: int" 
proof (*Notice that we do not have to prove again that int is a monoid because we already proved in
group.*)
  fix x :: int
  show "\<exists>y. x + y = 0 \<and> y + x = 0"
  proof -
    have 1:  "x + (-x) = 0" by simp
    also have 2: "(-x)+x=0" by simp
    from 1 2 have 3: "x + (-x) = 0 \<and> (-x) + x = 0" by simp
    then show "\<exists>y. x + y = 0 \<and> y + x = 0"  by (rule exI)
  qed
qed

(*Let us now prove some results*)


lemma (in mmonoid) id_unique : "(\<forall>a. a\<sqdot>b= a) \<Longrightarrow> (\<e>=b)"
proof -
  assume K: "\<forall>a. a\<sqdot>b= a"
  from K have "\<e>= \<e>\<sqdot>b" by simp
  also have "\<e>\<sqdot>b = b" by (simp add: idl)
  finally show ?thesis.
qed

lemma (in ggroup) inv_unique : "(b\<sqdot>a=\<e>) \<Longrightarrow> (b=inv a)"
proof - 
  assume 1 : "b\<sqdot>a=\<e>"
  have 2: "b=b\<sqdot> \<e>" by (simp add:idr)
  also have 3: "b\<sqdot> \<e> = b\<sqdot>a\<sqdot>inv a" by (simp add: invr)
  from 1 have 4: "b\<sqdot>a\<sqdot>inv a= \<e> \<sqdot> inv a" by simp
  have 5: "\<e> \<sqdot> inv a = inv a " by (simp add: idl)
  from 2 3 4 5 show "b=inv a" by simp
qed

locale submmonoid = mmonoid + 
  fixes F
  assumes subset: "F \<subseteq> G"
  assumes sub_op_closed: "(a \<in> F \<and> b \<in> F) \<Longrightarrow> ((a \<sqdot> b) \<in> F)"
  assumes sub_id_closed : " \<e> \<in> F"


locale subggroup = ggroup + 
  fixes F :: "'a set"
  assumes subset: "F \<subseteq> G"
  assumes sub_op_closed: "(a \<in> F \<and> b \<in> F) \<Longrightarrow> ((a \<sqdot> b) \<in> F)"
  assumes sub_id_closed : " \<e> \<in> F"
  assumes sub_inv_closed : "(a\<in> F) \<Longrightarrow> (inv a \<in> F) "

locale homgroup =
  map \<eta> M M'+  source: monoid M "(\<cdot>)" \<one> + target: monoid M' "(\<cdot>')" "\<one>'"
  



end