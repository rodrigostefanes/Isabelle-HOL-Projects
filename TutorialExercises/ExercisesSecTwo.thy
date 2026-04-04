theory ExercisesSecTwo
  imports Main
begin

(*Exercise 2.1*)

value "1 + (2::nat)"
value "1 + (2::int)"
value "1-(2::nat)"
value "1-(2::int)"

(*Exercise 2.2*)

fun add :: "nat \<Rightarrow> (nat \<Rightarrow> nat)" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"
(*Let's prove the associativity of the function add*)
theorem add_assoc : "add (add x y) z = add x (add y z)"
proof (induction x)
  case 0
  then show "add (add 0 y) z = add 0 (add y z)"
  proof -
    have "add (add 0 y) z = add y z" by simp
    also have "add y z = add 0 (add y z)" by simp
    finally show ?thesis .
  qed
next
    case (Suc x)
    then show "add (add (Suc x) y) z = add (Suc x) (add y z)"
    proof -
      have "add (add (Suc x) y) z = add (Suc(add x y)) z" by simp
      also have "add (Suc(add x y)) z = Suc (add (add x y) z)"by simp
      also have "Suc (add (add x y) z) = Suc (add x (add y z))" using Suc.IH by simp
      also have "Suc(add x (add y z)) = add (Suc x) (add y z)"by simp
      finally show ?thesis .
    qed
  qed
(*To prove the commutativity of the function add, we need the following two lemmas*)
lemma add_2[simp] : "add y 0 = y"
proof (induction y)
  case 0
  then show "add 0 0 =0"
    by simp
next
  case (Suc y)
  then show "add (Suc y) 0=Suc y"
    by simp
qed
lemma add_suc[simp] : "add (Suc x) y = add x (Suc y)"
proof (induction x)
  case 0
  then show "add (Suc 0) y=add 0 (Suc y)"
  proof -
    have  "add (Suc 0) y= Suc (add 0 y)" by simp
    also have "Suc (add 0 y) = Suc y"by simp
    also have "Suc y = add 0 (Suc y) " by simp
    finally show ?thesis .
  qed
next
  case (Suc x)
  then show "add (Suc(Suc x)) y = add (Suc x) (Suc  y)"
  proof -
    have "add (Suc(Suc(x))) y = Suc (add (Suc(x)) y)"by simp
    also have "Suc(add (Suc x) y) = Suc(add x (Suc y))"using Suc.IH by simp
    also have "Suc(add x (Suc y)) = add (Suc x) (Suc y)"by simp
    finally show ?thesis .
  qed
qed


theorem add_com[simp] : "add x y = add y x"
proof (induction x)
  case 0
  then show "add 0 y = add y 0 "
  proof -
    have "add 0 y = y " by simp
    also have "y=add y 0" by simp (*The first lemma was necessary here*)
    finally show ?thesis .
  qed
next
    case (Suc x)
    then show "add (Suc x) y = add y (Suc x)"
    proof -
      have "add (Suc x) y = Suc (add x y)"by simp
      also have "Suc (add x y) = Suc (add y x)" using Suc.IH by simp
      also have "Suc (add y x) = add (Suc y) x" by simp
      also have "add (Suc y) x = add y (Suc x)" by (rule add_suc) (*Why it didn't work using simp?*)
      finally show ?thesis .
    qed
  qed

fun double :: "nat \<Rightarrow> nat" where
"double 0=0" |
"double (Suc x) = Suc (Suc (double x))"

theorem add_double : "double m = add m m"
proof (induction m)
  case 0
  then show  "double 0 = add 0 0"
  proof -
    have "double 0 = 0" by simp
    also have "0 = add 0 0" by simp
    finally show ?thesis .
  qed
next
  case (Suc m)
  then show "double (Suc m) = add (Suc m) (Suc m)"
  proof -
    have "double (Suc m) = Suc(Suc(double m))" by simp
    also have "Suc(Suc(double m)) = Suc (Suc (add m m))" using Suc.IH by simp
    also have "Suc( Suc(add m m)) =Suc(add (Suc m) m)" using add.simps(2) by force (*using "by sim"
wasn't working (I have no idea why since it is only the definition of the function add). So I tried
to use the Sledgehammer and he suggested to use the code "using add.simps(2) by force"*)
    also have "Suc (add (Suc m) m) = Suc (add m (Suc m))" by simp (*Why in here I can't write
"by (rule add_com)"?*)
    also have "Suc(add m (Suc m)) = add (Suc m) (Suc m)" by simp
    finally show ?thesis .
  qed
qed


(*Exercise 2.3*)

fun count :: "'a \<Rightarrow> ('a list \<Rightarrow> nat)" where
"count y [] = 0" |
"count y (x # xs) = (if y = x then 1 + count y xs else count y xs)"

value " count (0::nat) [0,1,1,0,0,0]" (*It is necessary to write "(0::nat)" so he knows the type of
the list*)

theorem countlength:  "(count x xs) \<le> (length xs)"
proof (induction xs)
  case Nil
  then show "count x Nil \<le> length Nil" by simp
next
  case (Cons y xs)
  then show "count x (Cons y xs) \<le> length (Cons y xs)" 
  proof (cases "x=y")
    case True
    then show "count x (Cons y xs) \<le> length (Cons y xs)"
    proof -
      assume "x=y" (*Just like in math! Assume the antecedent and prove the consequent*)
      then have "count x (y# xs) = count x (x# xs)" by simp
      also have "count x (x#xs) =1+count x xs" by simp
      also have "1+(count x xs)\<le>1+(length xs)" using Cons.IH by simp
      also have "1+(length xs) = length (x # xs)"by simp
      also have "length (x # xs) = length (y#xs)"by simp
      finally show ?thesis .
    qed
  next
    case False
    assume "\<not>(x=y)"
    then have "count x (y# xs) =count x xs" by simp
    also have "count x xs \<le> length xs" using Cons.IH by simp
    also have "length xs \<le> 1+ length xs" by simp
    also have "1+length xs = length (y#xs)"by simp
    finally show ?thesis .
  qed
qed

(*Exercise 2.4*)

fun snoc :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a list)" where
"snoc Nil x =  Nil @ (x#Nil)" |
"snoc xs x = xs @ (x # Nil)" 

value "snoc [1,2,1,3] (4::nat)"

(*For the reverse it is the same as made in the Section 2.2*)

(*Exercise 2.5*)

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) =  (Suc n)+ (sum_upto n)"

value "sum_upto 100"

theorem sump_upto_formula : "sum_upto n = n*(n+1) div 2"
proof (induction n)
  case 0
  then show "sum_upto 0=0*(0+1) div 2" by simp
next
  case (Suc n)
  then show "sum_upto (Suc n) = (Suc n)*((Suc n)+1) div 2"
  proof -
    have "sum_upto (Suc n) = (Suc n) + (sum_upto n)" by simp
    also have "(Suc n)+(sum_upto n) = (Suc n) + (n*(n+1) div 2)"using Suc.IH by simp
    also have "(Suc n) + (n*(n+1) div 2) = (Suc n)*((Suc n)+1) div 2" by simp
    finally show ?thesis .
    qed
  qed

(*Exercise 2.6*)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
fun contents:: "'a tree \<Rightarrow> 'a list" where
"contents Tip = Nil"|
"contents (Node l a r)= ((contents l) @( contents r ))@(Cons a Nil)"
(*For example,*)
value" contents(Node (Node Tip (2::nat) Tip) 5 (Node Tip 8 Tip))"
(*Notice that we need to specify at least the type of one element so Isabelle can know what is the 
type of our tree*)
fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0"|
"sum_tree (Node l a r) = (sum_tree l)+a+(sum_tree r)"

value" sum_tree(Node (Node Tip (2::nat) Tip) 5 (Node Tip 8 Tip))"

theorem "sum_tree l = sum_list (contents l)"
proof (induction l)
  case Tip
  then show "sum_tree Tip = sum_list(contents Tip)"
  proof -
    have "sum_tree Tip = 0" by simp
    also have "0=sum_list(contents Tip)"by simp
    finally show ?thesis.
  qed
next
  case (Node l a r)
  then show "sum_tree (Node l a r) = sum_list(contents(Node l a r))"
  proof -
    have "sum_tree (Node l a r) = (sum_tree l) + a + (sum_tree r)" by simp 
    also have "(sum_tree l) + a + (sum_tree r) = sum_list(contents l) + a + (sum_list(contents r))" using Node.IH by simp
    also have " sum_list(contents l) + a + (sum_list(contents r)) = sum_list(((contents l) @ (Cons a Nil)) @ (contents r))" by simp
    also have "sum_list(((contents l) @ (Cons a Nil)) @ (contents r)) = sum_list(contents(Node l a r))" by simp
    finally show ?thesis.
  qed
qed

(*Another way of proving this theorem is the following one:)*)
theorem "sum_tree l = sum_list (contents l)"
  apply(induction l)
   apply(auto)
  done

(*Exercise 2.7*)
fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r ) = Node (mirror r ) a (mirror l)"

(*Pre-order: Visit the root first, then recursively traverse the left and right subtrees.
Pos-order: Recursively traverse the left and right subtrees first, then visit the root.*)

(*Notice that Pos-order is the same as the contents function that we defined. So we define:*)
definition post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order l = contents l"
fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order Tip = Nil"| 
"pre_order (Node l a r) = (Cons a Nil) @( pre_order l ) @ (pre_order r)" 

value"post_order (Node (Node Tip (2::nat) Tip) 5 (Node Tip 8 Tip))"
value"pre_order (Node (Node Tip (2::nat) Tip) 5 (Node Tip 8 Tip))"

theorem "pre_order(mirror l) = rev(post_order l)"
proof (induction l)
  case Tip
  then show "pre_order(mirror Tip) = rev(post_order Tip)"
  proof - 
    have "pre_order(mirror Tip) = pre_order Tip" by simp
    also have "pre_order Tip = Nil" by simp
    also have "Nil = rev Nil" by simp
    also have "rev Nil = rev (contents Tip)" by simp
    also have "rev (contents Tip) = rev (post_order Tip)" by (simp add: post_order_def)
    finally show ?thesis.
  qed
(*Before we prove the induction step, let's see another way that we could have proved the basis case.
We could have written the command "declare post_order_def[simp]" after the post_order definition
so we would have added the equivalence between post_order and contents in the simp command. So we 
wouldn't need to write 

also have "rev Nil = rev (contents Tip)" by simp
also have "rev (contents Tip) = rev (post_order Tip)" by (simp add: post_order_def)

We could have just written

also have "rev Nil =  rev (post_order Tip)" by simp

Another way without adding the "declare post_order_def[simp]" is simply typing 

also have "rev Nil =  rev (post_order Tip)" by (simp add: post_order_def)

Notice that the command "by (simp add: post_order_def)" temporarily includes the definition
of post_order into simp
*)
next
  case (Node l a r)
  then show  "pre_order(mirror (Node l a r)) = rev(post_order (Node l a r))"
  proof - 
    have "pre_order(mirror (Node l a r)) = pre_order( Node (mirror r ) a (mirror l))" by simp
    also have " pre_order( Node (mirror r ) a (mirror l)) =(Cons a Nil) @( pre_order (mirror r) ) @ (pre_order (mirror l))" by simp
    also have "(Cons a Nil) @( pre_order (mirror r) ) @ (pre_order (mirror l)) = (Cons a Nil) @ (rev(post_order r))@ (rev(post_order l))" using Node.IH by simp
    also have "(Cons a Nil) @ (rev(post_order r))@ (rev(post_order l)) = rev((post_order l) @ (post_order r) @ (Cons a Nil))" by simp
    also have " rev((post_order l) @ (post_order r) @ (Cons a Nil)) = rev (post_order (Node l a r))" by (simp add: post_order_def)
    finally show ?thesis.
  qed
qed

(*Let us add now the command "declare post_order_def[simp]" to see how simple our proof would be*)

declare post_order_def[simp]

theorem "pre_order(mirror l) = rev(post_order l)"
  apply(induction l)
   apply(auto)
  done


(*Exercise 2.8*)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse y [] = []"|
"intersperse y (x# xs) =x #(y #(intersperse y xs))"



value "intersperse (0::nat) [(1::nat),2,3,4,5]"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs)
   apply(auto)
  done


(*Exercise 2.9*)

fun itadd :: "nat \<Rightarrow>(nat \<Rightarrow> nat)" where
"itadd 0 m = m"|
"itadd (Suc n) m = itadd n (Suc m)"

theorem "itadd n m = add n m"
proof (induction n arbitrary: m)
  case 0
  then show "itadd 0 m = add 0 m"
  proof -
    have "itadd 0 m = m" by simp
    also have "m= add 0 m" by simp
    finally show ?thesis.
  qed
next
  case (Suc n)
  then show "itadd (Suc n) m = add (Suc n) m"
  proof - 
    have "itadd (Suc n) m = itadd n (Suc m)" by simp
    also have "itadd n (Suc m) = add n (Suc m)" using Suc.IH by simp
    also have "add n (Suc m) = add (Suc n) m" by (rule sym, rule add_suc)
    finally show ?thesis.
  qed
qed

(*Notice that we defined the function add. So it doesn't have all the theorems in auto on it. But the
function + has. So we can prove in a much simple way:*)

theorem "itadd n m =  n+ m"
  apply(induction n arbitrary:m)
   apply(auto)
  done


(*Exercise 2.11*)

datatype exp = Var| Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where 
"eval Var x = x" |
"eval 







end