theory SecTwoTwo
  imports Main 
begin

(*2.2 Types bool, nat and list*)

(*2.2.1 - Type bool*)

(*Let's start defining de boolean datatype*)
datatype bool = True | False
(*Let's now define the conjunction for the boolean type*)
fun conj :: "bool \<Rightarrow> (bool \<Rightarrow> bool)" where
"conj True True = True" |
"conj _ _ = False"
(*Let's see an example now"*) 
value "(conj True)(False)"

(*Type 2.2.2 - Type nat*)

datatype nat =  Zero | Suc nat

fun add :: "nat \<Rightarrow> (nat \<Rightarrow> nat)" where
"add Zero n = n" |
"add (Suc m) n = Suc(add m n)"
value "add (Suc Zero) (Suc Zero)"
(*Let's now prove a proposition*)
lemma add_02: "add m Zero = m"
proof (induction m)
  case Zero
  then show "add Zero Zero = Zero"
    by simp
next 
  case (Suc m)
  then show "add (Suc m) Zero = Suc m"
    by simp
qed
(*We can inspect the previous proposition in the following way*)
thm add_02

(*2.2.3 - Type list*)

(*Lists can be made from different types. The type of a list is specified by "'a"*)
datatype 'a list = Nil | Cons 'a "'a list"
(*We can define now functions on the datatype of lists using structural recursion*)
fun app :: "'a list \<Rightarrow> ('a list \<Rightarrow> 'a list)" where 
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"
fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil" |
  "rev (Cons x xs) = app (rev xs) (Cons x Nil)"
(*Some remarks:
-By default, xs and ys denote variables of list type.
-As in the case for the add function, the set of lists is an inductively defined set. We have a 
base set of elements (the type of the elements of the string) and we construct this set in the
following way: every string is an empty string or it is the concatenation (via the Cons function) 
of an element of the base set together with a string. Thus our functions app and rev are well
defined since they take care of all the possibilities of what a string could be.
- The function app is a function that describes how to concatenate two strings and the function rev
is a function that describes how to reverse the string.*)
value "rev ( Cons True (Cons False Nil))"

(*2.2.4 - The Proof Process*)

(*Lets now prove a theorem that reversing the reverse of a list results in the original list. For 
that, we are going to need some lemmas*)

lemma AppListNil:  "app xs Nil = xs"
proof (induction xs)
  case Nil
  then show "app Nil Nil = Nil"
    by simp
next
  case (Cons x1 xs)
  then show "app (Cons x1 xs) Nil = Cons x1 xs"
    by simp
qed
(*The following lemma can be shown in a faster way using the automatic theorem proving of Isabelle*)
lemma AppAssoc: "app (app xs ys) zs = app xs (app ys zs)" 
  apply(induction xs)
   apply(auto)
  done

  

lemma RevAp [simp] : "rev (app xs  ys) = app (rev ys) (rev xs )"
proof (induction xs)
  case Nil 
  then show "rev (app Nil ys) = app (rev ys) (rev Nil)"
  proof -
    have "rev(app Nil ys) = rev ys " by simp
    also have "rev ys = app (rev ys) Nil" by (rule sym, rule AppListNil)
    also have " app (rev ys) Nil= app (rev ys) (rev Nil)" by simp
    finally show ?thesis .
  qed
(*It's important to notice that the order of the equalities matters for us to apply the command
"finally show ?thesis ." because he is going to compare the left side of the first equality with
the right side of the last equality. We also had to use symmetry of the equality of the previous
lemma.*)
  case (Cons x1 xs)
  then show "rev (app (Cons x1 xs) ys) = app (rev ys) (rev (Cons x1 xs))"  
  proof - 
    have "rev(app (Cons x1 xs) ys) = rev (Cons x1 (app xs ys))" by simp
    also have "rev (Cons x1 (app xs ys)) = app (rev (app xs ys)) (Cons x1 Nil) " by simp
    also have "app (rev (app xs ys)) (Cons x1 Nil) = app (app (rev ys) (rev xs)) (Cons x1 Nil) " 
      using Cons.IH by simp
    also have "app (app (rev ys) (rev xs)) (Cons x1 Nil) = app (rev ys) (app (rev xs) (Cons x1 Nil))"
      by (rule AppAssoc)
    also have "app (rev ys) (app (rev xs) (Cons x1 Nil)) = app (rev ys) (rev (Cons x1 xs))" by simp
    finally show ?thesis .
  qed
qed
(* The [simp] box in "lemma RevAp [simp]" is used to add the lemma RevAp as a simplification rule
to be used in the command "simp". Since this lemma is important to prove the following theorem, 
without adding [simp] in the previous lemma, Isabelle wouldn't be able to prove our theorem by just
writing "by simp" in the inductive case (you can try removing [simp] from the previous lemma to
check this out by yourself. The importance of this lemma to prove the theorem, is easily verified
by writing an informal proof.*)

theorem revrev[simp]: "rev (rev xs) = xs"
proof (induction xs)
  case Nil
  then show "rev (rev Nil) = Nil"
    by simp
next
  case (Cons x1 xs)
  then show  "rev(rev (Cons x1 xs)) = Cons x1 xs"
    by simp
qed

(*2.2.5 - Predefined Lists*)

(*Isabelle's predefined symbols are the following ones:
[] as Nil
x # xs as Cons x xs
[x1,...,xn] is x1#...#xn#[]
xs @ ys is app xs ys

Notice then that [x] is x#[].

there is also some predefined functions, such as 

length :: 'a list \<Rightarrow> nat 

(with the obvious definition)

and the map function that applies a function to all elements of a list:

fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"map f Nil = Nil" |
"map f (Cons x xs) = Cons (f x ) (map f xs)"
*)


(*2.2.6 -Types int and real *)

(*We can add the theory Complex_Main to work with real numbers. Integers are already defined in Main*)
end