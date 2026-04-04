theory SecTwoFour
imports Main
begin



(*We have been defining functions in a recursive manner. If a function has more then one argument
we defined it via recursion in one of the arguments of the function. Thus, to prove some theorem
about the function, we have been doing induction in this variable that we defined it recursively.

So for example, if we defined a function f: nat x nat \<rightarrow> nat by recursion on the first variable
 and we wanted to prove that f(m,n) = 1 for every m,n in nat, then what we would have to do is to 
show that for some arbitrary n in nat we have that

f(1,n) = 1
If f(k,n) = 1, then f(k+1,n) = 1

But maybe for showing that "If f(k,n) = 1, then f(k+1,n) = 1", it would be necessary not to also have
the hypothesis that f(k,n+1) = 1. 

Thus, we can generalize our induction prove in the following way:

To show that f(m,n) = 1 for every n,m in nat, we need to prove the following things;

For every n in nat, f(1,n) =1 
If for every n in nat, f(k,n) = 1, then for every n in nat, f(k+1,n) = 1.

Let us now work with a concrete example and show how to implement this type of proof.
*)

(*The example that we will work is another version of the reverse function that doesn't require
the app function to be defined, only the Cons function. Hence, it is a more efficient method to
compute the reverse of a string*)

fun itrev :: "'a list \<Rightarrow> ('a list \<Rightarrow> 'a list)" where
"itrev [] ys = ys"|
"itrev (x # xs) ys = itrev xs (x# ys)" 

value "itrev [(1::nat),2,3,4] []"
value "itrev [(1::nat),2,3,4] [10,11,12]"

(*So notice that the function itrev takes two strings, reverse the first one and add it in the 
front of the second one (without reversing the second one).

A theorem that we would like to prove is that for every string xs, we have that
itrev xs [] = rev xs


It's proof would be something like:


theorem "itrev xs [] = rev xs"
proof (induction xs)
  case Nil
  then show "itrev [] [] = rev []" 
  proof -
    have "itrev [] [] = []" by simp
    also have "[] = rev[]" by simp
    finally show ?thesis.
  qed
next
  case (Cons x xs)
  then show "itrev (x#xs) [] = rev (x#xs)" 
  proof -
    have "itrev (x# xs) [] = itrev xs (x# [])" by simp
   \<dots> ?

Notice that for the induction hypothesis case, we want to prove that

If itrev xs [] = rev xs, then itrev (x #xs) [] = rev (x#xs)

But when we apply "itrev (x# xs) []", we get "itrev xs (x# [])". And we cannot apply the induction
hypothesis on "itrev xs (x# [])". We can only apply it on "itrev xs []". So this isn't going to work.

What we need to do is to prove a more general theorem. The following one:

theorem "itrev xs ys = (rev xs) @ ys "
proof (induction xs)
  case Nil
  then show "itrev [] ys = rev [] @ ys" 
  proof - 
    have "itrev [] ys = ys" by simp
    also have "ys = rev [] @ ys" by simp
    finally show ?thesis.
  qed
next
  case (Cons x xs) 
  then show "itrev (x#xs) ys = rev (x#xs) @ ys"
  proof - 
    have "itrev (x#xs) ys = itrev xs (x # ys)" by simp
... ? 

Again, we ge to the same problem where our induction hypothesis only applies to "itrev xs ys",but we
 want to apply to "itrev xs (x#ys)". So the solution to this problem is what we mentioned earlier
in this section. We will generalize our induction hypothesis to an arbitrary ys by adding the command
"(induction xs arbitrary: ys)":
*)
theorem "itrev xs ys = (rev xs) @ ys "
proof (induction xs arbitrary: ys)
  case Nil
  then show "itrev [] ys = rev [] @ ys" 
  proof - 
    have "itrev [] ys = ys" by simp
    also have "ys = rev [] @ ys" by simp
    finally show ?thesis.
  qed
next
  case (Cons x xs) 
  then show "itrev (x#xs) ys = rev (x#xs) @ ys"
  proof - 
    have "itrev (x#xs) ys = itrev xs (x # ys)" by simp
    also have "itrev xs (x# ys) = (rev xs) @ (x# ys)" using Cons.IH by simp
    also have "(rev xs) @ (x# ys) = rev (x #xs) @ ys" by simp
    finally show ?thesis.
  qed
qed
(*Or, we could prove using auto:*)
theorem "itrev xs ys = (rev xs) @ ys "
  apply(induction xs arbitrary: ys)
   apply(auto)
  done



end