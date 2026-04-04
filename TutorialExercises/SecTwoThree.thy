theory SecTwoThree
  imports Main
begin

(*2.3.1 - Datatypes*)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
(*An example of a tree can be a nat tree given by Node (Node Tip 2 Tip) 5 (Node Tip 8 Tip). In this 
example, we have the following tree:
    5
   / \
  2   8
Notice that the Tip doesn't count as a node. It is only there so we can produce roots for our tree*)
fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r ) = Node (mirror r ) a (mirror l)"
lemma "mirror(mirror l ) = l "
  apply(induction l)
   apply(auto)
  done


(*2.3.2 - Definitions*)

(*Non-recursive definitions:*)
definition sq :: "nat \<Rightarrow> nat" where
"sq n = n * n"

(*2.3.3 - Abbreviations*)
abbreviation sq' :: "nat \<Rightarrow> nat" where
"sq' n \<equiv> n * n"

(*2.3.4 - Recursive Definitions*)

(*Recursive definitions comes with induction rules. For example, the function that divides a 
natural number by two*)

fun div2:: "nat \<Rightarrow> nat" where
"div2 0 = 0"|
"div2 (Suc 0) = 0" |
"div2 (Suc(Suc n)) = Suc(div2 n)"

(*comes equipped with the following induction rule:

If P0, P(Suc 0) and for all n, Pn implies P(Suc (Suc n)), then Pm for all m

Notice that if P0 and P1, then P2 and P3 by the induction rule. So, the induction rule applied
to P0 gives us Pn for all even numbers n and the induction rule applied to P1 gives us Pn for all
odd numbers n.
*)

(*An example of the use of this rule is to prove the following lemma:*)

lemma "div2 n = n div 2"
  apply(induction n rule: div2.induct)
    apply(auto)
  done
(*If instead we had written 
lemma "div2 n = n div 2"
  apply(induction)
  apply(auto)
  done
we would get an error since auto wouldn't be able to prove our lemma*)

(*One other option is to try to prove "by hand". Notice then that our induction proof has an
 additional step.*)

lemma "div2 n = n div 2"
proof (induction n rule: div2.induct)
  case 1
  then show "div2 0 = 0 div 2"
    by simp
next
  case 2
  then show "div2 (Suc 0) = (Suc 0) div 2"
    by simp
next
  case (3 n)
  then show "div2 (Suc (Suc n)) = (Suc (Suc n)) div 2"
    by simp
qed

(*In general, if our function f is defined by recursion in such a way that there is more then one
rule for each constructor (for example, in div2 we had two rules for the constructur Suc: the rule
for Suc 0 and the rule for Suc n), then we need to add f.induct to the induction proof*)


end