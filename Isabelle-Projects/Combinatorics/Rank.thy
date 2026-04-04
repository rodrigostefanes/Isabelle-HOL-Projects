theory Rank

imports Main

begin

text \<open>
In this document, we formalize the rank and unrank functions and prove that they are
inverse of each other

In the first section we define the rank and unrank functions and also define predicates
that guarantees the restriction of the domain of the functions to appropriate sets

In the second section we prove that the image of the rank falls under the domain of unrank
and that the image of unrank falls under the domain of rank

In the third section we prove that the rank and unrank functions are inverse of each other

\<close>

section \<open> Basic Definitions\<close>

text \<open>
We denote the set of sequences of length n with entries ranging from 0 to d-1
equipped with the reverse lexicographic order as F(n,d)
 \<close>

text \<open> 
rank d xs gives the position of the sequence xs on F(|xs|,d)
 \<close>

fun rank :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
"rank  d [] = 0"
|
"rank  d (x#xs) = x+ d*(rank d xs)"

text \<open>
unrank n d k gives the k-th element of F(n,d)
\<close>

fun unrank :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where 
  "unrank 0 d k = Nil"
|
"unrank (Suc n) d k = (k mod d) # (unrank n d (k div d))"

text \<open>
Now that we have defined the functions, we need to restrict their domains
We do this by asking a predicate to hold
\<close>

abbreviation radix_cond :: "nat \<Rightarrow> bool" where
"radix_cond d \<equiv> (d \<ge> 2)"

abbreviation rank_cond1 :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
"rank_cond1 d xs \<equiv> (\<forall> i. ( i< length xs \<longrightarrow> (xs! i <d)))"

abbreviation unrank_cond1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"unrank_cond1 n d k \<equiv> (k < d^n)" (*we have d^n possible sequences, but we are counting from 0 to d^n-1*)

abbreviation rank_cond :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
"rank_cond d xs \<equiv> (radix_cond d \<and> rank_cond1 d xs)"

abbreviation unrank_cond :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"unrank_cond n d k \<equiv> (radix_cond d \<and> unrank_cond1 n d k)"


section \<open>Domains and Images\<close>

text \<open>
In this section we prove that the rank always falls under the domain of unrank and that the
 converse also holds

It is easy to see that rank d xs must be less or equal than d^n -1 since

rank d x y z ... = x + d.y + d^2.z + ... \<le> (d-1) +d.(d-1)+d^2(d-1) + ...
                                         = d-1 +(d^2-d)+(d^3-d^2) + ....
                                         = -1 + d^n

For the unrank is immediate since k mod d is always less or equal than d-1
\<close>

lemma rankcond_implies_unrankcond : "rank_cond d xs \<Longrightarrow> unrank_cond (length xs) d (rank d xs)"
proof (induction xs arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons a xs) (*Notice that we use the reverse lex. order so we can use induction on Cons a xs instead of something like xs#a *)
  then show ?case 
  proof -
    assume 1: "rank_cond d (a#xs)"
    have 2: "rank_cond d xs" using 1 by auto
    have 3: "unrank_cond (length xs) d (rank d xs)" using 2 and Cons.IH by simp
    have 4: "rank d (a#xs) = a + d*(rank d xs)" by simp
    have 5: "a < d" using 1 by auto
    have 6: "rank d (a#xs) < d + d*(rank d xs)" using 4 and 5 by simp
    have 7: "d + d*(rank d xs) = d*((rank d xs) + 1)" by simp
    have 8: "rank d xs + 1 \<le> d^(length xs)" using 3 by simp
    have 9: "d*(rank d xs + 1) \<le> d*(d^(length xs))" using 8 and nat_mult_le_cancel_disj by presburger
    have 10: "d*(d^(length xs)) = d^((length xs)+1)" by simp
    have 11: "rank d (a#xs) < d^((length xs)+1)" using 6 and 7 and 9 and 10 by presburger
    have 12: "unrank_cond (length (a#xs)) d (rank d (a#xs))" using 1 and 11 by auto
    show ?thesis using 12 by simp
  qed
qed

lemma unrankcond_implies_rankcond : "(unrank_cond n d k) \<Longrightarrow> (rank_cond d (unrank n d k))"
proof (induction n arbitrary: d k)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof -
    assume 1: "unrank_cond (Suc n) d k"
    have 2: "k< d^(n+1)" using 1 by simp
    have 3: "unrank (n+1) d k = (k mod d) # (unrank n d (k div d))" by simp
    have 4: "k div d < d^n" using 2 by (simp add: less_mult_imp_div_less mult.commute)
    have 5: "unrank_cond n d (k div d)" using 1 and 4 by simp
    have 6: "rank_cond d (unrank n d (k div d))" using 5 and Suc.IH by simp
    have 7: "(k mod d) < d" using 1 by auto (*using 1 is to certify that d>0*)
    have 8: "rank_cond d (unrank (Suc n) d k)" using 3 and 6 and 7 
      by (metis One_nat_def Suc_eq_plus1 add_diff_cancel_left' less_Suc_eq_0_disj list.size(4) nth_Cons' plus_1_eq_Suc)
    show ?thesis using 8 by simp
  qed
qed





section \<open>Rank and Unrank are inverse of each other \<close>

theorem rank_unrank_id : "unrank_cond n d k \<Longrightarrow> rank d (unrank n d k) = k"
proof (induction n arbitrary: d k)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof -
    assume 1: "unrank_cond (Suc n) d k"
    have 2: "unrank_cond n d (k div d)" using 1 by (simp add: less_mult_imp_div_less mult.commute)
    have 3: "rank d (unrank n d (k div d)) = k div d" using 2 and Suc.IH by simp
    have 4: "(k mod d) + d*(k div d) = k" by simp
    have 5:  "rank d ((k mod d)#(unrank n d (k div d))) = k" using 3 and 4 by simp
    have 6: "rank d (unrank (Suc n) d k) = k" using 5 by simp
    show ?thesis using 6 by simp
  qed
qed

text \<open> Before proving that the unrank undo what the rank did, we need to prove some lemmas \<close>


theorem unrank_rank_id : "rank_cond d xs \<Longrightarrow> unrank (length xs) d (rank d xs) = xs"
proof (induction xs arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
  proof - 
    assume 1: "rank_cond d (Cons a xs)"
    have 2: "length (Cons a xs) = length xs + 1" by simp
    have 3: "unrank (length xs +1) d (rank d (Cons a xs)) =
 ((rank d (Cons a xs)) mod d)#(unrank (length xs) d ((rank d (Cons a xs)) div d))" by simp
    have 4: "(rank d (Cons a xs)) mod d = a" 
      by (metis "1" "2" Suc_eq_plus1 mod_if mod_mult_self2 nth_Cons_0 rank.simps(2) zero_less_Suc)
    have 5: "(rank d (Cons a xs)) div d = rank d xs" 
      using "1" mult.commute by auto
    have 6: "rank_cond d xs" using 1 by auto
    have 7: "unrank (length xs) d (rank d xs) = xs" using 6 and Cons.IH by simp
    have 8: "unrank (length xs +1) d (rank d (Cons a xs)) = Cons a xs" 
      using 3 and 4 and 5 and 7 by simp
    show ?thesis using 8 by simp
  qed
qed

end