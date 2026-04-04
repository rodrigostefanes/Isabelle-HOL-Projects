theory AutoCorrode
  imports
    Micro_Rust_Std_Lib.StdLib_All
begin

fun min_fun :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"min_fun 0 0 = 0"|
"min_fun (Suc n) 0 = 0"|
"min_fun 0 (Suc m) = 0"|
"min_fun (Suc n) (Suc m) = Suc (min_fun n m) "

value "min_fun 2 3"


(*Boilerplate*)
locale showcase_ctx =
    reference reference_types +
    \<comment> \<open>Import \<^verbatim>\<open>reference_allocatable\<close> so we can allocate references for \<^verbatim>\<open>64 word\<close>.\<close>
    ref_word64: reference_allocatable reference_types _ _ _ _ _ _ _ word64_prism +
    ref_nat: reference_allocatable reference_types _ _ _ _ _ _ _ nat_prism +
    ref_bool: reference_allocatable reference_types _ _ _ _ _ _ _ bool_prism
  for 
  reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  \<comment> \<open>Ignore for now\<close>
  and word64_prism :: \<open>('gv, 64 word) prism\<close>
  and bool_prism :: \<open>('gv, bool) prism\<close>
  and nat_prism :: \<open>('gv, nat) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_word64.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_nat.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_bool.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun
(*End of the Boilerplate*)


definition min_ref :: \<open>('addr, 'gv, nat) ref \<Rightarrow> ('addr, 'gv, nat) ref \<Rightarrow>  ('s, nat, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>min_ref rA rB  \<equiv> FunctionBody \<lbrakk>
     if *rA<*rB {
      *rA
      }
     else{
      *rB
      }
  \<rbrakk>\<close>

definition min_ref_contract :: \<open>('addr, 'gv, nat) ref \<Rightarrow> ('addr, 'gv, nat) ref \<Rightarrow> 'gv \<Rightarrow> 'gv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('s, nat, 'b) function_contract\<close> where
  \<open>min_ref_contract rA rB gA gB vA vB \<equiv>
    let pre  = rA \<mapsto>\<langle>\<top>\<rangle> gA\<down>vA \<star> rB \<mapsto>\<langle>\<top>\<rangle> gB\<down>vB in
    let post = \<lambda> r.
               rA \<mapsto>\<langle>\<top>\<rangle> gA\<down>vA \<star> rB \<mapsto>\<langle>\<top>\<rangle> gB\<down>vB \<star> \<langle>r = min_fun vA vB\<rangle> in
    make_function_contract pre post\<close>
ucincl_auto min_ref_contract
(*rA is the pointer, gA is the bitwise representation of the value vA*)
(*rA \<mapsto>\<langle>\<top>\<rangle> gA\<down>vA tells us that the pointer rA has full acess(because of \<langle>\<top>\<rangle>) to the part of the memory
designed for gA and the bitwise representation of vA is gA*)
(*\<star> is the conjunction in separation logic, that is, it asserts that both parts live in separate parts of the memory*)

lemma min_fun_lemma: "min_fun a b = (if a < b then a else b)"
  apply (induction a b rule: min_fun.induct)
  apply auto
  done

theorem min_ref_spec:
  shows \<open>\<Gamma>; min_ref rA rB \<Turnstile>\<^sub>F min_ref_contract rA rB gA gB vA vB\<close>
  apply (crush_boot f: min_ref_def contract: min_ref_contract_def)
  apply (crush_base simp add: min_fun_lemma) 
  done










end
