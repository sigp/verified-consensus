theory sqrt_proof
imports Hoare_Logic
begin

context hoare_logic
begin
lemma rewrite_helper: "(\<lambda>a. (case a of (x', y) \<Rightarrow> return x') x) = (x o fst)"
  apply (rule ext, clarsimp simp: return_def)
  done

lemma idk2: "bindCont f (\<lambda>(x', y). return x') = (\<lambda>x. f (x o fst))"
  apply (rule ext)+
  apply (clarsimp simp: bindCont_def return_def rewrite_helper split: prod.splits)
  done

  

lemma integer_squareroot_aux_wp: "(\<And>n. hoare_triple (P n) (c n) Q) \<Longrightarrow>
  (\<And>x y n. I x y n \<Longrightarrow> y \<noteq> 0 \<and> y \<le> y + (n div y)) \<Longrightarrow>
 hoare_triple (\<lambda>s. I x y n \<and> (\<forall>x y . I x y n  \<longrightarrow> x \<le> y \<longrightarrow> P (x, y) s) \<and>
   (\<forall>x y . I x y n \<longrightarrow> y < x \<longrightarrow>  I y ((y + (n div y)) div 2) n))  (do { z <- integer_squareroot_aux x y n; c z}) Q"
  apply (rule_tac P="\<lambda>x y n. hoare_triple (\<lambda>s.  I x y n \<and>   (\<forall>x y . I x y n \<longrightarrow> x \<le> y \<longrightarrow> P (x, y) s) \<and>
   (\<forall>x y . I x y n \<longrightarrow> y < x \<longrightarrow>  I y ((y + (n div y)) div 2) n))  (do { z <- integer_squareroot_aux x y n; c z}) Q" in
 integer_squareroot_aux.induct[simplified]  )
  apply (atomize)
  apply (subst integer_squareroot_aux.simps)
  apply (rule hoare_weaken_pre)
   apply (wp)
    apply (clarsimp simp: bindCont_return')
    apply (blast)
   apply (wp)
   apply (erule_tac x="y + (n div y)" in allE, drule mp, clarsimp)
  apply (assumption)
  apply (clarsimp)
  apply (safe; clarsimp?)
  by (blast)
  
 


lemma "P 0 \<Longrightarrow> (\<And>n. P n \<Longrightarrow> n < n + 1 \<Longrightarrow> P (n + 1)) \<Longrightarrow> P (n :: 64 word)"
  by (metis add.commute word_induct2 word_overflow)

lemma "(2 + (n :: 64 word)) div 2 = n div 2 + 1"
  apply (induct n rule: word_induct2; clarsimp)
  oops


               
  
definition "sqrt (n :: u64) m \<equiv> 
  (m * m) div m = m \<and> (m * m) \<le> n \<and> 
  (\<forall>m'. m < m' \<longrightarrow> (m' * m') div m' = m' \<longrightarrow> ( m' * m' > n))"

lemma sqrt_unique: "sqrt n m \<Longrightarrow> sqrt n m' \<Longrightarrow> m = m'"
  apply (clarsimp simp: sqrt_def)
  apply (rule ccontr, clarsimp simp: linorder_neq_iff)
  apply (elim disjE)
   apply (erule_tac x=m' in allE, clarsimp) 
   apply (fastforce)
  apply (fastforce)
  done

lemma word_desc_induct: "P m \<Longrightarrow> (\<And>n. P n \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> P (n - 1)) \<Longrightarrow> n \<le> m \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> P (n :: u64)"
  apply (erule contrapos_pp)
  apply (induct arbitrary: n rule: word_induct2; clarsimp)
  by (metis add_diff_cancel2 le_step_down_word)

lemma "x * (x :: u64) div x = x \<Longrightarrow> x \<noteq> 0 \<Longrightarrow>  unat x * unat x < 2 ^ LENGTH(64)"
  apply (unat_arith)
    apply (clarsimp simp: word_arith_nat_div unat_mult_lem)
  by (smt (verit, ccfv_SIG) div_mult_le order_le_less_trans)

lemma x_square_defined_iff: "x * x div (x :: u64) = x \<longleftrightarrow> unat x * unat x < 2 ^ LENGTH(64)"
  apply (case_tac "x=0"; clarsimp?)
  apply (rule iffI)
   apply (unat_arith)
    apply (clarsimp simp: word_arith_nat_div unat_mult_lem)
  apply (smt (verit, ccfv_SIG) div_mult_le order_le_less_trans)
  apply (rule Word.word_div_mult)
  using word_greater_zero_iff apply blast
  apply (clarsimp)
  done

lemma x_squared_defined_mono: assumes x_le: "(x' :: u64) \<le> x" shows "(x * x) div x = (x :: u64) \<Longrightarrow>  x' * x' div x' = (x' :: u64)"
  apply (clarsimp simp: x_square_defined_iff)
  using x_le 
  by (meson mult_le_mono order_le_less_trans word_le_nat_alt)


lemma sqrt_iff_defined: "
    sqrt n m \<longleftrightarrow> (m * m) div m = m \<and> m * m \<le> n \<and> (m < m + 1  \<longrightarrow> (m + 1) * (m + 1) div (m + 1) = (m + 1) \<longrightarrow>  (m + 1) * (m + 1) > n)"
  apply (clarsimp simp: sqrt_def,safe)
   apply (erule_tac x="m+1" in allE)
   apply (drule mp)
         apply (clarsimp, clarsimp)
  using less_is_non_zero_p1 word_overflow apply blast
  using inc_le x_squared_defined_mono apply blast
  by (smt (verit, ccfv_SIG) inc_le mult_le_mono not_less_iff_gr_or_eq
        order_le_less_trans unat_mult_lem word_le_nat_alt x_square_defined_iff)
  
  
  
definition "sqrt' n = (THE m. sqrt n m)"

find_theorems "fst (_, _)"

lemma push_res_forward: "bindCont (word_unsigned_add x y) c = (bindCont (x .+ y) (\<lambda>z. c (x + y)))"
  apply (rule ext, clarsimp simp: bindCont_def word_unsigned_add_def Let_unfold return_def fail_def)
  done

lemma push_res_forward': 
  "bindCont (word_unsigned_div x y) c = (bindCont (word_unsigned_div x y) (\<lambda>z. c (x div y)))"
  apply (rule ext, clarsimp simp: bindCont_def word_unsigned_div_def Let_unfold return_def fail_def)
  done

lemma exists_singularI: "\<exists>x. P x \<Longrightarrow> \<forall>x y. P x \<longrightarrow> P y \<longrightarrow> x = y \<Longrightarrow> \<exists>!x. P x"
  apply (clarsimp)
  by blast

lemma sqrt_eqI: "sqrt x y \<Longrightarrow> sqrt' x = y"
  apply (clarsimp simp: sqrt'_def)
  apply (rule the1_equality; clarsimp?)
  apply (rule exists_singularI, blast)
  apply (clarsimp)
  by (simp add: sqrt_unique)


lemma zero_sqrt_zero[simp]:  "sqrt' 0 = 0"
  by (rule sqrt_eqI, clarsimp simp: sqrt_iff_defined)



lemma one_sqrt_one:  "sqrt' 1 = (1 :: u64)"
  by (rule sqrt_eqI, clarsimp simp: sqrt_iff_defined)



lemma mul_injective: "x * 2 = y * 2 \<Longrightarrow> (x * 2) div 2 = x \<Longrightarrow> (y * 2) div 2 = y \<Longrightarrow>  (x :: u64) = y " 
  apply (unat_arith; clarsimp)
  done

lemma div_2_times_2_div_2[simp]: "((x div 2) * 2) div 2 = ((x div 2) :: u64)"
  by (metis (no_types, lifting) add.commute add_cancel_right_right dvd_triv_left
               even_succ_div_2 mult.commute mult_div_mod_eq not_mod_2_eq_0_eq_1)

lemma "a * x = a * y \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> x = (y :: int)"
  apply (clarsimp)
  done



lemma less_plus_1_div_two_implies_eq_1: "n \<noteq> 0 \<Longrightarrow> n \<le> (n + 1) div 2 \<Longrightarrow> (n :: u64) = 1"
  apply (erule contrapos_pp) back
  apply (induct n rule: word_induct2)
   apply (clarsimp)
  apply (clarsimp)
  apply (unat_arith)
  done




lemma limited_by: "n \<ge> x \<Longrightarrow> n < n + 1 \<Longrightarrow>  x \<noteq> 0 \<Longrightarrow>  (x :: u64) + (n div x) \<le> n + 1"  
  apply (case_tac "x = n", clarsimp)
   apply (simp add: div_word_self)
  oops

lemma bounded_div_mono: "(x :: u64) \<le> x + y \<Longrightarrow> n \<noteq> 0 \<Longrightarrow>  x div n \<le> (x + y) div n"
  by (simp add: div_le_mono unat_arith_simps(6) word_le_nat_alt)

lemma square_less_than: "x \<le> x + n div x \<Longrightarrow> (x + n div x) div 2 = x \<Longrightarrow> x * x \<le> (n :: u64)" 
  by (metis (no_types, lifting) add_cancel_right_right add_diff_cancel_right'
                   div_less_dividend_word div_to_mult_word_lt mult.commute mult_2 mult_div_mod_eq
            not_mod_2_eq_0_eq_1 one_add_one word_le_less_eq word_le_minus_one_leq word_plus_mcs_4')


lemma square_less_than_by_1: "x \<le> x + n div x \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> ((x + n div x) div 2) - 1 = x \<Longrightarrow> x * x \<le> (n :: u64)"
  by (smt (verit, ccfv_threshold) add_diff_cancel_left'
          diff_numeral_special(9) div_by_0_word div_lt' div_to_mult_word_lt 
          less_1_simp linorder_not_le mult_2_right one_add_one unat_mult_lem 
           unat_plus_simple unsigned_1 word_diff_ls'(3) word_le_less_eq word_less_div)
  


lemma add_galois: "z \<le> z + y \<Longrightarrow> y \<le> (x :: u64) \<Longrightarrow> x \<le> z + y \<longleftrightarrow> x - y \<le> z"
  by (meson olen_add_eqv word_diff_ls'(3) word_diff_ls'(4))

lemma times_2_cases: "2 * ((n :: u64) div 2) = n \<or> 2 * (n div 2) = (n - 1)"
  apply (case_tac "\<exists>k. n = 2 * k", clarsimp)
   apply (metis add.right_neutral add_diff_cancel_right' mult_div_mod_eq not_mod_2_eq_0_eq_1)
  apply (clarsimp)
  apply (subgoal_tac "\<exists>k. n = (2 * k) + 1")
   apply (clarsimp)
   apply (metis add_diff_cancel_right' even_plus_one_iff mult_div_mod_eq odd_iff_mod_2_eq_one)
  by (meson dvdE oddE)

lemma times_2_cases': "((n :: u64) div 2) * 2  = n \<or> (n div 2) * 2  = (n - 1)"
  using times_2_cases 
  by (simp add: mult.commute)

lemma helper: " x \<noteq> 0 \<Longrightarrow> x = (n :: u64) div x \<Longrightarrow> \<exists>m\<le>x. (x * x) = n - m" 
  apply (rule_tac x="n - (n div x * x)" in exI) 
  apply (clarsimp)
  apply (frule_tac f="\<lambda>n. n * x" in arg_cong)
  apply (unat_arith, clarsimp)
  apply (safe)
  apply (metis (no_types, lifting) add_diff_cancel_left' mod_le_divisor mult_div_mod_eq order_le_less_trans times_div_less_eq_dividend unat_mult_lem unsigned_less)
  using word_div_mult_le word_le_nat_alt by blast


lemma nat_divD: " (n :: nat) div y = x \<Longrightarrow> y \<noteq> 0  \<Longrightarrow> n \<ge> x * y \<and> n \<le> y * (x + 1)"
  apply (intro conjI)
   apply fastforce
  by (metis add_le_same_cancel1 div_le_mono linorder_linear nonzero_mult_div_cancel_left not_one_le_zero)


lemmas unat_mult_simp =  unat_mult_lem[THEN iffD1]

 

lemma div_mod_step: "x \<le> x + r \<Longrightarrow> r < x \<Longrightarrow>  (x + r) div (x :: u64) = 1"
  using word_div_less word_div_sub word_gt_a_gt_0 by fastforce

lemma div_removes_mod: "r < x \<Longrightarrow> (k * x) \<le> ((k * x) + r) \<Longrightarrow> unat k * unat x < 2^64 \<Longrightarrow>
  ((k * x) + r) div (x :: u64) = (k * x) div x"
  apply (subgoal_tac "r = ((k * x) + r) mod x", clarsimp)
   apply (smt (verit, best) add_diff_cancel_left' add_diff_cancel_right'
   div_mult_le mod_div_mult_eq nonzero_mult_div_cancel_right not_less_iff_gr_or_eq 
    order_le_less_trans unat_arith_simps(6) unat_eq_zero unat_mult_lem unsigned_less
   word_eq_unatI word_gt_a_gt_0)
  apply (unat_arith, clarsimp)
  apply (subst unat_mult_lem[THEN iffD1])
  apply (clarsimp simp: unat_mult_lem)
  apply (subst msrevs(2))
  using mod_less by presburger

lemmas unat_mul_simp[simp] = unat_mult_lem[THEN iffD1]

lemma div_removes_mod': "r < (x :: u64) \<Longrightarrow> x\<noteq>0  \<Longrightarrow> k * x \<le> (k * x + r) \<Longrightarrow> 
unat k * unat x < 2 ^ 64\<Longrightarrow> 
 ((k * x) + r) div x = k"
  apply (subst div_removes_mod, clarsimp)
    apply (clarsimp)
   apply (clarsimp)
  apply (unat_arith)
  apply (clarsimp)
  done
  


lemma "(a :: nat) \<le> b \<Longrightarrow> a \<noteq> 0 \<Longrightarrow>  (\<exists>k r. k * a + r = b \<and> r < a)"
  apply (rule_tac x="(b div a) :: nat" in exI)
  apply (rule_tac x="(b mod a)" in exI)
  apply (clarsimp)
  done

  

lemma word_assist: " r < k - 1 \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> k \<le> k + (k - 1) \<Longrightarrow> (k :: u64) + r - 1 \<le> 2 * k - 2 " 
  apply (rule order_trans[where y="k + (k - 1) - 1"])
   defer
   apply (clarsimp)
  apply (case_tac "k \<le> k + k")
  apply (smt (verit, ccfv_SIG) add_diff_eq diff_add_eq lt1_neq0 
             order_trans word_diff_ls'(4) word_le_less_eq word_plus_mono_right word_random)
  
  by (meson Word.word_l_diffs(2) neq_0_no_wrap order_less_le plus_le_left_cancel_nowrap word_plus_mono_right2 word_sub_1_le word_sub_le_iff)



lemma div_helper: "b \<noteq> 0 \<Longrightarrow>a \<le> a + b \<Longrightarrow>  a div b = (c :: u64) \<Longrightarrow> (a + b) div b = (c + 1)"
  using div_removes_mod' 
  by (metis (no_types, lifting) eq_diff_eq olen_add_eqv word_div_sub word_neq_0_conv)


lemma div_removal'': "r < x \<Longrightarrow> unat k * unat x < (2^64)  \<Longrightarrow> 
  k * x \<le> k * x + r \<Longrightarrow> (k * x + r) div x = (k :: u64)" 
  apply (case_tac "x=0"; clarsimp)
  apply (rule div_removes_mod')
     apply (assumption)+
  apply (clarsimp)
  done
 

lemma helper': " x \<noteq> 0 \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> x \<le> n \<Longrightarrow> x * x div x = x \<Longrightarrow>  x = (n :: u64) div x - 1 \<Longrightarrow> \<exists>m\<le>(2 * x). (x * x) = n - m" 

  apply (rule_tac x="n - ((n div x - 1) * x)" in exI) 
  apply (clarsimp)
  apply (subgoal_tac "\<exists>k r. n = (k * x) + r \<and> r < x \<and> (k * x) div x = k \<and> unat k * unat x < 2 ^ 64", clarsimp) 
   apply (subgoal_tac "x = k - 1", clarsimp)
    apply (clarsimp simp: smt_arith_simplify)
    apply (rule word_assist, clarsimp, clarsimp)
    apply (metis (no_types, opaque_lifting) diff_add_eq diff_diff_eq2 
eq_iff_diff_eq_0 even_plus_one_iff inc_le plus_minus_no_overflow_ab word_div_lt_eq_0 word_div_sub word_gt_a_gt_0 word_le_less_eq word_le_not_less)
   apply (subst (asm) div_removal'', assumption)
  apply (clarsimp)
  apply (simp add: olen_add_eqv)
  apply (smt (verit) add.commute add_cancel_left_left add_cancel_right_right add_diff_cancel2 add_galois diff_add_cancel diff_diff_eq diff_diff_eq2 diff_numeral_special(9) div_less_dividend_word div_removes_mod div_word_self leD lt1_neq0 mult_2 mult_2_right mult_div_mod_eq nless_le olen_add_eqv one_add_one order_le_less_trans plus_minus_no_overflow_ab sub_wrap word_div_lt_eq_0 word_le_minus_one_leq word_sub_le_iff)
  apply (rule_tac x="n div x" in exI)
  apply (rule_tac x="n mod x" in exI)
  apply (safe)
    apply presburger
    apply (simp add: word_greater_zero_iff word_mod_less_divisor)
   apply (metis (mono_tags, lifting) div_lt' mult.right_neutral nonzero_mult_div_cancel_right 
           unat_arith_simps(6) unat_eq_zero unat_mult_lem word_div_1 word_div_mult_le word_eq_unatI)
  by (smt (verit) Euclidean_Rings.div_eq_0_iff div_lt' eq_2_64_0 linorder_neqE_nat linorder_not_less one_div_two_eq_zero order_less_trans power_less_imp_less_exp sub_wrap word64_power_less_1' word_eq_zeroI word_le_minus_cancel word_le_minus_mono_right zero_neq_numeral)

lemma "y \<noteq> 0 \<Longrightarrow>x \<ge> y \<Longrightarrow> z \<le> x div y \<longleftrightarrow> x \<ge> z * (y :: nat)" 
  apply (safe)
  using td_gal apply blast
  using less_eq_div_iff_mult_less_eq by blast

lemma lift_div: "m \<le> n * q \<Longrightarrow> m div q \<le> (n :: nat)"
  by (metis antisym div_by_0 linorder_linear nonzero_mult_div_cancel_right th2 zero_le)


lemma le_div_times_iff: "unat z * unat y < 2^64 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow>  x div y \<ge> z \<longleftrightarrow> x \<ge> z * (y :: u64)"
  apply (unat_arith, clarsimp)
  apply (safe)
  using th2 apply blast
  apply (subst less_eq_div_iff_mult_less_eq)
   defer
   apply (clarsimp)
  apply (blast)
  done


lemma le_div_timesI: "x \<le> z * (y :: u64) \<Longrightarrow>  x div y \<le> z "
  by (metis bits_div_by_0 div_lt_mult linorder_not_less word_gt_a_gt_0 word_neq_0_conv)



  

lemma square_less_than': " 2 * x + x * x \<le> 2 * x + x * x + 1 \<Longrightarrow>  2 * x \<le> 2 * x + x * x \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> x \<le> x + n div x \<Longrightarrow> x \<noteq> 0 \<Longrightarrow>  (x + n div x) div 2 = x \<Longrightarrow>
  (x + 1) * (x + 1) > (n :: u64)" 
  apply (clarsimp simp: smt_arith_simplify) 
  apply (subgoal_tac "n \<le> 2 * x + (x * x)")
   apply (metis (no_types, opaque_lifting) is_num_normalize(1) lt1_neq0 olen_add_eqv plus_one_helper2)
  apply (subgoal_tac "n - (x * x) \<le> 2 * x")
   apply (subst add_galois)
     defer
  apply (metis (no_types, lifting) add.commute add_cancel_right_right div_less_dividend_word div_to_mult_word_lt mult.commute mult_2 mult_div_mod_eq neq_0_no_wrap not_mod_2_eq_0_eq_1 one_add_one plus_one_helper word_div_mult_le word_plus_mcs_4)
    apply (assumption)
  apply (rule_tac y="2 * ((x + n div x) div 2)" in  order_trans[rotated])
    apply auto[1]
   apply (insert times_2_cases[where n="(x + n div x)"])[1]
   apply (elim disjE; clarsimp)
    apply (frule (1) helper)
    apply (clarsimp)
  using order_trans apply blast
   apply (frule helper'[where x=x and n=n])
        apply (clarsimp)
       apply (metis add_cancel_right_right div_less_dividend_word
             linorder_not_le one_add_one word_div_lt_eq_0 zero_neq_one)
     apply (metis (mono_tags, lifting) add_cancel_right_right
 antisym_conv2 div_less_dividend_word div_lt' nonzero_mult_div_cancel_right one_add_one one_neq_zero unat_0 unat_arith_simps(6) unat_mult_lem word_eq_unatI word_sub_1_le)
     apply (assumption)
   apply (clarsimp)
  apply (assumption)
  done


lemma context_conjI':
  assumes Q "Q \<Longrightarrow> P"
  shows "P \<and> Q"
  by (iprover intro: conjI assms)

lemma conjI_alt: "(P \<Longrightarrow> Q) \<Longrightarrow> (Q \<Longrightarrow> P) \<Longrightarrow> (\<not>P \<Longrightarrow> Q) \<Longrightarrow>  P \<and> Q"
  apply (intro conjI)
   apply (case_tac P; clarsimp)
  apply (case_tac P; clarsimp)
  done


lemma another_helper: "
       x \<le> n + 1 \<Longrightarrow> n < n + 1 \<Longrightarrow> 
       x  \<le> x + ((n :: 64  word) div x)" 
  apply (induct x rule: less_induct)
  apply (atomize)
  apply (case_tac "x = 0"; clarsimp)
  apply (case_tac "x = n + 1", clarsimp)
  apply (simp add: word_div_lt_eq_0)
  apply (erule_tac x="x - 1" in allE)
  apply (drule mp)
   apply (simp add: less_1_simp)
  apply (drule mp)
   apply (simp add: less_1_simp word_le_less_eq)
  by (smt (verit) add_diff_eq diff_add_eq_diff_diff_swap diff_diff_eq2 
     div_less_dividend_word div_mod_step inc_i inc_le le_m1_iff_lt 
      less_1_simp lt1_neq0 not_less_iff_gr_or_eq order_less_le_trans 
       word_diff_less word_div_1 word_div_sub word_greater_zero_iff 
      word_gt_a_gt_0 word_le_less_eq word_le_minus_one_leq word_le_not_less 
     word_not_simps(1) word_random word_sub_le_iff word_sub_plus_one_nonzero zadd_diff_inverse)


lemma yet_another_helper: "n div y \<le> y + 1 \<Longrightarrow> (y + n div y) div 2 \<le> (y :: u64)"
  apply (unat_arith, clarsimp, safe; clarsimp?)
  apply linarith
  by (linarith)

  



lemma diff_lessE: "(x :: nat) < y \<Longrightarrow> (a \<le> y \<Longrightarrow> y - a < y - x) \<Longrightarrow>  x < a"
  apply (case_tac "a \<le> y")
   apply (meson diff_le_mono2 le_def)
  by auto

lemma x_add_cases: "x div Suc (Suc 0) +
        x div Suc (Suc 0) = x \<or> x div Suc (Suc 0) +
        x div Suc (Suc 0) = (x - 1)"
  apply (case_tac "even x"; clarsimp?)
   apply (metis dvd_div_mult_self mult_2_right numeral_2_eq_2)
  by (metis One_nat_def mult_2 numeral_2_eq_2 odd_two_times_div_two_nat)



lemma midpoint_le: "x \<le> n \<Longrightarrow> (x :: nat) + n div x \<le> n + 1" 
  apply (induct x rule: less_induct)
  apply (case_tac x; clarsimp)
  apply (drule_tac x=nat in meta_spec)
  apply (clarsimp)
  sorry


lemma move_it: "Suc y = x \<Longrightarrow> y \<le> a \<Longrightarrow> x \<le> Suc a"
  by blast

lemma move_it': "x = y - Suc 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow>  x + 1 = (y :: nat)"
  by force

lemma times_2_cases_nat: "2 * ((n :: nat) div 2) = n \<or> 2 * (n div 2) = (n - 1)"
  apply (case_tac "\<exists>k. n = 2 * k", clarsimp)
  by (metis add.right_neutral add_diff_cancel_right' mult_div_mod_eq not_mod_2_eq_0_eq_1)


lemma "x * (n div x) = n - n mod (x :: nat)"
  by (metis minus_mod_eq_mult_div)

lemma "z \<noteq> 0 \<Longrightarrow> (x :: nat) \<le> y div z \<longleftrightarrow> x * z \<le> y"
  by (simp add: less_eq_div_iff_mult_less_eq)

lemma sqr_both_sides: "x * x \<le> y * y \<Longrightarrow> x \<le> (y :: nat)"
  using mult_le_mono nat_le_linear by fastforce


lemma idk: "(n :: nat) * 2 \<le> Suc n + n * n div Suc n"
  apply (induct n; clarsimp)
  by (simp add: less_eq_div_iff_mult_less_eq)

lemma "((x :: nat) \<le> z + y) = (x - y \<le> z)"
  using le_diff_conv by blast

lemma ratio: "p \<le> x \<Longrightarrow>  (p :: nat) * 2 \<le> x + p*p div x" 
  apply (case_tac "x=0"; clarsimp)
  apply (case_tac "x > 2 * p", clarsimp)
  apply (subst add.commute)
  apply (subst le_diff_conv[symmetric])
  apply (subst less_eq_div_iff_mult_less_eq; clarsimp?)
  apply (induct x; clarsimp)
  apply (case_tac "p = Suc x", clarsimp)
  apply (drule meta_mp, clarsimp)
  apply (erule order_trans[rotated])
  apply (clarsimp simp: smt_arith_simplify) 

  by (smt (verit, ccfv_threshold) Suc_diff_le add.assoc add_diff_cancel_left' le_Suc_eq le_add_diff_inverse2 le_antisym le_diff_conv mult.commute mult_Suc_right nat_le_linear trans_le_add1)
  
  
   

lemma ge_sqrt: "(p * p) \<le> n \<Longrightarrow>  x \<ge> p \<Longrightarrow>  ((x :: nat) + n div x) div 2 \<ge> p"
  apply (subst less_eq_div_iff_mult_less_eq)
   apply (clarsimp)
  apply (case_tac "x = p", clarsimp)
   apply (metis div_by_0 div_le_mono nonzero_mult_div_cancel_right)
  apply (rule order_trans[rotated], rule add_le_mono, rule order_refl)
   apply (rule div_le_mono, assumption)
  by (rule ratio, assumption)

lemma maximal_helper: "finite S \<Longrightarrow> ((S :: u64 set) \<noteq> {}) \<Longrightarrow> \<forall>n\<in>S. n \<le> m \<Longrightarrow> \<exists>i\<in>S. \<forall>n\<in>S. i \<ge> n"
  apply (induct S rule: finite_induct; clarsimp)
  by (metis (no_types, lifting) empty_iff linorder_linear order_trans)

lemma maximal_exists: " ((S :: u64 set) \<noteq> {}) \<Longrightarrow> \<forall>n\<in>S. n \<le> m \<Longrightarrow> \<exists>i\<in>S. \<forall>n\<in>S. i \<ge> n"
  apply (rule maximal_helper)
  using finite_code apply blast
  by (auto)


lemma (in hoare_logic) sqrt_exists_uniquely:  "\<exists>!m. (sqrt n m)"
  apply (rule exists_singularI)
   apply (induct n rule:word_induct2 ; clarsimp?)
    apply (rule_tac x=0 in exI)
    apply (clarsimp simp: sqrt_def)
  using word_neq_0_conv apply fastforce
   apply (case_tac "n = 0"; clarsimp?)
    apply (rule_tac x=1 in exI)
  apply (simp add: sqrt_iff_defined)
   apply (insert maximal_exists[where S="{x. x * x div x = x \<and>  x * x \<le> (_ + 1)}"])
   apply (atomize)
  apply (erule_tac x="n" in allE)
   apply (erule_tac x="(n + 1) div 2" in allE)
   apply (drule mp)
    apply (clarsimp)
    apply (rule_tac x=0 in exI; clarsimp)
   apply (drule mp)
    apply (clarsimp)
  apply (unat_arith, clarsimp)
    defer
    apply (clarsimp)
    apply (rule_tac x=i in exI)
    apply (clarsimp simp: sqrt_iff_defined)
    apply (intro conjI; clarsimp?)
     apply (clarsimp simp: add.commute)
    apply (metis add.commute linorder_not_le)
  using sqrt_unique apply presburger
  apply (subst (asm) unat_mul_simp) back
   apply (metis unat_div word_eq_unatI x_square_defined_iff)
  by (smt (verit, best) One_nat_def bot_nat_0.not_eq_extremum div_le_dividend
                        le_less_Suc_eq less_eq_div_iff_mult_less_eq linorder_le_less_linear 
                        mult_2 mult_2_right nat.inject nat_div_eq_Suc_0_iff numeral_2_eq_2
                        one_add_one order_le_less_trans unat_div unat_mult_lem word_eq_unatI 
                        x_square_defined_iff zero_less_numeral)

lemma (in hoare_logic) sqrt_induct: 
  "(\<And>p. (p * p) \<le> n \<Longrightarrow> p * p div p = p \<Longrightarrow>  (p < p + 1 \<Longrightarrow> (p + 1) * (p + 1) div (p + 1) = (p + 1) \<Longrightarrow> (p + 1) * (p + 1) > n) \<Longrightarrow> P p) \<Longrightarrow>
   P (sqrt' n)"
  apply (clarsimp simp: sqrt'_def)
  apply (rule the1I2)
   apply (rule sqrt_exists_uniquely)
  apply (clarsimp simp: sqrt_iff_defined)
  done

lemma  (in hoare_logic) word_sqrt_ge: 
 "x \<le> x + n div x \<Longrightarrow> x \<le> n \<Longrightarrow> x \<ge> sqrt' n \<Longrightarrow> (x + n div x) div 2 \<ge> sqrt' n"
  apply (induct rule: sqrt_induct)
  apply (unat_arith, clarsimp)
   apply (rule ge_sqrt)
    apply (metis div_le_mono th2)
   apply (assumption)
  apply (clarsimp)
  by (meson Nat.le_diff_conv2 div_le_dividend leD le_trans linorder_le_less_linear nat_add_left_cancel_le)




  

lemma "unat (n :: 2 word) < unat (x + 1) * unat (x + 1) \<Longrightarrow> n < n + 1 \<Longrightarrow> x \<le> n \<Longrightarrow>
       unat n < unat ((x + n div x) div 2 + 1) * unat ((x + n div x) div 2 + 1)" 
  apply (erule diff_lessE)
  apply (subgoal_tac "x + 1 \<noteq> 0")
   apply (subst unatSuc2, clarsimp)+
  apply (metis add_cancel_right_right bits_div_0 div_less_dividend_word less_is_non_zero_p1 one_add_one zero_neq_one)
    apply (subst unatSuc2, clarsimp)+
  apply (metis add_cancel_right_right bits_div_0 div_less_dividend_word less_is_non_zero_p1 one_add_one zero_neq_one)
   apply (clarsimp)
  oops

lemma (in hoare_logic) sqrt_le  : "sqrt' n \<le> n"
  apply (induct rule: sqrt_induct)
  by (metis (no_types, lifting) antisym_conv1 dual_order.strict_trans1 not_le_imp_less
                                order_less_imp_le word_coorder.extremum_strict word_div_less)


lemma (in hoare_logic) sqrt_le_eqI: "sqrt' n \<le> x \<Longrightarrow> x * x \<le> n \<Longrightarrow>  x * x div x = x \<Longrightarrow>  x = sqrt' n"
  apply (rule sqrt_eqI[symmetric], clarsimp simp: sqrt_def)
  by (metis order_le_less_trans sqrt_def sqrt_eqI sqrt_exists_uniquely)

lemma div_2_helper: "na < na + 2 \<Longrightarrow> (2 + na :: u64) div 2 = 1 + (na div 2)"
 
  by (simp add: add.commute div_helper)




lemma midpoint_leI: "n div x \<le> x + 3 \<Longrightarrow>  ((x :: nat) + n div x) div 2 \<le> x + 1" 
  by linarith



lemma midpoint_leD: " ((x :: nat) + n div x) div 2 \<le> x + 1 \<Longrightarrow> n div x \<le> x + 3 " 
  by linarith

lemma "Suc (na mod x) = x \<Longrightarrow> Suc na div x = Suc (na div x)"
  by (meson div_Suc mod_Suc)

lemma div_induct: "(\<And>k. k * (x :: nat) = n - (n mod x) \<Longrightarrow> P k) \<Longrightarrow> P (n div x)" 
  by (metis minus_mod_eq_div_mult)

lemma le_mul_mono: "x * y \<le> x * z \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> y \<le> (z :: nat)"
  by fastforce


lemma ge_sqrt_by_three:"(x + 1) * (x + 1) \<ge> n \<Longrightarrow> (n :: nat) div x \<le> x + 3"
  apply (case_tac "x=0"; clarsimp)
  apply (rule div_induct)
  apply (rule le_mul_mono[where x=x])
   apply (subst mult.commute)
   apply (simp)
proof -
  fix k :: nat
  assume a1: "k * x = n - n mod x"
  assume a2: "n \<le> Suc (x + (x + x * x))"
  have f3: "\<forall>n na nb. (n::nat) \<le> na + (n + nb)"
    by simp
  have f4: "n \<le> Suc (x * Suc (Suc x))"
    using a2 by simp
  have "\<forall>na. x * k \<le> na \<or> na < n"
    using f3 a1 by (metis add.commute add_diff_inverse_nat minus_mod_eq_mult_div mod_div_decomp mult.commute)
  then have "x * k \<le> x * (x + Suc (Suc 1))"
    using f4 f3 by (smt (z3) Suc_eq_plus1 Suc_le_eq add.commute add_Suc_shift add_diff_inverse_nat less_Suc_eq_le linorder_not_less mult_Suc_right nat_add_left_cancel_le th2)
  then show "n - n mod x \<le> x * (x + 3)"
    using a1 by (smt (z3) One_nat_def Suc_eq_plus1 mult.commute numeral_2_eq_2 numeral_One numeral_plus_numeral semiring_norm(5))
next
  assume "0 < x"
  then show "x \<noteq> 0"
    by auto
qed


lemma theE: "P (THE x. Q x) \<Longrightarrow> \<exists>!y. Q y  \<Longrightarrow> (\<And>x. Q x \<Longrightarrow> P x \<Longrightarrow> R) \<Longrightarrow>  R"
  by (metis theI)

find_theorems "unat ?n \<le> _"


lemma unat_max: "unat (n :: 64 word) \<le>  (2 ^  64) - 1"
  apply (rule word_unat_less_le)
  apply (unat_arith, clarsimp)
  done
sledgehammer

lemma le_suc_le: "x \<le> y \<Longrightarrow> Suc x \<le> Suc y"
  by force
 
lemma unat_sqrt_ge_trans: "(sqrt' n) \<le>  x \<Longrightarrow> x < x + 1 \<Longrightarrow> unat n \<le> (unat x + 1) * (unat x + 1)"
  apply (clarsimp simp: sqrt'_def)
  apply (erule theE)
   apply (simp add: sqrt_exists_uniquely)
  apply (clarsimp simp: sqrt_def)
  apply (erule_tac x="x + 1" in allE)
  apply (drule mp)
   apply force
  apply (case_tac "(x + 1) * (x + 1) div (x + 1) = x + 1")
  apply (drule mp, clarsimp)
   apply (smt (verit, del_insts) Suc_eq_plus1 add_Suc add_mult_distrib2 less_imp_le_nat less_is_non_zero_p1 mult_Suc nat_mult_1_right unat_mono unat_mult_simp word_overflow_unat x_square_defined_iff)
  apply (clarsimp simp: x_square_defined_iff)
  apply (subst (asm) unat_Suc2)
  using word_not_simps(3) apply blast
  apply (subst (asm) unat_Suc2)
  using word_not_simps(3) apply blast
  apply (clarsimp)
  apply (clarsimp simp: smt_arith_simplify(267))
  apply (drule le_suc_le)
  apply (erule order_trans[rotated])
  apply (clarsimp simp: smt_arith_simplify) 
  apply (rule order_trans[where y="2^64 - 1"])
   apply (rule unat_max)
  apply (clarsimp)
  done



lemma  (in hoare_logic) ge_sqrt_helper: assumes well_defined: "x < x + 1"  shows "x \<le> (n :: u64) \<Longrightarrow> x < x + n div x \<Longrightarrow> x < x + 1 \<Longrightarrow> x \<ge> sqrt' n \<Longrightarrow>
       (x + n div x) div 2 \<le> x + 1" 
  apply (unat_arith, clarsimp)
   apply (rule order_trans, rule midpoint_leI, rule ge_sqrt_by_three)
    apply (rule unat_sqrt_ge_trans)
  using word_le_nat_alt apply blast
  using well_defined apply blast
   apply linarith
  apply (clarsimp)
  by (smt (verit, best) Nat.diff_diff_right diff_le_self div_le_dividend leD le_trans less_imp_le_nat)
  
 

lemma (in hoare_logic)" (\<And>n. hoare_triple (P n) (c n) Q) \<Longrightarrow> 
   hoare_triple (\<lambda>s. n < n + 1 \<and> (n < n + 1 \<longrightarrow> P (sqrt' n) s))
  (bindCont (integer_squareroot n) c) Q"
  apply (case_tac "n = 0", clarsimp)
  find_theorems name:induct "_ :: u64"
  apply (rule hoare_weaken_pre)
    apply (clarsimp simp: integer_squareroot_def)
  apply (wp)
    apply (clarsimp)
    apply (clarsimp simp: bind_assoc bindCont_return')
    apply (wp)
   apply (clarsimp)
  apply (rule hoare_weaken_pre)
   apply (subst integer_squareroot_def )
   apply (simp only: bindCont_assoc[symmetric] bindCont_return' Let_unfold)+
   apply (rule wp)+
   apply (simp only: bindCont_assoc[symmetric] bindCont_return')?
  apply (rule 
           integer_squareroot_aux_wp[where I="(\<lambda>x y n. y \<noteq> 0 \<and> y \<le> y + (n div y) \<and> x \<le> n 
                                            \<and> x + 1 \<ge> y \<and> x \<ge> sqrt' n \<and>
                                               y = (x + (n div x)) div 2 )"])
    apply (clarsimp)
  apply (simp only: bindCont_assoc[symmetric] bindCont_return')?
    apply (atomize)
    apply (erule_tac x="fst (a, b)" in allE)
    apply (subst (asm) fst_conv, assumption) 
    apply (blast)
  apply (clarsimp)
  apply (intro context_conjI impI allI; clarsimp?)+
          apply (fastforce)
  apply (metis (no_types, opaque_lifting) inc_i lt1_neq0 not_less_iff_gr_or_eq one_add_one word_le_less_eq word_less_div)
                apply (smt (verit) add_diff_cancel_right' add_diff_eq diff_numeral_special(9) 
div_helper div_mod_step mult_2 not_less_iff_gr_or_eq order_le_less sub_wrap_lt times_2_cases word_div_lt_eq_0 word_leq_minus_one_le)
          apply (simp add: div_less_dividend_word less_is_non_zero_p1 word_le_less_eq)
  apply (rule sqrt_le)

      apply (simp add: div_word_self)
       apply (subgoal_tac "x = (sqrt' n)", clarsimp)
       apply (rule sqrt_le_eqI, assumption)
        apply (subgoal_tac " x = (x + n div x) div 2 \<or> x = (x + n div x) div 2 - 1")
         apply (elim disjE)
  using local.square_less_than apply fastforce
  apply (metis leI le_div_timesI order_less_imp_le word_le_plus_either word_must_wrap yet_another_helper)
     (*   apply (metis (no_types, lifting) diff_eq_eq le_step_down_word word_must_wrap) *)
  
  apply (metis (no_types, lifting) antisym_conv1 eq_diff_eq word_le_minus_one_leq word_must_wrap)

  
         apply (smt (z3) add.commute antisym_conv2 diff_add_cancel 
                         div_less_dividend_word div_lt' div_to_mult_word_lt dual_order.strict_iff_not 
                         eq_2_64_0 less_x_plus_1 mult_2 mult_2_right 
                         one_add_one times_2_cases u64_max word_coorder.extremum_unique
                         word_le_not_less word_plus_mcs_4 word_random x_square_defined_iff)
    apply (metis (no_types, lifting) add_cancel_right_right le_step_down_word lt1_neq0 
           mult_zero_right times_2_cases word_coorder.extremum_uniqueI word_less_1 word_less_div)
  
  apply (smt (verit, ccfv_SIG) add_cancel_left_right another_helper dual_order.order_iff_strict linorder_le_less_linear word_div_less word_le_plus_either)
    apply force
  defer
   apply (meson another_helper word_le_plus_either word_sqrt_ge)
  apply (rule ge_sqrt_helper)
  using less_is_non_zero_p1 word_overflow apply blast
     apply (assumption)
    apply (meson add_cancel_right_right antisym_conv1 leD word_less_div)
  using less_is_non_zero_p1 word_overflow apply blast
  by (meson another_helper word_le_plus_either word_sqrt_ge)
       

end


end