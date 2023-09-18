chapter \<open>Examples\<close>

section \<open>Sieve refinement development\<close>
 
theory SieveAtomic
imports
  "../AbstractAtomicTest/Constrained_Atomic_Commands"
  "../AbstractAtomicTest/Programming_Constructs"
  "../AbstractAtomicTest/IntroPar_Big"
  "HOL.Complex"
begin
  
(* The state 's' of the Sieve example is just a set of natural numbers.  *)
type_synonym sieve_state = "nat set"
  
locale sieve_nums
begin

definition comp_nums :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
"comp_nums n i \<equiv> { i * j | j . 2 \<le> j \<and> i * j \<le> n}"

definition comp_range :: "nat \<Rightarrow> nat set" where
"comp_range n \<equiv> { i . 2 \<le> i \<and> i \<le> sqrt n }"

definition Comp_nums :: "nat \<Rightarrow> nat set" where
"Comp_nums n \<equiv> \<Union> i \<in> comp_range n . comp_nums n i"
  
lemma finite_comp_range: "finite (comp_range n)"
proof -
  have "\<forall>na::nat. (2::nat) \<le> na \<and> (na \<le> (sqrt n)) \<longrightarrow> na \<le> nat (ceiling (sqrt n))"
    by linarith
  then have "\<exists>m::nat. \<forall>(na::nat)\<in>{ (i::nat) . (2::nat) \<le> i \<and> i \<le> sqrt n }. na \<le> m"
    by blast
  then have "finite({ i::nat . (2::nat) \<le> i \<and> i \<le> sqrt n })" 
    using finite_nat_set_iff_bounded_le by blast
  then have "finite(comp_range n)"
    using comp_range_def by simp
  thus ?thesis by simp
qed

lemma comp_range_non_empty: 
  assumes "n \<ge> 4"
  shows "comp_range n \<noteq> {}"
proof -
  have "n \<ge> 4 \<Longrightarrow> (2::nat) \<le> (2::nat) \<and> (2::nat) \<le> sqrt n"
    using real_le_rsqrt by simp
  then have "n \<ge> 4 \<Longrightarrow> (2::nat) \<in> comp_range n"
    using comp_range_def by simp
  then have "n \<ge> 4 \<Longrightarrow> comp_range n \<noteq> {}"
    by blast
  then show ?thesis using assms by simp
qed
    
end
  
locale sieve_pre = constrained_atomic +
  constrains test :: "sieve_state set \<Rightarrow> 'a"
  constrains pgm :: "sieve_state rel \<Rightarrow> 'a"
  constrains env :: "sieve_state rel \<Rightarrow> 'a"
begin
end
  
locale sieve = sieve_nums + sieve_pre + programming_constructs + intro_par_big
begin
  
definition RemMults :: "nat \<Rightarrow> nat \<Rightarrow> 'a"
  where "RemMults n i = (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> (comp_nums n i)})
               \<iinter> rely({(s,s').s' \<subseteq> s}) \<iinter> \<lparr>{(s, s'). s' \<inter> (comp_nums n i) = {}}\<rparr>"
  
lemma sieve_proof:
  (* n \<ge> 4 ensures there is at least one composite to remove. *)
  assumes n4: "n \<ge> 4"
  assumes cnums_def: "C = Comp_nums n"
  shows "(rely ({(s, s'). s' = s})) \<iinter> \<lparr>{(s, s'). s' = s - C}\<rparr> \<ge>
           (\<parallel>\<parallel>\<in>comp_range n. (\<lambda>i. RemMults n i))"
proof -  
  have finite: "finite (comp_range n)"
    using finite_comp_range by simp
  have nonempty: "(comp_range n) \<noteq> {}"
    using comp_range_non_empty n4 by simp
  have "(rely ({(s, s'). s' = s})) \<iinter> \<lparr>{(s, s'). s' = s - C}\<rparr>
    = (rely ({(s, s'). s' = s})) \<iinter> \<lparr>{(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C} \<inter> {(s, s'). s' \<inter> C = {}}\<rparr>"
  proof -  
    have "{(s, s'). s' = s - C} = {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C} \<inter> {(s, s'). s' \<inter> C = {}}"
      by blast
    thus ?thesis by simp
  qed
  also have "... = (rely ({(s,s').s' = s})) \<iinter>
             \<lparr>({(s, s'). s' = s} \<union> {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C})\<^sup>* \<inter> {(s,s'). s' \<inter> C = {} }\<rparr>"
  proof -     
    have a1: "{(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C} = {(s, s'). s' = s} \<union> {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}"
      by auto
    have "trans {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}" using trans_def by blast
    then have "{(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C} = {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}\<^sup>+" by simp
    then have "{(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C} = {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}\<^sup>*"
      using rtrancl_trancl_reflcl by blast
    then show ?thesis using a1 by simp
  qed
  also have "... \<ge> (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}) \<iinter> (rely ({(s,s').s' = s}))
                     \<iinter> \<lparr>{(s, s'). s' \<inter> C = {}}\<rparr>" (is "_ \<ge> ?rhs")
    using spec_trading conj_commute conj.sync_mono_left guar_introduce
    by (metis (no_types, lifting))
  also have "?rhs = (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}) \<iinter> (rely ({(s,s').s' = s}))
                     \<iinter> \<lparr>(\<Sqinter>i\<in>comp_range n. {(s, s'). s' \<inter> (comp_nums n i) = {}})\<rparr>"
  proof -
    have "{(s, s'). s' \<inter> C = {}} =
           (\<Sqinter>i\<in>comp_range n. {(s, s'). s' \<inter> (comp_nums n i) = {}})"
      using Comp_nums_def cnums_def by auto
    then show ?thesis using conj_assoc by metis
  qed
  also have "... \<ge>  (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}) \<iinter> ((rely ({(s,s').s' \<subseteq> s}))
                     \<iinter> \<lparr>(\<Sqinter>i\<in>comp_range n. {(s, s'). s' \<inter> (comp_nums n i) = {}})\<rparr>)" (is "_ \<ge> ?rhs")
  proof -
    have "{(s,s').s' = s} \<le> {(s,s').s' \<subseteq> s}" by auto
    then have "rely ({(s,s').s' = s}) \<ge> rely ({(s,s').s' \<subseteq> s})" using rely_weaken by simp
    then show ?thesis using conj.sync_mono_left conj.sync_mono_right conj_assoc by fastforce
  qed
  also have "?rhs \<ge> (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}) \<iinter>
                   (\<parallel>\<parallel>\<in>comp_range n. (\<lambda>i. guar({(s,s').s' \<subseteq> s}) \<iinter> rely({(s,s').s' \<subseteq> s})
                                   \<iinter> \<lparr>{(s, s'). s' \<inter> (comp_nums n i) = {}}\<rparr>))" (is "_ \<ge> ?rhs")
  proof -
    have "(rely ({(s,s').s' \<subseteq> s})) \<iinter> \<lparr>(\<Sqinter>i\<in>comp_range n. {(s, s'). s' \<inter> (comp_nums n i) = {}})\<rparr> \<ge>
                (\<parallel>\<parallel>\<in>comp_range n. (\<lambda>i. guar({(s,s').s' \<subseteq> s}) \<iinter> rely({(s,s').s' \<subseteq> s})
                                   \<iinter> \<lparr>{(s, s'). s' \<inter> (comp_nums n i) = {}}\<rparr>))"
       using spec_introduce_par_big finite nonempty by metis
    then show ?thesis using conj.sync_mono_right by blast 
  qed
  also have "?rhs \<ge> (\<parallel>\<parallel>\<in>comp_range n. (\<lambda>i.  (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C})
                                   \<iinter> guar({(s,s').s' \<subseteq> s})
                                   \<iinter> rely({(s,s').s' \<subseteq> s})
                                   \<iinter> \<lparr>{(s, s'). s' \<inter> (comp_nums n i) = {}}\<rparr>))" (is "_ \<ge> ?rhs")
   using conj_setpar_distrib finite nonempty guar_merge conj_assoc sorry
  also have "?rhs = (\<parallel>\<parallel>\<in>comp_range n. (\<lambda>i.  (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C})
                                      \<iinter> rely({(s,s').s' \<subseteq> s})
                                     \<iinter> \<lparr>{(s, s'). s' \<inter> (comp_nums n i) = {}}\<rparr>))"
  proof -
    have  a1: "{(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C} \<inter> {(s,s').s' \<subseteq> s} = {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}"
      by auto
    have g1: "(guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}) \<iinter> (guar{(s,s').s' \<subseteq> s}) = (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C})"
      using a1 guar_merge by presburger 
    have "(\<lambda>i. (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}) \<iinter> guar({(s,s').s' \<subseteq> s})
                \<iinter> rely({(s,s').s' \<subseteq> s}) \<iinter> \<lparr>{(s, s'). s' \<inter> (comp_nums n i) = {}}\<rparr>) = 
          (\<lambda>i. (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}) \<iinter> rely({(s,s').s' \<subseteq> s})
                \<iinter> \<lparr>{(s, s'). s' \<inter> (comp_nums n i) = {}}\<rparr>)"
      using g1 by simp    
    then show ?thesis by metis
  qed
  also have "... \<ge> (\<parallel>\<parallel>\<in>comp_range n. (\<lambda>i.  (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> (comp_nums n i)})
                     \<iinter> rely({(s,s').s' \<subseteq> s}) \<iinter> \<lparr>{(s, s'). s' \<inter> (comp_nums n i) = {}}\<rparr>))" (is "_ \<ge> ?rhs")
  proof -
    have "\<forall>i\<in> comp_range n. ({(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> (comp_nums n i)}
                               \<subseteq> {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C})"
      using Comp_nums_def cnums_def by auto
    then have "\<forall>i\<in>comp_range n.  (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C}) \<ge>
                                 (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> (comp_nums n i)})"
      using guar_strengthen by simp     
    then have "\<forall>i\<in>comp_range n. (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> C})
                     \<iinter> rely({(s,s').s' \<subseteq> s}) \<iinter> \<lparr>{(s, s'). s' \<inter> (comp_nums n i) = {}}\<rparr> \<ge>
                           (guar {(s, s'). s' \<subseteq> s \<and> s - s' \<subseteq> (comp_nums n i)})
                     \<iinter> rely({(s,s').s' \<subseteq> s}) \<iinter> \<lparr>{(s, s'). s' \<inter> (comp_nums n i) = {}}\<rparr>"
      using conj.sync_mono_left by simp
    then show ?thesis using setpar_mono2 by simp
  qed
  also have "?rhs = (\<parallel>\<parallel>\<in>comp_range n. (\<lambda>i. RemMults n i))"
    using RemMults_def by simp
  finally show ?thesis .
qed
  
end

locale sieve2_pre = constrained_atomic +
  constrains test :: "(sieve_state \<times> nat) set \<Rightarrow> 'a"
  constrains pgm :: "(sieve_state \<times> nat) rel \<Rightarrow> 'a"
  constrains env :: "(sieve_state \<times> nat) rel \<Rightarrow> 'a"
begin
end

locale sieve2 = sieve_nums + sieve2_pre + programming_constructs + intro_par_big
begin
  
(* Similiar to definition for RemMults above, but we rely the newly introduced state variable
    m = m' *)
definition RemMults :: "nat \<Rightarrow> nat \<Rightarrow> 'a"
  where "RemMults n i = (guar {((s,m), (s',m')). s' \<subseteq> s \<and> s - s' \<subseteq> (comp_nums n i)})
                       \<iinter> rely({((s,m), (s',m')).s' \<subseteq> s \<and> m = m'}) 
                       \<iinter> \<lparr>{((s,m), (s',m')). s' \<inter> (comp_nums n i) = {}}\<rparr>"

definition Rem :: "'a"
  where "Rem = (guar {((s,m), (s',m')). s' \<subseteq> s \<and> s - s' \<subseteq> {m}}) 
              \<iinter> rely({((s,m), (s',m')).s' \<subseteq> s \<and> m = m'}) \<iinter> \<lparr>{((s,m),(s',m')). m \<notin> s'}\<rparr>"
    
lemma sieve_proof_loop:
  (* n \<ge> 4 ensures there is at least one composite to remove. *)
  assumes n4: "n \<ge> 4"
  shows "RemMults n i \<ge> \<lparr>{((s,m), (s',m')). m' = 2 * i }\<rparr>;
           (While (BinaryOp (\<lambda>m n. m \<le> n) (Variable (\<lambda>(s,m). m)) (Constant n))
            do (Rem;\<lparr>{((s,m),(s',m')). m' = m + i} \<rparr>))"
proof -
  define b where "b = ((BinaryOp (\<lambda>m n. m \<le> n) (Variable (\<lambda>(s::sieve_state,m::nat). m)) (Constant n)))"
  define v_dec where "v_dec = {(v::nat,v'). v < v' \<and> v \<ge> 0 }"
  define r where "r = {((s::sieve_state,m::nat), (s',m')).s' \<subseteq> s \<and> m = m'}"
  define p where "p = {(s::sieve_state,m::nat). s \<inter> (comp_nums (m - 1) i) = {}}"
  define acc where "acc = (\<lambda>(s::sieve_state,m::nat). m)"
  define b0 where "b0 = {(s::sieve_state,m::nat). m \<le> n }"
  define b1 where "b1 = {(s::sieve_state,m::nat). m > n }"
  have single_ref: "single_ref b r"
    using single_reference_binaryop single_reference_variable single_reference_constant 
          constant_expr_constant b_def by metis
  moreover have v_wellfounded: "wellfounded_on (Variant acc v_dec) p"
    unfolding wellfounded_on_def restrict_domain_def p_def acc_def v_dec_def sorry
  moreover have v_trans: "trans v_dec" 
    using v_dec_def by (simp add: trans_def)       
  moreover have "p \<triangleleft> r \<subseteq> range_restriction p"
    unfolding restrict_domain_def r_def p_def by auto
  moreover have "p \<triangleleft> r \<subseteq> (Variant acc (v_dec\<^sup>=))"
    unfolding restrict_domain_def r_def Variant_def using acc_def v_dec_def by auto
  moreover have "p \<inter> {s. (eval b s) = True} \<subseteq> b0"
    unfolding p_def b0_def b_def BinaryOp_eval Variable_eval Constant_eval by auto
  moreover have "((b0 \<inter> p) \<triangleleft> r) \<subseteq> range_restriction b0" 
    unfolding restrict_domain_def b0_def p_def r_def by auto
  moreover have "p \<inter> {s. eval b s = False} \<subseteq> b1"
    unfolding p_def b1_def b_def BinaryOp_eval Variable_eval Constant_eval by auto
  moreover have "((b1 \<inter> p) \<triangleleft> r) \<subseteq> range_restriction b1" 
    unfolding restrict_domain_def b1_def p_def r_def by auto
  ultimately have "(rely r) \<iinter> \<ltort>p, (Variant acc (v_dec\<^sup>=)) \<triangleright> (p \<inter> b1)\<rtort> \<sqsubseteq> 
        (While b do ((rely r)\<iinter>\<ltort>p\<inter>b0, (Variant acc v_dec) \<triangleright> p\<rtort>))"
    using rely_loop by simp
  then show ?thesis sorry 
qed

end  
  
end