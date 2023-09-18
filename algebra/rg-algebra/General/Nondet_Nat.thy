section \<open>Non-deterministic choice indexed over a set of natural numbers\label{S:infimum-nat}\<close>

theory Nondet_Nat
imports 
  Refinement_Lattice
begin

locale nondet_nat
begin

lemma Nondet_partition_nat3: 
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::refinement_lattice"
  shows "(\<Squnion>j. f i j) =
    (\<Squnion>j\<in>{j. i = j}. f i j) \<squnion>
    (\<Squnion>j\<in>{j. i < j}. f i j) \<squnion>
    (\<Squnion>j\<in>{j. j < i}. f i j)"
proof -
  have univ_part: "UNIV = {j. i = j} \<union> {j. i < j} \<union> {j. j < i}" by auto
  have "(\<Squnion>j \<in> {j. i = j} \<union> {j. i < j} \<union> {j. j < i}. f i j) =
          (\<Squnion>j\<in>{j. i = j}. f i j) \<squnion>
          (\<Squnion>j\<in>{j. i < j}. f i j) \<squnion>
          (\<Squnion>j\<in>{j. j < i}. f i j)" by (metis SUP_union)
  with univ_part show ?thesis by simp
qed

lemma Nondet_Nondet_partition_nat3: 
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::refinement_lattice"
  shows "(\<Squnion>i. \<Squnion>j. f i j) =
    (\<Squnion>i. \<Squnion>j\<in>{j. i = j}. f i j) \<squnion>
    (\<Squnion>i. \<Squnion>j\<in>{j. i < j}. f i j) \<squnion>
    (\<Squnion>i. \<Squnion>j\<in>{j. j < i}. f i j)"
proof -
  have "(\<Squnion>i. \<Squnion>j. f i j) = (\<Squnion>i. ((\<Squnion>j\<in>{j. i = j}. f i j) \<squnion>
                                  (\<Squnion>j\<in>{j. i < j}. f i j) \<squnion>
                                  (\<Squnion>j\<in>{j. j < i}. f i j)))"
    by (simp add: Nondet_partition_nat3)
  also have "... = (\<Squnion>i. \<Squnion>j\<in>{j. i = j}. f i j) \<squnion>
                   (\<Squnion>i. \<Squnion>j\<in>{j. i < j}. f i j) \<squnion>
                   (\<Squnion>i. \<Squnion>j\<in>{j. j < i}. f i j)"
    by (simp add: complete_lattice_class.SUP_sup_distrib)
  finally show ?thesis .
qed

lemma NONDET_nat_shift: "(\<Squnion>i\<in>{i. 0 < i}. f i) = (\<Squnion>i. f (Suc i))"
  by (metis greaterThan_0 greaterThan_def range_composition)

lemma NONDET_nat_minus:
  fixes f :: "nat \<Rightarrow> 'a::refinement_lattice"
  shows "(\<Squnion>j\<in>{j. i < j}. f (j - i)) = (\<Squnion>k\<in>{k. 0 < k}. f k)"
  apply (rule antisym)
  apply (rule SUP_mono, simp)
  apply (meson eq_iff zero_less_diff)
  apply (rule SUP_mono, simp)
  by (metis add_diff_cancel_right' less_add_same_cancel2 order_refl)

(* TODO: generalise to P j i? *)
lemma Nondet_NONDET_guarded_switch:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::refinement_lattice"
  shows "(\<Squnion>i. \<Squnion>j\<in>{j. j < i}. f j (i - j)) = (\<Squnion>j. \<Squnion>i\<in>{i. j < i}. f j (i - j))"
proof (rule antisym)
  have "\<And>jj ii. jj < ii \<Longrightarrow> \<exists>i. \<exists>j<i. f j (i - j) \<ge> f jj (ii - jj)"
    by blast
  then have "\<And>jj ii. jj < ii \<Longrightarrow> \<exists>i. (\<Squnion>j\<in>{j. j < i}. f j (i - j)) \<ge> f jj (ii - jj)"
    by (meson SUP_upper mem_Collect_eq)
  then have "\<And>jj ii. jj < ii \<Longrightarrow> (\<Squnion>i. \<Squnion>j\<in>{j. j < i}. f j (i - j)) \<ge> f jj (ii - jj)"
    by (meson UNIV_I SUP_upper dual_order.trans)
  then have "\<And>jj. (\<Squnion>i. \<Squnion>j\<in>{j. j < i}. f j (i - j)) \<ge> (\<Squnion>ii\<in>{ii. jj < ii}. f jj (ii - jj))"
    by (metis (mono_tags, lifting) SUP_least mem_Collect_eq)
  then have "(\<Squnion>i. \<Squnion>j\<in>{j. j < i}. f j (i - j)) \<ge> (\<Squnion>jj. \<Squnion>ii\<in>{ii. jj < ii}. f jj (ii - jj))"
    by (simp add: SUP_least)
  then show "(\<Squnion>i. \<Squnion>j\<in>{j. j < i}. f j (i - j)) \<ge> (\<Squnion>j. \<Squnion>i\<in>{i. j < i}. f j (i - j))"
    by simp
next
  have "\<And>ii jj. jj < ii \<Longrightarrow> \<exists>j. \<exists>i>j. f j (i - j) \<ge> f jj (ii - jj)"
    by blast
  then have "\<And>ii jj. jj < ii \<Longrightarrow> \<exists>j. (\<Squnion>i\<in>{i. j < i}. f j (i - j)) \<ge> f jj (ii - jj)"
    by (meson SUP_upper mem_Collect_eq)
  then have "\<And>ii jj. jj < ii \<Longrightarrow> (\<Squnion>j. \<Squnion>i\<in>{i. j < i}. f j (i - j)) \<ge> f jj (ii - jj)"
    by (meson UNIV_I SUP_upper dual_order.trans)
  then have "\<And>ii. (\<Squnion>j. \<Squnion>i\<in>{i. j < i}. f j (i - j)) \<ge> (\<Squnion>jj\<in>{jj. jj < ii}. f jj (ii - jj))"
    by (metis (mono_tags, lifting) SUP_least mem_Collect_eq)
  then have "(\<Squnion>j. \<Squnion>i\<in>{i. j < i}. f j (i - j)) \<ge> (\<Squnion>ii. \<Squnion>jj\<in>{jj. jj < ii}. f jj (ii - jj))"
    by (simp add: SUP_least)
  then show "(\<Squnion>j. \<Squnion>i\<in>{i. j < i}. f j (i - j)) \<ge> (\<Squnion>i. \<Squnion>j\<in>{j. j < i}. f j (i - j))"
    by simp
qed

end

end
