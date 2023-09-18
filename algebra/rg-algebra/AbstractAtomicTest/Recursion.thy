theory Recursion
imports
  Expressions
begin

locale recursion = expressions (* lib_last
  for lib_last :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("L\<^sup>C\<^sub>_ _" [999, 999] 999) *)
begin

(* A slight variation to Lemma 50. r in this lemma maps to the converse of r
   in the other lemma, because this lemma uses the conventional definition
   of well-foundedness, as used in Isabelle.
   (\<forall>x. (\<forall>y. (y,x)\<in>r. P(y)) \<Rightarrow> P(x)) \<Rightarrow> (\<forall>x. P(x)) *)
lemma well_founded_variant:
  assumes r_wellfounded: "wf r"
  assumes refines: "\<And>k. (\<lbrace>fn_less v r k\<rbrace>;s \<ge> c) \<Longrightarrow> (\<lbrace>fn_eq v k\<rbrace>;s \<ge> c)"
  shows "s \<ge> c"
proof -
   (* (P x) is that s is refined by c under the condition variant v has the value x. *)
  define P where "P = (\<lambda>x. s \<ge> \<tau>(fn_eq v x);c)"
  have "\<forall>k::'c. (\<forall>j. (j,k)\<in>r \<longrightarrow> P j) \<longrightarrow> P k"
  proof 
    fix k
    have a1: "fn_less v r k = (\<Union>j\<in>{j.(j,k)\<in>r}. fn_eq v j)"  
      unfolding fn_less_def fn_eq_def by blast
    have "(s \<ge> \<tau>(fn_less v r k);c) \<longrightarrow> (s \<ge> \<tau>(fn_eq v k);c)"
      using refines by (simp add: assert_galois_test) 
    then have "(s \<ge> (\<Squnion>j\<in>{j.(j,k)\<in>r}. \<tau>(fn_eq v j);c)) \<longrightarrow> (s \<ge> \<tau>(fn_eq v k);c)"
      using test_Sup a1 by (simp add: NONDET_seq_distrib SUP_image)
    then have "(\<forall>j\<in>{j.(j,k)\<in>r}. (s \<ge> \<tau>(fn_eq v j);c)) \<longrightarrow> (s \<ge> \<tau>(fn_eq v k);c)"
      by (meson SUP_least)
    then show "(\<forall>j. (j,k)\<in>r \<longrightarrow> (P j)) \<longrightarrow> (P k)"
      using P_def by blast
  qed
  then have "\<forall>k::'c. P k"
    using r_wellfounded wf_def by metis
  then have "s \<ge> (\<Squnion>k. \<tau>(fn_eq v k);c)"
    by (simp add: P_def SUP_least)
  then show "s \<ge> c" by (metis NONDET_seq_distrib seq_nil_left fn_eq_all)
qed
  
lemma well_founded_recursion_early:
  assumes r_wellfounded: "wf r"
  assumes f_monotone: "mono f"
  assumes b_early: "\<lbrace>b\<rbrace>;s \<ge> gfp f"
  assumes refines: "\<forall>k::'c. (\<lbrace>fn_eq v k\<rbrace>;s \<ge> f(\<lbrace>(fn_less v r k) \<union> b\<rbrace>;s))"
  shows "s \<ge> gfp f"
proof -
  have "\<And>k::'c. \<lbrace>fn_less v r k\<rbrace>;s \<ge> gfp f \<longrightarrow> \<lbrace>fn_eq v k\<rbrace>;s \<ge> gfp f"
  proof
    fix k::'c
    assume assm: "\<lbrace>fn_less v r k\<rbrace>;s \<ge> gfp f"
    have "\<lbrace>fn_eq v k\<rbrace>;s \<ge> f(\<lbrace>(fn_less v r k) \<union> b\<rbrace>;s)" (is "_ \<ge> ?rhs")
      using refines by simp
    also have "?rhs = f(\<lbrace>fn_less v r k\<rbrace>;s \<sqinter> \<lbrace>b\<rbrace>;s)"
      using assert_inf by metis
    also have "... \<ge> f(gfp f)"
      using assm b_early f_monotone by (simp add: monoD)
    finally show "\<lbrace>fn_eq v k\<rbrace>;s \<ge> gfp f"      
      by (simp add: f_monotone gfp_fixpoint)
  qed
  then show ?thesis
    using r_wellfounded well_founded_variant by metis
qed

lemma well_founded_recursion:
  assumes r_wellfounded: "wf r"
  assumes f_monotone: "mono f"
  assumes refines: "\<forall>k::'c. \<lbrace>fn_eq v k\<rbrace>;s \<ge> f(\<lbrace>fn_less v r k\<rbrace>;s)"
  shows "s \<ge> gfp f"  
proof -
  define b where "b \<equiv> ({}::'b set)"
  have "\<lbrace>b\<rbrace>;s \<ge> gfp f" using b_def assert_bot by simp
  moreover have "\<forall>k::'c. (\<lbrace>fn_eq v k\<rbrace>;s \<ge> f(\<lbrace>(fn_less v r k) \<union> b\<rbrace>;s))"
    using refines b_def by auto  
  ultimately show ?thesis using well_founded_recursion_early r_wellfounded f_monotone by metis
qed

end
end