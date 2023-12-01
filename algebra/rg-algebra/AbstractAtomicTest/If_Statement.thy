section \<open>Conditionals\<close>
  
theory If_Statement
imports   
  "Expressions"
begin

(* Used to represent the constraint that the value type used for expressions need to contain
   a value for 'true' and 'false' (i.e. the booleans). *)
class has_booleans =
  fixes true :: "'a"
  fixes false :: "'a"
  assumes has_booleans_distinct: "true \<noteq> false"

abbreviation boolean :: "'v::has_booleans set" 
  where "boolean \<equiv> {true, false}"

locale if_statement = expressions (* _ _ bool_first_sets
  for bool_first_sets :: "'d \<Rightarrow> 'b set \<Rightarrow> 'b set" ("F\<^sup>S\<^sub>_ _" [999, 999] 999) *)
begin                     

(* The set of states in which the given expression (if evaluated in that state) has the given type 
   (as denoted by the set of values in that type.)*)
definition expr_type :: "('b,'v) expr \<Rightarrow> 'v set \<Rightarrow> 'b set"
  where "expr_type e type \<equiv> \<Union>val\<in>type. expr_eq e val"

definition if_statement :: "('b,'v::has_booleans) expr \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a \<Rightarrow> 'a"
 ( "(If_then_else_)" 40)
  where "if_statement b c d = (\<lbrakk>b\<rbrakk>(true);c \<squnion> \<lbrakk>b\<rbrakk>(false);d \<squnion> (\<Squnion>k\<in>-boolean. \<lbrakk>b\<rbrakk>(k);\<top>));idle"

lemma if_mono_left:
  assumes "c0 \<ge> c1"
  shows "(If b then c0 else d) \<ge> (If b then c1 else d)"
    using if_statement_def assms seq_mono_right nondet_mono_left seq_mono_left by metis

lemma if_mono_right:
  assumes "d0 \<ge> d1"
  shows "(If b then c else d0) \<ge> (If b then c else d1)"
    using if_statement_def assms seq_mono_right nondet_mono_left nondet_mono_right seq_mono_left by metis

lemma guar_conditional_distrib:
  assumes g_reflexive: "refl g"
  shows "(guar g) \<iinter> (If b then c else d) \<ge> (If b then (guar g) \<iinter> c else (guar g) \<iinter> d)"
proof -
  have "(guar g) \<iinter> (If b then c else d) \<ge> ((guar g) \<iinter> (\<lbrakk>b\<rbrakk>(true));c \<squnion>
                                            (guar g) \<iinter> (\<lbrakk>b\<rbrakk>(false));d \<squnion>
                                            (guar g) \<iinter> (\<Squnion>k\<in>-boolean. \<lbrakk>b\<rbrakk>(k);\<top>));idle" (is "_ \<ge> ?rhs")
    unfolding if_statement_def using g_reflexive guar_idle guar_distrib_seq guar_distrib_nondet by metis
  also have "?rhs \<ge> ((\<lbrakk>b\<rbrakk>(true));((guar g) \<iinter> c) \<squnion>
                    (\<lbrakk>b\<rbrakk>(false));((guar g) \<iinter> d) \<squnion>
                    (\<Squnion>k\<in>-boolean. \<lbrakk>b\<rbrakk>(k);\<top>));idle" (is "_ \<ge> ?rhs")
  proof -
    have a1: "\<And>v c. (guar g) \<iinter> (\<lbrakk>b\<rbrakk>v);c \<ge> (\<lbrakk>b\<rbrakk>v);((guar g) \<iinter> c)"
      using guar_distrib_seq eval_guar_absorb seq_mono_left g_reflexive by metis
    have a2: "\<And>k. (guar g) \<iinter> \<lbrakk>b\<rbrakk>(k);\<top> \<ge> \<lbrakk>b\<rbrakk>(k);\<top>" 
      using a1 conj_abort_right by metis
    have a3: "(guar g) \<iinter> (\<Squnion>k\<in>-boolean. \<lbrakk>b\<rbrakk>(k);\<top>) \<ge> (\<Squnion>k\<in>-boolean. (\<lbrakk>b\<rbrakk>(k));\<top>)"
      using guar_distrib_Nondet a2 by (simp add: NONDET_mono_quant SUP_image)
    show ?thesis using a1 a3 sup_mono seq_mono_left by metis
  qed
  finally show ?thesis unfolding if_statement_def by simp
qed

lemma rely_conditional:
  assumes single_reference_b: "single_reference b r"
  assumes tolerate_interference: "tolerates_interference p q r"
  assumes b_boolean: "p \<subseteq> expr_type b boolean"
  assumes pb_establishes_b0: "p \<inter> (expr_eq b (true)) \<subseteq> b0"
  assumes pr_maintains_b0: "stable b0 (p \<triangleleft> r)" 
  assumes pnegb_establishes_b1: "p \<inter> (expr_eq b (false)) \<subseteq> b1"
  assumes pr_maintains_b1: "stable b1 (p \<triangleleft> r)"
  shows "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> \<ge> (If b then ((rely r)\<iinter> \<lbrace>b0 \<inter> p\<rbrace>; \<lparr>q\<rparr>) else ((rely r)\<iinter> \<lbrace>b1 \<inter> p\<rbrace>; \<lparr>q\<rparr>))"
proof -
  have "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> \<ge> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>;idle" (is "_ \<ge> ?rhs")
    using tolerate_interference tolerate_interference_right by simp 
  also have "?rhs \<ge> ((rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>);((rely r) \<iinter> idle)" (is "_ \<ge> ?rhs")
    using rely_seq_distrib by simp
  also have "?rhs \<ge> ((rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>);idle" (is "_ \<ge> ?rhs")
    using rely_remove seq_mono_right by simp
  also have "?rhs \<ge> ((rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* O q\<rparr> \<squnion>
                    (rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* O q\<rparr> \<squnion>
                    (rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* O q\<rparr>);idle" (is "_ \<ge> ?rhs")
    using sup_idem spec_strengthen q_tolerates_rtrancl_left
          tolerate_interference conj.sync_mono_right seq_mono_left
    by (metis seq_mono_right assert_restricts_spec) 
  also have "?rhs \<ge> ((rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> (b0 \<inter> p)\<rparr>; \<lbrace>b0 \<inter> p\<rbrace>; \<lparr>q\<rparr> \<squnion> 
                     (rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> (b1 \<inter> p)\<rparr>; \<lbrace>b1 \<inter> p\<rbrace>; \<lparr>q\<rparr> \<squnion> 
                     (rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> {}\<rparr>;\<lbrace>\<bottom>\<rbrace>; \<lparr>q\<rparr>);idle" (is "_ \<ge> ?rhs")
    using seq_assoc seq_mono_left conj.sync_mono_right seq_mono_right spec_seq_introduce by simp
    also have "?rhs \<ge> (((rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> (b0 \<inter> p)\<rparr>);((rely r) \<iinter> \<lbrace>b0 \<inter> p\<rbrace>; \<lparr>q\<rparr>) \<squnion>
                    ((rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> (b1 \<inter> p)\<rparr>);((rely r) \<iinter> \<lbrace>b1 \<inter> p\<rbrace>; \<lparr>q\<rparr>) \<squnion>
                    ((rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> {}\<rparr>);\<top>);idle" (is "_ \<ge> ?rhs")
    using sup_mono seq_mono_left rely_seq_distrib conj_abort_right
    by (metis (no_types) assert_bot seq_assoc seq_abort)
  also have "?rhs \<ge> (\<lbrakk>b\<rbrakk>(true);((rely r) \<iinter> \<lbrace>b0 \<inter> p\<rbrace>; \<lparr>q\<rparr>) \<squnion>
                    \<lbrakk>b\<rbrakk>(false);((rely r) \<iinter> \<lbrace>b1 \<inter> p\<rbrace>; \<lparr>q\<rparr>) \<squnion>
                    (\<Squnion>k\<in>-{true,false}. \<lbrakk>b\<rbrakk>(k));\<top>);idle" (is "_ \<ge> ?rhs")
  proof -
    have "(rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> (b0 \<inter> p)\<rparr> \<ge> \<lbrakk>b\<rbrakk>(true)" 
      using rely_eval_expr pb_establishes_b0 pr_maintains_b0 single_reference_b
            tolerate_interference inf_commute unfolding tolerates_interference_def by metis
    moreover have "(rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> (b1 \<inter> p)\<rparr> \<ge> \<lbrakk>b\<rbrakk>(false)"
      using rely_eval_expr pnegb_establishes_b1 pr_maintains_b1 single_reference_b
            tolerate_interference inf_commute unfolding tolerates_interference_def by metis
    moreover have "(rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> {}\<rparr> \<ge> (\<Squnion>k\<in>-boolean. \<lbrakk>b\<rbrakk>(k))"
    proof (rule SUP_least)
      fix k::'c
      assume a1: "k \<in> -{true,false}"
      have "p \<inter> expr_eq b k \<subseteq> {}" using b_boolean a1 unfolding expr_type_def expr_eq_def by auto
      moreover have "stable {} (p \<triangleleft> r)" unfolding stable_def by auto
      moreover have "(p \<inter> {}) = {}" by auto
      ultimately show "(rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> {}\<rparr> \<ge> \<lbrakk>b\<rbrakk>(k)" 
        using rely_eval_expr single_reference_b
            tolerate_interference unfolding tolerates_interference_def by metis
    qed
    ultimately show ?thesis using seq_mono_left sup_mono by metis
  qed
  also have "?rhs = (If b then ((rely r)\<iinter> \<lbrace>b0 \<inter> p\<rbrace>; \<lparr>q\<rparr>) else ((rely r)\<iinter> \<lbrace>b1\<inter>p\<rbrace>; \<lparr>q\<rparr>))"
    using NONDET_seq_distrib if_statement_def by metis
  finally show ?thesis .
qed

end
  
end