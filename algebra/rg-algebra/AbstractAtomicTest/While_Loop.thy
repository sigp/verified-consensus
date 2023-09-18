section \<open>While loops\<close>
  
theory While_Loop
imports
  "Recursion"
  "If_Statement"
begin

locale while_loop = recursion + if_statement (*_ bool_last_sets
  for bool_last_sets :: "'e \<Rightarrow> 'b set \<Rightarrow> 'b set" ("L\<^sup>S\<^sub>_ _" [999, 999] 999) *)
begin

(* The relation on program states that represents decreasing the specified variant.
   The first argument is the relation to decrease. It is a relation on the
   type of the variant ('c).
   The second argument is the variant, represented as an accessor function, from the 
   program state (of type 'b) to the value of the variant (of type 'c).

   Example. If the provided relation is the increment relation on naturals, (x' = x + 1) and 
   the accessor is the identity function, the returned relation is:
     ... (4, 3), (3, 2), (2, 1), (1, 0)
 *)
definition dec_variant :: "('c rel)\<Rightarrow>('b\<Rightarrow>'c)\<Rightarrow>('b rel)" ("dec _ _" 1000)
  where "dec_variant r variant  = inv_image (r\<inverse>) variant" 

lemma dec_variant_trans:
  assumes wfr_trans: "trans wfr"
  shows "trans (dec wfr v)"
proof 
  fix x y z
  have a1: "trans ((wfr)\<inverse>)" by (simp add: wfr_trans)
  assume a2: "(x, y) \<in> (dec wfr v)"
  assume a3: "(y, z) \<in> (dec wfr v)"
  show "(x, z) \<in> (dec wfr v)"
    using a1 a2 a3 unfolding dec_variant_def by (meson in_inv_image transE)
qed

lemma dec_variant_refl:
  assumes refl_wfr: "refl wfr"
  shows "refl (dec wfr v)"
proof -
  have "refl ((wfr)\<inverse>)" by (simp add: refl_wfr)
  then have "\<And>x. (x,x) \<in> (dec wfr v)"
    unfolding dec_variant_def in_inv_image  by (simp add: refl_onD)
  then show ?thesis unfolding refl_on_def by auto
qed

lemma dec_variant_eq_rtrancl:
  assumes wfr_trans: "trans wfr"
  shows "(dec wfr\<^sup>= v) = (dec wfr\<^sup>= v)\<^sup>*"
proof -
  have "trans (wfr\<^sup>=)" using wfr_trans by simp
  then have "trans (dec wfr\<^sup>= v)" using dec_variant_trans by metis
  then have a1: "(dec wfr\<^sup>= v) = (dec wfr\<^sup>= v)\<^sup>+" by simp
  have "refl (wfr\<^sup>=)" by simp
  then have "refl (dec wfr\<^sup>= v)"
    using dec_variant_refl by metis
  then have a2: "(dec wfr\<^sup>= v) = (dec wfr\<^sup>= v)\<^sup>="
    unfolding refl_on_def by auto
  show ?thesis using a1 a2 by (metis trancl_reflcl)
qed

definition while_statement :: "('b,'v::has_booleans) expr \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a"
 ( "(While_do_)" 41)
  where "while_statement b c \<equiv> gfp (\<lambda>x. If b then c;x else nil)"

lemma while_f_mono:
  shows "mono (\<lambda>x. If b then c;x else nil)"
  unfolding if_statement_def mono_def
    by (metis  nondet_mono_left seq_mono_right seq_mono_left seq_assoc) 

lemma while_unfold:
  shows "(While b do c) = (If b then c;(While b do c) else nil)"
proof -
  define f where "f \<equiv> (\<lambda>x. If b then c;x else nil)"
  have "(If b then c;(While b do c) else nil) = f(gfp f)"
    using while_statement_def f_def by metis
  also have "... = gfp f" using while_f_mono f_def gfp_unfold by metis
  finally show ?thesis using while_statement_def f_def by metis
qed

lemma while_mono:
  assumes refine: "c \<ge> d"
  shows "(While b do c) \<ge> (While b do d)"
proof -
  define f where "f \<equiv> (\<lambda>x. If b then c;x else nil)"
  define g where "g \<equiv> (\<lambda>x. If b then d;x else nil)"
  have "\<And>x. f x \<ge> g x"
    using refine if_mono_left seq_mono_left f_def g_def by metis
  then have "gfp f \<ge> gfp g"
    using gfp_mono by metis
  then show ?thesis
    unfolding while_statement_def f_def g_def by metis
qed

lemma initial_assert_rely_generic:
  shows "\<lbrace>p\<rbrace>;((rely r) \<iinter> d \<iinter> c) = ((rely r) \<iinter> d \<iinter> \<lbrace>p\<rbrace>;c) "
proof (rule antisym)
  have "d \<iinter> (rely r) \<iinter> c \<ge> (\<tau> p);(d \<iinter> (rely r) \<iinter> \<lbrace>p\<rbrace>;c)"
  proof -
    have "nil \<ge> (\<tau> p);\<lbrace>p\<rbrace>"
      by (simp add: test_seq_assert nil_ref_test)
    then show ?thesis using test_pre_rely 
      by (metis test_seq_assert seq_nil_right seq_assoc seq_mono_left test_seq_refine test_conj_distrib)
  qed
  then show "\<lbrace>p\<rbrace>;((rely r) \<iinter> d \<iinter> c) \<ge> (rely r) \<iinter> d \<iinter> \<lbrace>p\<rbrace>;c"
    using assert_galois_test conj_commute by metis
next
  show "(rely r) \<iinter> d \<iinter> \<lbrace>p\<rbrace>;c \<ge> \<lbrace>p\<rbrace>;((rely r) \<iinter> d \<iinter> c)"
    by (metis conj.nil_sync_assert seq_nil_left seq_conj_interchange)
qed

lemma rely_assert:
  shows "\<lbrace>p\<rbrace>;((rely r) \<iinter> c) = ((rely r) \<iinter> \<lbrace>p\<rbrace>;c)"
  using initial_assert_rely_generic conj_chaos by metis

lemma wellfounded_rel_stable:
  assumes wfr_trans: "trans wfr"
  (* i.e. v \<preceq> k is stable under dec\<^sub>\<preceq>(v) if \<prec> is transitively closed. *)
  shows "stable (fn_less v (wfr\<^sup>=) k) (dec (wfr\<^sup>=) (v))" unfolding stable_def
proof (rule subsetI)
  fix b
  (* i.e. the Image of (rel v (wfr\<^sup>=) k) in (Variant v ((wfr\<inverse>)\<^sup>=)) *)
  assume "b \<in> (dec (wfr\<^sup>=) v) `` (fn_less v (wfr\<^sup>=) k)"
  then obtain x where a1: "x \<in> (fn_less v (wfr\<^sup>=) k) \<and> (x, b) \<in> dec (wfr\<^sup>=) v" 
    using Image_iff by blast
  then have "((v x), k) \<in> (wfr\<^sup>=) \<and> (v b, (v x)) \<in> (wfr\<^sup>=)" 
    unfolding fn_less_def dec_variant_def by auto
  moreover have "trans (wfr\<^sup>=)" by (simp add: wfr_trans) 
  ultimately have "(v b, k) \<in> (wfr\<^sup>=)" using trans_def by metis
  then show "b \<in> fn_less v (wfr\<^sup>=) k" unfolding fn_less_def by blast
qed


lemma rely_loop_early_tolerates_interference:
  assumes wfr_trans: "trans wfr"
  assumes tolerate_interference: "tolerates_interference p (q\<^sup>* \<triangleright> p) r"
  assumes pr_maintains_b1: "stable b1 (p \<triangleleft> r)"
  assumes pr_variant: "p \<triangleleft> r \<subseteq> (dec wfr\<^sup>= v)"
  assumes p'_def: "p' \<equiv> (p \<inter> (fn_less v (wfr\<^sup>=) k))"
  assumes q'_def: "q' \<equiv> q\<^sup>* \<triangleright> (p \<inter> b1)"
  shows  "tolerates_interference p' q' r" 
proof -
  have "stable (p \<inter> b1) r"
    using pr_maintains_b1 tolerate_interference unfolding tolerates_interference_def stable_def restrict_domain_def by auto
  moreover have "q' = (q\<^sup>* \<triangleright> p) \<triangleright> (p \<inter> b1)" unfolding restrict_range_def q'_def by auto
  ultimately have a1: "tolerates_interference p q' r" 
    using tolerates_interference_restict_post tolerate_interference by metis
  have "stable (fn_less v (wfr\<^sup>=) k) (dec (wfr)\<^sup>= v)"
    using wellfounded_rel_stable wfr_trans by metis
  then have "stable p' r"
    using tolerate_interference pr_variant unfolding p'_def stable_def 
          restrict_domain_def tolerates_interference_def by auto
  then show "tolerates_interference p' q' r"
    using a1 tolerates_interference_restict_pre unfolding p'_def by metis
qed

lemma expr_eq_distinct_true_false:
  shows "(expr_eq b true \<inter> expr_eq b false) = {}"
  unfolding expr_eq_def using has_booleans_distinct 
  by (metis (mono_tags, lifting) CollectD disjoint_iff_not_equal)

lemma rely_loop_early_first_condition:
  assumes g_reflexive: "refl g" 
  assumes wellfounded: "wf (wfr::('c) rel) "
  assumes wfr_trans: "trans wfr"
  assumes single_reference_b: "single_reference b r"
  assumes tolerate_interference: "tolerates_interference p (q\<^sup>* \<triangleright> p) r"
  assumes b_boolean: "p \<subseteq> expr_type b boolean"
  assumes pb_establishes_b0: "p \<inter> (expr_eq b true) \<subseteq> b0"
  assumes pr_maintains_b0: "stable b0 (p \<triangleleft> r)" (*b0 is stable under interference satisfying p \<triangleleft> r*)
  assumes pnegb_establishes_b1: "p \<inter> (expr_eq b false) \<subseteq> b1"
  assumes pr_maintains_b1: "stable b1 (p \<triangleleft> r)" (*b1 is stable under interference satisfying p \<triangleleft> r*)
  assumes pb2_establishes_b: "p \<inter> b2 \<subseteq> (expr_eq b false)"
  assumes pr_maintains_b2: "stable b2 (p \<triangleleft> r)" (*b2 is stable under interference satisfying p \<triangleleft> r*)
  assumes pr_variant: "p \<triangleleft> r \<subseteq> (dec (wfr\<^sup>=) v)"
  assumes step: "\<forall>k::'c. (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> ((fn_less v wfr k) \<union> b2))\<rparr> \<ge> c"
  shows first_condition: "(guar g) \<iinter> (rely r) \<iinter> \<lbrace>b2 \<inter> p\<rbrace>;\<lparr>q\<^sup>* \<triangleright> (p \<inter> b1)\<rparr> \<ge> gfp (\<lambda>x. If b then c;x else nil)"
proof -
  define f where "f \<equiv> (\<lambda>x. If b then c;x else nil)"
  define p' where "p' \<equiv> b2 \<inter> p"
  define q' where "q' \<equiv> q\<^sup>* \<triangleright> (p \<inter> b1)"
  have "(guar g) \<iinter> (rely r) \<iinter> \<lbrace>p'\<rbrace>;\<lparr>q'\<rparr> \<ge> 
          (guar g) \<iinter> (If b then (rely r) \<iinter> \<lbrace>{} \<inter> p'\<rbrace>;\<lparr>q'\<rparr> else (rely r) \<iinter> \<lbrace>b2 \<inter> p'\<rbrace>;\<lparr>q'\<rparr>)" (is "_ \<ge> ?rhs")
  proof -
    have "tolerates_interference p' q' r"
    proof -
      have "stable (b2 \<inter> p) r"
        using pr_maintains_b2 tolerate_interference unfolding tolerates_interference_def stable_def restrict_domain_def by auto
      then have a1: "tolerates_interference (b2 \<inter> p) (q\<^sup>* \<triangleright> p) r"
        using tolerates_interference_restict_pre tolerate_interference inf_commute by metis
    
      have "(q\<^sup>* \<triangleright> (p \<inter> b1)) = (q\<^sup>* \<triangleright> p) \<triangleright> (p \<inter> b1)" unfolding restrict_range_def by auto
      moreover have "stable (p \<inter> b1) r"
        using pr_maintains_b1 tolerate_interference unfolding tolerates_interference_def stable_def restrict_domain_def by auto
      ultimately show "tolerates_interference p' q' r"
        using a1 tolerates_interference_restict_post p'_def q'_def by metis
    qed
    moreover have "p' \<subseteq> expr_type b boolean" using b_boolean p'_def by auto
    moreover have "single_reference b r" using single_reference_b by simp
    moreover have "p' \<inter> (expr_eq b true) \<subseteq> {}" (* letting  b0 = {} *)
      using p'_def pb2_establishes_b expr_eq_distinct_true_false unfolding expr_eq_def by auto
    moreover have "stable {} (p' \<triangleleft> r)"
      unfolding stable_def by auto
    moreover have "p' \<inter> (expr_eq b false) \<subseteq> b2" using p'_def by auto
    moreover have "stable b2 (p' \<triangleleft> r)"
      using pr_maintains_b2 unfolding p'_def stable_def restrict_domain_def by auto
    ultimately show ?thesis using rely_conditional single_reference_b conj.sync_mono_right conj_assoc by metis
  qed
  also have "?rhs \<ge> (If b then (guar g) \<iinter> (rely r) \<iinter> \<lbrace>{} \<inter> p'\<rbrace>;\<lparr>q'\<rparr> else (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b2 \<inter> p'\<rbrace>;\<lparr>q'\<rparr>)" (is "_ \<ge> ?rhs")
    using guar_conditional_distrib g_reflexive local.conj_assoc by auto
  also have "?rhs \<ge> (If b then (guar g) \<iinter> \<lbrace>{}\<rbrace>;\<lparr>q'\<rparr> else (guar g) \<iinter> \<lbrace>b2 \<inter> p'\<rbrace>;\<lparr>q'\<rparr>)" (is "_ \<ge> ?rhs")
  proof -
    have wp1: "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>b2 \<inter> p'\<rbrace>;\<lparr>q'\<rparr> \<ge> (guar g) \<iinter> \<lbrace>b2 \<inter> p'\<rbrace>;\<lparr>q'\<rparr>" using rely_remove
      by (simp add: conj.sync_mono_left)
    have wp2: "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>{} \<inter> p'\<rbrace>;\<lparr>q'\<rparr> \<ge> (guar g) \<iinter> \<lbrace>{} \<inter> p'\<rbrace>;\<lparr>q'\<rparr>" using rely_remove
      by (simp add: conj.sync_mono_left)
    have "(If b then (guar g) \<iinter> (rely r) \<iinter> \<lbrace>{} \<inter> p'\<rbrace>;\<lparr>q'\<rparr> else (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b2 \<inter> p'\<rbrace>;\<lparr>q'\<rparr>) \<ge> 
                (If b then (guar g) \<iinter> \<lbrace>{} \<inter> p'\<rbrace>;\<lparr>q'\<rparr> else (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b2 \<inter> p'\<rbrace>;\<lparr>q'\<rparr>)" (is "_ \<ge> ?rhs")
      using if_mono_left conj_commute wp2 by auto
    also have "?rhs \<ge> (If b then (guar g) \<iinter> \<lbrace>{} \<inter> p'\<rbrace>;\<lparr>q'\<rparr> else (guar g) \<iinter> \<lbrace>b2 \<inter> p'\<rbrace>;\<lparr>q'\<rparr>)"
      using if_mono_right conj_commute wp1 by auto
    finally show ?thesis by simp
  qed
  also have "?rhs \<ge> (If b then c;(gfp f) else nil)" (is "_ \<ge> ?rhs")
  proof -
    have a: "(guar g) \<iinter> \<lbrace>p'\<rbrace>;\<lparr>q'\<rparr> \<ge> nil"
    proof -
      have a: "Id \<subseteq> q\<^sup>*" by blast
      have b: "p \<inter> b2 \<subseteq> p \<inter> b1" 
        using pb2_establishes_b pnegb_establishes_b1 by auto
      have c: "(p \<inter> b2) \<triangleleft> Id \<subseteq> Id \<triangleright> (p \<inter> b1)" using id_maintains_pre b by blast
      then have "(guar g) \<iinter> \<lbrace>p'\<rbrace>;\<lparr>q'\<rparr> \<ge> (guar g) \<iinter> \<lbrace>p \<inter> b2\<rbrace>;\<lparr>Id \<triangleright> (p \<inter> b1)\<rparr>" (is "_ \<ge> ?rhs") using spec_strengthen q'_def p'_def a range_restrict_q_mono 
        by (metis conj.sync_mono_right conj.test_sync_to_inf local.conj_commute seq_mono_right test.hom_iso_eq)
      also have "?rhs \<ge> (guar g) \<iinter> \<lbrace>p \<inter> b2\<rbrace>;\<lparr>Id\<rparr>" (is "_ \<ge> ?rhs") using spec_strengthen_under_pre c
        by (simp add: conj.sync_mono_right)
      also have "?rhs \<ge> nil" using spec_to_test
        by (metis (no_types, lifting) assert_nil assert_seq_self assert_top conj.nil_sync_nil 
              conj.sync_mono guar_def iter0 seq_mono spec_id_nil)
      finally show ?thesis.
    qed
    have "(guar g) \<iinter> \<lbrace>{}\<rbrace>;\<lparr>q'\<rparr> \<ge> c;(gfp f)"
      using assert_bot by (metis conj.assert_distrib seq_abort sup.absorb_iff2 sup_top_right)
    then have "(If b then (guar g) \<iinter> \<lbrace>{}\<rbrace>;\<lparr>q'\<rparr> else (guar g) \<iinter> \<lbrace>b2 \<inter> p'\<rbrace>;\<lparr>q'\<rparr>) \<ge> (If b then c;(gfp f) else (guar g) \<iinter> \<lbrace>b2 \<inter> p'\<rbrace>;\<lparr>q'\<rparr>)" (is "_ \<ge> ?rhs")
      using if_mono_left by blast
    also have "?rhs \<ge> (If b then c;(gfp f) else nil)"
      using a spec_to_test by (simp add: if_mono_right p'_def)
    finally show ?thesis.
  qed    
  also have "?rhs = gfp f"
  proof -
    have mono_f: "mono f"
      by (metis f_def if_mono_left infiter_step_mono mono_def)
    have "(If b then c;(gfp f) else nil) = f (gfp f)"
      unfolding f_def by auto          
    also have "... = gfp f"
      using gfp_fixpoint mono_f by blast
    finally show ?thesis.
  qed
  finally show ?thesis using p'_def q'_def f_def by simp
qed

lemma rely_loop_early_second_condition:
  assumes g_reflexive: "refl g"
  assumes wfr_trans: "trans wfr"
  assumes single_reference_b: "single_reference b r"
  assumes tolerate_interference: "tolerates_interference p (q\<^sup>* \<triangleright> p) r"
  assumes b_boolean: "p \<subseteq> expr_type b boolean"
  assumes pb_establishes_b0: "p \<inter> (expr_eq b (true)) \<subseteq> b0"
  assumes pr_maintains_b0: "stable b0 (p \<triangleleft> r)" 
  assumes pnegb_establishes_b1: "p \<inter> (expr_eq b (false)) \<subseteq> b1"
  assumes pr_maintains_b1: "stable b1 (p \<triangleleft> r)"
  assumes pb2_establishes_b_false: "p \<inter> b2 \<subseteq> (expr_eq b (false))"
  assumes pr_maintains_b2: "stable b2 (p \<triangleleft> r)"
  assumes pr_variant: "p \<triangleleft> r \<subseteq> (dec wfr\<^sup>= v)"
  assumes step:  "(guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr> q\<^sup>* \<triangleright> (p \<inter> ((fn_less v wfr k) \<union> b2))\<rparr> \<ge> c" 
  assumes s_def: "s = ((guar g) \<iinter> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>(q\<^sup>*) \<triangleright> (p \<inter> b1)\<rparr>)"
  shows "\<lbrace>fn_eq v k\<rbrace>;s \<ge> (If b then c;\<lbrace>(fn_less v wfr k) \<union> b2\<rbrace>;s else nil)"
proof -
  define p' where "p' \<equiv> (p \<inter> (fn_less v (wfr\<^sup>=) k))"
  define q' where "q' \<equiv> q\<^sup>* \<triangleright> (p \<inter> b1)"
  have "\<lbrace>fn_eq v k\<rbrace>;((guar g) \<iinter> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>(q\<^sup>*) \<triangleright> (p \<inter> b1)\<rparr>) 
                = (guar g) \<iinter> (rely r) \<iinter> \<lbrace>p \<inter> (fn_eq v k)\<rbrace>; \<lparr>(q\<^sup>*) \<triangleright> (p \<inter> b1)\<rparr>"
  proof -
    have f1: "\<And>B a r aa. \<lbrace>B\<rbrace> ; (a \<iinter> rely r \<iinter> aa) = a \<iinter> rely r \<iinter> \<lbrace>B\<rbrace> ; aa"
      using initial_assert_rely_generic local.conj_commute by force
    have "\<And>B Ba a. \<lbrace>B\<rbrace> ; (\<lbrace>Ba\<rbrace> ; a) = \<lbrace>B \<inter> Ba\<rbrace> ; a"
      by (metis (full_types) assert_seq_assert seq_assoc)
    then show ?thesis
      using f1 by (simp add: inf_commute)
  qed
  also have "... \<ge> (guar g) \<iinter> (rely r) \<iinter> \<lbrace>p'\<rbrace>; \<lparr>q'\<rparr>" (is "_ \<ge> ?rhs")
  proof -
    have "p \<inter> (fn_eq v k) \<subseteq> p'" unfolding fn_less_def fn_eq_def p'_def by auto
    then show ?thesis using conj.sync_mono_right q'_def
      by (simp add: assert_iso seq_mono_left) 
  qed
  also have "?rhs \<ge> (guar g) \<iinter> (If b then ((rely r)\<iinter>\<lbrace>b0 \<inter> p'\<rbrace>;\<lparr> q'\<rparr>) else ((rely r)\<iinter>\<lbrace>b1 \<inter> p'\<rbrace>; \<lparr>q'\<rparr>))" (is "_ \<ge> ?rhs")
  proof -
    have "tolerates_interference p' q' r"
      using rely_loop_early_tolerates_interference wfr_trans tolerate_interference pr_maintains_b1 
            pr_variant p'_def q'_def by metis
    moreover have "single_reference b r" using single_reference_b by simp
    moreover have "p' \<subseteq> expr_type b boolean" using b_boolean p'_def by auto
    moreover have "p' \<inter> (expr_eq b (true)) \<subseteq> b0" using pb_establishes_b0 p'_def by auto
    moreover have "stable b0 (p' \<triangleleft> r)"
      using pr_maintains_b0 unfolding p'_def stable_def restrict_domain_def by auto
    moreover have "p' \<inter> (expr_eq b (false)) \<subseteq> b1" using pnegb_establishes_b1 p'_def by auto
    moreover have "stable b1 (p' \<triangleleft> r)"
      using pr_maintains_b1 unfolding p'_def stable_def restrict_domain_def by auto
    ultimately show ?thesis using rely_conditional single_reference_b conj.sync_mono_right conj_assoc by metis
  qed
  also have "?rhs \<ge> (If b then ((guar g)\<iinter>(rely r)\<iinter>\<lbrace>b0 \<inter> p'\<rbrace>; \<lparr>q'\<rparr>) else ((guar g)\<iinter>(rely r)\<iinter>\<lbrace>b1 \<inter> p'\<rbrace>;\<lparr>q'\<rparr>))" (is "_ \<ge> ?rhs")
    using guar_conditional_distrib g_reflexive conj_assoc by metis
  also have "?rhs \<ge> (If b then ((guar g)\<iinter>(rely r)\<iinter>\<lbrace>b0 \<inter> p'\<rbrace>; \<lparr>q'\<rparr>) else nil)" (is "_ \<ge> ?rhs")
  proof -
    have "(b1 \<inter> p') \<triangleleft> Id \<subseteq> q'" 
      unfolding p'_def q'_def restrict_domain_def restrict_range_def by auto    
    then have "((guar g)\<iinter>(rely r)\<iinter>\<lbrace>b1 \<inter> p'\<rbrace>; \<lparr>q'\<rparr>) \<ge> (guar g)\<iinter>(rely r) \<iinter> \<lbrace>b1 \<inter> p'\<rbrace>; \<lparr>Id\<rparr>" (is "_ \<ge> ?rhs")
      using conj.sync_mono_right
      by (metis seq_mono_right assert_restricts_spec spec_strengthen) 
    also have "?rhs \<ge> (guar g)\<iinter>(rely r) \<iinter> \<lparr>Id\<rparr>" (is "_ \<ge> ?rhs")
      using conj.sync_mono_right assert_redundant by blast 
    also have "?rhs \<ge> nil"
      using spec_id_nil by (simp add: conj_refine iter0) 
    finally show ?thesis using if_mono_right by simp
  qed
  also have "?rhs \<ge> (If b then c;\<lbrace>(fn_less v wfr k) \<union> b2\<rbrace>;s else nil)" (is "_ \<ge> ?rhs")
  proof -
    have "(guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p'\<rbrace>;\<lparr>q'\<rparr> =
              (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> fn_less v (wfr\<^sup>=) k\<rbrace>; \<lparr>q\<^sup>* O (q\<^sup>* \<triangleright> (p \<inter> b1))\<rparr>"
      using p'_def q'_def
      by (simp add: inf_assoc range_restrict_relcomp) 
    also have "... \<ge> (guar g)\<iinter>(((rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> fn_less v (wfr\<^sup>=) k\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> ((fn_less v wfr k) \<union> b2))\<rparr>);
                               ((rely r) \<iinter> \<lbrace>(p \<inter> ((fn_less v wfr k) \<union> b2))\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> b1)\<rparr>))" (is "_ \<ge> ?rhs")
      using spec_seq_introduce rely_seq_distrib
      by (metis conj.sync_assoc conj.sync_mono_right rely_assert rely_sequential_nopost seq_assoc seq_mono_right) 
    also have "?rhs \<ge> ((guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> fn_less v (wfr\<^sup>=) k\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> ((fn_less v wfr k) \<union> b2))\<rparr>);
                     ((guar g) \<iinter> (rely r) \<iinter> \<lbrace>(p \<inter> ((fn_less v wfr k) \<union> b2))\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> b1)\<rparr>)" (is "_ \<ge> ?rhs")
      using guar_distrib_seq conj_assoc by presburger
    also have "?rhs \<ge> c; ((guar g) \<iinter> (rely r) \<iinter> \<lbrace>(p \<inter> ((fn_less v wfr k) \<union> b2))\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> b1)\<rparr>)" (is "_ \<ge> ?rhs")
      using step seq_mono_left by metis
    also have "?rhs = c;\<lbrace>(fn_less v wfr k) \<union> b2\<rbrace>;((guar g) \<iinter> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> b1)\<rparr>)"
      using assert_restricts_spec initial_assert_rely_generic seq_assoc conj_commute inf_commute
    proof -
      have f1: "\<And>B Ba a. \<lbrace>B\<rbrace> ; (\<lbrace>Ba\<rbrace> ; a) = \<lbrace>B \<inter> Ba\<rbrace> ; a"
        by (metis (no_types) assert_seq_assert seq_assoc)
      have "\<And>B a r aa. \<lbrace>B\<rbrace> ; (a \<iinter> rely r \<iinter> aa) = a \<iinter> rely r \<iinter> \<lbrace>B\<rbrace> ; aa"
        using initial_assert_rely_generic local.conj_commute by force
      then show ?thesis
        using f1 by (simp add: inf_commute seq_assoc)
    qed
    also have "... = c;\<lbrace>(fn_less v wfr k) \<union> b2\<rbrace>;s"
      using s_def by simp
    finally show ?thesis using if_mono_left by simp
  qed
  finally show ?thesis using s_def by simp
qed
                    
lemma rely_loop_early:
  assumes g_reflexive: "refl g" 
  assumes wellfounded: "wf (wfr::('c) rel) "
  assumes wfr_trans: "trans wfr"
  assumes single_reference_b: "single_reference b r"
  assumes tolerate_interference: "tolerates_interference p (q\<^sup>* \<triangleright> p) r"
  assumes b_boolean: "p \<subseteq> expr_type b boolean"
  assumes pb_establishes_b0: "p \<inter> (expr_eq b true) \<subseteq> b0"
  assumes pr_maintains_b0: "stable b0 (p \<triangleleft> r)" (*b0 is stable under interference satisfying p \<triangleleft> r*)
  assumes pnegb_establishes_b1: "p \<inter> (expr_eq b false) \<subseteq> b1"
  assumes pr_maintains_b1: "stable b1 (p \<triangleleft> r)" (*b1 is stable under interference satisfying p \<triangleleft> r*)
  assumes pb2_establishes_b: "p \<inter> b2 \<subseteq> (expr_eq b false)"
  assumes pr_maintains_b2: "stable b2 (p \<triangleleft> r)" (*b2 is stable under interference satisfying p \<triangleleft> r*)
  assumes pr_variant: "p \<triangleleft> r \<subseteq> (dec (wfr\<^sup>=) v)"
  assumes step: "\<forall>k::'c. (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> ((fn_less v wfr k) \<union> b2))\<rparr> \<ge> c"
  shows "(guar g) \<iinter> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> b1)\<rparr> \<ge> (While b do c)"
proof -
  define f where "f \<equiv> (\<lambda>x. If b then c;x else nil)"
  define s where "s \<equiv> (guar g) \<iinter> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>(q\<^sup>*) \<triangleright> (p \<inter> b1)\<rparr>"
  have "\<forall>k::'c. \<lbrace>fn_eq v k\<rbrace>;s \<ge> f(\<lbrace>(fn_less v wfr k) \<union> b2\<rbrace>;s)"
    unfolding f_def s_def using assms rely_loop_early_second_condition seq_assoc by metis
  moreover have "\<lbrace>b2\<rbrace>;s \<ge> gfp f"
  proof -
    have "\<lbrace>b2\<rbrace>;s = \<lbrace>b2\<rbrace>;((guar g) \<iinter> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>(q\<^sup>*) \<triangleright> (p \<inter> b1)\<rparr>)" unfolding s_def by simp
    also have "... = (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b2 \<inter> p\<rbrace>;\<lparr>q\<^sup>* \<triangleright> (p \<inter> b1)\<rparr>" using rely_assert assert_seq_assert
    proof -
      have f1: "\<forall>a B Ba. \<lbrace>B \<inter> Ba\<rbrace> ; a = \<lbrace>B\<rbrace> ; (\<lbrace>Ba\<rbrace> ; a)"
        by (metis assert_seq_assert seq_assoc)
      have "\<forall>B Ba. (B::'b set) \<inter> Ba = Ba \<inter> B"
        by fastforce
      then have "guar g \<iinter> rely r \<iinter> \<lbrace>p \<inter> b2\<rbrace> ; \<lparr>q\<^sup>* \<triangleright> (p \<inter> b1)\<rparr> = \<lbrace>b2 \<inter> p\<rbrace> ; (guar g \<iinter> (rely r \<iinter> \<lparr>q\<^sup>* \<triangleright> (p \<inter> b1)\<rparr>))"
        using conj.assert_distrib local.conj_assoc rely_assert by presburger
      then show ?thesis    
        using f1 initial_assert_rely_generic local.conj_commute by auto
    qed                       
    also have "... \<ge> gfp (\<lambda>x. If b then c;x else nil)" using assms rely_loop_early_first_condition by simp
    finally show ?thesis unfolding f_def by simp
  qed
  moreover have "mono f" using while_f_mono f_def by simp
  ultimately have "s \<ge> gfp f"
    using well_founded_recursion_early wellfounded by metis
  then show "s \<ge> (While b do c)" using f_def while_statement_def by metis
qed

lemma rely_while_tolerates_interference:
  assumes wfr_trans: "trans wfr"
  assumes tolerate_interference: "tolerates_interference p (q\<^sup>* \<triangleright> p) r"
  assumes pr_variant: "p \<triangleleft> r \<subseteq> (dec wfr\<^sup>= v)"  "IntroPar2"
  assumes q'_def: "q' \<equiv> ((dec wfr\<^sup>= v) \<inter> q\<^sup>*)"
  shows "tolerates_interference p (q'\<^sup>* \<triangleright> p) r"
proof -
  have a1: "(dec wfr\<^sup>= v) = (dec wfr\<^sup>= v)\<^sup>*"
    using wfr_trans dec_variant_eq_rtrancl by metis
  then have a2: "q' = (q'\<^sup>*)"
    unfolding q'_def using rtrancl_inter_rtrancl by metis

  have "(p \<triangleleft> (relcomp r (q\<^sup>* \<triangleright> p)) \<subseteq> (q\<^sup>* \<triangleright> p))"
    using tolerate_interference unfolding tolerates_interference_def by auto
  moreover have "(p \<triangleleft> (relcomp r ((dec wfr\<^sup>= v)\<^sup>*)) \<subseteq> ((dec wfr\<^sup>= v)\<^sup>*))"
    using pr_variant unfolding restrict_domain_def by auto
  ultimately have a3: "(p \<triangleleft> (relcomp r (((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> p)) \<subseteq> (((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> p))"
    unfolding restrict_domain_def restrict_range_def using a1 by auto

  have "(p \<triangleleft> (relcomp (q\<^sup>* \<triangleright> p) r) \<subseteq> (q\<^sup>* \<triangleright> p))"
    using tolerate_interference unfolding tolerates_interference_def by auto
  moreover have "(p \<triangleleft> (relcomp ((dec wfr\<^sup>= v)\<^sup>* \<triangleright> p) r) \<subseteq> (dec wfr\<^sup>= v)\<^sup>*)"
    using pr_variant unfolding restrict_domain_def restrict_range_def by auto
  ultimately have a4:  "(p \<triangleleft> (relcomp (((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> p) r) \<subseteq> ((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> p)"
    unfolding restrict_domain_def restrict_range_def using a1 by auto
  show ?thesis using tolerate_interference a2 a3 a4 unfolding tolerates_interference_def q'_def
    by metis
qed

lemma rely_while_step_refine_helper:
  assumes wfr_trans: "trans wfr"
  assumes step: "\<And>k::'c. (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr> \<ge> c"
  shows "\<tau>(fn_eq v k');((guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr>) \<ge> \<tau>(fn_eq v k');c"
proof -
  (* Merge precondition into strong spec. *)
  have "\<lbrace>fn_eq v k'\<rbrace>;((guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr>) =
        ((guar g) \<iinter> (rely r) \<iinter> \<lbrace>(fn_eq v k') \<inter> (b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k))\<rbrace>; \<lparr>((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr>)"
    using initial_assert_rely_generic local.conj_commute spec_seq_introduce assert_seq_assert seq_assoc
    by (metis (no_types, lifting)) 
  also have "... \<ge> c"
  (* Consider the case where k' \<preceq> k. *)
  proof (cases "(k',k)\<in> (wfr\<^sup>=)")
    case a1: True    
    (* Strengthen postcondition to obtain v \<prec> k', thereby also removing (dec wfr\<^sup>= v). *)
    have "(guar g) \<iinter> (rely r) \<iinter> \<lbrace>(fn_eq v k') \<inter> (b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k))\<rbrace>; \<lparr>((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr> \<ge>
          (guar g) \<iinter> (rely r) \<iinter> \<lbrace> b0 \<inter> p \<inter> (fn_eq v k')\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> (fn_less v wfr k'))\<rparr>" (is "_ \<ge> ?rhs")
    proof -
      have a2: "(fn_less v wfr k') \<subseteq> (fn_less v wfr k)"
        unfolding fn_less_def using wfr_trans a1 unfolding trans_def by auto
      have a3 : "(fn_eq v k') \<subseteq> (fn_less v (wfr\<^sup>=) k)"
        unfolding fn_less_def fn_eq_def using wfr_trans a1 unfolding trans_def by auto
  
      have "(fn_eq v k') \<inter> (b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)) = b0 \<inter> p \<inter> (fn_eq v k')" 
        using a3 by auto
      moreover have "(b0 \<inter> p \<inter> (fn_eq v k')) \<triangleleft> (q\<^sup>* \<triangleright> (p \<inter> (fn_less v wfr k'))) \<subseteq> ((dec (wfr)\<^sup>= v) \<inter> q\<^sup>* ) \<triangleright> (p \<inter> (fn_less v wfr k))"
        using a2 unfolding dec_variant_def restrict_domain_def fn_less_def fn_eq_def restrict_range_def by auto
      ultimately show ?thesis using spec_strengthen spec_seq_introduce conj.sync_mono_right
        by (metis seq_mono_right assert_restricts_spec) 
    qed
    (* Weaken precondition so that it is stable under r. *)
    also have "?rhs \<ge> (guar g) \<iinter> (rely r) \<iinter>  \<lbrace> b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k')\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> (fn_less v wfr k'))\<rparr>" (is "_ \<ge> ?rhs")
    proof -
      have a3 : "b0 \<inter> p \<inter>(fn_eq v k') \<subseteq> b0 \<inter> p \<inter>(fn_less v (wfr\<^sup>=) k')"
        unfolding fn_less_def fn_eq_def by auto
      then show ?thesis using  conj.sync_mono_right
        by (simp add: assert_iso seq_mono_left) 
    qed
    also have "?rhs \<ge> c"
      using step by metis
    finally show ?thesis by simp
  next
    case False (*(k', k) \<notin> wfr\<^sup>=*)
    (* The precondition must be false. *)
    then have "fn_eq v k' \<inter> (b0 \<inter> p \<inter> fn_less v (wfr\<^sup>=) k) = {}"
      unfolding fn_eq_def fn_less_def by auto
    then have "(guar g) \<iinter> (rely r) \<iinter> \<lbrace>(fn_eq v k') \<inter> (b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k))\<rbrace>; \<lparr>((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr> = \<top>"
      using assert_bot conj_abort_right by simp
    also have "... \<ge> c"
      by simp
    finally show ?thesis .
  qed
  finally show ?thesis
    using assert_galois_test test_seq_refine by blast 
qed

lemma rely_while_step_refine:
  assumes wfr_trans: "trans wfr"
  assumes step: "\<And>k::'c. (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr> \<ge> c"
  shows "(guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr> \<ge> c"
proof -
  have a1: "\<And>k'.  \<tau>(fn_eq v k');((guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr>) \<ge>
        \<tau>(fn_eq v k');c"
    using rely_while_step_refine_helper wfr_trans step by metis

  have "(guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr> = 
      (\<Squnion>k'. \<tau>(fn_eq v k');((guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr>))"
    using fn_eq_all by (metis NONDET_seq_distrib seq_nil_left) 
  also have "... \<ge> (\<Squnion>k'. \<tau>(fn_eq v k');c)"  (is "_ \<ge> ?rhs")
    using a1 by (meson SUP_mono)
  also have "?rhs = c"
    using fn_eq_all by (metis NONDET_seq_distrib seq_nil_left) 
  finally show ?thesis .
qed

lemma rely_loop:
  assumes g_reflexive: "refl g"
  assumes wellfounded: "wf (wfr::('c) rel) "
  assumes wfr_trans: "trans wfr"  "IntroPar2"
  assumes single_reference_b: "single_reference b r"
  assumes tolerate_interference: "tolerates_interference p (q\<^sup>* \<triangleright> p) r"
  assumes b_boolean: "p \<subseteq> expr_type b boolean"
  assumes pb_establishes_b0: "p \<inter> (expr_eq b true) \<subseteq> b0"
  assumes pr_maintains_b0: "stable b0 (p \<triangleleft> r)" (*b0 is stable under interference satisfying p \<triangleleft> r*)
  assumes pnegb_establishes_b1: "p \<inter> (expr_eq b false) \<subseteq> b1"
  assumes pr_maintains_b1: "stable b1 (p \<triangleleft> r)" (*b1 is stable under interference satisfying p \<triangleleft> r*)
  assumes pr_variant: "p \<triangleleft> r \<subseteq> (dec wfr\<^sup>= v)"
  assumes step: "\<And>k::'c. (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr> \<ge> c"
  shows "(guar g) \<iinter> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>((dec wfr\<^sup>= v) \<inter> q\<^sup>*) \<triangleright> (p \<inter> b1)\<rparr>
            \<ge> (While b do c)"
proof -
  define q' where "q' \<equiv> ((dec wfr\<^sup>= v) \<inter> q\<^sup>*)"
  define b2 where "b2 \<equiv> {}::('b set)"
  have a1: "q' = (q'\<^sup>*)"
    unfolding q'_def using wfr_trans dec_variant_eq_rtrancl rtrancl_inter_rtrancl by metis

  have "tolerates_interference p (q'\<^sup>* \<triangleright> p) r"
    using rely_while_tolerates_interference wfr_trans tolerate_interference pr_variant q'_def by metis
  moreover have "p \<inter> b2 \<subseteq> (expr_eq b false)"
    unfolding b2_def by auto
  moreover have "stable b2 (p \<triangleleft> r)"
    unfolding b2_def stable_def by auto
  moreover have "\<forall>k::'c. (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>q'\<^sup>* \<triangleright> (p \<inter> ((fn_less v wfr k) \<union> b2))\<rparr> \<ge> c"
    using rely_while_step_refine wfr_trans step a1 unfolding b2_def q'_def by fastforce
  ultimately have "(guar g) \<iinter> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q'\<^sup>* \<triangleright> (p \<inter> b1)\<rparr> \<ge> (While b do c)"
    using rely_loop_early assms by metis
  then show ?thesis using a1 unfolding q'_def by auto 
qed

(* This lemma shows that unless (b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)) = empty 
   (i.e. (b0 \<inter> p) and (fn_less v (wfr\<^sup>=) k) are disjoint sets) for all values of k that are the 
   'base elements' of a well-foudned relation, the loop body is implementable, because it is
   required to end up infeasible under some non-empty precondition.
   This calls into question whether any loop predicate  *)

lemma body_unimplementable_refine:
  assumes k: "\<exists>k. (\<nexists>prev. (prev,k) \<in> wfr) \<and> (b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)) \<noteq> empty"
  assumes c: "\<And>k::'c. (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr> \<ge> c"
  shows "\<exists>pre. \<lbrace>{pre}\<rbrace>;((guar g) \<iinter> (rely r) \<iinter> term;\<bottom>) \<ge> c"
proof -
  obtain k where a1: "(\<nexists>prev. (prev,k) \<in> wfr) \<and> (b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)) \<noteq> empty"
    using k by auto
  then have "(b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)) \<noteq> empty" by auto
  then obtain pre where a2: "{pre} \<subseteq> (b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k))" by auto
  have "\<lbrace>{pre}\<rbrace>;((guar g) \<iinter> (rely r) \<iinter> term;\<bottom>) = ((guar g) \<iinter> (rely r) \<iinter> \<lbrace>{pre}\<rbrace>; \<lparr>UNIV\<rparr>;\<bottom>)"
    using initial_assert_rely_generic conj_commute seq_assoc spec_univ by simp
  also have "... = ((guar g) \<iinter> (rely r) \<iinter> \<lbrace>{pre}\<rbrace>; \<lparr>UNIV \<triangleright> empty\<rparr>)"
    by (simp add: seq_assoc spec_test_restricts)
  also have "... \<ge> ((guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>UNIV \<triangleright> empty\<rparr>)" (is "_ \<ge> ?rhs")
    using a2 conj.sync_mono_right
    by (simp add: assert_iso seq_mono_left) 
  also have "?rhs = ((guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr>)"
  proof -
    have " q\<^sup>* \<triangleright> (p \<inter> (fn_less v wfr k)) = UNIV \<triangleright> empty" unfolding restrict_range_def fn_less_def using a1 by auto
    then show ?thesis by simp
  qed
  also have "... \<ge> c"
    using c by simp
  finally show ?thesis using nil_iter by metis
qed

lemma body_unimplementable_conditions:
  assumes wf: "wf wfr"
  assumes pb0_nonempty: "(p \<inter> b0) \<noteq> empty"
  assumes r_decreases_to_base: "\<forall>s \<in> (p \<inter> b0). v s \<in> (Range wfr) \<longrightarrow> (\<exists>s'. (v s, v s') \<in> wfr\<inverse> \<and> (s, s') \<in> r)"
  assumes p_stable_under_r: "stable p r"
  assumes b0_tolerates_decv: "stable b0 (p \<triangleleft> r)"
  shows "\<exists>k. (\<nexists>prev. (prev,k) \<in> wfr) \<and> (b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)) \<noteq> empty"
proof -
  define P where "P \<equiv> (\<lambda>k. (\<exists>s. (v s = k) \<and> s \<in> (p \<inter> b0))
                  \<longrightarrow> (\<exists>k'. (k' \<notin> Range wfr) \<and> (b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k')) \<noteq> empty))"
  have "\<And>x. (\<forall>y. (y, x) \<in> wfr \<longrightarrow> P y) \<longrightarrow> P x"
  proof 
    fix x
    assume a1: "(\<forall>y. (y, x) \<in> wfr \<longrightarrow> P y)" 
    have "(\<exists>s. (v s = x) \<and> s \<in> (p \<inter> b0)) \<Longrightarrow> 
              (\<exists>k'. (k' \<notin> Range wfr) \<and> (b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k')) \<noteq> empty)"
    proof -
      assume a2: "\<exists>s.(v s = x) \<and> s \<in> (p \<inter> b0)"
      then obtain s where a3: "(v s = x) \<and> s \<in> (p \<inter> b0)" by auto
      then show "(\<exists>k'. (k' \<notin> Range wfr) \<and> (b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k')) \<noteq> empty)"
      proof (cases "x \<notin> Range wfr")
        case True (* No predecessor *)
        then show ?thesis using a3 unfolding fn_less_def fn_eq_def by auto
      next
        case False (* There is a predecessor in the relation *)
        then have "v s \<in> Range (wfr)"
          using a3 unfolding fn_eq_def by auto
        then obtain sdec where a4: "(v s, v sdec) \<in> wfr\<inverse> \<and> (s, sdec) \<in> r"
          using r_decreases_to_base a3 by auto
        then have "P (v sdec)" using a1 a3 by auto
        moreover have "sdec \<in> (p \<inter> b0)" using a3 a4 b0_tolerates_decv p_stable_under_r unfolding stable_def restrict_domain_def by auto
        ultimately show ?thesis unfolding P_def by auto
      qed
    qed
    then show "P x" unfolding P_def by auto
  qed
  then have "\<forall>x. P x"
    by (metis wf wf_induct_rule)
  then show ?thesis unfolding P_def using pb0_nonempty by auto
qed

lemma body_unimplementable:
  assumes pb0_nonempty: "(p \<inter> b0) \<noteq> empty" (* it is possible to establish b0 under p. *)
  (* and for all states where p and b0 hold, where there exists in 
     wfr a way to decrement v, there is a step (s,s') in r that decrements v. *)
  assumes r_decreases_to_base: "\<forall>s \<in> (p \<inter> b0). v s \<in> (Range wfr) \<longrightarrow>
                                   (\<exists>s'. (v s, v s') \<in> wfr\<inverse> \<and> (s, s') \<in> (r))"
  (* The following are standard conditions for while-loop introduction *)
  assumes wf: "wf wfr" 
  assumes p_stable_under_r: "stable p r"
  assumes b0_tolerates_decv: "stable b0 (p \<triangleleft> r)"
  assumes c: "\<And>k::'c. (guar g) \<iinter> (rely r) \<iinter> \<lbrace>b0 \<inter> p \<inter> (fn_less v (wfr\<^sup>=) k)\<rbrace>; \<lparr>q\<^sup>* \<triangleright> (p \<inter> (fn_less v wfr k))\<rparr> \<ge> c"
  (* There exists atleast one starting state in which the loop body must have ended up doing 'magic' *)
  shows "\<exists>pre. \<lbrace>{pre}\<rbrace>;((guar g) \<iinter> (rely r) \<iinter> term;\<bottom>) \<ge> c"
  using assms body_unimplementable_refine body_unimplementable_conditions by metis


end
  
end
