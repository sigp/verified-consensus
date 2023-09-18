section \<open>Assignments under interference\<close>
theory Assignments
imports
  State_Relations
  Expressions
begin

(*declare [[show_types]]*)
                                      
locale assignments = expressions + state_relations + 
  (* for lib_last :: "'k \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("L\<^sup>C\<^sub>_ _" [999, 999] 999) + *)
  constrains set_var :: "'k \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 'b"
  constrains get_var :: "'k \<Rightarrow> 'b \<Rightarrow> 'v"
begin

text \<open>An assignment command evaluates its expression $e$ to a value $k$ 
  (non-atomically) and then atomically updates $x$ to $k$.
  The final idle command and the use of an optional step ensure that
  the definition is closed under finite stuttering.\<close>
definition assign :: "'k \<Rightarrow> ('b, 'v) expr \<Rightarrow> 'a" (infix "::=" 93)
  where "x ::= e \<equiv> \<Squnion>k. \<lbrakk>e\<rbrakk>k;opt((id_bar {|x|}) \<triangleright> (var_eq x k));idle"

lemma id_bar_refl:
  shows "refl (id_bar vars)"
  unfolding id_bar_def refl_on_def by auto

lemma intro_idle: 
  "\<And>k::'v. (rely r) \<iinter> \<lbrace>p \<inter> expr_eq e k\<rbrace>; \<lparr>(r\<^sup>*) \<triangleright> ((r\<^sup>*)``(p \<inter> expr_eq e k))\<rparr> \<ge> idle"
proof -
  fix k
  have r_trans: "r``((r\<^sup>*)``(p \<inter> expr_eq e k)) \<subseteq> ((r\<^sup>*)``(p \<inter> expr_eq e k))"
    using rtrancl.rtrancl_into_rtrancl by fastforce
  have stable_r_trans: "stable ((r\<^sup>*)``(p \<inter> expr_eq e k)) r"
    using rtrancl_into_rtrancl stable_def r_trans by fastforce
  have trans_image: "p \<inter> expr_eq e k \<subseteq> (r\<^sup>*)``(p \<inter> expr_eq e k)" 
    by blast
  have "(rely r) \<iinter> \<lbrace>p \<inter> expr_eq e k\<rbrace>; \<lparr>(r\<^sup>*) \<triangleright> ((r\<^sup>*)``(p \<inter> expr_eq e k))\<rparr> \<ge>
        (rely r) \<iinter> \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>; \<lparr>(r\<^sup>*) \<triangleright> ((r\<^sup>*)``(p \<inter> expr_eq e k))\<rparr>" (is "_ \<ge> ?rhs")
    using  assert_iso trans_image
    by (simp add: conj.sync_mono_right seq_mono_left)
  also have "?rhs \<ge> (rely r) \<iinter> idle" (is "_ \<ge> ?rhs")
    using rely_idle stable_r_trans by blast 
  also have "?rhs \<ge> idle" using rely_remove.
  finally (xtrans) show "(rely r) \<iinter> \<lbrace>p \<inter> expr_eq e k\<rbrace>; \<lparr>(r\<^sup>*) \<triangleright> ((r\<^sup>*)``(p \<inter> expr_eq e k))\<rparr> \<ge>  idle"
    using order_trans rely_remove by blast
qed

text \<open>This is the primary law for introducing an assignment command 
from which all other assignment laws are proven. 
It requires that the expression $e$ is single reference.
The relation $g$ is required to be reflexive so that stuttering program
steps satisfy the guarantee.
As usual when refining a specification command, its relation is required
to tolerate interference satisfying the rely relation $r$ from initial
states satisfying the precondition $p$.

The evaluation of a single-reference expression corresponds to evaluating
it in the state in which the single-reference variable is accessed.
The steps before and after this are either environment steps satisfying $r$
or stuttering program steps; collectively they satisfy $r^{\star}$.
The single program step that updates the variable $x$ must satisfy the guarantee.
\<close>
lemma rely_guar_assign:
  assumes g_refl: "refl g"
  assumes single_ref: "single_reference e r"
  assumes q_tolerates: "tolerates_interference p q r"
  assumes req_q: "\<And>k::'v. (p \<inter> (expr_eq e k)) \<triangleleft> (r\<^sup>*) O (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> q"
  assumes req_g: "\<And>k::'v. ((r\<^sup>*)``(p \<inter> (expr_eq e k))) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> g"
  shows "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr> \<ge> x::= e"
proof - 
  have refl: "refl (g \<inter> (id_bar {|x|}))" using id_bar_refl g_refl refl_on_Int
    by fastforce 
  have "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>;(x:\<^sub>f\<lparr>q\<rparr>) = 
        (rely r) \<iinter> (guar (g \<inter> (id_bar {|x|}))) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q\<rparr>" 
    unfolding var_frame_expand using guar_merge conj.assert_distrib conj.sync_assoc
    by metis 
  also have "\<dots> \<ge> (\<Squnion>k::'v. (\<lbrakk>e\<rbrakk>k);opt((id_bar {|x|}) \<triangleright> (var_eq x k)); idle)" (is "_ \<ge> ?rhs")
  proof -
    have all_k: "\<And>k::'v. (rely r) \<iinter> (guar (g \<inter> id_bar {|x|})) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> \<ge>
               \<lbrakk>e\<rbrakk>k; opt(id_bar {|x|} \<triangleright> var_eq x k); idle"
    proof -
      fix k
      have req_q_k: "(p \<inter> (expr_eq e k)) \<triangleleft> ((r\<^sup>*) O (id_bar {|x|}) \<triangleright> (var_eq x k)) \<subseteq> q"
        using domain_restrict_relcomp req_q by force

      have inner: "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> \<ge> \<tau>(expr_eq e k); idle;
                       \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>;opt((id_bar {|x|}) \<triangleright> (var_eq x k))" (is "_ \<ge> ?rhs")
      proof -
        have "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> \<ge> (rely r) \<iinter> \<tau>(expr_eq e k); \<lbrace>p\<rbrace>; \<lparr>q\<rparr>" (is "_ \<ge> ?rhs")
          by (simp add: conj.sync_mono_right seq_assoc test_seq_refine)
        also have "?rhs \<ge> (rely r) \<iinter> \<tau>(expr_eq e k); \<lbrace>p \<inter> expr_eq e k\<rbrace>; \<lparr>q\<rparr>" (is "_ \<ge> ?rhs")
        proof -
          have "\<tau> (expr_eq e k) ; \<lbrace>p\<rbrace> = \<tau> (expr_eq e k) ; \<lbrace>p \<inter> expr_eq e k\<rbrace>"
            by (metis assert_seq_assert inf_sup_aci(1) seq_assoc test_seq_assert)
          then show ?thesis
            by simp
        qed
        also have "?rhs \<ge> (rely r) \<iinter> \<tau>(expr_eq e k);
                         \<lbrace>p \<inter> expr_eq e k\<rbrace>; \<lparr>(r\<^sup>*) O ((id_bar {|x|}) \<triangleright> (var_eq x k))\<rparr>" (is "_ \<ge> ?rhs")
          using conj.sync_mono_right range_restrict_relcomp req_q_k 
                        seq_assoc seq_mono_right spec_strengthen_under_pre by simp
        also have "?rhs \<ge> (rely r) \<iinter> \<tau>(expr_eq e k);
                         (\<lbrace>p \<inter> expr_eq e k\<rbrace>; \<lparr>(r\<^sup>*) \<triangleright> ((r\<^sup>*)``(p \<inter> expr_eq e k))\<rparr>);
                         (\<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>;\<lparr>(id_bar {|x|}) \<triangleright> (var_eq x k)\<rparr>)" (is "_ \<ge> ?rhs")
          using conj.sync_mono_right seq_assoc seq_mono_right spec_seq_introduce by auto 
        also have "?rhs \<ge> (rely r) \<iinter> \<tau>(expr_eq e k);
                         ((rely r) \<iinter> \<lbrace>p \<inter> expr_eq e k\<rbrace>; \<lparr>(r\<^sup>*) \<triangleright> ((r\<^sup>*)``(p \<inter> expr_eq e k))\<rparr>);
                         (\<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>;\<lparr>(id_bar {|x|}) \<triangleright> (var_eq x k)\<rparr>)" (is "_ \<ge> ?rhs")
          using rely_refine_within by simp 
        also have "?rhs \<ge> (rely r) \<iinter> \<tau>(expr_eq e k); idle;
                         \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>;\<lparr>(id_bar {|x|}) \<triangleright> (var_eq x k)\<rparr>" (is "_ \<ge> ?rhs")
          using intro_idle seq_assoc seq_mono_left seq_mono_right
          by (simp add: conj.sync_mono_right)
        also have w: "?rhs \<ge> (rely r) \<iinter> \<tau>(expr_eq e k); idle;
                          \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>; opt((id_bar {|x|}) \<triangleright> (var_eq x k))" (is "_ \<ge> ?rhs")
        using spec_ref_opt conj_mono seq_mono by (simp add: conj.sync_mono_right) 
      finally show ?thesis
        using order_trans rely_remove by blast 
      qed
      have opt_guar: "(guar (g \<inter> id_bar {|x|})) \<iinter>
                        \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>; opt((id_bar {|x|}) \<triangleright> (var_eq x k)) \<ge>
                     opt(id_bar {|x|} \<triangleright> var_eq x k)"
      proof -
        have "(guar (g \<inter> id_bar {|x|})) \<iinter> 
                        \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>; opt((id_bar {|x|}) \<triangleright> (var_eq x k)) \<ge> 
                  \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>; 
                            opt(g \<inter> id_bar {|x|} \<inter> ((id_bar {|x|}) \<triangleright> (var_eq x k)))" (is "_ \<ge> ?rhs")
          using conj.assert_distrib guar_opt
          by (metis refl order_refl)
        also have "?rhs \<ge> \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>; opt((id_bar {|x|}) \<triangleright> (var_eq x k))" (is "_ \<ge> ?rhs")
        proof -
          have req_g_k: "((r\<^sup>*)``(p \<inter> (expr_eq e k))) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> g"
            by (simp add: req_g)
          have subset: "((r\<^sup>*)``(p \<inter> expr_eq e k)) \<triangleleft> ((id_bar {|x|}) \<triangleright> (var_eq x k)) \<subseteq>
                      g \<inter> ((id_bar {|x|}) \<triangleright> (var_eq x k))"
          proof -
            have f1: "(r\<^sup>* `` (p \<inter> expr_eq e k)) \<triangleleft> id_bar {|x|} \<inter> {(ba, b). b \<in> var_eq x k} \<subseteq> g"
              by (metis restrict_range_def req_g_k)
            have "\<And>r ra rb. (r::('b \<times> 'b) set) \<inter> (ra \<inter> rb) \<subseteq> ra"
              by fastforce
            then show ?thesis
              using f1 by (simp add: restrict_domain_def restrict_range_def inf_commute 
                  inf_left_commute)
          qed 
          have f: "\<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>; opt(g \<inter> ((id_bar {|x|}) \<triangleright> (var_eq x k))) \<ge>
              \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>; opt((id_bar {|x|}) \<triangleright> (var_eq x k))" (is "_ \<ge> ?rhs")
            using opt_strengthen_under_pre subset by blast
          show ?thesis using f by (metis restrict_range_def le_inf_iff opt_strengthen_under_pre subset)
        qed
        also have x: "?rhs \<ge> opt((id_bar {|x|}) \<triangleright> (var_eq x k))"
          using assert_redundant by auto
        show ?thesis
          using calculation order_trans x by blast
      qed

      have intro_idles: "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> \<ge> idle;((rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>); idle" (is "_ \<ge> ?rhs")
      proof -
        have "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> \<ge> (rely r) \<iinter> (idle; \<lbrace>p\<rbrace>; \<lparr>q\<rparr>); idle" (is "_ \<ge> ?rhs")
          using q_tolerates tolerate_interference
          by (metis order_refl seq_assoc) 
        also have "?rhs \<ge> ((rely r) \<iinter> idle;\<lbrace>p\<rbrace>; \<lparr>q\<rparr>); ((rely r) \<iinter> idle)" (is "_ \<ge> ?rhs")
          using rely_seq_distrib by blast
        also have "?rhs \<ge> ((rely r) \<iinter> idle);((rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>); ((rely r) \<iinter> idle)" (is "_ \<ge> ?rhs")
          using refine_within_rely_left rely_seq_distrib seq_assoc
          by (metis seq_mono_left) 
        also have x: "?rhs \<ge> idle;((rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>); idle"
          using rely_remove by (simp add: seq_mono) 
        show ?thesis
          using calculation order_trans x by blast
      qed

      have almost: "(guar (g \<inter> id_bar {|x|})) \<iinter> ((rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>) \<ge>
            idle; \<tau>(expr_eq e k); idle; opt((id_bar {|x|}) \<triangleright> (var_eq x k)); idle"
      proof -
        have "(guar (g \<inter> id_bar {|x|})) \<iinter> ((rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>) \<ge>
              (guar (g \<inter> id_bar {|x|})) \<iinter> idle; ((rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>); idle" (is "_ \<ge> ?rhs")
          using conj.sync_mono_right intro_idles by blast
        also have "?rhs \<ge> (guar (g \<inter> id_bar {|x|})) \<iinter> idle; (\<tau>(expr_eq e k); idle;
                       \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>;opt((id_bar {|x|}) \<triangleright> (var_eq x k))); idle" (is "_ \<ge> ?rhs")
          using inner by (simp add: conj.sync_mono_right seq_mono_left seq_mono_right)
        also have "?rhs \<ge> idle; 
                        ((guar (g \<inter> id_bar {|x|})) \<iinter> \<tau>(expr_eq e k); idle;
                          \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>;opt((id_bar {|x|}) \<triangleright> (var_eq x k)); idle)" (is "_ \<ge> ?rhs")
          using guar_distrib_seq seq_mono guar_idle refl seq_assoc by metis
        also have "?rhs \<ge> idle; 
                        ((guar (g \<inter> id_bar {|x|})) \<iinter> \<tau>(expr_eq e k); idle;
                          \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>;opt((id_bar {|x|}) \<triangleright> (var_eq x k))); idle" (is "_ \<ge> ?rhs")
          using guar_distrib_seq seq_mono_right guar_idle refl seq_assoc by metis 
        also have "?rhs \<ge> idle; \<tau>(expr_eq e k);
                        ((guar (g \<inter> id_bar {|x|})) \<iinter> idle;
                          \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>;opt((id_bar {|x|}) \<triangleright> (var_eq x k))); idle" (is "_ \<ge> ?rhs")
          using guar_distrib_seq seq_mono_left seq_mono_right guar_conj_test
          by (metis seq_assoc)
        also have "?rhs \<ge> idle; \<tau>(expr_eq e k); idle;
                        ((guar (g \<inter> id_bar {|x|})) \<iinter> 
                          \<lbrace>(r\<^sup>*)``(p \<inter> expr_eq e k)\<rbrace>;opt((id_bar {|x|}) \<triangleright> (var_eq x k)));
                        idle" (is "_ \<ge> ?rhs")
          using guar_distrib_seq guar_idle refl seq_mono_left seq_mono_right
          by (metis seq_assoc) 
        also have y: "?rhs \<ge> idle; \<tau>(expr_eq e k); idle; opt((id_bar {|x|}) \<triangleright> (var_eq x k)); idle" (is "_ \<ge> ?rhs")
          using opt_guar seq_mono_left seq_mono_right by auto 
        show ?thesis using y
          using calculation order_trans by blast
      qed
      show "(rely r) \<iinter> (guar (g \<inter> id_bar {|x|})) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> \<ge>
               \<lbrakk>e\<rbrakk>k; opt(id_bar {|x|} \<triangleright> var_eq x k); idle" (is "_ \<ge> ?rhs")
      proof -
        have "(rely r) \<iinter> (guar (g \<inter> id_bar {|x|})) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> \<ge>
              (rely r) \<iinter> ((guar (g \<inter> id_bar {|x|})) \<iinter> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>)" (is "_ \<ge> ?rhs")
          by (simp add: conj.comm.left_commute conj.sync_commute) 
        also have "?rhs \<ge>
              (rely r) \<iinter> (idle; \<tau>(expr_eq e k); idle); opt((id_bar {|x|}) \<triangleright> (var_eq x k)); idle" (is "_ \<ge> ?rhs")
          using almost conj.sync_mono_right conj.sync_assoc by fastforce 
        also have "?rhs \<ge>
              ((rely r) \<iinter> idle; \<tau>(expr_eq e k); idle); opt((id_bar {|x|}) \<triangleright> (var_eq x k)); idle" (is "_ \<ge> ?rhs")
          using rely_seq_distrib rely_remove
          by (metis conj.left_idem equal_within_rely_left)
        also have at_last: "?rhs \<ge>
              \<lbrakk>e\<rbrakk>k; opt((id_bar {|x|}) \<triangleright> (var_eq x k)); idle" (is "_ \<ge> ?rhs")
          using seq_mono_left single_reference_eval single_ref
          by metis
        show ?thesis using at_last
          using calculation order_trans by blast 
      qed
    qed
    show ?thesis using all_k
      by (simp add: SUP_least) 
  qed
  also have "?rhs \<ge> x ::= e"
    by (simp add: assign_def)
  then show ?thesis
    using calculation order_trans by blast
qed


text \<open>Introduce an assignment command when the precondition establishes
a property $p1$ that is stable under the rely condition.
\<close>

lemma rely_guar_assign_stable_pre:
  fixes p1:: "'v \<Rightarrow> 'b set"
  assumes refl: "refl g"
  assumes single_ref: "single_reference e r"
  assumes tolerate: "tolerates_interference p q r"
  assumes stable_p1: "\<And>k::'v. stable (p1 k) r"
  assumes establish_p1: "\<And>k::'v. expr_eq e k \<subseteq> p1 k"
  assumes req_gq: "\<And>k::'v. (p \<inter> p1 k) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> g \<inter> q"
  shows "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr> \<ge> x ::= e"
proof - 
  have stable_p_p1: "\<And>k::'v. stable (p \<inter> p1 k) r"
    using stable_inter tolerate stable_p1
    by (simp add: stable_inter tolerates_interference_def) 

  have req_q: "\<And>k::'v. (p \<inter> expr_eq e k) \<triangleleft> (r\<^sup>*) O (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> q"
  proof -
    fix k
    have p1_restrict: "(p1 k \<inter> p) \<triangleleft> r\<^sup>* O q \<subseteq> q"
      using domain_restrict_p_mono q_tolerates_rtrancl_left tolerate
      by (metis dual_order.trans domain_restrict_relcomp inf.cobounded2)

    have redundant_p_p1: "(p \<inter> p1 k) \<triangleleft> r\<^sup>* \<triangleright> (p \<inter> p1 k) = (p \<inter> p1 k) \<triangleleft> r\<^sup>*"
      using stable_p_p1 stable_maintains_invariant 
            stable_rtrancl by blast 
    have p1_q: "(p \<inter> p1 k) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> q"
      using req_gq by blast
    also have subst_p1_q: "(p \<inter> p1 k) \<triangleleft> (r\<^sup>* O ((p \<inter> p1 k) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k))) \<subseteq> q"
      using p1_q p1_restrict domain_restrict_relcomp
    proof -
      have "(p \<inter> p1 k) \<triangleleft> r\<^sup>* O q \<inter> q = (p \<inter> p1 k) \<triangleleft> r\<^sup>* O q"
        by (metis inf.order_iff inf_commute p1_restrict)
      then show ?thesis
        by (metis equalityE domain_restrict_relcomp le_inf_iff p1_q relcomp_mono)
    qed 
    have after_mid_swap: "((p \<inter> p1 k) \<triangleleft> (r\<^sup>*) \<triangleright> (p \<inter> p1 k)) O (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> q"
      using mid_domain_to_range subst_p1_q
      by (simp add: mid_domain_to_range domain_restrict_relcomp 
          restrict_domain_range_assoc)
    have after_redundant: "((p \<inter> p1 k) \<triangleleft> (r\<^sup>*)) O (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> q"
      using redundant_p_p1 after_mid_swap by simp 
    have cond_p1: "((p \<inter> p1 k) \<triangleleft> (r\<^sup>*)) O (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> q"
      using after_redundant by blast 
    have subset: "p \<inter> expr_eq e k \<subseteq> p \<inter> p1 k"
      using establish_p1 by blast 
    have almost: "((p \<inter> expr_eq e k) \<triangleleft> (r\<^sup>*)) O (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> q"
      using subset cond_p1 domain_restrict_p_mono by blast 
    ultimately show "(p \<inter> expr_eq e k) \<triangleleft> (r\<^sup>*) O (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> q"
      using almost
      by (simp add:domain_restrict_relcomp 
          range_restrict_relcomp)
  qed

  have req_g: "\<And>k::'v. ((r\<^sup>*)``(p \<inter> expr_eq e k)) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> g"
  proof -
    fix k
    have assum_g: "(p \<inter> p1 k) \<triangleleft> ((id_bar {|x|}) \<triangleright> (var_eq x k)) \<subseteq> g"
      using req_gq
      by (simp add: restrict_domain_range_assoc) 

    have subset: "p \<inter> expr_eq e k \<subseteq> p \<inter> p1 k" 
      using establish_p1 by blast 

    have "((r\<^sup>*)``(p \<inter> expr_eq e k)) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq>
          ((r\<^sup>*)``(p \<inter> p1 k)) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k)"
      using subset
      by (simp add: Image_mono domain_restrict_p_mono restrict_domain_range_assoc) 
    also have x: "\<dots> \<subseteq> (p \<inter> p1 k) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k)"
      using stable_p_p1 by (simp add: Image_closed_trancl stable_def) 
    show "((r\<^sup>*)``(p \<inter> expr_eq e k)) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> g"
      using req_gq x calculation by blast 
  qed  
  show ?thesis
    using rely_guar_assign refl single_ref tolerate req_q req_g by blast  
qed

text \<open>Introduce an assignment command when the expression is both 
single-reference and constant under the rely condition.
Note that it does not explicitly constrain $x$ to be constant.
\<close>
lemma local_expr_assign:
  assumes refl: "refl g"
  assumes single_ref: "single_reference e r"
  assumes estable: "estable e r"
  assumes tolerate: "tolerates_interference p q r"
  assumes req_gq: "\<And>k::'v. (p \<inter> expr_eq e k) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> g \<inter> q"
  shows "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>; x:\<^sub>f\<lparr>q\<rparr> \<ge> x ::= e"
proof -
  define p1 where "p1 \<equiv> expr_eq e"
  have stable_p1: "\<And>k::'v. stable (p1 k) r"
    using estable p1_def 
    by (simp add: estable_stable_eq) 
  have establish_p1: "\<And>k::'v. expr_eq e k \<subseteq> p1 k"
    using p1_def by blast
  have req_gq_p1: "\<And>k::'v. (p \<inter> p1 k) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> g \<inter> q"
    using req_gq p1_def by simp 
 show ?thesis
   using rely_guar_assign_stable_pre refl single_ref tolerate stable_p1
     establish_p1 req_gq_p1 by blast
qed

lemma trans_eval:
  fixes gte :: "'v \<Rightarrow> 'v \<Rightarrow> bool" (infix "\<succeq>" 50)
  assumes trans_gte: "transp gte"
  assumes first: "a \<succeq> b"
  assumes second: "b \<succeq> c"
  shows "a \<succeq> c"
  by (meson first second trans_gte transpD)

lemma stable_under_r:
  assumes stable_p: "stable p r"
  assumes in_r: "(\<sigma>,\<sigma>') \<in> r"
  assumes in_p: "\<sigma> \<in> p"
  shows "\<sigma>' \<in> p"
  by (meson in_p in_r r_into_rtrancl stable_p stable_rtrancl_helper)

lemma promote_x_stable:
  assumes x_stable: "\<And>k::'v. stable (var_eq x k) r"
  assumes in_r: "(\<sigma>,\<sigma>') \<in> r"
  shows "get_var x \<sigma> = get_var x \<sigma>'"
  using stable_under_r x_stable in_r var_eq_def by fastforce

lemma transfer:
  assumes subset: "p \<subseteq> p1"  "IntroPar2"
  assumes stable_p1: "stable p1 r"
  shows "p \<triangleleft> r = p \<triangleleft> r \<triangleright> p1"
proof -
  have p_p1: "p \<inter> p1 = p"
    using subset by (simp add: inf.order_iff) 
  have add_p1: "p \<triangleleft> r = p \<triangleleft> (p1 \<triangleleft> r)"
    by (simp add: domain_restrict_twice p_p1)
  also have "\<dots> = p \<triangleleft> (p1 \<triangleleft> r) \<triangleright> p1"
    using stable_maintains_invariant restrict_domain_range_assoc
    by (metis stable_p1)  
  also have f: "\<dots> = p \<triangleleft> r \<triangleright> p1"
    using add_p1 domain_restrict_twice by simp 
  show ?thesis using f
    using calculation by blast
qed

text \<open>Introduce an assignment when the variable $x$ is constant under $r$
but the expression $e$ may be changing monotonically under $r$.
\<close>
lemma rely_guar_assignment_monotonic:
  fixes gte :: "'v \<Rightarrow> 'v \<Rightarrow> bool" (infix "\<succeq>" 50)
  assumes refl_g: "refl g"
  assumes stable_p: "stable p r"
  assumes x_stable: "\<And>k::'v. stable (var_eq x k) r"
  assumes single_ref: "single_reference e r"
  assumes refl_gte: "reflp gte"
  assumes trans_gte: "transp gte"
  assumes id_or_r_dec: "(p \<triangleleft> (id_bar {|x|})) \<union> r \<subseteq> {(\<sigma>,\<sigma>'). (eval e \<sigma>) \<succeq> (eval e \<sigma>')}"
  assumes assm_g: "\<And>k::'v. (p \<inter> {\<sigma>. k \<succeq> (eval e \<sigma>)}) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> g"
  shows "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>;
          x:\<^sub>f\<lparr>{(\<sigma>,\<sigma>'). (eval e \<sigma>) \<succeq> (get_var x \<sigma>') \<and> (get_var x \<sigma>') \<succeq> (eval e \<sigma>')}\<rparr> \<ge>
            x ::= e"
proof -
  define q where "q \<equiv> {(\<sigma>,\<sigma>'). (eval e \<sigma>) \<succeq> (get_var x \<sigma>') \<and> (get_var x \<sigma>') \<succeq> (eval e \<sigma>')}"
  
  have constant_x_r: "r \<subseteq> {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'}"
    using promote_x_stable x_stable by fastforce

  have q_tolerates: "tolerates_interference p q r"
  proof -
    have tol_r_q: "p \<triangleleft> (r O q) \<subseteq> q"
    proof -
      have a1: "r O q  \<subseteq> {(\<sigma>,\<sigma>'). (eval e \<sigma>) \<succeq> (eval e \<sigma>')} O 
                       {(\<sigma>,\<sigma>'). (eval e \<sigma>) \<succeq> (get_var x \<sigma>') \<and> (get_var x \<sigma>') \<succeq> (eval e \<sigma>')}"
        using id_or_r_dec q_def by auto
      have a2: "\<dots> \<subseteq> {(\<sigma>,\<sigma>'). (\<exists>\<sigma>''. (eval e \<sigma>) \<succeq> (eval e \<sigma>'') \<and>
                           (eval e \<sigma>'') \<succeq> (get_var x \<sigma>') \<and> (get_var x \<sigma>') \<succeq> (eval e \<sigma>'))}"
        by blast
      have a3: "\<dots> \<subseteq> q"
        using trans_eval trans_gte q_def by blast
      have a4: "r O q \<subseteq> q"
        using a1 a2 a3 by auto 
      show ?thesis using a4
        by (metis dual_order.trans restrict_domain_def inf.cobounded2) 
    qed
    have tol_q_r: "p \<triangleleft> (q O r) \<subseteq> q"
    proof -
      have r_subset: "r \<subseteq> {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>' \<and> (eval e \<sigma>) \<succeq> (eval e \<sigma>')}"
        using constant_x_r id_or_r_dec by blast
      have "q O r \<subseteq> {(\<sigma>,\<sigma>'). (\<exists>\<sigma>''. (eval e \<sigma>) \<succeq> (get_var x \<sigma>'') \<and> (get_var x \<sigma>'') \<succeq> (eval e \<sigma>'') \<and>
                                 get_var x \<sigma>'' = get_var x \<sigma>' \<and> (eval e \<sigma>'') \<succeq> (eval e \<sigma>'))}"
        using q_def r_subset by blast
      also have b: "\<dots> \<subseteq> q"
        using q_def trans_eval trans_gte by auto
      show ?thesis
        by (meson b calculation dual_order.trans domain_restrict_remove)
    qed 
    show ?thesis using tolerates_interference_def stable_p tol_r_q tol_q_r by blast 
  qed
  
  have stable_ge_k_e_r: "\<And>k::'v. stable {\<sigma>. k \<succeq> (eval e \<sigma>)} r"
  proof -
    fix k
    have stable_geke: "stable {\<sigma>. k \<succeq> (eval e \<sigma>)} {(\<sigma>,\<sigma>'). eval e \<sigma>  \<succeq> eval e \<sigma>'}"
    proof -
      have "{(\<sigma>,\<sigma>'). eval e \<sigma>  \<succeq> eval e \<sigma>'}``{\<sigma>. k \<succeq> (eval e \<sigma>)} =
            {\<sigma>'. \<exists>\<sigma>. \<sigma> \<in> {\<sigma>. k \<succeq> eval e \<sigma>} \<and> (\<sigma>,\<sigma>') \<in> {(\<sigma>,\<sigma>'). eval e \<sigma>  \<succeq> eval e \<sigma>'}}"
        by auto
      have "\<dots> = {\<sigma>'. \<exists>\<sigma>. k \<succeq> eval e \<sigma> \<and> eval e \<sigma>  \<succeq> eval e \<sigma>'}"
        by simp
      have x: "\<dots> \<subseteq> {\<sigma>. k \<succeq> (eval e \<sigma>)}"
        using trans_eval trans_gte by blast
      show ?thesis using x by (simp add: stable_def)
    qed

    show stable_ge_k_e_r: "stable {\<sigma>. k \<succeq> (eval e \<sigma>)} r"
      using stable_geke id_or_r_dec stable_def 
      by (metis (no_types, lifting) Un_Image le_sup_iff subset_Un_eq)
  qed

  have stable_ge_k_e_r_starxxx: "\<And>k::'v. stable {\<sigma>. k \<succeq> (eval e \<sigma>)} (r\<^sup>*)"
    using stable_ge_k_e_r
    by (simp add: stable_rtrancl) 

  have stable_p_ge: "\<And>k. stable (p \<inter> {\<sigma>. k \<succeq> (eval e \<sigma>)}) r"
      using stable_inter stable_ge_k_e_r stable_p
      by blast 

  have rtran_stable: "\<And>k. (r\<^sup>*)``(p \<inter> expr_eq e k) \<subseteq> p \<inter> {\<sigma>. k \<succeq> (eval e \<sigma>)}"
  proof -
    fix k
    have stable_star: "stable {\<sigma>. k \<succeq> (eval e \<sigma>)} (r\<^sup>*)"
      using stable_ge_k_e_r by (simp add: stable_rtrancl) 
    have "(r\<^sup>*)``(p \<inter> expr_eq e k) \<subseteq> (r\<^sup>*)``(p \<inter> {\<sigma>. k \<succeq> (eval e \<sigma>)})"
      by (metis (mono_tags, lifting) Image_mono Int_Collect_mono expr_eq_def order_refl refl_gte reflpE)
    also have z: "\<dots> \<subseteq> (p \<inter> {\<sigma>. k \<succeq> (eval e \<sigma>)})"
      using stable_def
      by (metis Image_Int_subset Image_closed_trancl stable_ge_k_e_r stable_p)
    show "(r\<^sup>*)``(p \<inter> expr_eq e k) \<subseteq> p \<inter> {\<sigma>. k \<succeq> (eval e \<sigma>)}" using z
      using calculation by blast
  qed

  have req_q: "\<And>k::'v. (p \<inter> (expr_eq e k)) \<triangleleft> (r\<^sup>*) O (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> q"
  proof -
    fix k
    have subset_ge: "p \<inter> expr_eq e k \<subseteq> p \<inter> {\<sigma>. k \<succeq> (eval e \<sigma>)}"
      using rtran_stable by fastforce

    have stable_ge_id: "stable {\<sigma>. k \<succeq> (eval e \<sigma>)} (p \<triangleleft> (id_bar {|x|}))"
    proof -
      have a: "(p \<triangleleft> (id_bar {|x|}))``{\<sigma>. k \<succeq> (eval e \<sigma>)} =
            {\<sigma>'. \<exists>\<sigma>. \<sigma> \<in> {\<sigma>. k \<succeq> eval e \<sigma>} \<and> (\<sigma>,\<sigma>') \<in> (p \<triangleleft> (id_bar {|x|}))}"
        by blast
      also have b: "\<dots> \<subseteq> {\<sigma>'. \<exists>\<sigma>. k \<succeq> eval e \<sigma> \<and> eval e \<sigma> \<succeq> eval e \<sigma>'}"
        using id_or_r_dec by blast 
      also have c: "\<dots> \<subseteq> {\<sigma>'. k \<succeq> (eval e \<sigma>')}"
        using trans_eval trans_gte by blast
      also have d: "\<dots> \<subseteq> {\<sigma>. k \<succeq> (eval e \<sigma>)}"
        by simp
      show ?thesis using stable_def a b c d
        by (simp add: c stable_def order_trans)
    qed

    have transfer_id: "(p \<inter> {\<sigma>. k \<succeq> eval e \<sigma>}) \<triangleleft> (id_bar {|x|}) = 
          (p \<inter> {\<sigma>. k \<succeq> eval e \<sigma>}) \<triangleleft> (id_bar {|x|}) \<triangleright> {\<sigma>. k \<succeq> eval e \<sigma>}"
    proof -
      have x1: "(p \<inter> {\<sigma>. k \<succeq> eval e \<sigma>}) \<triangleleft> (id_bar {|x|}) = {\<sigma>. k \<succeq> eval e \<sigma>} \<triangleleft> p \<triangleleft> (id_bar {|x|})"
        by (simp add: domain_restrict_twice inf_commute)
      also have x2: "\<dots> = (p \<inter> {\<sigma>. k \<succeq> eval e \<sigma>}) \<triangleleft> (id_bar {|x|}) \<triangleright> {\<sigma>. k \<succeq> eval e \<sigma>}"
        using domain_restrict_twice stable_maintains_invariant stable_ge_id x1 by fastforce  
      show ?thesis
        using x1 x2 by blast
    qed

    have "(p \<inter> expr_eq e k) \<triangleleft> (r\<^sup>*) O (id_bar {|x|}) \<triangleright> var_eq x k =
          (p \<inter> expr_eq e k) \<triangleleft> (r\<^sup>*) O (p \<inter> {\<sigma>. k \<succeq> eval e \<sigma>}) \<triangleleft> (id_bar {|x|}) \<triangleright> var_eq x k" 
      using  subset_ge stable_p_ge
      by (simp add: stable_rtrancl_relcomp_subset domain_restrict_relcomp restrict_domain_range_assoc)
    also have "\<dots> \<subseteq> (p \<inter> expr_eq e k) \<triangleleft> (r\<^sup>*) O 
                    (p \<inter> {\<sigma>. k \<succeq> eval e \<sigma>}) \<triangleleft> (id_bar {|x|}) \<triangleright> {\<sigma>. k \<succeq> eval e \<sigma>} \<triangleright> var_eq x k"
      using transfer_id by auto 
    also have "\<dots> \<subseteq> (p \<inter> expr_eq e k) \<triangleleft> (r\<^sup>*) O (id_bar {|x|}) \<triangleright> ({\<sigma>. k \<succeq> eval e \<sigma>} \<inter> var_eq x k)"
      by (simp add: domain_restrict_remove range_restrict_twice restrict_domain_range_assoc relcomp_mono)
    also have "\<dots> \<subseteq> (p \<inter> expr_eq e k) \<triangleleft> {(\<sigma>,\<sigma>').\<top>} \<triangleright> ({\<sigma>. k \<succeq> eval e \<sigma>} \<inter> var_eq x k)"
      by (simp add: domain_restrict_q_mono range_restrict_q_mono domain_restrict_relcomp 
          range_restrict_relcomp)
    also have "\<dots> \<subseteq> (expr_eq e k) \<triangleleft> {(\<sigma>,\<sigma>').\<top>} \<triangleright> ((var_eq x k) \<inter> {\<sigma>. k \<succeq> eval e \<sigma>})"
      by (simp add: Int_commute domain_restrict_p_mono restrict_domain_range_assoc)
    also have "\<dots> \<subseteq> {(\<sigma>,\<sigma>') . eval e \<sigma> = k \<and> get_var x \<sigma>' = k \<and> k \<succeq> eval e \<sigma>'}"
    proof -
      have "expr_eq e k \<triangleleft> {(\<sigma>,\<sigma>').\<top>} \<triangleright> (var_eq x k \<inter> {\<sigma>. k \<succeq> eval e \<sigma>}) = 
            {(\<sigma>,\<sigma>'). \<sigma> \<in> expr_eq e k} \<inter> {(\<sigma>,\<sigma>'). \<sigma>' \<in> (var_eq x k \<inter> {\<sigma>. k \<succeq> eval e \<sigma>})}"
        by (simp add: restrict_domain_def restrict_range_def) 
      also have "\<dots> \<subseteq> {(\<sigma>,\<sigma>') . \<sigma> \<in> expr_eq e k \<and> \<sigma>' \<in> (var_eq x k \<inter> {\<sigma>. k \<succeq> eval e \<sigma>})}"
        by auto
      also have z: "\<dots> \<subseteq> {(\<sigma>,\<sigma>') . eval e \<sigma> = k \<and> get_var x \<sigma>' = k \<and> k \<succeq> eval e \<sigma>'}"
        by (simp add: expr_eq_def var_eq_def)
      show ?thesis using z
        using calculation by auto 
    qed
    also have e: "\<dots> \<subseteq> {(\<sigma>,\<sigma>'). eval e \<sigma> \<succeq> get_var x \<sigma>' \<and> get_var x \<sigma>' \<succeq> eval e \<sigma>'}"
    proof -
      have imp: "\<And>\<sigma>.\<And>\<sigma>'. eval e \<sigma> = k \<and> get_var x \<sigma>' = k \<and> k \<succeq> eval e \<sigma>' \<longrightarrow> 
                     eval e \<sigma> \<succeq> get_var x \<sigma>' \<and> get_var x \<sigma>' \<succeq> eval e \<sigma>'"
        using refl_gte reflpE by force
      show ?thesis
        using imp by blast 
    qed
    show "(p \<inter> (expr_eq e k)) \<triangleleft> (r\<^sup>*) O (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> q"
      using q_def e calculation by auto 
  qed
  have req_g: "\<And>k::'v. ((r\<^sup>*)``(p \<inter> (expr_eq e k))) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> g"
  proof -
    fix k
    have assm_g_x: "(p \<inter> {\<sigma>. k \<succeq> eval e \<sigma>}) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> g"
      using assm_g by blast
    show "((r\<^sup>*)``(p \<inter> (expr_eq e k))) \<triangleleft> (id_bar {|x|}) \<triangleright> (var_eq x k) \<subseteq> g"
      using assm_g_x rtran_stable
      by (metis (no_types, lifting) dual_order.trans domain_restrict_p_mono
        restrict_domain_range_assoc)
  qed
  show ?thesis
    using rely_guar_assign refl_g single_ref q_tolerates req_q req_g q_def by blast  
qed

end

end
