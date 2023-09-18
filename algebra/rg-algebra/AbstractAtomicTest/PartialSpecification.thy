section \<open>Partial specification command.\<close>

theory PartialSpecification
imports
  "Constrained_Atomic_Commands"
  "Termination"
begin

locale partial_spec = constrained_atomic + 
  constrains test :: "'state :: type set \<Rightarrow> 'a"
  constrains pgm:: "'state rel \<Rightarrow> 'a" 
  constrains env:: "'state rel \<Rightarrow> 'a"

begin

text \<open>Given a binary relation on states q, a partial specification command
  started in a state $\sigma$ either terminates in a state $\sigma'$, 
  such that $(\sigma,\sigma') \in q$ or does not terminate.
\<close> 
definition pspec :: "'state rel \<Rightarrow> 'a::refinement_lattice"   ( "\<lceil>_\<rceil>" 100)
  where "pspec q = (\<Squnion>s. \<tau>({s});chaos;\<tau>(q``{s}))"

lemma pspec_strengthen:
  assumes strengthen: "q2 \<subseteq> q1"
  shows "\<lceil>q1\<rceil> \<ge> \<lceil>q2\<rceil>"
proof -
  have "\<forall>s. q2``{s} \<subseteq> q1``{s}"
    using strengthen by blast
  then have a1: "\<forall>s. (\<tau>(q1``{s}) \<ge> \<tau>(q2``{s}))"
    using test.hom_mono by auto
  have "\<lceil>q1\<rceil> = (\<Squnion>s. (\<tau>({s}); chaos); \<tau>(q1``{s}))"
    using pspec_def by simp
  also have "... \<ge> (\<Squnion>s. \<tau>({s}); chaos; \<tau>(q2``{s}))" (is "_ \<ge> ?rhs")
    using seq_mono_right a1 by (meson SUP_mono)
  also have "?rhs = \<lceil>q2\<rceil>" 
    using pspec_def by simp
  finally show ?thesis .
qed

lemma pspec_univ: "\<lceil>UNIV\<rceil> = chaos"
proof -
  have a1: "\<forall>s. (UNIV = UNIV``{s})"
    by blast 
  have "\<lceil>\<top>\<rceil> = (\<Squnion>s. \<tau>({s});chaos;\<tau>(UNIV``{s}))"
    using pspec_def by simp      
  also have "... = (\<Squnion>s. \<tau>({s});chaos)"
    by (metis a1 seq_nil_right test_top)
  also have "... =  (\<Squnion>s. \<tau>({s}));chaos"
    by (simp add: NONDET_seq_distrib)
  also have "... = chaos"
    using Nondet_test_nil by simp
  finally show ?thesis .
qed

lemma pspec_chaos: "chaos \<ge> \<lceil>q\<rceil>"
proof -
  have "chaos = \<lceil>\<top>\<rceil>" using pspec_univ by simp
  also have "... \<ge> \<lceil>q\<rceil>" using pspec_strengthen by simp
  finally show ?thesis .
qed   

lemma test_restricts_pspec: "\<tau>(p);\<lceil>q\<rceil> = \<tau>(p);\<lceil>p \<triangleleft> q\<rceil>"
proof -
  have a1: "\<forall>s\<in>p.(q``{s} = ((p \<triangleleft> q)``{s}))"
    using restrict_domain_def by blast
      
  have "\<tau>(p);\<lceil>q\<rceil> = \<tau>(p);(\<Squnion>s. (\<tau>({s}); (chaos; \<tau>(q``{s}))))"
    using pspec_def seq_assoc by simp
  also have "... = (\<Squnion>s\<in>p. (\<tau>({s}); (chaos; \<tau>(q``{s}))))"
    using test_restricts_Nondet by simp
  also have "... = (\<Squnion>s\<in>p. (\<tau>({s}); (chaos; \<tau>((p \<triangleleft> q)``{s}))))"
    using a1 by simp
  also have "... = \<tau>(p);(\<Squnion>s. (\<tau>({s}); (chaos; \<tau>((p \<triangleleft> q)``{s}))))"
    using test_restricts_Nondet seq_assoc by simp
  also have "... = \<tau>(p);\<lceil>p \<triangleleft> q\<rceil>"
    using pspec_def seq_assoc by simp
  finally show ?thesis .  
qed

lemma assert_restricts_pspec: "\<lbrace>p\<rbrace>;\<lceil>q\<rceil> = \<lbrace>p\<rbrace>;\<lceil>p \<triangleleft> q\<rceil>"
  by (metis assert_seq_test seq_assoc test_restricts_pspec)

lemma pspec_strengthen_under_pre:
  assumes s: "p \<triangleleft> q2 \<subseteq> q1"
  shows  "\<lbrace>p\<rbrace>;\<lceil>q1\<rceil> \<ge> \<lbrace>p\<rbrace>;\<lceil>q2\<rceil>"
  using assert_restricts_pspec pspec_strengthen
  by (metis s seq_mono_right)

lemma pspec_test_restricts: "\<lceil>q \<triangleright> p\<rceil> = \<lceil>q\<rceil>;\<tau>(p)"
proof -
  have a1: "\<forall>s. (q \<triangleright> p)``{s} =
                q``{s} \<inter> p"
    using restrict_range_def by auto      
  have "\<lceil>q \<triangleright> p\<rceil> = (\<Squnion>s. (\<tau>({s}); chaos; \<tau>(q``{s} \<inter> p)))"
    using pspec_def a1 by simp
  also have "... = (\<Squnion>s. \<tau>({s}); chaos; \<tau>(q``{s});\<tau>(p))"   
    using test_inf_eq_seq seq_assoc test.hom_inf by auto 
  also have "... = (\<Squnion>s. \<tau>({s}); chaos; \<tau>(q``{s}));\<tau>(p)"    
    using Nondet_seq_distrib by (simp add:image_image)
  also have "... = \<lceil>q\<rceil>;\<tau>(p)"  
    using pspec_def by simp
  finally show ?thesis .  
qed

lemma pspec_assert_restricts: "\<lceil>q \<triangleright> p\<rceil>;\<lbrace>p\<rbrace> = \<lceil>q \<triangleright> p\<rceil>"
proof -
  have "\<lceil>q \<triangleright> p\<rceil>;\<lbrace>p\<rbrace> = \<lceil>q\<rceil>;(\<tau> p);\<lbrace>p\<rbrace>" 
    by (simp add: pspec_test_restricts)
  also have "... = \<lceil>q\<rceil>;(\<tau> p)"
    by (simp add: seq_assoc test_seq_assert)
  also have "... = \<lceil>q \<triangleright> p\<rceil>"
    by (simp add: pspec_test_restricts)
  finally show ?thesis by simp
qed 

lemma pspec_refine:
  assumes nonaborting: "chaos \<ge> c"
  assumes refine: "\<forall>s. c;\<tau>(q``{s}) \<ge> \<tau>({s});c"
  shows "\<lceil>q\<rceil> \<ge> c"
proof -
  have a1: "\<forall>s. chaos;\<tau>(q``{s}) \<ge> \<tau>({s});c"
    using nonaborting refine seq_mono_left order_trans by blast
  then have a2: "\<forall>s. \<tau>({s});chaos;\<tau>(q``{s}) \<ge> \<tau>({s});c"
    using seq_assoc test_seq_refine by auto

  have "\<lceil>q\<rceil> = (\<Squnion>s. (\<tau>({s}); chaos; \<tau>(q``{s})))"
    using pspec_def by simp
  also have "... \<ge> (\<Squnion>s. (\<tau>({s}); c))" (is "_ \<ge> ?rhs")
    using a2 by (simp add: SUP_subset_mono)
  also have "?rhs = (\<Squnion>s. (\<tau>({s})));c"
    by (simp add: NONDET_seq_distrib)
  also have "... = c"
    by (simp add: Nondet_test_nil)
  finally show ?thesis .
qed

lemma pspec_test_post: "\<lceil>q \<triangleright> p\<rceil> = \<lceil>q \<triangleright> p\<rceil>;\<tau>(p)"
proof -
  have a1: "q \<triangleright> p = (q \<triangleright> p) \<triangleright> p"
    using restrict_range_def by auto
  have "\<lceil>q \<triangleright> p\<rceil> = \<lceil>q \<triangleright> p\<rceil>;\<tau>(p)"
    using a1 pspec_test_restricts by metis
  then show ?thesis .  
qed

lemma pspec_test_commute : "\<lceil>q\<rceil>;\<tau>(q``p) \<ge> \<tau>(p);\<lceil>q\<rceil>"
proof -
  have a: "\<forall>s\<in>p. (q``{s}) \<subseteq> (q``p)" by blast
  have "\<lceil>q\<rceil>;\<tau>(q``p) \<ge> (\<Squnion>s\<in>p. \<tau>({s});chaos;\<tau>(q``{s} \<inter> (q``p)))" (is "_ \<ge> ?rhs")
    by (simp add: pspec_def seq_mono_left SUP_subset_mono NONDET_seq_distrib test_seq_test seq_assoc) 
  also have "?rhs = (\<Squnion>s\<in>p. \<tau>({s});(chaos;\<tau>(q``{s})))"
    by (smt Int_absorb2 Sup.SUP_cong a seq_assoc) 
  also have "... = \<tau>(p);(\<Squnion>s. \<tau>({s});(chaos;\<tau>(q``{s})))"
    by (simp add: test_restricts_Nondet)  
  also have "... = \<tau>(p);\<lceil>q\<rceil>" unfolding pspec_def
    by (simp add: seq_assoc)
  finally show ?thesis.
qed

lemma pspec_to_sequential:
  shows "\<lceil>a O b\<rceil> \<ge> \<lceil>a\<rceil>;\<lceil>b\<rceil>"
proof -
  have "\<lceil>a O b\<rceil> = (\<Squnion>s. \<tau>({s});chaos;\<tau>(b``a``{s}))" 
    by (metis (mono_tags, lifting) Sup.SUP_cong relcomp_Image pspec_def)
  also have "... = (\<Squnion>s. \<tau>({s});chaos;chaos;\<tau>(b``a``{s}))" using chaos_seq_chaos by (simp add: seq_assoc)
  also have "... \<ge> (\<Squnion>s. \<tau>({s});\<lceil>a\<rceil>;\<lceil>b\<rceil>;\<tau>(b``a``{s}))" (is "_ \<ge> ?rhs") using pspec_chaos
    by (simp add: SUP_subset_mono seq_mono SUP_mono' seq_mono_left seq_mono_right) 
  also have "?rhs \<ge> (\<Squnion>s. \<tau>({s});\<lceil>a\<rceil>;\<tau>(a``{s});\<lceil>b\<rceil>)" (is "_ \<ge> ?rhs") using pspec_test_commute
    by (simp add: SUP_mono' seq_assoc seq_mono_right)
  also have "?rhs \<ge> (\<Squnion>s. \<tau>({s});\<tau>({s}));\<lceil>a\<rceil>;\<lceil>b\<rceil>" (is "_ \<ge> ?rhs") using pspec_test_commute
    by (smt NONDET_seq_distrib SUP_mono' order_refl test_pre_post test_seq_idem)
  also have "?rhs = \<lceil>a\<rceil>;\<lceil>b\<rceil>" using test_seq_test Nondet_test_nil by auto
  finally show ?thesis.
qed

lemma pspec_seq_introduce: 
  shows "\<lceil>a O b\<rceil> \<ge> \<lceil>a \<triangleright> p\<rceil>;\<lbrace>p\<rbrace>;\<lceil>b\<rceil>"
proof -
  have "\<lceil>a O b\<rceil> \<ge> \<lceil>a\<rceil>;\<lceil>b\<rceil>" (is "_ \<ge> ?rhs")
    using pspec_to_sequential by simp
  also have "?rhs \<ge> \<lceil>a \<triangleright> p\<rceil>;\<lceil>b\<rceil>"
    using pspec_strengthen
    by (metis nil_ref_test seq_mono_left seq_mono_right seq_nil_right pspec_test_restricts) 
  finally show ?thesis using pspec_assert_restricts by auto
qed

(* TODO How do I generalise over sync? *)

lemma "c;(\<Squnion>s. \<tau>({s});d) = (\<Squnion>s. c;\<tau>({s});d)" using par.seq_NONDET_distrib[of _ _ "\<lambda>s. \<tau>({s});d"]
  using seq_assoc by simp

lemma conj_distribute_relation:
  "c \<iinter> (\<Squnion>s. \<tau>({s});d;\<tau>(q``{s})) = (\<Squnion>s. \<tau>({s});(c \<iinter> d);\<tau>(q``{s}))"
proof -
  have "c \<iinter> (\<Squnion>s. \<tau>({s});d;\<tau>(q``{s})) = (\<Squnion>s1. \<tau>({s1});(c \<iinter> (\<Squnion>s. \<tau>({s});d;\<tau>(q``{s}))))"
    using NONDET_seq_distrib Nondet_test_nil seq_nil_left by metis
  also have "... = (\<Squnion>s1. \<tau>({s1});c \<iinter> \<tau>({s1});(\<Squnion>s. \<tau>({s});d;\<tau>(q``{s})))"
    using test_conj_distrib by simp
  also have "... = (\<Squnion>s1. \<tau>({s1});c \<iinter> (\<Squnion>s\<in>{s1}. \<tau>({s});d;\<tau>(q``{s})))"
    using test_restricts_Nondet seq_assoc by simp
  also have "... = (\<Squnion>s1. \<tau>({s1});c \<iinter> \<tau>({s1});d;\<tau>(q``{s1}))"
    by simp
  also have "... = (\<Squnion>s1. \<tau>({s1});(c \<iinter> d);\<tau>(q``{s1}))"
    using conj.test_sync_post test_conj_distrib by simp
  finally show ?thesis .
qed

lemma par_distribute_relation:
  "c \<parallel> (\<Squnion>s. \<tau>({s});d;\<tau>(q``{s})) = (\<Squnion>s. \<tau>({s});(c \<parallel> d);\<tau>(q``{s}))"
proof -
  have "c \<parallel> (\<Squnion>s. \<tau>({s});d;\<tau>(q``{s})) = (\<Squnion>s1. \<tau>({s1});(c \<parallel> (\<Squnion>s. \<tau>({s});d;\<tau>(q``{s}))))"
    using NONDET_seq_distrib Nondet_test_nil seq_nil_left by metis
  also have "... = (\<Squnion>s1. \<tau>({s1});c \<parallel> \<tau>({s1});(\<Squnion>s. \<tau>({s});d;\<tau>(q``{s})))"
    using test_par_distrib by simp
  also have "... = (\<Squnion>s1. \<tau>({s1});c \<parallel> (\<Squnion>s\<in>{s1}. \<tau>({s});d;\<tau>(q``{s})))"
    using test_restricts_Nondet seq_assoc by simp
  also have "... = (\<Squnion>s1. \<tau>({s1});c \<parallel> \<tau>({s1});d;\<tau>(q``{s1}))"
    by simp
  also have "... = (\<Squnion>s1. \<tau>({s1});(c \<parallel> d);\<tau>(q``{s1}))"
    using par.test_sync_post test_par_distrib by simp
  finally show ?thesis .
qed

lemma pspec_distrib_par: "c \<parallel> (d \<iinter> \<lceil>q\<rceil>) = (c \<parallel> d) \<iinter> \<lceil>q\<rceil>"
proof -
  have "c \<parallel> (d \<iinter> \<lceil>q\<rceil>) = c \<parallel> (\<Squnion>s. (\<tau>({s});(d \<iinter> chaos);\<tau>(q``{s})))"
    using pspec_def conj_distribute_relation by simp
  also have "... = c \<parallel> (\<Squnion>s. (\<tau>({s});d;\<tau>(q``{s})))"
    by simp
  also have "... = (\<Squnion>s. (\<tau>({s});(c \<parallel> d);\<tau>(q``{s})))"
    using par_distribute_relation by simp
  also have "... = (c \<parallel> d) \<iinter> (\<Squnion>s. (\<tau>({s});chaos;\<tau>(q``{s})))"
    using conj_distribute_relation by simp
  also have "... = (c \<parallel> d) \<iinter> \<lceil>q\<rceil>"
    using pspec_def by simp
  finally show ?thesis .
qed

lemma par_pspec_pspec: "\<lceil>q1\<rceil> \<parallel> \<lceil>q2\<rceil> = \<lceil>q1 \<inter> q2\<rceil>"
proof -
  have chaos_nonaborting_test: "\<forall>s x. chaos \<ge> chaos; \<tau>(x)"
    using nil_ref_test seq_mono by fastforce
  have a1: "\<And>s. (q1``{s} \<inter> q2``{s}) = (q1 \<inter> q2)``{s}"
    by blast
  have "\<lceil>q1\<rceil> \<parallel> \<lceil>q2\<rceil> = (\<Squnion>s. (\<tau>({s}); (chaos; \<tau>(q1``{s}) \<parallel> chaos; \<tau>(q2``{s}))))"
    using pspec_def seq_assoc test_Nondet_par_product chaos_nonaborting_test by simp
  also have "... = (\<Squnion>s. (\<tau>({s}); (chaos; (\<tau>(q1``{s} \<inter> q2``{s}))))) "
    using par.test_sync_post2 chaos_par_chaos by auto 
  also have "... = (\<Squnion>s. (\<tau>({s}); (chaos; (\<tau>((q1 \<inter> q2)``{s})))))"
    by (simp add: a1)
  also have "... = \<lceil>q1 \<sqinter> q2\<rceil>"
    by (simp add: pspec_def seq_assoc)
  finally show ?thesis by simp
qed

lemma conj_pspec_pspec: "\<lceil>q1\<rceil> \<iinter> \<lceil>q2\<rceil> = \<lceil>q1 \<inter> q2\<rceil>"
proof -
  have chaos_nonaborting_test: "\<forall>s x. chaos \<ge> chaos; \<tau>(x)"
    using nil_ref_test seq_mono by fastforce
  have a1: "\<And>s. (q1``{s} \<inter> q2``{s}) =
                 (q1 \<inter> q2)``{s}"
    by blast
  have "\<lceil>q1\<rceil> \<iinter> \<lceil>q2\<rceil> =  (\<Squnion>s. (\<tau>({s}); (chaos; \<tau>(q1``{s})
                                  \<iinter> chaos; \<tau>(q2``{s}))))"
    using pspec_def seq_assoc test_Nondet_conj_product chaos_nonaborting_test by simp
  also have "... = (\<Squnion>s. (\<tau>({s}); (chaos; (\<tau>(q1``{s} \<sqinter>
                                           q2``{s}))))) " 
    using conj.test_sync_post2 using inf.nil_sync_atomic_pre test.hom_iso_eq test_top by fastforce
  also have "... = (\<Squnion>s. (\<tau>({s}); (chaos; (\<tau>((q1 \<inter> q2)``{s})))))" by (simp add: a1)
  also have "... = \<lceil>q1 \<sqinter> q2\<rceil>"
    by (simp add: pspec_def seq_assoc)
  finally show ?thesis by simp
qed

lemma pspec_par_term: "\<lceil>q\<rceil> \<parallel> chaos = \<lceil>q\<rceil>"
  using par_pspec_pspec pspec_univ by (metis inf_top.right_neutral)

lemma pspec_chain: 
  assumes recomp_ab: "a O b \<subseteq> c"
  shows "\<lceil>c\<rceil> \<ge> \<lceil>a\<rceil>;\<lceil>b\<rceil>"
  using pspec_strengthen pspec_to_sequential recomp_ab order_trans by metis

lemma pspec_conj_term: "\<lceil>q1\<rceil> = \<lceil>q1\<rceil> \<iinter> chaos"
proof -
  have "\<lceil>q1\<rceil> = \<lceil>q1 \<sqinter> \<top>\<rceil>"
    by simp
  also have "... = \<lceil>q1\<rceil> \<iinter> \<lceil>\<top>\<rceil>"
    using conj_pspec_pspec by metis
  also have "... = \<lceil>q1\<rceil> \<iinter> chaos"
    using pspec_univ by simp
  finally show ?thesis .
qed

lemma pspec_ref_pgm:
  shows "\<lceil>q\<rceil> \<ge> \<pi>(q)"
proof -
  have "\<pi> UNIV \<squnion> \<epsilon> UNIV \<ge> \<pi>(q)" using Env_def Pgm_def Atomic_ref_pgm Atomic_def2 by auto
  then have "(\<pi> UNIV \<squnion> \<epsilon> UNIV)\<^sup>\<star> \<ge> \<pi>(q)" using fiter1 order_trans by blast
  then have a1: "chaos \<ge> \<pi>(q)" unfolding chaos_def using Atomic_ref_pgm iter1 order_trans by blast

  have "\<And>s::'state. (q `` {s}) \<subseteq> q``{s}" by auto
  then have a2: "\<And>s. \<pi>(q);\<tau>(q``{s}) \<ge> \<tau>({s});\<pi>(q)" using pgm_test_ref by simp
  show ?thesis using a1 a2 pspec_refine by simp
qed

lemma pspec_ref_env:
  shows "\<lceil>q\<rceil> \<ge> \<epsilon>(q)"
proof -
  have "\<pi> UNIV \<squnion> \<epsilon> UNIV \<ge> \<epsilon>(q)" using Env_def Pgm_def Atomic_ref_env Atomic_def2 by auto
  then have "(\<pi> UNIV \<squnion> \<epsilon> UNIV)\<^sup>\<star> \<ge> \<epsilon>(q)" using fiter1 order_trans by blast
  then have a1: "chaos \<ge> \<epsilon>(q)" using Env_nonaborting env.Hom_ref_hom order_trans by blast

  have "\<And>s::'state. (q `` {s}) \<subseteq> q``{s}" by auto
  then have a2: "\<And>s. \<epsilon>(q);\<tau>(q``{s}) \<ge> \<tau>({s});\<epsilon>(q)" using env_test_ref by simp
  show ?thesis using a1 a2 pspec_refine by simp
qed

lemma pspec_to_test:
  shows "\<lceil>q\<rceil> \<ge> \<tau>({s. (s,s) \<in> q})"
proof -
  define p where "p \<equiv> {s. (s,s) \<in> q}"
  have "\<forall>s. {s} \<inter> p \<subseteq> p \<inter> q``{s}"
    unfolding restrict_range_def p_def by auto
  then have "\<forall>s. \<tau>(p);\<tau>(q``{s}) 
            \<ge> \<tau>({s});\<tau>(p)"
    by (simp add: test.hom_iso test_seq_test)
  moreover have "chaos \<ge> \<tau>(p)"
    using chaos_def fiter0 iter0 seq_mono nil_ref_test order_trans by fastforce 
  ultimately show ?thesis using pspec_refine p_def by simp
qed

lemma pspec_ref_opt:
  shows "\<lceil>q\<rceil> \<ge> opt q"
  unfolding opt_def using pspec_to_test pspec_ref_pgm by simp

lemma pspec_id_nil: "\<lceil>Id\<rceil> \<ge> nil"
proof -
  have "{s. (s, s) \<in> Id} = UNIV" by auto
  then show ?thesis using pspec_to_test by (metis test_top)
qed

lemma pspec_refine_iterated_relation: "\<lceil>r\<^sup>*\<rceil> \<ge> (\<lceil>r\<rceil>)\<^sup>\<star>"
proof -
  have a0: "\<And>r. \<lceil>(Id \<union> r)\<rceil> \<ge> (nil \<squnion> \<lceil>r\<rceil>)"
    by (metis (no_types) sup.orderE inf_sup_ord(3) le_sup_iff pspec_id_nil pspec_strengthen sup_ge2) 
  have a1: "r\<^sup>* = Id \<union> r\<^sup>*"
    by blast
  have a2: "(Id \<union> r) O (Id \<union> r\<^sup>*) = (r)\<^sup>*"
    by (metis inf_sup_aci(8) sup.commute trancl_reflcl a1 trancl_unfold_left)
  have a3: "\<lceil>(Id \<union> r)\<rceil> \<ge> (nil \<squnion> \<lceil>r\<rceil>)"
    by (metis a0)
  have a4: "\<lceil>Id \<union> (r\<^sup>*)\<rceil> \<ge> (nil \<squnion> \<lceil>r\<^sup>*\<rceil>)"    
    by (metis a0)
  have "\<lceil>r\<^sup>*\<rceil> \<ge> \<lceil>(Id \<squnion> r)\<rceil>; \<lceil>Id \<union> r\<^sup>*\<rceil>" (is "_ \<ge> ?rhs")
    using a2 pspec_chain by simp
  also have "?rhs \<ge> (nil \<squnion> \<lceil>r\<rceil>); (nil \<squnion> \<lceil>r\<^sup>*\<rceil>)" (is "_ \<ge> ?rhs")
    using a1 a3 a4 seq_mono by simp
  also have "?rhs = nil \<squnion> (\<lceil>r\<rceil> \<squnion> \<lceil>r\<^sup>*\<rceil>) \<squnion> \<lceil>r\<rceil>;\<lceil>r\<^sup>*\<rceil>"
    by (simp add: nondet_seq_distrib par.seq_nondet_distrib sup_assoc)
  also have "... \<ge> nil \<squnion> \<lceil>r\<rceil>;\<lceil>r\<^sup>*\<rceil>"
    by (meson sup_mono inf_sup_ord(3) order_refl)
  finally show ?thesis using fiter_induct_nil by simp
qed

end


(* Strong specification with preconditions  
locale strong_pspec_pre = strong_pspec lib_last
  for lib_last :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("L\<^sup>C\<^sub>_ _" [999, 999] 999)
begin
  
(* If you see '\<ltort>' and '\<rtort>' as text instead of symbols, then
  make sure to add the following lines to your isabelle symbols file in 
   ~/.isabelle/IsabelleYYYY/etc/symbols
\<ltort>              code: 0x0027ec  group: operator  font: DejaVuSans
\<rtort>              code: 0x0027ed  group: operator  font: DejaVuSans
  This should not be an issue if you used the readme in the root of this repository.
*)

definition pspecpre :: "'c set\<Rightarrow>'c rel\<Rightarrow>'a::refinement_lattice" ("\<ltort>_,_\<rtort>" 99)
  where "pspecpre p q \<equiv> \<lbrace>p\<rbrace>;\<lceil>q\<rceil>"
  
lemma pspecpre_eq_pspec:
  shows "\<lceil>q\<rceil>=\<ltort>\<top>,q\<rtort>"
  using pspecpre_def assert_top by simp

lemma pspecpre_strengthen_post: 
  assumes q2_strengthen_q1: "q2 \<subseteq> q1"
  shows "\<ltort>p,q1\<rtort> \<ge> \<ltort>p,q2\<rtort>"
proof -
  have "\<lbrace>p\<rbrace>;\<lceil>q1\<rceil> \<ge> \<lbrace>p\<rbrace>;\<lceil>q2\<rceil>"
    using pspec_strengthen seq_mono_right q2_strengthen_q1 by simp
  then show ?thesis using pspecpre_def by simp
qed
  
lemma pspecpre_weaken_pre:
  assumes p2_weakens_p1: "p1 \<subseteq> p2"
  shows "\<ltort>p1,q\<rtort> \<ge> \<ltort>p2,q\<rtort>"
proof -
  have "\<lbrace>p1\<rbrace> \<ge> \<lbrace>p2\<rbrace>"
    using p2_weakens_p1 by (simp add: assert_iso)     
  then have "\<lbrace>p1\<rbrace>;\<lceil>q\<rceil> \<ge> \<lbrace>p2\<rbrace>;\<lceil>q\<rceil>"
    using seq_mono_left by simp
  then show ?thesis using pspecpre_def by simp
qed
  
lemma pspecpre_ref_pspec:
  shows "\<ltort>p,q\<rtort> \<ge> \<lceil>q\<rceil>"
proof -
  have "p \<subseteq> \<top>"
    by simp
  then have "\<ltort>p,q\<rtort> \<ge> \<ltort>\<top>,q\<rtort>"
    using pspecpre_weaken_pre by simp
  then show ?thesis using pspecpre_eq_pspec by simp
qed
  
lemma pspecpre_test_post_extract:
  shows "\<ltort>p1,q \<triangleright> p2\<rtort> = \<ltort>p1,q\<rtort>;\<tau>(p2)"
proof -  
  have "\<ltort>p1,q \<triangleright> p2\<rtort> = \<lbrace>p1\<rbrace>;\<lceil>q \<triangleright> p2\<rceil>"
    using pspecpre_def by simp
  also have "... = \<lbrace>p1\<rbrace>;\<lceil>q\<rceil>;\<tau>(p2)"
    using pspec_test_restricts seq_assoc by simp
  also have "... = \<ltort>p1,q\<rtort>;\<tau>(p2)"
    using pspecpre_def by simp
  finally show ?thesis .
qed

lemma pspecpre_assert_post:
  shows "\<ltort>p1,q \<triangleright> p2\<rtort> = \<ltort>p1,q \<triangleright> p2\<rtort>;\<lbrace>p2\<rbrace>"
proof -  
  have "\<ltort>p1,q \<triangleright> p2\<rtort> = \<lbrace>p1\<rbrace>;\<lceil>q \<triangleright> p2\<rceil>"
    using pspecpre_def by simp
  also have "... = \<lbrace>p1\<rbrace>;\<lceil>q \<triangleright> p2\<rceil>;\<lbrace>p2\<rbrace>"
    using pspec_assert_restricts seq_assoc by simp
  also have "... = \<ltort>p1,q \<triangleright> p2\<rtort>;\<lbrace>p2\<rbrace>"
    using pspecpre_def by simp
  finally show ?thesis .
qed
  
lemma pspecpre_assert_pre:
  shows "\<lbrace>p1\<rbrace>;\<ltort>p2,q\<rtort> = \<ltort>p1 \<inter> p2,q\<rtort>"
proof -
  have "\<lbrace>p1\<rbrace>;\<ltort>p2,q\<rtort> = \<lbrace>p1\<rbrace>;\<lbrace>p2\<rbrace>;\<lceil>q\<rceil>"
    using pspecpre_def seq_assoc by simp
  also have "... = \<lbrace>p1 \<inter> p2\<rbrace>;\<lceil>q\<rceil>"
    using assert_seq_assert by simp
  finally show ?thesis using pspecpre_def by simp
qed
  
lemma pspecpre_pre_internalise:
  shows "\<ltort>p,q\<rtort> = \<ltort>p,p \<triangleleft> q\<rtort>"
proof -
  have "\<ltort>p,q\<rtort>= \<lbrace>p\<rbrace>;\<lceil>q\<rceil>"
    using pspecpre_def by simp
  also have "... = \<lbrace>p\<rbrace>;(\<tau> p);\<lceil>q\<rceil>"
    by (simp add: assert_seq_test)
  also have "... = \<lbrace>p\<rbrace>;(\<tau> p);\<lceil>p \<triangleleft> q\<rceil>"
    using test_restricts_pspec seq_assoc by simp
  also have "... = \<lbrace>p\<rbrace>;\<lceil>p \<triangleleft> q\<rceil>"
    by (simp add: assert_seq_test)
  also have "... = \<ltort>p,p \<triangleleft> q\<rtort>"
    using pspecpre_def by simp
  finally show ?thesis .
qed    
    
lemma pspecpre_ref_test:
  shows "\<ltort>p, q\<rtort> \<ge> \<tau>({s. (s,s) \<in> q})"
  using pspec_to_test pspecpre_def assert_redundant seq_mono_right by metis

lemma pspecpre_id_nil:
  shows "\<ltort>p, Id \<triangleright> p\<rtort> \<ge> nil"
proof -
  have "Id \<triangleright> p = p \<triangleleft> (Id \<triangleright> UNIV)"
    unfolding restrict_domain_def restrict_range_def by auto
  then have "\<ltort>p, Id \<triangleright> p\<rtort> = \<ltort>p, Id \<triangleright> UNIV\<rtort>"
    using pspecpre_pre_internalise by metis
  moreover have "{s. (s,s) \<in>  Id \<triangleright> UNIV} = UNIV"
    unfolding restrict_range_def by auto
  ultimately show ?thesis using pspecpre_ref_test test_top by metis
qed
  
lemma pspecpre_sequential:
  shows "\<ltort>p0,(relcomp q1 q2)\<rtort> \<ge> \<ltort>p0,q1 \<triangleright> p1\<rtort>;\<ltort>p1,q2\<rtort>"
proof -
  have a1: "(relcomp (q1 \<triangleright> p1) (q2)) \<subseteq> ((relcomp q1 q2))"
    using restrict_range_def by auto  
  have "\<ltort>p0,(relcomp q1 q2)\<rtort> = \<lbrace>p0\<rbrace>;\<lceil>(relcomp q1 q2)\<rceil>"
    using pspecpre_def by simp
  also have "... \<ge> \<lbrace>p0\<rbrace>;\<lceil>(relcomp (q1 \<triangleright> p1) (q2))\<rceil>" (is "_ \<ge> ?rhs")
    using pspec_strengthen seq_mono_right a1 by simp
  also have "?rhs \<ge> \<lbrace>p0\<rbrace>;\<lceil>q1 \<triangleright> p1\<rceil>;\<lceil>q2\<rceil>" (is "_ \<ge> ?rhs")
    using pspec_chain seq_mono_right seq_assoc by simp
  also have "?rhs = \<lbrace>p0\<rbrace>;\<lceil>q1 \<triangleright> p1\<rceil>;\<lbrace>p1\<rbrace>;\<lceil>q2\<rceil>"
    using pspec_assert_restricts seq_assoc by simp
  also have "... = \<ltort>p0,q1 \<triangleright> p1\<rtort>;\<ltort>p1,q2\<rtort>"
    using pspecpre_def seq_assoc by simp
  finally show ?thesis .  
qed

lemma pspecpre_tolerates_left:
  assumes tolerates_interference: "tolerates_interference p q r"
  shows "\<ltort>p,q\<rtort> \<ge> \<lceil>r\<^sup>*\<rceil>;\<ltort>p,q\<rtort>"
proof -   
  have a1: "p \<triangleleft> r\<^sup>* = (p \<triangleleft> r\<^sup>* ) \<triangleright> p"    
    using stable_rtrancl tolerates_interference
    unfolding tolerates_interference_def stable_def 
              restrict_range_def restrict_domain_def by auto
  have "p \<triangleleft> (relcomp (r\<^sup>* ) (q)) \<subseteq> q"
    using q_tolerates_rtrancl_left tolerates_interference by metis    
  then have "\<ltort>p,q\<rtort> \<ge> \<ltort>p,p \<triangleleft> (relcomp (r\<^sup>* ) (q))\<rtort>" (is "_ \<ge> ?rhs")
    using pspecpre_strengthen_post by simp
  also have "?rhs = \<ltort>p,(relcomp (r\<^sup>* ) (q))\<rtort>"
    using pspecpre_pre_internalise by simp
  also have "... \<ge> \<lbrace>p\<rbrace>;\<lceil>r\<^sup>*\<rceil>;\<lceil>q\<rceil>" (is "_ \<ge> ?rhs")
    using pspecpre_def pspec_chain seq_mono_right seq_assoc by simp
  also have "?rhs = \<ltort>p, r\<^sup>*\<rtort>;\<lceil>q\<rceil>"
    using pspecpre_def by simp
  also have "... = \<ltort>p, (p \<triangleleft> r\<^sup>* ) \<triangleright> p\<rtort>;\<lceil>q\<rceil>"     
    using a1 pspecpre_pre_internalise by simp
  also have "... = \<ltort>p, (p \<triangleleft> r\<^sup>* ) \<triangleright> p\<rtort>;\<lbrace>p\<rbrace>;\<lceil>q\<rceil>"     
    using pspecpre_assert_post pspec_def by simp
  also have "... = \<ltort>p, (p \<triangleleft> r\<^sup>* ) \<triangleright> p\<rtort>;\<ltort>p,q\<rtort>"     
    using pspecpre_def by (simp add: seq_assoc)
  also have "... = \<ltort>p, r\<^sup>*\<rtort>;\<ltort>p,q\<rtort>"  
    using a1 pspecpre_pre_internalise by simp
  also have "... \<ge> \<lceil>r\<^sup>*\<rceil>;\<ltort>p,q\<rtort>"
    using pspecpre_ref_pspec seq_mono_left by simp
  finally show ?thesis .
qed  

lemma pspecpre_tolerates_right:
  assumes tolerates_interference: "tolerates_interference p q r"  
  shows "\<ltort>p,q\<rtort> \<ge> \<ltort>p,q\<rtort>;\<lceil>r\<^sup>*\<rceil>"
proof -  
  have "p \<triangleleft> (relcomp (q) (r\<^sup>* )) \<subseteq> q"
    using q_tolerates_rtrancl_right tolerates_interference by metis    
  then have "\<ltort>p,q\<rtort> \<ge> \<ltort>p,p \<triangleleft> (relcomp (q) (r\<^sup>* ))\<rtort>" (is "_ \<ge> ?rhs")
    using pspecpre_strengthen_post by simp
  also have "?rhs = \<ltort>p,(relcomp (q) (r\<^sup>* ))\<rtort>"
    using pspecpre_pre_internalise by simp
  also have "... \<ge> \<lbrace>p\<rbrace>;\<lceil>q\<rceil>;\<lceil>r\<^sup>*\<rceil>" (is "_ \<ge> ?rhs")
    using pspecpre_def pspec_chain seq_mono_right seq_assoc by simp
  also have "?rhs = \<ltort>p,q\<rtort>;\<lceil>r\<^sup>*\<rceil>"
    using pspecpre_def by simp
  finally show ?thesis .
qed

end

*) 

end
