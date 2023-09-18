section \<open>Guarantees as mapping over abstract $\pgm$-steps\<close>

theory Guarantees
imports
  "ParallelFlip"

begin

locale pgm_restricts = parallel_flip + 
  constrains env :: "'step :: complete_boolean_algebra \<Rightarrow> 'a :: refinement_lattice" 
  constrains pgm :: "'step::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice" 
begin

definition 
  pgm_restrict:: "'step::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice"
where
  pgm_restrict_def [simp]: "pgm_restrict g = \<pi>(g) \<squnion> \<E>"

lemma pgm_restrict_atomic: "\<exists> q. pgm_restrict g = atomic q" 
  by (metis pgm_or_Env_atomic pgm_restrict_def)

lemma pgm_restrict_strengthen:
  assumes "g2 \<le> g1"
  shows "pgm_restrict g1 \<ge> pgm_restrict g2"
   using assms nondet_mono_left pgm.hom_iso pgm_restrict_def by force

lemma pgm_restrict_chaos: "chaos = (pgm_restrict top)\<^sup>\<omega>"  by (simp add: chaos_rel Pgm_def)

lemma pgm_restrict_refines_chaos: "chaos \<ge> pgm_restrict g" 
  using chaos_rel Env_nonaborting Atomic_nonaborting order.trans Atomic_ref_pgm pgm_restrict_def by auto 

lemma pgm_restrict_nested: "pgm_restrict g1 \<iinter> pgm_restrict g2 = pgm_restrict (g1 \<sqinter> g2)"
  by (metis conj_to_inf_nonaborting sup_inf_distrib2 pgm.hom_inf pgm_restrict_def 
            pgm_restrict_refines_chaos)


end
(*----------  guar_inf ---------------------*)

locale guarantees = pgm_restricts +
  constrains env :: "'step :: complete_boolean_algebra \<Rightarrow> 'a :: refinement_lattice" 
  constrains pgm :: "'step::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice" 
begin

definition
  guar:: "'step ::complete_boolean_algebra \<Rightarrow>'a::refinement_lattice"
where
  guar_def[simp]: "guar g = (pgm_restrict g)\<^sup>\<omega>"

lemma guar_strengthen:
  assumes "g2 \<le> g1"
  shows "(guar g1) \<ge> (guar g2)"
  using assms iter_mono pgm_restrict_strengthen by auto

lemma guar_top: "(guar top) = chaos" by (simp add: pgm_restrict_chaos)
    
lemma chaos_ref_guar: "chaos \<ge> (guar g)" using guar_top guar_strengthen top_greatest by metis 
    
lemma guar_seq_idem: "(guar g) ; (guar g) = (guar g)" by simp

lemma guar_merge: "(guar g1) \<iinter> (guar g2) = (guar (g1 \<sqinter> g2))"
  by (metis conj.atomic_iter_sync_iter guar_def pgm_or_Env_atomic pgm_restrict_def pgm_restrict_nested) 

(* needs assumption pgm_par_pgm: \<pi>\<parallel>\<pi>=\<top> *)
lemma guar_par_guar: "(guar g1) \<parallel> (guar g2) = (guar (g1 \<squnion> g2))"
proof -
  have g1: "(guar g1) \<parallel> (guar g2) = (\<pi>(g1) \<squnion> \<E>)\<^sup>\<omega> \<parallel> (\<pi>(g2) \<squnion> \<E>)\<^sup>\<omega>"
    by simp
  then have g2: "\<dots> = ((\<pi>(g1) \<squnion> \<E>) \<parallel> (\<pi>(g2) \<squnion> \<E>))\<^sup>\<omega>" 
    by (metis par.atomic_iter_sync_iter pgm_or_Env_atomic)
  then have g3: "\<dots> = ((\<pi>(g1) \<parallel> (\<pi>(g2) \<squnion> \<E>)) \<squnion> (\<E> \<parallel> (\<pi>(g2) \<squnion> \<E>)))\<^sup>\<omega>"
    by (simp add: par.nondet_sync_distrib)
  then have g4: "\<dots> = ((\<pi>(g1) \<parallel> \<pi>(g2)) \<squnion> (\<pi>(g1) \<parallel> \<E>) \<squnion> 
                        (\<E> \<parallel> \<pi>(g2)) \<squnion> (\<E> \<parallel> \<E>))\<^sup>\<omega>"
    by (simp add: sup_assoc par.sync_nondet_distrib) 
  then have g5: "\<dots> = (\<pi>(g1) \<squnion> \<pi>(g2) \<squnion> \<E>)\<^sup>\<omega>" 
    using sup_bot.left_neutral par_commute par.atomic_sync_identity 
              par.syncid_syncid pgm_atomic pgm_par_pgm by metis
  then have g6: "\<dots> = (guar (g1 \<squnion> g2))" by (simp)
  thus ?thesis using g1 g2 g3 g4 g5 g6 
    by presburger (* was auto - dubious proof - inconsistent axioms *)
qed

lemma guar_par_idem:
  "(guar g) \<parallel> (guar g) = (guar g)"
  using guar_par_guar by simp

lemma guar_distrib_nondet: "(guar g) \<iinter> (c \<squnion> d) = ((guar g) \<iinter> c) \<squnion> ((guar g) \<iinter> d)"
    by (simp add: conj.nondet_sync_distrib local.conj_commute)

lemma guar_distrib_Nondet: "(guar g) \<iinter> (\<Squnion>C) = (\<Squnion>c\<in>C. (guar g) \<iinter> c)"
  using conj_Nondet_distrib_nonaborting chaos_ref_guar by simp

lemma guar_distrib_conj: "(guar g) \<iinter> (c \<iinter> d) = ((guar g) \<iinter> c) \<iinter> ((guar g) \<iinter> d)"
  using conj_conj_distrib_left by auto

lemma guar_distrib_seq: "(guar g) \<iinter> (c ; d) \<ge> ((guar g) \<iinter> c) ; ((guar g) \<iinter> d)"
  using conj_seq_distrib guar_seq_idem by (simp add: seq_conj_interchange)

(* added and sorry-ed at the discretion of Larissa *)
lemma guar_distrib_seq_eq: "(((guar g) \<iinter> c) ; ((guar g) \<iinter> d)) = ((guar g) \<iinter> (c ; d))"
  sorry

lemma guar_distrib_par: "(guar g) \<iinter> (c \<parallel> d) \<ge> ((guar g) \<iinter> c) \<parallel> ((guar g) \<iinter> d)"
  using guar_par_idem by (metis par_conj_interchange)

lemma guar_conj_nil: "nil \<iinter> (guar g) = nil"
  unfolding guar_def using conj.atomic_iter_sync_nil pgm_restrict_atomic conj_commute by metis

lemma guar_introduce:
  shows "c \<ge> (guar g) \<iinter> c"
  using chaos_ref_guar conj.sync_mono_left conj_chaos_left by metis

lemma guar_conj_test: "(guar g) \<iinter> \<tau>(p) = \<tau>(p)"
proof -
  have "guar g \<iinter> nil = nil"
    using guar_conj_nil local.conj_commute by presburger
then show ?thesis
  by (metis conj.test_sync_post seq_nil_left)
qed 

end
end
