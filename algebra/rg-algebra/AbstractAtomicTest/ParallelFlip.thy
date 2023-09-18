section \<open>Parallel composition of $\pgm$ and $\epsilon$ steps defined via the flip operator\<close>

theory ParallelFlip
imports
  "PgmEnv_Commands"

begin

locale flip = pgm_env_commands (* lib_first for
  lib_first :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("F\<^sup>C\<^sub>_ _" [999, 999] 999) *)
begin

definition flip :: "'a \<Rightarrow> 'a"
  where "flip c \<equiv> (if c \<in> range(\<epsilon>) then 
                        (let p = (THE p. \<epsilon> p = c) in (\<pi>(p)))
                     else undefined)"

lemma flip_def2:
  shows "flip(\<epsilon>(p)) = \<pi>(p)"
proof -
  define P where "P \<equiv> (\<lambda>p'. \<epsilon> p' = \<epsilon> p)"
  have "P p" unfolding P_def by simp
  moreover have "\<And>p'. P p' \<Longrightarrow> p' = p"
    unfolding P_def using env.hom_injective unfolding inj_def by auto
  ultimately have a1: "(THE p'. P p') = p"
    using theI by blast
  have "flip (\<epsilon> p) = (let p' = (THE p'. \<epsilon> p' = (\<epsilon> p)) in (\<pi>(p')))"
    unfolding flip_def by auto
  also have "... = (\<pi> p)"
    using env.hom_injective a1 unfolding P_def by simp
  finally show ?thesis by simp
qed

end

locale parallel_flip = pgm_env_commands + flip +
  assumes env_par_env_axiom: "\<epsilon>(p) \<parallel> \<epsilon>(q) = \<epsilon>(p) \<sqinter> \<epsilon>(q)"  
  assumes pgm_par_pgm:   "\<pi>(p) \<parallel> \<pi>(q) = \<bottom>"
  assumes env_par_pgm_axiom:  "\<epsilon>(p) \<parallel> \<pi>(q) = flip(\<epsilon>(p)) \<sqinter> \<pi>(q)" 

begin

lemma pgm_com_par_pgm_com: "\<pi>(p);c \<parallel> \<pi>(q);d = \<bottom>"
  by (metis par.atomic_pre_sync_atomic_pre pgm_atomic pgm_par_pgm seq_magic_left)

lemma env_com_par_pgm_com:  "\<epsilon>(p);c \<parallel> \<pi>(q);d = \<pi>(p \<sqinter> q);(c \<parallel> d)"
  by (metis env_atomic env_par_pgm_axiom flip_def2 par.atomic_pre_sync_atomic_pre pgm_atomic pgm.hom_inf) 

lemma env_com_par_env_com: "\<epsilon>(p);c \<parallel> \<epsilon>(q);d =  \<epsilon>(p \<sqinter> q);(c \<parallel> d)"
  by (metis env_atomic env.hom_inf env_par_env_axiom par.atomic_pre_sync_atomic_pre)

lemma pgm_par_Env_com: "\<pi>(p);c \<parallel> \<E>;d = \<pi>(p);(c \<parallel> d)"
  by (metis Env_def env_com_par_pgm_com inf_top.left_neutral par.sync_commute)

lemma pgmenv_par_pgmenv: "(\<pi>(r) \<squnion> \<epsilon>(\<top>)) \<parallel> (\<pi>(r) \<squnion> \<epsilon>(\<top>)) = (\<pi>(r) \<squnion> \<epsilon>(\<top>))"
proof -
  have a1: "\<pi>(r)\<parallel>\<epsilon>(\<top>) = \<pi>(r)"
    by (metis abel_semigroup.commute Env_def par.comm.abel_semigroup_axioms
          par.atomic_sync_identity pgm_atomic)
  have a2: "\<epsilon>(\<top>)\<parallel>\<pi>(r) = \<pi>(r)"
    by (metis a1 par_commute)
  have a3: "\<pi>(r)\<parallel>\<pi>(r) = \<bottom>"
    using pgm_par_pgm by blast
  have "(\<pi>(r) \<squnion> \<epsilon>(\<top>)) \<parallel> (\<pi>(r) \<squnion> \<epsilon>(\<top>)) = (\<pi>(r)\<parallel>\<pi>(r)) \<squnion> (\<pi>(r)\<parallel>\<epsilon>(\<top>)) \<squnion> (\<epsilon>(\<top>)\<parallel>\<pi>(r)) \<squnion> (\<epsilon>(\<top>)\<parallel>\<epsilon>(\<top>))"
    using par.nondet_sync_product by simp
  also have "... = (\<pi>(r) \<squnion> \<epsilon>(\<top>))"    
    using env_par_env_axiom a1 a2 a3 by simp
  finally show ?thesis by simp
qed

end

end