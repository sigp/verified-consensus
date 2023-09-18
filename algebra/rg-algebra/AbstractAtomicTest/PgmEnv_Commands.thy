section \<open>Atomic commands with three sync operators: parallel, weak conjunction, supremum\<close>

theory PgmEnv_Commands
imports
  "../General/Abstract_Hom"
(*  "Atomic_Commands" *)
  "Abstract_Atomic_Test"
 (* "../General/Liberation" *)
begin

instantiation prod :: (complete_boolean_algebra, complete_boolean_algebra) complete_boolean_algebra
begin
  fun minus_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b"
    where "minus_prod (Pair a1 b1) (Pair a2 b2) = Pair (a1 - a2) (b1 - b2)"

  fun uminus_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b"
    where "uminus_prod (Pair a b) = Pair (-a) (-b)"

  definition Inf_prod :: "('a \<times> 'b) set \<Rightarrow> 'a \<times> 'b"
    where "Inf_prod P \<equiv> Pair (\<Sqinter>p\<in>P. fst p)  (\<Sqinter>p\<in>P. snd p)"

  definition Sup_prod :: "('a \<times> 'b) set \<Rightarrow> 'a \<times> 'b"
    where "Sup_prod P \<equiv> Pair (\<Squnion>p\<in>P. fst p)  (\<Squnion>p\<in>P. snd p)"

  definition bot_prod :: "'a \<times> 'b"
    where "bot_prod \<equiv> Pair bot bot"
  
  fun sup_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b"
    where "sup_prod (Pair a1 b1) (Pair a2 b2) = Pair (sup a1 a2) (sup b1 b2)"

  definition top_prod :: "'a \<times> 'b"
    where "top_prod \<equiv> Pair top top"

  fun inf_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b"
    where "inf_prod (Pair a1 b1) (Pair a2 b2) = Pair (inf a1 a2) (inf b1 b2)"

  fun less_eq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
    where "less_eq_prod (Pair a1 b1) (Pair a2 b2) = ((a1 \<le> a2) \<and> (b1 \<le> b2))"

  definition less_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
    where "less_prod a b \<equiv> less_eq a b \<and> a \<noteq> b"

instance proof
  fix x y :: "'a \<times> 'b"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_prod_def by (cases x; cases y; auto)
next
  fix x :: "'a \<times> 'b"
  show "x \<le> x"
    by (cases x; auto)
next
  fix x y z :: "'a \<times> 'b"
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z; auto)
next 
  fix x y :: "'a \<times> 'b"
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y; auto)
next
  fix x y :: "'a \<times> 'b"
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y; auto)
next
  fix x y :: "'a \<times> 'b"
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y; auto)
next
  fix x y z :: "'a \<times> 'b"
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z; auto)
next
  fix x y :: "'a \<times> 'b"
  show "x \<le> x \<squnion> y"
    by (cases x; cases y; auto)
next
  fix x y :: "'a \<times> 'b"
  show "y \<le> x \<squnion> y"
    by (cases x; cases y; auto)
next
  fix x y z :: "'a \<times> 'b"
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z; auto)
next
  fix x :: "'a \<times> 'b"
  fix A :: "('a \<times> 'b) set"
  show "x \<in> A \<Longrightarrow> \<Sqinter>A \<le> x"
    unfolding Inf_prod_def 
    apply (cases x; simp)
    apply (metis INF_lower fst_conv snd_conv)
    done
next
  fix z :: "'a \<times> 'b"
  fix A :: "('a \<times> 'b) set"
  show "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> \<Sqinter>A"
    unfolding Inf_prod_def 
    apply (cases z; simp)
    apply (metis (no_types) le_INF_iff less_eq_prod.simps prod.collapse)
    done
next
  fix x :: "'a \<times> 'b"
  fix A :: "('a \<times> 'b) set"
  show "x \<in> A \<Longrightarrow> x \<le> \<Squnion>A"
    unfolding Sup_prod_def apply (cases x; simp)
    apply (metis SUP_upper fst_conv snd_conv)
    done
next
  fix z :: "'a \<times> 'b"
  fix A :: "('a \<times> 'b) set"
  show "(\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> \<Squnion>A \<le> z"
    unfolding Sup_prod_def apply (cases z; simp)
    apply (metis (no_types) SUP_least less_eq_prod.simps prod.collapse)
    done
next
  show "(\<Sqinter>{}) = (\<top>::('a \<times> 'b))"
    unfolding Inf_prod_def top_prod_def by simp
next
  show "(\<Squnion>{}) = (\<bottom>::('a \<times> 'b))"
    unfolding Sup_prod_def bot_prod_def by simp
next
  fix A :: "('a \<times> 'b) set set"
  show "\<Sqinter>(Sup ` A) \<le> \<Squnion>(Inf ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y})"
    unfolding Sup_prod_def Inf_prod_def by (auto simp add: INF_SUP_set image_image)
next
  fix a :: "'a \<times> 'b"
  show "\<bottom> \<le> a"
    unfolding bot_prod_def by (cases a; auto)
next
  fix a :: "'a \<times> 'b"
  show "a \<le> \<top>"
    unfolding top_prod_def by (cases a; auto)
next
  fix x y z :: "'a \<times> 'b"
  show "x \<squnion> y \<sqinter> z = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
    by (cases x; cases y; cases z; auto simp add: sup_inf_distrib1) 
next
  fix x :: "'a \<times> 'b"
  show "x \<sqinter> - x = \<bottom>"
    unfolding bot_prod_def by (cases x; auto)
next
  fix x :: "'a \<times> 'b"
  show "x \<squnion> - x = \<top>"
    unfolding top_prod_def by (cases x; auto)
next
  fix x y :: "'a \<times> 'b"
  show "x - y = x \<sqinter> - y"
    by (cases x; cases y; auto simp add: diff_eq)
qed

end

locale pgm_env_atomic_pre = (*lib_boolean_stages lib 
  for lib :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("E\<^sup>C\<^sub>_ _" [999, 999] 999) + *)
  fixes pgm::"'step ::complete_boolean_algebra\<Rightarrow>'a::refinement_lattice" (\<open>\<pi>\<close>)
  fixes env::"'step ::complete_boolean_algebra\<Rightarrow>'a::refinement_lattice" (\<open>\<epsilon>\<close>)
  assumes pgm_env_distinct: "\<And>a b. \<pi>(a) \<sqinter> \<epsilon>(b) = \<bottom>"


locale pgm_env_atomic_hom_pre = pgm_env_atomic_pre  +
  pgm: abstract_hom_commands pgm +
  env: abstract_hom_commands env 
(*
  for lib_bool  :: "'b \<Rightarrow> 'c::complete_boolean_algebra \<Rightarrow> 'c" ("E\<^sup>R\<^sub>_ _" [999, 999] 999) *)
begin
end



locale pgm_env_atomic = pgm_env_atomic_hom_pre +
  constrains pgm::"'step ::complete_boolean_algebra\<Rightarrow> 'prog ::refinement_lattice"
  constrains env::"'step ::complete_boolean_algebra\<Rightarrow> 'prog ::refinement_lattice"
begin


abbreviation "Pgm" where "Pgm \<equiv> pgm.Hom"
lemmas Pgm_def = pgm.Hom_def

abbreviation "Env" ("\<E>") where "Env \<equiv> env.Hom"
lemmas Env_def = env.Hom_def

lemma shows "((\<pi>(p) \<squnion> \<epsilon>(e)) = (\<pi>(p') \<squnion> \<epsilon>(e'))) = (p = p' \<and> e = e')"
  apply (cases "p = p'")
    apply (cases "e = e'")
      apply simp
      apply (metis boolean_algebra_cancel.sup0 env.hom_iso_eq inf_sup_aci(5) pgm_env_distinct sup_inf_distrib1)
    apply (cases "e = e'")
      apply (metis pgm.hom_iso_eq pgm_env_distinct sup_bot.left_neutral sup_commute sup_inf_distrib2)
      apply (metis inf_sup_absorb inf_sup_aci(1) inf_sup_distrib1 pgm.hom_iso_eq pgm_env_distinct)
  done

lemma shows "((\<pi>(p) \<squnion> \<epsilon>(e)) = (\<pi>(p') \<squnion> \<epsilon>(e'))) = (p = p' \<and> e = e')"
proof (cases "p = p'")
  case a: True
  then show ?thesis
  proof (cases "e = e'")
    case True
    then show ?thesis using a by simp
  next
    case False
    then show ?thesis using a by (metis boolean_algebra_cancel.sup0 env.hom_iso_eq inf_sup_aci(5) pgm_env_distinct sup_inf_distrib1)
  qed
next
  case a: False
  then show ?thesis
  proof (cases "e = e'")
    case True
    then show ?thesis using a by (metis pgm.hom_iso_eq pgm_env_distinct sup_bot.left_neutral sup_commute sup_inf_distrib2)
  next
    case False
    then show ?thesis using a by (metis inf_sup_absorb inf_sup_aci(1) inf_sup_distrib1 pgm.hom_iso_eq pgm_env_distinct)
  qed
qed

lemma atomic_inj:
  shows "((\<pi>(p) \<squnion> \<epsilon>(e)) = (\<pi>(p') \<squnion> \<epsilon>(e'))) = (p = p' \<and> e = e')"
proof (cases "p = p'")
  case a1: True
  then show ?thesis proof (cases "e = e'")
    case True
    then show ?thesis using a1 by simp
  next
    case False
    then show ?thesis using a1
      by (metis env.hom_iso_eq sup_commute sup_inf_distrib2 sup_bot.right_neutral pgm_env_distinct)
  qed
next
  case a1: False
  then show ?thesis proof (cases "e = e'")
    case True
    then show ?thesis using a1 by (metis pgm.hom_iso_eq sup_commute sup_inf_distrib1 sup_bot.right_neutral pgm_env_distinct)
  next
    case False
    then show ?thesis using a1 by (metis env.hom_iso_eq sup_commute sup_inf_distrib1 sup_bot.right_neutral pgm_env_distinct)
  qed
qed

lemma intermediate1: "(\<pi> p1 \<squnion> \<epsilon> q1) \<sqinter> (\<pi> p2 \<squnion> \<epsilon> q2) = (\<pi> p1 \<sqinter> \<pi> p2) \<squnion> (\<pi> p1 \<sqinter> \<epsilon> q2) \<squnion> (\<epsilon> q1 \<sqinter> \<pi> p2) \<squnion> (\<epsilon> q1 \<sqinter> \<epsilon> q2)"
  by (metis sup_assoc inf_sup_distrib1 inf_sup_distrib2)

lemma "(\<pi> p1 \<sqinter> \<pi> p2) \<squnion> (\<epsilon> q1 \<sqinter> \<epsilon> q2) = (\<pi> p1 \<squnion> \<epsilon> q1) \<sqinter> (\<pi> p2 \<squnion> \<epsilon> q2)"
  using intermediate1 pgm_env_distinct by (simp add: inf_sup_aci(1))

lemma pgm_env_inf_nondet:
  shows "(\<pi> p1 \<sqinter> \<pi> p2) \<squnion> (\<epsilon> q1 \<sqinter> \<epsilon> q2) = (\<pi> p1 \<squnion> \<epsilon> q1) \<sqinter> (\<pi> p2 \<squnion> \<epsilon> q2)"
proof -
  have "(\<pi> p1 \<squnion> \<epsilon> q1) \<sqinter> (\<pi> p2 \<squnion> \<epsilon> q2) = (\<pi> p1 \<sqinter> \<pi> p2) \<squnion> (\<pi> p1 \<sqinter> \<epsilon> q2) \<squnion> (\<epsilon> q1 \<sqinter> \<pi> p2) \<squnion> (\<epsilon> q1 \<sqinter> \<epsilon> q2)"    
    by (metis sup_assoc inf_sup_distrib1 inf_sup_distrib2)
  also have "... = (\<pi> p1 \<sqinter> \<pi> p2) \<squnion> (\<epsilon> q1 \<sqinter> \<epsilon> q2) "
    using pgm_env_distinct by (simp add: inf_sup_aci(1))
  finally show ?thesis by simp
qed

definition atomic :: "('step \<times> 'step) \<Rightarrow> 'prog"
  where "atomic \<equiv> (\<lambda>(pgm,env). \<pi>(pgm) \<squnion> \<epsilon>(env))"

sublocale atomic: abstract_hom_commands atomic 
proof (unfold_locales)
  show "inj atomic"
    unfolding inj_def atomic_def using atomic_inj by auto
next
  fix p q
  show "atomic (p \<squnion> q) = atomic p \<squnion> atomic q"
    unfolding atomic_def by (cases p; cases q; clarsimp; metis sup.commute sup.assoc)
next
  fix p q
  show "atomic (p \<sqinter> q) = atomic p \<sqinter> atomic q"
    unfolding atomic_def
    apply (cases p)
    apply (cases q)
    apply (clarsimp simp add: pgm_env_inf_nondet)
    done
next
  show "atomic \<bottom> = \<bottom>"
    unfolding atomic_def by (simp add: bot_prod_def)
next
  fix p q 
  show "(p \<le> q) = (atomic q \<ge> atomic p)"
    unfolding atomic_def 
    apply (cases p; cases q; clarsimp, safe)
       apply (simp add: pgm.hom_mono sup.coboundedI1)
      apply (simp add: env.hom_mono le_supI2)
     apply (metis atomic_inj le_iff_sup pgm.hom_sup sup_assoc)
    by (metis atomic_inj env.hom_sup inf_sup_aci(5) le_iff_sup sup_assoc)
qed

lemma pgm_env_negate: 
  shows " atomic.negate(\<pi>(p) \<squnion> \<epsilon>(q)) = \<pi>(-p) \<squnion> \<epsilon>(-q)"
proof -
  have "\<pi>(-p) \<squnion> \<epsilon>(-q) = atomic (-p,-q)" unfolding atomic_def by auto
  also have "... =  atomic.negate(atomic (p,q))" unfolding atomic_def atomic.negate_def
    by (metis atomic_def atomic.hom_not uminus_prod.simps)
  also have "... =  atomic.negate(\<pi>(p) \<squnion> \<epsilon>(q))"
    unfolding atomic_def by auto
  finally show ?thesis by simp
qed

lemma Pgm_inverse_Env: 
  shows "Pgm = atomic.negate(Env)"
  unfolding pgm.Hom_def env.Hom_def by (metis compl_bot_eq compl_top_eq env.hom_bot inf_sup_aci(5)
      sup_bot_left pgm_env_negate pgm.hom_bot) 


lemma pgm_atomic: "\<exists> q. \<pi>(p) = atomic(q)"
proof -
  have "atomic (p,\<bottom>) = \<pi>(p)" unfolding atomic_def by auto
  then show ?thesis by metis
qed

lemma env_atomic: "\<exists> q. \<epsilon>(p) = atomic(q)"
proof -
  have "atomic (\<bottom>,p) = \<epsilon>(p)" unfolding atomic_def by auto
  then show ?thesis by metis
qed




end

locale pgm_env_commands_pre = seq + abstract_test_commands  + par + conj + pgm_env_atomic +
  constrains seq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a::refinement_lattice"
  constrains test :: "'t ::complete_boolean_algebra \<Rightarrow> 'a"
  constrains par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  constrains conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  constrains pgm :: "'step :: complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice"
  constrains env :: "'step \<Rightarrow>'a::refinement_lattice"
                                                   
locale pgm_env_commands = pgm_env_commands_pre  + 
  atomic_test_commands seq  atomic par Env conj test 
 (* for lib :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("E\<^sup>C\<^sub>_ _" [999, 999] 999) *)
begin

definition env_steps_set :: "'a::refinement_lattice set" 
  where "env_steps_set \<equiv> range(\<epsilon>)"
definition pgm_steps_set :: "'a::refinement_lattice set"
  where "pgm_steps_set \<equiv> range(\<pi>)"

lemma pgm_general_atomic: "range(\<pi>) \<subseteq> range(atomic)" using pgm_atomic by fastforce 
lemma env_general_atomic: "range(\<epsilon>) \<subseteq> range(atomic)" using env_atomic by fastforce 

lemma Atomic_def2:
  shows "Atomic = Pgm \<squnion> Env"
proof -
  have "Atomic = atomic (\<top>,\<top>)" by (simp add: Atomic_def top_prod_def)
  also have "... = Pgm \<squnion> Env" unfolding atomic_def Pgm_def Env_def by auto
  finally show ?thesis by simp
qed

lemma chaos_rel:
  shows "chaos = (Pgm \<squnion> \<E>)\<^sup>\<omega>"
  using chaos_def unfolding Atomic_def2 by simp

lemma chaos_def2: 
  shows "chaos \<equiv> (\<pi> \<top> \<squnion> \<epsilon> \<top>)\<^sup>\<omega>"
  using chaos_rel Pgm_def Env_def Env_def by simp

lemma Pgm_Env_disjoint: "Pgm \<sqinter> \<E> = \<bottom>" using atomid_sup_compl Pgm_inverse_Env
  by (simp add: inf.sync_commute)

lemma pgm_conj_atomid: "\<pi> p \<iinter> \<E> = \<bottom>"
  by (metis atomic_conj_inf env.Hom_def par.syncid_atomic pgm_atomic 
      pgm_env_atomic_pre.pgm_env_distinct pgm_env_atomic_pre_axioms)

lemma pgm_env_distinct: "\<pi>(p) \<sqinter> \<epsilon>(q) = \<bottom>"  
proof -
  have a2: "Pgm \<sqinter> \<E> \<ge> \<pi>(p) \<sqinter> \<E>" by (metis conj_to_inf pgm_conj_atomid Pgm_Env_disjoint) 
  then have a3: "... \<ge> \<pi>(p) \<sqinter> \<epsilon>(q)" by (simp add: pgm_env_distinct)
  thus ?thesis by (metis Pgm_Env_disjoint bot.extremum_uniqueI) 
qed

lemma "atomic.negate(Pgm) = env top"
  by (metis atomic.hom_not double_compl Env_def par.syncid_atomic Pgm_inverse_Env)

lemma "atomic.negate(Pgm) = \<E>"
  using Pgm_inverse_Env par.syncid_atomic by auto
    
lemma Atomic_ref_pgm: "Atomic \<ge> \<pi> p"
proof -
  have "Atomic \<ge> Pgm"
    by (metis (no_types) atomic.hom_not par.syncid_atomic Pgm_inverse_Env atomic.Hom_ref_hom)
  then show ?thesis
    by (metis (no_types) le_iff_sup le_sup_iff Pgm_def pgm.hom_iso top_greatest)
qed

lemma Atomic_ref_env: "Atomic \<ge> \<epsilon> p"
proof -
  have "Atomic \<ge> \<E>"
    using par.syncid_atomic atomic.Hom_ref_hom by force
  then show ?thesis
    using env.Hom_ref_hom Env_def order.trans by metis
qed

lemma pgm_or_Env_atomic: "\<exists> q. atomic(q) = \<pi>(p) \<squnion> \<E>"
  by (metis atomic.hom_sup par.syncid_atomic pgm_atomic)

lemma pgm_conj_pgm: "\<pi>(p) \<iinter> \<pi>(q) = \<pi>(p \<sqinter> q)"
proof -
  have "\<pi> p \<iinter> \<pi> q = \<pi> p \<sqinter> \<pi> q" 
    by (metis (no_types) Atomic_ref_pgm chaos_def conj_to_inf_nonaborting iter1 order.trans)
  then show ?thesis by simp
qed

lemma env_conj_env: "\<epsilon>(p) \<iinter> \<epsilon>(q) = \<epsilon>(p \<sqinter> q)"
proof -
  have "\<epsilon> p \<iinter> \<epsilon> q = \<epsilon> p \<sqinter> \<epsilon> q" 
    by (metis (no_types) Atomic_ref_env chaos_def conj_to_inf_nonaborting iter1 order.trans)
  then show ?thesis by simp
qed

lemma pgm_conj_env: "\<pi>(p) \<iinter> \<epsilon>(q) = \<bottom>"
  by (metis atomic_conj_inf env_atomic pgm_atomic pgm_env_distinct)

lemma env_conj_pgm: "\<epsilon>(p) \<iinter> \<pi>(q) = \<bottom>"
  using pgm_conj_env conj_commute by simp

lemma pgmenv_conj_env: "((\<pi>(a) \<squnion> \<epsilon>(b)) \<iinter> (\<epsilon>(c))) = (\<epsilon>(b \<sqinter> c))"
  using env_conj_env pgm_conj_env by (simp add: conj.nondet_sync_distrib)

lemma pgmenv_conj_pgmenv: "((\<pi>(a) \<squnion> \<epsilon>(b)) \<iinter> (\<pi>(c) \<squnion> \<epsilon>(d))) = (\<pi>(a \<sqinter> c) \<squnion> \<epsilon>(b \<sqinter> d))"
  using pgm_conj_pgm env_conj_env pgm_conj_env env_conj_pgm 
        by (simp add: conj.nondet_sync_product)
 
lemma pgmenv_par_env: "(\<pi>(r) \<squnion> \<epsilon>(\<top>)) \<parallel> (\<epsilon>(\<top>)) = (\<pi>(r) \<squnion> \<epsilon>(\<top>))"
  by (metis Env_def Env_def par.atomic_sync_identity par.sync_commute pgm_or_Env_atomic)
  
lemma Pgm_nonaborting: "chaos \<ge> Pgm"
   using Atomic_nonaborting dual_order.trans Pgm_def Atomic_ref_pgm unfolding Pgm_def by blast

lemma Env_nonaborting: "chaos \<ge> \<E>"
   using Atomic_nonaborting dual_order.trans par.syncid_atomic atomic.Hom_ref_hom by metis

lemma env_or_Pgm_atomic: "\<exists> q. atomic(q) = \<epsilon>(p) \<squnion> Pgm" 
    by (metis atomic.hom_sup env_atomic pgm_atomic Pgm_def) 

lemma negate_env_sup_Env_atomic: "\<exists> q. atomic(q) = (atomic.negate(\<epsilon>(p)) \<sqinter> \<E>)"
   by (metis (full_types) atomic.hom_inf atomic.hom_not env_atomic par.syncid_atomic)


lemma pgm_or_env_atomic: "\<exists>r. atomic(r) = \<pi>(p) \<squnion> \<epsilon>(q)" using pgm_atomic env_atomic
   by (metis atomic.hom_sup)

lemma negate_env_nondet_env: "atomic.negate(\<epsilon>(p)) \<squnion> \<epsilon>(p) = Atomic" using env_atomic atomic.hom_compl_inf by metis
lemma negate_env_inf_env: "atomic.negate(\<epsilon>(p)) \<sqinter> \<epsilon>(p) = \<bottom>" by (metis atomic.hom_compl_sup env_atomic) 
lemma negate_env_inf_Env_nondet_env: "(atomic.negate(\<epsilon>(p)) \<sqinter> \<E>) \<squnion> \<epsilon>(p) =  \<E>"
  by (metis abstract_hom_commands.hom_compl_inf env.abstract_hom_commands_axioms inf.atomic_sync_identity 
      negate_env_nondet_env par.syncid_atomic sup.right_idem sup_inf_distrib2) 

lemma env_negate_def2: "env.negate(\<epsilon>(p)) = atomic.negate(\<epsilon>(p)) \<sqinter> \<E>"
proof -
  have b1: "\<exists> q. \<epsilon>(q) = (atomic.negate(\<epsilon>(p)) \<sqinter> \<E>)"
  proof -
    have f1: "\<epsilon> (- p) = \<E> \<sqinter> env.negate (\<epsilon> p)"
      by (metis env.Hom_ref_hom env.hom_not inf.absorb_iff2)
    have f2: "atomic.negate (\<epsilon> p) \<sqinter> \<E> \<sqinter> env.negate (\<epsilon> p) = env.negate (\<epsilon> p) \<sqinter> atomic.negate (\<epsilon> p)"
      by (metis (no_types, lifting) abstract_hom_commands.hom_not env.abstract_hom_commands_axioms 
          f1 inf.sync_assoc inf.sync_commute)
    have "\<epsilon> p \<sqinter> env.negate (\<epsilon> p) = \<epsilon> p \<sqinter> atomic.negate (\<epsilon> p)"
      using negate_env_inf_env env.hom_compl_inf inf.sync_commute env.hom_compl_sup by auto
    then have "\<epsilon> (- p) = \<E> \<sqinter> atomic.negate (\<epsilon> p)"
      using f2 f1 by (metis negate_env_inf_Env_nondet_env Env_def env.hom_compl_inf inf.nondet_sync_distrib)
    then show ?thesis
      by (metis (no_types) inf.sync_commute)
  qed 
  have b2: "(atomic.negate(\<epsilon>(p)) \<sqinter> \<epsilon>(p)) \<sqinter> \<E> = \<bottom> \<sqinter> \<E>" by (simp add: negate_env_inf_env)
  have b3: "(atomic.negate(\<epsilon>(p)) \<sqinter> \<E>) \<sqinter> \<epsilon>(p) = \<bottom>"
    by (metis negate_env_inf_env inf.sync_assoc inf.sync_commute inf_bot_left) 
  have b4: "\<epsilon>(p) \<sqinter> (atomic.negate(\<epsilon>(p)) \<sqinter> \<E>) = \<bottom>" using b3 inf.sync_commute by auto
  thus ?thesis 
    using b1 negate_env_inf_Env_nondet_env 
    by (metis b3 Env_def env.hom_compl_sup env.hom_compl_inf inf.nondet_sync_distrib3 inf_sup_absorb)
qed

lemma atomic_negate_env: "atomic.negate(\<epsilon>(p)) = env.negate(\<epsilon>(p)) \<squnion> Pgm" 
proof -
  have d1: "env.negate(\<epsilon>(p)) \<squnion> Pgm = (atomic.negate(\<epsilon>(p)) \<sqinter> \<E>) \<squnion> Pgm" 
     using env_negate_def2 by auto 
  then have d2: "... = (atomic.negate(\<epsilon>(p)) \<squnion> Pgm) \<sqinter> Atomic"
    by (metis Atomic_def2 sup.commute sup_inf_distrib2) 
  thus ?thesis
    by (metis env.hom_not pgm.hom_bot pgm.hom_compl_inf pgm.hom_not pgm_env_negate sup.commute 
        sup_bot.left_neutral) 
qed

lemma env_negate_def3: "env.negate(\<epsilon>(p)) = atomic.negate(\<epsilon>(p) \<squnion> Pgm)"
    by (metis atomic_negate_env atomic.hom_not double_compl env_atomic env.hom_not) 

definition general_atomic :: "'c \<Rightarrow> 'a" ("\<alpha>")
  where "general_atomic step = \<pi>(step) \<squnion> \<epsilon>(step)"

sublocale general_atomic: abstract_hom_commands general_atomic
proof (unfold_locales)
  show "inj general_atomic"
    unfolding inj_def atomic_def
    by (simp add: general_atomic_def atomic_inj)
next
  fix p q
  show "\<alpha> (p \<squnion> q) = \<alpha>(p) \<squnion> \<alpha>(q)"
    unfolding general_atomic_def by (simp add: inf_sup_aci(7) sup_assoc)
next
  fix p q
  show "\<alpha> (p \<sqinter> q) = \<alpha>(p) \<sqinter> \<alpha>(q)"
    unfolding general_atomic_def by (simp add: pgm_env_inf_nondet)
next
  show "general_atomic \<bottom> = \<bottom>"
    unfolding general_atomic_def by (simp add: bot_prod_def)
next
  fix p q 
  show "(p \<le> q) = (\<alpha>(q) \<ge> \<alpha>(p))"
    unfolding atomic_def
    by (metis general_atomic_def atomic_inj env.hom_inf le_iff_inf pgm.hom_inf pgm_env_inf_nondet)
qed

abbreviation "Atomic2" where "Atomic2 \<equiv> general_atomic.Hom"
lemmas Atomic2_def = general_atomic.Hom_def

lemma seq_iter_conj:
  assumes "a = atomic(r\<^sub>1, r\<^sub>2)" and "b = atomic(s\<^sub>1, s\<^sub>2)"
  shows "a;a\<^sup>\<omega> \<iinter> b = a \<iinter> b"
proof -
  have "a;a\<^sup>\<omega> \<iinter> b = a;a\<^sup>\<omega> \<iinter> b;nil" by simp        
  also have "... = (a \<iinter> b);(a\<^sup>\<omega> \<iinter> nil)"
    using assms
    using conj.atomic_pre_sync_atomic_pre by blast
  also have "... = (a \<iinter> b);nil"
  proof -
    have "(a \<iinter> b);(a\<^sup>\<omega> \<iinter> nil) = (a \<iinter> b);((a;a\<^sup>\<omega> \<squnion> nil) \<iinter> nil)" using iter_unfold sup.commute by metis
    also have "... = (a \<iinter> b);((a;a\<^sup>\<omega> \<iinter> nil) \<squnion> (nil \<iinter> nil))"
      by (simp add: conj.nondet_sync_distrib)
    also have "... = (a \<iinter> b);((a;a\<^sup>\<omega> \<iinter> nil) \<squnion> nil)"
      by auto
    also have "... = (a \<iinter> b);nil" using assms
      using calculation conj.atomic_iter_sync_nil by auto
    finally show ?thesis.
  qed
  also have "... = a \<iinter> b" by simp
  finally show ?thesis.
qed

lemma atomic_general_atomic:"atomic(r, r) = \<alpha>(r)" unfolding atomic_def general_atomic_def by auto

end
end
