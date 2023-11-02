theory CRA_Atomic
imports Seq_Atomic CRA_Obs
begin

locale sync_atomic_elem =  sync_semigroup + seq: seq_atomic  +  
  constrains f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and unit_of :: "'a \<Rightarrow> 'a" and 
             seq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and first :: "'a \<Rightarrow> 'a" and
             last :: "'a \<Rightarrow> 'a" and test :: "'states \<Rightarrow> 'a"  and
             step :: "labels \<Rightarrow> ('states \<times> 'states) \<Rightarrow> 'a"
           assumes seq_atomic_abort_sync: "f y (bottom y) \<notin> \<Omega> \<Longrightarrow> f (step l s; y) (step l' s'; b) \<le>  f (step l s) (step l' s') ;  f y (bottom y) \<or> f (step l s; y) (step l' s'; b) \<le>  f (step l s) (step l' s') ;  f b (bottom b) "
           assumes seq_atomic_nonaborting_sync: "f y (bottom y) \<in> \<Omega> \<Longrightarrow> f b (bottom b) \<in> \<Omega> \<Longrightarrow> f (step l s; y) (step l' s'; b) \<le>  f (step l s) (step l' s') ;  f y  b"
           assumes seq_bot_sync: "x \<in> \<Omega> \<Longrightarrow> f (x ; y) (step l s; b) \<le>  f x (step l s) ;  f y b"

  assumes bot_conj_step: "x \<in> \<Omega> \<Longrightarrow>  f (step l s ; c) x \<in> \<Omega>"
  assumes bot_conj_test: "x \<in> \<Omega> \<Longrightarrow>  f (test t) x \<in> \<Omega>"
  assumes sync_step_test: " f (test t) (step l s ; x) \<in> \<Omega>"  
  assumes conv_merge_step: "x \<le> f (step l s) (step l' s') \<Longrightarrow> x \<notin> \<Omega> \<Longrightarrow>
          \<exists>l'' s''. x \<le> step l'' s'' \<and> step l'' s''  \<le> f (step l s) (step l' s') " 


begin


lemma seq_bot_sync': "x \<in> \<Omega> \<Longrightarrow> f ( (step l s); b) (x ; y) \<le>  f  (step l s) x ; f b y"
  by (meson commute dual_order.trans seq.flip.mono_f seq_bot_sync)


lemma seq_atomic_nonaborting_sync':"f b (bottom b) \<notin> \<Omega> \<Longrightarrow> f (step l s; y) (step l' s'; b) \<le>  f (step l s) (step l' s') ;  f b (bottom b) \<or> f (step l s; y) (step l' s'; b) \<le>  f (step l s) (step l' s') ;  f y (bottom y) "
  by (meson commute dual_order.trans seq.flip.mono_f seq_atomic_abort_sync)
(* lemma test_nonempty[simp]: "\<Down> (range test) \<union> \<Omega> = \<Down> (range test)"
  by (safe; clarsimp simp: in_down_iff down_image_iff) *)


(* lemma steps_nonempty[simp]:"\<Down> (\<Union> (range ` range step)) \<union> \<down> \<bottom> = \<Down> (\<Union> (range ` range step))"
  by (safe; clarsimp simp: in_down_iff down_image_iff down_sup_distrib) *)



lemma unit_closed_closed: "x \<le> unit_of y \<Longrightarrow> x \<le> unit_of x"
  oops
  sledgehammer
  oops
  by (metis (no_types, opaque_lifting) down_unit mono_f
             unit_of_apply dual_order.trans commute)


lemma [simp]: "\<down>(f \<bottom>  (step l x)) = \<down>\<bottom>"
  apply (safe; clarsimp simp: in_down_iff)
  by (metis bot_conj_step dual_order.trans commute)


lemma [simp]: "\<down>(f (step l x) \<bottom>  ) = \<down>\<bottom>"
  apply (safe; clarsimp simp: in_down_iff)
  by (metis bot_conj_step dual_order.trans commute)


lemma [simp]: "\<down>(f \<bottom>  (step l x ; c)) = \<down>\<bottom>"
  apply (safe; clarsimp simp: in_down_iff)
  by (meson dual_order.trans mono_f order_refl preorder_bot_class.bot_least sync_step_test)



lemma [simp]: "\<down>(f (step l x ; c) \<bottom>  ) = \<down>\<bottom>"
  apply (safe; clarsimp simp: in_down_iff)
  by (smt (z3) commute mono_f order_refl order_trans preorder_bot_class.bot_least sync_step_test)


lemma [simp]: "\<down>(f (test t) \<bottom>  ) = \<down>\<bottom>"
  apply (safe; clarsimp simp: in_down_iff)
  by (meson dual_order.trans mono_f order_refl
            preorder_bot_class.bot_least sync_step_test)


lemma [simp]: "\<down>(f  \<bottom>  (test t) ) = \<down>\<bottom>"
  apply (safe; clarsimp simp: in_down_iff)
  by (metis (no_types, opaque_lifting) commute dual_order.trans mono_f
             order_refl preorder_bot_class.bot_least sync_step_test)


lemma mono_on_sync[simp]:  "mono_on UNIV (f)"
  apply (rule mono_onI)
  by (meson le_funI mono_f order_refl)


lemma mono_on_sync'[simp]:  "mono_on UNIV (f x)"
  apply (rule mono_onI)
  by (meson le_funI mono_f order_refl)


lemma mono_on_sync''[simp]:  "mono_on UNIV (\<lambda>x. f x y)"
  apply (rule mono_onI)
  by (meson le_funI mono_f order_refl)


lemma mono_on_seq[simp]:  "mono_on UNIV (\<lambda>x.  x ; y)"
  apply (rule mono_onI)
  by (meson order_refl seq.mono_f)

lemma mono_on_seq'[simp]:  "mono_on UNIV (\<lambda>x.  y ; x)"
  apply (rule mono_onI)
  by (meson order_refl seq.mono_f)

lemma [simp]: "\<down>(f \<bottom> \<bottom>) = \<down>(\<bottom>)"
  apply (safe; clarsimp simp: in_down_iff)
  by (meson dual_order.trans mono_f preorder_bot_class.bot_least sync_step_test)


lemma conj_conv_atomic_bot: "convolute \<bottom> (seq.datomic q) = \<bottom>"
  apply (transfer)
  apply (clarsimp simp: mono_on_down mono_on_sup 
        mono_on_SUP mono_on_principle mono_on_down' commute)
  apply (safe; clarsimp simp: in_down_iff)
  apply (meson bot_conj_step commute in_omega le_bottom_bottom_le mono_f order_trans seq.test_step')
   apply (meson bot_le_unit_bot down_unit in_omega mono_f omega_mono order_refl)
  apply (clarsimp simp: Bex_def)
  apply (rule_tac x=x in exI, intro conjI, fastforce)
  apply (clarsimp)
  by (meson bot_idemp dual_order.trans le_bottom_bottom_le mono_f)


lemma nonempty_bot_union: "S \<noteq> {} \<Longrightarrow> \<Down> (S) \<union> \<Down> {\<bottom>} = \<Down>(S :: 'a :: preorder_bot set)"
  by (metis Un_empty_right Un_insert_right down_down
            down_union_distrib test_seq.insert_bot_nonempty
            seq.test_seq_axioms)


lemma nonempty_bot_union': "S \<noteq> {} \<Longrightarrow> \<Down> (S) \<union> \<down>\<bottom> = \<Down>(S :: 'a :: preorder_bot set)" 
  apply (safe; clarsimp simp: in_down_iff)
  apply (rule in_downsetI, clarsimp)
  apply (rule_tac x=x in bexI)
  using order_trans preorder_bot_class.bot_least apply blast
  using downset_set_def by blast

lemma le_test_seq_iff: "x \<le> test t ; c \<longleftrightarrow> (first x \<le> test t \<and> x \<le> c)"
  apply (safe)
  using seq.first_test apply blast
  oops
  sledgehammer
  oops
   apply (meson dual_order.trans seq.test_le')
  by (meson dual_order.trans seq.flip.unit_of_apply seq.mono_f)



(* lemma "Din x (seq.convolute (seq.dtest (t))  c) \<longleftrightarrow> (Din (first x) (seq.dtest t) \<and> Din x c) "
  apply (safe; transfer, clarsimp simp: in_down_iff)
    apply (elim disjE; clarsimp simp: in_Down_iff in_down_iff)
     apply (rule_tac x=xc in bexI; clarsimp?)
  
     apply (meson order_trans seq.aborting seq.first_test seq.mono_f)
    apply (metis bot_least_trans order_trans seq.aborting
                 seq.bot_annihilate_seq seq.flip.unit_of_unit seq.mono_f)
    apply (elim disjE; clarsimp simp: in_Down_iff in_down_iff)
    apply (meson dual_order.refl in_downsetI seq.flip.mono_f seq.test_le')
   apply (metis in_Down_iff seq.bot_annihilate_seq seq.mono_f)
  apply (elim disjE; (clarsimp simp: in_Down_iff down_image_iff)?)
   apply (meson down_image_iff seq.flip.unit_of_apply)
  using in_down_iff seq.flip.unit_of_apply by blast
*)

lemma seq_omega_closed:"x \<le> bottom y \<Longrightarrow> x ; z \<in> \<Omega>"
  by (meson in_omega order_trans seq.aborting seq.bot_annihilate_seq seq.mono_f)

lemma f_omega_closed: "x \<in> \<Omega> \<Longrightarrow> y \<in> \<Omega> \<Longrightarrow> f x y \<in> \<Omega>"
  by (meson bot_le_unit_bot down_unit in_omega ordered_semigroup_axioms ordered_semigroup_def refine_trans)

lemma conv_sync_test_step: "convolute seq.conv_test_pre.nil (seq.convolute (seq.datomic p) c) = \<bottom>"
  apply (clarsimp simp: seq.conv_test_pre.nil_def, transfer)
  apply  (clarsimp simp: mono_on_down  mono_on_SUP mono_on_principle mono_on_down'
                         conj.commute   )
  apply (safe; clarsimp simp: in_down_iff)
      apply (meson in_omega omega_mono sync_step_test)
     apply (frule_tac z=xc in seq_omega_closed)
     apply (clarsimp)
     apply (meson bot_conj_test in_omega omega_mono)
    apply (meson bot_conj_step commute in_omega omega_mono)
   apply (meson f_omega_closed in_omega omega_mono seq_omega_closed)
  apply (erule_tac x="bottom y" in ballE; clarsimp)
   apply (erule_tac x="bottom y" in ballE; clarsimp?)
  apply (erule_tac x="bottom y" in ballE; clarsimp?)
     apply (meson bot_idemp mono_f order_refl order_trans seq.flip.bot_idemp)
    apply (meson in_downsetI in_mono in_omega le_bottom_bottom_le)
   apply (meson order_refl)
  apply (meson order_refl)
  done

abbreviation (input) "aborting c \<equiv> f c (bottom c) \<notin> \<Omega>"

lemma f_bot_bot: "(f (y\<^sub>\<bottom>) (ya\<^sub>\<bottom>)) \<le> (f (y\<^sub>\<bottom>) (ya\<^sub>\<bottom>))\<^sub>\<bottom>  "
  by (metis bot_idemp f_omega_closed in_omega le_bottom_bottom_le order_trans preorder_bot_class.bot_least)

lemma bot_helper: " 
       x \<le> f (xa ; xb) (xc ; xd) \<Longrightarrow> xa \<le> (bottom y) \<Longrightarrow>
       xc \<le> bottom ya \<Longrightarrow>   x \<le> f (bottom y) (bottom ya) ; f (bottom y) (bottom ya )"
  apply (drule order_trans, rule mono_f, rule seq.mono_f, assumption, rule order_refl)
   apply (rule seq.mono_f, assumption, rule order_refl)
  apply (drule order_trans, rule mono_f) 
    apply (rule seq.bot_annihilate_seq)
    apply (rule seq.bot_annihilate_seq)

  apply (erule order_trans)
  apply (rule order_trans, rule f_bot_bot)
  apply (rule order_trans, rule seq.bot_idemp)
  by (simp add: seq.flip.mono_f)

thm seq_atomic_abort_sync[simplified]


  
lemma conv_sync_seq_step: "convolute (seq.convolute (seq.datomic q) d) (seq.convolute (seq.datomic p) c) \<le> seq.convolute (convolute (seq.datomic q) (seq.datomic p)) (convolute c d)"
  apply (case_tac "p = {}"; clarsimp?)
   apply (metis bot.extremum conj_conv_atomic_bot conv_sync.sync_commute conv_sync.sync_mono_right conv_sync_test_step seq.down_seq_distrib_right.seq_magic_left)
  apply (case_tac "q = {}"; clarsimp?)
  apply (metis bot.extremum conj_conv_atomic_bot conv_sync.sync_mono_left conv_sync_test_step seq.down_seq_distrib_right.seq_magic_left)

  apply (clarsimp simp: less_eq_downset_def, transfer)
  apply  (clarsimp simp: mono_on_down  mono_on_SUP mono_on_principle mono_on_down'
                         conj.commute  )
  apply (safe; clarsimp simp: in_down_iff)
     apply (drule order_trans, rule seq_bot_sync)
      apply auto[1]
     apply (erule_tac x="bottom y" in ballE; clarsimp)
      apply (erule_tac x="(ad, ae, bb)" in ballE; clarsimp)
      apply (erule_tac x="xc" in ballE; clarsimp?) back
  apply (erule_tac x="xb" in ballE; clarsimp?) back
      apply (meson commute dual_order.trans mono_f order_refl seq.flip.mono_f)
     apply (blast)
    apply (erule_tac x="bottom y" in ballE, clarsimp)
     apply (erule_tac x="bottom ya" in ballE)
    apply (erule_tac x="bottom y" in ballE)
       apply (erule_tac x="bottom ya" in ballE)
  using bot_helper 
        apply force
       apply (metis IntD2 in_omega inf.orderE order_refl)
  apply (metis IntD2 in_omega inf.orderE order_refl)
  apply (metis IntD2 in_omega inf.orderE order_refl)
  apply (metis IntD2 in_omega inf.orderE order_refl)
   apply (rule_tac x="(ad, ae, bb)" in bexI; clarsimp) 
   apply (rule_tac x="(af, ag, bc)" in bexI; clarsimp)
   apply (case_tac "\<not>aborting xa \<and> \<not>aborting xb", elim conjE)
  apply (drule order_trans, rule seq_atomic_nonaborting_sync, blast, blast)
    apply (meson commute dual_order.trans seq.flip.mono_f)
   apply (simp)
   apply (elim disjE)
    apply (drule_tac l=ad and s="(ae, bb)" and l'=af and s'="(ag, bc)" and y= xa and b = xb in seq_atomic_abort_sync[simplified])
    apply (elim disjE)
     apply (drule order_trans, assumption)
  apply (rule_tac x="bottom xa" in bexI, rule_tac x="xa" in bexI)
      apply (meson ab_ordered_semigroup.commute ab_ordered_semigroup_axioms ordered_semigroup.mono_f refine_trans seq.ordered_semigroup_axioms)
     apply (assumption)
     apply (meson in_mono in_omega order_refl)
 apply (drule order_trans, assumption)
  apply (rule_tac x=" xb" in bexI, rule_tac x="bottom xb" in bexI)
      apply (meson ab_ordered_semigroup.commute ab_ordered_semigroup_axioms ordered_semigroup.mono_f refine_trans seq.ordered_semigroup_axioms)
     apply (meson in_mono in_omega order_refl)
    apply (assumption)
   apply (drule_tac l'=ad and s'="(ae, bb)" and l=af and s="(ag, bc)" and y= xb and b = xa in seq_atomic_abort_sync[simplified])
   apply (elim disjE)
    apply (drule order_trans, rule order_trans, rule commute, assumption) 

    apply (rule_tac x=" xb" in bexI, rule_tac x="bottom xb" in bexI)
      apply (erule order_trans) 
      apply (metis commute order_refl seq.mono_f)
  apply (metis in_omega preorder_bot_class.bot_least seq.aborting subset_eq)
    apply (meson ab_ordered_semigroup.commute ab_ordered_semigroup_axioms ordered_semigroup.mono_f refine_trans seq.ordered_semigroup_axioms)
  defer
     apply (drule order_trans, rule seq_bot_sync')
   apply auto[1]
  apply (rule_tac x="(ad, ae, bb)" in bexI)
   apply (rule disjI2)
  apply (rule_tac x="bottom y" in bexI; clarsimp)
      apply (meson commute dual_order.trans mono_f order_refl seq.flip.mono_f)
    apply (blast)+
  apply (rule_tac x="bottom xa" in bexI, rule_tac x=xa in bexI)
    apply (meson commute order_trans seq.mono_f)
   apply fastforce
  apply (metis in_omega preorder_bot_class.bot_least seq.aborting subset_eq)
  done

definition "merge c c' \<equiv> f (step (fst c) (snd c)) ( step (fst c') (snd c'))"



lemma convolute_step_convolute: "convolute (seq.datomic P) (seq.datomic Q) = 
      seq.datomic (\<Squnion>p\<in>P. \<Squnion>q\<in>Q. {c. step (fst c) (snd c) \<le> merge p q})"
  apply (case_tac "P = {}"; case_tac "Q = {}"; clarsimp?)
     apply (metis conj_conv_atomic_bot seq.step_atomic.atomic.hom_bot)
    apply (metis conj_conv_atomic_bot)
  using conj_conv_atomic_bot conv_sync.sync_commute apply auto[1]
  apply (rule antisym)
  apply (subst less_eq_downset_def)
  apply (transfer)
  (*  apply  (clarsimp simp: mono_on_down  mono_on_SUP mono_on_principle 
                         mono_on_down' commute nonempty_bot_union' nonempty_bot_union ) *)
   apply (clarsimp simp: in_down_iff down_image_iff merge_def)
   apply (intro conjI; clarsimp simp: in_Down_iff)
    apply (elim disjE; clarsimp simp: down_image_iff in_down_iff)
     apply (subgoal_tac "x \<le> f (step a (aa, b)) (step ab (ac, ba))")
      apply (drule conv_merge_step)
      apply (clarsimp)
  
      apply fastforce
     apply (meson mono_f order_trans)
    apply (meson bot_conj_step in_omega mono_f omega_mono order_refl seq.test_step')
   apply (elim disjE; clarsimp simp: down_image_iff in_down_iff)
    apply (meson bot_conj_step commute dual_order.trans in_omega mono_f order_eq_refl seq.test_step')
  apply (meson f_omega_closed in_omega omega_mono)
 apply (subst less_eq_downset_def)
  apply (transfer)
  apply (clarsimp)
  apply (intro conjI)
   apply (clarsimp simp:)
   apply (clarsimp simp: down_image_iff in_down_iff merge_def Bex_def)
   apply (meson dual_order.trans order_refl)
  apply (clarsimp)
   apply (clarsimp simp: down_image_iff in_down_iff merge_def Bex_def)
  by (meson bot_idemp dual_order.trans in_omega le_bottom_bottom_le)
  

end

locale cra_atomic_sync = conj_par + par_sync: sync_atomic_elem par to_env + conj_sync: sync_atomic_elem conj unit_of



locale cra_atomic_elem = cra_elem + seq_atomic +  cra_atomic_sync + 

  assumes to_env_step: "to_env (step l s ; c) = (step Env s ; to_env c)"
  assumes par_steps: "par (step l s) (step Env s) \<ge> step l s" and
          par_steps': "par (step l s) (step Env s) \<le> step l s" and
(*
  par_sync: " x \<le> step l s \<parallel> step l' s' \<Longrightarrow> \<not> (x \<le> \<bottom>) \<Longrightarrow> (l = Env \<or> l' = Env) \<and> s = s'" and

  step_unit: " (step l s) \<le> unit_of (step l s)" and
  sync_steps: "conj (step l s) (step l' s') \<le> step l s" and *)

  no_pgm_env: "x \<le> step Pgm s ; c \<Longrightarrow> x \<le> step Env s' ; d \<Longrightarrow> x \<in> \<Omega>" 


begin


lemma mono_seq[simp]: "mono_on UNIV (;) "
  apply (intro mono_onI)
  by (simp add: le_fun_def cs.seq.mono_f)


lemma mono_seq'[simp]: "mono_on UNIV (seq c)"
  apply (intro mono_onI)
  by (simp add: le_fun_def cs.seq.mono_f)


lemma mono_conj[simp]: "mono_on UNIV (conj)"
  apply (intro mono_onI)
  by (simp add: le_fun_def conj.mono_f)


lemma mono_conj'[simp]: "mono_on UNIV (conj c)"
  apply (intro mono_onI)
  by (simp add: le_fun_def conj.mono_f)


lemma mono_conj''[simp]: "mono_on UNIV (\<lambda>x. conj x c)"
  apply (intro mono_onI)
  by (simp add: le_fun_def conj.mono_f)


sublocale down_iteration_infinite_distrib: iteration_infinite_distrib cs.seq.convolute cs.seq.dnil ..

sublocale down_seq_distrib_right: seq_distrib_right cs.seq.convolute cs.seq.dnil ..



inductive finite_obs :: "labels set \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool"
  where
    testI [simp, intro!]: "finite_obs l 0 (test t)"
  | stepI [simp, intro!]: "finite_obs ls n A \<Longrightarrow>
    first A \<le> test (snd s) \<Longrightarrow> l \<in> ls \<Longrightarrow> finite_obs ls (Suc n) (step l s ; A)"


definition "not_environment c \<equiv> \<forall>s d t. \<not> (step Env s ; d \<ge> c) \<and> \<not> (test t \<ge> c) " 


end


locale cra_atomic_iter = cra_atomic_elem +
 assumes command_split:  " x \<le> unit_of y \<Longrightarrow>
        y \<in> \<Omega> \<or> (\<exists>t. x \<le> test t) \<or> (\<exists>l s x'. x <= step l s; x' \<and>  x' \<le> unit_of x' \<and> (l = Pgm \<or> l = Env) )"
 assumes command_split_env:  " x \<le> to_env y \<Longrightarrow>
        y \<in> \<Omega> \<or> (\<exists>t. x \<le> test t) \<or> (\<exists> s x'. x <= step Env s; x' \<and>  x' \<le> to_env x'  )"
 assumes aborting_when: "(\<And>x. \<not> x \<le> unit_of x \<Longrightarrow> 
     \<exists>a y b n. finite_obs {Pgm, Env} n a \<and> conj y (bottom y) \<notin> \<Omega> \<and> first y \<le> last a \<and> x \<ge> a ; y ; b)" 
assumes aborting_when': "\<not> x \<le> to_env x \<Longrightarrow> 
     \<exists>a y b n. finite_obs {Env} n a \<and> not_environment y \<and> first y \<le> last a \<and> x \<ge> a ; y ; b" 
begin

lemma unit_closed_closed: "x \<le> unit_of y \<Longrightarrow> x \<le> unit_of x"
  sorry
  oops
  by (metis (no_types, opaque_lifting) conj.down_unit conj.mono_f
             conj.unit_of_apply dual_order.trans local.conj.commute)

lift_definition llp :: " 'a downset \<Rightarrow> 'a downset" is "\<lambda>S. \<Down>(unit_of ` S)"
  apply (intro conjI)
  apply (rule set_eqI)
   apply (clarsimp simp:down_image_iff)
  apply (safe)
  apply (clarsimp simp: down_image_iff)
  apply (rule_tac x="bottom y" in bexI; clarsimp?)
  using conj.bot_le_unit_bot dual_order.trans apply blast
  using in_omega by blast

lemma "x \<in> \<Omega> \<Longrightarrow> unit_of x \<in> \<Omega>"
  apply (clarsimp)
  sledgehammer
  oops

lemma iter_conj_dunit: "seq_elem_fiter.iter step_atomic.Atomic \<ge> conj.dunit"
  apply (rule seq_elem_fiter.iter_induct_nil)
  defer
  apply (clarsimp simp: sup_downset_def gfp_def less_eq_downset_def cs.seq.conv_test_pre.nil_def step_atomic.Atomic_def)
   apply (transfer)
  apply (clarsimp simp: down_sup_distrib down_union_distrib down_image_iff in_down_iff)
   apply (erule contrapos_pp) back
  apply (clarsimp)
   apply (frule command_split)
  apply (erule disjE; clarsimp?)
  sledgehammer
  oops
  sledgehammer
  apply (erule_tac x="step l (a, b)" in ballE)
   apply (meson UNIV_I down_image_iff)
  apply (clarsimp simp: down_image_iff)
  apply (rule_tac x="step l (a, b)" in bexI)
   apply (meson UNIV_I down_image_iff)
  apply (clarsimp simp: down_image_iff)
  by (blast)


lift_definition datomic_l :: "labels set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow>   'a downset"  is "\<lambda>l S. \<Down>(\<Union>f\<in>(step ` l). f ` S) \<union> \<Omega> "
  by (clarsimp simp: down_sup_distrib down_union_distrib)

lemma iter_par_dunit: "seq_elem_fiter.iter (datomic_l {Env} UNIV) \<ge> par.dunit"
  apply (rule seq_elem_fiter.iter_induct_nil)
  defer
  apply (clarsimp simp: sup_downset_def gfp_def less_eq_downset_def cs.seq.conv_test_pre.nil_def step_atomic.Atomic_def)
   apply (transfer)
   apply (clarsimp)
  apply (clarsimp simp: down_sup_distrib down_union_distrib down_image_iff in_down_iff)
   apply (erule contrapos_pp) back
  apply (clarsimp)
apply (frule command_split_env)
  apply (erule disjE; clarsimp?)
  apply (erule_tac x="step Env (a, b)" in ballE)
  apply (meson UNIV_I down_image_iff)
  by (metis order_refl range_eqI sp.in_Down_iff)


lemma llp_distrib: "llp (c \<squnion> d) = llp c \<squnion> llp d"
  apply (clarsimp simp: sup_downset_def gfp_def 
        less_eq_downset_def cs.seq.conv_test_pre.nil_def
        step_atomic.Atomic_def, transfer, clarsimp)
  by (simp add: down_union_distrib image_Un)





inductive finite_env_obs :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  where
    testI [simp, intro!]: "finite_env_obs 0 (test t)"
  | estepI [simp, intro!]: "finite_env_obs n A \<Longrightarrow> first A \<le> test (snd s)
                            \<Longrightarrow> finite_env_obs (Suc n) (step Env s ; A)"



notation cs.seq.convolute (infixl \<open>\<Zsemi>\<close> 60 )

lemma in_left: "c \<le> a \<squnion> b \<Longrightarrow> c \<sqinter> b \<le> \<bottom> \<Longrightarrow> c \<le> (a :: 'd :: refinement_lattice)"
  by (simp add: inf.absorb_iff2 inf_commute inf_sup_distrib1)

lemma step_test_last: "step l' (x, y) ; test y \<ge> step l' (x, y)"
  by(rule test_step')


  by (meson cs.seq.unit_of_unit order_eq_refl step_last)

(* lemma le_step_ge_nonterm_step:"b \<le> step l s \<Longrightarrow> b \<le> \<bottom> \<or> step l s ; \<bottom> \<le> b"
  apply (drule order_trans[where z="step l s ; test (snd s)"])
   apply (metis cs.seq.unit_of_unit last_step old.prod.exhaust order_eq_refl snd_conv)
  apply (clarsimp)
  apply (frule step_meet_seq[rotated 2], assumption, rule order_refl, rule order_refl)
  apply (clarsimp)
  apply (cases s, clarsimp)
  apply (frule step_atomic)
  apply (elim disjE; clarsimp?)
    apply (meson cs.seq.bot_annihilate_seq cs.seq.mono_f dual_order.trans)
   apply (frule_tac b="step l (a, ba)" and d="\<bottom>" in step_meet_seq[rotated 2])
      apply (meson cs.seq.le_test cs.seq.mono_f dual_order.trans)
     apply (rule order_refl)+
   apply (clarsimp)
  oops
*)
lemma step_bot_mono: "a \<le> b \<Longrightarrow> a ; bottom d \<le> b ; c " sorry


lemma prime_seq:  " prime (step l (a, b) ; A) = (prime (step l (a, b))) \<Zsemi> prime A" 
  apply (transfer, intro set_eqI iffI; clarsimp)
   apply (clarsimp simp: in_down_iff)
   apply (rule_tac x="step l (a, b) " in bexI; clarsimp?)
   apply (rule_tac x="A " in bexI; clarsimp?)
  apply (metis cs.seq.last_unit in_omega last_omega_closed)
  apply (clarsimp simp: in_down_iff)
  apply (elim disjE; clarsimp simp: in_down_iff)
  apply (elim disjE; clarsimp simp: in_down_iff)
    apply (meson cs.seq.flip.mono_f dual_order.trans)
   apply (frule step_atomic)
   apply (elim disjE; clarsimp?)
     apply (meson in_omega omega_mono par_sync.seq_omega_closed)
  apply (subgoal_tac "x \<le> step l (a, b) ; (bottom (test b))")
     apply (meson dual_order.trans order_refl step_bot_mono)
    apply (meson cs.seq.flip.mono_f order_trans step_bot_mono)
   apply (meson cs.seq.mono_f dual_order.trans step_bot_mono)
  apply (elim disjE; clarsimp)
   apply (meson in_omega omega_mono par_sync.seq_omega_closed)
  by (meson in_omega omega_mono par_sync.seq_omega_closed)

find_theorems "?y \<le> ?y ; last ?y"

lemma last_bot_trans:"x \<le> y ; z \<Longrightarrow> last y \<le> bottom b \<Longrightarrow> x \<le> y ; bottom b"
  apply (drule order_trans)
   apply (rule cs.seq.mono_f)
    apply (rule cs.seq.last_unit, rule order_refl)
 apply (drule order_trans) back
   apply (rule cs.seq.mono_f)
   apply (rule cs.seq.mono_f)
     apply (rule order_refl, assumption, rule order_refl)
  by (meson cs.seq.bot_annihilate_seq cs.seq.flip.assoc cs.seq.mono_f dual_order.trans order_refl)
  

lemma conj_upper: "x \<le> a \<Longrightarrow> x \<le> b \<Longrightarrow> x \<le> conj a b"
  by (meson conj.idemp conj.mono_f dual_order.trans)

abbreviation (input) "aborting c \<equiv> conj c (bottom c) \<notin> \<Omega>"

lemma conj_step_idemp: "conj (step l s) (step l s) \<le> step l s"
  by (meson conj.covering conj.idemp dual_order.trans in_omega order_refl step_not_le_bot)

lemma inf_exchange: "x \<le> step l s ; c \<Longrightarrow> x \<le> step l s ; d \<Longrightarrow> \<exists>y. (y \<in> \<Omega> \<or> (y \<le> c \<and> y \<le> d)) \<and> x \<le> step l s; y" sorry

lemma atomic_inf: "(step_atomic.Atomic \<Zsemi> b) \<sqinter> (step_atomic.Atomic \<Zsemi> c) = (step_atomic.Atomic \<Zsemi> (b \<sqinter> c))"
  apply (rule antisym, clarsimp simp: less_eq_downset_def inf_downset_def step_atomic.Atomic_def)
   apply (transfer)
   apply (clarsimp simp: in_down_iff)
   apply (elim disjE; clarsimp simp: down_sup_distrib down_union_distrib down_image_iff)
      apply (frule_tac a=xa and b=xb and c=xc and d=xd in step_meet_seq[rotated 2]; assumption?, clarsimp?)
      apply (subgoal_tac "y \<le> step a (ab, ba)")
       apply (subgoal_tac "y \<le> step aa (ac, bb)")
        apply (drule  (1) step_meet')
        apply (elim disjE; clarsimp)
         apply (rule_tac x="step a (ab, ba)" in bexI)
          apply (subgoal_tac "x \<le> y ; (bottom ya)")
  apply (rule_tac x="bottom ya" in bexI)
            apply (meson dual_order.trans step_bot_mono)
           apply (metis Int_iff in_downsetI in_mono in_omega le_bottom_bottom_le)
          apply (erule (1) last_bot_trans)
         apply (fastforce simp: down_image_iff)
        defer

        apply (metis dual_order.trans)
       apply (metis dual_order.trans)
  apply (metis Int_iff cs.seq.last_unit dual_order.trans in_omega inf.absorb_iff1 last_omega_closed par_sync.seq_omega_closed)
  apply (metis Int_iff cs.seq.last_unit dual_order.trans in_omega inf.absorb_iff1 last_omega_closed par_sync.seq_omega_closed)
  apply (metis Int_iff cs.seq.last_unit dual_order.trans in_omega inf.absorb_iff1 last_omega_closed par_sync.seq_omega_closed)

  apply (clarsimp simp:  less_eq_downset_def inf_downset_def step_atomic.Atomic_def)
  apply (transfer)
  apply (clarsimp, intro conjI; clarsimp simp: down_sup_distrib down_union_distrib)
   apply (meson rangeI sp.in_Down_iff)
   apply (meson rangeI sp.in_Down_iff)
  apply (rule_tac x="step aa (ab, ba)" in bexI; clarsimp?)
   apply (subgoal_tac "x \<le> (step aa (ab, ba) ; xc) \<and> x \<le> (step aa (ab, ba) ; xd)")
    apply (elim conjE)
    apply (drule (1) inf_exchange)
    apply (clarsimp)
    apply (rule_tac x=ya in bexI)
     apply blast
    apply (metis IntI in_mono in_omega sp.in_Down_iff)
   apply (meson cs.seq.flip.mono_f dual_order.trans order_refl)
  apply (fastforce simp: down_image_iff)
  done


lemma atomic_inf': "(datomic A \<Zsemi> b) \<sqinter> (datomic B \<Zsemi> c) = (datomic (A \<sqinter> B) \<Zsemi> (b \<sqinter> c))"
  sorry
  apply (rule antisym, clarsimp simp: less_eq_downset_def inf_downset_def step_atomic.Atomic_def)
   apply (transfer)
   apply (clarsimp simp: in_down_iff)
   apply (elim disjE; clarsimp simp: down_sup_distrib down_union_distrib down_image_iff)
         apply (frule_tac a=xa and b=xb and c=xc and d=xd in step_meet_seq[rotated 2]; assumption?, clarsimp?)
      apply (rule_tac x=y in bexI, rule_tac x=y' in bexI)
  oops
           apply (clarsimp)
          apply (meson IntI in_downsetI)
      apply (clarsimp simp: down_union_distrib down_image_iff )
  apply (smt (z3) dual_order.trans fst_conv snd_conv)
      apply (clarsimp simp: down_union_distrib down_image_iff in_down_iff)

  

  apply (frule_tac a=xa and b=xb and c=xc and d=xd in step_meet_seq[rotated 2]; assumption?, clarsimp?)
      apply (rule_tac x=y in bexI, rule_tac x=y' in bexI)
  apply (clarsimp)
       apply (meson IntI in_downsetI)
      apply (clarsimp simp: down_union_distrib down_image_iff )
     apply (meson dual_order.trans in_down_iff)

  apply (frule_tac a=xa and b=xb and c=xc and d=xd in step_meet_seq[rotated 2]; assumption?, clarsimp?)
   apply (clarsimp simp: down_union_distrib down_image_iff in_down_iff)
    apply (smt (z3) IntI UnCI cs.seq.mono_f dual_order.refl order_trans in_down_iff cs.seq.down_bot_seq_bot)
   apply (clarsimp simp: down_union_distrib down_image_iff in_down_iff)
  apply (subgoal_tac "x \<le> \<bottom>")

    apply (meson IntI UnCI bot_least_trans in_down_iff)
  apply (meson cs.seq.aborting cs.seq.bot_annihilate_seq cs.seq.flip.mono_f order_trans)
  by (simp add: cs.seq.down_seq_distrib_right.seq_mono)



lemma step_matching_labels: "x \<le> step l s \<Longrightarrow> x \<le> step l' s \<Longrightarrow> x \<in> \<Omega> \<or> l = l'"
  apply (case_tac l; case_tac l'; clarsimp?)
   apply (meson cs.seq.last_unit dual_order.trans in_omega no_pgm_env)
  apply (meson cs.seq.last_unit dual_order.trans in_omega no_pgm_env)

  done

lemma atomic_inf_l: "(datomic_l l A \<Zsemi> b) \<sqinter> (datomic_l l' B \<Zsemi> c) = (datomic_l (l \<sqinter> l') (A \<sqinter> B) \<Zsemi> (b \<sqinter> c))"
  sorry
  apply (rule antisym, clarsimp simp: less_eq_downset_def inf_downset_def step_atomic.Atomic_def)
   apply (transfer)
   apply (clarsimp simp: in_down_iff)
   apply (case_tac "x \<le> \<bottom>")
  apply (metis IntI in_down_iff sp.le_bot_le_any)
   apply (elim disjE; clarsimp simp: down_sup_distrib down_union_distrib down_image_iff)

      apply (frule_tac a=xa and b=xb and c=xc and d=xd in step_meet_seq[rotated 2]; assumption?, clarsimp?)
  apply (subgoal_tac "y = ya", clarsimp)

      apply (rule_tac x=ya in bexI, rule_tac x=yb in bexI; clarsimp?)
          apply (meson IntI in_downsetI)
         apply (clarsimp simp: down_union_distrib down_image_iff )
       apply (smt (z3) IntI dual_order.trans in_down_iff in_downsetI step_meet)
  apply (smt (z3) IntI dual_order.trans in_down_iff in_downsetI step_matching_labels step_meet)
         apply (clarsimp simp: down_union_distrib down_image_iff in_down_iff )
     apply (metis IntI cs.seq.flip.mono_f dual_order.trans par.aborting in_down_iff cs.seq.down_bot_seq_bot sp.le_bot_le_any)
  apply (metis IntI cs.seq.flip.mono_f dual_order.trans par.aborting in_down_iff cs.seq.down_bot_seq_bot sp.le_bot_le_any)
   apply (metis IntI cs.seq.flip.mono_f dual_order.trans par.aborting in_down_iff cs.seq.down_bot_seq_bot sp.le_bot_le_any)
  apply (clarsimp, intro conjI)
   apply (rule  cs.seq.down_seq_distrib_right.seq_mono)
    apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: down_image_iff in_Down_iff)
  apply blast
  apply (clarsimp)
   apply (rule  cs.seq.down_seq_distrib_right.seq_mono)
   apply (clarsimp simp: less_eq_downset_def, transfer)
    apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: down_image_iff in_Down_iff)
  using IntD1 image_is_empty down_image_iff apply fastforce
  by (simp add: cs.seq.down_seq_distrib_right.seq_mono)

 
  
lemma prime_datomic_l: "prime (step l s) = datomic_l {l} {s}"
  apply (transfer)
  by (clarsimp)

lemma step_atomic_split: "step_atomic.Atomic = datomic_l {Pgm} UNIV \<squnion> datomic_l {Env} UNIV"
  apply (clarsimp simp: step_atomic.Atomic_def sup_downset_def)
  apply (transfer)
  by (safe; clarsimp simp: down_image_iff in_down_iff; metis labels.exhaust)


lemma datomic_inf_pgm_env: "((datomic_l {Pgm} P \<Zsemi> A) \<sqinter> (datomic_l {Env} Q \<Zsemi> B)) = \<bottom>"
  apply (subst atomic_inf_l, clarsimp)
  apply (clarsimp simp: inf_downset_def, transfer)
  apply (clarsimp)
  apply (safe; clarsimp simp: in_down_iff)
   apply (meson in_omega omega_mono par_sync.seq_omega_closed)
  by (metis Int_iff cs.seq.last_unit in_omega inf.order_iff last_omega_closed)
  oops
  apply (clarsimp simp: inf_downset_def, transfer)
  apply (safe; clarsimp simp: in_down_iff down_image_iff)
       apply (meson cs.seq.mono_f no_pgm_env order_eq_refl refine_trans)
      apply (meson cs.seq.aborting cs.seq.bot_annihilate_seq cs.seq.flip.mono_f dual_order.trans)
  apply (meson cs.seq.aborting cs.seq.bot_annihilate_seq cs.seq.flip.mono_f dual_order.trans)
    apply (meson cs.seq.aborting cs.seq.bot_annihilate_seq cs.seq.flip.mono_f dual_order.trans) 
   apply blast
  apply blast
  done

lemma finite_is_finite: "finite_obs l i x \<Longrightarrow>  cs.seq.conv_test.seq_power (datomic_l l UNIV) i \<sqinter> prime (x) = prime (x)"
  apply (induct x rule: finite_obs.induct)
  apply (clarsimp)
   apply (clarsimp simp: cs.seq.conv_test_pre.nil_def)
   defer
   apply (clarsimp)
   apply (clarsimp simp: prime_seq)
   apply (clarsimp simp: prime_datomic_l)
  apply (clarsimp simp: atomic_inf_l)
  apply (clarsimp simp: inf_downset_def, transfer, clarsimp)
  by (safe; clarsimp simp: in_down_iff down_image_iff, blast)
  
  


lemma eq_length:  "(cs.seq.conv_test.seq_power (datomic_l l A) i  \<Zsemi> c) \<sqinter> (cs.seq.conv_test.seq_power (datomic_l l' B) i \<Zsemi> d) = 
       cs.seq.conv_test.seq_power (datomic_l (l \<sqinter> l') (A \<sqinter> B)) i  \<Zsemi> (c \<sqinter> d) "
  apply (induct i; clarsimp)
  using atomic_inf_l cs.seq.downset_seq_distrib_left.seq_assoc by presburger

lemma seq_power_split: "z = x + y \<Longrightarrow> cs.seq.conv_test.seq_power c z = 
   (cs.seq.conv_test.seq_power c x \<Zsemi>  cs.seq.conv_test.seq_power c y)"
  apply (induct x arbitrary: y z; clarsimp)
  by (clarsimp simp: cs.seq.conv_semi.assoc)

lemma nat_lessD:"a < (b :: nat) \<Longrightarrow> b = a + (b - a)"
  by force


lemma test_atomic_bot:"(datomic_l l B \<Zsemi> d) \<sqinter> prime (test t) = \<bottom>"
  apply (clarsimp simp: inf_downset_def step_atomic.Atomic_def, transfer, safe; clarsimp simp: in_down_iff down_union_distrib down_image_iff in_Down_iff)
    apply (subgoal_tac "x \<le> conj (test t) ((step y (aa, ba)); b)")
  apply (insert conj_sync.sync_step_test, clarsimp)[1]
     apply (meson in_omega omega_mono)
    apply (meson conj_upper cs.seq.flip.mono_f dual_order.trans order_refl)
   apply (meson in_omega omega_mono par_sync.seq_omega_closed)
  by (meson cs.seq.last_unit in_omega last_omega_closed subset_iff)


lemma seq_power_test: "cs.seq.conv_test.seq_power (datomic_l l B) i \<sqinter> prime (test t) = prime (test t) \<Longrightarrow> i = 0"
  apply (induct i; clarsimp)
  apply (clarsimp simp: test_atomic_bot)
  apply (transfer)
  apply (clarsimp simp: set_eq_iff)
  apply (erule_tac x="test t" in allE)
  apply (clarsimp simp: in_down_iff)
  by (metis omega_mono par_sync.seq_omega_closed step_not_bot test_step)


lemma atomic_sync_step: "l \<in> ls \<Longrightarrow> (a, b) \<in> S \<Longrightarrow>  (datomic_l ls S \<Zsemi> c) \<sqinter> (prime (step l (a, b)) \<Zsemi> d) = prime (step l (a, b)) \<Zsemi> (c \<sqinter> d)"
   apply (clarsimp simp: prime_datomic_l)
  using atomic_inf_l conv_cra_test.inf.nondet_sync_distrib conv_cra_test.inf.sync_commute datomic_inf_pgm_env by auto


lemma atomic_sync_env_step: "(step_atomic.Atomic \<Zsemi> c) \<sqinter> (prime (step Env (a, b)) \<Zsemi> d) = prime (step Env (a, b)) \<Zsemi> (c \<sqinter> d)"
   apply (clarsimp simp: prime_datomic_l)
   apply (subst step_atomic_split)
  apply (subst cs.seq.conv_test.nondet_seq_distrib)
  using atomic_sync_step conv_cra_test.inf.nondet_sync_distrib datomic_inf_pgm_env prime_datomic_l by auto



lemma prime_test_is_dtest: "prime (test t) = cs.seq.dtest {t}"
  by (transfer, safe; clarsimp simp: in_down_iff)


lemma finite_obs_sync: "finite_obs l i c \<Longrightarrow> 
       (cs.seq.conv_test.seq_power (datomic_l l UNIV) i \<Zsemi> x) \<sqinter> (prime c \<Zsemi> y) \<le> (prime c) \<Zsemi> (x \<sqinter> y) "
  apply (induct c arbitrary:  rule: finite_obs.inducts; clarsimp?) 
   defer
  using atomic_sync_step cs.seq.downset_seq_distrib_left.seq_assoc
        cs.seq.downset_seq_distrib_left.seq_mono_right prime_seq 
  using conv_cra_test.inf.sync_commute cs.seq.conv_test.test_inf_interchange2 
   apply (smt (verit) UNIV_I)
  using conv_cra_test.inf.sync_commute cs.seq.conv_test.test_inf_interchange2 prime_test_is_dtest by auto


lemma finite_obs_zero_iff: "finite_obs ls 0 y \<longleftrightarrow> (\<exists>t. y = test t)"
  apply (safe)
  apply (erule finite_obs.cases; clarsimp)
  by (fastforce)


lemma first_step_seq: "first (step l s) \<ge> first (step l s ; c)"
  by (meson cs.seq.assoc' cs.seq.flip.mono_f dual_order.trans order_refl sp.first_le_first_iff)

lift_definition First :: " 'a downset \<Rightarrow> 'a downset"  is "\<lambda>S. \<Down>(first ` (S - \<Omega>)) \<union> \<Omega> "
  apply (clarsimp simp: down_sup_distrib down_union_distrib)
  done
  apply ( clarsimp simp: image_iff down_image_iff)
  by (meson cs.bottom_seq_omega cs.seq.flip.bot_idemp cs.seq.flip.bot_le_unit_bot dual_order.trans in_mono omega_mono)


lemma first_seq: "first (y ; y') \<le> first y"
  by (meson cs.seq.flip.assoc cs.seq.flip.mono_f order_refl order_trans sp.first_le_first_iff)

lemma test_lower_bound: "x \<notin> \<Omega> \<Longrightarrow> x \<le> test t \<Longrightarrow> x \<le> test t' \<Longrightarrow> t = t'"
  by (meson cs.seq.test_atom cs.seq.test_le dual_order.trans in_omega)
  oops

  find_theorems "_ - _" \<Down>

  
  

lemma First_test_seq: "First (prime (test t) \<Zsemi> c) \<le> (prime (test t))"
  apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: down_image_iff  in_Down_iff in_down_iff)
  
  apply (elim disjE; clarsimp simp: in_down_iff)
   apply (meson cs.seq.first_le cs.seq.first_test cs.seq.test_seq_test first_seq order_trans)
  by (meson in_omega omega_mono par_sync.seq_omega_closed)
 
  

lemma prime_test_le: "prime (test b) \<le> prime (test t) \<Longrightarrow> b = t"
  apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: down_image_iff in_down_iff)
  apply (subgoal_tac "test b \<le> test t")
   apply (simp add: cs.seq.test_le)
  by (metis (full_types) DiffD2 Un_iff cs.seq.test_nil in_down_iff in_mono order_refl rangeI)


lemma first_test_chain: " First (prime A) \<le> prime (test t) \<Longrightarrow> test b \<le> first A \<Longrightarrow> A \<notin> \<Omega> \<Longrightarrow> prime (test b) \<le> prime (test t)"
  apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: down_image_iff in_down_iff)
  apply (clarsimp simp: subset_iff in_Down_iff)
  apply (frule cs.seq.test_atom)
  apply (elim disjE; clarsimp?)
  apply (erule_tac x=x in allE)
  apply (drule mp)
   apply (rule_tac x=A in bexI)
    apply (metis order_trans)
   apply simp
  by (elim disjE; clarsimp simp: in_down_iff)

lemma omega_seq_simp[simp]: "\<Omega> \<subseteq> c \<Longrightarrow> (\<Union>x\<in>\<Omega>. \<Union>b\<in>c. \<down> (x ; b)) = \<Omega>"
  apply (safe; clarsimp simp: in_down_iff)
   apply (meson in_omega omega_mono par_sync.seq_omega_closed)
  apply (rule_tac x="bottom y" in bexI; clarsimp?)
  apply (rule_tac x="bottom y" in bexI; clarsimp?)
  using cs.seq.flip.bot_idemp dual_order.trans apply blast
   apply force
  by blast

lemma not_step_omega: "\<not>(step l s ; c) \<in> \<Omega>"
  apply (clarsimp)
  sorry

lemma first_prime_step_eq: 
 "First (prime (step la (a, ba) ; Aa) \<Zsemi> c) = prime (test a)"
  apply (transfer; clarsimp)
  apply (safe)
   apply (clarsimp simp: in_Down_iff in_down_iff)
   apply (meson cs.seq.first_le first_seq first_step order_trans)
   apply (clarsimp simp: in_Down_iff in_down_iff)
  apply (rule_tac x="step la (a, ba) ; Aa ; bottom Aa" in bexI; clarsimp?)
   apply (meson cs.seq.assoc cs.seq.first_le dual_order.trans first_step')
  apply (intro conjI)
   apply (rule disjI1)
   apply (rule_tac x="step la (a, ba) ; Aa " in bexI; clarsimp?)
   apply (rule_tac x="bottom Aa" in bexI; clarsimp)
   apply fastforce
  apply (clarsimp)
  by (meson cs.seq.assoc in_omega not_step_omega refine_trans)

lemma first_test_prime: "A \<notin> \<Omega> \<Longrightarrow> First (prime A) = prime (test t) \<Longrightarrow> test t \<le> first A "
  apply (transfer; clarsimp simp: down_image_iff)
  apply (clarsimp simp: set_eq_iff in_down_iff in_Down_iff Bex_def)
  apply (erule_tac x="test t" in allE) back
  apply (clarsimp)
  apply (elim disjE; clarsimp)
  using cs.seq.first_le dual_order.trans apply blast
  by (metis DiffD2 cs.seq.test_nil in_omega rangeI)



lemma test_match: "finite_obs l i y \<Longrightarrow> first A \<le> test b \<Longrightarrow> \<not>A \<in> \<Omega> \<Longrightarrow>
                   prime A = prime y \<Zsemi> c \<Longrightarrow> first y \<le> test b"
  apply (case_tac "\<exists>t. y = test t", clarsimp)
  apply (drule arg_cong[where f=First])
    apply (subgoal_tac "First (prime A) \<le> prime (test t)")
     defer
  using First_test_seq apply presburger
    apply (erule finite_obs.cases; clarsimp)
    apply (blast)
   apply (drule arg_cong[where f=First])
   apply (clarsimp simp: first_prime_step_eq)
   apply (erule order_trans[rotated])
   apply (meson dual_order.trans first_step first_test_prime in_omega)
    apply (erule finite_obs.cases; clarsimp)
   apply (metis cs.seq.flip.first_test cs.seq.flip.unit_of_apply cs.seq.test_atom first_test_chain in_omega omega_mono par_sync.seq_omega_closed prime_test_le)
  by (metis \<Omega>_def conj_sync.sync_step_test cra_atomic_iter.not_step_omega cra_atomic_iter_axioms cs.nil_par_nil_weak down_down in_downsetI)


  
lemma finite_obs_not_bot: "finite_obs ls i A \<Longrightarrow> \<not> A \<in> \<Omega>"
  apply (erule finite_obs.cases; clarsimp)
   apply (metis DiffD2 cs.seq.test_nil in_omega rangeI)
  using not_step_omega by auto




lemma prime_test_step: "prime (test a) \<Zsemi> prime (step l (a, b) ; A) = prime (step l (a, b) ; A) "
  apply (transfer)
  apply (intro set_eqI iffI; clarsimp simp: in_down_iff)
   apply (elim disjE; clarsimp simp: in_down_iff)+
     apply (meson cs.seq.mono_f cs.seq.test_le' refine_trans)
    apply (meson cs.seq.first_test_test' cs.seq.flip.down_unit cs.seq.flip.mono_f refine_trans)
   apply (elim disjE; clarsimp simp: in_down_iff)+
    apply (meson in_omega omega_mono par_sync.seq_omega_closed)
   apply (meson in_omega omega_mono par_sync.seq_omega_closed)
  apply (elim disjE; clarsimp?)
   apply (meson cs.seq.first_le cs.seq.flip.unit_of_apply dual_order.trans first_step in_down_iff)
  by (meson cs.seq.last_unit in_omega last_omega_closed)

lemma finite_obs_split: "finite_obs ls i x \<Longrightarrow> i' < i \<Longrightarrow> 
    \<exists>y y'. prime x = prime y \<Zsemi> prime y' \<and> finite_obs ls i' y \<and> finite_obs ls (i - i') y'"
  apply (induct x arbitrary: i' rule: finite_obs.inducts ; clarsimp?)
   apply (case_tac i'; clarsimp)
    apply (clarsimp simp: finite_obs_zero_iff)
    apply (rule_tac x="test a" in exI)
    apply (rule_tac x="(step l (a, b) ; A)" in exI)
    apply (intro conjI)
      defer
      apply (fastforce)
     apply (erule stepI ; clarsimp?)
    apply (drule_tac x=nat in meta_spec)
    apply (clarsimp)
    apply (rule_tac x="  (step l (a, b)) ;  y" in exI)
    apply (rule_tac x="y'" in exI)
    apply (intro conjI)
  using cs.seq.downset_seq_distrib_left.seq_assoc prime_seq apply auto[1]
 apply (rule stepI; clarsimp?)
     apply (rule test_match, assumption+)
      apply (erule finite_obs_not_bot)
     apply (assumption)+
  by (clarsimp simp: prime_test_step)+
  


lemma dnil_step_bot: "cs.seq.dnil \<sqinter> (prime (step l (a, b)) \<Zsemi> c) = \<bottom>"
  apply (rule antisym; clarsimp?)
  apply (rule order_trans)
   apply (rule conj.conj_to_inf)
  apply (clarsimp simp:  cs.seq.nil_dnil[symmetric])
  apply (clarsimp simp: less_eq_downset_def inf_downset_def 
                        cs.seq.nil_dnil[symmetric] cs.seq.conv_test_pre.nil_def)
  apply (transfer)
  apply  (clarsimp simp: mono_on_down  mono_on_SUP mono_on_principle mono_on_down' conj.commute )
  apply (intro conjI)
   apply  (clarsimp simp: in_down_iff)
   apply (elim disjE; clarsimp)
    apply (meson conj_sync.sync_step_test in_omega omega_mono)
   apply (meson conj_sync.bot_conj_test in_omega omega_mono)
  apply (clarsimp)
  apply (elim disjE; clarsimp simp: in_down_iff)
   apply (meson conj_sync.bot_conj_step in_omega local.conj.commute omega_mono)
  by (meson conj.covering dual_order.trans in_omega)
  

lemma infiter_sync: "finite_obs ls i x \<Longrightarrow> 
  seq_elem_fiter.infiter (datomic_l ls UNIV) \<sqinter> (prime x \<Zsemi> d) =
  prime x \<Zsemi> (seq_elem_fiter.infiter (datomic_l ls UNIV) \<sqinter>  d)"
  apply (rule antisym)
   apply (subst seq_elem_fiter.infiter_unfold_any[where i=i])
  apply (simp add: finite_obs_sync)
  apply (clarsimp, intro conjI)
   apply (subst seq_elem_fiter.infiter_unfold_any[where i=i]) back
   apply (metis cs.seq.down_seq_distrib_right.seq_mono finite_is_finite inf_sup_ord(1))
  by (simp add: cs.seq.downset_seq_distrib_left.seq_assoc cs.seq.downset_seq_distrib_left.seq_mono_right)

lemma fiter_unfold_seq:"seq_elem_fiter.fiter c =
   cs.seq.conv_test_pre.nil \<squnion>
  (cs.seq.conv_test.seq_power (c \<squnion> cs.seq.conv_test_pre.nil)  i \<Zsemi> seq_elem_fiter.fiter c)"
  apply (induct i; clarsimp)
   apply (metis seq_elem_fiter.fiter_fiter seq_elem_fiter.fiter_seq_fiter seq_elem_fiter.fiter_unfold)
  by (smt (verit, ccfv_threshold) cs.seq.conv_test.seq_nil_left cs.seq.conv_test.seq_power_front 
  cs.seq.down_seq_distrib_right.seq_mono cs.seq.downset_seq_distrib_left.seq_assoc
  seq_elem_fiter.fiter0 seq_elem_fiter.fiter_decomp seq_elem_fiter.fiter_fiter
  seq_elem_fiter.fiter_unfold sup.absorb2 sup.cobounded2)




lemma SUP_cong: "(\<And>x. x \<in> S \<Longrightarrow> ((f x) :: 'e :: complete_lattice) = g x) 
                             \<Longrightarrow> Sup (f ` S) = Sup (g ` S)"
  by (intro antisym; clarsimp simp: Sup_le_iff)

lemma SUP_cong': "bij_betw m S S' \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> ((f x) :: 'e :: complete_lattice) = g (m x)) \<Longrightarrow>
    Sup (f ` S) = Sup (g ` S')"
  apply (intro antisym; clarsimp simp: Sup_le_iff)
  apply (rule SUP_upper)
  using bij_betwE apply blast
  by (metis (no_types, lifting) SUP_upper bij_betw_def imageE)

lemma finite_obs_sync':" finite_obs ls i c \<Longrightarrow> 
      (cs.seq.conv_test.seq_power (datomic_l ls UNIV) i \<Zsemi> x) \<sqinter> (prime c \<Zsemi> y) = prime c \<Zsemi> x \<sqinter> y"
  apply (rule antisym)
   apply (erule finite_obs_sync)
  by (metis cs.seq.down_seq_distrib_right.seq_mono finite_is_finite inf.cobounded1 inf.cobounded2 inf_greatest)

lemma sync_less: "finite_obs ls i x \<Longrightarrow> (\<Squnion>b\<in>cs.seq.conv_test.seq_power ((datomic_l ls UNIV)) ` {j. j < i}. b \<sqinter> (prime x \<Zsemi> d)) \<le> prime x \<Zsemi> c"
  apply (simp add: Sup_le_iff; clarsimp)
  apply (frule (1) finite_obs_split)
  apply (clarsimp)
  apply (subgoal_tac "cs.seq.conv_test.seq_power (datomic_l ls UNIV) a \<sqinter> (prime y \<Zsemi> prime y' \<Zsemi> d) = prime y \<Zsemi> cs.seq.conv_test_pre.nil \<sqinter> (prime y' \<Zsemi> d)")
   apply (simp only:)
  apply (subst cs.seq.conv_semi.assoc)
   apply (rule cs.seq.conv_test.seq_mono_right)
  apply (erule_tac finite_obs.cases; clarsimp?) back back
    apply (simp add: cs.seq.downset_seq_distrib_left.seq_assoc cs.seq.nil_dnil dnil_step_bot prime_seq)
  apply (simp add: cs.seq.downset_seq_distrib_left.seq_assoc cs.seq.nil_dnil dnil_step_bot prime_seq)
  
  by (metis cs.seq.conv_test.seq_nil_right cs.seq.nil_dnil finite_obs_sync')


lemma sync_eq: "finite_obs ls i x \<Longrightarrow>cs.seq.conv_test.seq_power (datomic_l ls UNIV) i \<sqinter> (prime x \<Zsemi>  d) = prime x \<Zsemi> (cs.seq.conv_test_pre.nil \<sqinter>  d)" 
  by (metis cs.seq.conv_test.seq_nil_right cs.seq.downset_seq_distrib_left.seq_assoc finite_obs_sync')

lemma sync_greater: 
"finite_obs ls i x \<Longrightarrow> (\<Squnion>xa\<in>cs.seq.conv_test.seq_power (datomic_l ls UNIV) ` Collect ((<) i). xa \<sqinter> (prime x \<Zsemi> d)) =
 (\<Squnion>i\<in>{1..}. (prime x \<Zsemi> (cs.seq.conv_test.seq_power (datomic_l ls UNIV) i \<sqinter> d)))" 
  apply (subgoal_tac "(\<Squnion>xa\<in>cs.seq.conv_test.seq_power (datomic_l ls UNIV) ` Collect ((<) i). xa \<sqinter> (prime x \<Zsemi>  d)) =
                      (\<Squnion>xa\<in>Collect ((<) i). (cs.seq.conv_test.seq_power (datomic_l ls UNIV) xa) \<sqinter> (prime x \<Zsemi> d))")
  apply (simp only:)
   apply (rule SUP_cong'[where m="\<lambda>x. x - i"])
    apply (simp add: bij_betw_def, intro conjI)
     apply (rule inj_onI)
     apply (metis mem_Collect_eq nat_lessD)
    apply (intro set_eqI iffI; clarsimp simp: image_iff)
     apply auto[1]
  apply (metis add_Suc_right diff_add_inverse less_add_Suc1 linorder_not_less not0_implies_Suc zero_less_Suc)
   apply (simp add: image_iff)
  using cs.seq.conv_test.seq_power_split_less cs.seq.downset_seq_distrib_left.seq_assoc finite_obs_sync' apply presburger
  by (metis conv_cra_test.inf.NONDET_sync_distrib conv_cra_test.inf.Nondet_sync_distrib image_is_empty)

lemma sup_merge_zero:"(x :: 'e :: complete_lattice) = f 0 \<Longrightarrow> \<Squnion> (f ` {Suc 0..}) \<squnion> x = \<Squnion>(range f)"
  apply (intro antisym)
   apply (meson SUP_mono Sup_upper UNIV_I dual_order.eq_iff rangeI sup_least)
  apply (clarsimp)
  apply (clarsimp simp: Sup_le_iff)
  apply (case_tac a; clarsimp?)
  by (metis SUP_le_iff Suc_le_mono atLeast_iff inf_sup_aci(5) less_eq_nat.simps(1) sup_ge2)

lemma fiter_not_abort: "finite_obs ls i x \<Longrightarrow> seq_elem_fiter.fiter (datomic_l ls UNIV) \<sqinter> (prime x \<Zsemi> d) = prime x \<Zsemi> (seq_elem_fiter.fiter (datomic_l ls UNIV) \<sqinter> d) "
  apply (subst seq_elem_iter.fiter_seq_choice)
  apply (rule_tac i1=i in ssubst[OF nondet_nat.Nondet_partition_nat3])
  apply (simp only: inf_sup_distrib2 Sup_inf)
  apply (clarsimp)
  apply (clarsimp simp: sync_eq sync_greater)
  thm sync_greater
  thm sup_merge_zero
  apply (subst seq_elem_iter.seq_NONDET_distrib[symmetric])
   apply (clarsimp)
  apply (subst sup_commute)
  apply (subst sup_assoc)
  apply (subst sup_commute, subst sup.absorb2, rule sync_less, assumption)
  apply (subst seq_elem_fiter.seq_nondet_distrib[symmetric])
  apply (subst sup_merge_zero)
   apply (clarsimp)
  apply (subgoal_tac "(\<Squnion>x. cs.seq.conv_test.seq_power (datomic_l ls UNIV) x \<sqinter>  d) = (\<Squnion>x. cs.seq.conv_test.seq_power (datomic_l ls UNIV) x) \<sqinter> d")
   apply (simp only:)
  apply (simp only: seq_elem_iter.fiter_seq_choice[symmetric])
  apply (subst SUP_inf)
  apply (clarsimp)
  done

lemma rewrite: "(x \<sqinter> y) \<squnion> (z \<sqinter> y) = (x \<squnion> z) \<sqinter> (y :: 'e :: distrib_lattice)"
  
  by (simp add: inf_sup_distrib2)

lemma last_test_le: "last (test t) \<le> (test t)"
  using cs.seq.first_test_last_test_iff cs.seq.flip.first_test by auto


lemma last_test_ge: "last (test t) \<ge> (test t)"
  by (metis DiffD2 cs.seq.flip.down_unit cs.seq.last_unit cs.seq.test_is_first cs.seq.test_nil in_omega rangeI)


lemma prime_cong: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> prime x = prime y"
  apply (transfer, clarsimp, intro set_eqI iffI; clarsimp simp: in_down_iff)
  using dual_order.trans apply blast
  using dual_order.trans apply blast
  done


lemma step_seq_ref: "prime (step l s) \<Zsemi> c \<le> prime (step l s) \<Zsemi> d \<Longrightarrow>
                     prime (test (snd s)) \<Zsemi> c \<le>  prime (test (snd s)) \<Zsemi> d "
  apply (clarsimp simp: less_eq_downset_def)
  apply (transfer; clarsimp)
  apply (clarsimp simp: in_down_iff)
  apply (rule_tac x="test b" in bexI)
  apply (drule_tac c="step l (a, b) ; ba" in subsetD)
    apply (clarsimp)
    apply (rule_tac x="step l (a, b)" in bexI; clarsimp?)
    apply (rule_tac x="ba" in bexI; clarsimp?)
   apply (clarsimp simp: in_down_iff)
  apply (elim disjE; clarsimp simp: in_down_iff)
   apply (rule_tac x=xc in bexI; clarsimp?)
   apply (subgoal_tac "step l (a, b) ; ba \<le> step l (a, b) ; xc")
  apply (frule ref_tail; clarsimp)
      apply (meson cs.seq.flip.mono_f dual_order.refl dual_order.trans)
    apply (meson cs.seq.mono_f order_eq_refl order_trans)
  using not_step_omega apply auto[1]
  by (clarsimp)
  

lemma prefix_test_eq: "test b \<ge> first A \<Longrightarrow> prime (test b) \<Zsemi> (prime A \<Zsemi> c) =  (prime A \<Zsemi> c)"
  apply (transfer; clarsimp, intro set_eqI iffI; clarsimp simp: in_down_iff)
  apply (elim disjE; clarsimp simp: in_down_iff)+
     apply (meson cs.seq.mono_f cs.seq.test_le' in_down_iff refine_trans)
    defer
  apply (elim disjE; clarsimp simp: in_down_iff)+
     apply (meson in_omega omega_mono par_sync.seq_omega_closed)
    apply (meson in_omega omega_mono par_sync.seq_omega_closed)
  apply (elim disjE; clarsimp simp: in_down_iff)+
    apply (meson cs.seq.first_le first_seq in_down_iff order_trans sp.first_le_first_iff)
  apply (meson cs.seq.last_unit in_omega last_omega_closed)
proof -
  fix Aa :: 'a and ba :: 'b and ca :: "'a set" and x :: 'a and xa :: 'a and xb :: 'a and y :: 'a
  assume a1: "\<forall>y. \<not> x \<le> y\<^sub>\<bottom>"
  assume a2: "xa \<le> test ba"
  assume a3: "x \<le> xa ; xb"
  assume a4: "xb \<le> y\<^sub>\<bottom>"
  obtain aa :: "'b \<Rightarrow> 'a" where
    "xa \<le> first (aa ba)"
    using a2 cs.seq.test_is_first by moura
  then show "\<exists>xa\<in>\<down> Aa. \<exists>xb\<in>ca. x \<le> xa ; xb"
    using a4 a3 a1 by (meson cs.seq.flip.down_unit cs.seq.mono_f in_omega omega_mono)
qed

lemma prefix_test_eq': "last b \<ge> first A \<Longrightarrow> prime (last b) \<Zsemi> (prime A \<Zsemi> c) =  (prime A \<Zsemi> c)"
  apply (case_tac "last b \<in> \<Omega>")
   defer
  apply (subgoal_tac "\<exists>t. last b \<le> test t", clarsimp)
  using cs.seq.test_atom order_trans prefix_test_eq prime_cong apply fastforce
   apply (meson cs.seq.down_last cs.seq.flip.unit_of_unit cs.seq.not_bot_testable dual_order.trans)
  apply (clarsimp)
  apply (rule antisym)
  sorry
  oops



lemma last_seq_r: "first A \<le> test b \<Longrightarrow> last (step l (a, b) ; A) \<le> last A" 
  apply (rule order_trans, rule cs.seq.last_first_seq)
  sorry
  sledgehammer
  
  oops
  by (metis cs.seq.assoc cs.seq.flip.mono_f cs.seq.unit_of_unit order_refl)


lemma last_step_seq: "test b \<ge> first A \<Longrightarrow> last (step l (a, b) ; A) \<ge> last A"
  by (meson cs.seq.last_first_seq dual_order.trans last_step')


lemma finite_obs_seq_step: "finite_obs ls i x \<Longrightarrow>  prime x \<Zsemi> c \<le> prime x \<Zsemi> d \<Longrightarrow>
      (prime ( (last x)) \<Zsemi> c) \<le> (prime ((last x)) \<Zsemi> d)"
  apply (induct x rule: finite_obs.inducts)
  apply (metis last_test_ge last_test_le prime_cong)
   apply (clarsimp simp: prime_seq)
  apply (clarsimp simp: cs.seq.conv_semi.assoc)
   apply (frule step_seq_ref)
   apply (clarsimp)
  apply (clarsimp simp: prefix_test_eq)
  apply (subst prime_cong[where y="last _", rotated], rule last_step_seq, assumption)
  apply (erule  last_seq_r)
  apply (subst prime_cong[where y="last _", rotated], rule last_step_seq, assumption)
  using last_seq_r apply blast
  apply (assumption)
  done



lemma prefix_test_eq'': "prime (last b) \<ge> First A \<Longrightarrow> prime (last b) \<Zsemi> ( A) =  ( A)"
  apply (clarsimp simp: less_eq_downset_def)
  sorry
  apply (transfer; clarsimp, intro set_eqI iffI; clarsimp simp: in_down_iff)
  apply (metis cs.seq.down_unit cs.seq.flip.down_unit cs.seq.flip.mono_f cs.seq.flip.unit_of_apply in_Down_iff refine_trans)
  apply (case_tac "A \<le> \<bottom>")
  apply blast
  apply (rule_tac x="last b" in bexI; (clarsimp simp: in_down_iff)?)
  apply (rule_tac x="x" in bexI; (clarsimp simp: in_down_iff)?)
  apply (subgoal_tac "first x \<le> last b")
  apply (metis cs.seq.first_last rangeE rangeI sp.first_le_first_iff)
   apply (drule_tac c="first x" in subsetD)
  using down_image_iff apply blast
  by (clarsimp simp: in_down_iff)+

lemma le_first_le_test: "x \<le> first y \<Longrightarrow> x \<in> \<Omega> \<or> (\<exists>t. x \<ge> test t \<and> x \<le> test t)"
  by (meson cs.seq.not_bot_testable' cs.seq.test_atom dual_order.trans in_omega)

lemma First_inf: "First (c \<sqinter> d) \<le> (First c \<sqinter> First d)"
  apply (clarsimp simp: less_eq_downset_def inf_downset_def, transfer, clarsimp)
  apply (intro conjI, clarsimp simp: in_down_iff down_image_iff)
  apply (meson DiffI in_omega)
  apply (clarsimp simp: in_down_iff down_image_iff)
  by (metis DiffI in_omega)

lemma greater_botI:"((x :: 'a :: preorder_bot) \<le> \<bottom> \<Longrightarrow> False) \<Longrightarrow> x > \<bottom>"
  oops
  by (meson less_le_not_le preorder_bot_class.bot_least)

lemma not_aborting_not_aborting_seq: 
 "bottom x < a \<iinter> bottom y \<Longrightarrow> (a ; bottom z) \<iinter> bottom y >  bottom x"

  sorry


lemma not_aborting_iter: "a \<in> {c. conj c (bottom c) \<notin> \<Omega>} \<Longrightarrow> prime (a) \<Zsemi> c \<le> seq_elem_fiter.iter (datomic_l {Pgm, Env} UNIV) \<sqinter> (prime a \<Zsemi> c)  \<Longrightarrow> False"
   apply (clarsimp simp: less_eq_downset_def seq_elem_fiter.iter_def gfp_def inf_downset_def sup_downset_def step_atomic.Atomic_def )
  apply (clarsimp simp: cs.seq.conv_test_pre.nil_def)
  apply (transfer)
  apply (drule_tac c="a ; bottom (last a)" in subsetD; clarsimp)
   apply (metis in_down_iff in_mono in_omega order_refl)

  apply (elim disjE; clarsimp?)
  apply (drule_tac c="a ; bottom (last a)" in subsetD; clarsimp)
     apply (elim disjE; clarsimp simp: down_image_iff in_down_iff)
  sorry
  sledgehammer
  oops
  apply (smt (verit, ccfv_SIG) conj.mono_f cs.conj_bot_test dual_order.refl dual_order.strict_trans2 less_le_not_le local.conj.commute not_aborting_not_aborting_seq)
  
    apply (clarsimp simp: down_union_distrib )
    apply (elim disjE; clarsimp simp: down_image_iff in_down_iff)
     apply (subgoal_tac "a ; \<bottom> \<le>  step Pgm (aa, b) ; xb") 
      apply (subgoal_tac "conj (step Pgm (aa, b) ; xb) \<bottom> \<le> \<bottom>") 
  
       apply (meson conj.mono_f dual_order.strict_trans2 less_le_not_le not_aborting_not_aborting_seq preorder_bot_class.bot_least)
  apply (metis (no_types, opaque_lifting) conj.mono_f conj_sync.sync_step_test dual_order.trans local.conj.commute order_eq_refl preorder_bot_class.bot_least)
  apply (meson cs.seq.mono_f dual_order.refl dual_order.trans)
apply (subgoal_tac "a ; \<bottom> \<le>  step Env (aa, b) ; xb") 
  apply (subgoal_tac "conj (step Env (aa, b) ; xb) \<bottom> \<le> \<bottom>") 
     
      apply (meson conj.mono_f dual_order.strict_trans2 less_le_not_le not_aborting_not_aborting_seq preorder_bot_class.bot_least)
  apply (metis (no_types, opaque_lifting) conj.mono_f conj_sync.sync_step_test dual_order.trans local.conj.commute order_eq_refl preorder_bot_class.bot_least)

    apply (meson cs.seq.mono_f dual_order.refl dual_order.trans)
  apply (clarsimp simp: in_down_iff)
  using cs.le_bot_conj' dual_order.strict_trans2 less_le_not_le
  by (metis dual_order.refl not_aborting_not_aborting_seq)


(* lemma not_aborting_iter': "a \<in> {c. par c \<bottom> > \<bottom>} \<Longrightarrow> prime (a) \<Zsemi> c \<le> seq_elem_fiter.iter (datomic_l {Env} UNIV) \<sqinter> (prime a \<Zsemi> c)  \<Longrightarrow> False"
   apply (clarsimp simp: less_eq_downset_def seq_elem_fiter.iter_def gfp_def inf_downset_def sup_downset_def step_atomic.Atomic_def )
  apply (clarsimp simp: cs.seq.conv_test_pre.nil_def)
 apply (transfer)
  apply (clarsimp)
  apply (drule_tac c="a ; \<bottom>" in subsetD; clarsimp)
  using in_down_iff apply blast
  apply (elim disjE; clarsimp?)
  apply (drule_tac c="a ; \<bottom>" in subsetD; clarsimp)
   apply (elim disjE; clarsimp simp: down_image_iff in_down_iff)
      apply (meson ab_ordered_semigroup_def less_le_not_le not_aborting_not_aborting_seq' 
 order_le_less_trans order_refl ordered_semigroup.mono_f par.ab_ordered_semigroup_axioms sp.test_bot)
  apply (metis less_le_not_le not_aborting_not_aborting_seq' order_le_less_trans order_refl par.commute sp.le_bot_par)
 apply (subgoal_tac "a ; \<bottom> \<le>  step Env (aa, b) ; xb") 
      apply (subgoal_tac "par (step Env (aa, b) ; xb) \<bottom> \<le> \<bottom>") 
      apply (meson less_le_not_le not_aborting_not_aborting_seq' order_le_less_trans order_refl par.mono_f)

      apply (metis (no_types, opaque_lifting) order_eq_refl order_trans par.commute par.mono_f par_sync.sync_step_test preorder_bot_class.bot_least)
    apply (meson cs.seq.flip.mono_f dual_order.trans order_refl)
  apply (subgoal_tac "a ; \<bottom> \<le> \<bottom>")
    apply (meson less_le_not_le not_aborting_not_aborting_seq' par.mono_f preorder_bot_class.bot_least sp.le_bot_par)
  apply (meson cs.seq.bot_annihilate_seq cs.seq.mono_f dual_order.trans par.aborting)
  apply (clarsimp simp: in_down_iff)
  using dual_order.strict_trans2 less_le_not_le
  by (metis not_aborting_not_aborting_seq' order_refl par.commute sp.le_bot_par)
*)

lemma le_inf_iff_simple: "(x :: 'e :: complete_lattice) \<le> y \<sqinter> x \<Longrightarrow> x \<le> y "
  using le_inf_iff by blast

lemma not_environment_step_False: "not_environment a \<Longrightarrow> a  \<le>  step Env s ; b \<Longrightarrow> False"
  apply (clarsimp simp: not_environment_def)
  apply (erule_tac x="fst s" in allE)
  apply (erule_tac x="snd s" in allE)
  by (metis prod.collapse)

lemma not_environment_test_False: "not_environment a \<Longrightarrow> a  \<le>  test t \<Longrightarrow> False"
  by (clarsimp simp: not_environment_def)

lemma not_aborting_iter'': "not_environment a \<Longrightarrow> prime (a) \<Zsemi> c \<le> seq_elem_fiter.iter (datomic_l {Env} UNIV) \<sqinter> (prime a \<Zsemi> c)  \<Longrightarrow> False"
  sorry
  apply (drule le_inf_iff_simple)
   apply (clarsimp simp: less_eq_downset_def seq_elem_fiter.iter_def gfp_def inf_downset_def sup_downset_def step_atomic.Atomic_def )
  apply (clarsimp simp: cs.seq.conv_test_pre.nil_def)
 apply (transfer)
  apply (clarsimp simp: par_sync.nonempty_bot_union' par_sync.nonempty_bot_union mono_on_down  mono_on_SUP mono_on_principle mono_on_down' conj.commute)
  apply (drule_tac c="a ; \<bottom>" in subsetD; clarsimp)
  using in_down_iff apply blast
  apply (elim disjE; clarsimp?)
  apply (drule_tac c="a ; \<bottom>" in subsetD; clarsimp)
   apply (elim disjE; clarsimp simp: down_image_iff in_down_iff)
    apply (meson cs.seq.test_seq_test dual_order.trans not_environment_def)
   apply (erule (1) not_environment_step_False)
  by (meson in_down_bot_trans in_down_iff not_environment_def)
 


lemma le_first_le_test': "x \<le> first y \<Longrightarrow> \<exists>t. x \<le> test t"
  oops
  using le_first_le_test sp.le_bot_le_any by blast

lemma first_iter_atomic: "First (seq_elem_fiter.iter (datomic_l l UNIV)) = cs.seq.dtest UNIV"
  apply (clarsimp simp: seq_elem_fiter.iter_def gfp_def sup_downset_def less_eq_downset_def)
  apply (clarsimp simp: cs.seq.conv_test_pre.nil_def step_atomic.Atomic_def)
  apply (transfer)
  apply (safe; clarsimp simp: in_down_iff down_image_iff)
  apply (meson in_omega le_first_le_test)
    apply (elim disjE; clarsimp?)
     apply (erule le_first_le_test')
    apply (erule le_first_le_test')
   apply (rule_tac x="test y" in bexI)
  using cs.seq.first_test_test' dual_order.trans apply blast
  apply (clarsimp)
  apply (intro conjI)
  apply (clarsimp)
   apply (rule_tac x="\<down>(test y) \<union> \<Omega>" in exI, clarsimp)
  apply (intro conjI)
     apply (smt (verit) Un_iff in_down_iff rangeI sp.in_Down_iff subset_iff)
    apply force
   apply (clarsimp simp: down_sup_distrib down_union_distrib)
  using dual_order.trans by blast

lemma inf_tau: "cs.seq.dtest UNIV \<sqinter> First A = First A"
  apply (clarsimp simp: inf_downset_def, transfer, clarsimp)
  apply (safe; clarsimp simp: down_image_iff in_down_iff)
  by (meson in_omega le_first_le_test)

lemma le_first_le_seq: "first a \<le> x \<Longrightarrow> First (prime a \<Zsemi> c) \<le> prime ( x)"
  apply (clarsimp simp: less_eq_downset_def)
  apply (transfer; clarsimp simp: down_image_iff in_down_iff)
  by (meson cs.seq.first_le dual_order.trans first_seq)

lemma step_atomic_datomic_l: "step_atomic.Atomic = datomic_l {Pgm, Env} UNIV"
  apply (clarsimp simp: step_atomic.Atomic_def, transfer, clarsimp)
  by (safe; clarsimp simp: in_down_iff down_image_iff
            down_sup_distrib down_union_distrib; metis labels.exhaust)


lemma iter_not_aborting: "finite_obs {Pgm, Env} i x \<Longrightarrow> a \<in> {c. conj c (bottom c) \<notin> \<Omega>} \<Longrightarrow> last x \<ge> first a \<Longrightarrow>  prime x \<Zsemi> prime a \<Zsemi> c \<le> seq_elem_fiter.iter step_atomic.Atomic \<Longrightarrow> False"
  apply (clarsimp simp: step_atomic_datomic_l)
  apply (subst (asm)  inf.absorb_iff2)

  apply (subst (asm) seq_elem_fiter.iter_isolation)
  apply (subst (asm) inf_sup_distrib2)
  apply (subst (asm) cs.seq.conv_semi.assoc)
  apply (subst (asm) fiter_not_abort, assumption)
  apply (subst (asm) cs.seq.conv_semi.assoc)
  apply (clarsimp simp: infiter_sync)
  apply (subst (asm) seq_elem_fiter.seq_nondet_distrib[symmetric])
  apply (subst (asm) rewrite)
  apply (subst (asm) seq_elem_fiter.iter_isolation[symmetric])
  apply (drule sym, drule eq_refl)
  apply (subst (asm) cs.seq.conv_semi.assoc)
  apply (drule (1) finite_obs_seq_step[rotated])
  apply (subst (asm) prefix_test_eq'')
  apply (erule le_first_le_seq)
  apply (subst (asm) prefix_test_eq'')
   apply (rule order_trans, rule First_inf)
   apply (clarsimp simp: first_iter_atomic inf_tau)
   apply (erule le_first_le_seq)
  by (erule not_aborting_iter[rotated], fastforce)

lemma [simp]:"\<Down> (\<down> b \<union> \<Omega>) = \<down>b \<union> \<Omega>" 
  by (clarsimp simp: down_sup_distrib down_union_distrib)

lemma seq_downsub_iff: "A \<Zsemi> B \<down>\<subseteq> C \<longleftrightarrow> (\<forall>v. (\<exists>a b. a \<down>\<in> A \<and> b \<down>\<in> B \<and> v \<le> a ; b) \<longrightarrow> v \<down>\<in> C )"
  apply (safe)
   apply (transfer)
   apply (clarsimp)
  apply (drule_tac c="a;b" in subsetD; (clarsimp simp: in_down_iff)?)
    apply blast
  using in_Down_iff apply blast
   apply (transfer)

  apply (clarsimp simp: in_down_iff)
  apply (erule_tac x=x in allE)
  apply (drule mp, blast)
  apply (clarsimp)
  done


lemma Dsub_iff': "Dsub A B \<longleftrightarrow> (\<forall>x. x \<down>\<in> A \<longrightarrow> x \<notin> \<Omega> \<longrightarrow> x \<down>\<in> B)"
  apply (transfer)
  apply (safe; transfer; clarsimp)
   apply blast
  using in_omega by blast

lemma in_seq_iff: "x \<down>\<in> A \<Zsemi> B \<longleftrightarrow> (\<exists>a b. a \<down>\<in> A \<and> b \<down>\<in> B \<and> x \<le> a ; b)"
  apply (transfer; safe; clarsimp simp: in_down_iff)
   apply (rule_tac x=a in exI, clarsimp)
  apply (rule_tac x=b in exI, clarsimp)
  by blast

lemma in_prime_iff: "a \<down>\<in> prime x \<longleftrightarrow> (a \<le> x \<or> a \<in> \<Omega>)"
  by (transfer; safe; clarsimp simp: in_down_iff)


lemma in_llp_iff: "a \<down>\<in> llp x \<longleftrightarrow> (\<exists>v. v \<down>\<in> x \<and> a \<le> unit_of v )"
  apply (transfer; safe; clarsimp simp: in_down_iff down_image_iff)
   apply (blast)
  apply (blast)
  done

lemma not_din_iff: "\<not> y \<down>\<in> c \<longleftrightarrow> (\<forall>x. x \<down>\<in> c \<longrightarrow> \<not> y \<le> x)"
  apply (transfer; clarsimp)
  apply (safe)
  using in_downsetI apply blast
  by blast

lemma le_llp_if: "(\<And>x i d s a . finite_obs {Pgm, Env} i x \<Longrightarrow> conj a (bottom a) \<notin> \<Omega> \<Longrightarrow> first a \<le> last x \<Longrightarrow>   prime x  \<Zsemi> prime a \<Zsemi> d \<le> c \<Longrightarrow> False) \<Longrightarrow> c \<le> gfp llp"
  apply (rule gfp_upperbound)
  apply (clarsimp simp: less_eq_downset_def in_prime_iff  Dsub_iff' in_seq_iff seq_downsub_iff in_llp_iff)
  apply (atomize)
  apply (erule contrapos_pp, clarsimp)
  apply (erule_tac x=x in allE) back
  apply (clarsimp)
   apply (drule aborting_when)
   apply (clarsimp)
   apply (rule_tac x=a in exI)
   apply (intro conjI)
    apply (rule_tac x=n in exI)
  apply (fastforce)
   apply (rule_tac x="prime (b) " in exI)
   apply (rule_tac x="y" in exI)
  apply (intro conjI; clarsimp simp: in_prime_iff)
  apply (elim disjE; clarsimp simp: not_din_iff)
         apply (meson Din_intro cs.seq.mono_f refine_trans)
        apply (meson cs.seq.flip.mono_f dual_order.trans order_refl step_bot_mono)
       apply (meson bot_in in_omega omega_mono sp.omega_seq)
      apply (meson bot_in in_omega omega_mono sp.omega_seq)
     apply (meson Din_intro cs.seq.flip.mono_f step_bot_mono)
    apply (meson cs.seq.mono_f dual_order.trans order_refl step_bot_mono)
   apply (meson bot_in in_omega omega_mono sp.omega_seq)
  by (meson bot_in in_omega omega_mono sp.omega_seq)
 

lemma not_env_iter: "(\<And>x i d s a ls. finite_obs (\<eta> Env) i x \<Longrightarrow> not_environment a \<Longrightarrow> first a \<le> last x \<Longrightarrow>   prime x  \<Zsemi> prime a \<Zsemi> d \<le> c \<Longrightarrow> False) \<Longrightarrow> c \<le> par.dunit"
  apply (clarsimp simp: less_eq_downset_def  )
  sorry
  apply (transfer, clarsimp simp: down_image_iff)
  apply (rule_tac x="x" in exI)
  apply (atomize)
  apply (erule contrapos_pp, clarsimp)
   apply (drule aborting_when')
   apply (clarsimp)
  apply (rule_tac x=a in exI)
  apply (intro conjI)
  apply (rule_tac x=n in exI, fastforce simp: eta_def)
   apply (rule_tac x="\<down>(b)" in exI, clarsimp)
   apply (rule_tac x="y" in exI)
   apply (intro conjI; clarsimp)
    apply (clarsimp simp: in_down_iff)
  apply (subgoal_tac "xa \<le> x")
  using in_downsetI apply blast
   apply (rule order_trans[rotated], assumption)
  apply (erule order_trans)
   apply (smt (verit, del_insts) cs.seq.assoc cs.seq.mono_f refine_trans)
  done

lemma  iter_env_always: "finite_obs {Env} i x \<Longrightarrow> not_environment a \<Longrightarrow> last x \<ge> first a \<Longrightarrow>  prime x \<Zsemi> prime a \<Zsemi> c \<le> seq_elem_fiter.iter (datomic_l {Env} UNIV) \<Longrightarrow> False"
  apply (subst (asm)  inf.absorb_iff2)
  apply (subst (asm) seq_elem_fiter.iter_isolation)
  apply (subst (asm) inf_sup_distrib2)
  apply (subst (asm) cs.seq.conv_semi.assoc)
  apply (subst (asm) fiter_not_abort, assumption)
  apply (subst (asm) cs.seq.conv_semi.assoc)
  apply (subst (asm) infiter_sync, assumption)
  apply (subst (asm) seq_elem_fiter.seq_nondet_distrib[symmetric])
  apply (subst (asm) rewrite)
  apply (subst (asm) seq_elem_fiter.iter_isolation[symmetric])
  apply (drule sym, drule eq_refl)
  apply (subst (asm) cs.seq.conv_semi.assoc)
  apply (drule (1) finite_obs_seq_step[rotated])
  apply (subst (asm) prefix_test_eq'')
  apply (erule le_first_le_seq)
  apply (subst (asm) prefix_test_eq'')
   apply (rule order_trans, rule First_inf)
   apply (clarsimp simp: first_iter_atomic inf_tau)
   apply (erule le_first_le_seq)
  using not_aborting_iter'' by blast

lemma llp_is_dunit: "gfp llp = conj.dunit"
  apply (rule antisym)
   apply (clarsimp simp: gfp_def Sup_le_iff )
  apply (clarsimp simp: less_eq_downset_def)
   apply (transfer)
   apply (clarsimp simp: down_image_iff)
   apply (meson down_image_iff subset_iff)
  apply (clarsimp simp: gfp_def Sup_le_iff )
  apply (rule Sup_upper, clarsimp)
  apply (clarsimp simp: less_eq_downset_def)
  apply (transfer)
   apply (clarsimp simp: down_image_iff Bex_def)
  using unit_closed_closed by blast

lemma infiter_ref_conj:
  "down_iteration_infinite_distrib.infiter (conj.convolute (datomic p) (datomic q)) \<le>
   conj.convolute (down_iteration_infinite_distrib.infiter (datomic p)) (down_iteration_infinite_distrib.infiter (datomic q))"
  sorry

lemma infiter_ref_par: "down_iteration_infinite_distrib.infiter (par.convolute (datomic p) (datomic q)) \<le>
       par.convolute (down_iteration_infinite_distrib.infiter (datomic p)) (down_iteration_infinite_distrib.infiter (datomic q))"
  sorry


sublocale atomic_conv_conj_seq_elem: conj_atomic cs.seq.convolute cs.seq.conv_test_pre.nil datomic conj.convolute 
  apply (standard)
  using conj.conv_idemp apply presburger
  apply (clarsimp)
  using conj_sync.convolute_step_convolute apply blast
        apply (rule antisym)
  using conj.conv_sync.sync_commute conj_sync.conv_sync_seq_step apply presburger
        apply (simp add: cs.exchange_convolute.exchange)
  using conj_sync.conv_sync_test_step apply fastforce
      defer
      apply (clarsimp simp: step_atomic.Atomic_def, blast)
     apply (clarsimp simp: step_atomic.Atomic_def)
  apply (subst conj_sync.convolute_step_convolute)
     apply (transfer)
     apply (safe; clarsimp simp: in_down_iff down_image_iff conj_sync.merge_def)
      apply (frule conj.covering, elim disjE; clarsimp?)
      apply (frule step_meet', rule order_refl)
      apply (elim disjE; clarsimp?)
        apply (metis Diff_iff cs.seq.test_nil in_omega last_step' omega_mono rangeI)
  sledgehammer
  thm conj_sync.bot_conj_step
  sorry
      apply (smt (verit, ccfv_SIG) conj.covering conj.unit_of_unit conj_sync.bot_conj_step
                                   dual_order.trans local.conj.idem step_meet')
  apply (metis fst_conv local.conj.idem order_refl snd_conv)
    apply auto[1]
   apply (subgoal_tac "(seq_elem_fiter.iter step_atomic.Atomic) = gfp llp")
    apply (simp add: llp_is_dunit )
  apply (rule antisym)
    apply (rule le_llp_if)
    apply (erule_tac i=i in iter_not_aborting[rotated -1])
      apply (clarsimp)+
   apply (simp add: iter_conj_dunit llp_is_dunit)
  apply (rule infiter_ref_conj)
  done

lemma env_is_datomic: " datomic_l {Env} UNIV = datomic {s. fst s = Env}"
  apply (transfer, safe; clarsimp simp: down_image_iff in_down_iff)
  done

sublocale atomic_conv_par_seq_elem: par_atomic cs.seq.convolute cs.seq.conv_test_pre.nil datomic par.convolute "datomic_l {Env} UNIV"
  apply (standard)
  using conv_cra.nil_par_nil apply fastforce
  apply (clarsimp)
  using par_sync.convolute_step_convolute apply blast
        apply (rule antisym)
  using par.conv_sync.sync_commute par_sync.conv_sync_seq_step apply presburger
  apply (simp add: sp.exchange_convolute.exchange)
  using par_sync.conv_sync_test_step apply fastforce
     apply (rule infiter_ref_par)
    apply (rule_tac x="{s. fst s = Env}" in exI)
    apply (transfer, safe; clarsimp simp: down_image_iff in_down_iff)
   apply (subst env_is_datomic)
   apply (subst  par_sync.convolute_step_convolute)
   apply (transfer, safe; clarsimp simp: down_image_iff in_down_iff  par_sync.merge_def)
    apply (erule order_trans)
    apply (erule order_trans)
  sorry
  apply (subst par.commute)
  apply (rule par_steps')
  apply (metis fst_conv par.commute par_steps snd_conv)
   apply (subgoal_tac "(seq_elem_fiter.iter (datomic_l {Env} UNIV)) = par.dunit")
    apply (simp add: llp_is_dunit )
  apply (rule antisym)
   apply (rule not_env_iter)
  apply (rule iter_env_always, fastforce, assumption)
    apply (metis eta_def iter_env_always)
  apply (metis eta_def iter_env_always)
  apply (clarsimp)+
  using iter_par_dunit by fastforce

sublocale atomic_conv_commands: atomic_commands cs.seq.convolute cs.seq.conv_test_pre.nil datomic par.convolute "datomic_l {Env} UNIV" conj.convolute
   apply (standard)
                   apply auto[1]
          apply (metis step_atomic.atomic.hom_inf)
         apply (simp add: atomic_inf')
        apply (metis conj.conj_to_inf conj_sync.conv_sync_test_step inf.absorb2 inf_bot_left)
       apply (metis cs.seq.down_seq_distrib_right.seq_mono le_inf_iff order_eq_refl seq_elem_fiter.infiter_induct seq_elem_fiter.infiter_unfold)
  using atomic_conv_conj_seq_elem.conj.syncid_atomic apply auto[1]
     apply (simp add: inf.absorb2 step_atomic.atomic.Hom_ref_hom)
    apply (simp add: cs.exchange_convolute.exchange)
   apply (simp add: exchange_convolute.exchange)
  using sp.exchange_convolute.exchange by presburger
end

end