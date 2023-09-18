theory CouplingInvariants
  imports
  "While_Loop"
  "AtomicSpecification"
  "Local"
begin                                   

datatype ('c, 'a) scoped = Scoped (d : "'c set") (v : 'a)




locale tuple_system =
  fixes \<DD> :: "'a set set" and T :: "'b set" and d :: "'b \<Rightarrow> 'a set" and down :: "('b \<times> 'a set) \<Rightarrow> 'b" 
  assumes a1: "U \<in> \<DD> \<Longrightarrow> x \<in> T \<Longrightarrow> U \<subseteq> d x \<Longrightarrow> d (down (x, U)) = U" and
          a2: "U \<in> \<DD> \<Longrightarrow> W \<in> \<DD> \<Longrightarrow> x \<in> T \<Longrightarrow> U \<subseteq> W  \<Longrightarrow> W \<subseteq> d x \<Longrightarrow> down ((down (x, W)), U) = down (x, U)" and
          a3: "U \<in> \<DD> \<Longrightarrow> x \<in> T \<Longrightarrow> d x = U \<Longrightarrow> (down (x, U)) = x" and
          a4: "U \<in> \<DD> \<Longrightarrow> W \<in> \<DD> \<Longrightarrow> x \<in> T \<Longrightarrow> y \<in> T \<Longrightarrow> d x = U \<Longrightarrow> d y = W \<Longrightarrow>   down (x, (U \<inter> W)) = down (y, (U \<inter> W)) \<Longrightarrow> \<exists>z\<in>T.  d z = (U \<union> W) \<and> down (z, U) = x \<and> down (z, W) = y" and
          a5: "U \<in> \<DD> \<Longrightarrow> x \<in> T \<Longrightarrow> d x = U \<Longrightarrow> W \<in> \<DD> \<Longrightarrow>  U \<subseteq> W  \<Longrightarrow> \<exists>y\<in>T. d y = W \<and>  (down (y, U)) = x"


locale coupling_inv = locals + atomic_specification + while_loop
begin                  


text \<open>The identity relation on all variables not in the set $vars$. \<close>
definition id_bar' :: "'c set \<Rightarrow> 'b rel"
  where "id_bar' vars = {(\<sigma>,\<sigma>'). \<forall>x::'c. x \<notin> vars \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}"


text \<open>Add a frame of $vars$ to a command $c$.\<close>
definition var_frame_set' :: "'c set \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<^sub>s" 95)
  where "var_frame_set' vars c \<equiv> conj (guar (id_bar' vars))  c"

definition scoped_ref :: "('c, 'a) scoped \<Rightarrow> ('c, 'a) scoped \<Rightarrow> bool" where
 "scoped_ref x y \<equiv> var_frame_set' (d x) (v x) \<le> var_frame_set' (d y) (v y)"


definition scoped_ref_strict :: "('c, 'a) scoped \<Rightarrow> ('c, 'a) scoped \<Rightarrow> bool" where
 "scoped_ref_strict x y \<equiv> var_frame_set' (d x) (v x) < var_frame_set' (d y) (v y)"

declare [[show_sorts=false]] [[show_types=false]]

definition "inf_scoped x y \<equiv> Scoped (d x \<sqinter> d y) (v x \<sqinter> v y)"

definition "sup_scoped x y \<equiv> Scoped (d x \<squnion> d y) (var_frame_set' (d x) (v x) \<squnion> var_frame_set' (d y) (v y))"

definition "Sup_scoped x \<equiv> Scoped (\<Squnion>(d ` x))  (\<Squnion>c\<in>x. var_frame_set' (d c) (v c)) "

definition "Inf_scoped x \<equiv> Scoped (\<Sqinter>(d ` x))  (\<Sqinter>(v ` x)) "



declare guar_def[simp del]

notation conj (infixl "\<oplus>" 40) 

lemma id_bar_inf: "(id_bar' y \<inter> id_bar' x) = id_bar' (x \<inter>  y) "
  by (clarsimp simp: id_bar'_def, safe; blast)

lemma conj_inf_exchange: "(c\<^sub>0 \<sqinter> c\<^sub>1) \<iinter> (d\<^sub>0 \<sqinter> d\<^sub>1) \<ge> (c\<^sub>0 \<iinter> d\<^sub>0) \<sqinter> (c\<^sub>1 \<iinter> d\<^sub>1)" sorry


lemma var_frame_mono: "S \<subseteq> S' \<Longrightarrow> c \<le> c' \<Longrightarrow> (S :: 'c set) :\<^sub>s c \<le> (S' :: 'c set) :\<^sub>s c'"
  apply (clarsimp simp: var_frame_set'_def)
  apply (rule conj.sync_mono)
   apply (rule guar_strengthen)
   apply (clarsimp simp: id_bar'_def)
   apply (erule_tac x=x in allE)
  by (auto)

lemma var_frame_idemp:  "(var_frame_set' (S :: 'c set) c) = var_frame_set' S (var_frame_set' S c)"
  by (clarsimp simp: var_frame_set'_def)


sublocale scoped_refinement: refinement_lattice Inf_scoped Sup_scoped inf_scoped  "scoped_ref" "scoped_ref_strict" sup_scoped "Sup_scoped {}" "Inf_scoped {}"
  apply (standard)
                  apply (clarsimp simp: scoped_ref_strict_def scoped_ref_def)
                  apply (safe; fastforce)
                 apply (clarsimp simp: scoped_ref_def)
  apply (clarsimp simp: scoped_ref_def)
                apply (erule (1) order_trans)
               apply (clarsimp simp: scoped_ref_def)
               defer
               apply (clarsimp simp: scoped_ref_def inf_scoped_def)

               apply (clarsimp simp: var_frame_set'_def)
               apply (rule conj.sync_mono, rule guar_strengthen)
  apply (clarsimp simp: id_bar'_def)
               apply auto[1]
 apply (clarsimp simp: scoped_ref_def inf_scoped_def)

               apply (clarsimp simp: var_frame_set'_def)
               apply (rule conj.sync_mono, rule guar_strengthen)
  apply (clarsimp simp: id_bar'_def)
              apply auto[1]
             apply (clarsimp simp: scoped_ref_def inf_scoped_def var_frame_set'_def)
             apply (rule order_trans, erule (1) inf_greatest)
             apply (rule order_trans, rule conj_inf_exchange)
  
  apply (metis conj.sync_mono_left conj_to_inf guar_merge id_bar_inf inf.sync_commute)

             apply (clarsimp simp: scoped_ref_def sup_scoped_def var_frame_set'_def)
             apply (subst conj.sync_nondet_distrib)
  apply (rule le_supI1)
  find_theorems sup "_ \<le> _ \<squnion> _"
            apply (subst conj_assoc[symmetric], clarsimp simp: guar_merge id_bar_inf)
   apply (clarsimp simp: scoped_ref_def sup_scoped_def var_frame_set'_def)
             apply (subst conj.sync_nondet_distrib)
           apply (rule le_supI2)
            apply (subst conj_assoc[symmetric], clarsimp simp: guar_merge id_bar_inf)

             apply (rule conj.sync_mono, rule guar_strengthen)
  apply (clarsimp simp: id_bar'_def)
             apply simp  
            apply (clarsimp simp: scoped_ref_def sup_scoped_def var_frame_set'_def)

           apply (rule order_trans[rotated])
             apply (erule (1) sup_least)
             apply (subst conj.sync_nondet_distrib)
          apply (clarsimp simp: conj_assoc[symmetric] guar_merge id_bar_inf)
         apply (clarsimp simp: scoped_ref_def Inf_scoped_def)
         apply (rule var_frame_mono)
          apply blast
         apply (simp add: INF_lower)
        apply (clarsimp simp: scoped_ref_def Inf_scoped_def)
        apply (clarsimp simp: var_frame_set'_def)
        defer
        apply (clarsimp simp: scoped_ref_def Sup_scoped_def)
  apply (subst var_frame_idemp)
        apply (rule var_frame_mono)
         apply blast
        apply (erule  complete_lattice_class.SUP_upper2)
        apply (blast)
       apply (clarsimp simp: scoped_ref_def Sup_scoped_def)
  apply (case_tac "A = {}", clarsimp)
        apply (clarsimp simp: var_frame_set'_def)
        apply (metis guar_conj_test order_refl seq_magic_left test.hom_bot test_seq_refine)
       apply (clarsimp simp: var_frame_set'_def)
       apply (subst conj.sync_NONDET_distrib, assumption)
       apply (subst Sup_le_iff, clarsimp)
       apply (clarsimp simp: conj_assoc[symmetric] guar_merge id_bar_inf)
       apply (subgoal_tac "d a \<inter> \<Union> (d ` A) = d a")
  apply (clarsimp)
       apply blast
      apply (clarsimp)
     apply (clarsimp)
    apply (clarsimp simp: Inf_scoped_def Sup_scoped_def scoped_ref_def)
       apply (clarsimp simp: var_frame_set'_def)

  sorry

lemma var_frame_distrib: "(S :: 'c set) :\<^sub>s (x \<squnion> y) = (S :\<^sub>s x) \<squnion> (S :\<^sub>s y)"
  apply (clarsimp simp: var_frame_set'_def)
  using guar_distrib_nondet by force


lemma scoped_eqI: "var_frame_set' (d x) (v x) = var_frame_set' (d y) (v y) \<Longrightarrow> x = y"
  sorry

lemma id_bar_inf': "S \<subseteq> S' \<Longrightarrow> (id_bar' S \<inter> id_bar' S') = (id_bar' S)"
  apply (clarsimp simp: id_bar'_def)
  by (fastforce)

thm id_bar_inf

lemma var_merge: "S \<subseteq> S' \<Longrightarrow>  (S :: 'c set) :\<^sub>s ((S' :: 'c set) :\<^sub>s  c) = (S :\<^sub>s c) "
  apply (clarsimp simp: var_frame_set'_def guar_merge conj_assoc[symmetric])
  apply (clarsimp simp: id_bar_inf )
  sledgehammer
  using id_bar_inf id_bar_inf' by force
  apply (fastforce)

sublocale tuple_system "UNIV :: 'c set set" "UNIV :: ('c, 'a) scoped set" d "\<lambda>x. Scoped (snd x) (v (fst x))"
  apply (standard; clarsimp)
   apply (rule_tac x="Scoped (d x \<union> d y) (var_frame_set' (d x) (v x) \<squnion> var_frame_set' (d y) (v x))" in exI)
   apply (intro conjI)
     apply (clarsimp)
    apply (rule scoped_eqI, clarsimp)
    apply (clarsimp simp: var_frame_distrib var_frame_idemp[symmetric])
    apply (clarsimp simp: var_frame_set'_def guar_merge conj_assoc[symmetric] id_bar_inf)
    apply (subst sup.absorb_iff1[symmetric])
    apply (fold var_frame_set'_def)
    apply (rule var_frame_mono)
     apply (blast)
    apply (blast)
    apply (rule scoped_eqI, clarsimp)

apply (clarsimp simp: var_frame_distrib var_frame_idemp[symmetric])
    apply (clarsimp simp: var_frame_set'_def guar_merge conj_assoc[symmetric] id_bar_inf)
    apply (subst sup.absorb_iff2[symmetric])
    apply (fold var_frame_set'_def)
    apply (rule var_frame_mono)
     apply (blast)
   apply (blast)
  by (rule_tac x="Scoped W (v x)" in exI, clarsimp)
  


definition "chaos U = (U, chaos_pre.functor_of.fobj U)" 

definition "d = fst"

primrec down where "down (x, v) = (v, chaos_pre.functor_of.farr (v, fst x) `` snd x)"


  find_theorems Sup conj
  apply (

  
  find_theorems name:SUP "_ \<le> \<Squnion> _"
  apply (rule SUP_upper)




  find_theorems gfp Inf
            apply simp  
 apply (clarsimp simp: scoped_ref_def sup_scoped_def var_frame_set'_def)
           apply (rule order_trans[rotated])
            apply (erule (1) sup_least)
           apply (subst conj_commute)
           apply (subst conj.nondet_sync_distrib)
           apply (rule semilattice_sup_class.sup_mono)
            apply (subst conj_commute)
             apply (rule conj.sync_mono, rule guar_strengthen)
  apply (clarsimp simp: id_bar'_def)


  

  find_theorems sup name: mono

  thm conj.nondet_sync_distrib
  find_theorems sup conj

 apply (clarsimp simp: scoped_ref_def inf_scoped_def)

             apply (clarsimp simp: var_frame_set'_def)
             apply (rule order_trans)
              apply (erule (1) inf_greatest)
             apply (rule order_trans, rule conj_to_inf)
  find_theorems "iter _ \<sqinter> iter _"
  find_theorems  conj inf
apply (rule conj.sync_mono)
  apply (intro conjI; clarsimp?)


definition "nats = lfp (\<lambda>S. {0} \<union> Suc ` S)"

definition "nats' = gfp (\<lambda>S. {0} \<union> Suc ` S)"

declare [[show_sorts=false]] [[show_types=false]]


lemma "UNIV = nats'"
  unfolding nats'_def
  apply (rule antisym)
   apply (rule coinduct)
    apply (clarsimp simp: mono_def)
    apply (clarsimp simp: image_iff)
  apply blast
   apply (clarsimp)
    apply (clarsimp simp: image_iff)
   apply (meson old.nat.exhaust)
  apply (clarsimp)
  done



definition normal :: "'a set \<Rightarrow> 'a set" where
 "normal P = {c. \<exists>t t' M. (\<forall>m\<in>M. snd m \<in> P) \<and>  c = assert t ; (test t' \<squnion> (\<Squnion>m\<in>M. \<alpha> (fst m) ; snd m))}"


term "gfp normal"

thm infiter_induct
term "gfp"
term " (\<lambda>f. fst (g a) \<parallel> fst (g b) ; f (snd (g a)) (snd (g b)))" 

lemma mono_preserves: "mono normal"
  apply (clarsimp intro!: monoI simp: normal_def)
  apply (rule_tac x=t in exI)
  apply (rule_tac x=t' in exI)
  apply (rule_tac x=M in exI)
  apply (clarsimp)
  apply (frule (1) bspec, clarsimp)
  apply (blast)
  done

lemma normal_form: "UNIV = gfp normal" sorry

lemma is_normal: "x \<in> gfp normal"
  by (clarsimp simp: normal_form[symmetric])


lemma "a \<parallel> b = c"
  apply (insert is_normal[where x=a], clarsimp simp: gfp_def)
  apply (frule_tac c=a in subsetD, clarsimp)
  apply (subst (asm) normal_def) back
  apply (clarsimp)

apply (insert is_normal[where x=b], clarsimp simp: gfp_def)
  apply (frule_tac c=b in subsetD, clarsimp)
  apply (subst (asm) normal_def) back back back back
  apply (clarsimp)
  find_theorems assert par
  apply (clarsimp simp: par.assert_distrib[symmetric])
  apply (subst par_commute)
  apply (clarsimp simp: par.assert_distrib[symmetric])
  apply (subst seq_assoc[symmetric])
  apply (clarsimp simp: assert_seq_assert)
  find_theorems par sup
  find_theorems assert seq
  apply (clarsimp)

term Ball
thm gfp_ordinal_induct[OF mono_preserves, simplified normal_form[symmetric], simplified, where P="\<lambda>S. Ball S P", simplified, THEN spec]


lemma "UNIV \<subseteq> S \<longleftrightarrow> S = UNIV"

lemmas normal_induct = gfp_ordinal_induct[OF mono_preserves, simplified normal_form[symmetric], simplified, where P="\<lambda>S. Ball S P" for P, simplified, THEN spec, simplified order_top_class.top_unique, simplified]




  apply (rule antisym, clarsimp?)



(*
For completeness
lemma "restrict_range UNIV p = range_restriction p" (= {(\<sigma>, \<sigma>'). p \<in> \<sigma>'} as in the paper)
proof -
  have "restrict_range UNIV p = UNIV \<inter> range_restriction p" unfolding restrict_range_def by simp
  also have "... = range_restriction p"
    by simp
  finally show ?thesis .
qed
*)

definition inv :: "'b set \<Rightarrow> 'a" where
  "inv p \<equiv> \<alpha>(UNIV \<triangleright> p)\<^sup>\<omega>"

lemma inv_strengthen:
  assumes "p\<^sub>1 \<supseteq> p\<^sub>2"
  shows "inv p\<^sub>1 \<ge> inv p\<^sub>2"
proof -
  have "UNIV \<triangleright> p\<^sub>1 \<ge> UNIV \<triangleright> p\<^sub>2"
    by (simp add: assms range_restrict_p_mono)
  then have "\<alpha>(UNIV \<triangleright> p\<^sub>1) \<ge> \<alpha>(UNIV \<triangleright> p\<^sub>2)"
    using general_atomic.hom_mono by auto
  then have "\<alpha>(UNIV \<triangleright> p\<^sub>1)\<^sup>\<omega> \<ge> \<alpha>(UNIV \<triangleright> p\<^sub>2)\<^sup>\<omega>"
    using iter_mono by auto
  then show ?thesis using inv_def by simp
qed

lemma inv_introduce: "c \<ge> inv p \<iinter> c"
proof -
  have inv_chaos: "inv UNIV = chaos"
    by (simp add: restrict_range_def inv_def Atomic_def2 general_atomic_def env.Hom_def pgm.Hom_def 
        chaos_def)
  have "c = chaos \<iinter> c" by simp
  also have "... = inv UNIV \<iinter> c" using inv_chaos by simp
  also have "... \<ge> inv p \<iinter> c"
    using conj.sync_mono_left inv_strengthen by auto
  finally show ?thesis .
qed

lemma guarded_inv:      
  "\<tau>(p);(\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>) = \<tau>(p);(\<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p)\<^sup>\<omega>)"
proof -
  have "-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p \<supseteq> (p \<triangleleft> UNIV) \<inter> UNIV \<triangleright> p" by auto
  then have "\<tau>(p);(\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>) \<ge> \<tau>(p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega>"
    by (simp add: iter_mono seq_mono_right)
  also have "... \<ge> \<tau>(p);(\<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p)\<^sup>\<omega>)"
    by (simp add: iter_mono le_infI2 seq_mono_right)
  then have left_right:"\<tau>(p);(\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>) \<ge> \<tau>(p);(\<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p)\<^sup>\<omega>)".
  have helper: "nil \<squnion> \<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p);\<tau>(p);\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega> \<ge> \<tau>(p);\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>"
  proof -
    have "nil \<squnion> \<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p);\<tau>(p);\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega> \<ge> 
        \<tau>(p) \<squnion> \<alpha>(p \<triangleleft> UNIV \<inter> (-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p));\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>" (is "_ \<ge> ?rhs")
    proof -
      have absorb: "\<And>r p. \<alpha>(r \<inter> (UNIV \<triangleright> p));\<tau>(p) = \<alpha>(r \<inter> (UNIV \<triangleright> p))" 
        by (metis general_atomic_test_post inf_top.left_neutral restrict_range_def)
      have negate: "p \<triangleleft> UNIV \<inter> (-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p) = p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p"
        by (simp add: inf_sup_distrib1)
      have "nil \<squnion> \<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p);\<tau>(p);\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega> \<ge> 
              \<tau>(p) \<squnion> \<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p);\<tau>(p);\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>" (is "_ \<ge> ?rhs")
        using nil_ref_test sup.mono by fastforce
      also have "?rhs = \<tau>(p) \<squnion> \<alpha>(p \<triangleleft> UNIV \<inter> (-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p));\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>"
        using absorb negate by auto
      finally show ?thesis.
    qed
    also have "?rhs = \<tau>(p) \<squnion> \<tau>(p) ; \<alpha>(- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p);\<alpha> (- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p)\<^sup>\<omega>"
      using atomic_pull_test by presburger
    also have "... = \<tau>(p);(nil \<squnion> \<alpha>(- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p);\<alpha> (- p \<triangleleft> UNIV \<union> UNIV \<triangleright> p)\<^sup>\<omega>)"
      using par.seq_nondet_distrib seq_assoc seq_nil_right by presburger
    also have "... = \<tau>(p);\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>"
      using iter_unfold by auto
    finally show ?thesis.
  qed
  then have right_left: "\<tau>(p);(\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>) \<le> \<tau>(p);(\<alpha>(p \<triangleleft> UNIV \<inter> UNIV \<triangleright> p)\<^sup>\<omega>)"
    using iter_induct_nil seq_assoc test_seq_refine by auto 
  finally show ?thesis using right_left left_right by auto
qed

lemma guarded_inv2: "\<tau>(p);(\<alpha>(-(p \<triangleleft> UNIV) \<union> UNIV \<triangleright> p)\<^sup>\<omega>) = \<tau>(p);inv(p)"
  by (metis general_atomic_test_post atomic_pull_test guarded_inv local.inv_def par.iter_leapfrog seq_assoc test_seq_idem)

lemma inv_preserve: "\<tau>(p);(inv p) = \<tau>(p);(inv p);\<tau>(p)"
proof -
  have "\<tau>(p);(inv p) = \<tau>(p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega>" unfolding inv_def by simp
  also have "... = \<tau>(p);(\<alpha>(UNIV \<triangleright> p);\<tau>(p))\<^sup>\<omega>" using general_atomic_test_post by auto
  also have "... = (\<tau>(p);\<alpha>(UNIV \<triangleright> p))\<^sup>\<omega> ; \<tau>(p) ; \<tau>(p)"
    using par.iter_leapfrog test_seq_idem seq_assoc by auto
  also have "... = \<tau>(p);(\<alpha>(UNIV \<triangleright> p) ; \<tau>(p))\<^sup>\<omega> ; \<tau>(p)"
    using par.iter_leapfrog by auto
  also have "... = \<tau>(p);(inv p);\<tau>(p)" using general_atomic_test_post inv_def by auto
  finally show ?thesis .
qed

lemma inv_maintain: "\<tau>(p);(inv p \<iinter> c) = \<tau>(p);(inv p \<iinter> c);\<tau>(p)"
proof -
  have a: "\<tau>(p);(inv p \<iinter> c) = \<tau>(p);inv p \<iinter> \<tau>(p);c"
    using test_conj_distrib by simp
  also have b: "... = \<tau>(p);(inv p);\<tau>(p) \<iinter> \<tau>(p);c"
    using inv_preserve by auto
  also have "... = (\<tau>(p);(inv p) \<iinter> \<tau>(p);c);\<tau>(p)"
    using conj.test_sync_post local.conj_commute by simp
  also have c: "... = \<tau>(p);(inv p \<iinter> c);\<tau>(p)" using a by simp
  finally show ?thesis .
qed

lemma inv_distrib_Nondet: "inv p \<iinter> (\<Squnion>C) = (\<Squnion>c \<in> C. (inv p \<iinter> c))"
  using conj_Nondet_distrib_nonaborting inv_introduce by force

lemma inv_distrib_nondet: "inv p \<iinter> (c \<squnion> d) = (inv p \<iinter> c) \<squnion> (inv p \<iinter> d)"
  using conj.sync_nondet_distrib by simp


lemma iter_conj_conj_distrib_left: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<ge> (c\<^sup>\<omega> \<iinter> d)\<^sup>\<omega>"
  oops  
  by (simp add: iter0 iter_conj_distrib)

lemma iter_conj_par_distrib: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<ge> (c \<iinter> d)\<^sup>\<omega>"
  oops
proof -
  have a: "c\<^sup>\<omega> \<ge> c" by (metis iter1)
  have b: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<ge> (c\<^sup>\<omega> \<iinter> d)\<^sup>\<omega>" by (metis iter_conj_conj_distrib_left)
  have "c\<^sup>\<omega> \<iinter> d \<ge> c \<iinter> d" using a 
    by (simp add: conj.sync_mono_left)
  thus ?thesis using a b by (metis refine_trans iter_mono) 
qed


notation conj (infixl "\<oplus>" 40) 

lemma iter_seq_split: "((iter a) \<oplus> (c ; d)) =
       ((iter a \<oplus> (((c \<oplus> fiter Atomic) ; d))) \<squnion> (iter a \<oplus> ((c \<oplus> infiter Atomic)) ; d))"
  apply (subst conj_chaos[where a=c, symmetric])
  using chaos_def conj.sync_nondet_distrib nondet_seq_distrib par.iter_isolation by presburger

lemma conj_inf_abort: "(c \<oplus> infiter s) = (c \<oplus> infiter s) ; top"
  by (metis assert_bot conj.test_sync_post_helper1 infiter_iter_magic test.hom_bot)

lemma conj_inf_annihilate:
"(c \<oplus> infiter s) ; d = (c \<oplus> infiter s)"
  by (metis conj_inf_abort seq_abort seq_assoc)

lemma "a = atomic s \<Longrightarrow> (iter a \<oplus> ((c \<oplus> infiter Atomic) ; d)) = (infiter a \<oplus> c) ;  (iter a \<oplus> d) "
  apply (subst conj_inf_annihilate)
  by (metis (no_types, lifting) conj.comm.left_commute conj.test_sync_post
                conj_id conj_inf_annihilate infiter_iter_magic test.hom_bot)

declare guar_def[simp del]
declare rely_def[simp del]
declare dem_def[simp del]

declare [[show_types=false]][[show_sorts=false]]


lemma inf_helper: "(\<Sqinter> M \<oplus> a) \<le> (\<Sqinter> ((conj a) ` M))"
  apply (subst le_Inf_iff, clarsimp)
  by (metis Inf_lower conj.sync_mono_right local.conj_commute)

lemma gfp_ordinal_induct_top:
  fixes f :: "'x::complete_lattice \<Rightarrow> 'x"
  assumes mono: "mono f"
    and P_f: "\<And>S. P S \<Longrightarrow> gfp f \<le> S \<Longrightarrow> P (f S)"
    and P_Union: "\<And>M. M \<noteq> {} \<Longrightarrow> \<forall>S\<in>M. P S \<Longrightarrow> P (Inf M)"
    and P_top: "{S. gfp f \<le> S \<and> P S} \<noteq> {}"
  shows "P (gfp f)"
proof -
  let ?M = "{S. gfp f \<le> S \<and> P S}"
  from P_Union have "P (Inf ?M)" 
    apply (case_tac "{S. gfp f \<le> S \<and> P S} = {}")
    using P_top apply auto[1]
    apply (clarsimp)
    done
  also have "Inf ?M = gfp f"
  proof (rule antisym)
    show "gfp f \<le> Inf ?M"
      by (blast intro: Inf_greatest)
    then have "f (gfp f) \<le> f (Inf ?M)"
      by (rule mono [THEN monoD])
    then have "gfp f \<le> f (Inf ?M)"
      using mono [THEN gfp_unfold] by simp
    then have "f (Inf ?M) \<in> ?M"
      using P_Union 
      using P_f \<open>gfp f \<le> \<Sqinter> {S. gfp f \<le> S \<and> P S}\<close> calculation by blast
    then have "Inf ?M \<le> f (Inf ?M)"
      by (rule Inf_lower)
    then show "Inf ?M \<le> gfp f"
      by (rule gfp_upperbound)
  qed
  finally show ?thesis .
qed




lemma conj_bot_bot: "conj bot x = conj bot x ; y"
  by (metis antisym seq_abort seq_abort_conj seq_abort_right seq_assoc seq_magic_left)
   

lemma inv_distrib_seq: "inv p \<iinter> (c ; d) = (inv p \<iinter> c) ; (inv p \<iinter> d)"
proof -
  have "inv p \<iinter> (c ; d) \<ge> (inv p \<iinter> c) ; (inv p \<iinter> d)"
    using iter_seq_iter local.inv_def seq_conj_interchange by metis
  moreover have "(inv p \<iinter> c) ; (inv p \<iinter> d) \<ge> inv p \<iinter> (c ; d) "
    using inv_dist_over_Inf oops
  ultimately show ?thesis by simp
qed

lemma general_distrib_conj: "a\<^sup>\<omega> \<iinter> (c \<iinter> d) = (a\<^sup>\<omega> \<iinter> c) \<iinter> (a\<^sup>\<omega> \<iinter> d)"
  using conj_conj_distrib_left by auto

lemma inv_distrib_test: "inv p \<iinter> \<tau>(p\<^sub>1) = \<tau>(p\<^sub>1)"
  by (metis (no_types, lifting) conj.sync_nondet_distrib conj.test_sync_nil inv_introduce iter0
      le_iff_sup local.conj_commute local.inv_def sup.order_iff)

lemma inv_distrib_assert: "inv p \<iinter> \<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
  by (metis conj.nil_sync_assert inv_distrib_test local.conj_assoc test_sequential_pre.test_top 
      test_sequential_pre_axioms)

lemma inv_distrib_pgm: "inv p \<iinter> \<pi>(r) = \<pi>(r \<triangleright> p)"
proof -
  have "inv p \<iinter> \<pi>(r) = (\<alpha>(UNIV \<triangleright> p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<squnion> nil) \<iinter> \<pi>(r)"
    unfolding inv_def using iter_unfold sup.commute by metis
  also have "... = \<alpha>(UNIV \<triangleright> p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> \<pi>(r) \<squnion> nil \<iinter> \<pi>(r)"
    by (simp add: conj.nondet_sync_distrib)
  also have "... = \<alpha>(UNIV \<triangleright> p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> atomic(r, \<bottom>) \<squnion> nil \<iinter> \<pi>(r)" 
    using atomic_def by auto
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> atomic(r, \<bottom>) \<squnion> nil \<iinter> \<pi>(r)" 
    using seq_iter_conj atomic_general_atomic by metis
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> \<pi>(r) \<squnion> nil \<iinter> \<pi>(r)" using atomic_def
    by simp
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> \<pi>(r) \<squnion> \<bottom>"
    by (metis conj.nil_sync_atomic_pre pgm_atomic seq_nil_right)
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> \<pi>(r)" by auto
  also have "... = \<pi>(r \<triangleright> p)"
    by (simp add: general_atomic_def conj.sync_nondet_distrib local.conj_commute pgm_conj_env pgm_conj_pgm restrict_range_def)
  finally show ?thesis.
qed

lemma inv_distrib_env: "inv p \<iinter> \<epsilon>(r) = \<epsilon>(r \<triangleright> p)"
proof -
  have "inv p \<iinter> \<epsilon>(r) = (\<alpha>(UNIV \<triangleright> p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<squnion> nil) \<iinter> \<epsilon>(r)"
    unfolding inv_def using iter_unfold sup.commute by metis
  also have "... = \<alpha>(UNIV \<triangleright> p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> \<epsilon>(r) \<squnion> nil \<iinter> \<epsilon>(r)"
    by (simp add: conj.nondet_sync_distrib)
  also have "... = \<alpha>(UNIV \<triangleright> p);\<alpha>(UNIV \<triangleright> p)\<^sup>\<omega> \<iinter> atomic(\<bottom>, r) \<squnion> nil \<iinter> \<epsilon>(r)"
    using atomic_def by auto
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> atomic(\<bottom>, r) \<squnion> nil \<iinter> \<epsilon>(r)"
    using seq_iter_conj atomic_general_atomic by metis
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> \<epsilon>(r) \<squnion> nil \<iinter> \<epsilon>(r)" unfolding atomic_def by simp
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> \<epsilon>(r) \<squnion> \<bottom>"
    by (metis conj.nil_sync_atomic_pre env_atomic seq_nil_right)
  also have "... = \<alpha>(UNIV \<triangleright> p) \<iinter> \<epsilon>(r)" by auto
  also have "... = \<epsilon>(r \<triangleright> p)"
    by (simp add: general_atomic_def inf_commute pgmenv_conj_env restrict_range_def)
  finally show ?thesis.
qed

lemma inv_distrib_atomic: "inv p \<iinter> \<alpha>(r) = \<alpha>(r \<triangleright> p)"
  using inv_distrib_pgm inv_distrib_env by (simp add: general_atomic_def conj.sync_nondet_distrib)

lemma inv_distrib_lfp:
  assumes "mono G"
  shows "inv p \<iinter> lfp (\<lambda>x. G x) = lfp (\<lambda>x. inv p \<iinter> G x)"
proof -
  have H_mono: "mono (\<lambda>x. inv p \<iinter> G(x))"
    unfolding mono_def using assms conj.sync_mono_right mono_def by blast 
  have F_dist: "dist_over_nondet (\<lambda>x. inv p \<iinter> x)"
    by (simp add: inv_distrib_Nondet)
  have comp: "\<And>x. (((\<lambda>x. inv p \<iinter> x) \<circ> G) x = 
                ((\<lambda>x. inv p \<iinter> G(x)) \<circ> (\<lambda>x. inv p \<iinter> x)) x)"
    apply (auto simp add:comp_def)
    sorry
  have "(\<lambda>x. inv p \<iinter> x) (lfp G) = (lfp (\<lambda>x. inv p \<iinter> G(x)))"
    using H_mono F_dist assms comp fusion_lfp_eq by blast
  then show ?thesis by simp
qed


lemma inv_distrib_gfp: 
  assumes "mono G"
  shows "inv p \<iinter> gfp (\<lambda>x. G x) = gfp (\<lambda>x. inv p \<iinter> G x)"
proof-
  have H_mono: "mono (\<lambda>x. inv p \<iinter> G(x))"
    unfolding mono_def using assms conj.sync_mono_right mono_def by blast 
  have F_dist: "dist_over_inf (\<lambda>x. inv p \<iinter> x)"
    by (simp add: inv_dist_over_Inf)
  have comp: "\<And>x. (((\<lambda>x. inv p \<iinter> x) \<circ> G) x = 
                ((\<lambda>x. inv p \<iinter> G(x)) \<circ> (\<lambda>x. inv p \<iinter> x)) x)"
    apply (auto simp add:comp_def)
    sorry
  have "(\<lambda>x. inv p \<iinter> x) (gfp G) = (gfp (\<lambda>x. inv p \<iinter> G(x)))"
    using H_mono F_dist assms comp fusion_gfp_eq by blast
  then show ?thesis by simp
qed

lemma finite_iter_distrib: "inv p \<iinter> c\<^sup>\<star> = (inv p \<iinter> c)\<^sup>\<star>"
proof -
  have H_mono: "mono (\<lambda>x. nil \<squnion> (inv p \<iinter> c);x)"
    unfolding mono_def by (meson nondet_mono_right seq_mono_right)
  have G_mono: "mono (\<lambda>x. nil \<squnion> c;x)"
    unfolding mono_def  by (meson nondet_mono_right seq_mono_right)
  have F_dist: "dist_over_nondet (\<lambda>x. inv p \<iinter> x)"
    by (simp add: inv_distrib_Nondet)
  have comp: "\<And>x. (((\<lambda>x. inv p \<iinter> x) \<circ> (\<lambda>x. nil \<squnion> c;x)) x = 
                ((\<lambda>x. nil \<squnion> (inv p \<iinter> c);x) \<circ> (\<lambda>x. inv p \<iinter> x)) x)"
    apply(auto simp add: comp_def)
    apply(auto simp add: inv_distrib_nondet inv_distrib_seq) (* inv_distrib_seq unproved *)
    using inv_distrib_test by (metis test_sequential_pre.test_top test_sequential_pre_axioms)
  have "(\<lambda>x. inv p \<iinter> x) (lfp (\<lambda>x. nil \<squnion> c;x)) = (lfp (\<lambda>x. nil \<squnion> (inv p \<iinter> c);x))"
    using H_mono G_mono F_dist comp fusion_lfp_eq by blast
  then show ?thesis using fiter_def by simp
qed

lemma iter_distrib: "inv p \<iinter> c\<^sup>\<omega> = (inv p \<iinter> c)\<^sup>\<omega>"
proof -
  have H_mono: "mono (\<lambda>x. nil \<squnion> (inv p \<iinter> c);x)"
    unfolding mono_def by (simp add: seq_mono_right sup.coboundedI2)
  have G_mono: "mono (\<lambda>x. nil \<squnion> c;x)"
    unfolding mono_def by (simp add: seq_mono_right sup.coboundedI2)
  have comp: "\<And>x. (((\<lambda>x. inv p \<iinter> x) \<circ> (\<lambda>x. nil \<squnion> c;x)) x = 
                ((\<lambda>x. nil \<squnion> (inv p \<iinter> c);x) \<circ> (\<lambda>x. inv p \<iinter> x)) x)"
    apply(auto simp add: comp_def)
    apply(auto simp add: inv_distrib_nondet inv_distrib_seq) (* inv_distrib_seq unproved *)
    using inv_distrib_test by (metis test_sequential_pre.test_top test_sequential_pre_axioms)
  have "(\<lambda>x. inv p \<iinter> x) (gfp (\<lambda>x. nil \<squnion> c;x)) = (gfp (\<lambda>x. nil \<squnion> (inv p \<iinter> c);x))"
    using H_mono G_mono inv_dist_over_Inf comp fusion_gfp_eq by blast
  then show ?thesis using iter_def by simp
qed

lemma atomic_par_conj: "\<And>c. \<alpha>(r)\<^sup>\<omega> \<iinter> c = \<epsilon>(r)\<^sup>\<omega> \<parallel> c" sorry

lemma promise_distrib:
  "\<alpha>(r)\<^sup>\<omega> \<iinter> (c \<parallel> d) = (\<alpha>(r)\<^sup>\<omega> \<iinter> c) \<parallel> (\<alpha>(r)\<^sup>\<omega> \<iinter> d)"
proof -
  have "\<alpha>(r)\<^sup>\<omega> \<iinter> (c \<parallel> d) = \<epsilon>(r)\<^sup>\<omega> \<parallel> (c \<parallel> d)"
    using atomic_par_conj by simp
  also have "... = \<epsilon>(r)\<^sup>\<omega> \<parallel> \<epsilon>(r)\<^sup>\<omega> \<parallel> c \<parallel> d"
  proof -
    have "\<epsilon>(r)\<^sup>\<omega> \<parallel> (c \<parallel> d) = (\<epsilon>(r) \<parallel> \<epsilon>(r))\<^sup>\<omega> \<parallel> (c \<parallel> d)"
      using env_par_env_axiom by simp
    also have "... = \<epsilon>(r)\<^sup>\<omega> \<parallel> \<epsilon>(r)\<^sup>\<omega> \<parallel> c \<parallel> d"
      by (smt atomic_par_conj calculation conj.comm.left_commute conj.idem local.conj_commute par_assoc)
    finally show ?thesis.
  qed
  also have "... = (\<epsilon>(r)\<^sup>\<omega> \<parallel> c) \<parallel> (\<epsilon>(r)\<^sup>\<omega> \<parallel> d)"
    using par_assoc par_commute by auto
  also have "... = (\<alpha>(r)\<^sup>\<omega> \<iinter> c) \<parallel> (\<alpha>(r)\<^sup>\<omega> \<iinter> d)"
    using atomic_par_conj by simp
  finally show ?thesis .
qed

lemma inv_lib_no_interference:
  assumes "id_set{|x,y|} \<triangleright> p \<subseteq> p \<triangleleft> UNIV"
  shows "E\<^sup>C\<^sub>x(\<tau>(p);(demand (id x) \<iinter> inv p)) \<iinter> demand (id y) \<ge> \<tau>(E\<^sup>S\<^sub>x p);inv(E\<^sup>S\<^sub>x p) \<iinter> demand (id y)"
  sorry

lemma merge_iteration: "(\<pi>(s \<inter> s') \<squnion> \<epsilon>(r \<inter> r'))\<^sup>\<omega> = (\<pi>(s) \<squnion> \<epsilon>(r))\<^sup>\<omega> \<iinter> (\<pi>(s') \<squnion> \<epsilon>(r'))\<^sup>\<omega>"
  by (metis conj.atomic_iter_sync_iter pgm_or_env_atomic pgmenv_conj_pgmenv)

lemma union_helper: "{(s, s'). p(s)} \<union> {(s, s'). p'(s')} = {(s, s'). p(s) \<or> p'(s')}"
  by blast 

lemma inv_lib_constrained_interference:
  assumes "(-((E\<^sup>S\<^sub>x p) \<triangleleft> UNIV)) \<union> UNIV \<triangleright> (E\<^sup>S\<^sub>x p) \<supseteq> (id y)"
  shows "\<tau>(E\<^sup>S\<^sub>x p);(inv(E\<^sup>S\<^sub>x p) \<iinter> demand (id y)) = \<tau>(E\<^sup>S\<^sub>x p);(guar_inv(E\<^sup>S\<^sub>x p) \<iinter> demand (id y))"
proof -
  have "\<tau>(E\<^sup>S\<^sub>x p);(inv(E\<^sup>S\<^sub>x p) \<iinter> demand (id y)) = \<tau>(E\<^sup>S\<^sub>x p);((\<alpha>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p)\<^sup>\<omega>) \<iinter> demand (id y))"
    using guarded_inv2 conj_mono by (simp add: test_conj_distrib)
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<alpha>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p)\<^sup>\<omega>) \<iinter> (\<epsilon>(id y) \<squnion> Pgm)\<^sup>\<omega>)"
    using dem_def restrict_def by auto                                                                           
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);(((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> \<epsilon>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p))\<^sup>\<omega>) \<iinter> (\<epsilon>(id y) \<squnion> Pgm)\<^sup>\<omega>)"
    unfolding general_atomic_def by auto
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);(((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> \<epsilon>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p))\<^sup>\<omega>) \<iinter> (\<epsilon>(id y) \<squnion> \<pi>(UNIV))\<^sup>\<omega>)"
    by (simp add: pgm.Hom_def)
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<pi>((-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<inter> UNIV) \<squnion> \<epsilon>((-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<inter> (id y))))\<^sup>\<omega>"
    by (metis conj.atomic_iter_sync_iter inf_sup_aci(5) pgm_or_env_atomic pgmenv_conj_pgmenv sup_commute)
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> \<epsilon>(id y)))\<^sup>\<omega>"
    using assms by (simp add: inf.absorb_iff2)
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<pi>((-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<inter> UNIV) \<squnion> \<epsilon>(UNIV \<inter> (id y))))\<^sup>\<omega>"
    by simp
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> \<epsilon>(UNIV))\<^sup>\<omega> \<iinter> (\<pi>(UNIV) \<squnion> \<epsilon>(id y))\<^sup>\<omega>)"
    using merge_iteration by presburger
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> Env)\<^sup>\<omega> \<iinter> (Pgm \<squnion> \<epsilon>(id y))\<^sup>\<omega>)"
    by (simp add: env.Hom_def pgm.Hom_def)
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> Env)\<^sup>\<omega> \<iinter> demand (id y))"
    by (metis inf_sup_aci(5) restrict_def restrict_demand)
  also have "... = \<tau>(E\<^sup>S\<^sub>x p);(guar_inv (E\<^sup>S\<^sub>x p) \<iinter> demand (id y))"
  proof -
    have negate_set_helper: "-{(s, s'). s \<in> (E\<^sup>S\<^sub>x p)} = {(s, s'). s \<notin> (E\<^sup>S\<^sub>x p)}"  by blast
    have "\<tau>(E\<^sup>S\<^sub>x p);((\<pi>(-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p) \<squnion> Env)\<^sup>\<omega> \<iinter> demand (id y))
          = \<tau>(E\<^sup>S\<^sub>x p);((guar(-{(s, s'). s \<in> (E\<^sup>S\<^sub>x p)} \<union> {(s, s'). s' \<in> (E\<^sup>S\<^sub>x p)})) \<iinter> demand (id y))"
      sorry
     (* by (simp add: restrict_domain_def restrict_range_def) *)
    also have "... = \<tau>(E\<^sup>S\<^sub>x p);((guar({(s, s'). -(s \<in> (E\<^sup>S\<^sub>x p))} \<union> {(s, s'). s' \<in> (E\<^sup>S\<^sub>x p)})) \<iinter> demand (id y))"
      by (simp add: negate_set_helper)
    also have "... = \<tau>(E\<^sup>S\<^sub>x p);((guar({(s, s'). -(s \<in> (E\<^sup>S\<^sub>x p)) \<or> s' \<in> (E\<^sup>S\<^sub>x p)})) \<iinter> demand (id y))"
      by (simp add: union_helper) 
    also have "... = \<tau>(E\<^sup>S\<^sub>x p);((guar_inv(E\<^sup>S\<^sub>x p)) \<iinter> demand (id y))"
      using guar_inv_def by auto
    finally show ?thesis.
  qed
  finally show ?thesis.
qed

lemma inv_distrib_par: "inv p \<iinter> (c \<parallel> d) = (inv p \<iinter> c) \<parallel> (inv p \<iinter> d)"
  unfolding inv_def using promise_distrib by auto

end

locale data_refines = coupling_inv
begin

definition data_refines :: "'a \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<ge>\<^sub>_ _" 50) where
  "data_refines c p d \<equiv> \<tau>(p);(inv p \<iinter> c) \<ge> \<tau>(p);(inv p \<iinter> d)"

lemma dataref_trans :
  assumes "a \<ge>\<^sub>p b"
      and "b \<ge>\<^sub>p c"
    shows "a \<ge>\<^sub>p c"
proof -
  have "\<tau>(p);(inv p \<iinter> a) \<ge> \<tau>(p);(inv p \<iinter> b)" (is "... \<ge> ?rhs")
    using assms(1) data_refines_def by blast
  also have "?rhs \<ge> \<tau>(p);(inv p \<iinter> c)"
    using assms(2) data_refines_def xtrans by blast
  finally show ?thesis
    by (simp add: data_refines_def)
qed

(* Data refining program operators *)


lemma dataref_Nondet:
  assumes "\<forall>d\<in>D. \<exists>c\<in>C. (c \<ge>\<^sub>p d)"
  shows "\<Squnion>C \<ge>\<^sub>p \<Squnion>D"
proof -
  have "\<tau>(p);(inv p \<iinter> (\<Squnion>C)) = (\<Squnion>c\<in>C. \<tau>(p);(inv p \<iinter> c))"
    using inv_distrib_Nondet by (metis Sup_empty empty_is_image par.seq_NONDET_distrib test_seq_magic) 
  also have "... \<ge> (\<Squnion>d\<in>D. \<tau>(p);(inv p \<iinter> d))" (is "... \<ge> ?rhs")
    using assms data_refines_def by (simp add: SUP_mono)
  also have "?rhs = \<tau>(p);(inv p \<iinter> (\<Squnion>D))" 
    using inv_distrib_Nondet by (metis Sup_empty empty_is_image par.seq_NONDET_distrib test_seq_magic)
  finally show ?thesis using data_refines_def by simp
qed

lemma dataref_nondet:
  assumes "c\<^sub>1 \<ge>\<^sub>p d\<^sub>1" and "c\<^sub>2 \<ge>\<^sub>p d\<^sub>2"
  shows "c\<^sub>1 \<squnion> c\<^sub>2 \<ge>\<^sub>p d\<^sub>1 \<squnion> d\<^sub>2"
proof -
  let ?C = "{c\<^sub>1, c\<^sub>2}"
  let ?D = "{d\<^sub>1, d\<^sub>2}"
  have "\<forall>d\<in>?D. \<exists>c\<in>?C. (c \<ge>\<^sub>p d)"
    using assms conj.sync_mono local.data_refines_def seq_mono by auto
  moreover have "\<Squnion>?C \<ge>\<^sub>p \<Squnion>?D"
    using dataref_Nondet calculation by blast
  ultimately show ?thesis by simp
qed

lemma dataref_seq_distrib: "\<tau>(p);(inv p \<iinter> (c;d)) = \<tau>(p);(inv p \<iinter> c);\<tau>(p);(inv p \<iinter> d)"
    using inv_distrib_seq inv_maintain seq_assoc by metis

lemma dataref_seq:
  assumes "c\<^sub>1 \<ge>\<^sub>p d\<^sub>1" and "c\<^sub>2 \<ge>\<^sub>p d\<^sub>2"
  shows "c\<^sub>1;c\<^sub>2 \<ge>\<^sub>p d\<^sub>1;d\<^sub>2"
proof -
  have "\<tau>(p);(inv p \<iinter> c\<^sub>1;c\<^sub>2) = \<tau>(p);(inv p \<iinter> c\<^sub>1);\<tau>(p);(inv p \<iinter> c\<^sub>2)"
    using dataref_seq_distrib by auto
  also have "... \<ge> \<tau>(p);(inv p \<iinter> d\<^sub>1);\<tau>(p);(inv p \<iinter> d\<^sub>2)" (is "_ \<ge> ?rhs")
    using assms data_refines_def seq_assoc seq_mono by metis
  also have "?rhs = \<tau>(p);(inv p \<iinter> d\<^sub>1;d\<^sub>2)"
    using dataref_seq_distrib by auto
  finally show ?thesis using data_refines_def by simp
qed

lemma inv_test_finite_iter: "\<tau>(p);(inv p \<iinter> c)\<^sup>\<star> = \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
proof -
  have "\<tau>(p);(inv p \<iinter> c)\<^sup>\<star> \<ge> \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
    by (meson fiter_mono seq_mono_left seq_mono_right subsetI test.hom_mono test_seq_refine)
  moreover have "\<tau>(p);(inv p \<iinter> c)\<^sup>\<star> \<le> \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
  proof -
    have "(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star> \<ge> \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
      by (simp add: test_seq_refine)
    moreover have "(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star> \<ge> \<tau>(p) \<squnion> \<tau>(p);(inv p \<iinter> c);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
      using inv_maintain
      by (metis (no_types, lifting) calculation fiter_unfold par.seq_nondet_distrib seq_assoc seq_nil_right test_seq_idem) (* TODO *)

    moreover have "(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star> \<ge> \<tau>(p) \<squnion> \<tau>(p);(inv p \<iinter> c);\<lbrace>p\<rbrace>;(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
      by (metis calculation(2) inv_maintain seq_assoc test_seq_assert)
    moreover have "\<lbrace>p\<rbrace>;(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star> \<ge> nil \<squnion> (inv p \<iinter> c);\<lbrace>p\<rbrace>;(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
      using assert_galois_test calculation(3) seq_assoc test_nondet_distrib by auto
    ultimately show ?thesis
      by (metis assert_galois_test assert_seq_test fiter_induct_nil seq_assoc)
  qed
  ultimately show ?thesis by simp
qed

lemma dataref_finite_iter:
  assumes "c \<ge>\<^sub>p d"
  shows "c\<^sup>\<star> \<ge>\<^sub>p d\<^sup>\<star>"
proof -
  have "\<tau>(p);(inv p \<iinter> c\<^sup>\<star>) = \<tau>(p);(inv p \<iinter> c)\<^sup>\<star>"
    using finite_iter_distrib by simp
  also have "... = \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<star>"
    using inv_test_finite_iter by simp
  also have "... \<ge> \<tau>(p);(\<tau>(p);(inv p \<iinter> d))\<^sup>\<star>" (is "_ \<ge> ?rhs")
    using assms data_refines_def fiter_mono seq_mono_right by simp
  also have "?rhs = \<tau>(p);(inv p \<iinter> d)\<^sup>\<star>"
    using inv_test_finite_iter by simp
  also have "... = \<tau>(p);(inv p \<iinter> d\<^sup>\<star>)"
    using finite_iter_distrib by simp
  finally show ?thesis using data_refines_def by simp
qed

lemma inv_test_iter: "\<tau>(p);(inv p \<iinter> c)\<^sup>\<omega> = \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<omega>"
proof -
  have "\<tau>(p);(inv p \<iinter> c)\<^sup>\<omega> \<ge> \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<omega>"
    by (meson iter_mono order_refl seq_mono_right test_seq_refine)
  moreover have "\<tau>(p);(inv p \<iinter> c)\<^sup>\<omega> \<le> \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<omega>"
  proof -
    have "\<tau>(p);(inv p \<iinter> c)\<^sup>\<omega> \<ge> \<tau>(p);(inv p \<iinter> c)\<^sup>\<omega>"
      by simp
    moreover have "\<tau>(p) \<squnion> \<tau>(p);(inv p \<iinter> c);(inv p \<iinter> c)\<^sup>\<omega> \<ge> \<tau>(p);(inv p \<iinter> c)\<^sup>\<omega>"
      by (metis iter_unfold seq_assoc seq_nil_right test_nondet_distrib_weak)
    moreover have "nil \<squnion> \<tau>(p);(inv p \<iinter> c);\<tau>(p);(inv p \<iinter> c)\<^sup>\<omega> \<ge> \<tau>(p);(inv p \<iinter> c)\<^sup>\<omega>"
      using calculation
    proof -
      have "nil \<squnion> \<tau>(p);(inv p \<iinter> c);\<tau>(p);(inv p \<iinter> c)\<^sup>\<omega> \<ge> \<tau>(p) \<squnion> \<tau>(p);(inv p \<iinter> c);(inv p \<iinter> c)\<^sup>\<omega>"
        using inv_maintain nil_ref_test sup_mono by fastforce
      then show ?thesis using calculation order_trans by blast
    qed
    ultimately show ?thesis using iter_induct_nil seq_assoc test_seq_refine by auto
  qed                                   
  ultimately show ?thesis by simp
qed

lemma dataref_iter:
  assumes "c \<ge>\<^sub>p d"
  shows "c\<^sup>\<omega> \<ge>\<^sub>p d\<^sup>\<omega>"
proof -
  have "\<tau>(p);(inv p \<iinter> c\<^sup>\<omega>) = \<tau>(p);(inv p \<iinter> c)\<^sup>\<omega>" 
    using iter_distrib by simp
  also have "... = \<tau>(p);(\<tau>(p);(inv p \<iinter> c))\<^sup>\<omega>"
    using inv_test_iter by simp
  also have "... \<ge> \<tau>(p);(\<tau>(p);(inv p \<iinter> d))\<^sup>\<omega>" (is "_ \<ge> ?rhs")
    using assms iter_mono local.data_refines_def seq_mono_right by simp
  also have "?rhs = \<tau>(p);(inv p \<iinter> d)\<^sup>\<omega>"
    using inv_test_iter by simp
  also have "... = \<tau>(p);(inv p \<iinter> d\<^sup>\<omega>)"
    using iter_distrib by simp
  finally show ?thesis using data_refines_def by simp
qed

lemma dataref_conj_distrib:
  "\<tau>(p);(inv p \<iinter> (c \<iinter> d)) = (\<tau>(p);(inv p \<iinter> c)) \<iinter> (\<tau>(p);(inv p \<iinter> d))"
proof -
  have "\<tau>(p);(inv p \<iinter> (c \<iinter> d)) = \<tau>(p);((inv p \<iinter> c) \<iinter> (inv p \<iinter> d))"
    using conj_conj_distrib_left by auto
  also have "... = (\<tau>(p);(inv p \<iinter> c)) \<iinter> (\<tau>(p);(inv p \<iinter> d))"
    by (simp add: test_conj_distrib)
  finally show ?thesis.
qed

lemma dataref_conj:
  assumes "c\<^sub>1 \<ge>\<^sub>p d\<^sub>1" and "c\<^sub>2 \<ge>\<^sub>p d\<^sub>2"
  shows "c\<^sub>1 \<iinter> c\<^sub>2 \<ge>\<^sub>p d\<^sub>1 \<iinter> d\<^sub>2"
proof -
  have "\<tau>(p);(inv p \<iinter> (c\<^sub>1 \<iinter> c\<^sub>2)) = \<tau>(p);(inv p \<iinter> c\<^sub>1) \<iinter> \<tau>(p);(inv p \<iinter> c\<^sub>2)"
    using dataref_conj_distrib by auto
  also have "... \<ge> \<tau>(p);(inv p \<iinter> d\<^sub>1) \<iinter> \<tau>(p);(inv p \<iinter> d\<^sub>2)" (is "_ \<ge> ?rhs")
    using assms by (simp add: conj.sync_mono local.data_refines_def)
  also have "?rhs = \<tau>(p);(inv p \<iinter> (d\<^sub>1 \<iinter> d\<^sub>2))"
    using dataref_conj_distrib by simp
  finally show ?thesis using data_refines_def by simp
qed

lemma dataref_par_distrib:
  "\<tau>(p);(inv p \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)) = \<tau>(p);(inv p \<iinter> c\<^sub>1) \<parallel> \<tau>(p);(inv p \<iinter> c\<^sub>2)"
proof -
  have "\<tau>(p);(inv p \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)) = \<tau>(p);((inv p \<iinter> c\<^sub>1) \<parallel> (inv p \<iinter> c\<^sub>2))"
    using inv_distrib_par by simp (* this is listed as promise_distrib in the paper but this is more specific *)
  also have "... = \<tau>(p);(inv p \<iinter> c\<^sub>1) \<parallel> \<tau>(p);(inv p \<iinter> c\<^sub>2)"
    using test_par_distrib by simp
  finally show ?thesis.
qed

lemma dataref_par:
  assumes "c\<^sub>1 \<ge>\<^sub>p d\<^sub>1" and "c\<^sub>2 \<ge>\<^sub>p d\<^sub>2"
  shows "c\<^sub>1 \<parallel> c\<^sub>2 \<ge>\<^sub>p d\<^sub>1 \<parallel> d\<^sub>2"
proof -
  have "\<tau>(p);(inv p \<iinter> (c\<^sub>1 \<parallel> c\<^sub>2)) = \<tau>(p);(inv p \<iinter> c\<^sub>1) \<parallel> \<tau>(p);(inv p \<iinter> c\<^sub>2)"
    using dataref_par_distrib by simp
  also have "... \<ge> \<tau>(p);(inv p \<iinter> d\<^sub>1) \<parallel> \<tau>(p);(inv p \<iinter> d\<^sub>2)" (is "_ \<ge> ?rhs")
    using assms by (simp add: local.data_refines_def par.sync_mono)
  also have "?rhs = \<tau>(p);(inv p \<iinter> (d\<^sub>1 \<parallel> d\<^sub>2))"
    using dataref_par_distrib by simp
  finally show ?thesis using data_refines_def by simp
qed

(* Data refining primitive commands *)

lemma dataref_test:
  assumes "p \<inter> p\<^sub>2 \<subseteq> p\<^sub>1"
  shows "(\<tau> p\<^sub>1) \<ge>\<^sub>p (\<tau> p\<^sub>2)"
proof -
  have "p \<inter> p\<^sub>2 \<subseteq> p \<inter> p\<^sub>1"
    using assms by simp
  moreover have "\<tau>(p);\<tau>(p\<^sub>1) \<ge> \<tau>(p);\<tau>(p\<^sub>2)"
    using calculation test.hom_iso test_seq_test by auto
  moreover have "\<tau>(p);(inv p \<iinter> \<tau>(p\<^sub>1)) \<ge> \<tau>(p);(inv p \<iinter> \<tau>(p\<^sub>2))"
    using calculation(2) inv_distrib_test by auto
  ultimately show ?thesis using data_refines_def by simp
qed

corollary dataref_nil: "nil \<ge>\<^sub>p (\<tau> p)"
proof -
  have "nil = \<tau>(UNIV)"
    using nil_def by simp
  also have "... \<ge>\<^sub>p (\<tau> p)"
    using dataref_test by auto
  finally show ?thesis.
qed

lemma dataref_pgm:
  assumes "p \<triangleleft> r\<^sub>2 \<triangleright> p \<subseteq> r\<^sub>1"
  shows "(\<pi> r\<^sub>1) \<ge>\<^sub>p (\<pi> r\<^sub>2)"
proof -
  have "p \<triangleleft> r\<^sub>1 \<triangleright> p \<supseteq> p \<triangleleft> r\<^sub>2 \<triangleright> p"
    using assms restrict_range_def restrict_domain_def
    by (metis (no_types, lifting) Int_left_absorb inf_le2 le_inf_iff)
  moreover have "\<pi>(p \<triangleleft> r\<^sub>1 \<triangleright> p) \<ge> \<pi>(p \<triangleleft> r\<^sub>2 \<triangleright> p)"
    using calculation pgm.hom_mono by blast
  moreover have "\<tau>(p);\<pi>(r\<^sub>1 \<triangleright> p) \<ge> \<tau>(p);\<pi>(r\<^sub>2 \<triangleright> p)"
    by (metis calculation(2) pgm_test_pre restrict_domain_range_assoc)
  moreover have "\<tau>(p);(inv p \<iinter> \<pi>(r\<^sub>1)) \<ge> \<tau>(p);(inv p \<iinter> \<pi>(r\<^sub>2))"
    using calculation(3) inv_distrib_pgm by simp
  ultimately show ?thesis using data_refines_def by simp
qed

lemma dataref_env:
  assumes "p \<triangleleft> r\<^sub>2 \<triangleright> p \<subseteq> r\<^sub>1"
  shows "(\<epsilon> r\<^sub>1) \<ge>\<^sub>p (\<epsilon> r\<^sub>2)"
proof -
  have "p \<triangleleft> r\<^sub>1 \<triangleright> p \<supseteq> p \<triangleleft> r\<^sub>2 \<triangleright> p"
    using assms restrict_range_def restrict_domain_def
    by (metis (no_types, lifting) inf_le1 inf_le2 le_inf_iff) 
  moreover have "\<epsilon>(p \<triangleleft> r\<^sub>1 \<triangleright> p) \<ge> \<epsilon>(p \<triangleleft> r\<^sub>2 \<triangleright> p)"
    using calculation env.hom_mono by blast
  moreover have "\<tau>(p);\<epsilon>(r\<^sub>1 \<triangleright> p) \<ge> \<tau>(p);\<epsilon>(r\<^sub>2 \<triangleright> p)"
    using calculation(2) by (simp add: env_test_pre restrict_domain_range_assoc) 
  moreover have "\<tau>(p);(inv p \<iinter> \<epsilon>(r\<^sub>1)) \<ge> \<tau>(p);(inv p \<iinter> \<epsilon>(r\<^sub>2))"
    using calculation(3) inv_distrib_env by auto
  ultimately show ?thesis using data_refines_def by simp
qed

lemma dataref_atomic:
  assumes "p \<triangleleft> r\<^sub>2 \<triangleright> p \<subseteq> r\<^sub>1"
  shows "(\<alpha> r\<^sub>1) \<ge>\<^sub>p (\<alpha> r\<^sub>2)"
  using dataref_env dataref_pgm by (simp add: assms general_atomic_def dataref_nondet)

corollary dataref_Pgm: "Pgm \<ge>\<^sub>p (\<pi> r)"
  by (simp add: dataref_pgm pgm.Hom_def)

corollary dataref_Env: "Env \<ge>\<^sub>p (\<epsilon> r)"
  by (simp add: dataref_env env.Hom_def)

corollary dataref_Atomic: "Atomic2 \<ge>\<^sub>p (\<alpha> r)"
  by (simp add: general_atomic.Hom_ref_hom conj.sync_mono_right local.data_refines_def seq_mono)

(* Data refining composite commands *)

lemma assert_def_equiv: "\<lbrace>p\<rbrace> = nil \<squnion> \<tau>(-p);\<top>"
  by (smt assert_def seq_abort_right sup.orderE sup_assoc sup_commute test.hom_not test_nondet_compl)

lemma dataref_assert:
  assumes "p \<inter> p\<^sub>1 \<subseteq> p\<^sub>2"
  shows "\<lbrace>p\<^sub>1\<rbrace> \<ge>\<^sub>p \<lbrace>p\<^sub>2\<rbrace>"
proof -
  have nil_dref_nil: "nil \<ge>\<^sub>p nil"
    by (simp add: local.data_refines_def) 
  have abort_dref_abort: "\<top> \<ge>\<^sub>p \<top>"
    by (simp add: dataref_iter iter_abort nil_dref_nil) 
  have "\<lbrace>p\<^sub>1\<rbrace> = nil \<squnion> \<tau>(-p\<^sub>1);\<top>" using assert_def_equiv by simp
  also have "... \<ge>\<^sub>p (nil \<squnion> \<tau>(-p\<^sub>2);\<top>)"
  proof -
    have "p \<inter> -p\<^sub>2 \<subseteq> -p\<^sub>1" using assms by blast
    then have "(\<tau>(-p\<^sub>1)) \<ge>\<^sub>p (\<tau>(-p\<^sub>2))" using dataref_test by auto
    then have "(\<tau>(-p\<^sub>1);\<top>) \<ge>\<^sub>p (\<tau>(-p\<^sub>2);\<top>)" using dataref_seq abort_dref_abort by auto
    then have "(nil \<squnion> \<tau>(-p\<^sub>1);\<top>) \<ge>\<^sub>p (nil \<squnion> \<tau>(-p\<^sub>2);\<top>)" using dataref_nondet nil_dref_nil by auto
    then show ?thesis .
  qed
  also have "... = \<lbrace>p\<^sub>2\<rbrace>"
    using assert_def_equiv by auto
  finally show ?thesis.
qed

lemma dataref_guar:
  assumes "p \<triangleleft> g\<^sub>2 \<triangleright> p \<subseteq> g\<^sub>1"
  shows "(guar g\<^sub>1) \<ge>\<^sub>p (guar g\<^sub>2)"
proof -
  have "(\<pi>(g\<^sub>1) \<squnion> Env) \<ge>\<^sub>p (\<pi>(g\<^sub>2) \<squnion> Env)"
    using dataref_nondet dataref_atomic assms dataref_Env dataref_pgm env.Hom_def by auto
  then have "((\<pi>(g\<^sub>1) \<squnion> Env)\<^sup>\<omega>) \<ge>\<^sub>p ((\<pi>(g\<^sub>2) \<squnion> Env)\<^sup>\<omega>)"
    using dataref_iter by simp
  then show ?thesis using guar_def by auto
qed

lemma rely_def2: "rely r = (Pgm \<squnion> Env \<squnion> \<epsilon>(-r);\<top>)\<^sup>\<omega>"
proof -
  have "(Pgm \<squnion> Env \<squnion> \<epsilon>(-r);\<top>)\<^sup>\<omega> = (Pgm \<squnion> \<epsilon>(r) \<squnion> \<epsilon>(-r) \<squnion> \<epsilon>(-r);\<top>)\<^sup>\<omega>"
    by (metis (no_types, lifting) env.Hom_def env.hom_sup sup_assoc sup_compl_top)
  also have "... = ((\<epsilon>(r) \<squnion> Pgm) \<squnion> (atomic.negate(\<epsilon>(r)) \<sqinter> \<E>);\<top>)\<^sup>\<omega>"
    by (smt env_assump_def1 env_assump_def5 inf_sup_aci(5) inf_sup_aci(6) negate_env_sup_Env par.seq_nondet_distrib pgm.Hom_def seq_nil_right sup_top_left)
  finally show ?thesis unfolding rely_def by simp
qed

lemma dataref_rely:
  assumes "p \<triangleleft> r\<^sub>1 \<triangleright> p \<subseteq> r\<^sub>2"
  shows "(rely r\<^sub>1) \<ge>\<^sub>p (rely r\<^sub>2)"
proof -
  have nil_dref_nil: "nil \<ge>\<^sub>p nil"
    by (simp add: local.data_refines_def) 
  have abort_dref_abort: "\<top> \<ge>\<^sub>p \<top>"
    by (simp add: dataref_iter iter_abort nil_dref_nil) 
  have calculation: "p \<triangleleft> (-r\<^sub>2) \<triangleright> p \<subseteq> -r\<^sub>1"
    using assms restrict_range_def restrict_domain_def
  proof -
    have "p \<triangleleft> r\<^sub>1 \<inter> range_restriction p \<inter> r\<^sub>2 = p \<triangleleft> r\<^sub>1 \<triangleright> p"
      by (metis assms inf.orderE restrict_range_def)
    then have "p \<triangleleft> (- r\<^sub>2) \<triangleright> p \<inter> r\<^sub>1 = - r\<^sub>2 \<inter> - r\<^sub>2 \<inter> (p \<triangleleft> r\<^sub>1 \<inter> range_restriction p \<inter> r\<^sub>2)"
      by (simp add: Int_commute inf.left_commute restrict_domain_def restrict_range_def)
    then show ?thesis
      by (simp add: disjoint_eq_subset_Compl)
  qed
  then have "(Pgm \<squnion> Env \<squnion> \<epsilon>(-r\<^sub>1);\<top>) \<ge>\<^sub>p (Pgm \<squnion> Env \<squnion> \<epsilon>(-r\<^sub>2);\<top>)"
  proof -
    have "(\<epsilon>(-r\<^sub>1);\<top>) \<ge>\<^sub>p (\<epsilon>(-r\<^sub>2);\<top>)"
      using dataref_seq dataref_env calculation abort_dref_abort by auto
    then have "(Pgm \<squnion> Env \<squnion> \<epsilon>(-r\<^sub>1);\<top>) \<ge>\<^sub>p (Pgm \<squnion> Env \<squnion> \<epsilon>(-r\<^sub>2);\<top>)"
      using dataref_nondet dataref_Pgm dataref_Env by (simp add: env.Hom_def pgm.Hom_def)
    then show ?thesis.
  qed
  then have "((Pgm \<squnion> Env \<squnion> \<epsilon>(-r\<^sub>1);\<top>)\<^sup>\<omega>) \<ge>\<^sub>p ((Pgm \<squnion> Env \<squnion> \<epsilon>(-r\<^sub>2);\<top>)\<^sup>\<omega>)"
    using dataref_iter by simp
  then show ?thesis using rely_def2 by simp
qed

lemma dataref_term: "term \<ge>\<^sub>p term"
  by (simp add: local.data_refines_def)

lemma restrict_image:
  assumes "s \<in> p"
  shows "q``{s} = (p\<triangleleft>q)``{s}"
  apply(auto simp add:assms restrict_domain_def Image_def)
  done

lemma dataref_spec:
  assumes "p \<inter> p\<^sub>1 \<subseteq> p\<^sub>2"
      and "(p \<inter> p\<^sub>1) \<triangleleft> q\<^sub>2 \<triangleright> p \<subseteq> q\<^sub>1"
    shows "\<lbrace>p\<^sub>1\<rbrace>;\<lparr>q\<^sub>1\<rparr> \<ge>\<^sub>p \<lbrace>p\<^sub>2\<rbrace>;\<lparr>q\<^sub>2\<rparr>"
proof -
  have "(\<forall>s\<in>p\<^sub>1. p \<inter> (p\<^sub>1 \<triangleleft> q\<^sub>2)``{s} \<subseteq> (p\<^sub>1 \<triangleleft> q\<^sub>1)``{s})"
    apply(auto simp add: Image_def restrict_domain_def)
    using assms(2) restrict_domain_def restrict_range_def sorry
  then have calculation: "(\<forall>s\<in>p\<^sub>1. ((\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>1)``{s})) \<ge>\<^sub>p (\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>2)``{s}))))"
    using dataref_test by simp
  then have a: "(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>1)``{s})) \<ge>\<^sub>p (\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>2)``{s}))"
    apply(auto simp add: data_refines_def)
    sorry
  have "\<lbrace>p\<^sub>1\<rbrace>;\<lparr>q\<^sub>1\<rparr> = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>1``{s}))"
    unfolding spec_def by simp
  moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>(q\<^sub>1``{s}))"
  proof -
    have "\<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>1``{s})) = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>1``{s}))"
      using assert_seq_test seq_assoc by (metis (no_types, lifting))
    also have "... = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1);(\<Squnion>s\<in>UNIV. \<tau>({s});term;\<tau>(q\<^sub>1``{s}))" by simp
    also have "... = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1);(\<tau>(UNIV);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>1``{s})))"
      using test_restricts_Nondet test_top by simp
    moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1 \<inter> UNIV);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>1``{s}))"
      using test_seq_test seq_assoc calculation by simp
    moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;(\<tau>(p\<^sub>1);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>1``{s})))"
      using seq_assoc by simp
    moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>(q\<^sub>1``{s}))"
      by (simp add: test_Nondet_distrib seq_assoc)
    ultimately show ?thesis by (simp add: assert_seq_test)
  qed
  moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>1)``{s}))"
    using  restrict_image Sup.SUP_cong restrict_domain_def Image_def by smt
  moreover have "... \<ge>\<^sub>p \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>2)``{s}))"
    using a dataref_seq dataref_assert by simp
  moreover have "\<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>((p\<^sub>1 \<triangleleft> q\<^sub>2)``{s})) = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>(q\<^sub>2``{s}))"
    using  restrict_image Sup.SUP_cong restrict_domain_def Image_def by smt
  moreover have "\<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>(q\<^sub>2``{s})) = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s}))"
  proof -
    have "\<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s})) = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s}))"
      using assert_seq_test seq_assoc by (metis (no_types, lifting))
    also have "... = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1);(\<Squnion>s\<in>UNIV. \<tau>({s});term;\<tau>(q\<^sub>2``{s}))" by simp
    also have "... = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1);(\<tau>(UNIV);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s})))"
      using test_restricts_Nondet test_top by simp
    moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;\<tau>(p\<^sub>1 \<inter> UNIV);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s}))"
      using test_seq_test seq_assoc calculation by simp
    moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;(\<tau>(p\<^sub>1);(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s})))"
      using seq_assoc by simp
    moreover have "... = \<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s\<in>p\<^sub>1. \<tau>({s});term;\<tau>(q\<^sub>2``{s}))"
      by (simp add: test_Nondet_distrib seq_assoc)
    ultimately show ?thesis by (simp add: assert_seq_test)
  qed
  moreover have "\<lbrace>p\<^sub>1\<rbrace>;(\<Squnion>s. \<tau>({s});term;\<tau>(q\<^sub>2``{s})) \<ge>\<^sub>p \<lbrace>p\<^sub>2\<rbrace>;\<lparr>q\<^sub>2\<rparr>"
    apply(auto simp add: spec_def)
    using dataref_assert assms(1) dataref_seq data_refines_def by simp
  ultimately show ?thesis using dataref_trans by presburger
qed


lemma dataref_idle:
  assumes "p \<triangleleft> g \<triangleright> p \<subseteq> Id"
  shows "idle \<ge>\<^sub>p (guar g \<iinter> term)"
  using idle_def dataref_conj dataref_term dataref_guar assms by simp


lemma dataref_opt:
  assumes "p \<triangleleft> q\<^sub>2 \<triangleright> p \<subseteq> q\<^sub>1"
  shows "(opt(q\<^sub>1)) \<ge>\<^sub>p (opt(q\<^sub>2))"
proof -
  have calc: "{\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>2} \<inter> p \<subseteq> {\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>1}"
  proof -
    have "{\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>2} \<inter> p = {\<sigma>. (\<sigma>,\<sigma>)\<in>p \<triangleleft> q\<^sub>2}"
      unfolding restrict_domain_def restrict_range_def by fastforce
    also have "... = {\<sigma>. (\<sigma>,\<sigma>)\<in>p \<triangleleft> q\<^sub>2 \<triangleright> p}"
      by (metis (no_types, lifting) Int_Collect inf_commute restrict_domain_def restrict_range_def split_conv)
    also have "... \<subseteq> {\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>1}"
      using assms by auto
    finally show ?thesis .
  qed 
  have "opt(q\<^sub>1) = \<pi>(q\<^sub>1) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>1})" unfolding opt_def by simp
  also have "... \<ge>\<^sub>p (\<pi>(q\<^sub>2) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>2}))"
    using dataref_nondet dataref_atomic dataref_test calc
    by (metis (no_types, lifting) assms dataref_pgm inf_commute)
  moreover have "(\<pi>(q\<^sub>2) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>)\<in>q\<^sub>2})) = opt(q\<^sub>2)" unfolding opt_def by simp
  ultimately show ?thesis by simp
qed

lemma dataref_atomic_spec:
  assumes "p \<inter> p\<^sub>1 \<subseteq> p\<^sub>2"
      and "(p \<inter> p\<^sub>1) \<triangleleft> q\<^sub>2 \<triangleright> p \<subseteq> q\<^sub>1"
      and "p \<triangleleft> g \<triangleright> p \<subseteq> Id"
    shows "\<langle>p\<^sub>1, q\<^sub>1\<rangle> \<ge>\<^sub>p ((guar g \<iinter> term);\<lbrace>p\<^sub>2\<rbrace>;opt(q\<^sub>2);(guar g \<iinter> term))"
proof -
  have a: "idle \<ge>\<^sub>p (guar g \<iinter> term)" using assms(3) dataref_idle by simp
  have b: "\<lbrace>p\<^sub>1\<rbrace> \<ge>\<^sub>p \<lbrace>p\<^sub>2\<rbrace>"
    by (simp add: assms(1) dataref_assert)
  have "p \<triangleleft> q\<^sub>2 \<triangleright> p \<subseteq> p\<^sub>1 \<triangleleft> q\<^sub>2"
    using assms(2) restrict_range_def restrict_domain_def sorry
  then have c: "(opt(p\<^sub>1 \<triangleleft> q\<^sub>2)) \<ge>\<^sub>p (opt(q\<^sub>2))"
    using dataref_opt by auto
  have idle_dref_idle: "idle \<ge>\<^sub>p idle"
    by (simp add: local.data_refines_def) 
  have "(p \<inter> p\<^sub>1) \<triangleleft> q\<^sub>2 \<triangleright> p \<subseteq> p\<^sub>1 \<triangleleft>  q\<^sub>1"
    using assms(2)
    by (metis (no_types, lifting) domain_restrict_twice inf.absorb_iff2 inf_aci(4) 
        inf_commute inf_sup_aci(2) restrict_domain_def restrict_domain_range_assoc) 
  then have opt_dref: "(opt(p\<^sub>1 \<triangleleft> q\<^sub>1)) \<ge>\<^sub>p (opt(p\<^sub>1 \<triangleleft> q\<^sub>2))"
    using dataref_opt by (simp add: domain_restrict_twice) 
  have assert_dref: "\<lbrace>p\<^sub>1\<rbrace> \<ge>\<^sub>p \<lbrace>p\<^sub>1\<rbrace>"
      by (simp add: dataref_assert)
  have "\<langle>p\<^sub>1, p\<^sub>1 \<triangleleft> q\<^sub>1\<rangle> \<ge> \<langle>p\<^sub>1, q\<^sub>1\<rangle>"
    by (simp add: strengthen_spec)
  also have "\<langle>p\<^sub>1, q\<^sub>1\<rangle> \<ge> \<langle>p\<^sub>1, p\<^sub>1 \<triangleleft> q\<^sub>1\<rangle>"
    using strengthen_spec assms atomic_spec_strengthen_post by (simp add: restrict_domain_def) 
  then have "\<langle>p\<^sub>1, q\<^sub>1\<rangle> = \<langle>p\<^sub>1, p\<^sub>1 \<triangleleft> q\<^sub>1\<rangle>" 
    using calculation by auto
  then have w: "\<langle>p\<^sub>1, q\<^sub>1\<rangle> = idle;\<lbrace>p\<^sub>1\<rbrace>;opt(p\<^sub>1 \<triangleleft> q\<^sub>1);idle"
    using atomic_spec_def by auto
  moreover have "(idle;\<lbrace>p\<^sub>1\<rbrace>;opt(p\<^sub>1 \<triangleleft> q\<^sub>1);idle) \<ge>\<^sub>p (idle;\<lbrace>p\<^sub>1\<rbrace>;opt(p\<^sub>1 \<triangleleft> q\<^sub>2);idle)"
    using idle_dref_idle opt_dref dataref_seq calculation assert_dref by simp
  moreover have "(idle;\<lbrace>p\<^sub>1\<rbrace>;opt(p\<^sub>1 \<triangleleft> q\<^sub>2);idle) \<ge>\<^sub>p ((guar g \<iinter> term);\<lbrace>p\<^sub>2\<rbrace>;opt(q\<^sub>2);(guar g \<iinter> term))"
  proof -
    have "(idle;\<lbrace>p\<^sub>1\<rbrace>) \<ge>\<^sub>p ((guar g \<iinter> term) ;\<lbrace>p\<^sub>2\<rbrace>)"
      using a b dataref_seq by auto
    moreover have "(idle;\<lbrace>p\<^sub>1\<rbrace>;opt(p\<^sub>1 \<triangleleft> q\<^sub>2)) \<ge>\<^sub>p ((guar g \<iinter> term);\<lbrace>p\<^sub>2\<rbrace>;opt(q\<^sub>2))"
      using calculation c dataref_seq by blast
    moreover have "(idle;\<lbrace>p\<^sub>1\<rbrace>;opt(p\<^sub>1 \<triangleleft> q\<^sub>2);idle) \<ge>\<^sub>p ((guar g \<iinter> term);\<lbrace>p\<^sub>2\<rbrace>;opt(q\<^sub>2);(guar g \<iinter> term))"
      using calculation(2) dataref_seq a by blast
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis
    using dataref_trans by presburger
qed

lemma dataref_rgspec:
  assumes "p \<inter> p\<^sub>1 \<subseteq> p\<^sub>2"
      and "p \<triangleleft>  r\<^sub>1 \<triangleright> p \<subseteq> r\<^sub>2"
      and "p \<triangleleft> g\<^sub>2 \<triangleright> p \<subseteq> g\<^sub>1"
      and "(p \<inter> p\<^sub>1) \<triangleleft> q\<^sub>2 \<triangleright> p \<subseteq> q\<^sub>1"
    shows "(rely r\<^sub>1 \<iinter> guar g\<^sub>1 \<iinter> \<lbrace>p\<^sub>1\<rbrace>;\<lparr>q\<^sub>1\<rparr>) \<ge>\<^sub>p (rely r\<^sub>2 \<iinter> guar g\<^sub>2 \<iinter> \<lbrace>p\<^sub>2\<rbrace>;\<lparr>q\<^sub>2\<rparr>)"
proof -
  have "(rely r\<^sub>1 \<iinter> guar g\<^sub>1) \<ge>\<^sub>p (rely r\<^sub>2 \<iinter> guar g\<^sub>2)"
    using dataref_conj dataref_rely dataref_guar assms by auto
  moreover have "\<lbrace>p\<^sub>1\<rbrace>;\<lparr>q\<^sub>1\<rparr> \<ge>\<^sub>p \<lbrace>p\<^sub>2\<rbrace>;\<lparr>q\<^sub>2\<rparr>"
    using dataref_spec assms by simp 
  ultimately show ?thesis using dataref_conj by blast
qed

(*
lemma dataref_expr:
  assumes "p \<inter> expr_eq(e\<^sub>1, k) = p \<inter> expr_eq(e\<^sub>2, k)"
      and "single_reference e\<^sub>1 r"
      and "single_reference e\<^sub>2 r"
  shows "(\<lbrakk>e\<^sub>1\<rbrakk>k) \<ge>\<^sub>p (\<lbrakk>e\<^sub>2\<rbrakk>k)"
*)

lemma dataref_conditional:
  assumes "p \<inter> (expr_type b\<^sub>1 boolean) = p \<inter> (expr_type b\<^sub>2 boolean)"
  assumes "single_reference b\<^sub>1 r"
  assumes "single_reference b\<^sub>2 r"
      and "c\<^sub>1 \<ge>\<^sub>p c\<^sub>2" and "d\<^sub>1 \<ge>\<^sub>p d\<^sub>2"
    shows "(If b\<^sub>1 then c\<^sub>1 else d\<^sub>1) \<ge>\<^sub>p (If b\<^sub>2 then c\<^sub>2 else d\<^sub>2)"
proof -
  have "(If b\<^sub>1 then c\<^sub>1 else d\<^sub>1) = (\<lbrakk>b\<^sub>1\<rbrakk>(true);c\<^sub>1 \<squnion> \<lbrakk>b\<^sub>1\<rbrakk>(false);d\<^sub>1 \<squnion> (\<Squnion>k\<in>-boolean. \<lbrakk>b\<^sub>1\<rbrakk>(k);\<top>));idle"
    unfolding if_statement_def by simp
  moreover have "(\<lbrakk>b\<^sub>1\<rbrakk>(true);c\<^sub>1 \<squnion> \<lbrakk>b\<^sub>1\<rbrakk>(false);d\<^sub>1 \<squnion> (\<Squnion>k\<in>-boolean. \<lbrakk>b\<^sub>1\<rbrakk>(k);\<top>));idle \<ge>\<^sub>p 
    (\<lbrakk>b\<^sub>2\<rbrakk>(true);c\<^sub>2 \<squnion> \<lbrakk>b\<^sub>2\<rbrakk>(false);d\<^sub>2 \<squnion> (\<Squnion>k\<in>-boolean. \<lbrakk>b\<^sub>2\<rbrakk>(k);\<top>));idle" sorry
  moreover have "(\<lbrakk>b\<^sub>2\<rbrakk>(true);c\<^sub>2 \<squnion> \<lbrakk>b\<^sub>2\<rbrakk>(false);d\<^sub>2 \<squnion> (\<Squnion>k\<in>-boolean. \<lbrakk>b\<^sub>2\<rbrakk>(k);\<top>));idle = (If b\<^sub>2 then c\<^sub>2 else d\<^sub>2)"
    unfolding if_statement_def by simp
  ultimately show ?thesis by auto
qed

lemma dataref_gfp:
  assumes "\<And>x. ((G(x)) \<ge>\<^sub>p (F(x)))"
      and "mono G" and "mono F"
  shows "(gfp (\<lambda>x. G(x))) \<ge>\<^sub>p (gfp (\<lambda>x. F(x)))"
proof -
  have "\<tau>(p);(inv p \<iinter> gfp (\<lambda>x. G(x))) = \<tau>(p);(gfp (\<lambda>x. inv p \<iinter> G(x)))"
    using inv_distrib_gfp seq_mono assms by simp
  also have "... = gfp (\<lambda>x. \<tau>(p);(inv p \<iinter> G(x)))" sorry
  also have "... \<ge> gfp (\<lambda>x. \<tau>(p);(inv p \<iinter> F(x)))" (is "... \<ge> ?rhs")
    using assms(1) by (simp add: gfp_mono data_refines_def)
  also have "?rhs = \<tau>(p);(gfp (\<lambda>x. (inv p \<iinter> F(x))))" sorry
  also have "... = \<tau>(p);(inv p \<iinter> gfp (\<lambda>x. F(x)))"
    using inv_distrib_gfp seq_mono assms by simp
  finally show ?thesis using data_refines_def by blast 
qed

lemma dataref_while:
  assumes "p \<inter> (expr_type b\<^sub>1 boolean) = p \<inter> (expr_type b\<^sub>2 boolean)" and "c\<^sub>1 \<ge>\<^sub>p c\<^sub>2"
  shows "(While b\<^sub>1 do c\<^sub>1) \<ge>\<^sub>p (While b\<^sub>2 do c\<^sub>2)"
proof -
  have "(While b\<^sub>1 do c\<^sub>1) = gfp (\<lambda>x. If b\<^sub>1 then c\<^sub>1;x else nil)" 
    unfolding while_statement_def by simp
  moreover have "(gfp (\<lambda>x. If b\<^sub>1 then c\<^sub>1;x else nil)) \<ge>\<^sub>p (gfp (\<lambda>x. If b\<^sub>2 then c\<^sub>2;x else nil))"
    using dataref_gfp sorry
  moreover have "(gfp (\<lambda>x. If b\<^sub>2 then c\<^sub>2;x else nil)) = (While b\<^sub>2 do c\<^sub>2)"
    unfolding while_statement_def by simp
  ultimately show ?thesis by auto
qed

lemma dataref:
  assumes "{|x,y|}:\<^sub>s initx \<ge> {|y|}:\<^sub>s inity;\<lbrace>py\<rbrace>;\<tau>(p)"
      and "py \<subseteq> E\<^sup>S\<^sub>x p"
      and "\<lbrace>py\<rbrace>;{|y,x,z|}:\<^sub>s cx \<ge>\<^sub>p \<lbrace>py\<rbrace>;{|y,x,z|}:\<^sub>s dy"
      and "nil \<squnion> Atomic2;\<top> \<ge> \<tau>(py);{|y,x,z|}:\<^sub>s dy"
      and "-(E\<^sup>S\<^sub>x p \<triangleleft> UNIV) \<union> UNIV \<triangleright> E\<^sup>S\<^sub>x p \<supseteq> id y"
      and "\<lbrace>py\<rbrace>;({|y,z|}:\<^sub>s dy \<iinter> guar_inv(E\<^sup>S\<^sub>x p)) \<ge> \<lbrace>py\<rbrace>;{|y,z|}:\<^sub>s dy" 
    shows "(var x . {|x,z|}:\<^sub>s (initx;cx)) \<ge> (var y . {|y,z|}:\<^sub>s (inity;\<lbrace>py\<rbrace>;dy))"
  sorry
