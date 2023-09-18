theory Upset
imports Downset

begin

unbundle lattice_syntax



typedef (overloaded) ('a) upset = "{S. \<Up>S = (S :: ('a :: preorder set)) \<and> S \<noteq> {}} " 
  apply (rule_tac x=UNIV in exI, clarsimp simp: upset_set_def)
  apply (safe)
   apply blast
  apply (clarsimp)
  apply (rule_tac x=x in exI)
  apply (clarsimp)
  done

setup_lifting type_definition_upset


lift_definition uprime :: "('a :: preorder \<Rightarrow> 'a upset)" is
 "\<lambda>x. \<up>(x :: 'a)"
  apply (clarsimp simp: preorder_class.upset_set_def preorder_class.upset_def)
    apply (intro set_eqI conjI iffI; clarsimp?)
    using preorder_class.dual_order.trans apply auto[1]
    using preorder_class.dual_order.trans apply auto[1]
    apply (rule_tac x=a in exI)
    by (simp add: eta_def )


lift_definition Uun     :: "'a :: preorder upset \<Rightarrow> 'a  upset \<Rightarrow> 'a upset" is "union" 
  apply (clarsimp simp: upset_set_def, intro iffI set_eqI; clarsimp)
  by auto

(* lift_definition Uinter  :: "'a :: preorder_top upset \<Rightarrow> 'a  upset \<Rightarrow> 'a upset" is "inter" 
  apply (intro conjI)
   apply (clarsimp simp: upset_set_def, intro iffI set_eqI; clarsimp?)
  apply auto[1]
   apply auto[1]
  apply (clarsimp)
*)

lift_definition Uin :: "'a :: preorder  \<Rightarrow> 'a  upset \<Rightarrow> bool" is "(\<lambda>a A. a \<in>  A)" done

lift_definition Usub :: "'a :: preorder upset \<Rightarrow> 'a  upset \<Rightarrow> bool" is " (\<subseteq>)" done

(* lift_definition UInf :: "'a ::preorder_top upset set \<Rightarrow> 'a upset" is
                        "Inf :: 'a set set \<Rightarrow> 'a set"
  apply (clarsimp simp: upset_set_def downset_def eta_def)
  apply (intro set_eqI iffI; clarsimp)
  by auto *)

notation Usub (infixr "(\<up>\<subseteq>)" 50)

notation Uin (infixr "(\<up>\<in>)" 50)

lemma top_in[simp]: "\<top> \<up>\<in> S" 
  apply (transfer, clarsimp)
  done

lemma Din_intro: "a \<up>\<in>  S \<Longrightarrow>  x \<ge> a  \<Longrightarrow> x \<up>\<in> S"
  apply (transfer)
  apply (clarsimp simp:)
  using upset_set_def by auto


lemma Dsub_iff: "Usub A B \<longleftrightarrow> (\<forall>x. x \<up>\<in> A \<longrightarrow> x \<up>\<in> B)"
  apply (transfer)
  apply (safe; transfer; clarsimp)
  apply (fastforce)
  done



lemma downclosed_inverseI: "\<Up>y = y \<Longrightarrow> x \<in> y \<Longrightarrow> x \<up>\<in> (Abs_upset y) "
  apply (clarsimp simp: Uin_def)
  apply (subst  Abs_upset_inverse)
   apply (clarsimp)
  using upset_set_def by fastforce
  by (safe)

lemma Dinter_commute:"Uinter A B = Uinter B A"
  apply (transfer)
  oops
  by (simp add: inf_commute)

instantiation upset :: (preorder) semilattice_sup begin 

definition "less_eq_upset a (b :: 'a upset) = Usub a b"
definition "sup_upset = Uun"

definition "(f:: ('a :: preorder) upset)  < g \<longleftrightarrow> f \<le> g \<and> \<not> (g \<le> f)"


instance
  apply (standard; (clarsimp simp: sup_upset_def less_upset_def less_eq_upset_def )?)
  apply (clarsimp simp: less_eq_upset_def)
          apply (transfer; clarsimp)
  apply (transfer; clarsimp)
         apply (force)
  apply (transfer; clarsimp)
  apply (transfer; clarsimp)
  apply (transfer; clarsimp)
  apply (transfer; clarsimp)
  done
end


lemma [simp]:"\<Up>(\<up>x) = \<up> (x :: 'a :: preorder)"
  apply (clarsimp simp: upset_set_def upset_def eta_def)
  apply (safe)
  using order_trans apply blast
   apply force
  done

lemma (in bounded_order) [simp]: "(\<up>\<bottom>) = (UNIV )"    
  by (clarsimp simp:upset_set_def upset_def eta_def bot_least )

lemma  [simp]: "(\<Up>UNIV) = (UNIV :: 'a :: preorder set)"    
  by (clarsimp simp:upset_set_def upset_def eta_def , fastforce )


  
lemma  [simp]: "x \<in> \<up>(x :: 'a :: preorder) "
  by (clarsimp simp:upset_set_def upset_def eta_def )
(* 
instantiation upset :: (preorder_top) Inf begin
 lift_definition Inf_upset :: "'a upset set \<Rightarrow> 'a upset" is Inf
  apply (clarsimp simp: upset_set_def upset_def  eta_def)
  apply (intro set_eqI iffI; clarsimp)
   by auto
instance ..
end

instantiation upset :: (preorder_top) complete_lattice begin 
lift_definition top_upset :: "'a upset" is " (\<Up>UNIV) " by (clarsimp)
lift_definition bot_upset :: "'a upset" is " (\<up>(\<top>)) " by clarsimp

lift_definition Sup_upset :: "'a upset set \<Rightarrow> 'a upset" is "\<lambda>S. \<Union>S \<union> \<up>(\<top>)"
  apply (clarsimp simp: upset_set_def upset_def eta_def)
  apply (case_tac "set = {}", clarsimp)

  apply (intro set_eqI iffI; clarsimp)
  using order_trans apply blast
   apply auto[1]
  apply (intro set_eqI iffI; clarsimp)
  apply (metis (mono_tags, lifting) mem_Collect_eq order_trans)
  by fastforce

instance
  apply (standard; (clarsimp simp: less_eq_upset_def)?)
       apply (transfer)
       apply (blast)
  apply (transfer)
      apply (meson Inf_greatest)
  apply (transfer)
     apply (clarsimp simp: Sup_upset_def)
  apply (transfer)
    apply (clarsimp simp: Sup_upset_def)
  apply blast
    apply (transfer)
    apply (simp add: Inf_lower)
  apply (transfer)
    apply (clarsimp simp: upset_def upset_set_def eta_def)
    apply (intro conjI)
     apply blast
  apply blast

  apply (rule antisym)
  apply (clarsimp simp: less_eq_upset_def ; clarsimp?)
  apply (transfer)
    apply (clarsimp simp: upset_def upset_set_def eta_def)
    apply blast
  apply (clarsimp simp: less_eq_upset_def ; clarsimp?)
  apply (transfer)
   apply (clarsimp)
  apply (rule antisym)
  apply (clarsimp simp: less_eq_upset_def ; clarsimp?)
   apply (transfer, clarsimp)

  apply (clarsimp simp: less_eq_upset_def ; clarsimp?)
  apply (transfer, clarsimp)
  done


end
*)
lemma [simp]: "\<Up> {x} = \<up>x"
  by (clarsimp simp: upset_set_def upset_def eta_def)

context order_bot begin

subclass preorder_bot by (standard, rule bot_least)
end


lemma (in order) [simp]: "\<Up>(\<Up>S) = \<Up>S"
  apply (clarsimp simp: upset_set_def upset_def eta_def)
  apply (intro set_eqI iffI; clarsimp)
  using local.dual_order.trans apply blast
  using local.dual_order.trans apply blast
  done

lemma up_insert[simp]:"\<Up>(insert x S) = \<up>x \<union> \<Up>S" 
  apply (clarsimp simp: upset_set_def upset_def eta_def)
  apply (intro set_eqI iffI; clarsimp)
  done
  
lemma top_great_trans[simp]:"(x :: 'a :: preorder_top) \<ge> \<top> \<Longrightarrow> x \<ge> y"
  using dual_order.trans preorder_top_class.top_greatest by blast



lemma up_union_distrib: "\<Up>(X \<union> Y) = \<Up>X \<union> \<Up>Y"
  apply (intro set_eqI iffI; clarsimp simp: upset_set_def)
  by blast+

lemma up_sup_distrib: "\<Up>(Sup X) = Sup ((\<Up>) ` X)"
  by (intro set_eqI iffI; clarsimp simp: upset_set_def)

lemma up_in_downset_iff: "(\<top> :: 'a :: preorder_top) \<in> \<Up> S \<longleftrightarrow> S \<noteq> {}"
  apply (safe)
   apply (clarsimp simp: upset_set_def)
  by (clarsimp simp: upset_set_def)


lemma up_up[simp]: "\<Up>(\<Up>S) = \<Up>S"
  apply (clarsimp simp: upset_set_def upset_def eta_def)
  apply (intro set_eqI iffI; clarsimp)
  using order_trans apply blast
  using order_trans apply blast
  done


(*
instantiation downset :: (preorder_bot) complete_distrib_lattice
  
begin
instance
  apply (standard)
  apply (case_tac "A = {}", clarsimp)
  apply (clarsimp simp: less_eq_downset_def, transfer)
  apply (intro iffI conjI set_eqI subsetI)
  apply (clarsimp)
   apply (rule_tac x="(\<lambda>Y. \<Down>(SOME X.  X \<in> Y \<and> x \<in> X ) \<union> \<down>\<bottom>) ` A " in exI)
  apply (intro conjI)
    apply (rule_tac x="(\<lambda>Y. \<Down>(SOME X.  X \<in> Y \<and> x \<in> X ) \<union> \<down>\<bottom>)" in exI, clarsimp simp: down_union_distrib) 
    apply (subst Un_commute, subst down_insert[symmetric], subst insert_absorb)
     apply (simp add: someI2_bex)
    apply (metis (mono_tags, lifting) verit_sko_ex')

    apply (clarsimp simp: Un_commute down_insert[symmetric] insert_absorb someI2_bex)
   apply (metis (mono_tags, lifting) verit_sko_ex')
    apply (clarsimp simp: Un_commute down_insert[symmetric] insert_absorb someI2_bex)
   apply (metis (mono_tags, lifting) verit_sko_ex')

  done
  
 
end


instantiation downset :: (preorder_bot) bounded_order begin
instance 
  by (standard; clarsimp)
end

(* why is this necessary? *)


instantiation downset :: (preorder_bot) refinement_lattice begin
instance ..
end


lemma downset_set_def': "\<Down>X = {y. \<exists>x\<in>X. y \<le> x}" unfolding downset_set_def ..
*)
declare bot_least[simp]


lemma in_up_iff: "x \<in> \<up> y \<longleftrightarrow> x \<ge> y " unfolding upset_def eta_def upset_set_def
  by (clarsimp)


lemma eq_univ_iff:  "S = UNIV \<longleftrightarrow> (\<forall>x. x \<in> S)"
  by (safe; blast)




lemma not_in_down_iff: " x \<notin> \<up> y \<longleftrightarrow> ~(x \<ge> y)" 
  by (safe; clarsimp simp: in_up_iff)


lemma in_upsetI: "\<Up>a = a \<Longrightarrow> (\<exists>x'\<in>a. x \<ge> x') \<Longrightarrow> x \<in> a " 
  apply (clarsimp simp: upset_set_def)
  using upset_set_def by auto

end

lemma rewrite_sup:  "(\<And>a. a \<le> x \<Longrightarrow> g a \<le> g x) \<Longrightarrow>  (\<Union>a\<in>\<down> x. \<Union>b\<in>c. \<down> (g a b)) = (\<Squnion>b\<in>c. \<down>(g x b))"
  apply (safe; clarsimp simp: in_down_iff)
  apply (meson le_funD preorder_class.dual_order.trans)
  using in_down_iff by blast

lemma rewrite_sup': "mono_on UNIV g \<Longrightarrow> (\<Union>b\<in>\<down> x. \<down> (g b)) = \<down>(g x) "
  apply (safe; clarsimp simp: in_down_iff preorder_class.downset_set_def) 
  apply (meson dual_order.trans monotoneD)
  using in_down_iff by blast


lemma sup_down_down: "(\<And>x. x \<le> c \<Longrightarrow> g x \<le> g c) \<Longrightarrow> (\<Union>x\<in>\<down> c. \<down> (g x)) = \<down> (g c)"
  apply (safe; clarsimp simp: in_down_iff)
  using order_trans apply blast
  by (fastforce dest: monoD)


lemma SUP_SUP: "(\<Union>x\<in>a. \<Union>y\<in>b. g x y) = (\<Union>(x, y)\<in>(a \<times> b). g x y)"
  apply (safe; clarsimp)
   apply (blast)
  apply (blast)
  done





lemma split_set: "(S :: 'a :: complete_lattice) = (\<Squnion>{x. (x \<le> S)})"
  by (metis Sup_eqI dual_order.refl mem_Collect_eq)

lemma (in order_bot) bot_in_downset_iff: "\<bottom> \<in> \<Down> S \<longleftrightarrow> S \<noteq> {}"
  by (clarsimp simp: downset_set_def, blast)


lemma down_nonempty[simp]:"\<down> x \<noteq> {}"
  apply (clarsimp simp: downset_def)
  apply (clarsimp simp: downset_set_def eta_def)
  by (blast)

lemma Ball_down: "(\<forall>x\<in> \<down>y. P x y) \<longleftrightarrow> (\<forall>x\<le>y. P x y)"
  apply (safe)
  apply (clarsimp simp: downset_def)
   apply (clarsimp simp: downset_set_def eta_def)
  apply (clarsimp simp: downset_def)
  apply (clarsimp simp: downset_set_def eta_def)
  done



lemma in_down_bot_trans[simp]: "(x :: 'a :: preorder_bot) \<in> \<down>\<bottom> \<Longrightarrow> x \<in> \<down>y"
  by (clarsimp simp: in_down_iff)

lemma down_image_iff:"x \<in> \<Down> (g ` S) \<longleftrightarrow> (\<exists>y\<in>S. x \<le> g y) "
  apply (safe; clarsimp simp: downset_set_def')
  apply (blast)
  done

lemma in_Down_iff: "(x \<in> \<Down> y) = (\<exists>c\<in>y. x \<le> c)" by (clarsimp simp: downset_def downset_set_def eta_def)





lemma mono_downset_comp: "mono (f) \<Longrightarrow> (\<Union>x\<in>\<down> (c). \<Union>y\<in>x'. \<down> (f x y)) = (\<Union>y\<in>x'. \<down>(f c y))"
  apply (safe; clarsimp simp:in_down_iff Bex_def)
  apply (rule_tac x=y in exI)
  apply (meson dual_order.trans le_funD monoD)
  by blast

lemma mono_downset_comp_alt: "mono (f) \<Longrightarrow> (\<Union>x\<in>\<down> (c). (\<Down>(\<Union>y\<in>x'. f x y))) = \<Down>(\<Union>y\<in>x'. (f c y))"
  apply (safe; clarsimp simp: in_down_iff Bex_def downset_set_def)
   apply (clarsimp simp: mono_def le_fun_def)
   apply (erule_tac x=xa in allE)
   apply (erule_tac x=c in allE)
   apply (clarsimp)
   apply (rule_tac x=xb in exI, blast)
  by blast

lemma mono_downset_comp': "mono (f) \<Longrightarrow> (\<Union>x\<in>\<down> (c). f x) = ((f c))"
  apply (safe; clarsimp simp: in_down_iff Bex_def)
  apply (drule monoD, assumption)
  apply blast
  by blast

lemma mono_on_down: "mono_on UNIV f \<Longrightarrow> \<Union> (f ` (\<down> c)) = (f c)" 
  apply (safe; clarsimp simp: in_down_iff Bex_def)
  apply (meson in_mono monotoneD)
  by blast

lemma mono_on_down': "mono_on UNIV f \<Longrightarrow> \<Union> (f ` (\<Down> c)) = Sup(f ` c)" 
  apply (safe; clarsimp simp: in_down_iff Bex_def)
  apply (meson in_Down_iff in_mono monotoneD)
  using in_Down_iff by auto

lemma mono_comp[intro!, simp]:"mono_on UNIV f \<Longrightarrow> mono_on UNIV g \<Longrightarrow> mono_on UNIV (f o g)"
  by (simp add: mono_on_def)


lemma mono_comp'[intro!, simp]:"mono_on UNIV f \<Longrightarrow> mono_on UNIV g \<Longrightarrow> mono_on UNIV (\<lambda>x. f (g x))"
  by (simp add: mono_on_def)

lemma mono_on_sup[intro, simp]: "mono_on UNIV f \<Longrightarrow> mono_on UNIV g \<Longrightarrow> mono_on UNIV (\<lambda>x. f x \<union> g x)"
  apply (rule mono_onI; clarsimp?)
  by (metis monotoneD sup.coboundedI1 sup_commute)

lemma mono_on_SUP:  " (\<And>x. mono_on UNIV (\<lambda>y . f y x)) \<Longrightarrow> mono_on UNIV (\<lambda>x. \<Union> (f x `  S))"
  apply (rule mono_onI; clarsimp)
  apply (rule_tac x=xa in bexI)
   apply (meson in_mono monotoneD)
  apply (clarsimp)
  done

lemma mono_on_principle: "mono_on UNIV f \<Longrightarrow> mono_on UNIV (\<lambda>y. \<down> (f y))"
  apply (rule mono_onI; clarsimp simp: in_down_iff)
  by (meson dual_order.trans monotoneD)
end