theory Downset

imports 
 Main 
"rg-algebra/General/CRA"
"rg-algebra/General/Distributive_Iteration"
"rg-algebra/AbstractTests/Test_Commands"
"rg-algebra/AbstractAtomic/Atomic_Commands"

begin

unbundle lattice_syntax

definition "eta (x :: 'a) = {x}"

notation eta ("\<eta>")

class preorder_bot = preorder + bot +
  assumes bot_least: "\<bottom> \<le> a"

context preorder begin
definition downset_set ("\<Down>") where
  "\<Down>X = {y. \<exists>x \<in> X. y \<le> x}"

definition downset  ("\<down>") where 
  "\<down> = \<Down> \<circ> \<eta>"


definition upset_set ("\<Up>") where
  "\<Up>X = {y. \<exists>x \<in> X. y \<ge> x}"

definition upset  ("\<up>") where 
  "\<up> = \<Up> \<circ> \<eta>"
end


class preorder_top = preorder + top +
  assumes top_greatest[simp]: "a \<le> \<top>"

typedef (overloaded) ('a) downset = "{S. \<Down>S = (S :: ('a :: preorder_bot set)) \<and> bot \<in> S} " 
  apply (rule_tac x=UNIV in exI, clarsimp simp: downset_set_def)
  apply (safe)
   apply blast
  apply (clarsimp)
  apply (rule_tac x=x in exI)
  apply (clarsimp)
  done

setup_lifting type_definition_downset


lift_definition prime :: "('a :: preorder_bot \<Rightarrow> 'a downset)" is
 "\<lambda>x. \<down>x"
  apply (clarsimp simp: preorder_class.downset_set_def preorder_class.downset_def)
    apply (intro set_eqI conjI iffI; clarsimp?)
    using preorder_class.dual_order.trans apply auto[1]
    using preorder_class.dual_order.trans apply auto[1]
    by (simp add: eta_def preorder_bot_class.bot_least)


abbreviation (input) "lift_set (f :: 'a set \<Rightarrow> 'a set \<Rightarrow> 'b) \<equiv>
   \<lambda>(x :: 'a :: preorder_bot downset)  (y :: 'a downset).  (f (Rep_downset x) (Rep_downset y))"  

lift_definition Dun     :: "'a :: preorder_bot downset \<Rightarrow> 'a downset \<Rightarrow> 'a downset" is "union" 
  apply (clarsimp simp: downset_set_def, intro iffI set_eqI; clarsimp)
  by auto

lift_definition Dinter  :: "'a :: preorder_bot downset \<Rightarrow> 'a downset \<Rightarrow> 'a downset" is "inter" 
  apply (clarsimp simp: downset_set_def, intro iffI set_eqI; clarsimp)
  by auto

lift_definition Din :: "'a :: preorder_bot \<Rightarrow> 'a downset \<Rightarrow> bool" is "(\<lambda>a A. a \<in>  A)" done

lift_definition Dsub :: "'a :: preorder_bot downset \<Rightarrow> 'a downset \<Rightarrow> bool" is " (\<subseteq>)" done

lift_definition DInf :: "'a ::preorder_bot downset set \<Rightarrow> 'a downset" is
                        "Inf :: 'a set set \<Rightarrow> 'a set"
  apply (clarsimp simp: downset_set_def downset_def eta_def)
  apply (intro set_eqI iffI; clarsimp)
  by auto

notation Dsub (infixr "(\<down>\<subseteq>)" 50)

notation Din (infixr "(\<down>\<in>)" 50)

lemma bot_in[simp]: "\<bottom> \<down>\<in> S" 
  apply (transfer, clarsimp)
  done

lemma Din_intro: "a \<down>\<in>  S \<Longrightarrow>  x \<le> a  \<Longrightarrow> x \<down>\<in> S"
  apply (transfer)
  apply (clarsimp simp: downset_def downset_set_def)
  using order_trans by fastforce


lemma Dsub_iff: "Dsub A B \<longleftrightarrow> (\<forall>x. x \<down>\<in> A \<longrightarrow> x \<down>\<in> B)"
  apply (transfer)
  apply (safe; transfer; clarsimp)
  apply (fastforce)
  done



lemma downclosed_inverseI: "\<Down>y = y \<Longrightarrow> x \<in> y \<Longrightarrow> x \<down>\<in> (Abs_downset y) "
  apply (clarsimp simp: Din_def)
  apply (subst  Abs_downset_inverse)
   apply (clarsimp)
  using Downset.preorder_bot_class.bot_least downset_set_def apply blast
  by (safe)

lemma Dinter_commute:"Dinter A B = Dinter B A"
  apply (transfer)
  by (simp add: inf_commute)

instantiation downset :: (preorder_bot) lattice begin 
definition "(less_downset :: ('a :: preorder_bot) downset \<Rightarrow> 'a downset \<Rightarrow> bool) = (inf Dsub (\<noteq>)) "

definition "less_eq_downset = Dsub"
definition "sup_downset = Dun"
definition "inf_downset = Dinter"

instance
  apply (standard; (clarsimp simp: sup_downset_def inf_downset_def less_downset_def less_eq_downset_def ), transfer; clarsimp)
   apply (safe)
   apply force
  apply force
  done
end

class bounded_order = preorder_top + preorder_bot

lemma [simp]:"\<Down>(\<down>x) = \<down> (x :: 'a :: preorder)"
  apply (clarsimp simp: downset_set_def downset_def eta_def)
  apply (safe)
  using order_trans apply blast
   apply force
  done

lemma (in bounded_order) [simp]: "(\<down>\<top>) = (UNIV )"    
  by (clarsimp simp: downset_set_def downset_def eta_def )

lemma  [simp]: "(\<Down>UNIV) = (UNIV :: 'a :: preorder set)"    
  by (clarsimp simp: downset_set_def downset_def eta_def, fastforce)
  
lemma  [simp]: "x \<in> \<down> (x :: 'a :: preorder) "
  by (clarsimp simp: downset_set_def downset_def eta_def)

instantiation downset :: (preorder_bot) Inf begin
 lift_definition Inf_downset :: "'a downset set \<Rightarrow> 'a downset" is Inf
  apply (clarsimp simp: downset_set_def downset_def eta_def)
  apply (intro set_eqI iffI; clarsimp)
   by auto
instance ..
end

instantiation downset :: (preorder_bot) complete_lattice begin 
lift_definition top_downset :: "'a downset" is " (\<Down>UNIV) " by (clarsimp)
lift_definition bot_downset :: "'a downset" is " (\<down>bot) " by clarsimp

lift_definition Sup_downset :: "'a downset set \<Rightarrow> 'a downset" is "\<lambda>S. \<Union>S \<union> \<down>(\<bottom>)"
  apply (clarsimp simp: downset_set_def downset_def eta_def)
  apply (case_tac "set = {}", clarsimp)

  apply (intro set_eqI iffI; clarsimp)
  using order_trans apply blast
   apply auto[1]
  apply (intro set_eqI iffI; clarsimp)
  apply (metis (mono_tags, lifting) mem_Collect_eq order_trans)
  by fastforce

instance
  apply (standard; (clarsimp simp: less_eq_downset_def)?)
       apply (transfer)
       apply (blast)
  apply (transfer)
      apply (meson Inf_greatest)
  apply (transfer)
     apply (clarsimp simp: Sup_downset_def)
  apply (transfer)
    apply (clarsimp simp: Sup_downset_def)
  apply blast
    apply (transfer)
    apply (simp add: Inf_lower)
  apply (transfer)
    apply (clarsimp simp: downset_def downset_set_def eta_def)
    apply (intro conjI)
     apply blast
  apply blast

  apply (rule antisym)
  apply (clarsimp simp: less_eq_downset_def Dsub_iff; clarsimp?)
  apply (transfer)
    apply (clarsimp simp: downset_def downset_set_def eta_def)
    apply blast
  apply (clarsimp simp: less_eq_downset_def Dsub_iff; clarsimp?)
  apply (transfer)
   apply (clarsimp)
  apply (rule antisym)
  apply (clarsimp simp: less_eq_downset_def Dsub_iff; clarsimp?)
   apply (transfer, clarsimp)

  apply (clarsimp simp: less_eq_downset_def Dsub_iff; clarsimp?)
  apply (transfer, clarsimp)
  done


end

lemma [simp]: "\<Down> {x} = \<down>x"
  by (clarsimp simp: downset_set_def downset_def eta_def)

context order_bot begin

subclass preorder_bot by (standard, rule bot_least)
end


lemma (in order) [simp]: "\<Down>(\<Down>S) = \<Down>S"
  apply (clarsimp simp: downset_set_def downset_def eta_def)
  apply (intro set_eqI iffI; clarsimp)
  using local.dual_order.trans apply blast
  using local.dual_order.trans apply blast
  done

lemma down_insert[simp]:"\<Down>(insert x S) = \<down>x \<union> \<Down>S" 
  apply (clarsimp simp: downset_set_def downset_def eta_def)
  apply (intro set_eqI iffI; clarsimp)
  done
  
lemma bot_least_trans[simp]:"(x :: 'a :: preorder_bot) \<le> \<bottom> \<Longrightarrow> x \<le> y"
  using order_trans preorder_bot_class.bot_least by blast



lemma down_union_distrib: "\<Down>(X \<union> Y) = \<Down>X \<union> \<Down>Y"
  apply (intro set_eqI iffI; clarsimp simp: downset_set_def)
  by blast+

lemma down_sup_distrib: "\<Down>(Sup X) = Sup ((\<Down>) ` X)"
  by (intro set_eqI iffI; clarsimp simp: downset_set_def)

lemma bot_in_downset_iff: "(\<bottom> :: 'a :: preorder_bot) \<in> \<Down> S \<longleftrightarrow> S \<noteq> {}"
  apply (safe)
   apply (clarsimp simp: downset_set_def)
  by (clarsimp simp: downset_set_def)


lemma down_down[simp]: "\<Down>(\<Down>x) = \<Down>x" 
  apply (safe; clarsimp simp: downset_set_def)
  using order_trans by blast+

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

declare bot_least[simp]
lemma (in preorder_bot) [simp]: "\<bottom> \<in> \<down> S"
  by (clarsimp simp: downset_set_def downset_def eta_def bot_least)
 
lemma (in preorder_bot) [simp]: "\<Down>{} = ({} )"
  by (clarsimp simp: downset_set_def)

lemma eq_univ_iff:  "S = UNIV \<longleftrightarrow> (\<forall>x. x \<in> S)"
  by (safe; blast)


lemma in_down_iff: "x \<in> \<down> y \<longleftrightarrow> x \<le> y " unfolding preorder_class.downset_def eta_def downset_set_def'
  by (clarsimp)


lemma not_in_down_iff: " x \<notin> \<down> y \<longleftrightarrow> ~(x \<le> y)" 
  by (simp add: in_down_iff)

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



lemma in_downsetI: "\<Down>a = a \<Longrightarrow> (\<exists>x'\<in>a. x \<le> x') \<Longrightarrow> x \<in> a " 
  apply (clarsimp simp: downset_set_def)
  using preorder_class.downset_set_def by auto


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