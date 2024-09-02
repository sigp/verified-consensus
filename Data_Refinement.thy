theory Data_Refinement
imports Process_Epoch_O_Specs
begin

declare [[show_sorts=false]]
declare [[show_types=false]]

lemma sep_conj_impl_emptyI: "P s \<Longrightarrow> (\<And>s. Q s \<Longrightarrow> R s) \<Longrightarrow> (P \<and>* (Q \<longrightarrow>* R)) s"
  by (metis sep_add_zero sep_add_zero_sym sep_conjI sep_disj_zero sep_implI)


lemma sep_conj_sep_impl_spec: "\<lbrakk>((Q -* R) \<and>* P) h; \<And>h. (Q -* R) h \<Longrightarrow> (P \<longrightarrow>* R') h\<rbrakk> \<Longrightarrow> R' h"
  by (metis (full_types) sep.mult_commute sep_conj_sep_impl2)

lemma septraction_iff: "(P -* Q) s \<longleftrightarrow> (\<exists>h. P h \<and> s ## h \<and> Q (s + h))"
  apply (clarsimp simp: septraction_def sep_impl_def pred_neg_def)
  apply (safe; clarsimp?)
   apply (blast)
  apply (blast)
  done

lemma septract_commute: "(P -* (Q -* R)) = (Q -* (P -* R))"
  apply (intro ext iffI; simp add: septraction_iff)
   apply (clarsimp)
   apply (metis sep_add_assoc sep_add_commute sep_add_disjD sep_disj_addI1 sep_disj_commuteI)
   apply (clarsimp)
  apply (metis sep_add_assoc sep_add_commute sep_add_disjD sep_disj_addI1 sep_disj_commuteI)
  done



text \<open>definition "domain P \<equiv> \<Union>((dom o snd) ` P)"\<close>

definition "down f = {g. \<exists>h. g o h = f}" 

definition "domain P \<equiv> \<Union>f\<in>\<Union>(set_of ` Collect P). {f}"

definition "epsilon d \<equiv> (\<lambda>p. set_of p = d)"

notation epsilon ("\<epsilon>" )


definition "domain_of P S \<equiv> finite S \<and> sep.prod epsilon S \<ge> P" 

lemma "epsilon (domain (maps_to l v)) \<ge> (maps_to l v)  "
  apply (clarsimp simp: domain_of_def epsilon_def)
  by (clarsimp simp: domain_def maps_to_def set_of_def)


notation domain ("\<delta>" )


abbreviation (input) "\<phi> P \<equiv> (\<lambda>s. s \<in> P)"

context extended_hl_pre begin

definition "hoare_df P f Q d \<equiv> \<exists>P' Q'. 
            hoare_triple (lift P') f (lift Q') \<and> (epsilon d -* (P \<and>* epsilon d)) \<le>  (epsilon d -* P') \<and> (Q \<and>* epsilon d) \<ge> Q'"

(* definition "hoare_df P f Q d \<equiv> \<exists>P' Q'. d \<subseteq> domain (Collect P') \<and> 
            hoare_triple P' f Q' \<and> P \<le>  (epsilon d -* P') \<and> (Q \<and>* epsilon d) \<ge> Q'" *)

lemma hoare_dfI: "hoare_triple (lift P') f (lift Q') \<Longrightarrow>  (epsilon d -* (P \<and>* epsilon d)) \<le>  (epsilon d -* P') \<Longrightarrow> (Q \<and>* epsilon d) \<ge> Q' \<Longrightarrow> 
                  hoare_df P f Q d"
  apply (clarsimp simp: hoare_df_def)
  apply (intro exI conjI, assumption)
  by (assumption)+

lemma septraction_iff: "(P -* Q) s \<longleftrightarrow> (\<exists>h. P h \<and> h ## s \<and> Q (s + h))"
  apply (clarsimp simp: septraction_def sep_impl_def pred_neg_def)
  apply (clarsimp simp: sep_disj_commute)
  by (blast)


definition "precise_p P \<equiv> (\<forall>h hp hp'. hp \<preceq> h \<and> P hp \<and> hp' \<preceq> h \<and> P hp' \<longrightarrow> hp = hp')"

lemma "precise_p P \<Longrightarrow> (P \<and>* R) (s + h) \<Longrightarrow> s ## h \<Longrightarrow> P s \<Longrightarrow> R h"
  apply (clarsimp simp: precise_p_def sep_conj_def)
  apply (subgoal_tac "s = x"; clarsimp?)
  oops

lemma maps_to_set_of_iff: "maps_to l v s \<Longrightarrow> set_of s = ({f. \<exists>v. (\<lambda>s'. set l s' v) = f} \<union> {id})"
  by (clarsimp simp: maps_to_def)

lemma maps_to_point_of_iff: "maps_to l v s \<Longrightarrow> point_of s =  (\<lambda>s'. set l s' (Some v))"
  by (clarsimp simp: maps_to_def)

lemma eps_domain_maps_to_is: "epsilon (domain (maps_to l v)) = (EXS v. maps_to l v)"
  apply (intro ext iffI; clarsimp simp: epsilon_def)
   apply (clarsimp simp: domain_def)
   apply (rule exI)
     
   apply (subst maps_to_def)
   apply (intro conjI)
     apply (case_tac "set_of s = {}"; clarsimp)
  using id_in_set apply blast
  apply (clarsimp simp: maps_to_def)
    apply (intro set_eqI iffI; clarsimp)
     apply (clarsimp simp: set_eq_iff)
     apply (erule_tac x=x in allE)
     apply (drule iffD2, blast)
     apply (clarsimp simp: maps_to_set_of_iff)
    apply (safe; clarsimp)
     apply (metis UN_iff empty_Collect_eq empty_iff point_in_set)
    apply (rule_tac x="lens_pset l v" in exI)
    apply (intro conjI)
     apply (metis Collect_empty_eq UN_empty emptyE id_in_set maps_to_lens_pset')
  using lens_pset_simps(1) apply force
     apply (case_tac "set_of s = {}"; clarsimp)
    apply (metis empty_iff id_in_set)

   apply (subst (asm) set_eq_iff, clarsimp)
   apply (erule_tac x="point_of s" in allE, clarsimp)
  sorry
     apply (erule_tac x=x in allE)
  find_theorems maps_to
  
  find_theorems maps_to set_of
  
subgoal proof -
  fix s :: "'c domain_pair" and x :: "'c domain_pair" and xa :: "'c domain_pair" and xb :: "'c \<Rightarrow> 'c"
  assume a1: "dom_funs x = {f. \<exists>v. (\<lambda>s. lens.set l s v) = f}"
  assume a2: "insert (state_of s) (dom_funs s) = insert (\<lambda>s. lens.set l s (Some v)) {f. \<exists>v. (\<lambda>s. lens.set l s v) = f}"
  assume a3: "xb \<in> dom_funs s"
  have "\<forall>f. f \<notin> dom_funs x \<or> (\<exists>z. (\<lambda>c. lens.set l c z) = f)"
    using a1 by blast
  then show "\<exists>z. (\<lambda>c. lens.set l c z) = xb"
    using a3 a2 a1 by (metis insert_iff)
qed
  sorry


lemma p_set_eq_iff: "A = B \<longleftrightarrow> set_of A = set_of B \<and> point_of A = point_of B "
  by (metis Rep_p_set_inject domain_pair.expand point_of_def set_of_def)


lemma precise_p_eps_maps: "precise_p (epsilon (domain (maps_to l v)))"
  apply (clarsimp simp: precise_p_def eps_domain_maps_to_is)
  apply (clarsimp simp: sep_substate_def)
  apply (intro p_set_eqI)
   apply (clarsimp simp: sep_disj_p_set_def disj_cylindric_set_def)
   apply (simp add: maps_to_def)
  apply (clarsimp simp: sep_disj_p_set_def disj_cylindric_set_def)
  apply (subst (asm) p_set_eq_iff;
         clarsimp simp: plus_p_simps maps_to_point_of_iff maps_to_set_of_iff)
  by (metis (no_types, lifting) comp_eq_dest_lhs get_set_def maps_to_def valid_lens_def)


definition "cancellative P \<equiv> \<forall>a b c. a ## b \<longrightarrow> a ## c \<longrightarrow> a + b = a + c \<longrightarrow> P a \<longrightarrow> c = b" 


lemma "inj f \<Longrightarrow> f o g = g o f \<Longrightarrow> f o h = h o f \<Longrightarrow> f \<circ> g = f \<circ> h \<Longrightarrow> g = h" 
  apply (intro ext)
  apply (drule_tac x=x in fun_cong)+
  apply (clarsimp)
  by (metis injD)

lemma "surj f \<Longrightarrow> f o g = g o f \<Longrightarrow> f o h = h o f \<Longrightarrow> f \<circ> g = f \<circ> h \<Longrightarrow> g = h" 
  apply (intro ext)
  apply (clarsimp)
  by (metis surj_fun_eq)

lemma valid_set_set_app: "valid_lens l \<Longrightarrow>  lens.set l (lens.set l s v) v' = lens.set l s v'" 
  apply (clarsimp simp: valid_lens_def) 
  by (clarsimp simp: set_set_def)

lemma valid_set_get_app: "valid_lens l \<Longrightarrow>  lens.set l s (lens.get l s) = s"
  apply (clarsimp simp: valid_lens_def)
  by (clarsimp simp: set_get_def)

lemma valid_get_set_app: "valid_lens l \<Longrightarrow>  lens.get l (lens.set l s v) = v"
  apply (clarsimp simp: valid_lens_def)
  by (clarsimp simp: get_set_def)


lemma cancellable_lens: " valid_lens l \<Longrightarrow> \<forall>x v. set l (f x) v = f (set l x v) \<Longrightarrow>  \<forall>x v. set l (g x) v = g (set l x v)
 \<Longrightarrow> \<forall>x v. set l (f x) v = set l (g x) v \<Longrightarrow>  f = g" 
  apply (rule ext)
  apply (clarsimp simp: valid_lens_def)
  by (metis set_get_def set_set_def)

lemma cancellable_lens': " valid_lens l \<Longrightarrow> \<forall>x v. set l (f x) v = f (set l x v) \<Longrightarrow>  \<forall>x v. set l (g x) v = g (set l x v)
 \<Longrightarrow> \<forall>x . set l (f x) v = set l (g x) v \<Longrightarrow>  f = g" 
  apply (rule ext)
  apply (clarsimp simp: valid_lens_def)
  by (metis set_get_def set_set_def)

definition "to_rel p \<equiv> \<Union>f\<in>(set_of p - {id}). {s. (snd s) = f (fst s)}"

definition "Surj_on R S \<equiv> snd ` R = S"

abbreviation "Surj R \<equiv> Surj_on R UNIV"

lemma Surj_relD: "Surj (to_rel p) \<Longrightarrow> \<exists>f\<in>(set_of p - {id}). \<exists>y. f y = x"
  apply (clarsimp simp: to_rel_def Surj_on_def)
  apply (clarsimp simp: set_eq_iff)
  apply (erule_tac x=x in allE)
  apply (clarsimp simp: image_iff)
  apply (blast)
  done

lemma cancellable_lens'': " \<forall>(f,g)\<in>((set_of S - {id}) \<times> (set_of S - {id})).  f o g = f \<Longrightarrow> Surj (to_rel S) \<Longrightarrow> 
    \<forall>(f,g)\<in>((set_of S - {id}) \<times> (set_of S - {id})). f \<noteq> g \<longrightarrow> (\<forall>h. f o (g o h) \<noteq>  (g o h) o f) \<Longrightarrow>
     S ## A \<Longrightarrow> S ## B \<Longrightarrow> S + A = S + B \<Longrightarrow> A = B" 
  apply (rule p_set_eqI; clarsimp simp: sep_disj_p_set_def)
   defer
   apply (clarsimp simp: p_set_eq_iff plus_p_simps disj_cylindric_set_def)
   apply (rule ext)
   apply (drule_tac x=x in Surj_relD)
   apply (clarsimp)
   apply (erule contrapos_np)
   apply (drule_tac x="f y" in fun_cong)
   apply (clarsimp)
   apply (smt (verit, del_insts) comp_apply id_comp id_in_set insertE insert_Diff point_in_set)
   apply (clarsimp simp: p_set_eq_iff plus_p_simps disj_cylindric_set_def)
  apply (intro set_eqI iffI; clarsimp?)
   apply (clarsimp simp: set_eq_iff)
   apply (erule_tac x=x in allE)
   apply (drule iffD1)
    apply (metis id_comp id_in_set)
   apply (clarsimp)
   apply (case_tac "f=id"; clarsimp?)
  apply (subgoal_tac "\<exists>h\<in>set_of S. h \<noteq> id \<and> h \<noteq> f", clarsimp)
    apply (subgoal_tac "h o (f o g) = (f o g) o h")
     apply blast
    apply blast
   apply (metis Diff_iff Surj_relD comp_apply eq_id_iff singletonI)
 apply (clarsimp simp: set_eq_iff)
   apply (erule_tac x=x in allE)
   apply (drule iffD2)
    apply (metis id_comp id_in_set)
   apply (clarsimp)
   apply (case_tac "f=id"; clarsimp?)
  apply (subgoal_tac "\<exists>h\<in>set_of S. h \<noteq> id \<and> h \<noteq> f", clarsimp)
    apply (subgoal_tac "h o (f o g) = (f o g) o h")
     apply blast
    apply blast
  apply (metis Diff_iff Surj_relD comp_apply eq_id_iff singletonI)
  done
  

lemma commutative_funs_disj: "a ## b \<Longrightarrow> f \<in> set_of a \<Longrightarrow> g \<in> set_of b \<Longrightarrow> f o g = g o f"
     apply (clarsimp simp: sep_disj_p_set_def)
  apply (clarsimp simp: disj_cylindric_set_def set_of_def)
  by blast

lemma commutative_funs_disj': "a ## b \<Longrightarrow> f \<in> set_of a \<Longrightarrow> g \<in> set_of b \<Longrightarrow> f (g x) = g (f x)"
  apply (drule (2) commutative_funs_disj)
  by (drule fun_cong[where x=x], clarsimp)
  


lemma maps_toI: "point_of s = (\<lambda>s. set l s (Some v)) \<Longrightarrow> set_of s = {f. (\<exists>v. f = (\<lambda>s. set l s  v))} \<union> {id} \<Longrightarrow> valid_lens l \<Longrightarrow>  maps_to l v s"
  apply (clarsimp simp: maps_to_def)
  apply (intro set_eqI iffI; clarsimp)
   apply (blast)
  apply (blast)
  done

lemma maps_to_set_ofI[elim!]:"maps_to l v a \<Longrightarrow> (\<lambda>s. set l s v') \<in> set_of a"
  apply (clarsimp simp: maps_to_def set_of_def)
  by fastforce

lemma maps_to_state_of_simp:"maps_to l v a \<Longrightarrow> point_of a = (\<lambda>s. set l s (Some v))"
  by (clarsimp simp: maps_to_def set_of_def)


lemma maps_to_set_of_simp:"maps_to l v a \<Longrightarrow> f \<in> set_of a \<longleftrightarrow> (\<exists>v. f = (\<lambda>s. set l s v) \<or> f = id)" 
  apply (clarsimp simp: maps_to_def)
  apply (blast)
  done

text \<open>lemma maps_to_dom_funs_simp:"maps_to l v a \<Longrightarrow> f \<in> dom_funs a \<longleftrightarrow> (\<exists>v. f = (\<lambda>s. set l s v))" sorry

  by (clarsimp simp: maps_to_def set_of_def)\<close>

lemma cannot_commute: "maps_to l v a \<Longrightarrow> a ## c \<Longrightarrow> (\<lambda>s. lens.set l s v') \<circ> f \<in> set_of c \<Longrightarrow> False"
  apply (subgoal_tac "\<forall>v. (\<lambda>s. lens.set l s v) o ((\<lambda>s. lens.set l s v') \<circ> f) = ((\<lambda>s. lens.set l s v') \<circ> f) o (\<lambda>s. lens.set l s v)")
subgoal proof -
  assume a1: "maps_to l v a"
  assume a2: "\<forall>v. (\<lambda>s. lens.set l s v) \<circ> ((\<lambda>s. lens.set l s v') \<circ> f) = (\<lambda>s. lens.set l s v') \<circ> f \<circ> (\<lambda>s. lens.set l s v)"
  have "\<forall>z c. get l (lens.set l c z) = z"
    using a1 by (simp add: get_set_def maps_to_def valid_lens_def)
  then show ?thesis
    using a2 by (metis (no_types) comp_apply option.distinct(1))
qed
  by (metis commutative_funs_disj maps_to_set_ofI)

lemma cannot_commute': "maps_to l v a \<Longrightarrow> maps_to l' v' b \<Longrightarrow> a ## b \<Longrightarrow> 
(\<lambda>s. lens.set l' s va) = (\<lambda>s. lens.set l s vaa) \<circ> (\<lambda>s. lens.set l' s vc) \<Longrightarrow> False"
  by (metis cannot_commute maps_to_set_ofI)

lemma in_union_disjI: "x \<in> A \<or> x \<in> B \<Longrightarrow> x \<in> A \<union> B"
  by (clarsimp)

lemma cancellable_maps_to: "a ## b \<Longrightarrow> a ## c \<Longrightarrow> a + b = a + c \<Longrightarrow> maps_to l v a \<Longrightarrow> b = c"
  apply (subgoal_tac "b = c", clarsimp)
  apply (rule cancellable_lens''[rotated -1], assumption)
      apply (clarsimp simp: maps_to_set_of_simp)
      apply (simp add: maps_to_def valid_write_write)
     apply (clarsimp simp: Surj_on_def to_rel_def image_iff)
     apply (intro set_eqI iffI; clarsimp simp: image_iff)
     apply (rule_tac x="write l (get l x)" in bexI; clarsimp?)
      apply (rule_tac x=x in exI)
      apply (simp add: maps_to_def valid_set_get_app)
     apply (intro conjI; clarsimp)
     apply (metis cannot_commute id_comp id_in_set)
    apply (clarsimp simp: maps_to_set_of_simp)
  apply (subgoal_tac "va \<noteq> vaa")
     apply (metis (mono_tags, lifting) comp_def maps_to_def valid_get_set_app)
    apply force
  by (clarsimp)+

 

lemma cancellative_maps_to: "cancellative (maps_to l v)"
  apply (clarsimp simp: cancellative_def)
  apply (erule cancellable_maps_to; clarsimp?)
  apply (fastforce)
  done

  

lemma septract_cancel_chain:"(Q -* Q \<and>* R) s \<Longrightarrow> precise_p Q \<Longrightarrow>  cancellative Q \<Longrightarrow>
  (\<And>s h. Q s \<Longrightarrow> s ## h \<Longrightarrow> \<exists>s'. P s' \<and> s' ## h) \<Longrightarrow> P \<le> Q \<Longrightarrow> R \<le> R' \<Longrightarrow>  (Q -* P \<and>* R') s"
  apply (clarsimp simp: septraction_iff)
  apply (atomize)
  apply (erule_tac x=h in allE)
  apply (erule_tac x=s in allE)
  apply (clarsimp)
  apply (rule_tac x=s' in exI)
  apply (intro conjI)
    apply (blast)
   apply (assumption)
  apply (rule_tac x=s' and y=s in sep_conjI)
     apply (assumption)

    apply (erule predicate1D)
    defer
    apply (clarsimp)
   apply (clarsimp simp: sep_add_ac)
  apply (clarsimp simp: sep_conj_def)
  apply (subgoal_tac "x = h"; clarsimp?)
   apply (subgoal_tac "y = s"; clarsimp?)
   apply (clarsimp simp: cancellative_def)
   apply (metis sep_add_commute)
  apply (clarsimp simp: precise_p_def)
  by (metis sep_add_commute sep_substate_disj_add)


lemma eps_dom_mutual_disjoint: "epsilon (\<delta> (maps_to l v)) s \<Longrightarrow> s ## h \<Longrightarrow> valid_lens l \<Longrightarrow> \<exists>s'. maps_to l v' s' \<and> s' ## h"
  apply (clarsimp simp: epsilon_def maps_to_def domain_def)
  apply (rule_tac x="lens_pset l v'" in exI)
  apply (clarsimp simp: lens_pset_simps)
  apply (clarsimp simp: sep_disj_p_set_def disj_cylindric_set_def lens_pset_simps split: if_splits)
  using id_in_set by blast

lemma cancel_mono: "cancellative P \<Longrightarrow> Q \<le> P \<Longrightarrow> cancellative Q"
  apply (clarsimp simp: cancellative_def)
  apply (drule (1) predicate1D)
  by blast


lemma cancel_ex_iff[simp]: "cancellative (EXS x. P x) \<longleftrightarrow> (\<forall>x. (cancellative (P x)))"
  apply (clarsimp simp: cancellative_def, intro iffI ; clarsimp?)
  apply (blast)
  done

lemma cancel_eps: "cancellative (epsilon (\<delta> (maps_to l v)))"
  apply (subst eps_domain_maps_to_is)
  apply (clarsimp)
  by (meson cancellative_maps_to)
 

lemma "(pre :: ((BeaconState \<times> ('b \<Rightarrow> 'b heap_value option)) p_set \<Rightarrow> bool)) = ( (maps_to beacon_slots b \<and>* maps_to previous_epoch_participation pep \<and>*
   maps_to current_epoch_participation cep \<and>*  maps_to validators v))  \<Longrightarrow>
 hoare_df pre process_justification_and_finalization_fast ( (maps_to beacon_slots b \<and>* maps_to previous_epoch_participation pep \<and>*
   maps_to current_epoch_participation cep \<and>*  maps_to validators v)) (domain (maps_to progressive_balances_cache pbc))"
  apply (clarsimp, rule hoare_dfI)
    apply (rule process_fast_spec)
   apply (clarsimp)
   apply (rule septract_cancel[rotated], assumption)
    apply (sep_select 2, assumption)
   apply (clarsimp simp: sep_conj_assoc)
   apply (drule septract_cancel, assumption) back
    apply (sep_select_asm 5, assumption) back
   apply (erule septract_cancel_chain)
       apply (meson precise_p_eps_maps)
  apply (simp add: cancel_eps)
     apply (erule (1) eps_dom_mutual_disjoint)
     defer
     apply (clarsimp)
  apply (meson eps_domain_maps_to_is)
     apply (clarsimp)
     apply (sep_solve)
    apply (clarsimp)
   apply (sep_cancel)+
   apply (meson eps_domain_maps_to_is)
  by simp


lemma not_dom_iff: "p \<notin> dom s \<longleftrightarrow> (\<forall>v.  [p \<mapsto> v] ## s)"
  apply (safe; clarsimp simp: sep_disj_fun_def sep_disj_option_def split: option.splits)
  apply (erule_tac x=y in allE, erule_tac x=p in allE, clarsimp)
  done

end