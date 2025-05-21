theory Fun_Algebra imports
  "Verified_Consensus.Sep_Tactics"
  "Verified_Consensus.Extended_Separation_Algebra"
  Lens
begin

instantiation unit ::  stronger_sep_algebra begin

fun sep_disj_unit :: "unit \<Rightarrow> unit \<Rightarrow> bool" where
 "sep_disj_unit x y \<longleftrightarrow> True" 

fun plus_unit :: "unit \<Rightarrow> unit \<Rightarrow> unit" where
 "plus_unit x y = ()" 


definition "zero_unit = ()"

instance
  by (standard, case_tac x; (clarsimp simp: zero_unit_def)?)
 

end

lemma [simp]: "None ## x" by (clarsimp simp: sep_disj_option_def)

definition "add_lens l l' =  Lens (\<lambda>s. (get l s, get l' s)) (\<lambda>s (a, b). set l' (set l s a) b) (\<lambda>(a, b). valid l a \<and> valid l' b)"

definition "disj_lens l l' \<equiv> (\<forall>s v. get l s = get l (set l' s v)) \<and> (\<forall>s v. get l' s = get l' (set l s v)) " 

definition "ptr_lens p = Lens (\<lambda>s. s p) (\<lambda>s v. s(p := v)) (\<lambda>s. True)" 

lemma "p \<noteq> p' \<Longrightarrow> disj_lens (ptr_lens p) (ptr_lens p')"
  apply (clarsimp simp: disj_lens_def, safe; clarsimp simp: ptr_lens_def)
  done


definition "disj_cylindric_set S S' \<equiv> \<forall>f\<in>S. \<forall>f'\<in>S'. f o f' = f' o f"


datatype 'a domain_pair = Pair (dom_funs : "('a \<Rightarrow> 'a) set") (state_of:  "'a \<Rightarrow> 'a")

abbreviation "pointed_set \<equiv> {d. state_of d \<in> dom_funs d \<and> id \<in> dom_funs d}"

typedef ('a) p_set = "pointed_set :: 'a domain_pair set"
  by (rule_tac x="Pair {id} id" in exI, clarsimp)

definition "point_of p = state_of (Rep_p_set p)"

definition "set_of p = dom_funs (Rep_p_set p)"

definition "id_p \<equiv> Abs_p_set (Pair {id} id)"


lemma set_of_id [simp]: "set_of (id_p) = {id}" 
  apply (clarsimp simp: set_of_def id_p_def)
  by (subst Abs_p_set_inverse; clarsimp)

lemma point_of_id [simp]: "point_of (id_p) = id" 
  apply (clarsimp simp: point_of_def id_p_def)
  by (subst Abs_p_set_inverse; clarsimp)

lemma p_set_eqI: "set_of A = set_of B \<Longrightarrow> point_of A = point_of B \<Longrightarrow> A = B"
  by (metis Rep_p_set_inject domain_pair.expand point_of_def set_of_def)

lemma point_in_set[simp]: "point_of S \<in> set_of S"
  by (metis (mono_tags, lifting) Rep_p_set mem_Collect_eq point_of_def set_of_def)

lemma id_in_set[simp]: "id \<in> set_of S"
  by (metis (mono_tags, lifting) Rep_p_set mem_Collect_eq point_of_def set_of_def)

definition "valid_dp S \<equiv> \<forall>f\<in>S. \<forall>g\<in>S. f o g = f" 

lemma commutative_lens_get_set: "valid_lens b \<Longrightarrow> valid_lens c \<Longrightarrow> 
      (\<lambda>s. set b s v) o (\<lambda>s. set c s v') = (\<lambda>s. set c s v') o (\<lambda>s. set b s v) \<Longrightarrow>
          v = get b (set c (set b s v) v')"
  by (metis comp_apply get_set_def valid_lens_def)

lemma surj_setter: "valid_lens l \<Longrightarrow> surj (\<lambda>(s, v). set l s v)"
  apply (clarsimp simp: surj_def)
  by (metis set_get_def valid_lens_def)

lemma lens_commuteI:  "valid_lens b \<Longrightarrow> valid_lens c \<Longrightarrow> 
        ((\<lambda>s. set b s v) o (\<lambda>s. set c s v') = (\<lambda>s. set b s v) \<and> (\<lambda>s. set b s v) o (\<lambda>s. set c s v') = (\<lambda>s. set c s v')) \<or>
      (\<forall>v v'. (\<lambda>s. set b s v) o (\<lambda>s. set c s v') = (\<lambda>s. set c s v') o (\<lambda>s. set b s v)) \<Longrightarrow> (\<lambda>s. set b s v) o (\<lambda>s. set c s v') = (\<lambda>s. set c s v') o (\<lambda>s. set b s v)"
  apply (intro ext; clarsimp)
  apply (elim disjE; clarsimp?)
   apply metis
  by (metis comp_apply)

end