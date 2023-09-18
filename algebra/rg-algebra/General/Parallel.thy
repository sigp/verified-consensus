section \<open>Parallel operator \label{S:parallel}\<close>

theory Parallel
imports Refinement_Lattice Abstract_Sync
begin

subsection \<open>Basic parallel operator\<close>


locale par =
  fixes par :: "'a::top \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<parallel>" 75)
  assumes par_abort:   "\<top> \<parallel> c = \<top>"    (* ++ *)
text \<open>The parallel operator has as an annihilator of the abort (@{term "\<top>"}).\<close>

locale skip = 
  fixes skip :: "'a"  ("skip") 

locale parallel = par + skip + par: comm_monoid par skip
begin

text \<open>The parallel operator is associative, commutative and has identity @{term "skip"},
  that is, it forms an commutative monoid.
  \<close>

lemmas [algebra_simps, field_simps] =
  par.assoc
  par.commute
  par.left_commute

lemmas par_assoc = par.assoc            (* 36 *)
lemmas par_commute = par.commute        (* 37 *)
lemmas par_skip = par.right_neutral     (* 38 *)
lemmas par_skip_left = par.left_neutral (* 38 + 37 *)

lemma par_abort_right: "c \<parallel> \<top> = \<top>"
  by (simp add: par_abort par_commute)

end


subsection \<open>Distributed parallel\<close>

text \<open>
  The parallel operator distributes across arbitrary non-empty non-deterministic choice.
\<close>
locale par_distrib = parallel + abstract_sync par
end
