section \<open>Liberation with iteration operators\<close>

theory Iteration_Liberation
imports
  Iteration
  Liberation
  Sequential_Liberation
begin

locale iter_lib = iteration + seq_lib +
  assumes finite_liberation: "E\<^sup>C\<^sub>x ((E\<^sup>C\<^sub>x c) \<^sup>;^ (i-1)) = (E\<^sup>C\<^sub>x c) \<^sup>;^ i"
  constrains lib :: "'b \<Rightarrow> 'a \<Rightarrow> 'a"

begin

text_raw \<open>\DefineSnippet{iterationfixed}{%\<close>
lemma localised_fixed_iteration: "E\<^sup>C\<^sub>x ((E\<^sup>C\<^sub>x c)\<^sup>;^ i) = (E\<^sup>C\<^sub>x c)\<^sup>;^ i" (* Lemma 1 *)
  by (metis finite_liberation localising_first seq_first seq_nil_left seq_right)

text_raw \<open>}%EndSnippet\<close>

lemma localised_finite_iteration: "E\<^sup>C\<^sub>x ((E\<^sup>C\<^sub>x c)\<^sup>\<star>) = (E\<^sup>C\<^sub>x c)\<^sup>\<star>" (* Lemma 2 *)
  by (metis diff_Suc_1 finite_liberation iter_fiter nil_iter seq_nil_right 
      seq_power_0 seq_power_Suc)

lemma localised_omega_iteration: "E\<^sup>C\<^sub>x ((E\<^sup>C\<^sub>x c)\<^sup>\<omega>) = (E\<^sup>C\<^sub>x c)\<^sup>\<omega>" (* Lemma 3 *)
  by (metis abort_remove top.extremum diff_Suc_1 eq_iff finite_liberation iter0 
      last seq_nil_right seq_power_0 seq_power_Suc)

lemma localised_inf_iteration: "E\<^sup>C\<^sub>x ((E\<^sup>C\<^sub>x c)\<^sup>\<infinity>) = (E\<^sup>C\<^sub>x c)\<^sup>\<infinity>"
  by (metis antisym infiter_induct infiter_unfold lib_lattice.remove_lib 
      liberation_stages.axioms(1) liberation_stages_axioms localising_last remove_lib seq_left)

lemma localised_atomic_fixed_iteration: "((E\<^sup>C\<^sub>x a) = (L\<^sup>C\<^sub>x a)) \<Longrightarrow> ((E\<^sup>C\<^sub>x (a\<^sup>;^i)) = ((E\<^sup>C\<^sub>x a)\<^sup>;^i))" (* Lemma 4 *)
  by (metis diff_Suc_1 finite_liberation seq_nil_right seq_power_0 seq_power_Suc)

lemma localised_atomic_finite_iteration: "((E\<^sup>C\<^sub>x a) = (L\<^sup>C\<^sub>x a)) \<Longrightarrow> ((E\<^sup>C\<^sub>x (a\<^sup>\<star>)) = ((E\<^sup>C\<^sub>x a)\<^sup>\<star>))" (* Lemma 5 *)
proof -
  assume "E\<^sup>C\<^sub>x a = L\<^sup>C\<^sub>x a"
  have "\<And>a. a = nil"
    by (metis diff_Suc_1 finite_liberation iter_abort localised_fixed_iteration localised_omega_iteration 
        seq_abort seq_nil_left seq_power_0 seq_power_Suc)
  then show ?thesis
    by metis
qed

lemma localised_atomic_omega_iteration: "((E\<^sup>C\<^sub>x a) = (L\<^sup>C\<^sub>x a)) \<Longrightarrow> ((E\<^sup>C\<^sub>x (a\<^sup>\<omega>)) = ((E\<^sup>C\<^sub>x a)\<^sup>\<omega>))" (* Lemma 6 *)
  by (metis diff_Suc_1 finite_liberation localised_omega_iteration seq_nil_right seq_power_0 seq_power_Suc)

lemma localised_atomic_infinite_iteration: "((E\<^sup>C\<^sub>x a) = (L\<^sup>C\<^sub>x a)) \<Longrightarrow> ((E\<^sup>C\<^sub>x (a\<^sup>\<infinity>)) = ((E\<^sup>C\<^sub>x a)\<^sup>\<infinity>))"
  by (metis (full_types) infiter_iter_magic lib_lattice.magic_remove liberation_stages.axioms(1) 
      liberation_stages_axioms localised_atomic_omega_iteration seq_right)

end

end
