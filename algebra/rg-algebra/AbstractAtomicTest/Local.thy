section \<open>Local variables\<close>

theory Local
imports
  "State_Relations"
  "Test_Liberation"
  "Sync_Liberation"
begin



locale locals_pre = state_relations + test_liberation  + 
                    liberation +  
                    inf: sync_liberation inf + 
                    conj: sync_liberation conj + 
                    par: sync_liberation par +
  constrains seq      :: "'a :: refinement_lattice \<Rightarrow> 'a \<Rightarrow> 'a" 
  constrains pgm      :: "('state \<times> 'state) set \<Rightarrow> 'a"
  constrains env      :: "('state \<times> 'state) set \<Rightarrow> 'a"
  constrains test     :: "'state set \<Rightarrow> 'a"
  constrains set_var  :: "'var \<Rightarrow> 'v \<Rightarrow> 'state \<Rightarrow> 'state"
  constrains get_var  :: "'var \<Rightarrow> 'state \<Rightarrow> 'v" 
  constrains lib      :: "'var \<Rightarrow> 'a \<Rightarrow> 'a"
  constrains lib_bool_sets :: "'var \<Rightarrow> 'state set \<Rightarrow> 'state set"
  constrains lib_bool :: "'var \<Rightarrow> ('state \<times> 'state) set \<Rightarrow> ('state \<times> 'state) set"
  constrains iter :: "'a \<Rightarrow> 'a"

locale locals = locals_pre +
  assumes lib_rel_first : "F\<^sup>R\<^sub>x r = id_bar({|x|}) O r" 
  assumes lib_rel_last : "L\<^sup>R\<^sub>x r = r O id_bar({|x|})"
begin

lemma last_univ: "L\<^sup>R\<^sub>x (id(x)) = UNIV"
  using lib_rel_last id_univ by simp

lemma rel_univ: "E\<^sup>R\<^sub>x (id(x)) = UNIV"
  using last last_univ by blast  

lemma localise_rely: "E\<^sup>C\<^sub>x (rely r) = rely (lib_univ x r)" (* Lemma 7 *)
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot 
    test.hom_iso_eq test_lib test.hom_not test_top
  by (metis (full_types))

text_raw \<open>\DefineSnippet{librely}{}\<close>
lemma lib_rely: "r = (E\<^sup>R\<^sub>x r) \<Longrightarrow> (rely (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (rely r))"
text_raw \<open>%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot 
      test.hom_iso_eq test_lib test.hom_not test_top
  by (metis (full_types))

(* Lemma 8 - localise_gdr *)
text_raw \<open>\DefineSnippet{libguar}{}\<close>
lemma localise_guar: "((E\<^sup>R\<^sub>x r) = (bool_last x r)) \<Longrightarrow> (guar (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (guar r))" (* 68 *)
text_raw \<open>%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot test.hom_iso_eq test_lib 
      test.hom_not test_top
  by (metis (full_types))

text_raw \<open>\DefineSnippet{libdem}{}\<close>
lemma localise_dem: "((E\<^sup>R\<^sub>x r) = (bool_last x r)) \<Longrightarrow> (demand (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (demand r))" (* 69 *)
text_raw \<open>%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot test.hom_iso_eq test_lib 
      test.hom_not test_top
  by (metis (full_types))

lemma localise_relies: "((E\<^sup>R\<^sub>x r) = r) \<Longrightarrow> (rely (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (rely r))" (* 70 *)
  using lib_rely by blast


lemma demand_chaos : "E\<^sup>C\<^sub>x(demand (id(x))) = chaos"
proof -
  have "E\<^sup>C\<^sub>x(demand (id(x))) = demand (E\<^sup>R\<^sub>x (id(x)))" by (metis last_univ localise_dem rel_univ)
  also have "... = demand(UNIV)" by (simp add: rel_univ)
  also have "... = chaos" using restrict_iter_top by auto
  finally show ?thesis.
qed

lemma guar_chaos : "E\<^sup>C\<^sub>x(guar (id(x))) = chaos"
proof -
  have "E\<^sup>C\<^sub>x(guar (id(x))) = guar (E\<^sup>R\<^sub>x (id(x)))" by (metis last_univ localise_guar rel_univ)
  also have "... = guar (UNIV)" by (simp add: rel_univ)
  also have "... = chaos" using guar_top by blast
  finally show ?thesis.
qed

(* introduces local scopes *)
text_raw \<open>\DefineSnippet{liblocal}{}\<close>
definition
  local :: "'c \<Rightarrow> 'a::refinement_lattice  \<Rightarrow> 'a" ("(3local _ ./ _)" [0, 10] 10)
where
  local_def [simp]: "(local x . c) = E\<^sup>C\<^sub>x(demand (id(x)) \<iinter> c) \<iinter> (guar (id(x)))"
text_raw \<open>%EndSnippet\<close>

(* introduces local variable blocks *)
text_raw \<open>\DefineSnippet{libvar}{}\<close>
definition
  var :: "'c \<Rightarrow> 'a \<Rightarrow> 'a" ("(3var _ ./ _)" [0, 10] 10)
where
  var_def [simp]: "(var x . c) = idle ; (local x . c) ; idle"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>\DefineSnippet{localproofs}{}\<close>
lemma local_default_guar: "(local x . c) = (local x . c) \<iinter> (guar (id(x)))"
  by simp

lemma var_default_guar: "(var x . c) = (var x . c) \<iinter> (guar (id(x)))"
proof - 
  have id_Id: "id(x) \<inter> Id = Id"
    using id_set_def local.id_def by auto 
  have a0: "(var x . c) = idle ; (local x . c) ; idle" by simp
  also have a1: "... = (idle \<iinter> guar (id(x))) ; ((local x . c) \<iinter> guar (id(x))) ; (idle \<iinter> guar (id(x)))"
  proof -
    have "guar Id = guar (local.id x) \<iinter> guar Id"
      using guar_merge id_Id by presburger
    then show ?thesis
      using idle_def local.conj_assoc local.conj_commute by force
  qed    
  also have a2: "... = (idle ; (local x . c) ; idle) \<iinter> guar (id(x))" using guar_distrib_seq_eq
    by (metis conj.sync_commute)
  also have a3: "... = (var x . c) \<iinter> guar (id(x))" by auto
  finally show ?thesis.
qed

lemma local_default_rely : "(local x . c) = (local x . c \<iinter> rely (id(x)))"
  using conj.sync_assoc conj.sync_commute local_def rely_demand by metis

lemma var_default_rely : "(var x . c) = (var x . c \<iinter> rely (id(x)))"
  using local_default_rely by simp

lemma introduce_local :
  assumes "c = E\<^sup>C\<^sub>x c \<iinter> guar (id(x))"
  shows "c = (local x . E\<^sup>C\<^sub>x c)"
proof -
  have "(local x . E\<^sup>C\<^sub>x c) = E\<^sup>C\<^sub>x(demand (id(x))) \<iinter> E\<^sup>C\<^sub>x c \<iinter> guar (id(x))"
    using conj.sync_lib by simp
  also have "\<dots> = E\<^sup>C\<^sub>x(demand (id(x))) \<iinter> c"
    using assms conj.sync_assoc by metis
  also have "\<dots> = c"
    using demand_chaos conj_chaos_left by simp
  finally show ?thesis by simp
qed

lemma introduce_local_refine :
  assumes "c \<ge> E\<^sup>C\<^sub>x c \<iinter> guar (id(x))"
  shows "c \<ge> (local x . E\<^sup>C\<^sub>x c)"
proof -
  have a: "E\<^sup>C\<^sub>x(guar (id(x)) \<iinter> E\<^sup>C\<^sub>x c) = E\<^sup>C\<^sub>x(guar (id(x))) \<iinter> E\<^sup>C\<^sub>x c"
  using conj.sync_lib by auto
  have b: "E\<^sup>C\<^sub>x(E\<^sup>C\<^sub>x c \<iinter> guar (id(x))) \<iinter> guar (id(x)) = E\<^sup>C\<^sub>x c \<iinter> guar (id(x))"
  proof -
    have "E\<^sup>C\<^sub>x(E\<^sup>C\<^sub>x c \<iinter> guar (id(x))) \<iinter> guar (id(x)) = (E\<^sup>C\<^sub>x c) \<iinter> E\<^sup>C\<^sub>x(guar (id(x))) \<iinter> guar (id(x))"
      using a conj_commute by auto
    also have "\<dots> = E\<^sup>C\<^sub>x c \<iinter> guar (id(x))" using guar_chaos by simp
    finally show ?thesis.
  qed
  then have "c \<ge> E\<^sup>C\<^sub>x c \<iinter> guar (id(x))" (is "_ \<ge> ?rhs")
    using assms by simp
  also have "?rhs = (local x . E\<^sup>C\<^sub>x(E\<^sup>C\<^sub>x c \<iinter> guar (id(x))))"
    using introduce_local b by auto
  also have "\<dots> = (local x . E\<^sup>C\<^sub>x c \<iinter> E\<^sup>C\<^sub>x(guar (id(x))))"
    using conj_commute a by auto
  also have "\<dots> = (local x . E\<^sup>C\<^sub>x c)" using guar_chaos by auto
  finally show ?thesis.
qed

lemma introduce_var :
  assumes "c = idle;c;idle"
      and "c = E\<^sup>C\<^sub>x c \<iinter> guar (id(x))"
    shows "c = (var x . E\<^sup>C\<^sub>x c)"
  using assms introduce_local local_def by simp

lemma introduce_var_refine :
  assumes "c \<ge> idle;c;idle"
      and "c \<ge> E\<^sup>C\<^sub>x c \<iinter> guar (id(x))"
    shows "c \<ge> (var x . E\<^sup>C\<^sub>x c)"
proof -
  have "c \<ge> idle;c;idle" (is "_ \<ge> ?rhs") using assms(1) by simp
  also have "?rhs \<ge> idle;(local x . E\<^sup>C\<^sub>x c);idle" (is "_ \<ge> ?rhs")
    using assms(2) introduce_local_refine seq_mono by simp
  also have "?rhs = (var x . E\<^sup>C\<^sub>x c)" unfolding var_def by simp
  finally show ?thesis.
qed

lemma local_distribute :
  assumes "E\<^sup>C\<^sub>x d = d"
  shows "(local x . c) \<iinter> d = (local x . c \<iinter> d)"
proof -
  have "demand (id(x)) \<iinter> (c \<iinter> d) = c \<iinter> (demand (id(x)) \<iinter> d)"
    by (simp add: conj.sync_assoc local.conj_commute)
  then have "E\<^sup>C\<^sub>x (demand (id(x)) \<iinter> (c \<iinter> d)) = E\<^sup>C\<^sub>x (c \<iinter> demand (id(x))) \<iinter> E\<^sup>C\<^sub>x d"
    by (metis (full_types) assms conj.sync_assoc conj.sync_lib)
  then show ?thesis using assms local.conj_assoc local.conj_commute by fastforce
qed

lemma var_guar_distribute :
  assumes "refl g"
      and "g = E\<^sup>R\<^sub>x g"
    shows "(var x . c) \<iinter> guar g = (var x . c \<iinter> guar g)"
proof -
  have "(var x . c) \<iinter> guar g = (idle;(local x . c);idle) \<iinter> guar g"
    using local_def by simp
  also have "\<dots> = (idle \<iinter> guar g);((local x . c) \<iinter> guar g);(idle \<iinter> guar g)"
    using conj.sync_commute guar_distrib_seq_eq by metis
  also have "\<dots> = idle;((local x . c) \<iinter> guar g);idle"
    using assms(1) conj.sync_commute guar_idle by auto
  also have "\<dots> = idle;(local x . c \<iinter> guar g);idle"
  proof -
    have distrib_guar : "g = E\<^sup>R\<^sub>x g \<Longrightarrow> (local x . c) \<iinter> guar g = (local x . c \<iinter> guar g)"
      using localise_guar local_distribute localising_last by metis
    then show "?thesis" using assms(2) by simp
  qed
  also have "\<dots> = (var x . c \<iinter> guar g)"
    unfolding var_def by simp
  finally show ?thesis.
qed

lemma var_guar :
  assumes "refl g"
  shows "(var x . c \<iinter> guar g) = (var x . c \<iinter> guar g) \<iinter> guar((id(x)) \<inter> E\<^sup>R\<^sub>x g)"
proof -
  have a: "g \<subseteq> E\<^sup>R\<^sub>x g" using remove_lib by auto
  have lib_lib: "E\<^sup>R\<^sub>x g = E\<^sup>R\<^sub>x (E\<^sup>R\<^sub>x g)"
    using lib_boolean_axioms lib_boolean_def lib_lattice.lib_idem by fastforce
  have lib_refl: "refl (E\<^sup>R\<^sub>x g)" 
    using UNIV_Times_UNIV iso_tuple_UNIV_I refl_onI refl_on_def subset_UNIV subset_eq assms a by metis
  have "(var x . c \<iinter> guar g) = (var x . c \<iinter> guar(g \<inter> E\<^sup>R\<^sub>x g))"
    by (metis (no_types, lifting) a equalityI le_inf_iff order_refl)
  also have "\<dots> = (var x . c \<iinter> guar g \<iinter> guar(E\<^sup>R\<^sub>x g))" 
    using guar_merge conj.sync_assoc by metis
  also have "\<dots> = (var x . c \<iinter> guar g) \<iinter> guar(E\<^sup>R\<^sub>x g) \<iinter> guar (id(x))" 
    using var_default_guar var_guar_distribute lib_lib lib_refl by simp
  also have "\<dots> = (var x . c \<iinter> guar g) \<iinter> guar((id(x)) \<inter> E\<^sup>R\<^sub>x g)"
    using guar_merge conj.sync_assoc inf_commute by metis
  finally show ?thesis.
qed

lemma var_rely_distribute_refine :
  "(var x . c) \<iinter> rely r \<ge> (var x . c \<iinter> rely(E\<^sup>R\<^sub>x r))"
proof -
  have "(var x . c) \<iinter> rely r = (idle;(local x . c);idle) \<iinter> rely r"
    using var_def by simp
  also have "\<dots> \<ge> idle;((local x . c) \<iinter> rely r);idle" (is "_ \<ge> ?rhs")
  proof -
    have "(idle;(local x . c);idle) \<iinter> rely r \<ge> (rely r \<iinter> (idle;(local x . c)));(rely r \<iinter> idle)" (is "_ \<ge> ?rhs")
      using rely_seq_distrib conj_commute by metis
    also have "?rhs \<ge> (rely r \<iinter> idle);(rely r \<iinter> (local x . c));(rely r \<iinter> idle)" (is "_ \<ge> ?rhs")
      using rely_seq_distrib seq_mono by blast
    also have "?rhs \<ge> idle;((local x . c) \<iinter> rely r);idle"
      using rely_remove conj_commute seq_mono by simp
    finally show ?thesis.
  qed
  also have "?rhs \<ge> idle;((local x . c) \<iinter> rely(E\<^sup>R\<^sub>x r));idle" (is "_ \<ge> ?rhs")
    using conj.sync_mono lib_boolean_axioms rely_weaken seq_mono by auto
  also have "?rhs = idle;(local x . c \<iinter> rely(E\<^sup>R\<^sub>x r));idle"
    using localise_rely local_distribute by (metis (no_types, lifting) lib_lattice.lib_idem lib_rely 
          liberation_stages.axioms(1) liberation_stages_axioms)
  also have "\<dots> = (var x . c \<iinter> rely(E\<^sup>R\<^sub>x r))" unfolding var_def by simp
  finally show ?thesis.
qed

lemma var_distribute_rely :
  "(var x . c) \<iinter> rely r \<ge> (var x . c \<iinter> rely ((id(x)) \<inter> E\<^sup>R\<^sub>x r))"
proof -
  have "(var x . c) \<iinter> rely r = (var x . c \<iinter> rely (id(x))) \<iinter> rely r"
    using var_default_rely by auto
  also have "\<dots> \<ge> (var x . c \<iinter> rely ((id(x)) \<inter> E\<^sup>R\<^sub>x r))"
    using var_rely_distribute_refine rely_conj_rely conj.sync_assoc by metis
  finally show ?thesis.
qed

text_raw \<open>%EndSnippet\<close>

end

end
