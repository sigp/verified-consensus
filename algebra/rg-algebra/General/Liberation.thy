section \<open>Liberation operator\<close>

theory Liberation
imports
  Main
begin
unbundle lattice_syntax

print_locale comm_monoid
print_locale semilattice_neutr
print_locale complete_boolean_algebra
print_locales

unbundle lattice_syntax

(* liberation over commands (refinement lattices) *)
text_raw \<open>\DefineSnippet{liblattice}{}%\<close>
locale lib_lattice =
  fixes lib :: "'b \<Rightarrow> 'a :: complete_distrib_lattice \<Rightarrow> 'a" ("E\<^sup>C\<^sub>_ _" [999, 999] 999)
  assumes remove_lib [simp]: "E\<^sup>C\<^sub>x c \<ge> c" (* 19 *)
    and lib_meet_distrib: "E\<^sup>C\<^sub>x (c \<sqinter> (E\<^sup>C\<^sub>x d)) = (E\<^sup>C\<^sub>x c) \<sqinter> (E\<^sup>C\<^sub>x d)" (* 20 *)
    and lib_commu: "E\<^sup>C\<^sub>y (E\<^sup>C\<^sub>x c) = E\<^sup>C\<^sub>x (E\<^sup>C\<^sub>y c)" (* 21 *)
    and lib_join_distrib: "E\<^sup>C\<^sub>x (\<Squnion>C) = (\<Squnion>c\<in>C. E\<^sup>C\<^sub>x c)" (* 22 *)
begin

text_raw \<open>%EndSnippet\<close> 

declare [[show_types]]

text_raw \<open>\DefineSnippet{liblatticebasic}{a}%\<close>
lemma abort_remove: "E\<^sup>C\<^sub>x \<top> = \<top>" (* 24 *)
  using remove_lib top.extremum_unique by blast

lemma magic_remove: "E\<^sup>C\<^sub>x \<bottom> = \<bottom>" (* 23 *)
  using lib_join_distrib by (metis SUP_empty Sup_empty) 

lemma lib_idem: "(E\<^sup>C\<^sub>x (E\<^sup>C\<^sub>x c)) = (E\<^sup>C\<^sub>x c)" (* 26 *)
  using lib_meet_distrib 
  by (metis abort_remove inf_top.left_neutral)

lemma lib_refine: "(c \<ge> d) \<Longrightarrow> ((E\<^sup>C\<^sub>x c) \<ge> (E\<^sup>C\<^sub>x d))" (* 27 *)
  by (metis dual_order.trans lib_meet_distrib remove_lib inf.order_iff)

text_raw \<open>%EndSnippet\<close>

text_raw \<open>\DefineSnippet{liblatticecomplex}{}%\<close>
lemma binary_nondet: "E\<^sup>C\<^sub>x (c \<squnion> d) = (E\<^sup>C\<^sub>x c) \<squnion> (E\<^sup>C\<^sub>x d)" (* 25 *)
proof -
  have "E\<^sup>C\<^sub>x (c \<squnion> d) = E\<^sup>C\<^sub>x (\<Squnion> {c, d})" 
    by simp
  also have "... = (\<Squnion>q \<in> {c, d}. E\<^sup>C\<^sub>x q)" 
    using lib_join_distrib by blast
  also have "... = (E\<^sup>C\<^sub>x c) \<squnion> (E\<^sup>C\<^sub>x d)"
    by simp
  finally show ?thesis .
qed
text_raw \<open>%EndSnippet\<close>

end

print_locale complete_boolean_algebra

declare [[show_sorts]]

(* liberation over complete boolean algebras *)
text_raw \<open>\DefineSnippet{libboolean}{}%\<close>
locale lib_bool =
  fixes lib_bool :: "'b \<Rightarrow> 'c::complete_boolean_algebra \<Rightarrow> 'c" ("E\<^sup>R\<^sub>_ _" [999, 999] 999)

locale lib_boolean = lib_lattice + lib_bool + lib_lattice lib_bool +
  constrains lib :: "'b \<Rightarrow> 'a::complete_distrib_lattice \<Rightarrow> 'a"
  constrains lib_bool :: "'b \<Rightarrow> 'c::complete_boolean_algebra \<Rightarrow> 'c"
begin
text_raw \<open>%EndSnippet\<close>

text_raw \<open>\DefineSnippet{libuniv}{}%\<close>
definition lib_univ :: "'b \<Rightarrow> 'c :: complete_boolean_algebra \<Rightarrow> 'c"
  where "lib_univ x c \<equiv> -(E\<^sup>R\<^sub>x (-c))"

text_raw \<open>%EndSnippet\<close>

text_raw \<open>\DefineSnippet{libuniversal}{}%\<close>
lemma universal: "E\<^sup>R\<^sub>x (lib_univ x c) = (lib_univ x c)"
text_raw \<open>%EndSnippet\<close>
proof -
  have f1: "lib_univ x c = - E\<^sup>R\<^sub>x (- c)"
    by (metis lib_boolean.lib_univ_def lib_boolean_axioms)
  then have "E\<^sup>R\<^sub>x (lib_univ x c) \<squnion> - E\<^sup>R\<^sub>x (- c) = E\<^sup>R\<^sub>x (lib_univ x c)"
    by (simp add: sup.absorb2 sup_commute)
  then have f2: "E\<^sup>R\<^sub>x (lib_univ x c) = (E\<^sup>R\<^sub>x (lib_univ x c) \<sqinter> E\<^sup>R\<^sub>x (- c)) \<squnion> - E\<^sup>R\<^sub>x (- c)"
    by (simp add: sup_inf_distrib2)
  have "\<bottom> = E\<^sup>R\<^sub>x (lib_univ x c) \<sqinter> E\<^sup>R\<^sub>x (- c)"
    using f1 by (metis (no_types) compl_inf_bot lib_lattice.magic_remove lib_lattice_axioms lib_meet_distrib)
  then show ?thesis
    using f2 f1 by auto
qed

end

(* liberation over commands in their first and last stages *)
text_raw \<open>\DefineSnippet{liberationstages}{}%\<close>
locale lib_first =
  fixes lib_first :: "'b \<Rightarrow> 'a::complete_distrib_lattice \<Rightarrow> 'a" ("F\<^sup>C\<^sub>_ _" [999, 999] 999) (* must enter \supC first *)

locale lib_last =
  fixes lib_last :: "'b \<Rightarrow> 'a::complete_distrib_lattice \<Rightarrow> 'a" ("L\<^sup>C\<^sub>_ _" [999, 999] 999)

locale liberation_stages = lib_lattice + lib_first + lib_last + 
    lib_lattice lib_first + lib_lattice lib_last +
  assumes first: "E\<^sup>C\<^sub>x c \<ge> F\<^sup>C\<^sub>x c" (* 37 *)
    and last: "E\<^sup>C\<^sub>x c \<ge> L\<^sup>C\<^sub>x c" (* 38 *)
    and lib_with_first: "E\<^sup>C\<^sub>x (F\<^sup>C\<^sub>y c) = F\<^sup>C\<^sub>y (E\<^sup>C\<^sub>x c)" (* 39 *)
    and lib_with_last: "E\<^sup>C\<^sub>x (L\<^sup>C\<^sub>y c) = L\<^sup>C\<^sub>y (E\<^sup>C\<^sub>x c)" (* 40 *)
    and first_with_last: "F\<^sup>C\<^sub>x (L\<^sup>C\<^sub>y c) = F\<^sup>C\<^sub>y (L\<^sup>C\<^sub>x c)" (* 41 *)
begin
text_raw \<open>%EndSnippet\<close>

lemma first_idem: "F\<^sup>C\<^sub>x F\<^sup>C\<^sub>x c = F\<^sup>C\<^sub>x c"
  by (meson lib_lattice.lib_idem liberation_stages.axioms(2) liberation_stages_axioms)

lemma first_commu: "E\<^sup>C\<^sub>x F\<^sup>C\<^sub>x c = F\<^sup>C\<^sub>x E\<^sup>C\<^sub>x c"
  by (simp add: lib_with_first)

lemma remove_first: "F\<^sup>C\<^sub>x c \<ge> c"
  by (meson lib_lattice.remove_lib liberation_stages.axioms(2) liberation_stages_axioms)

lemma last_idem: "L\<^sup>C\<^sub>x L\<^sup>C\<^sub>x c = L\<^sup>C\<^sub>x c"
  by (simp add: lib_idem)

lemma last_commu: "E\<^sup>C\<^sub>x L\<^sup>C\<^sub>x c = L\<^sup>C\<^sub>x E\<^sup>C\<^sub>x c"
  by (simp add: lib_with_last)

lemma remove_last: "L\<^sup>C\<^sub>x c \<ge> c"
  by (simp)

text_raw \<open>\DefineSnippet{libstagesproperties}{}%\<close>
lemma localising_last: "E\<^sup>C\<^sub>x c = L\<^sup>C\<^sub>x E\<^sup>C\<^sub>x c"
  by (metis antisym last lib_lattice.lib_idem liberation_stages_axioms 
      liberation_stages_def remove_lib)

lemma localising_first: "E\<^sup>C\<^sub>x c = F\<^sup>C\<^sub>x E\<^sup>C\<^sub>x c"
  by (metis antisym first lib_lattice.lib_idem liberation_stages_axioms 
      liberation_stages_def remove_first)
text_raw \<open>%EndSnippet\<close>

end

(* liberation over complete boolean algebras in their different states *)
text_raw \<open>\DefineSnippet{libboolstages}{}%\<close>
locale bool_first =
  fixes bool_first :: "'b \<Rightarrow> 'a::complete_boolean_algebra \<Rightarrow> 'a" ("F\<^sup>R\<^sub>_ _" [999, 999] 999)

locale bool_last =
  fixes bool_last :: "'b \<Rightarrow> 'a::complete_boolean_algebra \<Rightarrow> 'a" ("L\<^sup>R\<^sub>_ _" [999, 999] 999)

locale lib_boolean_stages = lib_boolean + bool_first + bool_last + liberation_stages + 
    liberation_stages lib_bool bool_first bool_last
text_raw \<open>%EndSnippet\<close>


(* liberation over types coerced to sets later in the theory *)
text_raw \<open>\DefineSnippet{libboolsets}{}%\<close>
locale lib_bool_sets =
  fixes lib_bool_sets :: "'b \<Rightarrow> 'a::complete_boolean_algebra \<Rightarrow> 'a" ("E\<^sup>S\<^sub>_ _" [999, 999] 999)

locale bool_first_sets =
  fixes bool_first_sets :: "'b \<Rightarrow> 'a::complete_boolean_algebra \<Rightarrow> 'a" ("F\<^sup>S\<^sub>_ _" [999, 999] 999)

locale bool_last_sets =
  fixes bool_last_sets :: "'b \<Rightarrow> 'a::complete_boolean_algebra \<Rightarrow> 'a" ("L\<^sup>S\<^sub>_ _" [999, 999] 999)

locale lib_boolean_sets = lib_bool_sets + bool_first_sets + bool_last_sets + liberation_stages +
    liberation_stages lib_bool_sets bool_first_sets bool_last_sets
text_raw \<open>%EndSnippet\<close>

locale liberation = lib_boolean_sets + lib_boolean_stages +
  constrains lib_bool_sets :: "'b \<Rightarrow> 'e::complete_boolean_algebra \<Rightarrow> 'e"
        and lib :: "'b \<Rightarrow> 'd::complete_distrib_lattice \<Rightarrow> 'd"
        and lib_bool :: "'b \<Rightarrow> 'a::complete_boolean_algebra \<Rightarrow> 'a"
  

end
