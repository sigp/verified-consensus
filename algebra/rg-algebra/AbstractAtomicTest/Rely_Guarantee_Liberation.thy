theory Rely_Guarantee_Liberation
  imports Relies_Guarantees
          Test_Liberation
begin

locale rg_lib = relies_guarantees + test_liberation + lib_bool +
  constrains env      :: "('state \<times> 'state) set \<Rightarrow> 'a"
  constrains pgm      :: "('state \<times> 'state) set \<Rightarrow> 'a"
  constrains test     :: "'state set \<Rightarrow> 'a" 
  constrains lib      :: "'varname \<Rightarrow> 'a \<Rightarrow> 'a"
  constrains lib_bool :: "'varname \<Rightarrow> 'state rel \<Rightarrow> 'state rel"
begin

(* localise over relies and guarantees *)

text_raw \<open>\DefineSnippet{relyuniv}{\<close>
lemma localise_rely: "E\<^sup>C\<^sub>x (rely r) = rely (lib_univ x r)" (* Lemma 7 *)
text_raw \<open>}%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot 
    test.hom_iso_eq test_lib test.hom_not test_top
  by (metis (full_types))

text_raw \<open>\DefineSnippet{librely}{\<close>
lemma lib_rely: "r = (E\<^sup>R\<^sub>x r) \<Longrightarrow> (rely (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (rely r))"
text_raw \<open>}%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot 
      test.hom_iso_eq test_lib test.hom_not test_top
  by (metis (full_types))

(* Lemma 8 - localise_gdr *)
text_raw \<open>\DefineSnippet{libguar}{\<close>
lemma localise_guar: "((E\<^sup>R\<^sub>x r) = (bool_last x r)) \<Longrightarrow> (guar (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (guar r))" (* 68 *)
text_raw \<open>}%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot test.hom_iso_eq test_lib 
      test.hom_not test_top
  by (metis (full_types))

text_raw \<open>\DefineSnippet{libdem}{\<close>
lemma localise_dem: "((E\<^sup>R\<^sub>x r) = (bool_last x r)) \<Longrightarrow> (demand (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (demand r))" (* 69 *)
text_raw \<open>}%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot test.hom_iso_eq test_lib 
      test.hom_not test_top
  by (metis (full_types))

lemma localise_relies: "((E\<^sup>R\<^sub>x r) = r) \<Longrightarrow> (rely (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (rely r))" (* 70 *)
  using lib_rely by blast

end

end