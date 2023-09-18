theory Test_Liberation
imports
  "State_Relations"
  "../General/Liberation"
begin

locale test_liberation = test_sequential_pre + liberation_stages +
  assumes test_lib: "E\<^sup>C\<^sub>x (test p) = test (lib_bool x p)"
  assumes test_first: "E\<^sup>C\<^sub>x (test p) = F\<^sup>C\<^sub>x (test p)"
  assumes test_last: "E\<^sup>C\<^sub>x (test p) = L\<^sup>C\<^sub>x (test p)"
  constrains lib :: "'var \<Rightarrow> 'a \<Rightarrow> 'a"
begin

lemma first_last_nil: "F\<^sup>C\<^sub>x nil = L\<^sup>C\<^sub>x nil"
  by (metis test_first test_last test_top)

lemma lib_first_nil: "F\<^sup>C\<^sub>x nil = nil"
  by (metis test_first test_lib test_top top_apply)

lemma lib_last_nil: "L\<^sup>C\<^sub>x nil = nil"
  using first_last_nil lib_first_nil by auto

lemma lib_nil: "E\<^sup>C\<^sub>x nil = nil"
  by (metis lib_last_nil test_last test_top)

lemma first_last_sigma: "F\<^sup>C\<^sub>x (\<tau> \<Sigma>) = L\<^sup>C\<^sub>x (\<tau> \<Sigma>)"
  using test_first test_last by auto

lemma lib_first_sigma: "F\<^sup>C\<^sub>x (\<tau> \<Sigma>) = (\<tau> \<Sigma>)"
  using test_first test_lib by force

lemma lib_last_sigma: "L\<^sup>C\<^sub>x (\<tau> \<Sigma>) = (\<tau> \<Sigma>)"
  using first_last_sigma lib_first_sigma by auto

lemma lib_sigma: "E\<^sup>C\<^sub>x (\<tau> \<Sigma>) = (\<tau> \<Sigma>)"
  by (simp add: lib_first_sigma test_first)

end
end