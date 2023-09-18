section \<open>Abstract view of tests\<close>

theory Abstract_Test
imports
  "../General/Refinement_Lattice"
  "../General/Abstract_Hom"
begin

locale abstract_test_commands_pre =
  fixes test :: "'b::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice" ("\<tau>")
  assumes test_Sup: "\<tau>(Sup P) = (\<Squnion>s\<in>P. \<tau> s)"

locale abstract_test_commands = abstract_test_commands_pre + test: abstract_hom_commands \<tau> 
begin                                               

lemma test_de_morgan: 
  assumes test_commands: "\<tau>(p) = t1 \<and> \<tau>(q) = t2"
  shows "test.negate (t1 \<squnion> t2) = test.negate t1 \<sqinter> test.negate t2"
proof -
  have f1: "\<tau> (- p) = test.negate t1" using test_commands by auto
  have f2: "test.negate t2 = \<tau> (- q)" using test_commands by auto
  have "t1 \<squnion> t2 = \<tau> (p \<squnion> q)" using test_commands test.hom_sup by presburger
  then have "test.negate t1 \<sqinter> test.negate t2 = test.negate (t1 \<squnion> t2)"
    using f1 f2 by (metis test.hom_inf test.hom_not compl_sup)
  then show ?thesis 
    using test_commands by fastforce
qed
end
end
