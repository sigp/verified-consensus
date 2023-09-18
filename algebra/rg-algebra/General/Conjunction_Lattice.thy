theory Conjunction_Lattice
imports Conjunction
begin

context conjunction begin

sublocale conj_order: semilattice_neutr_order conj chaos "\<lambda>x y. conj x y = x"  "\<lambda>x y. conj x y = x \<and> x \<noteq> y"
  apply (standard; clarsimp?)
   apply fastforce+
  done

sublocale semilattice_inf conj "\<lambda>x y. conj x y = x"  "\<lambda>x y. conj x y = x \<and> x \<noteq> y"
  apply (standard; safe?; clarsimp?)
    apply (fastforce simp: conj.commute)+
   apply (metis local.conj_assoc)
  using local.conj_commute by force

end

end