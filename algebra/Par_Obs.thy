theory Par_Obs
imports Ordered_Semigroups
begin

locale to_env = fixes to_env

locale par =
  fixes par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<parallel>" 75)

locale par_elem = par + to_env + ab_ordered_semigroup par + top_semigroup par + sync_semigroup par to_env 
begin

sublocale conv_skip: skip dunit done

sublocale conv_parallel: parallel convolute dunit
  apply (standard)
   apply (rule conv_top_strict.top_strict)
  by fastforce

sublocale par_distrib convolute dunit ..

end

end