theory Utils
  imports Unsigned Types
begin

primrec assert :: "bool \<Rightarrow> unit option" where
  "assert True = Some ()" |
  "assert False = None"

definition enumerate :: "'a list \<Rightarrow> (u64 \<times> 'a) list" where
  "enumerate l \<equiv> zip (map u64 [0..<length l]) l"

end