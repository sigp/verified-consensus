theory Utils
  imports Unsigned Types Invariants
begin

primrec assert :: "bool \<Rightarrow> unit option" where
  "assert True = Some ()" |
  "assert False = None"

definition enumerate :: "'a list \<Rightarrow> (u64 \<times> 'a) list" where
  "enumerate l \<equiv> zip (map u64 [0..<length l]) l"

definition safe_sum :: "u64 set \<Rightarrow> u64 option" where
  "safe_sum s \<equiv> foldl (\<lambda>acc x. acc \<bind> ((.+) x)) (Some (u64 0)) (sorted_list_of_set s)"

(* FIXME(sproul): return optional value rather than undefined? *)
definition list_index :: "'a List \<Rightarrow> u64 \<Rightarrow> 'a" where
  "list_index l i \<equiv> list_inner l ! u64_to_nat i"

end