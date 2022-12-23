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

definition list_index :: "'a List \<Rightarrow> u64 \<Rightarrow> 'a option" where
  "list_index l i \<equiv>
    if i < u64 (length (list_inner l)) then
      Some (list_inner l ! u64_to_nat i)
    else
      None"

definition unsafe_list_index :: "'a List \<Rightarrow> u64 \<Rightarrow> 'a" where
  "unsafe_list_index l i \<equiv> the (list_index l i)"

definition vector_index :: "'a Vector \<Rightarrow> u64 \<Rightarrow> 'a option" where
  "vector_index v i \<equiv>
    if i < u64 (length (vector_inner v)) then
      Some (vector_inner v ! u64_to_nat i)
    else
      None"

definition unsafe_vector_index :: "'a Vector \<Rightarrow> u64 \<Rightarrow> 'a" where
  "unsafe_vector_index v i \<equiv> the (vector_index v i)"

definition shift_and_clear_bitvector :: "Config \<Rightarrow> Bitvector \<Rightarrow> Bitvector" where
  "shift_and_clear_bitvector c bv \<equiv>
    Bitvector ([False] @ take (u64_to_nat (JUSTIFICATION_BITS_LENGTH c) - 1) (bitvector_inner bv))"

definition bitvector_update :: "Bitvector \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> Bitvector" where
  "bitvector_update bv i v \<equiv> Bitvector (list_update (bitvector_inner bv) i v)"

definition bitvector_all :: "Bitvector \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "bitvector_all bv start end \<equiv>
    list_all (\<lambda>x. x) (take (end - start) (drop start (bitvector_inner bv)))"

definition flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" where
  "flip f x y \<equiv> f y x"

function integer_squareroot_aux :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> (u64 \<times> u64) option" where
  "integer_squareroot_aux x y n =
    (if y < x then
      Some (x, y)
    else do {
      let x' = y;
      y' \<leftarrow> (x' .+ n);
      integer_squareroot_aux x' y' n
  })"
  by auto

definition integer_squareroot :: "u64 \<Rightarrow> u64 option" where
  "integer_squareroot n \<equiv> do {
    let x = n;
    y \<leftarrow> (x .+ u64 1) \<bind> (flip (\\) (u64 2));
    (x', _) \<leftarrow> integer_squareroot_aux x y n;
    Some x'
  }"

end