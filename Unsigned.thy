theory Unsigned
  imports Main HOL.Nat
begin

datatype u8 = u8 nat
datatype u64 = u64 nat

primrec u64_to_nat :: "u64 \<Rightarrow> nat" where
  "u64_to_nat (u64 n) = n"

definition valid_u64 :: "u64 \<Rightarrow> bool" where
  "valid_u64 n \<equiv> u64_to_nat n < 2 ^ 64"

definition check_bin_op ::
  "('a \<Rightarrow> 'b) \<Rightarrow>
   ('b \<Rightarrow> 'a) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow>
   ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
   'a \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "check_bin_op unwrap wrap check op x y \<equiv>
    let result = wrap (op (unwrap x) (unwrap y)) in
    if check result then Some result else None"

definition u64_add :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" (infixl ".+" 65) where
  "u64_add x y \<equiv> check_bin_op u64_to_nat u64 valid_u64 (+) x y"

definition u64_sub :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" (infixl ".-" 65) where
  "u64_sub x y \<equiv>
    if u64_to_nat x \<ge> u64_to_nat y then
      check_bin_op u64_to_nat u64 valid_u64 (-) x y
    else
      None"

definition u64_mul :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" (infixl ".*" 70) where
  "u64_mul x y \<equiv> check_bin_op u64_to_nat u64 valid_u64 (*) x y"

definition u64_div :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" (infixl "\\" 70) where
  "u64_div x y \<equiv>
    if y = u64 0 then
      None
    else
      check_bin_op u64_to_nat u64 valid_u64 ((div)) x y"

(* Sanity check lemmas *)
lemma u64_add_overflow_int_max: "u64 (2 ^ 64 - 1) .+ u64 1 = None"
  by (clarsimp simp: u64_add_def valid_u64_def check_bin_op_def)

lemma u64_add_overflow_contradiction: "(u64 (2 ^ 64 - 1) .+ u64 1 = Some (u64 0)) \<Longrightarrow> False"
  by (clarsimp simp: u64_add_def valid_u64_def check_bin_op_def)

lemma u64_sub_overflow_zero: "u64 0 .- u64 1 = None"
  by (clarsimp simp: u64_sub_def valid_u64_def check_bin_op_def)

lemma u64_div_zero: "n \\ u64 0 = None"
  by (clarsimp simp: u64_div_def valid_u64_def check_bin_op_def)

end