theory Unsigned
  imports Main HOL.Nat "HOL-Library.Monad_Syntax"
begin

datatype u8 = u8 nat
datatype u64 = u64 nat
datatype Slot = Slot u64
datatype Epoch = Epoch u64

primrec u64_to_nat :: "u64 \<Rightarrow> nat" where
  "u64_to_nat (u64 n) = n"

primrec slot_to_u64 :: "Slot \<Rightarrow> u64" where
  "slot_to_u64 (Slot n) = n"

primrec epoch_to_u64 :: "Epoch \<Rightarrow> u64" where
  "epoch_to_u64 (Epoch n) = n"

definition valid_u64 :: "u64 \<Rightarrow> bool" where
  "valid_u64 n \<equiv> u64_to_nat n < 2 ^ 64"

definition valid_slot :: "Slot \<Rightarrow> bool" where
  "valid_slot s \<equiv> valid_u64 (slot_to_u64 s)"

definition valid_epoch :: "Epoch \<Rightarrow> bool" where
  "valid_epoch e \<equiv> valid_u64 (epoch_to_u64 e)"

consts
  unsigned_add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"
  unsigned_sub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"
  unsigned_mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"
  unsigned_div :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option"

notation
  unsigned_add (infixl ".+" 65) and
  unsigned_sub (infixl ".-" 65) and
  unsigned_mul (infixl ".*" 70) and
  unsigned_div (infixl "\\" 70)

definition check_bin_op_then ::
  "('a \<Rightarrow> 'b) \<Rightarrow>
   ('b \<Rightarrow> 'a) \<Rightarrow>
   ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow>
   ('b \<Rightarrow> 'b \<Rightarrow> 'b option) \<Rightarrow>
   'a \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "check_bin_op_then unwrap wrap arg_check check op x y \<equiv>
    if arg_check x y then do {
      result_b \<leftarrow> op (unwrap x) (unwrap y);
      let result_a = wrap result_b;
      if check result_a then Some result_a else None
    } else None"

definition check_bin_op ::
  "('a \<Rightarrow> 'b) \<Rightarrow>
   ('b \<Rightarrow> 'a) \<Rightarrow>
   ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow>
   ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
   'a \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "check_bin_op unwrap wrap arg_check check op \<equiv>
    check_bin_op_then unwrap wrap arg_check check (\<lambda>x y. Some (op x y))"

definition any_args :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "any_args _ _ \<equiv> True"

definition u64_add :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" where
  "u64_add \<equiv> check_bin_op u64_to_nat u64 any_args valid_u64 (+)"

definition u64_sub :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" where
  "u64_sub \<equiv>
    check_bin_op u64_to_nat u64 (\<lambda>x y. u64_to_nat x \<ge> u64_to_nat y) valid_u64 (-)"

definition u64_mul :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" where
  "u64_mul \<equiv> check_bin_op u64_to_nat u64 any_args valid_u64 (*)"

definition u64_div :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 option" where
  "u64_div \<equiv> check_bin_op u64_to_nat u64 (\<lambda>_ y. y \<noteq> u64 0) valid_u64 (div)"

definition lift_slot_bin_op :: "(u64 \<Rightarrow> u64 \<Rightarrow> u64 option) \<Rightarrow> Slot \<Rightarrow> Slot \<Rightarrow> Slot option" where
  "lift_slot_bin_op \<equiv> check_bin_op_then slot_to_u64 Slot any_args valid_slot"

definition lift_epoch_bin_op :: "(u64 \<Rightarrow> u64 \<Rightarrow> u64 option) \<Rightarrow> Epoch \<Rightarrow> Epoch \<Rightarrow> Epoch option" where
  "lift_epoch_bin_op \<equiv> check_bin_op_then epoch_to_u64 Epoch any_args valid_epoch"

definition slot_add :: "Slot \<Rightarrow> Slot \<Rightarrow> Slot option" where
  "slot_add \<equiv> lift_slot_bin_op u64_add"

definition slot_sub :: "Slot \<Rightarrow> Slot \<Rightarrow> Slot option" where
  "slot_sub \<equiv> lift_slot_bin_op u64_sub"

definition slot_mul :: "Slot \<Rightarrow> Slot \<Rightarrow> Slot option" where
  "slot_mul \<equiv> lift_slot_bin_op u64_mul"

definition slot_div :: "Slot \<Rightarrow> Slot \<Rightarrow> Slot option" where
  "slot_div \<equiv> lift_slot_bin_op u64_div"

definition epoch_add :: "Epoch \<Rightarrow> Epoch \<Rightarrow> Epoch option" where
  "epoch_add \<equiv> lift_epoch_bin_op u64_add"

definition epoch_sub :: "Epoch \<Rightarrow> Epoch \<Rightarrow> Epoch option" where
  "epoch_sub \<equiv> lift_epoch_bin_op u64_sub"

definition epoch_mul :: "Epoch \<Rightarrow> Epoch \<Rightarrow> Epoch option" where
  "epoch_mul \<equiv> lift_epoch_bin_op u64_mul"

definition epoch_div :: "Epoch \<Rightarrow> Epoch \<Rightarrow> Epoch option" where
  "epoch_div \<equiv> lift_epoch_bin_op u64_div"

adhoc_overloading
  unsigned_add u64_add slot_add epoch_add and
  unsigned_sub u64_sub slot_sub epoch_sub and
  unsigned_mul u64_mul slot_mul epoch_mul and
  unsigned_div u64_div slot_div epoch_div

lemmas u64_simps = valid_u64_def u64_add_def u64_sub_def u64_mul_def u64_div_def
lemmas slot_simps = valid_slot_def slot_add_def slot_sub_def slot_mul_def slot_div_def
                    lift_slot_bin_op_def
lemmas epoch_simps = valid_epoch_def epoch_add_def epoch_sub_def epoch_mul_def epoch_div_def
                     lift_epoch_bin_op_def
lemmas unsigned_simps = any_args_def check_bin_op_then_def check_bin_op_def

(* Sanity check lemmas *)
lemma u64_add_overflow_int_max: "u64 (2 ^ 64 - 1) .+ u64 1 = None"
  by (clarsimp simp: u64_simps unsigned_simps)

lemma u64_add_overflow_contradiction: "(u64 (2 ^ 64 - 1) .+ u64 1 = Some (u64 0)) \<Longrightarrow> False"
  by (clarsimp simp: u64_simps unsigned_simps)

lemma u64_sub_overflow_zero: "u64 0 .- u64 1 = None"
  by (clarsimp simp: u64_simps unsigned_simps)

lemma u64_div_zero: "n \\ u64 0 = None"
  by (clarsimp simp: u64_simps unsigned_simps)

lemma slot_div_zero: "n \\ Slot (u64 0) = None"
  by (clarsimp simp: slot_simps u64_simps unsigned_simps)

end