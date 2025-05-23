(* Definition of the `verified_con` locale which is used in the rest of the project *)
theory VerifiedConsensus
  imports "Verified_Consensus.Idle" 
           Cont_Monad_Algebra 
           Types Config 
          "Word_Lib.Word_64" 
          "Word_Lib.More_Arithmetic"  
           Invariants 
           Lens
begin

datatype ('a, 'b) Lex_Prod = Prod (major :'a) (minor : 'b) 

instantiation Lex_Prod :: (preorder, preorder) preorder
begin

  fun less_eq_Lex_Prod :: "('a, 'b) Lex_Prod \<Rightarrow> ('a, 'b) Lex_Prod \<Rightarrow> bool"
    where "less_eq_Lex_Prod (Prod a1 b1) (Prod a2 b2) = ((a1 \<le> a2) \<and> ((a2 \<le> a1) \<longrightarrow> b1 \<le> b2))"

  definition less_Lex_Prod :: "('a, 'b) Lex_Prod \<Rightarrow> ('a, 'b) Lex_Prod \<Rightarrow> bool"
    where "less_Lex_Prod a b \<equiv> less_eq a b \<and> \<not>(less_eq b a)"

instance 
  apply (standard)
    apply (clarsimp simp: less_Lex_Prod_def)
   apply (case_tac x;  clarsimp)
  apply (case_tac x; case_tac y; case_tac z;  clarsimp)
  by (metis order_trans)
  
end

instantiation Lex_Prod :: (order, order) order
begin
instance
  apply (standard)
  by (case_tac x; case_tac y; clarsimp)
end

declare [[show_sorts=false]]

type_synonym ('var, 'val) heap = "'var \<Rightarrow> 'val option"

datatype ('var) heap_value = list "'var heap_value list" | u8 u8 | u64 u64 | ptr "'var"

primrec is_list where
  "is_list (list _) = True"|
  "is_list (u8 _) = False" |
  "is_list (u64 _) = False"|
  "is_list (ptr _) = False"

primrec list_of where
  "list_of (list xs) = Some xs"|
  "list_of (u8 _)    = None" |
  "list_of (u64 _)   = None" |
  "list_of (ptr _)   = None"


primrec is_u8 where
  "is_u8 (list _) = False"|
  "is_u8 (u8 _) = True" |
  "is_u8 (u64 _) = False"


primrec u8_of where
  "u8_of (list _) = None"|
  "u8_of (u8 x)   = Some x" |
  "u8_of (u64 _)  = None"


primrec is_u64 where
  "is_u64 (list _) = False"|
  "is_u64 (u8 _)   = False"|
  "is_u64 (u64 _)  = True"

primrec is_ptr where
  "is_ptr (list _) = False"|
  "is_ptr (u8 _)   = False"|
  "is_ptr (u64 _)  = False" |
  "is_ptr (ptr _) = True"



primrec u64_of where
  "u64_of (list _) = None"|
  "u64_of (u8 _)   = None" |
  "u64_of (u64 x)  = Some x"


primrec ptr_of where
  "ptr_of (list _) = None"|
  "ptr_of (u8 _)   = None" |
  "ptr_of (u64 _)  = None" |
  "ptr_of (ptr x)  = Some x"


consts
  read :: "'a \<Rightarrow> ('b, 'c) cont"

consts
  index_s :: "'a \<Rightarrow> 'b \<Rightarrow> ('c, 'd) cont" (infixl "#!" 54)

consts 
  write_to :: "'a \<Rightarrow> 'b \<Rightarrow> (unit, 'c) cont" 

consts
  modify_s :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> (unit, 'd) cont"


abbreviation modify :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> (unit, 'c) cont" where
   "modify a f \<equiv> (bindCont (read a) (\<lambda>x. write_to a (f x)))"

abbreviation modifyM :: "'a \<Rightarrow> ('b \<Rightarrow> ('b, 'c) cont) \<Rightarrow> (unit, 'c) cont" where
   "modifyM a f \<equiv> (bindCont (read a) (\<lambda>x. bindCont (f x) (write_to a)))"

adhoc_overloading modify_s == modify modifyM

abbreviation 
  "when b p \<equiv> (if b then p else return ())" 


definition genesis_time  where
 "genesis_time \<equiv> lens_comp (Lens genesis_time_f (\<lambda>(a :: BeaconState) b. a\<lparr>genesis_time_f := b\<rparr> ) (\<lambda>_. True)) first"

definition "genesis_validators_root = Lens genesis_validators_root_f  (\<lambda>(a :: BeaconState) b. a\<lparr>genesis_validators_root_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "beacon_slots = Lens BeaconState.slot_f  (\<lambda>(a :: BeaconState) b. a\<lparr> BeaconState.slot_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "fork         = Lens fork_f  (\<lambda>(a :: BeaconState) b. a\<lparr>fork_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "latest_block_header = Lens latest_block_header_f  (\<lambda>(a :: BeaconState) b. a\<lparr>latest_block_header_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "block_roots = Lens block_roots_f  (\<lambda>(a :: BeaconState) b. a\<lparr>block_roots_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "state_roots = Lens state_roots_f  (\<lambda>(a :: BeaconState) b. a\<lparr>state_roots_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "historical_roots = Lens historical_roots_f  (\<lambda>(a :: BeaconState) b. a\<lparr>historical_roots_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "historical_summaries = Lens historical_summaries_f (\<lambda>(a :: BeaconState) b. a\<lparr>historical_summaries_f := b\<rparr>) (\<lambda>_. True) |> first"

definition "eth1_data = Lens eth1_data_f  (\<lambda>(a :: BeaconState) b. a\<lparr>eth1_data_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "eth1_data_votes = Lens eth1_data_votes_f  (\<lambda>(a :: BeaconState) b. a\<lparr>eth1_data_votes_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "eth1_deposit_index = Lens eth1_deposit_index_f  (\<lambda>(a :: BeaconState) b. a\<lparr>eth1_deposit_index_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "validators = Lens validators_f  (\<lambda>(a :: BeaconState) b. a\<lparr>validators_f := b\<rparr> ) (case_option True (\<lambda>xs. (let ys = Invariants.var_list_inner xs in sum_list (map (unat o Validator.effective_balance_f) ys) < 2^(64) \<and> distinct ys \<and> length ys < 2^64 ))) |> first"

definition "balances = Lens balances_f  (\<lambda>(a :: BeaconState) b. a\<lparr>balances_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "randao_mixes = Lens randao_mixes_f  (\<lambda>(a :: BeaconState) b. a\<lparr>randao_mixes_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "slashings = Lens slashings_f  (\<lambda>(a :: BeaconState) b. a\<lparr>slashings_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "previous_epoch_participation = Lens previous_epoch_participation_f  (\<lambda>(a :: BeaconState) b. a\<lparr>previous_epoch_participation_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "current_epoch_participation = Lens current_epoch_participation_f  (\<lambda>(a :: BeaconState) b. a\<lparr>current_epoch_participation_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "justification_bits = Lens justification_bits_f  (\<lambda>(a :: BeaconState) b. a\<lparr>justification_bits_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "previous_justified_checkpoint = Lens previous_justified_checkpoint_f  (\<lambda>(a :: BeaconState) b. a\<lparr>previous_justified_checkpoint_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "current_justified_checkpoint = Lens current_justified_checkpoint_f  (\<lambda>(a :: BeaconState) b. a\<lparr>current_justified_checkpoint_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "finalized_checkpoint = Lens finalized_checkpoint_f  (\<lambda>(a :: BeaconState) b. a\<lparr>finalized_checkpoint_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "inactivity_scores = Lens inactivity_scores_f  (\<lambda>(a :: BeaconState) b. a\<lparr>inactivity_scores_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "current_sync_committee = Lens current_sync_committee_f  (\<lambda>(a :: BeaconState) b. a\<lparr>current_sync_committee_f := b\<rparr> ) (\<lambda>_. True) |> first"

definition "next_sync_committee = Lens next_sync_committee_f  (\<lambda>(a :: BeaconState) b. a\<lparr>next_sync_committee_f := b\<rparr> ) (\<lambda>_. True) |> first"

syntax
  "_mod_expr" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c " ("_ ::= _" [1000, 13] 13)
  "_mod_exprM" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c " ("_ := _" [1000, 13] 13)



translations
 "_mod_expr a b"  \<rightharpoonup> "CONST modify a (\<lambda>a. b)"
 "_mod_exprM a b" \<rightharpoonup> "CONST modifyM a (\<lambda>a. b)"

definition foo where 
   "foo x y \<equiv>  (x :=  return (0 :: nat))"


locale verified_con = idle_command +
  constrains pgm  :: "(BeaconState \<times> ('var, 'var heap_value) heap) rel \<Rightarrow> 'a"
  constrains env  :: "(BeaconState \<times> ('var, 'var heap_value) heap) rel \<Rightarrow> 'a"
  constrains test :: "(BeaconState \<times> ('var, 'var heap_value) heap) set \<Rightarrow> 'a"
  fixes config :: "Config"

begin

text \<open>locale verified_con = idle_command + test_liberation  + 
                      liberation +  
                    inf: sync_liberation inf + 
                    conj: sync_liberation conj + 
                    par: sync_liberation par +
  constrains pgm  :: "(BeaconState \<times> ('var, 'var heap_value) heap) rel \<Rightarrow> 'a"
  constrains env  :: "(BeaconState \<times> ('var, 'var heap_value) heap) rel \<Rightarrow> 'a"
  constrains test :: "(BeaconState \<times> ('var, 'var heap_value) heap) set \<Rightarrow> 'a"
  constrains lib  :: "'var \<Rightarrow> 'a \<Rightarrow> 'a"
  constrains lib_bool  :: "'var \<Rightarrow> 
                           (BeaconState \<times> ('var, 'var heap_value) heap) rel \<Rightarrow>
                           (BeaconState \<times> ('var, 'var heap_value) heap) rel"
  constrains lib_bool_sets  :: "'var \<Rightarrow> 
                           (BeaconState \<times> ('var, 'var heap_value) heap) set \<Rightarrow>
                           (BeaconState \<times> ('var, 'var heap_value) heap) set"

  fixes config :: "Config"
\<close>


lemma nil_not_top[simp]: "(nil = \<top>) = False"
  by (metis (full_types) UNIV_I abstract_hom_commands.hom_iso_eq empty_iff seq_abort seq_nil_left
      test.abstract_hom_commands_axioms)

definition read_beacon :: "((BeaconState \<times> ('var \<Rightarrow> 'var heap_value option), 'b option) lens)  \<Rightarrow> ('b, 'a) cont" where
  "read_beacon l \<equiv> do { state \<leftarrow> getState; if (get l  state) = None then fail else return (the (get l state)) }"


definition write_beacon :: "((BeaconState \<times> ('var \<Rightarrow> 'var heap_value option), 'b option) lens) \<Rightarrow> 'b \<Rightarrow> (unit, 'a) cont" where
  "write_beacon l b \<equiv> do { state \<leftarrow> getState; 
                          if (get l state) = None then fail else
                          setState (set l state (Some b))  }"

definition "lift_option v = (if v = None then fail else return (the v))"

definition read_list :: "'var \<Rightarrow> ('var heap_value list, 'a) cont" where
  "read_list p \<equiv> do {state <- getState; 
                     lift_option (do {v <- (snd state p); list_of v})}"

definition read_u8 :: "'var \<Rightarrow> (8 word, 'a) cont" where
  "read_u8 p \<equiv> do {state <- getState; 
                   lift_option (do {v <- (snd state p); u8_of v})}"


definition read_u64 :: "'var \<Rightarrow> (64 word, 'a) cont" where
  "read_u64 p \<equiv> do {state <- getState; 
                     x <- lift_option (do {v <- (snd state p); u64_of v});
                     return x}"

definition index_u64_from_list :: "'var heap_value list \<Rightarrow> u64 =>  (u64, 'a) cont" where
  "index_u64_from_list  ls index \<equiv> (if unat index \<ge> length ls 
            then fail else lift_option (u64_of (ls ! unat index)))  "


definition index_ptr_from_list :: "'var heap_value list \<Rightarrow> u64 =>  ('var, 'a) cont" where
  "index_ptr_from_list  ls index \<equiv> (if unat index \<ge> length ls 
            then fail else lift_option (ptr_of (ls ! unat index)))  "

definition index_u8_from_list :: "'var heap_value list \<Rightarrow> u8 \<Rightarrow>  (u8, 'a) cont" where
  "index_u8_from_list ls index \<equiv> (if unat index \<ge> length ls 
            then fail else lift_option (u8_of (ls ! unat index)))"

definition write_list :: "'var \<Rightarrow> 'var heap_value list \<Rightarrow> (unit, 'a) cont" where
  "write_list p x \<equiv> do {state <- getState;
                          _ <- lift_option (do {v <- (snd state p); if (is_list v) then Some True else None});
                         setState ((fst state), fun_upd (snd state) p (Some (list x)))}"


definition write_u8 :: "'var \<Rightarrow> 8 word \<Rightarrow> (unit, 'a) cont" where
  "write_u8 p x \<equiv> do {state <- getState;
                         _ <- lift_option (do {v <- (snd state p); if (is_u8 v) then Some True else None});
                        setState ((fst state), (snd state)(p := Some (u8 x)))}"


definition write_u64 :: "'var \<Rightarrow> 64 word \<Rightarrow> (unit, 'a) cont" where
  "write_u64 p x \<equiv> do {state <- getState;
                         _ <- lift_option (do {v <- (snd state p); if (is_u64 v) then Some True else None});
                         setState ((fst state), (snd state)(p := Some (u64 x)))}"


definition "v_list_lens i \<equiv> 
            (Lens (\<lambda>l. if unat (i :: 64 word)  < length (var_list_inner l) \<and> length (var_list_inner l) < 2 ^ 64  then Some (var_list_inner l ! unat i) else None) 
            (\<lambda>l e. case e of (Some e) \<Rightarrow> VariableList (list_update (var_list_inner l) (unat i) e) | _ \<Rightarrow> l) (\<lambda>_. True))"


definition "offset n \<equiv> 
            (Lens (\<lambda>l. VariableList (drop n (var_list_inner l))) 
            (\<lambda>l e. let xs = var_list_inner l in 
                  VariableList (take n xs @ take (length xs - n) (var_list_inner e))) (\<lambda>_. True))"



definition "var_list_index_lens ls i \<equiv> do {
  l <- read_beacon (v_list_lens i |oo> ls);
  return (v_list_lens i |oo> ls) }"

notation "var_list_index_lens" (infixr "!?"  88)

abbreviation (input) "mut x \<equiv> x" 





adhoc_overloading
  read == read_beacon read_list read_u64 read_u8

adhoc_overloading
 index_s == index_u8_from_list index_u64_from_list index_ptr_from_list

adhoc_overloading
  write_to == write_beacon write_list write_u8 write_u64

end

end