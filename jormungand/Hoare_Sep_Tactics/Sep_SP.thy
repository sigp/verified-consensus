theory Sep_SP
 imports
 Sep_Forward
 SP
begin
(*
declare hoare_strengthen_post[sp_pre]
declare hoare_seq_ext[rotated, sp] 
declare put_sp [sp] return_sp [sp] get_sp [sp] assert_sp [sp] *)

named_theorems sep_sp

ML \<open>
fun attrib thm ctxt thm' =
    ( [thm'] MRS thm)
    |> Goal.norm_result ctxt
  handle THM _ => thm'

fun try_then xs = Thm.rule_attribute [] (attrib xs o Context.proof_of )

\<close>

attribute_setup TRY_THEN = \<open> Attrib.thm >>  try_then \<close>

method sep_sp uses rl spec declares sep_sp  = (sp sp: spec[TRY_THEN sep_sp] rl )

lemma "(\<not>(P \<and>* (\<lambda>s. \<not> Q s)) s) = ((P \<leadsto>* Q) s)"
              "(\<not>((\<lambda>s. \<not> Q s) \<and>* P) s) = ((P \<leadsto>* Q) s)"                                                            
 apply (clarsimp simp: sep_coimpl_def pred_neg_def)
 by (clarsimp simp: sep_coimpl_def pred_neg_def sep_conj_commute)


lemma sep_conj_coimpl_precise: "(P \<and>* R) s \<Longrightarrow> precise P \<Longrightarrow> (P \<leadsto>* R) s" 
  by (simp add: precise_conj_coimpl)

(*
lemma gets_sp[sp]: "\<lbrace>\<lambda>s. P (f s) s\<rbrace> gets f \<lbrace>\<lambda>rv s. P rv s \<and> rv = f s\<rbrace>"
  apply (clarsimp simp: gets_def, sp)
  apply (clarsimp, assumption)
  apply (sp)
  apply (fastforce)
done 

lemma gets_the_sp: "\<lbrace>\<lambda>s. Q s\<rbrace> gets_the f \<lbrace>\<lambda>rv s . Q s \<and> f s \<noteq> None \<and> rv = the (f s) \<rbrace>"
  apply (clarsimp simp: gets_the_def, sp)
  apply (case_tac x;  clarsimp simp: assert_opt_def)
  apply (sp, clarsimp)
  apply (intro conjI)
  apply (rule_tac x=a in exI)
  apply (clarsimp)
  by (metis option.sel)
*)
  

end