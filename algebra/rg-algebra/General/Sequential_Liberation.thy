section \<open>Liberation over sequential composition\<close>

theory Sequential_Liberation
  imports Sequential
          Liberation 
begin

locale seq_lib = seq + liberation_stages  +
   assumes seq_first: "E\<^sup>C\<^sub>x (c ; (F\<^sup>C\<^sub>x d)) = (E\<^sup>C\<^sub>x c) ; (E\<^sup>C\<^sub>x d)" (* 59 *)
   assumes seq_last: "E\<^sup>C\<^sub>x ((L\<^sup>C\<^sub>x c) ; d) = (E\<^sup>C\<^sub>x c) ; (E\<^sup>C\<^sub>x d)" (* 60 *) 
begin

(* liberation over sequential commands *)

text_raw \<open>\DefineSnippet{seqproofs}{%\<close>
lemma seq_right: "E\<^sup>C\<^sub>x (c ; (E\<^sup>C\<^sub>x d)) = (E\<^sup>C\<^sub>x c) ; (E\<^sup>C\<^sub>x d)" (* 61 *)
text_raw \<open>}%EndSnippet\<close>
  by (metis lib_lattice.lib_idem liberation_stages.axioms(1)
      liberation_stages_axioms localising_first seq_first)

lemma seq_left: "E\<^sup>C\<^sub>x ((E\<^sup>C\<^sub>x c) ; d) = (E\<^sup>C\<^sub>x c) ; (E\<^sup>C\<^sub>x d)" (* 62 *)
  by (metis lib_lattice.lib_idem liberation_stages.axioms(1) 
      liberation_stages_axioms localising_last seq_last)

end

end
