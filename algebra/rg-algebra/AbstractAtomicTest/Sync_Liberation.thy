theory Sync_Liberation
imports
  "../AbstractAtomic/Abstract_Atomic_Sync"
  "../General/Liberation"
  "../AbstractAtomic/Atomic_Commands"
begin

locale sync_liberation = abstract_sync + liberation_stages +
  assumes sync_lib: "E\<^sup>C\<^sub>x (c \<otimes> (E\<^sup>C\<^sub>x d)) = (E\<^sup>C\<^sub>x c) \<otimes> (E\<^sup>C\<^sub>x d)" (* 65 *)
  assumes sync_first: "F\<^sup>C\<^sub>x (c \<otimes> (F\<^sup>C\<^sub>x d)) = (F\<^sup>C\<^sub>x c) \<otimes> (F\<^sup>C\<^sub>x d)" (* 66 *)

locale par_liberation  = par_atomic   + par  : sync_liberation par 
locale conj_liberation = conj_atomic  + conj : sync_liberation conj 
locale inf_liberation  = inf_atomic   + inf  : sync_liberation inf

locale command_liberation = atomic_commands + par_liberation + conj_liberation + inf_liberation

end