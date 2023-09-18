section \<open>Programming constructs\<close>
  
theory Programming_Constructs
  imports
  "AtomicSpecification"
  "While_Loop"
  "Assignments"
  "IntroPar_Big"
  "Local"
  "Rely_Guarantee_Liberation"
begin

locale programming_constructs = locals + assignments + while_loop +
                                intro_par_big + rg_lib


datatype 'id Val = Integer "nat" | Boolean "bool" | Set "'id Val fset" | 
               Struct "'id \<rightharpoonup> 'id Val" | Array "nat \<rightharpoonup> 'id Val"

(* Theory of concurrent programs including programming constructs with a fixed
   value universe defined by Val. *)
locale programming_constructs_simple = programming_constructs  +
  constrains test :: "'state set \<Rightarrow> 'a"  
  constrains lib :: "'varname \<Rightarrow> 'a \<Rightarrow> 'a"
  constrains lib_bool :: "'varname \<Rightarrow> ('state \<times> 'state) set \<Rightarrow> ('state \<times> 'state) set"
  constrains pgm :: "('state \<times> 'state) set \<Rightarrow> 'a"  
  constrains env :: "('state \<times> 'state) set \<Rightarrow> 'a"  
  constrains set_var :: "'varname \<Rightarrow> 'id Val \<Rightarrow> 'state \<Rightarrow> 'state"
  constrains get_var :: "'varname \<Rightarrow> 'state \<Rightarrow> 'id Val"
begin

end

end
