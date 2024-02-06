theory SP
imports
 Main
"~~/src/HOL/Eisbach/Eisbach"
begin

text \<open>Rule collections for strongest postconditions\<close>
named_theorems sp
named_theorems sp_pre

text \<open> Strongest postcondition method setup \<close>
method sp declares sp = ((((rule sp)+), (rule sp_pre, rule sp, assumption?)?)  |
                        (rule sp_pre, rule sp, assumption?))

end