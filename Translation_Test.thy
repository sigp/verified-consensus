theory Translation_Test
 imports ProcessEpoch "Algebra/Traces"
begin

locale verified_con = constrained_atomic +
  constrains pgm  :: "BeaconState rel \<Rightarrow> 'a"
  constrains env  :: "BeaconState rel \<Rightarrow> 'a"
  constrains test :: "BeaconState set \<Rightarrow> 'a"

begin

abbreviation set_justified_checkpoint :: "Checkpoint \<Rightarrow> (unit, 'a) cont"
  where "set_justified_checkpoint n \<equiv> modifyState (\<lambda>state. state \<lparr> current_justified_checkpoint_f := n \<rparr>)"

end