import Gem5Lean
open Gem5
#print axioms Gem5.step_sound
#print axioms Gem5.step_wf
#print axioms Gem5.run_wf
#print axioms Gem5.Port.no_lost_retry
#print axioms Gem5.Port.buggy_stuck_forever
#print axioms Gem5.SoC.instr_refines
#print axioms Gem5.SoC.soc_refines_isa
#print axioms Gem5.NoC.cdg_acyclic
#print axioms Gem5.NoC.progress
#print axioms Gem5.NoC.drain
#print axioms Gem5.NoC.moves_bounded
#print axioms Gem5.NoC.stepNet_none
#print axioms Gem5.NoC.adaptive_deadlock
