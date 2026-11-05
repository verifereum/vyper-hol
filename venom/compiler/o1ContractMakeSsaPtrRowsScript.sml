(*
 * The per-state rows of the pointer discipline (access_ok, taint_ok)
 * carry from an input state to the output state a frame lockstep pairs
 * it with, and MakeSSA adds no DALLOCA.
 *)
Theory o1ContractMakeSsaPtrRows
Ancestors
  o1FrameLockstep ptrDiscipline contextCodegenRel codegenRel
  makeSsaCurrentDefs makeSsaCurrentOrigin o1PassContract venomWf

(* Paired states (p): same opcode, operands renamed by sg, equal values,
   provenance and taint through ghost_rel, equal memory ranges
   (write_ranges_pair, read_ranges_pair, inst_pair_ops_ghost); the
   revert exemptions carry by the two implications.  Unpaired states
   (~p) run an ASSIGN or a NOP: no memory range, no comparison, and
   taint_ok allows ASSIGN any operand. *)
Theorem lockstep_ptr_rows:
  lockstep_sim L C C' fn fn' pos R /\ R p (inst,s) sg (inst',s') /\
  ghost_rel sg G tn G' tn' /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
  (p /\ in_revert_forward fn s ==> in_revert_forward fn' s') /\
  (p /\ about_to_revert fn inst s ==> about_to_revert fn' inst' s') ==>
  access_ok lo G' fn' inst' s' /\ taint_ok fn' tn' inst' s'
Proof
  cheat
QED

(* make_ssa_current_fn_origin: a DALLOCA of the output is a renamed
   instruction of the input, with the same opcode. *)
Theorem make_ssa_current_fn_dalloca:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts fn') ==>
  EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts fn)
Proof
  cheat
QED
