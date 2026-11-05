Theory scratchPrefixSim
Ancestors
  mixedPrefixSim stackPlanTypes list rich_list words spillSim deepDupFrameSim
  asmSem planExec stackOpSim codegenRel asmIR doSwapSim
Libs dep_rewrite

Theorem prefix_spill_wf_address_bounds:
  !ops ps. prefix_spill_wf f lo ops ps ==>
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops
Proof
  Induct_on `ops` >> simp[prefix_spill_wf_def] >>
  rpt strip_tac
  >- (Cases_on `h` >> gvs[spill_op_wf_def]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem prefix_spill_wf_front_emit_address_bounds:
  prefix_spill_wf f lo (FRONT (pre ++ [SOEmit name] ++ post)) ps ==>
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) pre
Proof
  strip_tac >> drule prefix_spill_wf_address_bounds >>
  Cases_on `post` >> simp[FRONT_APPEND]
QED

Theorem scratch_expand_read32:
  !offs mem at.
  word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP at (FOLDL (\m off. asm_expand_memory (off + 32) m) mem offs))) =
  word_of_bytes T (0w:bytes32) (TAKE 32 (DROP at mem))
Proof
  Induct_on `offs` >> simp[word_of_bytes_take_drop_expand]
QED

