Theory o1CodeEndSsaProtectedUses
Ancestors
  o1CodeEndSsaProtectedCleanup o1ContractMakeSsa o1PassContract
  venomPassSchedule unitTransformDefs o1MakeSsaCfg
  makeSsaCurrentLockstep makeSsaCurrentWfSsa codegenSymRel
  venomInst venomWf list

Theorem make_ssa_stage_protected_uses:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  EVERY (\f. !x. code_end_var f x ==> ?d op. MEM d (fn_insts f) /\
    d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
    d.inst_outputs = [x] /\
    (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
    (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
      MEM (Var x) j.inst_operands ==>
      j.inst_opcode = CODECOPY /\
      (?dst sz. j.inst_operands = [dst; Var x; sz] /\
        dst <> Var x /\ sz <> Var x) /\
      ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) C.ctx_functions ==>
  EVERY (\g. !x i. code_end_var g x /\ MEM i (fn_insts g) /\
    MEM (Var x) i.inst_operands ==>
    i.inst_opcode = ASSIGN \/ i.inst_opcode = CODECOPY) C'.ctx_functions
Proof
  strip_tac >> drule make_ssa_stage_functions >> strip_tac >>
  simp[EVERY_EL] >> gen_tac >> strip_tac >>
  `n < LENGTH C.ctx_functions` by metis_tac[LIST_REL_LENGTH] >>
  drule_all make_ssa_stage_el >> strip_tac >>
  qabbrev_tac `f = EL n C.ctx_functions` >>
  qabbrev_tac `g = EL n C'.ctx_functions` >>
  `MEM f C.ctx_functions` by simp[Abbr `f`, EL_MEM] >>
  rename1 `make_ssa_current_fn supply f = (g,supply')` >>
  `?eb. entry_block f = SOME eb` by
    (Cases_on `f.fn_blocks` >>
     fs[wf_function_def, fn_has_entry_def, entry_block_def]) >>
  drule_all make_ssa_lockstep_phi_context >> strip_tac >>
  `fn_entry_label f = SOME eb.bb_label` by simp[fn_entry_label_def] >>
  `!x. code_end_var f x ==> ?d op. MEM d (fn_insts f) /\
    d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
    d.inst_outputs = [x] /\
    (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
    (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
      MEM (Var x) j.inst_operands ==>
      j.inst_opcode = CODECOPY /\
      (?dst sz. j.inst_operands = [dst; Var x; sz] /\
        dst <> Var x /\ sz <> Var x) /\
      ?a b. bb.bb_instructions = a ++ [d;j] ++ b)` by
    fs[EVERY_MEM] >>
  drule code_end_ssa_context_protected_uses >>
  disch_then (qspecl_then [`g`, `eb.bb_label`] mp_tac) >>
  simp[] >> strip_tac >> rpt strip_tac >> disj2_tac >>
  first_x_assum irule >> simp[] >> qexists `x` >> simp[]
QED
