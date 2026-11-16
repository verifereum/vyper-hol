Theory o1CodeEndFmpLifetime
Ancestors
  o1LabelFlowMiddleFmp o1PassContract venomPassDispatcher venomInst list

Theorem fmp_stage_protected_lifetime:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (\C' f observed. view C' f observed /\
      EVERY fmp_sig_no_param observed.cu_context.ctx_functions) C C' /\
  EVERY (o1_fn_row 3) C.ctx_functions /\
  EVERY no_raw_fmp_ops C.ctx_functions /\
  EVERY (\f. !x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
        MEM (Var x) j.inst_operands ==>
        j.inst_opcode = CODECOPY /\
        (?dst sz. j.inst_operands = [dst; Var x; sz] /\
          dst <> Var x /\ sz <> Var x) /\
        ?pre post. bb.bb_instructions = pre ++ d::j::post)) C.ctx_functions ==>
  EVERY (\f. !x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
        MEM (Var x) j.inst_operands ==>
        j.inst_opcode = CODECOPY /\
        (?dst sz. j.inst_operands = [dst; Var x; sz] /\
          dst <> Var x /\ sz <> Var x) /\
        ?pre post. bb.bb_instructions = pre ++ d::j::post)) C'.ctx_functions
Proof
  simp[ctx_pass_stage_def, EVERY_MEM] >> rpt strip_tac >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >> gvs[] >>
  drule fmp_row_code_end_lifetime >>
  simp[EVERY_MEM] >> metis_tac[]
QED
