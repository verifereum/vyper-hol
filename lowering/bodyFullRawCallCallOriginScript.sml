(* A specified CALL step carries its origin and pointer checks together. *)
Theory bodyFullRawCallCallOrigin
Ancestors
  oracleCallStepPtr fragGasSeqPtr bodyPtrDefs venomState ptrDiscipline
  ptrSafeRun contextCodegenRel memLocDefs venomInst memSafeRun
  venomExecSemantics venomInstProps fragGasOriginPtr

Theorem raw_call_step_origin_full:
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [gas_op;to_op;val_op;dp;dl;op;rz]) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [gas_op;to_op;dp;dl;op;rz])) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand rz s = SOME rn /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p s (w2n az)) /\
  (rn <> 0w ==> ?p. op = Var p /\ ptr_covers G tn p s (w2n rn)) /\
  EVERY (\p. op_taint tn p = {}) inst.inst_operands /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
  allocas_from lo s /\ stor_taint_ok_at D tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  inst_mem_below_frontier inst s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK u ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G inst u, step_taint inst s u tn)
Proof
  strip_tac >>
  `access_ok 0 G func inst s` by
    (irule call_access_ok_ptr >>
     gvs[ptr_covers_def] >> metis_tac[eval_operand_def, arithmeticTheory.ADD_COMM]) >>
  `access_ok lo G func inst s` by
    (qpat_x_assum `access_ok 0 _ _ _ _` mp_tac >>
     simp[access_ok_def] >> metis_tac[arithmeticTheory.LESS_ADD_NONZERO]) >>
  `taint_ok func tn inst s` by
    (irule call_taint_ok_ptr >>
     simp[source_memory_read_ranges_def, mem_read_ops_def,
          memory_range_of_operands_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (simp[ptr_inst_ok_def] >>
     gvs[stor_taint_ok_at_def] >> metis_tac[call_step_not_Halt]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> GAS /\ inst_dload_in_section inst s` by
    simp[is_terminator_def, inst_dload_in_section_def] >>
  drule_all straight_line_origin_ptr_edge >> simp[] >> strip_tac >>
  `step_inst 0 ctx inst s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[gas_origin_ptr_path_rules]
QED
