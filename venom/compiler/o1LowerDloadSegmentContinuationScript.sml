(* Runner composition for the supplied finite LowerDload expansions. *)
Theory o1LowerDloadSegmentContinuation
Ancestors
  o1LowerDloadSuppliedSegmentNext o1LowerDloadSuppliedSegmentExec
  o1LowerDloadSuppliedSegmentResources o1LowerDloadJointRelation o1PassContract
  venomExecSemantics venomState venomInst instIdxIndep lowerDloadDefs irSupply
  ptrDiscipline unitMemInv o1LowerDloadOccurrence gasEvents list rich_list finite_map

Theorem ld_generated_step_pc:
  MEM inst.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD] /\
  step_inst fuel C inst s = OK s1 ==>
  step_inst fuel C inst (s with vs_inst_idx := pc) =
    OK (s1 with vs_inst_idx := pc)
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_alloca_def, exec_pure2_def, exec_read1_def,
       eval_operands_def, eval_operand_def, lookup_var_def,
       bind_outputs_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[eval_op_inst_idx, update_var_def, write_memory_with_expansion_def,
      mload_def, read_memory_def]
QED

Theorem ld_exec_block_finite_continuation:
  !es f.
    (!j. j < LENGTH es ==>
      get_instruction bb (f j).vs_inst_idx = SOME (EL j es) /\
      ~is_terminator (EL j es).inst_opcode /\
      ?u. step_inst fuel C (EL j es) (f j) = OK u /\
          f (SUC j) = u with vs_inst_idx := SUC (f j).vs_inst_idx) ==>
    exec_block fuel C bb (f 0) = exec_block fuel C bb (f (LENGTH es))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!j. j < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  CONV_TAC (LHS_CONV (REWR_CONV exec_block_def)) >> simp[] >>
  first_x_assum (qspec_then `\j. f (SUC j)` mp_tac) >>
  simp[] >> disch_then irule >>
  gen_tac >> strip_tac >>
  first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]
QED

Theorem ld_generated_packet_continuation_joint:
  TAKE (LENGTH es) (DROP (f 0).vs_inst_idx bb.bb_instructions) = es /\
  (f 0).vs_inst_idx + LENGTH es <= LENGTH bb.bb_instructions /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) es /\
  (!j. j < LENGTH es ==> step_inst fuel C (EL j es) (f j) = OK (f (SUC j))) ==>
  exec_block fuel C bb (f 0) =
  exec_block fuel C bb
    (f (LENGTH es) with vs_inst_idx := (f 0).vs_inst_idx + LENGTH es) /\
  gas_events_block fuel C owner bb (f 0) =
  gas_events_block fuel C owner bb
    (f (LENGTH es) with vs_inst_idx := (f 0).vs_inst_idx + LENGTH es)
Proof
  strip_tac >>
  qabbrev_tac `g = \j. f j with vs_inst_idx := (f 0).vs_inst_idx + j` >>
  `!j. j < LENGTH es ==>
      get_instruction bb (g j).vs_inst_idx = SOME (EL j es) /\
      ~is_terminator (EL j es).inst_opcode /\
      (EL j es).inst_opcode <> GAS /\
      (EL j es).inst_opcode <> INVOKE /\
      ?u. step_inst fuel C (EL j es) (g j) = OK u /\
          g (SUC j) = u with vs_inst_idx := SUC (g j).vs_inst_idx` suffices_by
    (strip_tac >>
     qspecl_then [`es`,`g`] mp_tac ld_exec_block_finite_continuation >>
     qspecl_then [`es`,`g`] mp_tac gas_events_block_silent_finite_continuation >>
     simp[Abbr `g`] >> metis_tac[]) >>
  simp[Abbr `g`] >> gen_tac >> strip_tac >>
  `MEM (EL j es).inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]` by
    (gvs[EVERY_MEM] >> metis_tac[MEM_EL]) >>
  `step_inst fuel C (EL j es)
     (f j with vs_inst_idx := (f 0).vs_inst_idx + j) =
   OK (f (SUC j) with vs_inst_idx := (f 0).vs_inst_idx + j)` by
    (irule ld_generated_step_pc >> metis_tac[]) >>
  `~is_terminator (EL j es).inst_opcode` by
    gvs[MEM, is_terminator_def] >>
  `((EL j es).inst_opcode <> GAS) /\ ((EL j es).inst_opcode <> INVOKE)` by
    gvs[MEM] >>
  simp[] >> conj_tac
  >- (simp[get_instruction_def] >>
      `EL j (TAKE (LENGTH es) (DROP (f 0).vs_inst_idx bb.bb_instructions)) = EL j es`
        by simp[] >>
      gvs[EL_TAKE, EL_DROP]) >>
  qexists_tac `f (SUC j) with vs_inst_idx := (f 0).vs_inst_idx + j` >> gvs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM]
QED

Theorem ld_generated_packet_continuation:
  TAKE (LENGTH es) (DROP (f 0).vs_inst_idx bb.bb_instructions) = es /\
  (f 0).vs_inst_idx + LENGTH es <= LENGTH bb.bb_instructions /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) es /\
  (!j. j < LENGTH es ==> step_inst fuel C (EL j es) (f j) = OK (f (SUC j))) ==>
  exec_block fuel C bb (f 0) =
  exec_block fuel C bb
    (f (LENGTH es) with vs_inst_idx := (f 0).vs_inst_idx + LENGTH es)
Proof
  metis_tac[ld_generated_packet_continuation_joint]
QED

Theorem ld_two_step_packet_continuation_joint:
  LENGTH es = 2 /\
  TAKE 2 (DROP t.vs_inst_idx bb.bb_instructions) = es /\
  t.vs_inst_idx + 2 <= LENGTH bb.bb_instructions /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) es /\
  step_inst fuel C (EL 0 es) t = OK t2 /\
  step_inst fuel C (EL 1 es) t2 = OK t3 ==>
  exec_block fuel C bb t =
  exec_block fuel C bb (t3 with vs_inst_idx := t.vs_inst_idx + 2) /\
  gas_events_block fuel C owner bb t =
  gas_events_block fuel C owner bb (t3 with vs_inst_idx := t.vs_inst_idx + 2)
Proof
  strip_tac >>
  `es <> []` by (strip_tac >> gvs[]) >>
  qspecl_then [`es`, `\j. if j = 0 then t else if j = 1 then t2 else t3`]
    mp_tac (Q.GENL [`es`,`f`] ld_generated_packet_continuation_joint) >>
  simp[] >> disch_then irule >>
  gen_tac >> strip_tac >>
  `j = 0 \/ j = 1` by decide_tac >> gvs[]
QED

Theorem ld_two_step_packet_continuation:
  LENGTH es = 2 /\
  TAKE 2 (DROP t.vs_inst_idx bb.bb_instructions) = es /\
  t.vs_inst_idx + 2 <= LENGTH bb.bb_instructions /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) es /\
  step_inst fuel C (EL 0 es) t = OK t2 /\
  step_inst fuel C (EL 1 es) t2 = OK t3 ==>
  exec_block fuel C bb t =
  exec_block fuel C bb (t3 with vs_inst_idx := t.vs_inst_idx + 2)
Proof
  metis_tac[ld_two_step_packet_continuation_joint]
QED

Theorem ld_four_step_packet_continuation_joint:
  LENGTH es = 4 /\
  TAKE 4 (DROP t.vs_inst_idx bb.bb_instructions) = es /\
  t.vs_inst_idx + 4 <= LENGTH bb.bb_instructions /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) es /\
  step_inst fuel C (EL 0 es) t = OK t1 /\
  step_inst fuel C (EL 1 es) t1 = OK t2 /\
  step_inst fuel C (EL 2 es) t2 = OK t3 /\
  step_inst fuel C (EL 3 es) t3 = OK t4 ==>
  exec_block fuel C bb t =
  exec_block fuel C bb (t4 with vs_inst_idx := t.vs_inst_idx + 4) /\
  gas_events_block fuel C owner bb t =
  gas_events_block fuel C owner bb (t4 with vs_inst_idx := t.vs_inst_idx + 4)
Proof
  strip_tac >>
  `es <> []` by (strip_tac >> gvs[]) >>
  qspecl_then [`es`, `\j. if j = 0 then t else if j = 1 then t1 else
                         if j = 2 then t2 else if j = 3 then t3 else t4`]
    mp_tac (Q.GENL [`es`,`f`] ld_generated_packet_continuation_joint) >>
  simp[] >> disch_then irule >>
  gen_tac >> strip_tac >>
  `j = 0 \/ j = 1 \/ j = 2 \/ j = 3` by decide_tac >> gvs[]
QED

Theorem ld_four_step_packet_continuation:
  LENGTH es = 4 /\
  TAKE 4 (DROP t.vs_inst_idx bb.bb_instructions) = es /\
  t.vs_inst_idx + 4 <= LENGTH bb.bb_instructions /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) es /\
  step_inst fuel C (EL 0 es) t = OK t1 /\
  step_inst fuel C (EL 1 es) t1 = OK t2 /\
  step_inst fuel C (EL 2 es) t2 = OK t3 /\
  step_inst fuel C (EL 3 es) t3 = OK t4 ==>
  exec_block fuel C bb t =
  exec_block fuel C bb (t4 with vs_inst_idx := t.vs_inst_idx + 4)
Proof
  metis_tac[ld_four_step_packet_continuation_joint]
QED

Theorem ld_successful_supply_packet:
  MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  step_inst fuel C inst s = OK s1 /\
  lower_dload_inst_supply v inst = (es,v') ==>
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) es /\
  LENGTH es = (if inst.inst_opcode = DLOAD then 4 else 2)
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def]
QED

Theorem ld_joint_generated_slice:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ active_inst fn inst s /\
  MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  step_inst fuel C inst s = OK s1 /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  LENGTH es = (if inst.inst_opcode = DLOAD then 4 else 2) /\
  TAKE (LENGTH es) (DROP t.vs_inst_idx bb.bb_instructions) = es ==>
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) es
Proof
  strip_tac >>
  `(?ptr out. inst.inst_opcode = DLOAD /\ inst.inst_operands = [ptr] /\
       inst.inst_outputs = [out]) \/
   (?dst ptr sz. inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;ptr;sz])` by
    (gvs[MEM] >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  (`?v es' v'. lower_dload_inst_supply v inst = (es',v') /\
      TAKE (LENGTH es') (DROP t.vs_inst_idx bb.bb_instructions) = es'` by
     (drule ld_joint_segment_control >>
      disch_then (drule_at (Pat `o1_ctx_shape _`)) >>
      disch_then (drule_at (Pat `active_inst _ _ _`)) >>
      disch_then (qspecl_then [`sz`,`ptr`,`out`,`dst`] mp_tac) >>
      simp[] >> strip_tac >> gvs[] >> metis_tac[]) >>
   drule_all ld_successful_supply_packet >> strip_tac >> gvs[])
QED

Theorem ld_joint_dloadbytes_continue:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  mem_inv dload_offset_ok C vs /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = DLOADBYTES /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 t' fn' bb'.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = exec_block fuel C' bb' t' /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t'
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  strip_tac >> drule_all ld_joint_dloadbytes_next >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) es` by
    (`MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
     rev_drule ld_joint_generated_slice >>
     disch_then (drule_at (Pat `lookup_block _ _ = SOME _`)) >>
     simp[] >> disch_then irule >> metis_tac[]) >>
  `exec_block fuel C' bb' t =
   exec_block fuel C' bb' (t3 with vs_inst_idx := t.vs_inst_idx+2)` by
    (irule ld_two_step_packet_continuation >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ld_joint_dload_continue:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  mem_inv dload_offset_ok C vs /\ mem_inv dload_headroom_ok C vs /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = DLOAD /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 t' fn' bb' X1.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = exec_block fuel C' bb' t' /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t'
      n a U B HP (occurrence_step a HP H inst s1) sites X1 ts
Proof
  strip_tac >> drule_all ld_joint_dload_next >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) es` by
    (`MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
     rev_drule ld_joint_generated_slice >>
     disch_then (drule_at (Pat `lookup_block _ _ = SOME _`)) >>
     simp[] >> disch_then irule >> metis_tac[]) >>
  `exec_block fuel C' bb' t =
   exec_block fuel C' bb' (t4 with vs_inst_idx := t.vs_inst_idx+4)` by
    (irule ld_four_step_packet_continuation >> metis_tac[]) >>
  metis_tac[]
QED
