(* A specified raw call step carries its origin and pointer checks together. *)
Theory bodyFullRawCallCallOrigin
Ancestors
  oracleCallStepPtr fragGasSeqPtr bodyPtrDefs venomState ptrDiscipline
  ptrSafeRun contextCodegenRel codegenRel memLocDefs venomInst memSafeRun
  venomExecSemantics venomInstProps fragGasOriginPtr fragGasOrigin gasEvents

(* CALL and CALLDATACOPY use the same memory-safe edge for DALLOCA ranges. *)
Theorem non_gas_mem_safe_origin_ptr_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
  mem_safe_step 0 ctx i s /\
  ptr_inst_ok D lo 0 ctx func G tn i s /\
  step_inst_base i s = OK u ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u, step_taint i s u tn)
Proof
  strip_tac >>
  `step_inst 0 ctx i s = OK u` by simp[step_inst_non_invoke] >>
  `u.vs_halted = s.vs_halted` by
    (qpat_assum `step_inst 0 ctx i s = OK u` (fn run =>
     qpat_assum `~is_terminator i.inst_opcode` (fn ordinary =>
       ACCEPT_TAC (MATCH_MP step_preserves_halted (CONJ run ordinary))))) >>
  PURE_REWRITE_TAC[gas_origin_ptr_edge_def] >> conj_tac
  >- (rewrite_tac[gas_origin_edge_def] >> conj_tac >- simp[] >>
      qexistsl_tac [`0`, `bb`, `i`, `OK u`] >> simp[gas_events_step_def]) >>
  drule_all straight_line_ptr_edge >> simp[]
QED

Theorem raw_call_step_mem_safe_origin_full:
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
  mem_safe_step 0 ctx inst s /\
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
     gvs[ptr_covers_def] >> rpt strip_tac >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `access_ok lo G func inst s` by
    (qpat_x_assum `access_ok 0 _ _ _ _` mp_tac >>
     simp[access_ok_def] >> metis_tac[arithmeticTheory.LESS_ADD_NONZERO]) >>
  `taint_ok func tn inst s` by
    (irule call_taint_ok_ptr >>
     Cases_on `eval_operand gas_op s` >>
     Cases_on `eval_operand to_op s` >>
     Cases_on `eval_operand val_op s` >>
     simp[source_memory_read_ranges_def, mem_read_ops_def,
          memory_range_of_operands_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (simp[ptr_inst_ok_def] >>
     gvs[stor_taint_ok_at_def] >> metis_tac[call_step_not_Halt]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> GAS /\ inst_dload_in_section inst s` by
    simp[is_terminator_def, inst_dload_in_section_def] >>
  drule_all non_gas_mem_safe_origin_ptr_edge >> simp[] >> strip_tac >>
  `step_inst 0 ctx inst s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (u with vs_inst_idx := SUC s.vs_inst_idx,
     step_prov PG G inst u, step_taint inst s u tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G inst u, step_taint inst s u tn)` by
    (irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  metis_tac[gas_origin_ptr_path_rules, listTheory.APPEND]
QED

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
  `inst.inst_opcode <> INVOKE` by fs[] >>
  `mem_safe_step 0 ctx inst s` by simp[mem_safe_step_non_invoke] >>
  mp_tac raw_call_step_mem_safe_origin_full >> simp[]
QED

Theorem raw_delegate_call_step_mem_safe_origin_full:
  inst.inst_opcode = DELEGATECALL /\
  inst.inst_operands = [gas_op;to_op;dp;dl;op;rz] /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand rz s = SOME rn /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p s (w2n az)) /\
  (rn <> 0w ==> ?p. op = Var p /\ ptr_covers G tn p s (w2n rn)) /\
  EVERY (\p. op_taint tn p = {}) inst.inst_operands /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
  allocas_from lo s /\ stor_taint_ok_at D tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  mem_safe_step 0 ctx inst s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK u ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G inst u, step_taint inst s u tn)
Proof
  strip_tac >>
  `?gas addr. eval_operand gas_op s = SOME gas /\
              eval_operand to_op s = SOME addr` by
    (Cases_on `eval_operand gas_op s` >> Cases_on `eval_operand to_op s` >>
     gvs[step_inst_base_opcode_eqs]) >>
  pop_assum strip_assume_tac >>
  `source_memory_read_ranges inst s = [(w2n ao,w2n az)] /\
   source_memory_write_ranges inst s = [(w2n ro,w2n rn)]` by
    simp[source_memory_read_ranges_def, source_memory_write_ranges_def,
         mem_read_ops_def, mem_write_ops_def, memory_range_of_operands_def] >>
  `access_ok lo G func inst s` by
    (simp[access_ok_def, mem_read_ops_def, mem_write_ops_def] >>
     fs[ptr_covers_def, eval_operand_def] >>
     rpt strip_tac
     >- (qpat_x_assum `rn <> 0w ==> _` drule >>
         strip_tac >> gvs[eval_operand_def] >> metis_tac[]) >>
     qpat_x_assum `az <> 0w ==> _` drule >>
     strip_tac >> gvs[eval_operand_def] >> metis_tac[]) >>
  `taint_ok func tn inst s` by
    (gvs[listTheory.EVERY_MEM, taint_ok_def] >> metis_tac[]) >>
  `step_inst 0 ctx inst s = OK u` by simp[step_inst_non_invoke] >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (simp[ptr_inst_ok_def] >> gvs[stor_taint_ok_at_def]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> GAS /\ inst_dload_in_section inst s` by
    simp[is_terminator_def, inst_dload_in_section_def] >>
  drule_all non_gas_mem_safe_origin_ptr_edge >> simp[] >> strip_tac >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (u with vs_inst_idx := SUC s.vs_inst_idx,
     step_prov PG G inst u, step_taint inst s u tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G inst u, step_taint inst s u tn)` by
    (irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  metis_tac[gas_origin_ptr_path_rules, listTheory.APPEND]
QED

Theorem raw_delegate_call_step_origin_full:
  inst.inst_opcode = DELEGATECALL /\
  inst.inst_operands = [gas_op;to_op;dp;dl;op;rz] /\
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
  `inst.inst_opcode <> INVOKE` by fs[] >>
  `mem_safe_step 0 ctx inst s` by simp[mem_safe_step_non_invoke] >>
  mp_tac raw_delegate_call_step_mem_safe_origin_full >> simp[]
QED
