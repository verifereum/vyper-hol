(* Clean unary scalar operands at a joint boundary. *)
Theory o1LowerDloadJointScalar
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadJointAssign o1LowerDloadGhost o1LowerDloadOpaque
  o1LowerDloadJointRelation o1LowerDloadOccurrence ptrDiscipline
  pointerConfinedDefs memLocDefs unitShapeDefs o1PassContract
  venomInst finite_map list pred_set contextCodegenRel irSupply
  o1LowerDloadEnvironment o1LowerDloadRelocationKernel venomState
  venomExecSemantics venomExecProps

Theorem ld_scalar_no_provenance:
  ptr_use_ok P pv inst /\ FDOM G SUBSET pv /\
  ~is_pointer_preserving_op inst.inst_opcode /\
  ~MEM inst.inst_opcode [LT; GT; EQ; INVOKE] /\
  mem_read_ops inst = NONE /\ mem_write_ops inst = NONE /\
  MEM op inst.inst_operands ==> op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v` >>
  Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN pv` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[ptr_use_ok_def] >> metis_tac[]
QED

Theorem ld_unary_no_provenance:
  ptr_use_ok P pv inst /\ FDOM G SUBSET pv /\
  MEM inst.inst_opcode [ISZERO; NOT] /\ MEM op inst.inst_operands ==>
  op_prov G op = NONE
Proof
  strip_tac >> irule ld_scalar_no_provenance >>
  qexistsl_tac [`P`,`inst`,`pv`] >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def]
QED

Theorem ld_active_operand_ir_var:
  active_inst fn inst s /\ MEM (Var v) inst.inst_operands ==>
  MEM v (fn_ir_vars fn)
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (fs[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[]) >>
  simp[NoAsms, fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP] >>
  qexists_tac `FLAT (MAP inst_ir_vars bb.bb_instructions)` >>
  conj_tac >- (qexists_tac `bb` >> simp[]) >>
  simp[NoAsms, MEM_FLAT, MEM_MAP] >> qexists_tac `inst_ir_vars inst` >>
  conj_tac >- (qexists_tac `inst` >> simp[]) >>
  simp[inst_ir_vars_def, inst_uses_def] >> disj2_tac >>
  qpat_x_assum `MEM (Var v) _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  simp[operand_vars_APPEND, operand_vars_def, operand_var_def]
QED

Theorem ld_active_operand_non_retpc:
  opaque_use_ok fn /\ active_inst fn inst s /\
  (!v. ~retpc_use_ok inst v) /\ MEM (Var v) inst.inst_operands ==>
  ~retpc_var fn v
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  metis_tac[opaque_use_ok_retpc_use]
QED

Theorem ld_joint_nonaddress_no_provenance:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  active_inst fn inst s /\ MEM op inst.inst_operands /\
  inst.inst_opcode <> INVOKE /\ ~is_pointer_preserving_op inst.inst_opcode /\
  ~MEM inst.inst_opcode [LT;GT;EQ] /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) ==>
  op_prov H op = NONE
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[frame_reachable_prov_support] >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >>
     `MEM inst (fn_insts fn)` by
       (fs[active_inst_def, fn_insts_def,
           o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
     metis_tac[]) >>
  `op_prov G op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >> rename1 `FLOOKUP G vv` >>
     Cases_on `FLOOKUP G vv` >> simp[] >>
     `vv IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     gvs[ptr_use_ok_def] >> metis_tac[]) >>
  `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
    fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
  drule occurrence_op_erasure >> disch_then (qspec_then `op` mp_tac) >>
  Cases_on `op_prov H op` >> simp[occurrence_param_ok_def]
QED

Theorem ld_joint_nonaddress_operand:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ MEM op inst.inst_operands /\
  inst.inst_opcode <> INVOKE /\ ~is_pointer_preserving_op inst.inst_opcode /\
  ~MEM inst.inst_opcode [LT;GT;EQ] /\ op_taint tn op = {} /\
  (!v. ~retpc_use_ok inst v) /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `op_prov H op = NONE` by
    (irule ld_joint_nonaddress_no_provenance >> metis_tac[]) >>
  irule ld_joint_operand_clean >>
  metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc]
QED

Theorem ld_joint_scalar_no_provenance:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  active_inst fn inst s /\ ~is_pointer_preserving_op inst.inst_opcode /\
  ~MEM inst.inst_opcode [LT; GT; EQ; INVOKE] /\
  mem_read_ops inst = NONE /\ mem_write_ops inst = NONE ==>
  !op. MEM op inst.inst_operands ==> op_prov H op = NONE
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  qpat_x_assum `ptr_discipline _ _ _`
    (strip_assume_tac o MATCH_MP ptr_discipline_fn_ptr_ok) >>
  drule frame_reachable_prov_support >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (gvs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
    fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
  rpt strip_tac >>
  `op_prov G op = NONE` by (irule ld_scalar_no_provenance >> metis_tac[]) >>
  drule occurrence_op_erasure >> disch_then (qspec_then `op` mp_tac) >>
  simp[occurrence_param_ok_def]
QED

Theorem ld_joint_scalar_operands_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  ~is_pointer_preserving_op inst.inst_opcode /\
  ~MEM inst.inst_opcode [LT; GT; EQ; INVOKE] /\
  mem_read_ops inst = NONE /\ mem_write_ops inst = NONE /\
  (!tn s op. taint_ok fn tn inst s /\ MEM op inst.inst_operands ==>
    op_taint tn op = {}) /\
  (!v. ~retpc_use_ok inst v) ==>
  !op. MEM op inst.inst_operands ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_prov H op = NONE` by
    metis_tac[ld_joint_scalar_no_provenance] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  rpt strip_tac >>
  `op_prov H op = NONE /\ op_taint tn op = {}` by metis_tac[] >>
  simp[] >> irule ld_joint_operand_clean >>
  metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc]
QED

Theorem ld_joint_unary_operands_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ISZERO; NOT] ==>
  !op. MEM op inst.inst_operands ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule ld_joint_scalar_operands_clean >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def,
    mem_write_ops_def, retpc_use_ok_def, taint_ok_def] >> metis_tac[]
QED

Theorem ld_joint_binary_operands_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; SLT; SGT; AND; OR; XOR] ==>
  !op. MEM op inst.inst_operands ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule ld_joint_scalar_operands_clean >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def,
    mem_write_ops_def, retpc_use_ok_def, taint_ok_def] >> metis_tac[]
QED

Theorem ld_env_clean_update:
  ld_env_agree sites fn H tn s t /\ inst.inst_outputs = [out] /\
  occurrence_out a HP H inst (update_var out x s) = NONE /\
  out_taint tn inst s = {} ==>
  ld_env_agree sites fn
    (occurrence_step a HP H inst (update_var out x s))
    (step_taint inst s (update_var out x s) tn)
    (update_var out x s) (update_var out x t)
Proof
  strip_tac >>
  simp[ld_env_agree_def, update_var_def, FLOOKUP_UPDATE,
       occurrence_step_def, set_prov_def, FLOOKUP_DRESTRICT,
       step_taint_def, set_var_taint_def, op_taint_def] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `v = out` >> gvs[ld_env_agree_def]) >>
  rpt gen_tac >> Cases_on `v = out` >>
  gvs[ld_env_agree_def, op_taint_def, ld_value_agree_scalar,
      word_agree_except_def] >> rpt strip_tac >> gvs[]
QED

Theorem ld_joint_unary_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ISZERO; NOT] /\ step_inst fuel C inst s = OK s1 ==>
  ?out x. s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out x t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out x t)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    metis_tac[ld_joint_unary_operands_clean] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_pure1_def, AllCaseEqs()] >>
  (strip_tac >> rename1 `eval_operand op1 s = SOME arg` >>
  qpat_x_assum `update_var _ _ _ = s1` (SUBST_ALL_TAC o SYM) >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexistsl_tac [`out`,`value`] >> simp[] >>
  conj_tac
  >- (qexists_tac `arg` >> simp[Abbr `value`] >> metis_tac[MEM]) >>
  irule ld_env_clean_update >> simp[] >>
  conj_tac >- simp[out_taint_def] >>
  conj_tac >- simp[occurrence_out_def, out_prov_def] >>
  metis_tac[ld_joint_environment])
QED

Theorem ld_joint_unary_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ MEM inst.inst_opcode [ISZERO; NOT] /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  strip_tac >> drule_all ld_joint_unary_step >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by gvs[] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    gvs[is_terminator_def] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def] >> gvs[]) >>
  `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1) (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def] >> gvs[]) >>
  qexists_tac `update_var out x t` >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  irule ld_joint_var_update_next >> simp[] >>
  conj_tac >- (qexistsl [`out`,`s.vs_gas_readings`,`x`,`x`] >>
    fs[update_var_def, venom_state_component_equality,
       ld_joint_boundary_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[] >>
  gvs[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, update_var_def, new_site_bytes_def, written_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure1_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem ld_joint_binary_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; SLT; SGT; AND; OR; XOR] /\
  step_inst fuel C inst s = OK s1 ==>
  ?out x. s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out x t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out x t)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    metis_tac[ld_joint_binary_operands_clean] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  fs[MEM] >>
  (gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >>
  qpat_x_assum `update_var _ _ _ = s1` (SUBST_ALL_TAC o SYM) >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexistsl_tac [`out`,`value`] >> simp[] >>
  conj_tac
  >- (simp[Abbr `value`] >> metis_tac[MEM]) >>
  irule ld_env_clean_update >> simp[] >>
  conj_tac >- simp[out_taint_def] >>
  conj_tac >- simp[occurrence_out_def, out_prov_def] >>
  metis_tac[ld_joint_environment])
QED

Theorem ld_joint_binary_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\
  MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; SLT; SGT; AND; OR; XOR] /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  strip_tac >> drule_all ld_joint_binary_step >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by gvs[] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    gvs[is_terminator_def] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def] >> gvs[]) >>
  `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1) (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def] >> gvs[]) >>
  qexists_tac `update_var out x t` >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  irule ld_joint_var_update_next >> simp[] >>
  conj_tac >- (qexistsl [`out`,`s.vs_gas_readings`,`x`,`x`] >>
    fs[update_var_def, venom_state_component_equality,
       ld_joint_boundary_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[] >>
  fs[MEM] >>
  (gvs[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, update_var_def, new_site_bytes_def, written_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  rpt (pop_assum kall_tac) >>
  namedCases_on `inst.inst_operands` ["", "h tail"] >> simp[] >>
  namedCases_on `tail` ["", "h2 tail2"] >> simp[] >>
  namedCases_on `tail2` ["", "h3 tail3"] >> simp[] >>
  Cases_on `tail3` >> simp[])
QED
