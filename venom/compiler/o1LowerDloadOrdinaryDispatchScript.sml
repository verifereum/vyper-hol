Theory o1LowerDloadOrdinaryDispatch
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadJointArithmetic o1LowerDloadJointScalar
  o1LowerDloadJointTernary o1LowerDloadJointCompare o1LowerDloadJointShift
  o1LowerDloadJointResidualScalar o1LowerDloadJointRead0 o1LowerDloadJointRead1
  o1LowerDloadJointParam o1LowerDloadJointRetpc o1LowerDloadJointAssign
  o1LowerDloadJointBump o1LowerDloadJointIdentity o1LowerDloadJointMemoryRead
  o1LowerDloadJointMemoryWrite o1LowerDloadJointCleanWrite
  o1LowerDloadJointRangeCopy o1LowerDloadJointRangeRead
  o1LowerDloadJointStorageRead o1LowerDloadJointStorageWrite
  o1LowerDloadJointInternalEffects o1LowerDloadJointExternal
  o1LowerDloadReadiness venomInstProps o1LowerDloadJointRelation
  o1LowerDloadOccurrence o1PassContract contextCodegenRel venomInst
  venomWf ptrDiscipline venomExecSemantics list pointerConfinedDefs memLocDefs
  unitShapeDefs unitTransformDefs o1LowerDloadEnvironment
  o1LowerDloadRelocationKernel o1LowerDloadShared finite_map pred_set

Theorem ld_dalloca_success_iff[local]:
  inst.inst_opcode = DALLOCA ==>
  (step_inst fuel C inst s = OK s1 <=>
   ?sop out sz. inst.inst_operands = [sop] /\ inst.inst_outputs = [out] /\
     eval_operand sop s = SOME sz /\
     s1 = update_var out s.vs_fmp
            (s with vs_fmp := s.vs_fmp + n2w (ceil32 (w2n sz))))
Proof
  strip_tac >> simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_env_dalloca_update[local]:
  ld_env_agree sites fn H tn s t /\ inst.inst_opcode = DALLOCA /\
  inst.inst_outputs = [out] /\ tn1.t_var = tn.t_var |+ (out,{}) ==>
  ld_env_agree sites fn (occurrence_step a HP H inst s1) tn1
    (update_var out x (s with vs_fmp := f))
    (update_var out x (t with vs_fmp := f))
Proof
  strip_tac >>
  simp[ld_env_agree_def, venomStateTheory.update_var_def, FLOOKUP_UPDATE,
       occurrence_step_def, occurrence_out_def, set_prov_def,
       FLOOKUP_DRESTRICT, op_taint_def] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `out = v` >> gvs[ld_env_agree_def]) >>
  rpt gen_tac >> Cases_on `out = v` >>
  gvs[ld_env_agree_def, ld_value_agree_scalar, word_agree_except_def] >>
  rpt strip_tac >> TRY (gvs[] >> NO_TAC) >>
  first_x_assum drule_all >> simp[op_taint_def]
QED

(* Run tac only on a goal whose head constant is name ("?" for an
   existential); fail otherwise, so FIRST tries the next case. *)
fun ld_on_head name tac (g as (_, w)) =
  let val hd = if is_exists w then "?"
               else (#1 (dest_const (#1 (strip_comb w))) handle HOL_ERR _ => "")
  in if hd = name then tac g else NO_TAC g end

Theorem ld_joint_dalloca_next[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = DALLOCA /\
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
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `MEM fn C.ctx_functions` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >>
     first_x_assum drule >> simp[o1_fn_shape_def, wf_function_def, fn_labels_def]) >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    gvs[is_terminator_def] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def]) >>
  `vs.vs_allocas = FEMPTY` by gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `occurrence_annotation_ok (dyn_floor C vs) n a U B HP
     (occurrence_step a HP H inst s1) stk PG (step_prov PG G inst s1)
     (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[occ_frame_reachable_annotation] >>
  `!op. MEM op inst.inst_operands ==>
     op_prov H op = NONE /\ op_taint tn op = {} /\
     eval_operand op s = eval_operand op t` by
    (drule ld_joint_scalar_operands_clean >>
     gvs[is_pointer_preserving_op_def, mem_read_ops_def,
         mem_write_ops_def, retpc_use_ok_def, taint_ok_def] >> metis_tac[]) >>
  `tn.t_mem SUBSET (step_taint inst s s1 tn).t_mem /\
   (step_taint inst s s1 tn).t_stor = tn.t_stor /\
   (step_taint inst s s1 tn).t_trans = tn.t_trans /\
   (step_taint inst s s1 tn).t_imm = tn.t_imm` by
    simp[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
         imm_taint_def, step_writes_def,
         codegenRelTheory.source_memory_write_ranges_def,
         range_bytes_def, SUBSET_DEF] >>
  `?sop out sz. inst.inst_operands = [sop] /\ inst.inst_outputs = [out] /\
     eval_operand sop s = SOME sz /\
     s1 = update_var out s.vs_fmp
            (s with vs_fmp := s.vs_fmp + n2w (ceil32 (w2n sz)))` by
    (qpat_x_assum `step_inst fuel C inst s = OK s1` mp_tac >>
     simp[ld_dalloca_success_iff]) >>
  `eval_operand sop t = SOME sz` by metis_tac[MEM] >>
  `(step_taint inst s s1 tn).t_var = tn.t_var |+ (out,{})` by
    simp[step_taint_def, set_var_taint_def, out_taint_def] >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  qhdtm_assum `ld_joint_frame`
    (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
  `s.vs_fmp = t.vs_fmp` by gvs[ld_joint_local_fields_def] >>
  `active_inst fn inst2 (s with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `active_inst fn inst2 _` mp_tac >>
     simp[active_inst_def, venomStateTheory.update_var_def]) >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
  drule_all ld_joint_control_unchanged_next >> strip_tac >>
  qexists_tac `update_var out t.vs_fmp
    (t with vs_fmp := t.vs_fmp + n2w (ceil32 (w2n sz)))` >>
  qexistsl_tac [`u`,`fn'`] >>
  conj_tac >- (simp[ld_dalloca_success_iff] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `ld_env_agree sites fn (occurrence_step a HP H inst s1)
     (entry_taint with t_var := (step_taint inst s s1 tn).t_var)
     (update_var out s.vs_fmp
        (s with vs_fmp := s.vs_fmp + n2w (ceil32 (w2n sz))))
     (update_var out s.vs_fmp
        (t with vs_fmp := s.vs_fmp + n2w (ceil32 (w2n sz))))` by
    (irule ld_env_dalloca_update >> simp[] >>
     qexists_tac `entry_taint with t_var := tn.t_var` >> simp[]) >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  rewrite_tac[ld_joint_boundary_def] >> rpt conj_tac >>
  FIRST [
    first_assum ACCEPT_TAC,
    ld_on_head "ld_memory_agree"
      (gvs[ld_memory_agree_def, venomStateTheory.update_var_def, SUBSET_DEF] >>
       metis_tac[]),
    ld_on_head "ld_dyn_agree"
      (gvs[ld_dyn_agree_def, venomStateTheory.update_var_def, SUBSET_DEF] >>
       metis_tac[]),
    ld_on_head "ld_shared_agree"
      (gvs[ld_shared_agree_def, venomStateTheory.update_var_def] >> metis_tac[]),
    ld_on_head "?"
      (qexistsl_tac [`u`,`fn'`] >>
       conj_tac >- first_assum ACCEPT_TAC >>
       rewrite_tac[ld_joint_frame_def] >> rpt conj_tac >>
       (* DALLOCA moves only the output variable and the FMP, by the same
          amount on both sides *)
       FIRST [
         first_assum ACCEPT_TAC,
         rewrite_tac[venomStateTheory.update_var_def,
                     venomStateTheory.venom_state_accfupds,
                     combinTheory.K_THM] >> first_assum ACCEPT_TAC,
         ld_on_head "ld_env_agree"
           (qpat_x_assum `ld_env_agree _ _ (occurrence_step _ _ _ _ _) _ _ _` mp_tac >>
            qpat_x_assum `s.vs_fmp = t.vs_fmp` (fn th => rewrite_tac[th]) >>
            simp[NoAsms, ld_env_agree_def, venomStateTheory.update_var_def]),
         ld_on_head "ld_params_agree"
           (qpat_x_assum `ld_params_agree _ _ s t` mp_tac >>
            simp[NoAsms, ld_params_agree_def, venomStateTheory.update_var_def]),
         ld_on_head "ld_joint_local_fields"
           (qpat_x_assum `ld_joint_local_fields s t` mp_tac >>
            simp[NoAsms, ld_joint_local_fields_def, venomStateTheory.update_var_def]),
         ld_on_head "ld_joint_control"
           (qpat_x_assum `ld_joint_control _ _ _ (_ with vs_inst_idx := _) _` mp_tac >>
            simp[NoAsms, ld_joint_control_def, venomStateTheory.update_var_def] >>
            rpt strip_tac >> metis_tac[]),
         ld_on_head "ld_joint_allocas"
           (qpat_x_assum `ld_joint_allocas _ _ _ _ t` mp_tac >>
            simp[NoAsms, ld_joint_allocas_def, venomStateTheory.update_var_def] >>
            rpt strip_tac >> metis_tac[]),
         fn (g as (_, w)) =>
           (print ("ld_joint_dalloca_next: no frame case closes " ^
                   term_to_string w ^ "\n"); NO_TAC g)]),
    gvs[venomStateTheory.update_var_def] >> NO_TAC,
    fn (g as (_, w)) => (print ("ld_joint_dalloca_next: no case closes " ^
        term_to_string w ^ "\n"); NO_TAC g)]
QED

Theorem ld_joint_ordinary_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t n a U B HP H sites X ts /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_src_inv D C vs /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  (?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst) /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DLOAD; DLOADBYTES; ALLOCA] /\
  ~in_revert_forward fn s /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 t1 u fn'.
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> strip_tac >>
     drule occ_frame_reachable_annotation >> simp[]) >>
  `wf_function fn` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> first_x_assum drule >>
     simp[o1_fn_shape_def]) >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `?inst2. active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ld_nonterminator_successor >>
     drule_all step_preserves_control_flow >> simp[] >> metis_tac[]) >>
  `~MEM inst.inst_opcode [MEMTOP; DRET; GETFMP; SETFMP; RETFMP; FMP_PARAM]` by
    (`?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
       metis_tac[ptr_discipline_fn_ptr_ok] >>
     fs[EVERY_MEM] >> first_x_assum drule >>
     simp[fn_ptr_ok_def] >> strip_tac >> first_x_assum drule >> simp[MEM]) >>
  qexists_tac `inst2` >> simp[] >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (irule ld_joint_dalloca_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [ADD; SUB]`
  >- (irule ld_joint_arithmetic_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; SLT; SGT; AND; OR; XOR]`
  >- (irule ld_joint_binary_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [ADDMOD; MULMOD]`
  >- (irule ld_joint_ternary_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [ISZERO; NOT]`
  >- (irule ld_joint_unary_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [LT; GT; EQ]`
  >- (irule ld_joint_compare_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [SHL; SHR; SAR]`
  >- (irule ld_joint_shift_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [SIGNEXTEND; BYTE; OFFSET; INITIAL_FMP]`
  >- (irule ld_joint_residual_scalar_next >> simp[]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (irule ld_joint_gas_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE;
    CHAINID; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
    BLOBBASEFEE; CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE]`
  >- (irule ld_joint_read0_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [BLOCKHASH; BLOBHASH; BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD]`
  >- (irule ld_joint_read1_next >> simp[]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (irule ld_joint_param_next >> simp[]) >>
  Cases_on `inst.inst_opcode = RETPC_PARAM`
  >- (irule ld_joint_retpc_next >> simp[]) >>
  Cases_on `inst.inst_opcode = ASSIGN`
  >- (irule ld_joint_assign_next >> simp[]) >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (irule ld_joint_bump_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE]`
  >- (irule ld_joint_identity_next >> simp[]) >>
  Cases_on `inst.inst_opcode = MLOAD`
  >- (irule ld_joint_mload_next >> simp[]) >>
  Cases_on `inst.inst_opcode = MSTORE`
  >- (irule ld_joint_mstore_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [MSTORE8; CALLDATACOPY; CODECOPY; RETURNDATACOPY; EXTCODECOPY]`
  >- (irule ld_joint_clean_write_next >> simp[]) >>
  Cases_on `inst.inst_opcode = MCOPY`
  >- (irule ld_joint_mcopy_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [ILOAD; SHA3]`
  >- (irule ld_joint_range_read_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [SLOAD; TLOAD]`
  >- (irule ld_joint_storage_load_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [SSTORE; TSTORE]`
  >- (irule ld_joint_storage_store_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [ISTORE; LOG]`
  >- (irule ld_joint_internal_effect_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL]`
  >- (irule ld_joint_call_next >> simp[]) >>
  Cases_on `inst.inst_opcode = DELEGATECALL`
  >- (irule ld_joint_delegatecall_next >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [CREATE; CREATE2]`
  >- (irule ld_joint_create_next >> simp[]) >>
  `inst.inst_opcode = PHI` by
    (Cases_on `inst.inst_opcode` >> gvs[MEM, is_terminator_def]) >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED
