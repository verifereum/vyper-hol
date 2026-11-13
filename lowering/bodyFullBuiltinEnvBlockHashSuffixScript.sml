(* BlockHash suffix: one endpoint and one ghost pair for all horizons. *)
Theory bodyFullBuiltinEnvBlockHashSuffix
Ancestors
  bodyFullGhostFrame fragGasEmitCtrl fragGasSeqPtr gasOutcomeFullCompose
  builtinProps builtinMisc builtinSimple exprSimUnopProps exprSimDefs
  exprSimHypsDefs exprSimSource exprSimProps exprLoweringProps compileEnv
  loweringStateRelDefs exprUnopSimDefs bodyPtrDefs varsExt freshWrites
  fragExec fragExecMem memSafeRun allocaHistoryFragment arithmeticProps
  vyperInterpreter vyperContext vyperValue vyperValueOperation valueEncoding
  vyperStorageTrace vyperStorageFootprint venomExecSemantics venomInstProofs
  venomInst venomState integer integer_word words list rich_list finite_map
  emitHelper arithmetic builtinIntClamp ptrDiscipline ptrSafeRun decoderGhostFramePtr codegenRel
  ghostPcTransportPtr instIdxIndep
Libs intLib

Theorem blockhash_full_suffix:
 !arg sa op sb func st0 cenv cx mid s ctx DF lo d G tn explicit PG i.
 compile_blockhash arg sa = (op,sb) /\ fn_has_code sa sb func /\
 fn_inst_ids_distinct func /\ storage_trace_domain cx st0 mid.storage_trace /\
 local_ptrs_reserved cenv sa /\
 (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
 (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
 0 <= i /\ i < 2 ** 256 /\
 eval_operand arg s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i)) /\
 op_taint tn arg = {} /\ op_prov G arg = NONE /\
 (!p. arg = Var p ==> not_fresh_at sa p) /\ ~ctx_has_dalloca ctx /\
 ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
 (!H. valid_horizon cx st0 H mid.storage_trace ==>
   stmt_state_rel H ctx func cenv cx mid s /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx mid G tn s) ==>
 ?r G' tn'.
 (!H. valid_horizon cx st0 H mid.storage_trace ==>
   gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G',tn') /\
   case unop_result cx (BaseT (BytesT (Fixed 32))) BlockHash
          [BaseT (UintT 256)] (IntV i) mid of
   | INL v => ?t. r = OK t /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       expr_val_rel cx (BaseT (BytesT (Fixed 32))) v op t /\
       op_taint tn' op = {} /\ op_prov G' op = NONE /\
       stmt_state_rel H ctx func cenv cx mid t /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G' tn' t /\
       alloca_history func t /\
       t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
       t.vs_alloca_next = s.vs_alloca_next /\
       tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
       tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
       (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
          FLOOKUP G' p = FLOOKUP G p /\
          op_taint tn' (Var p) = op_taint tn (Var p))
   | INR ex => expr_exit (INR ex) r)
Proof
 rpt gen_tac >> strip_tac >>
 `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
    mid.storage_trace` by fs[storage_trace_domain_def] >>
 `stmt_state_rel (storage_trace_horizon mid.storage_trace)
    ctx func cenv cx mid s` by metis_tac[] >>
 `call_ctx_rel cx.txn s.vs_call_ctx s.vs_tx_ctx s.vs_block_ctx` by
   fs[stmt_state_rel_def, state_rel_def] >>
 `tx_env_ok cx.txn` by fs[call_ctx_rel_def] >>
 `?n. i = &n` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
 gvs[typed_val_to_w256_def, val_to_w256_def, integer_wordTheory.i2w_pos] >>
 `0 < cx.txn.block_number /\ cx.txn.block_number < 2 ** 255` by
   fs[tx_env_ok_def] >>
 `n < 2 ** 256` by simp[] >>
 drule_all blockhash_signed_window >> strip_tac >>
 `s.vs_block_ctx.bc_number = n2w cx.txn.block_number` by
   fs[call_ctx_rel_def] >>
 `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
 `eval_operand arg (drop_fresh sa s) = SOME (n2w n)` by
   metis_tac[eval_operand_drop_fresh] >>
 `EVERY (\j. j.inst_opcode <> GAS /\ j.inst_opcode <> INVOKE /\
      ~is_terminator j.inst_opcode /\ ~is_ext_call_op j.inst_opcode)
      (emitted_insts sa sb)` by
   (drule compile_blockhash_outputs >> simp[EVERY_MEM] >>
    rpt strip_tac >> first_x_assum drule >> rpt strip_tac >>
    gvs[is_terminator_def, is_ext_call_op_def]) >>
 `vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
    (run_inst_seq (emitted_insts sa sb) s)` by
   (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
    fs[EVERY_MEM]) >>
 qabbrev_tac `cur = STRING #"%" (toString sa.cs_next_var)` >>
 qabbrev_tac `low = STRING #"%" (toString (sa.cs_next_var+1))` >>
 qabbrev_tac `old = STRING #"%" (toString (sa.cs_next_var+2))` >>
 qabbrev_tac `good = STRING #"%" (toString (sa.cs_next_var+3))` >>
 qabbrev_tac `recent = STRING #"%" (toString (sa.cs_next_var+4))` >>
 qabbrev_tac `out = STRING #"%" (toString (sa.cs_next_var+5))` >>
 `op = Var out /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id NUMBER [] [cur];
     mk_inst (sa.cs_next_id+1) SUB [Var cur; Lit 256w] [low];
     mk_inst (sa.cs_next_id+2) SLT [arg; Var low] [old];
     mk_inst (sa.cs_next_id+3) ISZERO [Var old] [good];
     mk_inst (sa.cs_next_id+4) ASSERT [Var good] [];
     mk_inst (sa.cs_next_id+5) LT [arg; Var cur] [recent];
     mk_inst (sa.cs_next_id+6) ASSERT [Var recent] [];
     mk_inst (sa.cs_next_id+7) BLOCKHASH [arg] [out]] /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
   (qpat_x_assum `compile_blockhash _ _ = _` mp_tac >>
    simp[compile_blockhash_def, emit_op_def, emit_void_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
      emit_def, Abbr `cur`, Abbr `low`, Abbr `old`, Abbr `good`,
      Abbr `recent`, Abbr `out`] >> strip_tac >> gvs[] >>
    simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
 `!p. not_fresh_at sa p ==>
    p <> cur /\ p <> low /\ p <> old /\ p <> good /\ p <> recent /\ p <> out` by
   (simp[Abbr `cur`, Abbr `low`, Abbr `old`, Abbr `good`,
      Abbr `recent`, Abbr `out`, not_fresh_at_def] >> metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
 `ALL_DISTINCT [cur;low;old;good;recent;out]` by
   simp[Abbr `cur`, Abbr `low`, Abbr `old`, Abbr `good`,
      Abbr `recent`, Abbr `out`, builtinIntClampTheory.fresh_var_name_eq] >>
 `arg <> Var cur /\ arg <> Var low /\ arg <> Var old /\
  arg <> Var good /\ arg <> Var recent /\ arg <> Var out` by metis_tac[] >>
 qabbrev_tac `j1 = mk_inst sa.cs_next_id NUMBER [] [cur]` >>
 qabbrev_tac `j2 = mk_inst (sa.cs_next_id+1) SUB [Var cur; Lit 256w] [low]` >>
 qabbrev_tac `j3 = mk_inst (sa.cs_next_id+2) SLT [arg; Var low] [old]` >>
 qabbrev_tac `j4 = mk_inst (sa.cs_next_id+3) ISZERO [Var old] [good]` >>
 qabbrev_tac `u1 = update_var cur (n2w cx.txn.block_number) s` >>
 qabbrev_tac `u2 = update_var low (n2w cx.txn.block_number - 256w) u1` >>
 qabbrev_tac `u3 = update_var old
    (bool_to_word (word_lt (n2w n:bytes32) (n2w cx.txn.block_number - 256w))) u2` >>
 qabbrev_tac `u4 = update_var good
    (bool_to_word (~word_lt (n2w n:bytes32) (n2w cx.txn.block_number - 256w))) u3` >>
 `step_inst_base j1 s = OK u1 /\
  step_inst_base j2 u1 = OK u2 /\
  step_inst_base j3 u2 = OK u3 /\
  step_inst_base j4 u3 = OK u4` by
   (Cases_on `arg` >>
    gvs[ALL_DISTINCT, eval_operand_def, lookup_var_def] >>
    simp[Abbr `j1`, Abbr `j2`, Abbr `j3`, Abbr `j4`,
      Abbr `u1`, Abbr `u2`, Abbr `u3`, Abbr `u4`,
      step_inst_base_opcode_eqs, exec_read0_def, exec_pure2_def,
      exec_pure1_def, mk_inst_def, eval_operand_def,
      update_var_def, lookup_var_def, FLOOKUP_UPDATE, bool_to_word_def]) >>
 qabbrev_tac `G1 = step_prov PG G j1 u1` >>
 qabbrev_tac `tn1 = step_taint j1 s u1 tn` >>
 qabbrev_tac `G2 = step_prov PG G1 j2 u2` >>
 qabbrev_tac `tn2 = step_taint j2 u1 u2 tn1` >>
 qabbrev_tac `G3 = step_prov PG G2 j3 u3` >>
 qabbrev_tac `tn3 = step_taint j3 u2 u3 tn2` >>
 qabbrev_tac `G4 = step_prov PG G3 j4 u4` >>
 qabbrev_tac `tn4 = step_taint j4 u3 u4 tn3` >>
 `(!p. not_fresh_at sa p ==> lookup_var p u4 = lookup_var p s /\
       FLOOKUP G4 p = FLOOKUP G p /\
       op_taint tn4 (Var p) = op_taint tn (Var p)) /\
  tn4.t_mem = tn.t_mem /\ tn4.t_stor = tn.t_stor /\
  tn4.t_trans = tn.t_trans /\ tn4.t_imm = tn.t_imm` by
   (conj_tac
    >- (gen_tac >> strip_tac >>
        `p <> cur /\ p <> low /\ p <> old /\ p <> good` by metis_tac[] >>
        simp[Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
        simp[Abbr `G4`, Abbr `G3`, Abbr `G2`, Abbr `G1`,
          Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
          Abbr `j4`, Abbr `j3`, Abbr `j2`, Abbr `j1`,
          step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
    simp[Abbr `tn4`, Abbr `j4`, step_taint_def, mem_taint_def,
      store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
      step_writes_def, new_site_bytes_def, source_memory_write_ranges_def,
      range_bytes_def, written_taint_def] >>
    simp[Abbr `tn3`, Abbr `j3`, step_taint_def, mem_taint_def,
      store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
      step_writes_def, new_site_bytes_def, source_memory_write_ranges_def,
      range_bytes_def, written_taint_def] >>
    simp[Abbr `tn2`, Abbr `j2`, step_taint_def, mem_taint_def,
      store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
      step_writes_def, new_site_bytes_def, source_memory_write_ranges_def,
      range_bytes_def, written_taint_def] >>
    simp[Abbr `tn1`, Abbr `j1`, step_taint_def, mem_taint_def,
      store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
      step_writes_def, new_site_bytes_def, source_memory_write_ranges_def,
      range_bytes_def, written_taint_def] >>
    simp[Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, update_var_def] >>
    simp[FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
 `op_prov G1 (Var cur) = NONE /\ op_taint tn1 (Var cur) = {}` by
   (simp[Abbr `G1`, Abbr `tn1`, Abbr `j1`, step_prov_def,
      out_prov_def, set_prov_def, op_prov_def, step_taint_def,
      op_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
      FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
 `op_prov G2 (Var low) = NONE /\ op_taint tn2 (Var low) = {}` by
   (simp[Abbr `G2`, Abbr `tn2`, Abbr `j2`, step_prov_def,
      out_prov_def, set_prov_def, first_prov_def, op_prov_def,
      step_taint_def, op_taint_def, set_var_taint_def, out_taint_def,
      mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
    Cases_on `eval_operand (Var cur) u1` >> simp[]) >>
 `op_prov G3 (Var old) = NONE /\ op_taint tn3 (Var old) = {}` by
   (simp[Abbr `G3`, Abbr `tn3`, Abbr `j3`, step_prov_def,
      out_prov_def, set_prov_def, op_prov_def, step_taint_def,
      op_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
      FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
    Cases_on `eval_operand arg u2` >> simp[]) >>
 `op_prov G4 (Var good) = NONE /\ op_taint tn4 (Var good) = {}` by
   (simp[Abbr `G4`, Abbr `tn4`, Abbr `j4`, step_prov_def,
      out_prov_def, set_prov_def, op_prov_def, step_taint_def,
      op_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
      FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
    Cases_on `eval_operand (Var old) u3` >> simp[]) >>
 `op_taint tn2 arg = {} /\ op_prov G2 arg = NONE` by
   (Cases_on `arg` >>
    fs[op_taint_def, op_prov_def, Abbr `tn2`, Abbr `tn1`,
      Abbr `G2`, Abbr `G1`, Abbr `j2`, Abbr `j1`,
      GSYM op_taint_def, step_taint_other_output, step_prov_other_output,
      mk_inst_def]) >>
 `!D lo k. allocas_from lo s ==>
    ptr_inst_ok D lo 0 ctx func G tn j1 s /\
    ptr_inst_ok D lo 0 ctx func G1 tn1 j2 (u1 with vs_inst_idx := k) /\
    ptr_inst_ok D lo 0 ctx func G2 tn2 j3 (u2 with vs_inst_idx := k) /\
    ptr_inst_ok D lo 0 ctx func G3 tn3 j4 (u3 with vs_inst_idx := k)` by
   (rpt gen_tac >> strip_tac >>
    simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
      Abbr `j1`, Abbr `j2`, Abbr `j3`, Abbr `j4`, mk_inst_def,
      source_memory_write_ranges_def, contextCodegenRelTheory.source_memory_read_ranges_def,
      step_inst_non_invoke, step_inst_inst_idx_indep, is_terminator_def,
      exec_result_map_def] >>
    simp[Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u4`,
      update_var_def, allocas_from_def] >>
    fs[allocas_from_def] >> conj_tac
    >- (reverse conj_tac >- metis_tac[] >>
        qx_gen_tac `operand` >> Cases_on `operand = Var cur` >> simp[] >>
        Cases_on `operand = Lit 256w` >> simp[op_taint_def]) >>
    conj_tac
    >- (reverse conj_tac >- metis_tac[] >>
        qx_gen_tac `operand` >> Cases_on `operand = arg` >> simp[] >>
        Cases_on `operand = Var low` >> simp[]) >> metis_tac[]) >>
 `!D lo. allocas_from lo s ==>
    inst_seq_ptr D lo ctx func PG G tn [j1;j2;j3;j4] s G4 tn4` by
   (map_every qx_gen_tac [`D0`,`lo0`] >> strip_tac >>
    `ptr_inst_ok D0 lo0 0 ctx func G tn j1 s` by metis_tac[] >>
    `~is_terminator j2.inst_opcode /\ ~is_terminator j3.inst_opcode /\
     ~is_terminator j4.inst_opcode` by
      simp[Abbr `j2`, Abbr `j3`, Abbr `j4`, mk_inst_def, is_terminator_def] >>
    simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
      Abbr `G4`, Abbr `G3`, Abbr `G2`, Abbr `G1`,
      Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`] >>
    metis_tac[]) >>
 `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
   (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
    qexists_tac `l` >> simp[DROP_APPEND] >>
    `LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + 8) = 0` by decide_tac >>
    simp[]) >>
 `run_inst_seq [j1;j2;j3;j4] s = OK u4` by
   simp[run_inst_seq_def] >>
 `run_inst_seq_mem_ok [j1;j2;j3;j4] s` by
   (irule run_inst_seq_mem_ok_every >>
    simp[Abbr `j1`, Abbr `j2`, Abbr `j3`, Abbr `j4`,
      unitTransformDefsTheory.inst_mem_below_frontier_def,
      memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      source_memory_write_ranges_def]) >>
 `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u4 with vs_inst_idx := s.vs_inst_idx + 4),G4,tn4)` by
   (gen_tac >> strip_tac >>
    `allocas_from lo s` by
      (qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >>
       simp[ghost_inv_at_def]) >>
    `inst_seq_ptr (DF H) lo ctx func PG G tn [j1;j2;j3;j4] s G4 tn4` by metis_tac[] >>
    `isPREFIX [j1;j2;j3;j4] (DROP s.vs_inst_idx bb.bb_instructions)` by
      simp[IS_PREFIX_APPEND] >>
    `EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode) [j1;j2;j3;j4]` by
      simp[Abbr `j1`, Abbr `j2`, Abbr `j3`, Abbr `j4`, mk_inst_def, is_terminator_def] >>
    drule_all run_inst_seq_gas_origin_ptr_path >>
    simp[Abbr `j1`, Abbr `j2`, Abbr `j3`, Abbr `j4`, mk_inst_def]) >>
 qabbrev_tac `j5 = mk_inst (sa.cs_next_id+4) ASSERT [Var good] []` >>
 qabbrev_tac `v4 = u4 with vs_inst_idx := s.vs_inst_idx + 4` >>
 `get_instruction bb v4.vs_inst_idx = SOME j5` by
   (`s.vs_inst_idx + 4 < LENGTH bb.bb_instructions` by
      (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
       simp[LENGTH_DROP] >> decide_tac) >>
    `EL 4 (DROP s.vs_inst_idx bb.bb_instructions) = j5` by simp[Abbr `j5`] >>
    simp[Abbr `v4`, get_instruction_def] >> metis_tac[EL_DROP, ADD_COMM]) >>
 `eval_operand (Var good) v4 =
    SOME (bool_to_word (~word_lt (n2w n:bytes32) (n2w cx.txn.block_number - 256w))) /\
  ~v4.vs_halted /\ v4.vs_current_bb = s.vs_current_bb /\
  v4.vs_allocas = s.vs_allocas /\ v4.vs_alloca_next = s.vs_alloca_next` by
   simp[Abbr `v4`, Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
     eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE, ALL_DISTINCT] >>
 `!D lo. allocas_from lo s ==> ptr_inst_ok D lo 0 ctx func G4 tn4 j5 v4` by
   (rpt gen_tac >> strip_tac >>
    simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, Abbr `j5`, mk_inst_def,
      source_memory_write_ranges_def, contextCodegenRelTheory.source_memory_read_ranges_def,
      allocas_from_def, step_inst_def, step_inst_base_def] >>
    IF_CASES_TAC >> simp[] >> fs[allocas_from_def]) >>
 `word_lt (n2w n:bytes32) (n2w cx.txn.block_number - 256w) ==>
   !H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
       (Abort Revert_abort (revert_state (set_returndata [] v4)),G4,tn4)` by
   (strip_tac >> gen_tac >> strip_tac >>
    `allocas_from lo s` by
      (qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _ /\ _ /\ _` drule >>
       simp[ghost_inv_at_def]) >>
    `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (v4,G4,tn4) []
       (Abort Revert_abort (revert_state (set_returndata [] v4)),G4,tn4)` by
      (irule exit_inst_origin_ptr >>
       simp[exit_result_def] >> qexistsl [`bb`,`j5`] >>
       simp[Abbr `j5`, mk_inst_def, step_inst_def, step_inst_base_def,
         bool_to_word_def, exit_result_def, mem_safe_step_def,
         unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def,
         source_memory_write_ranges_def, contextCodegenRelTheory.source_memory_read_ranges_def,
         gasEventsTheory.gas_events_step_def, gasCountTheory.gas_count_step_def] >> metis_tac[]) >>
    qpat_x_assum `!H. valid_horizon _ _ _ _ ==> gas_origin_ptr_path _ _ _ _` drule >>
    strip_tac >>
    drule fragGasOriginPtrTheory.gas_origin_ptr_path_append >>
    simp[]) >>
 qabbrev_tac `j6 = mk_inst (sa.cs_next_id+5) LT [arg;Var cur] [recent]` >>
 qabbrev_tac `u6 = update_var recent (bool_to_word (n < cx.txn.block_number)) u4` >>
 qabbrev_tac `G6 = step_prov PG G4 j6 u6` >>
 qabbrev_tac `tn6 = step_taint j6 u4 u6 tn4` >>
 `step_prov PG G4 j5 u4 = G4 /\ step_taint j5 u4 u4 tn4 = tn4` by
   (simp[Abbr `j5`, mk_inst_def, step_prov_def, step_taint_def,
     mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
     step_writes_def, new_site_bytes_def, source_memory_write_ranges_def,
     range_bytes_def, written_taint_def, set_var_taint_def, set_prov_def] >>
    simp[taint_component_equality, DRESTRICT_UNIV,
      FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
 `eval_operand arg u4 = SOME (n2w n) /\
  eval_operand (Var cur) u4 = SOME (n2w cx.txn.block_number)` by
   (Cases_on `arg` >> fs[ALL_DISTINCT, Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
     eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
 `cx.txn.block_number < 2 ** 256` by fs[] >>
 `cx.txn.block_number MOD dimword (:256) = cx.txn.block_number` by
   fs[wordsTheory.dimword_def] >>
 `step_inst_base j6 u4 = OK u6` by
   simp[Abbr `j6`, Abbr `u6`, step_inst_base_def, exec_pure2_def,
     mk_inst_def, eval_operands_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
 `op_taint tn4 arg = {} /\ op_prov G4 arg = NONE /\
  op_taint tn4 (Var cur) = {} /\ op_prov G4 (Var cur) = NONE` by
   (Cases_on `arg` >>
    fs[ALL_DISTINCT, op_taint_def, op_prov_def, Abbr `tn4`, Abbr `tn3`,
      Abbr `tn2`, Abbr `G4`, Abbr `G3`, Abbr `G2`, Abbr `j4`, Abbr `j3`,
      Abbr `j2`, Abbr `G1`, Abbr `tn1`, Abbr `j1`,
      GSYM op_taint_def, step_taint_other_output, step_prov_other_output,
      mk_inst_def]) >>
 `eval_operand (Var good) u4 =
    SOME (bool_to_word (~word_lt (n2w n:bytes32) (n2w cx.txn.block_number - 256w)))` by
   (qpat_x_assum `eval_operand (Var good) v4 = _` mp_tac >>
    simp[Abbr `v4`, eval_operand_def, lookup_var_def]) >>
 `step_inst_base j5 u4 =
    if word_lt (n2w n:bytes32) (n2w cx.txn.block_number - 256w)
    then Abort Revert_abort (revert_state (set_returndata [] u4)) else OK u4` by
   (simp[Abbr `j5`, step_inst_base_def, mk_inst_def, bool_to_word_def] >>
    IF_CASES_TAC >> simp[]) >>
 `u4.vs_allocas = s.vs_allocas /\ u6.vs_allocas = s.vs_allocas /\
  u6.vs_requests = u4.vs_requests` by
   simp[Abbr `u6`, Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, update_var_def] >>
 `!lo. allocas_from lo u4 = allocas_from lo s /\
        allocas_from lo u6 = allocas_from lo s` by simp[allocas_from_def] >>
 `!lo t. access_ok lo G4 func j6 t /\ taint_ok func tn4 j6 t` by
   (rpt gen_tac >>
    simp[access_ok_def, taint_ok_def, Abbr `j6`, mk_inst_def,
      source_memory_write_ranges_def, contextCodegenRelTheory.source_memory_read_ranges_def] >>
    conj_tac
    >- (Cases_on `arg` >> fs[op_prov_def, flookup_thm]) >>
    qpat_x_assum `op_taint tn4 arg = {}` mp_tac >>
    qpat_x_assum `op_taint tn4 (Var cur) = {}` mp_tac >>
    map_every (fn pat => qpat_x_assum pat kall_tac)
      [`compile_blockhash _ _ = _`, `!H. valid_horizon _ _ _ _ ==> _ /\ _ /\ _`] >>
    metis_tac[]) >>
 `!lo k. allocas_from lo (u4 with vs_inst_idx := k) = allocas_from lo s` by
   simp[allocas_from_def] >>
 `!lo t. access_ok lo G4 func j5 t /\ taint_ok func tn4 j5 t` by
   (simp[access_ok_def, taint_ok_def, Abbr `j5`, mk_inst_def,
      source_memory_write_ranges_def, contextCodegenRelTheory.source_memory_read_ranges_def] >>
    metis_tac[]) >>
 `!D lo k. allocas_from lo s ==>
   ptr_inst_ok D lo 0 ctx func G4 tn4 j5 (u4 with vs_inst_idx := k) /\
   ptr_inst_ok D lo 0 ctx func G4 tn4 j6 (u4 with vs_inst_idx := k)` by
   (rpt gen_tac >> strip_tac >>
    `j5.inst_opcode <> INVOKE /\ ~is_terminator j5.inst_opcode /\
     j6.inst_opcode <> INVOKE /\ ~is_terminator j6.inst_opcode` by
      simp[Abbr `j5`, Abbr `j6`, mk_inst_def, is_terminator_def] >>
    simp[ptr_inst_ok_def, step_inst_non_invoke, step_inst_inst_idx_indep,
      exec_result_map_def] >>
    Cases_on `word_lt (n2w n:bytes32) (n2w cx.txn.block_number - 256w)` >>
    simp[exec_result_map_def]) >>
 `~word_lt (n2w n:bytes32) (n2w cx.txn.block_number - 256w) ==>
   !D lo. allocas_from lo s ==>
    inst_seq_ptr D lo ctx func PG G tn [j1;j2;j3;j4;j5;j6] s G6 tn6` by
   (strip_tac >> map_every qx_gen_tac [`D0`,`lo0`] >> strip_tac >>
    `ptr_inst_ok D0 lo0 0 ctx func G tn j1 s` by metis_tac[] >>
    `~is_terminator j2.inst_opcode /\ ~is_terminator j3.inst_opcode /\
     ~is_terminator j4.inst_opcode /\ ~is_terminator j5.inst_opcode /\
     ~is_terminator j6.inst_opcode` by
      simp[Abbr `j2`, Abbr `j3`, Abbr `j4`, Abbr `j5`, Abbr `j6`,
        mk_inst_def, is_terminator_def] >>
    simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
      Abbr `G6`, Abbr `tn6`, Abbr `G4`, Abbr `G3`, Abbr `G2`, Abbr `G1`,
      Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`] >>
    metis_tac[]) >>
 `~word_lt (n2w n:bytes32) (n2w cx.txn.block_number - 256w) ==>
   !H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u6 with vs_inst_idx := s.vs_inst_idx + 6),G6,tn6)` by
   (strip_tac >> gen_tac >> strip_tac >>
    `allocas_from lo s` by
      (qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _ /\ _ /\ _` drule >>
       simp[ghost_inv_at_def]) >>
    `inst_seq_ptr (DF H) lo ctx func PG G tn [j1;j2;j3;j4;j5;j6] s G6 tn6` by metis_tac[] >>
    `isPREFIX [j1;j2;j3;j4;j5;j6] (DROP s.vs_inst_idx bb.bb_instructions)` by
      simp[IS_PREFIX_APPEND] >>
    `EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode) [j1;j2;j3;j4;j5;j6]` by
      simp[Abbr `j1`, Abbr `j2`, Abbr `j3`, Abbr `j4`, Abbr `j5`, Abbr `j6`,
        mk_inst_def, is_terminator_def] >>
    `run_inst_seq [j1;j2;j3;j4;j5;j6] s = OK u6` by simp[run_inst_seq_def] >>
    `run_inst_seq_mem_ok [j1;j2;j3;j4;j5;j6] s` by
      (irule run_inst_seq_mem_ok_every >>
       simp[Abbr `j1`, Abbr `j2`, Abbr `j3`, Abbr `j4`, Abbr `j5`, Abbr `j6`,
         unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
         contextCodegenRelTheory.source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
    drule_all run_inst_seq_gas_origin_ptr_path >>
    simp[Abbr `j1`, Abbr `j2`, Abbr `j3`, Abbr `j4`, Abbr `j5`, Abbr `j6`, mk_inst_def]) >>
 qabbrev_tac `j7 = mk_inst (sa.cs_next_id+6) ASSERT [Var recent] []` >>
 qabbrev_tac `v6 = u6 with vs_inst_idx := s.vs_inst_idx + 6` >>
 `get_instruction bb v6.vs_inst_idx = SOME j7` by
   (`s.vs_inst_idx + 6 < LENGTH bb.bb_instructions` by
      (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
       simp[LENGTH_DROP] >> decide_tac) >>
    `EL 6 (DROP s.vs_inst_idx bb.bb_instructions) = j7` by simp[Abbr `j7`] >>
    simp[Abbr `v6`, get_instruction_def] >> metis_tac[EL_DROP, ADD_COMM]) >>
 `eval_operand (Var recent) v6 = SOME (bool_to_word (n < cx.txn.block_number)) /\
  ~v6.vs_halted /\ v6.vs_current_bb = s.vs_current_bb /\
  v6.vs_allocas = s.vs_allocas /\ v6.vs_alloca_next = s.vs_alloca_next` by
   simp[Abbr `v6`, Abbr `u6`, Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
     eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE, ALL_DISTINCT] >>
 `op_taint tn6 (Var recent) = {} /\ op_prov G6 (Var recent) = NONE` by
   (simp[Abbr `tn6`, Abbr `G6`, Abbr `j6`, mk_inst_def, step_taint_def, step_prov_def,
      out_prov_def, out_taint_def, op_taint_def, op_prov_def,
      set_var_taint_def, set_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
    Cases_on `eval_operand arg u4` >> simp[]) >>
 `!D lo. allocas_from lo s ==> ptr_inst_ok D lo 0 ctx func G6 tn6 j7 v6` by
   (rpt gen_tac >> strip_tac >>
    simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, Abbr `j7`, mk_inst_def,
      source_memory_write_ranges_def, contextCodegenRelTheory.source_memory_read_ranges_def,
      allocas_from_def, step_inst_def, step_inst_base_def] >>
    IF_CASES_TAC >> simp[] >> fs[allocas_from_def]) >>
 `~word_lt (n2w n:bytes32) (n2w cx.txn.block_number - 256w) /\
  ~(n < cx.txn.block_number) ==>
   !H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort (revert_state (set_returndata [] v6)),G6,tn6)` by
   (strip_tac >> gen_tac >> strip_tac >>
    `allocas_from lo s` by
      (qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _ /\ _ /\ _` drule >>
       simp[ghost_inv_at_def]) >>
    `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (v6,G6,tn6) []
       (Abort Revert_abort (revert_state (set_returndata [] v6)),G6,tn6)` by
      (irule exit_inst_origin_ptr >> simp[exit_result_def] >> qexistsl [`bb`,`j7`] >>
       simp[Abbr `j7`, mk_inst_def, step_inst_def, step_inst_base_def,
         bool_to_word_def, exit_result_def, mem_safe_step_def,
         unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def,
         source_memory_write_ranges_def, contextCodegenRelTheory.source_memory_read_ranges_def,
         gasEventsTheory.gas_events_step_def, gasCountTheory.gas_count_step_def] >> metis_tac[]) >>
    `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v6,G6,tn6)` by metis_tac[] >>
    drule fragGasOriginPtrTheory.gas_origin_ptr_path_append >> simp[]) >>
 drule_all compile_blockhash_run >>
 `cx.txn.block_number < 2 ** 256` by fs[] >>
 `cx.txn.block_number MOD dimword (:256) = cx.txn.block_number` by
   fs[wordsTheory.dimword_def] >>
 simp[drop_fresh_def, wordsTheory.w2n_n2w, GSYM wordsTheory.dimword_def] >>
 simp[unop_result_def, evaluate_builtin_def, tx_env_ok_evaluate_block_hash] >>
 Cases_on `n < cx.txn.block_number /\ cx.txn.block_number <= n + 256` >>
 simp[]
 >- suspend "success" >>
 suspend "revert"
QED

Resume blockhash_full_suffix[success]:
 `cx.txn.block_number - 256 <= n` by decide_tac >>
 simp[] >> strip_tac >>
 qpat_x_assum `vars_ext_result _ _` mp_tac >>
 simp[vars_ext_result_def] >> strip_tac >>
 `s.vs_block_ctx.bc_blockhash n =
    EL (cx.txn.block_number - (n + 1)) cx.txn.block_hashes` by
   (fs[call_ctx_rel_def] >> drule tx_env_ok_hash_window >>
    disch_then (qspec_then `n` mp_tac) >> gvs[] >> decide_tac) >>
 `~word_lt (n2w n:bytes32) (n2w cx.txn.block_number - 256w)` by metis_tac[] >>
 qabbrev_tac `j8 = mk_inst (sa.cs_next_id+7) BLOCKHASH [arg] [out]` >>
 qabbrev_tac `u8 = update_var out (s.vs_block_ctx.bc_blockhash n) v6` >>
 qabbrev_tac `t8 = u8 with vs_inst_idx := s.vs_inst_idx + 8` >>
 qabbrev_tac `G8 = step_prov PG G6 j8 u8` >>
 qabbrev_tac `tn8 = step_taint j8 v6 u8 tn6` >>
 `step_inst_base j7 v6 = OK v6` by
   simp[Abbr `j7`, mk_inst_def, step_inst_base_def, bool_to_word_def] >>
 `step_prov PG G6 j7 v6 = G6 /\ step_taint j7 v6 v6 tn6 = tn6` by
   (simp[Abbr `j7`, mk_inst_def, step_prov_def, step_taint_def,
     mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
     step_writes_def, new_site_bytes_def, source_memory_write_ranges_def,
     range_bytes_def, written_taint_def, set_var_taint_def, set_prov_def] >>
    simp[taint_component_equality, DRESTRICT_UNIV,
      FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
 `eval_operand arg v6 = SOME (n2w n) /\
  v6.vs_block_ctx = s.vs_block_ctx` by
   (Cases_on `arg` >>
    simp[Abbr `v6`, Abbr `u6`, Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
    fs[eval_operand_def, lookup_var_def]) >>
 `step_inst_base j8 v6 = OK u8` by
   simp[Abbr `j8`, Abbr `u8`, mk_inst_def, step_inst_base_def, exec_read1_def,
     wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
 `u8.vs_allocas = s.vs_allocas /\ u8.vs_requests = v6.vs_requests /\
  ~u8.vs_halted` by simp[Abbr `u8`, update_var_def] >>
 `op_taint tn6 arg = {} /\ op_prov G6 arg = NONE` by
   (Cases_on `arg` >>
    fs[Abbr `tn6`, Abbr `G6`, Abbr `j6`, mk_inst_def,
      step_taint_def, step_prov_def, out_prov_def, out_taint_def,
      set_var_taint_def, set_prov_def, op_taint_def, op_prov_def,
      FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
 `j8.inst_opcode <> INVOKE /\ ~is_terminator j8.inst_opcode` by
   simp[Abbr `j8`, mk_inst_def, is_terminator_def] >>
 `!D lo k. allocas_from lo s ==>
    ptr_inst_ok D lo 0 ctx func G6 tn6 j8 (v6 with vs_inst_idx := k)` by
   (qx_gen_tac `D1` >> qx_gen_tac `lo1` >> qx_gen_tac `k` >> strip_tac >>
    `allocas_from lo1 (v6 with vs_inst_idx := k) /\ allocas_from lo1 u8` by
      (qpat_x_assum `allocas_from lo1 s` mp_tac >> simp[allocas_from_def]) >>
    simp[ptr_inst_ok_def, step_inst_non_invoke, step_inst_inst_idx_indep,
      exec_result_map_def] >>
    simp[access_ok_def, taint_ok_def, Abbr `j8`, mk_inst_def,
      contextCodegenRelTheory.source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
 `!D lo1. allocas_from lo1 s ==> inst_seq_ptr D lo1 ctx func PG G6 tn6
    [j7;j8] v6 G8 tn8` by
   (rpt gen_tac >> strip_tac >>
    `ptr_inst_ok D lo1 0 ctx func G6 tn6 j7 v6 /\
     ptr_inst_ok D lo1 0 ctx func G6 tn6 j8 (v6 with vs_inst_idx := SUC v6.vs_inst_idx)` by
      metis_tac[] >>
    simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
      Abbr `G8`, Abbr `tn8`] >> metis_tac[]) >>
 `!H. valid_horizon cx st0 H mid.storage_trace ==>
   gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t8,G8,tn8)` by
   (gen_tac >> strip_tac >>
    `allocas_from lo s` by
      (qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _ /\ _ /\ _` drule >>
       simp[ghost_inv_at_def]) >>
    `inst_seq_ptr (DF H) lo ctx func PG G6 tn6 [j7;j8] v6 G8 tn8` by metis_tac[] >>
    `isPREFIX [j7;j8] (DROP v6.vs_inst_idx bb.bb_instructions)` by
      (qspecl_then [`6`,`s.vs_inst_idx`,`bb.bb_instructions`] mp_tac DROP_DROP_T >>
       simp[] >> strip_tac >>
       `DROP v6.vs_inst_idx bb.bb_instructions = [j7;j8] ++ rest` by
         (simp[Abbr `v6`] >> metis_tac[ADD_COMM]) >>
       qpat_x_assum `DROP v6.vs_inst_idx _ = _` (fn th => pure_rewrite_tac[th]) >>
       simp[NoAsms, IS_PREFIX_APPEND]) >>
    `EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode) [j7;j8]` by
      simp[Abbr `j7`, Abbr `j8`, mk_inst_def, is_terminator_def] >>
    `run_inst_seq [j7;j8] v6 = OK u8` by simp[run_inst_seq_def] >>
    `run_inst_seq_mem_ok [j7;j8] v6` by
      (irule run_inst_seq_mem_ok_every >>
       simp[Abbr `j7`, Abbr `j8`, mk_inst_def,
         unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def,
         contextCodegenRelTheory.source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
    `lookup_block v6.vs_current_bb func.fn_blocks = SOME bb` by
      metis_tac[Abbr `v6`] >>
    `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (v6,G6,tn6) [] (OK t8,G8,tn8)` by
      (drule_all run_inst_seq_gas_origin_ptr_path >>
       simp[Abbr `j7`, Abbr `j8`, mk_inst_def, Abbr `t8`, Abbr `v6`]) >>
    `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v6,G6,tn6)` by metis_tac[] >>
    drule fragGasOriginPtrTheory.gas_origin_ptr_path_append >> simp[]) >>
 `!p. not_fresh_at sa p ==> lookup_var p t8 = lookup_var p s /\
   FLOOKUP G8 p = FLOOKUP G p /\ op_taint tn8 (Var p) = op_taint tn (Var p)` by
   (gen_tac >> strip_tac >>
    `p <> recent /\ p <> out` by metis_tac[] >>
    simp[Abbr `t8`, Abbr `u8`, Abbr `v6`, Abbr `u6`, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE] >>
    simp[Abbr `G8`, Abbr `tn8`, Abbr `G6`, Abbr `tn6`, Abbr `j8`, Abbr `j6`,
      step_prov_other_output, step_taint_other_output, mk_inst_def] >>
    metis_tac[lookup_var_def]) >>
 `op_taint tn8 (Var out) = {} /\ op_prov G8 (Var out) = NONE` by
   simp[Abbr `G8`, Abbr `tn8`, Abbr `j8`, mk_inst_def, step_prov_def,
     step_taint_def, out_prov_def, out_taint_def, set_prov_def, set_var_taint_def,
     op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
 `tn8.t_mem = tn.t_mem /\ tn8.t_stor = tn.t_stor /\
  tn8.t_trans = tn.t_trans /\ tn8.t_imm = tn.t_imm` by
   (simp[Abbr `tn8`, Abbr `j8`, step_taint_def, mem_taint_def,
      store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
      step_writes_def, new_site_bytes_def, source_memory_write_ranges_def,
      range_bytes_def, written_taint_def] >>
    simp[Abbr `tn6`, Abbr `j6`, step_taint_def, mem_taint_def,
      store_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def,
      step_writes_def, new_site_bytes_def, source_memory_write_ranges_def,
      range_bytes_def, written_taint_def] >>
    simp[Abbr `u8`, Abbr `v6`, Abbr `u6`, Abbr `u4`, Abbr `u3`, Abbr `u2`,
      Abbr `u1`, update_var_def] >>
    simp[FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
 `t8 = s with <|vs_vars := t8.vs_vars; vs_inst_idx := s.vs_inst_idx + 8|>` by
   simp[Abbr `t8`, Abbr `u8`, Abbr `v6`, Abbr `u6`, Abbr `u4`, Abbr `u3`,
     Abbr `u2`, Abbr `u1`, update_var_def] >>
 `t8.vs_memory = s.vs_memory /\ t8.vs_allocas = s.vs_allocas /\
  t8.vs_alloca_next = s.vs_alloca_next /\ t8.vs_call_ctx = s.vs_call_ctx /\
  t8.vs_accounts = s.vs_accounts /\ t8.vs_transient = s.vs_transient /\
  t8.vs_immutables = s.vs_immutables` by
   simp[Abbr `t8`, Abbr `u8`, Abbr `v6`, Abbr `u6`, Abbr `u4`, Abbr `u3`,
     Abbr `u2`, Abbr `u1`, update_var_def] >>
 qexistsl [`OK t8`,`G8`,`tn8`] >>
 gen_tac >> strip_tac >>
 `stmt_state_rel H ctx func cenv cx mid s /\
  ghost_inv_at (DF H) lo d cenv cx mid G tn s` by metis_tac[] >>
 `ghost_inv_at (DF H) lo d cenv cx mid G8 tn8 t8` by
   (irule ghost_inv_at_exterior_frame >> metis_tac[]) >>
 `stmt_state_rel H ctx func cenv cx mid (s with vs_vars := t8.vs_vars)` by
   (irule stmt_state_rel_vars_frame >> simp[] >>
    qpat_x_assum `local_ptrs_reserved cenv sa` mp_tac >>
    simp[local_ptrs_reserved_def] >> rpt strip_tac >>
    `!p. not_fresh_at sa p ==> lookup_var p t8 = lookup_var p s` by metis_tac[] >>
    simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
 `stmt_state_rel H ctx func cenv cx mid t8` by
   (`t8 = (s with vs_vars := t8.vs_vars) with vs_inst_idx := s.vs_inst_idx + 8` by
      (qpat_assum `t8 = _` mp_tac >> simp[NoAsms]) >>
    metis_tac[stmt_state_rel_inst_idx]) >>
 simp[] >>
 `~t8.vs_halted /\ t8.vs_current_bb = sa.cs_current_bb /\
  t8.vs_inst_idx = LENGTH sa.cs_current_insts + 8` by
    simp[Abbr `t8`, Abbr `u8`, update_var_def, Abbr `v6`, Abbr `u6`,
      Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`] >>
 simp[] >> conj_tac
 >- (simp[loweringPostsTheory.expr_val_rel_def, Abbr `t8`, Abbr `u8`, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     simp[is_word_type_def, evaluate_type_def, typed_val_to_w256_def,
       val_to_w256_def, PAD_RIGHT, length_word_to_bytes_be,
       word_of_bytes_be_to_bytes]) >>
 `alloca_inv s` by metis_tac[stmt_state_rel_def] >>
 `run_inst_seq [j1;j2;j3;j4;j5;j6;j7;j8] s =
    OK (update_var out (s.vs_block_ctx.bc_blockhash n) u6)` by
   (`step_inst_base j7 u6 = OK u6` by
      simp[Abbr `j7`, Abbr `u6`, mk_inst_def, step_inst_base_def,
        eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
        bool_to_word_def] >>
    `step_inst_base j8 u6 = OK (update_var out (s.vs_block_ctx.bc_blockhash n) u6)` by
      (`eval_operand arg u6 = SOME (n2w n) /\ u6.vs_block_ctx = s.vs_block_ctx` by
        (conj_tac
         >- (qpat_x_assum `eval_operand arg v6 = _` mp_tac >>
             simp[Abbr `v6`, eval_op_inst_idx]) >>
         qpat_x_assum `v6.vs_block_ctx = _` mp_tac >> simp[Abbr `v6`]) >>
       simp[Abbr `j8`, mk_inst_def, step_inst_base_def, exec_read1_def,
         wordsTheory.w2n_n2w, wordsTheory.dimword_def]) >>
    simp[run_inst_seq_def, Abbr `u8`, Abbr `v6`, update_var_def]) >>
 `EVERY (\j. ~is_terminator j.inst_opcode) [j1;j2;j3;j4;j5;j6;j7;j8]` by
   (qpat_x_assum `EVERY _ (emitted_insts sa sb)` mp_tac >> simp[]) >>
 `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
 `DROP s.vs_inst_idx bb.bb_instructions = [j1;j2;j3;j4;j5;j6;j7;j8] ++ rest` by
   metis_tac[] >>
 drule_all alloca_history_run_inst_seq >>
 simp[Abbr `t8`, Abbr `u8`, Abbr `v6`, update_var_def]
QED

Resume blockhash_full_suffix[revert]:
 `n MOD dimword (:256) = n` by fs[wordsTheory.dimword_def] >>
 `~(cx.txn.block_number - 256 <= n /\ n < cx.txn.block_number)` by decide_tac >>
 simp[] >> strip_tac >>
 Cases_on `word_lt (n2w n:bytes32) (n2w cx.txn.block_number - 256w)`
 >- (qexistsl [`Abort Revert_abort (revert_state (set_returndata [] v4))`,`G4`,`tn4`] >>
     simp[expr_exit_def] >> metis_tac[]) >>
 `~(n < cx.txn.block_number)` by metis_tac[] >>
 qexistsl [`Abort Revert_abort (revert_state (set_returndata [] v6))`,`G6`,`tn6`] >>
 simp[expr_exit_def] >> metis_tac[]
QED

Finalise blockhash_full_suffix
