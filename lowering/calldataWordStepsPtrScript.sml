(* Pointer ghost boundaries for primitive calldata word instructions. *)
Theory calldataWordStepsPtr
Ancestors ptrSafetyTransport valueEncodingProps calldataClampPtr calldataDecodePtr abiDecoderContract
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps fragExec
  venomInst list arithmetic words bodyPtrDefs decoderGhostFramePtr
  ptrDiscipline ptrSafeRun venomState venomExecSemantics entryDispatchPtr
  fragExecPtr ghostPcTransportPtr finite_map pred_set codegenRel instIdxIndep

Theorem calldata_load_prefix_framed:
  emit_op CALLDATALOAD [src] sa = (v,sb) /\
  eval_operand src s = SOME sw /\ fresh_vars_wrt sa s /\
  op_taint tn src = {} /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ fresh_vars_wrt sb t /\
    eval_operand v t = SOME (abi_decode_load CALLDATALOAD sw s) /\
    op_taint u v = {} /\ op_prov H v = NONE /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!a w. eval_operand a s = SOME w ==> eval_operand a t = SOME w) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK t` >>
  qabbrev_tac `out = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id CALLDATALOAD [src] [out]` >>
  `emitted_insts sa sb = [inst]` by simp[Abbr `inst`, Abbr `out`] >>
  `step_inst_base inst s = OK t` by (fs[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]) >>
  `t = update_var out (abi_decode_load CALLDATALOAD sw s) s` by
    (qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
     simp[Abbr `inst`, step_inst_base_def, exec_read1_def,
       abi_decode_load_def, abi_decode_source_def]) >>
  qabbrev_tac `H = step_prov PG G inst t` >>
  qabbrev_tac `u = step_taint inst s t tn` >>
  `v = Var out` by simp[Abbr `out`] >>
  `op_taint u v = {}` by
    (simp[Abbr `u`, Abbr `inst`] >>
     irule dispatch_scalar_output_clean >> simp[]) >>
  `op_prov H v = NONE` by
    simp[Abbr `H`, Abbr `inst`, op_prov_def, step_prov_def,
      out_prov_def, set_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  `u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
   u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm` by
    (simp[Abbr `u`, Abbr `inst`, step_taint_def, mem_taint_def,
      new_site_bytes_def, step_writes_def, written_taint_def,
      store_taint_def, imm_taint_def, adopt_reset_def, update_var_def,
      mk_inst_def, EXTENSION, FLOOKUP_DEF, source_memory_write_ranges_def,
      range_bytes_def, SF CONJ_ss]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint u (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> out` by (fs[not_fresh_at_def, Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
     simp[Abbr `H`, Abbr `u`, Abbr `inst`, mk_inst_def,
       step_prov_other_output, step_taint_other_output]) >>
  suspend "endpoint"
QED

Resume calldata_load_prefix_framed[endpoint]:
  `t.vs_inst_idx = s.vs_inst_idx` by simp[update_var_def] >>
  `t with vs_inst_idx := s.vs_inst_idx = t` by
    simp[venom_state_component_equality] >>
  `((!fuel. ptr_safe_run D lo fuel ctx fn PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
    !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)` by
    suspend "continuation" >>
  `sa.cs_current_bb = sb.cs_current_bb` by fs[same_blocks_def] >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    simp[update_var_def, same_blocks_def] >>
  qpat_x_assum `t = update_var _ _ s` kall_tac >>
  `fresh_vars_wrt sb (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_x_assum `fresh_vars_wrt sb t` mp_tac >> simp[fresh_vars_wrt_def]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `H`, `u`] >>
  simp[eval_op_inst_idx] >>
  simp[venom_state_component_equality]
QED

Resume calldata_load_prefix_framed[continuation]:
  strip_tac >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    !k. k < LENGTH [inst] ==> get_instruction bb (LENGTH sa.cs_current_insts + k) =
      SOME (EL k [inst])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >>
     fs[same_blocks_def, Abbr `inst`, Abbr `out`]) >>
  `!fuel. step_inst fuel ctx inst s = OK t` by
    (gen_tac >> simp_tac (srw_ss()) [Abbr `inst`, step_inst_non_invoke, mk_inst_def] >>
     qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
     simp_tac (srw_ss()) [mk_inst_def]) >>
  `get_instruction bb (LENGTH sa.cs_current_insts) = SOME inst` by
    (qpat_x_assum `!k. k < LENGTH _ ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_requests = s.vs_requests` by
    simp[update_var_def] >>
  qpat_x_assum `t = update_var _ _ s` kall_tac >>
  gen_tac >> irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`, `inst`, `t`] >>
  asm_simp_tac (srw_ss()) [Abbr `inst`, mk_inst_def, is_terminator_def] >>
  conj_tac
  >- (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ H u _` mp_tac >>
      simp[Abbr `H`, Abbr `u`, mk_inst_def, ADD1]) >>
  irule (SRULE [mk_inst_def] ptr_safe_dispatch_scalar_step) >>
  asm_simp_tac (srw_ss()) [] >> qexists_tac `t` >>
  asm_simp_tac (srw_ss()) [mk_inst_def] >>
  qpat_x_assum `!fuel. step_inst _ _ _ s = OK t` (qspec_then `fuel` mp_tac) >>
  simp[mk_inst_def]
QED

Finalise calldata_load_prefix_framed

Theorem clean_mstore_prefix_framed:
  emit_void MSTORE [Var p;v] sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand v s = SOME w /\
  ptr_covers G tn p s 32 /\ op_taint tn v = {} /\ fresh_vars_wrt sa s /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ fresh_vars_wrt sb t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!a z. eval_operand a s = SOME z ==> eval_operand a t = SOME z) /\
    ptr_covers H u p t 32 /\ mem_word_at (w2n dw) t.vs_memory = w /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN u.t_mem) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MSTORE [Var p;v] []` >>
  qabbrev_tac `t = mstore (w2n dw) w s` >>
  `step_inst_base inst s = OK t` by
    simp[Abbr `inst`, Abbr `t`, step_inst_base_def, exec_write2_def] >>
  `emitted_insts sa sb = [inst]` by simp[Abbr `inst`] >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by
    simp[run_inst_seq_def] >>
  qabbrev_tac `H = step_prov PG G inst t` >>
  qabbrev_tac `u = step_taint inst s t tn` >>
  `!x. FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)` by
    simp[Abbr `H`, Abbr `u`, Abbr `inst`, mk_inst_def,
      step_prov_other_output, step_taint_other_output] >>
  `ptr_covers H u p t 32` by
    (simp[Abbr `H`, Abbr `u`] >> irule ptr_covers_step_frame >>
     simp[Abbr `inst`, mk_inst_def, Abbr `t`, mstore_def, lookup_var_def]) >>
  `!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN u.t_mem` by
    (gen_tac >> strip_tac >> simp[Abbr `u`, Abbr `inst`] >>
     irule mstore_word_clean >> fs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  `u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm` by
    simp[Abbr `u`, Abbr `inst`, step_taint_nonmemory_frame, mk_inst_def] >>
  `new_site_bytes s t = {}` by
    (simp[Abbr `t`, mstore_def, new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >>
     metis_tac[]) >>
  `written_taint tn inst s = {}` by
    simp[Abbr `inst`, written_taint_def, mk_inst_def] >>
  `u.t_mem SUBSET tn.t_mem` by
    (simp_tac (srw_ss()) [Abbr `u`] >>
     irule (SRULE [] (Q.INST [`R` |-> `{}:num set`] step_taint_memory_bound)) >>
     simp[]) >>
  suspend "store_endpoint"
QED

Resume clean_mstore_prefix_framed[store_endpoint]:
  `t.vs_inst_idx = s.vs_inst_idx /\ ~t.vs_halted /\
   t.vs_current_bb = s.vs_current_bb /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_vars = s.vs_vars /\
   t.vs_requests = s.vs_requests /\ t.vs_labels = s.vs_labels` by
    simp[Abbr `t`, mstore_def] >>
  `mem_word_at (w2n dw) t.vs_memory = w` by
    simp[Abbr `t`, mstore_mem_word_at_same] >>
  `((!fuel. ptr_safe_run D lo fuel ctx fn PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
    !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)` by
    suspend "store_continuation" >>
  qpat_x_assum `Abbrev (t = _)` kall_tac >>
  `t with vs_inst_idx := s.vs_inst_idx = t` by
    simp[venom_state_component_equality] >>
  `sa.cs_current_bb = sb.cs_current_bb` by fs[same_blocks_def] >>
  `fresh_vars_wrt sb (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_x_assum `fresh_vars_wrt sa s` mp_tac >> simp[fresh_vars_wrt_def]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `H`, `u`] >>
  simp[eval_op_inst_idx, ptr_covers_def, lookup_var_def, eval_operand_def] >>
  conj_tac >- simp[venom_state_component_equality] >>
  Cases_on `a` >> simp[eval_operand_def, lookup_var_def]
QED

Resume clean_mstore_prefix_framed[store_continuation]:
  strip_tac >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    !k. k < LENGTH [inst] ==> get_instruction bb (LENGTH sa.cs_current_insts + k) =
      SOME (EL k [inst])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> fs[same_blocks_def]) >>
  `!fuel. step_inst fuel ctx inst s = OK t` by
    (gen_tac >> simp_tac (srw_ss()) [Abbr `inst`, step_inst_non_invoke, mk_inst_def] >>
     qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
     simp_tac (srw_ss()) [mk_inst_def]) >>
  `get_instruction bb (LENGTH sa.cs_current_insts) = SOME inst` by
    (qpat_x_assum `!k. k < LENGTH _ ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `Abbrev (t = _)` kall_tac >>
  gen_tac >> irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`, `inst`, `t`] >>
  asm_simp_tac (srw_ss()) [Abbr `inst`, mk_inst_def, is_terminator_def] >>
  conj_tac
  >- (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ H u _` mp_tac >>
      simp[Abbr `H`, Abbr `u`, mk_inst_def, ADD1]) >>
  simp_tac (srw_ss()) [ptr_safe_defs] >>
  irule ptr_inst_ok_lower_bound_transport >>
  conj_tac >- simp[] >> qexists_tac `0` >> simp[] >>
  irule (SRULE [mk_inst_def] ptr_inst_ok_mstore) >>
  fs[eval_operand_def, lookup_var_def]
QED

Finalise clean_mstore_prefix_framed
