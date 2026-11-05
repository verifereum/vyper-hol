(* Actual emitted code for the allocation-free calldata word decoder. *)
Theory calldataWordPtr
Ancestors calldataClampPtr calldataDecodePtr abiDecoderClampedWord abiDecoderContract abiDecoderClamp
  abiEncoder compileEnv emitHelper exprLoweringProps fragExec
  venomInst list arithmetic words bodyPtrDefs decoderGhostFramePtr
  ptrDiscipline ptrSafeRun venomState venomExecSemantics entryDispatchPtr
  fragExecPtr ghostPcTransportPtr finite_map pred_set codegenRel instIdxIndep ptrSafetyTransport

Theorem calldata_unclamped_word_instructions:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w)
    (DecPrimWord NoClamp) sa = ((),sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id CALLDATALOAD [src]
       ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id + 1) MSTORE
       [Var p; Var ("%" ++ toString sa.cs_next_var)] []] /\
  sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 2
Proof
  simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, APPEND_ASSOC, DROP_PREFIX]
QED

Theorem calldata_unclamped_word_prefix_framed:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w)
    (DecPrimWord NoClamp) sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s 32 /\
  op_taint tn src = {} /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' 32 /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    mem_word_at (w2n dw) s'.vs_memory = abi_decode_load CALLDATALOAD sw s /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    mem_word_at (w2n dw) t.vs_memory = abi_decode_load CALLDATALOAD sw s` by
    (drule abi_decoder_clamped_word_sequence >>
     disch_then (qspecl_then [`s`, `sw`, `w2n dw`] mp_tac) >>
     simp[abi_decode_source_opcode_def, abi_decoder_clamp_valid_def, w2n_lt] >>
     metis_tac[]) >>
  drule calldata_unclamped_word_instructions >> strip_tac >>
  qabbrev_tac `v = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `i0 = mk_inst sa.cs_next_id CALLDATALOAD [src] [v]` >>
  qabbrev_tac `i1 = mk_inst (sa.cs_next_id + 1) MSTORE [Var p;Var v] []` >>
  `emitted_insts sa sb = [i0;i1]` by simp[Abbr `i0`, Abbr `i1`, Abbr `v`] >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  rename1 `step_inst_base i0 s = OK s1` >>
  `p <> v /\ src <> Var v` by
    (qpat_x_assum `fresh_vars_wrt sa s` mp_tac >>
     simp[fresh_vars_wrt_def] >>
     disch_then (qspec_then `sa.cs_next_var` mp_tac) >>
     gvs[Abbr `v`, eval_operand_def, lookup_var_def, FLOOKUP_DEF] >>
     strip_tac >> Cases_on `src` >>
     gvs[eval_operand_def, lookup_var_def, FLOOKUP_DEF] >> metis_tac[]) >>
  `s1 = update_var v (abi_decode_load CALLDATALOAD sw s) s` by
    (qpat_x_assum `step_inst_base i0 s = OK s1` mp_tac >>
     simp[Abbr `i0`, step_inst_base_def, exec_read1_def, abi_decode_load_def, abi_decode_source_def]) >>
  `eval_operand (Var p) s1 = SOME dw /\ eval_operand src s1 = SOME sw` by
    (simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     Cases_on `src` >> gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qabbrev_tac `G1 = step_prov PG G i0 s1` >>
  qabbrev_tac `tn1 = step_taint i0 s s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 t` >>
  qabbrev_tac `tn2 = step_taint i1 s1 t tn1` >>
  `ptr_covers G1 tn1 p s1 32` by
    (simp[Abbr `G1`, Abbr `tn1`] >> irule ptr_covers_step_frame >>
     simp[Abbr `i0`, mk_inst_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `op_taint tn1 (Var v) = {}` by
    (simp[Abbr `tn1`, Abbr `i0`] >> irule dispatch_scalar_output_clean >> simp[]) >>
  `t = mstore (w2n dw) (abi_decode_load CALLDATALOAD sw s) s1` by
    (qpat_x_assum `step_inst_base i1 s1 = OK t` mp_tac >>
     fs[Abbr `i1`, step_inst_base_def, exec_write2_def, eval_operand_def,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers G2 tn2 p t 32` by
    (simp[Abbr `G2`, Abbr `tn2`] >> irule ptr_covers_step_frame >>
     simp_tac (srw_ss()) [Abbr `i1`, mk_inst_def] >>
     qpat_x_assum `t = mstore _ _ _` SUBST1_TAC >>
     simp_tac (srw_ss()) [mstore_def, lookup_var_def] >> metis_tac[]) >>
  `!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tn2.t_mem` by
    (gen_tac >> strip_tac >> simp[Abbr `tn2`, Abbr `i1`] >>
     irule mstore_word_clean >> fs[eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `(!x. not_fresh_at sa x ==> x <> v)` by
    (simp[not_fresh_at_def, Abbr `v`] >> metis_tac[LESS_EQ_REFL]) >>
  `(!x. not_fresh_at sa x ==> FLOOKUP G2 x = FLOOKUP G x /\
      op_taint tn2 (Var x) = op_taint tn (Var x))` by
    (rpt strip_tac >> simp[Abbr `G2`, Abbr `tn2`, Abbr `G1`, Abbr `tn1`,
       step_prov_other_output, step_taint_other_output, Abbr `i0`, Abbr `i1`, mk_inst_def]) >>
  `tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm` by
    simp[Abbr `tn2`, Abbr `tn1`, Abbr `i0`, Abbr `i1`,
         step_taint_nonmemory_frame, mk_inst_def] >>
  `new_site_bytes s s1 = {} /\ new_site_bytes s1 t = {}` by
    (simp[update_var_def, mstore_def, new_site_bytes_def, EXTENSION,
          FLOOKUP_DEF] >> metis_tac[]) >>
  `written_taint tn i0 s = {} /\ written_taint tn1 i1 s1 = {}` by
    (Cases_on `eval_operand (Var p) s1` >>
     simp_tac (srw_ss()) [Abbr `i0`, Abbr `i1`, written_taint_def, mk_inst_def] >>
     asm_rewrite_tac[] >> simp[]) >>
  `tn1.t_mem SUBSET tn.t_mem /\ tn2.t_mem SUBSET tn1.t_mem` by
    (conj_tac
     >- (simp_tac (srw_ss()) [Abbr `tn1`] >>
         irule (SRULE [] (Q.INST [`R` |-> `{}:num set`] step_taint_memory_bound)) >>
         simp_tac (srw_ss()) [] >> metis_tac[]) >>
     simp_tac (srw_ss()) [Abbr `tn2`] >>
     irule (SRULE [] (Q.INST [`R` |-> `{}:num set`] step_taint_memory_bound)) >>
     simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `tn2.t_mem SUBSET tn.t_mem` by metis_tac[SUBSET_TRANS] >>
  `t.vs_inst_idx = s.vs_inst_idx /\ ~t.vs_halted /\
   t.vs_current_bb = s.vs_current_bb /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_vars = s1.vs_vars` by
    simp[mstore_def, update_var_def] >>
  `eval_operand (Var p) t = SOME dw /\ eval_operand src t = SOME sw` by
    (Cases_on `src` >> gvs[eval_operand_def, lookup_var_def,
       mstore_def, update_var_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `G2`, `tn2`] >>
  `t with vs_inst_idx := LENGTH sa.cs_current_insts = t` by
    simp[venom_state_component_equality] >>
  `ptr_covers G2 tn2 p (t with vs_inst_idx := LENGTH sb.cs_current_insts) 32` by
    (qpat_x_assum `ptr_covers G2 tn2 p t 32` mp_tac >>
     simp_tac (srw_ss()) [ptr_covers_def, lookup_var_def]) >>
  simp[eval_operand_def, lookup_var_def] >> conj_tac
  >- metis_tac[] >>
  suspend "continuation"
QED

Resume calldata_unclamped_word_prefix_framed[continuation]:
  conj_tac
  >- fs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- metis_tac[] >>
  strip_tac >>
  qpat_x_assum `!i. _ ==> i NOTIN _` kall_tac >>
  qpat_x_assum `!x. not_fresh_at _ _ ==> _ /\ _` kall_tac >>
  qpat_x_assum `mem_word_at _ _ = _` kall_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` kall_tac >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
     !k. k < LENGTH [i0;i1] ==> get_instruction bb (LENGTH sa.cs_current_insts + k) =
       SOME (EL k [i0;i1])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> simp[]) >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_allocas = s.vs_allocas /\
   s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_requests = s.vs_requests /\
   t.vs_requests = s1.vs_requests` by simp[update_var_def, mstore_def] >>
  `!fuel. step_inst fuel ctx i1
    (s1 with vs_inst_idx := LENGTH sa.cs_current_insts + 1) =
    OK (t with vs_inst_idx := LENGTH sa.cs_current_insts + 1)` by
    (gen_tac >> simp_tac (srw_ss()) [Abbr `i1`, step_inst_non_invoke,
       mk_inst_def, step_inst_inst_idx_indep, is_terminator_def] >>
     qpat_x_assum `step_inst_base i1 s1 = OK t` mp_tac >>
     simp_tac (srw_ss()) [mk_inst_def] >>
     disch_then SUBST1_TAC >> simp_tac (srw_ss()) [exec_result_map_def]) >>
  `get_instruction bb (LENGTH sa.cs_current_insts + 1) = SOME i1` by
    (qpat_x_assum `!k. k < LENGTH _ ==> _` (qspec_then `1` mp_tac) >> simp[]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G1 tn1
    (s1 with vs_inst_idx := LENGTH sa.cs_current_insts + 1)` by
    (gen_tac >>
     irule ptr_safe_run_scalar_continuation >>
     qexistsl_tac [`bb`, `i1`, `t with vs_inst_idx := LENGTH sa.cs_current_insts + 1`] >>
     asm_simp_tac (srw_ss()) [Abbr `i1`, mk_inst_def, is_terminator_def,
       step_prov_inst_idx, step_taint_inst_idx] >>
     conj_tac >- simp[ADD1] >>
     simp_tac (srw_ss()) [ptr_safe_defs] >>
     irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (qpat_x_assum `allocas_from lo s` mp_tac >>
       simp_tac (srw_ss()) [allocas_from_def, update_var_def]) >>
     qexists_tac `0` >> simp_tac (srw_ss()) [] >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mstore) >>
     asm_rewrite_tac[] >>
     qpat_x_assum `ptr_covers G1 tn1 p s1 32` mp_tac >>
     simp_tac (srw_ss()) [ptr_covers_def, lookup_var_def, update_var_def] >>
     gvs[update_var_def]) >>
  `!fuel. step_inst fuel ctx i0 s = OK s1` by
    (gen_tac >> simp_tac (srw_ss()) [Abbr `i0`, step_inst_non_invoke, mk_inst_def] >>
     qpat_x_assum `step_inst_base _ s = OK s1` mp_tac >>
     simp_tac (srw_ss()) [mk_inst_def]) >>
  `get_instruction bb (LENGTH sa.cs_current_insts) = SOME i0` by
    (qpat_x_assum `!k. k < LENGTH _ ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  gen_tac >> irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`, `i0`, `s1`] >>
  asm_simp_tac (srw_ss()) [Abbr `i0`, mk_inst_def, is_terminator_def] >>
  conj_tac
  >- (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G1 tn1 _` mp_tac >>
      simp[Abbr `G1`, Abbr `tn1`, mk_inst_def, ADD1]) >>
  irule (SRULE [mk_inst_def] ptr_safe_dispatch_scalar_step) >>
  asm_simp_tac (srw_ss()) [] >> qexists_tac `s1` >>
  asm_simp_tac (srw_ss()) [mk_inst_def] >>
  qpat_x_assum `!fuel. step_inst _ _ _ s = OK s1` (qspec_then `fuel` mp_tac) >>
  simp[mk_inst_def]
QED

Finalise calldata_unclamped_word_prefix_framed
