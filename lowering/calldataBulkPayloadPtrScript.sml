(* Ghost frame for the payload-copy instruction; independent of the ABI type. *)
Theory calldataBulkPayloadPtr
Ancestors calldataDecodePtr decoderRawEndpointPtr calldataBulkLive
  bodyPtrDefs ptrDiscipline venomInst venomState finite_map pred_set
  decoderGhostFramePtr emitHelperProps fragExec venomExecSemantics
  codegenRel contextCodegenRel ptrSafeRun compileEnv emitHelper list arithmetic
  exprLoweringProps abiDecoderBulk words abiDecoderComposition decoderArraySetupPtr
  instIdxIndep

(* The calldata address step: base Lit 0w adds no instruction. *)
val calldata_pos_addr = prove(
  ``compile_abi_dec_addr (Lit 0w) pos st = (pos,st)``,
  simp[abiEncoderTheory.compile_abi_dec_addr_def, compileEnvTheory.comp_return_def]);

Theorem calldatacopy_ghost_frame:
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  eval_operand n s = SOME nw /\
  t = write_memory_with_expansion (w2n dw)
    (TAKE (w2n nw)
      (DROP (w2n sw) s.vs_call_ctx.cc_calldata ++ REPLICATE (w2n nw) 0w)) s ==>
  (!root cap. ptr_covers G tn root s cap ==>
    ptr_covers (step_prov PG G (mk_inst id CALLDATACOPY [dst;src;n] []) t)
      (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn) root t cap) /\
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn).t_mem
    SUBSET tn.t_mem /\
  (!i. w2n dw <= i /\ i < w2n dw + w2n nw ==>
    i NOTIN (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn).t_mem) /\
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn).t_imm = tn.t_imm /\
  (!x. lookup_var x t = lookup_var x s /\
    FLOOKUP (step_prov PG G (mk_inst id CALLDATACOPY [dst;src;n] []) t) x = FLOOKUP G x /\
    op_taint (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s t tn) (Var x) =
      op_taint tn (Var x)) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[ptr_covers_def, step_prov_def, step_taint_def, set_prov_def,
        set_var_taint_def, mk_inst_def, op_taint_def, FLOOKUP_DRESTRICT, lookup_var_def,
        write_memory_with_expansion_def, write_memory_def, expand_memory_def])
  >- (`new_site_bytes s t = {}` by
        (gvs[new_site_bytes_def, write_memory_with_expansion_def,
          write_memory_def, expand_memory_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
      `written_taint tn (mk_inst id CALLDATACOPY [dst;src;n] []) s = {}` by
        simp[written_taint_def, mk_inst_def] >>
      mp_tac (Q.INST [`R` |-> `{}:num set`,
        `inst` |-> `mk_inst id CALLDATACOPY [dst;src;n] []`]
        step_taint_memory_bound) >> simp[])
  >- (metis_tac[calldatacopy_written_range_clean])
  >- simp[calldatacopy_nonmemory_taint]
  >- simp[calldatacopy_nonmemory_taint]
  >- simp[calldatacopy_nonmemory_taint]
  >- (gvs[step_prov_def, step_taint_def, set_prov_def, set_var_taint_def,
        mk_inst_def, op_taint_def, FLOOKUP_DRESTRICT, lookup_var_def,
        write_memory_with_expansion_def, write_memory_def, expand_memory_def])
  >> gvs[write_memory_with_expansion_def, write_memory_def, expand_memory_def]
QED

Theorem emit_calldatacopy_endpoint_ptr:
  emit_void CALLDATACOPY [Var p;src;n] sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  eval_operand n s = SOME nw /\ ptr_covers G tn p s (w2n nw) /\
  op_taint tn src = {} /\ op_taint tn n = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u.
    (!root cap. ptr_covers G tn root s cap ==> ptr_covers H u root t cap) /\
    u.t_mem SUBSET tn.t_mem /\
    (!i. w2n dw <= i /\ i < w2n dw + w2n nw ==> i NOTIN u.t_mem) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!D lower ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  `t = write_memory_with_expansion (w2n dw)
    (TAKE (w2n nw)
      (DROP (w2n sw) s.vs_call_ctx.cc_calldata ++ REPLICATE (w2n nw) 0w)) s` by
    gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def] >>
  drule_all calldatacopy_ghost_frame >>
  disch_then (qspecl_then [`tn`,`sa.cs_next_id`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) t`,
    `step_taint (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) s t tn`] >>
  simp[] >> rpt strip_tac >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    !k. k < LENGTH [mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []] ==>
      get_instruction bb (LENGTH sa.cs_current_insts + k) =
        SOME (EL k [mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> simp[]) >>
  irule calldatacopy_safe_continuation >> simp[] >>
  qexistsl_tac [`dw`,`sa.cs_next_id`,`n`,`nw`,`p`,`src`,`sw`] >>
  simp[ADD1] >> conj_tac
  >- fs[ptr_covers_def] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED


Theorem calldata_bulk_payload_endpoint_ptr:
  abi_decode_bulk_payload (Var root) src cnt mem_sz CALLDATALOAD (Lit 0w) sa = ((),sb) /\
  lookup_var root s = SOME (n2w d) /\ eval_operand src s = SOME a /\
  eval_operand cnt s = SOME (n2w n) /\
  not_fresh_at sa root /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. cnt = Var x ==> not_fresh_at sa x) /\
  ptr_covers G tn root s capacity /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  op_taint tn cnt = {} /\ op_prov G cnt = NONE /\
  32 + n * mem_sz <= capacity /\ d + 32 < dimword (:256) /\
  n * mem_sz < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H u.
    ptr_covers H u root t capacity /\ u.t_mem SUBSET tn.t_mem /\
    (!i. d+32 <= i /\ i < d+32+n*mem_sz ==> i NOTIN u.t_mem) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  simp[abi_decode_bulk_payload_def, calldata_pos_addr, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w mem_sz)] sa = (sz,c1)` >>
  rename1 `emit_op ADD [src; Lit 32w] c1 = (sd,c2)` >>
  rename1 `emit_op ADD [Var root; Lit 32w] c2 = (dd,c3)` >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 c2 ++
    emitted_insts c2 c3 ++ emitted_insts c3 sb` by
    (imp_res_tac inst_extends_trans >>
     metis_tac[emitted_insts_append, inst_extends_def]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  dxrule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 sb) s3 = OK t` >>
  dxrule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  dxrule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz) /\
   op_taint tn (Lit (n2w mem_sz)) = {} /\
   op_prov G (Lit (n2w mem_sz)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `MUL`] emit_scalar_binop_raw_endpoint_ptr)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `op_taint u1 sz = {}` >> rename1 `op_prov H1 sz = NONE` >>
  qpat_assum `!x. not_fresh_at sa x ==> _` 
    (mp_then Any mp_tac old_operand_ghost_frame) >>
  disch_then (qspec_then `src` mp_tac) >> simp[] >> strip_tac >>
  `eval_operand src s1 = SOME a /\
   eval_operand (Lit 32w) s1 = SOME 32w /\
   op_taint u1 (Lit 32w) = {} /\ op_prov H1 (Lit 32w) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] emit_scalar_binop_raw_endpoint_ptr)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `op_taint u2 sd = {}` >> rename1 `op_prov H2 sd = NONE` >>
  `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
   c2.cs_next_var <= c3.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x /\ not_fresh_at c2 x /\ not_fresh_at c3 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `lookup_var root s2 = SOME (n2w d) /\ ptr_covers H2 u2 root s2 capacity` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `eval_operand (Lit 32w) s2 = SOME (n2w 32) /\
   op_taint u2 (Lit 32w) = {} /\ op_prov H2 (Lit 32w) = NONE /\
   32 + n*mem_sz <= capacity /\ w2n (n2w d : bytes32)+32 < dimword (:256)` by
    (`d < dimword (:256)` by decide_tac >>
     simp[eval_operand_def, op_taint_def, op_prov_def, w2n_n2w]) >>
  drule_all (Q.INST [`off` |-> `32`, `n` |-> `n*mem_sz`]
    (SPEC_ALL emit_ptr_offset_raw_endpoint_ptr)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `ptr_covers H3 u3 q s3 (n*mem_sz)` >>
  `(!x. sz = Var x ==> not_fresh_at c1 x) /\
   (!x. sd = Var x ==> not_fresh_at c2 x)` by
    (imp_res_tac abiDecoderReentryTheory.abi_decoder_operand_live_emit >>
     conj_tac >> rpt strip_tac >> gvs[] >>
     fs[calldataDynOwnedTheory.calldata_operand_live_not_fresh]) >>
  `!x. sz = Var x ==> not_fresh_at c2 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `!x. sz = Var x ==> _` drule >>
     simp[not_fresh_at_def] >> disch_then irule >> decide_tac) >>
  qpat_assum `!x. not_fresh_at c1 x ==> _`
    (mp_then Any mp_tac old_operand_ghost_frame) >>
  disch_then (qspec_then `sz` mp_tac) >> simp[] >> strip_tac >>
  qpat_assum `!x. not_fresh_at c2 x ==> _`
    (mp_then Any mp_tac old_operand_ghost_frame) >>
  disch_then (qspec_then `sz` mp_tac) >> simp[] >> strip_tac >>
  qpat_assum `!x. not_fresh_at c2 x ==> _`
    (mp_then Any mp_tac old_operand_ghost_frame) >>
  disch_then (qspec_then `sd` mp_tac) >> simp[] >> strip_tac >>
  `d < dimword (:256)` by decide_tac >>
  `eval_operand (Var q) s3 = SOME (n2w (d+32)) /\
   eval_operand sz s3 = SOME (n2w (n*mem_sz)) /\
   ptr_covers H3 u3 q s3 (w2n (n2w (n*mem_sz):bytes32))` by
    (fs[w2n_n2w, word_mul_n2w] >> simp[eval_operand_def]) >>
  `emit_void CALLDATACOPY [Var q;sd;sz] c3 = ((),sb)` by
    fs[abi_decode_copy_opcode_def] >>
  `run_inst_seq (emitted_insts c3 sb)
      (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) =
      OK (t with vs_inst_idx := LENGTH c3.cs_current_insts)` by
    (drule emitted_insts_emit_void >> strip_tac >>
     simp[run_inst_seq_inst_idx, is_terminator_def, mk_inst_def, exec_result_map_def]) >>
  `eval_operand (Var q) (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) = SOME (n2w (d+32)) /\
   eval_operand sd (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) = SOME (a+32w) /\
   eval_operand sz (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) = SOME (n2w (n*mem_sz)) /\
   ptr_covers H3 u3 q (s3 with vs_inst_idx := LENGTH c3.cs_current_insts)
     (w2n (n2w (n*mem_sz):bytes32))` by
    simp[eval_op_inst_idx, ptr_covers_def, lookup_var_def] >>
  drule_all (Q.INST [`s` |-> `s3 with vs_inst_idx := LENGTH c3.cs_current_insts`,
    `t` |-> `t with vs_inst_idx := LENGTH c3.cs_current_insts`]
    (SPEC_ALL emit_calldatacopy_endpoint_ptr)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  fs[ptr_covers_def, lookup_var_def, w2n_n2w] >>
  qexistsl_tac [`H`,`u`] >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\ cs_extends c3 sb` by
    (imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     fs[cs_extends_def, same_blocks_def, inst_extends_def]) >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
   fn_has_code c2 c3 func /\ fn_has_code c3 sb func` by
    (imp_res_tac cs_extends_trans >> metis_tac[fn_has_code_split]) >>
  `s1.vs_current_bb = c1.cs_current_bb /\ s2.vs_current_bb = c2.cs_current_bb /\
   s3.vs_current_bb = c3.cs_current_bb` by
    (imp_res_tac emit_op_same_blocks >> fs[same_blocks_def]) >>
  `allocas_from lower s1 /\ allocas_from lower s2 /\
   allocas_from lower (s3 with vs_inst_idx := LENGTH c3.cs_current_insts)` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  strip_tac >>
  `!fuel. ptr_safe_run D lower fuel ctx func PG H3 u3
      (s3 with vs_inst_idx := LENGTH c3.cs_current_insts)` by metis_tac[] >>
  `!fuel. ptr_safe_run D lower fuel ctx func PG H2 u2
      (s2 with vs_inst_idx := LENGTH c2.cs_current_insts)` by metis_tac[] >>
  `!fuel. ptr_safe_run D lower fuel ctx func PG H1 u1
      (s1 with vs_inst_idx := LENGTH c1.cs_current_insts)` by metis_tac[] >>
  `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
    (simp[venom_state_component_equality]) >>
  metis_tac[]
QED
