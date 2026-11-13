(* The allocation-free leaves of the owned source decoder contract: primitive
   words and bytestrings, and dynamic arrays of static elements without clamp
   (copied in bulk).  Neither allocates scratch. *)
Theory sourceOwnedLeafPtr
Ancestors
  sourcePrimitiveGasMem sourceBulkGasMem
  sourceOwnedArrayLoopPtr sourcePrimitiveReentryPtr abiDecoderSequenceReach
  decoderPrimitiveObservations decoderWorldFramePtr
  sourceBulkArrayLayout calldataBulkReentry calldataBulkUniformPtr
  abiDecoderBulkExecute abiStaticDynarrayLayout calldataTypedRobustPtr dynarrayLiveRobustPtr
  abiDecoderClampedWord abiDecoderBytesTyped abiValueEncoding
  abiDecoderCoherence sourceBytesRepresentation calldataDecodePtr abiDecoderReentry
  venomState abiDecoderBytes calldataDynOwned abiDecoderFrameCompose
  allocaFrontierBound allocaBudgetProps venomMemDefs ptrDiscipline bodyPtrDefs arithmetic
  abiDecoderBulk abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  decoderNavigationPtr decoderGhostFramePtr decoderRawEndpointPtr
  fragExec venomInst venomExecSemantics instIdxIndep finite_map words list
  calldataBulkPayloadPtr fragGasOriginPtr decoderArraySetupPtr abiDecoderComposition
  loweringStateRelDefs moduleLoweringProps

Theorem source_bulk_payload_origin_from_copy[local]:
  (!sa p src n sb s dw sw nw G tn t PG.
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
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn s) /\
      (!D lower explicit ctx func.
        fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
        ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
        s.vs_inst_idx = LENGTH sa.cs_current_insts /\
        w2n dw + w2n nw <= s.vs_alloca_next ==>
        gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
          (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))) ==>
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
  d + 32 + n * mem_sz <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
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
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  disch_tac >>
  simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def, comp_return_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w mem_sz)] sa = (sz,c1)` >>
  rename1 `emit_op ADD [src; Lit 32w] c1 = (sd,c2)` >>
  rename1 `emit_op ADD [Var root; Lit 32w] c2 = (dd,c3)` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
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
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\ cs_extends c3 sb` by
    (imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     fs[cs_extends_def, same_blocks_def, inst_extends_def]) >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
   fn_has_code c2 c3 func /\ fn_has_code c3 sb func` by
    (imp_res_tac cs_extends_trans >> metis_tac[fn_has_code_split]) >>
  `eval_operand sz s1 = SOME (n2w n * n2w mem_sz) /\
   s1.vs_labels = s.vs_labels /\ s2.vs_labels = s1.vs_labels /\
   s3.vs_labels = s2.vs_labels /\
   s1.vs_current_bb = s.vs_current_bb /\ s2.vs_current_bb = s1.vs_current_bb /\
   s3.vs_current_bb = s2.vs_current_bb /\
   s1.vs_alloca_next = s.vs_alloca_next /\
   s2.vs_alloca_next = s1.vs_alloca_next /\ s3.vs_alloca_next = s2.vs_alloca_next /\
   s1.vs_allocas = s.vs_allocas /\ s2.vs_allocas = s1.vs_allocas /\
   s3.vs_allocas = s2.vs_allocas /\
   ~s1.vs_halted /\ ~s2.vs_halted /\ ~s3.vs_halted` by
    (imp_res_tac emitted_insts_emit_op >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE, AllCaseEqs()]) >>
  `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz) /\
   op_taint tn (Lit (n2w mem_sz)) = {} /\
   op_prov G (Lit (n2w mem_sz)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `MUL`]
    (SPEC_ALL emit_scalar_binop_endpoint_ptr_origin_core))) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] strip_assume_tac) >>
  rename1 `op_taint u1 sz = {}` >> rename1 `op_prov H1 sz = NONE` >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac >>
  qpat_assum `!x. not_fresh_at sa x ==> _`
    (mp_then Any mp_tac old_operand_ghost_frame) >>
  disch_then (qspec_then `src` mp_tac) >> simp[] >> strip_tac >>
  `eval_operand src s1 = SOME a /\
   eval_operand (Lit 32w) s1 = SOME 32w /\
   op_taint u1 (Lit 32w) = {} /\ op_prov H1 (Lit 32w) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  `run_inst_seq (emitted_insts c1 c2)
      (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) =
      OK (s2 with vs_inst_idx := LENGTH c1.cs_current_insts)` by
    (qpat_assum `emit_op ADD [src; Lit 32w] c1 = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s1`,`LENGTH c1.cs_current_insts`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  drule_all (SRULE [eval_op_inst_idx] (Q.INST [`opc` |-> `ADD`,
    `s` |-> `s1 with vs_inst_idx := LENGTH c1.cs_current_insts`,
    `t` |-> `s2 with vs_inst_idx := LENGTH c1.cs_current_insts`]
    (SPEC_ALL emit_scalar_binop_endpoint_ptr_origin_core))) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] strip_assume_tac) >>
  rename1 `op_taint u2 sd = {}` >> rename1 `op_prov H2 sd = NONE` >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac >>
  fs[lookup_var_def] >>
  `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
   c2.cs_next_var <= c3.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x /\ not_fresh_at c2 x /\ not_fresh_at c3 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `lookup_var root s2 = SOME (n2w d) /\ ptr_covers H2 u2 root s2 capacity` by
    (gvs[ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  `eval_operand (Lit 32w) s2 = SOME (n2w 32) /\
   op_taint u2 (Lit 32w) = {} /\ op_prov H2 (Lit 32w) = NONE /\
   32 + n*mem_sz <= capacity /\ w2n (n2w d : bytes32)+32 < dimword (:256)` by
    (`d < dimword (:256)` by decide_tac >>
     simp[eval_operand_def, op_taint_def, op_prov_def, w2n_n2w]) >>
  `run_inst_seq (emitted_insts c2 c3)
      (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) =
      OK (s3 with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    (qpat_assum `emit_op ADD [Var root; Lit 32w] c2 = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s2`,`LENGTH c2.cs_current_insts`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  `ptr_covers H2 u2 root (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) capacity` by
    simp[ptr_covers_def, lookup_var_def] >>
  drule_all (SRULE [eval_op_inst_idx, cj 4 control_moves_keep_vars]
    (Q.INST [`off` |-> `32`, `n` |-> `n*mem_sz`,
      `s` |-> `s2 with vs_inst_idx := LENGTH c2.cs_current_insts`,
      `t` |-> `s3 with vs_inst_idx := LENGTH c2.cs_current_insts`]
      (SPEC_ALL emit_ptr_offset_endpoint_ptr_origin_core))) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] strip_assume_tac) >>
  rename1 `dd = Var q` >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac >>
  rename1 `u3.t_mem = u2.t_mem` >>
  rename1 `gas_origin_ptr_path _ (_,H2,u2) [] (_,H3,u3)` >>
  `(!x. sz = Var x ==> not_fresh_at c1 x) /\
   (!x. sd = Var x ==> not_fresh_at c2 x)` by
    (imp_res_tac abiDecoderReentryTheory.abi_decoder_operand_live_emit >>
     conj_tac >> rpt strip_tac >> gvs[] >>
     fs[calldata_operand_live_not_fresh]) >>
  `!x. sz = Var x ==> not_fresh_at c2 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `!x. sz = Var x ==> _` drule >>
     simp[not_fresh_at_def] >> disch_then irule >> decide_tac) >>
  qpat_assum `!x. not_fresh_at c1 x ==> _`
    (mp_then Any mp_tac (SRULE[lookup_var_def] old_operand_ghost_frame)) >>
  disch_then (qspec_then `sz` mp_tac) >> simp[lookup_var_def] >> strip_tac >>
  qpat_assum `!x. not_fresh_at c2 x ==> _`
    (mp_then Any mp_tac old_operand_ghost_frame) >>
  disch_then (qspec_then `sz` mp_tac) >> simp[lookup_var_def] >> strip_tac >>
  qpat_assum `!x. not_fresh_at c2 x ==> _`
    (mp_then Any mp_tac old_operand_ghost_frame) >>
  disch_then (qspec_then `sd` mp_tac) >> simp[lookup_var_def] >> strip_tac >>
  `eval_operand sd s2 = SOME (a + 32w)` by
    (qpat_assum `emit_op ADD [src; Lit 32w] c1 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `d < dimword (:256)` by decide_tac >>
  `eval_operand (Var q) s3 = SOME (n2w (d+32)) /\
   eval_operand sz s3 = SOME (n2w (n*mem_sz)) /\
   ptr_covers H3 u3 q s3 (w2n (n2w (n*mem_sz):bytes32))` by
    (fs[w2n_n2w, word_mul_n2w] >> simp[eval_operand_def, lookup_var_def]) >>
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
  qpat_assum `!sa p src n sb s dw sw nw G tn t PG. _`
    (fn th => drule_all (Q.INST
      [`s` |-> `s3 with vs_inst_idx := LENGTH c3.cs_current_insts`,
       `t` |-> `t with vs_inst_idx := LENGTH c3.cs_current_insts`,
       `PG` |-> `PG`] (SPEC_ALL th))) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `u4.t_mem SUBSET u3.t_mem` >>
  rename1 `gas_origin_ptr_path _ (_,H3,u3) [] (_,H4,u4)` >>
  fs[] >>
  qpat_x_assum `!sa p src n sb s dw sw nw G tn t PG. _` kall_tac >>
  `allocas_from lower s1 /\ allocas_from lower s2 /\ allocas_from lower s3 /\
   s1.vs_current_bb = c1.cs_current_bb /\
   s2.vs_current_bb = c2.cs_current_bb /\
   s3.vs_current_bb = c3.cs_current_bb` by
    (imp_res_tac emit_op_same_blocks >> fs[allocas_from_def, same_blocks_def] >> metis_tac[]) >>
  qexistsl [`H4`,`u4`] >>
  simp[w2n_n2w] >>
  conj_tac >-
    (qpat_assum `!root cap. ptr_covers H3 u3 root _ cap ==> _` irule >>
     simp[ptr_covers_def, lookup_var_def] >>
     gvs[ptr_covers_def, lookup_var_def, w2n_n2w] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
  rpt gen_tac >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
     (OK (s1 with vs_inst_idx := LENGTH c1.cs_current_insts),H1,u1)` by metis_tac[] >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
     (s1 with vs_inst_idx := LENGTH c1.cs_current_insts,H1,u1) []
     (OK (s2 with vs_inst_idx := LENGTH c2.cs_current_insts),H2,u2)` by metis_tac[] >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
     (s2 with vs_inst_idx := LENGTH c2.cs_current_insts,H2,u2) []
     (OK (s3 with vs_inst_idx := LENGTH c3.cs_current_insts),H3,u3)` by metis_tac[] >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
     (s3 with vs_inst_idx := LENGTH c3.cs_current_insts,H3,u3) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H4,u4)` by simp[] >>
  metis_tac[gas_origin_ptr_path_append, APPEND]

QED

Theorem source_owned_primitive_decoder_ptr:
  abi_decoder_coherent ce env sf ty tv /\
  ((?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\ is_word_type ty) \/
   (?m. type_to_abi_dec_info sf ce ty = DecBytestring m)) /\
  compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  eval_operand childsrc r = SOME (n2w srcpos) /\
  lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var (Var child) /\
  abi_decoder_operand_live middle.cs_next_var (Var root) /\
  ptr_covers G tn child r (type_memory_size tv) /\
  ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
  alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
  e + type_memory_size tv < dimword (:256) /\
  (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP r.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
  allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
  r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?t H u.
    abi_decode_sim ctx fn r t /\
    gas_path_mem ctx fn r 0 (OK t) /\
    (!D explicit. gas_origin_ptr_path (D, lower, explicit, ctx, fn, PG) (r, G, tn) [] (OK t, H, u)) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v e mem) /\
    abi_decode_footprint_frame [(e,type_memory_size tv)] r t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
    r.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
    (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
    (!op. abi_decoder_operand_live middle.cs_next_var op ==>
      eval_operand op t = eval_operand op r) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r) /\
    t.vs_accounts = r.vs_accounts /\ t.vs_transient = r.vs_transient /\
    t.vs_logs = r.vs_logs /\ t.vs_outcomes = r.vs_outcomes /\
    t.vs_requests = r.vs_requests /\
    t.vs_pending_deletions = r.vs_pending_deletions /\ t.vs_tx_ctx = r.vs_tx_ctx /\
    t.vs_block_ctx = r.vs_block_ctx /\ t.vs_fmp = r.vs_fmp /\
    t.vs_gas_readings = r.vs_gas_readings
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `evaluate_type env ty = SOME tv /\
   type_memory_size tv = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `((?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
       is_word_type ty /\ type_memory_size tv = 32) \/
    (?m. type_to_abi_dec_info sf ce ty = DecBytestring m /\
       type_memory_size tv = abi_decode_bytes_copy_size m /\ m < dimword (:256)))` by
    (qpat_x_assum `(?clamp. _ /\ is_word_type ty) \/ _` strip_assume_tac
     >- metis_tac[abi_word_type_size] >>
     drule_all coherent_source_bytes_representation >> strip_tac >>
     disj2_tac >> qexists `m` >>
     `m < dimword (:256)` by
       (mp_tac (Q.INST [`n` |-> `m`] abi_decoder_bytes_copy_size) >> decide_tac) >>
     metis_tac[]) >> (
  `type_memory_size tv < dimword (:256) /\ e < dimword (:256) /\
    srcpos < dimword (:256)` by decide_tac >>
  `not_fresh_at middle child /\ not_fresh_at middle root /\
   (!x. childsrc = Var x ==> not_fresh_at middle x)` by
    (conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     rpt strip_tac >>
     metis_tac[calldata_operand_live_not_fresh]) >>
  `eval_operand (Var child) r = SOME (n2w e)` by simp[eval_operand_def] >>
  `?t H u.
    run_inst_seq (emitted_insts middle end_st) r = OK (t with vs_inst_idx := r.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ptr_covers H u child t (type_memory_size tv) /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v e mem) /\
    abi_decode_frame e (type_memory_size tv) r t /\ fresh_vars_wrt limit t /\
    t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next /\
    (!op w. (!x. op = Var x ==> not_fresh_at middle x) /\ eval_operand op r = SOME w ==>
      eval_operand op t = SOME w) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r)` by
    (irule source_primitive_decoder_reentry_ptr >>
     metis_tac[]) >>
  `base_addr + owner_cap <= r.vs_alloca_next` by
    metis_tac[alloca_inv_def, alloca_next_valid_def] >>
  `e + type_memory_size tv <= r.vs_alloca_next` by decide_tac >>
  `gas_path_mem ctx fn r 0
     (OK ((t with vs_inst_idx := r.vs_inst_idx) with
       vs_inst_idx := LENGTH end_st.cs_current_insts))` by
    (irule source_primitive_run_gas_path_mem >>
     conj_tac >- simp[] >>
     qexistsl [`child`, `type_to_abi_dec_info sf ce ty`, `e`, `middle`,
       `childsrc`, `type_memory_size tv`] >> metis_tac[]) >>
  `gas_path_mem ctx fn r 0 (OK t)` by
    (qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >>
     qpat_x_assum `t.vs_inst_idx = _` (fn th => simp[GSYM th])) >>
  drule decoder_primitive_code_shape >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `abi_decode_sim ctx fn r t` by
    (drule_all abi_decoder_run_sequence_reach >>
     qpat_x_assum `t.vs_inst_idx = _` (fn th => simp[GSYM th])) >>
  `!op. abi_decoder_operand_live middle.cs_next_var op ==>
    eval_operand op t = eval_operand op r` by
    (rpt strip_tac >>
     drule decoder_primitive_old_operand >>
     disch_then (qspecl_then [`t with vs_inst_idx := r.vs_inst_idx`,`r`,`op`] mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     simp[eval_operand_def, lookup_var_def]) >>
  drule_all decoder_run_world_frame >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qexistsl [`t`,`H`,`u`] >>
  pure_asm_rewrite_tac [] >>
  simp_tac bool_ss [] >>
  conj_tac >- metis_tac[abi_decode_frame_footprint] >>
  conj_tac >-
    (qpat_x_assum `alloca_inv r` mp_tac >>
     pure_asm_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     simp_tac bool_ss []) >>
  conj_tac >-
    (qpat_x_assum `alloca_frontier_inv ctx fn site r` mp_tac >>
     pure_asm_rewrite_tac [alloca_frontier_inv_def, remaining_alloca_budget_def] >>
     simp_tac bool_ss []) >>
  conj_tac >-
    (qpat_x_assum `allocas_from lower r` mp_tac >>
     pure_asm_rewrite_tac [allocas_from_def] >> simp_tac bool_ss []) >>
  simp_tac bool_ss [LESS_EQ_REFL] >>
  `lookup_var root t = lookup_var root r` by
    (qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _` (qspec_then `Var root` mp_tac) >>
     simp[eval_operand_def]) >>
  qpat_x_assum `ptr_covers G tn root r outsz` mp_tac >>
  pure_rewrite_tac[ptr_covers_def] >>
  `FLOOKUP H root = FLOOKUP G root /\ op_taint u (Var root) = op_taint tn (Var root)` by
    metis_tac[] >>
  pure_asm_rewrite_tac[] >> simp_tac bool_ss [])
QED

Theorem source_owned_bulk_array_ptr:
  abi_decoder_coherent ce env sf (ArrayT ety (Dynamic maxn)) tv /\
  ~is_abi_dynamic ce.ce_struct_fields ety /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ety) /\
  compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn))) middle = ((),end_st) /\
  value_has_type tv v /\
  vyper_to_abi env (ArrayT ety (Dynamic maxn)) v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av) < dimword (:256) /\
  eval_operand childsrc r = SOME (n2w srcpos) /\
  lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var (Var child) /\
  abi_decoder_operand_live middle.cs_next_var (Var root) /\
  ptr_covers G tn child r (type_memory_size tv) /\
  ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
  alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
  e + type_memory_size tv < dimword (:256) /\
  (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP r.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
  allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
  r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?t H u.
    abi_decode_sim ctx fn r t /\
    gas_path_mem ctx fn r 0 (OK t) /\
    (!D explicit. gas_origin_ptr_path (D, lower, explicit, ctx, fn, PG) (r, G, tn) [] (OK t, H, u)) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v e mem) /\
    abi_decode_footprint_frame [(e,type_memory_size tv)] r t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
    r.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
    (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
    (!op. abi_decoder_operand_live middle.cs_next_var op ==>
      eval_operand op t = eval_operand op r) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r) /\
    t.vs_accounts = r.vs_accounts /\ t.vs_transient = r.vs_transient /\
    t.vs_logs = r.vs_logs /\ t.vs_outcomes = r.vs_outcomes /\
    t.vs_requests = r.vs_requests /\
    t.vs_pending_deletions = r.vs_pending_deletions /\ t.vs_tx_ctx = r.vs_tx_ctx /\
    t.vs_block_ctx = r.vs_block_ctx /\ t.vs_fmp = r.vs_fmp /\
    t.vs_gas_readings = r.vs_gas_readings /\
    t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all source_bulk_array_layout >> strip_tac >>
  `evaluate_type env (ArrayT ety (Dynamic maxn)) = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn)) =
    DecDynArray (type_to_abi_dec_info sf ce ety) (abi_embedded_static_size ce.ce_struct_fields ety)
      (type_memory_size etv) F maxn` by
    simp[exprLoweringTheory.type_to_abi_dec_info_def] >>
  `0 < type_slot_size etv /\
   1 + maxn * type_slot_size etv < dimword (:256)` by
    (qpat_x_assum `evaluate_type env (ArrayT _ _) = _` mp_tac >>
     pure_asm_rewrite_tac [Once vyperValueTheory.evaluate_type_def] >>
     simp_tac (srw_ss()) [LET_THM, AllCaseEqs(), vyperValueTheory.type_slot_size_def]) >>
  `maxn <= maxn * type_slot_size etv` by
    (Cases_on `type_slot_size etv` >- decide_tac >> simp[MULT_SUC]) >>
  `maxn < dimword (:256)` by decide_tac >>
  `type_memory_size tv = 32 + maxn * type_memory_size etv` by
    metis_tac[valueEncodingTheory.type_memory_size_def] >>
  `LENGTH vs * type_memory_size etv <= maxn * type_memory_size etv` by
    simp[LE_MULT_RCANCEL] >>
  `32 + LENGTH vs * type_memory_size etv <= type_memory_size tv /\
   e+32 < dimword (:256) /\ LENGTH vs * type_memory_size etv < dimword (:256)` by
    decide_tac >>
  `LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av) =
    32 + LENGTH vs * type_memory_size etv` by
    (pure_asm_rewrite_tac [listTheory.LENGTH_APPEND] >> simp_tac (srw_ss()) []) >>
  `srcpos+32 < dimword (:256) /\ srcpos < dimword (:256)` by decide_tac >>
  `mem_word_at srcpos r.vs_call_ctx.cc_calldata = n2w (LENGTH vs) /\
   mem_bytes_at (srcpos+32) (LENGTH vs * type_memory_size etv)
     r.vs_call_ctx.cc_calldata = FLAT (MAP (enc (vyper_to_abi_type env ety)) avs)` by
    (irule abiDecoderBulkTheory.static_dynarray_source_windows >>
     pure_asm_rewrite_tac [] >>
     conj_tac >-
       (qpat_x_assum `mem_bytes_at srcpos _ _ = _` mp_tac >>
        pure_rewrite_tac [vyperABITheory.vyper_to_abi_type_def] >>
        pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
     metis_tac[]) >>
  `abi_decode_load CALLDATALOAD (n2w srcpos : bytes32) r = n2w (LENGTH vs)` by
    (qpat_x_assum `mem_word_at srcpos _ = _` mp_tac >>
     simp_tac (srw_ss()) [abiDecoderContractTheory.abi_decode_load_def,
       abiDecoderContractTheory.abi_decode_source_def, valueEncodingDefsTheory.mem_word_at_def,
       valueEncodingDefsTheory.mem_bytes_at_def, wordsTheory.w2n_n2w] >>
     `srcpos MOD dimword (:256) = srcpos` by simp[] >>
     pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
  `eval_operand (Var child) r = SOME (n2w e)` by simp[eval_operand_def] >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_ONCE_REWRITE_RULE
      [exprLoweringTheory.type_to_abi_dec_info_def]) >>
  `compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray (type_to_abi_dec_info sf ce ety)
      (abi_embedded_static_size ce.ce_struct_fields ety) (type_memory_size etv) F maxn)
      middle = ((),end_st)` by metis_tac[] >>
  drule_all calldata_bulk_reentry_sequence >> strip_tac >>
  `base_addr + owner_cap <= r.vs_alloca_next` by
    metis_tac[alloca_inv_def, alloca_next_valid_def] >>
  `e + (32 + LENGTH vs * type_memory_size etv) <= r.vs_alloca_next /\
   e + (32 + LENGTH vs * type_memory_size etv) < dimword (:256)` by decide_tac >>
  `gas_path_mem ctx fn r 0
     (OK (t with vs_inst_idx := LENGTH end_st.cs_current_insts))` by
    (drule_all source_bulk_run_gas_path_mem >> simp_tac (srw_ss()) []) >>
  `not_fresh_at middle child /\ not_fresh_at middle root /\
   (!x. childsrc = Var x ==> not_fresh_at middle x)` by
    (conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     rpt strip_tac >> metis_tac[calldata_operand_live_not_fresh]) >>
  drule_all calldata_bulk_decoder_endpoint_ptr_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `val_in_memory tv v e t.vs_memory` by
    (pure_asm_rewrite_tac [] >>
     irule static_dynarray_canonical_layout >> metis_tac[]) >>
  `!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v e mem` by
    (rpt strip_tac >> pure_asm_rewrite_tac [] >> irule clean_live_prefix_dynarray_robust >>
     metis_tac[vyperTypingTheory.all_have_type_EVERY]) >>
  `abi_decode_source_opcode CALLDATALOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abiDecoderBulkTheory.abi_decoder_bulk_shape >> strip_tac >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  `inst_extends middle end_st` by
    (pure_asm_rewrite_tac [emitHelperPropsTheory.inst_extends_def,
       exprLoweringPropsTheory.emitted_insts_def] >>
     metis_tac[rich_listTheory.IS_PREFIX_APPEND, rich_listTheory.DROP_LENGTH_APPEND]) >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `t' = _` SUBST_ALL_TAC >>
  `t.vs_labels = r.vs_labels` by
    metis_tac[ctorAbiActualObservationsTheory.ctor_actual_sequence_labels] >>
  `!op. abi_decoder_operand_live middle.cs_next_var op ==>
    eval_operand op t = eval_operand op r` by
    (rpt strip_tac >> Cases_on `op` >>
     simp_tac (srw_ss()) [eval_operand_def] >>
     metis_tac[calldata_operand_live_not_fresh]) >>
  drule_all decoder_run_world_frame >> strip_tac >>
  `alloca_inv t` by
    (qpat_x_assum `alloca_inv r` mp_tac >>
     pure_asm_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     simp_tac bool_ss []) >>
  `alloca_frontier_inv ctx fn site t` by
    (qpat_x_assum `alloca_frontier_inv ctx fn site r` mp_tac >>
     pure_asm_rewrite_tac [alloca_frontier_inv_def, remaining_alloca_budget_def] >>
     simp_tac bool_ss []) >>
  `allocas_from lower (t with vs_inst_idx := LENGTH end_st.cs_current_insts)` by
    (qpat_x_assum `allocas_from lower r` mp_tac >>
     simp_tac (srw_ss()) [allocas_from_def] >> pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
  `ptr_covers H u root t outsz` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> metis_tac[]) >>
  `abi_decode_frame e (type_memory_size tv) r t` by
    (irule abiDecoderFrameComposeTheory.abi_decode_frame_widen >>
     qexistsl [`e`,`32 + LENGTH vs * type_memory_size etv`] >>
     pure_asm_rewrite_tac [] >> decide_tac) >>
  `abi_decode_footprint_frame [(e,type_memory_size tv)] r
     (t with vs_inst_idx := LENGTH end_st.cs_current_insts)` by
    (simp_tac (srw_ss()) [GSYM abi_decode_frame_footprint,
       abiDecoderContractTheory.abi_decode_frame_def] >>
     metis_tac[abiDecoderContractTheory.abi_decode_frame_def]) >>
  qpat_x_assum `tv = _` SUBST_ALL_TAC >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qexistsl [`t with vs_inst_idx := LENGTH end_st.cs_current_insts`,`H`,`u`] >>
  pure_asm_rewrite_tac [] >>
  simp_tac (srw_ss()) [loweringStateRelDefsTheory.fresh_vars_wrt_def,
    lookup_var_def, eval_operand_def] >>
  pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >>
  conj_tac >- (qpat_assum `fresh_vars_wrt _ t` mp_tac >>
    simp_tac (srw_ss()) [loweringStateRelDefsTheory.fresh_vars_wrt_def]) >>
  simp_tac arith_ss [] >>
  conj_tac >- (qpat_x_assum `ptr_covers H u child t _` mp_tac >>
    pure_asm_rewrite_tac [] >> simp_tac arith_ss []) >>
  metis_tac[]
QED
