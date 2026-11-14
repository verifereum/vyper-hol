(* Bulk payload replay with ghosts chosen before the continuation domain. *)
Theory calldataBulkUniformPtr
Ancestors moduleLoweringProps rich_list venomInstProps decoderNavigationPtr fragGasOriginPtr fragGasSeqPtr calldataBulkPayloadPtr decoderRawEndpointPtr decoderGhostFramePtr
  decoderArraySetupPtr calldataDynOwned abiDecoderBulk abiEncoder compileEnv loweringStateRelDefs
  emitHelper emitHelperProps exprLoweringProps bodyPtrDefs ptrDiscipline
  ptrSafeRun venomInst venomState venomExecSemantics instIdxIndep
  finite_map pred_set words list arithmetic abiDecoderComposition fragExec
  decoderHeaderRawPtr decoderArrayInitPtr abiDecoderDynarrayPrefix
  abiDecoderDynarrayBound abiDecoderArrayHeader abiDecoderContract abiDecoderGuards
  abiDecoderReentry

Theorem calldata_bulk_payload_endpoint_ptr_uniform_joint:
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
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s) /\
    (alloca_inv s /\ d + capacity <= s.vs_alloca_next /\ ~s.vs_halted ==>
      alloca_inv t /\ !D explicit.
        gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
          (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  strip_tac >> drule_all calldata_bulk_payload_endpoint_ptr_uniform_origin_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`H`,`u`] >> simp[]
QED

Theorem calldata_bulk_payload_endpoint_ptr_uniform:
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
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  strip_tac >> drule_all calldata_bulk_payload_endpoint_ptr_uniform_origin >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`H`,`u`] >> simp[]
QED

Theorem calldata_bulk_phase_runs[local]:
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) sa = ((),sb) /\
  ~dec_info_needs_clamp ei /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?count_op c1 cnt c2 s1 s2.
    abi_decode_count_guard CALLDATALOAD src maxn sa = (count_op,c1) /\
    abi_decode_array_header (Var root) src CALLDATALOAD c1 = (cnt,c2) /\
    abi_decode_bulk_payload (Var root) src cnt mem_sz CALLDATALOAD (Lit 0w) c2 = ((),sb) /\
    inst_extends sa c1 /\ inst_extends c1 c2 /\ inst_extends c2 sb /\
    cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 sb /\
    sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
    same_blocks sa c1 /\ same_blocks c1 c2 /\
    (!x. cnt = Var x ==> not_fresh_at c2 x) /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2) /\
    run_inst_seq (emitted_insts sa c1) s = OK s1 /\
    run_inst_seq (emitted_insts c1 c2) s1 = OK s2 /\
    run_inst_seq (emitted_insts c2 sb) s2 = OK t
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases,
    abi_decode_dynarray_position_prefix_def,
    compile_abi_dec_addr_def,
    abiDecoderBytesBoundTheory.abi_decode_bytes_head_def,
    abi_decode_dynarray_payload_guard_def, abi_decode_dynarray_end_guard_def,
    abi_decode_bulk_body_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM, eval_operand_def, ADD_CLAUSES,
    abi_decoder_operand_live_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn sa = (count_op,c1)` >>
  rename1 `abi_decode_array_header (Var root) src CALLDATALOAD c1 = (cnt,c2)` >>
  `inst_extends sa c1 /\ inst_extends c1 c2 /\ inst_extends c2 sb` by
    (imp_res_tac abi_decode_count_guard_shape >>
     qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     qpat_x_assum `abi_decode_bulk_payload _ _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def,
       abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     metis_tac[inst_extends_trans]) >>
  `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
   same_blocks sa c1 /\ same_blocks c1 c2 /\
   (!x. cnt = Var x ==> not_fresh_at c2 x) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2)` by
    (qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abi_decode_count_guard_def, abi_decode_array_header_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
     imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     fs[same_blocks_def, not_fresh_at_def, is_terminator_def, mk_inst_def] >>
     rename1 `emit_op CALLDATALOAD [src] c1 = (_,mid)` >>
     `emitted_insts c1 c2 = emitted_insts c1 mid ++ emitted_insts mid c2` by
       (irule emitted_insts_append >> simp[]) >> simp[is_terminator_def]) >>
  `cs_extends sa c1 /\ cs_extends c1 c2` by
    fs[cs_extends_def, same_blocks_def, inst_extends_def] >>
  `cs_extends c2 sb` by
    (qpat_x_assum `abi_decode_bulk_payload _ _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def, comp_return_def, comp_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     imp_res_tac inst_extends_trans >> fs[cs_extends_def, same_blocks_def, inst_extends_def] >>
     simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 sb` by
    (imp_res_tac inst_extends_trans >> metis_tac[emitted_insts_append,inst_extends_def]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
  dxrule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 sb) s2 = OK t` >>
  dxrule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  qexistsl_tac [`s1`,`s2`] >> simp[]
QED

Theorem calldata_bulk_decoder_endpoint_ptr_uniform_origin:
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) sa = ((),sb) /\
  ~dec_info_needs_clamp ei /\ lookup_var root s = SOME (n2w d) /\
  eval_operand src s = SOME a /\ abi_decode_load CALLDATALOAD a s = n2w n /\
  not_fresh_at sa root /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  ptr_covers G tn root s capacity /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  32+n*mem_sz <= capacity /\ d+32 < dimword (:256) /\ n*mem_sz < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H u.
    ptr_covers H u root t capacity /\ u.t_mem SUBSET tn.t_mem /\
    (!i. d <= i /\ i < d+32+n*mem_sz ==> i NOTIN u.t_mem) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s) /\
    (d+32+n*mem_sz <= s.vs_alloca_next ==>
     !D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  strip_tac >> drule_all calldata_bulk_phase_runs >> strip_tac >>
  drule_all (Q.INST [`H` |-> `ARB`] calldata_count_guard_endpoint_ptr_origin_core) >>
  disch_then (qspecl_then [`ARB`,`ctx`,`ARB`,`PG`,`G`] strip_assume_tac) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  rename1 `op_taint u1 count_op = {}` >> rename1 `op_prov H1 count_op = NONE` >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x /\ not_fresh_at c2 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `s1.vs_labels = s.vs_labels /\ s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_allocas = s.vs_allocas /\ s1.vs_alloca_next = s.vs_alloca_next /\
   ~s1.vs_halted` by simp[] >>
  qpat_assum `!x. not_fresh_at sa x ==> _`
    (mp_then Any mp_tac old_operand_ghost_frame) >>
  disch_then (qspec_then `src` mp_tac) >> simp[] >> strip_tac >>
  `lookup_var root s1 = SOME (n2w d) /\ ptr_covers H1 u1 root s1 capacity` by
    (conj_tac >- metis_tac[] >> irule ptr_covers_frame >> metis_tac[]) >>
  `not_fresh_at c1 root /\ 32 <= capacity /\ d < dimword (:256)` by
    (simp[] >> decide_tac) >>
  `eval_operand src s1 = SOME a` by fs[] >>
  `run_inst_seq (emitted_insts c1 c2)
      (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) =
      OK (s2 with vs_inst_idx := LENGTH c1.cs_current_insts)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `lookup_var root (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) = SOME (n2w d) /\
   ptr_covers H1 u1 root (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) capacity /\
   eval_operand src (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) = SOME a /\
   ~(s1 with vs_inst_idx := LENGTH c1.cs_current_insts).vs_halted` by
    gvs[lookup_var_def, ptr_covers_def, eval_op_inst_idx] >>
  drule_all (Q.INST [`H` |-> `ARB`,
    `s` |-> `s1 with vs_inst_idx := LENGTH c1.cs_current_insts`,
    `t` |-> `s2 with vs_inst_idx := LENGTH c1.cs_current_insts`]
    (SPEC_ALL calldata_array_header_endpoint_ptr_origin_core)) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] strip_assume_tac) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  fs[lookup_var_def, ptr_covers_def, eval_op_inst_idx] >>
  rename1 `op_taint u2 cnt = {}` >> rename1 `op_prov H2 cnt = NONE` >>
  `abi_decoder_operand_live c1.cs_next_var src` by
    (Cases_on `src` >> fs[abi_decoder_operand_live_def, calldata_operand_live_not_fresh] >> metis_tac[]) >>
  `eval_operand src s2 = SOME a /\ op_taint u2 src = {} /\ op_prov H2 src = NONE` by
    (conj_tac >- metis_tac[] >> Cases_on `src` >>
     fs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `lookup_var root s2 = SOME (n2w d) /\ not_fresh_at c2 root /\
   (!x. src = Var x ==> not_fresh_at c2 x)` by
    (qpat_assum `!x. not_fresh_at c1 x ==> _`
      (qspec_then `root` mp_tac) >> fs[lookup_var_def] >> metis_tac[]) >>
  `eval_operand cnt s2 = SOME (n2w n)` by
    (qpat_x_assum `s1 = s with vs_vars := _` SUBST_ALL_TAC >>
     fs[abi_decode_load_def, abi_decode_source_def]) >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 sb func` by
    (imp_res_tac cs_extends_trans >> metis_tac[fn_has_code_split]) >>
  `allocas_from lower s1 /\ allocas_from lower s2 /\ ~s2.vs_halted /\
   s1.vs_current_bb = c1.cs_current_bb /\ s2.vs_current_bb = c2.cs_current_bb /\
   s2.vs_alloca_next = s.vs_alloca_next` by
    (fs[allocas_from_def, same_blocks_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts c2 sb)
     (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) =
     OK (t with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    metis_tac[decoderHeaderRawPtrTheory.calldata_bulk_payload_run_pc] >>
  `lookup_var root (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) = SOME (n2w d) /\
   eval_operand src (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) = SOME a /\
   eval_operand cnt (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) = SOME (n2w n) /\
   ptr_covers H2 u2 root (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) capacity /\
   allocas_from lower (s2 with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    (gvs[lookup_var_def, eval_op_inst_idx, ptr_covers_def, allocas_from_def] >> metis_tac[]) >>
  `32 + n * mem_sz <= capacity /\ n * mem_sz < dimword (:256)` by
    simp[MULT_COMM, ADD_COMM] >>
  mp_tac (SRULE [] (Q.INST
    [`sa` |-> `c2`, `G` |-> `H2`, `tn` |-> `u2`,
     `s` |-> `s2 with vs_inst_idx := LENGTH c2.cs_current_insts`,
     `t` |-> `t with vs_inst_idx := LENGTH c2.cs_current_insts`]
    (SPEC_ALL calldata_bulk_payload_endpoint_ptr_uniform_origin))) >>
  impl_tac >-
    (gvs[lookup_var_def, eval_op_inst_idx, ptr_covers_def, allocas_from_def] >>
     metis_tac[]) >>
  strip_tac >> rename1 `u3.t_mem SUBSET u2.t_mem` >>
  rename1 `ptr_covers H3 u3 root _ capacity` >>
  `allocas_from lower (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) /\
   allocas_from lower (s2 with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  qexistsl [`H3`,`u3`] >>
  conj_tac >- (fs[ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac >- (irule SUBSET_TRANS >> qexists_tac `u2.t_mem` >> simp[]) >>
  conj_tac >-
    (rpt strip_tac >> Cases_on `i < d+32`
     >- (qpat_x_assum `u3.t_mem SUBSET u2.t_mem` mp_tac >>
         simp[SUBSET_DEF] >> metis_tac[]) >>
     gvs[]) >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> fs[lookup_var_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
    (OK (s1 with vs_inst_idx := LENGTH c1.cs_current_insts),H1,u1)` by
    (qpat_assum `s1 = s with vs_vars := _`
      (fn eq => simp_tac (srw_ss()) [eq]) >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
    (s1 with vs_inst_idx := LENGTH c1.cs_current_insts,H1,u1) []
    (OK (s2 with vs_inst_idx := LENGTH c2.cs_current_insts),H2,u2)` by
      (first_assum irule >> simp[] >> decide_tac) >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
    (s2 with vs_inst_idx := LENGTH c2.cs_current_insts,H2,u2) []
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H3,u3)` by
      (first_assum irule >> simp[] >> decide_tac) >>
  NTAC 3 (qpat_x_assum `gas_origin_ptr_path _ _ [] _` mp_tac) >>
  rpt (pop_assum kall_tac) >>
  metis_tac[gas_origin_ptr_path_append, APPEND]
QED

Theorem calldata_bulk_decoder_endpoint_ptr_uniform:
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) sa = ((),sb) /\
  ~dec_info_needs_clamp ei /\ lookup_var root s = SOME (n2w d) /\
  eval_operand src s = SOME a /\ abi_decode_load CALLDATALOAD a s = n2w n /\
  not_fresh_at sa root /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  ptr_covers G tn root s capacity /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  32+n*mem_sz <= capacity /\ d+32 < dimword (:256) /\ n*mem_sz < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H u.
    ptr_covers H u root t capacity /\ u.t_mem SUBSET tn.t_mem /\
    (!i. d <= i /\ i < d+32+n*mem_sz ==> i NOTIN u.t_mem) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  strip_tac >> drule_all calldata_bulk_decoder_endpoint_ptr_uniform_origin >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`H`,`u`] >> simp[]
QED
