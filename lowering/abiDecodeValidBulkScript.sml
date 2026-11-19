(* Compose the guard, count store and packed copy on one decoder execution. *)
Theory abiDecodeValidBulk
Ancestors
  abiDecodeValidBulkRun abiDecodeValidArrayHeader abiDecodeValidBulkPayload
  abiDecoderArrayLoopInit abiDecoderDynarrayPrefix abiDecoderBulk
  abiDecoderContract abiEncoder abiDecoderComposition bodyPtrBopHashSuffix
  abiDecoderBulkExecute abiValidAllocatedContract abiValidAllocatedObservations
  abiDecodePtrMemberFrame decoderArraySetupPtr
  decoderGhostFramePtr freshWrites
  stateRelProj entrySinkExtraction entryDecoderHistoryFrame ctorAbiActualWorld
  exprPtrCleanBufferPost valueEncodingTyping valueEncodingProps
  abiDecoderReentry abiMalformedSiteFrame abiMalformedRecursiveInterface
  fragExec fragGasOriginPtr instIdxIndep ghostPcTransportPtr
  exprLoweringProps emitHelperProps allocaHistory compileEnv
  bodyPtrDefs ptrDiscipline venomExecSemantics venomInst venomMemDefs venomState
  list rich_list arithmetic finite_map pred_set words valueEncoding valueEncodingDefs

Theorem bulk_decode_actual_cuts[local]:
  compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),en) /\
  ~dec_info_needs_clamp ei /\ fn_has_code st en func /\
  run_inst_seq (emitted_insts st en) s = OK actual ==>
  ?addr c1 cnt c2 r1 r2.
    abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn abi_sz st = (addr,c1) /\
    abi_decode_array_header (Var output) addr MLOAD c1 = (cnt,c2) /\
    abi_decode_bulk_payload (Var output) pos cnt mem_sz MLOAD (Var source) c2 = ((),en) /\
    fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func /\
    c1.cs_current_bb = st.cs_current_bb /\ c2.cs_current_bb = st.cs_current_bb /\
    en.cs_current_bb = st.cs_current_bb /\ isPREFIX st.cs_current_insts en.cs_current_insts /\
    st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts c1 c2) /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c2 en) /\
    EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts c1 c2) /\
    run_inst_seq (emitted_insts st c1) s = OK r1 /\
    run_inst_seq (emitted_insts c1 c2) r1 = OK r2 /\
    run_inst_seq (emitted_insts c2 en) r2 = OK actual
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  `?addr c1 cnt c2.
    abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn abi_sz st = (addr,c1) /\
    abi_decode_array_header (Var output) addr MLOAD c1 = (cnt,c2) /\
    abi_decode_bulk_payload (Var output) pos cnt mem_sz MLOAD (Var source) c2 = ((),en)` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [abi_decode_bulk_phases, abi_decode_bulk_body_def,
       comp_bind_def, LET_THM] >>
     pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
  pop_assum strip_assume_tac >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `inst_extends c2 en /\ same_blocks c2 en` by
    (qpat_x_assum `abi_decode_bulk_payload _ _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def,
          abi_decode_copy_opcode_def, comp_bind_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     rpt (pairarg_tac >> gvs[]) >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     conj_tac >- metis_tac[inst_extends_trans] >> fs[same_blocks_def]) >>
  `cs_extends st c1 /\ cs_extends c1 c2 /\ cs_extends c2 en` by
    (simp[cs_extends_def, same_blocks_def, inst_extends_def] >>
     fs[same_blocks_def, inst_extends_def]) >>
  `fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 en func` by
    metis_tac[cs_extends_trans, fn_has_code_split] >>
  `emitted_insts st en = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 en` by
    (`inst_extends st c2` by metis_tac[inst_extends_trans] >>
     metis_tac[emitted_insts_append, inst_extends_def, APPEND_ASSOC]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c2 en) /\
   EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts c1 c2)` by
    (qpat_assum `EVERY (\i. _ /\ _ /\ _) (emitted_insts st en)` mp_tac >>
     qpat_assum `EVERY (\i. abi_decoder_reentry_opcode _) (emitted_insts st en)` mp_tac >>
     qpat_assum `emitted_insts st en = _` (fn th =>
       simp_tac bool_ss [th, EVERY_APPEND]) >> (simp[EVERY_MEM])) >>
  qpat_x_assum `run_inst_seq (emitted_insts st en) s = OK actual` mp_tac >>
  asm_simp_tac bool_ss [bop_run_inst_seq_append_ok] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK first` >>
  rename1 `run_inst_seq (emitted_insts c1 c2) first = OK second` >>
  `inst_extends st en` by metis_tac[inst_extends_trans] >>
  `isPREFIX st.cs_current_insts en.cs_current_insts` by
    (qpat_x_assum `inst_extends st en` (SUBST1_TAC o REWRITE_RULE [inst_extends_def]) >>
     simp[NoAsms]) >>
  `en.cs_current_bb = st.cs_current_bb` by
    ((qpat_assum `same_blocks c2 en` mp_tac >> simp[same_blocks_def] >> (gvs[same_blocks_def]))) >>
  qexistsl [`addr`,`c1`,`cnt`,`c2`,`first`,`second`] >> simp[] >> fs[EVERY_MEM]
QED

(* Boundary facts for the two allocated buffers, independently of their ghosts. *)
Theorem bulk_decode_buffer_bounds[local]:
  alloca_inv s /\ abi_malformed_allocated_window live B L xs s /\
  abi_malformed_destination func cenv scopes dstid d cap s /\ live <> dstid ==>
  B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
  d+cap <= s.vs_alloca_next /\ (B+L <= d \/ d+cap <= B)
Proof
  simp[abi_malformed_allocated_window_def, abi_malformed_destination_def,
       alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  strip_tac >>
  `B + cap' <= s.vs_alloca_next /\ b + sz <= s.vs_alloca_next /\
   (B+cap' <= b \/ b+sz <= B)` by metis_tac[] >> decide_tac
QED

(* The register and memory behavior at the guard/header boundary is independent
   of the outer entry relation or the value returned by decoding. *)
Theorem bulk_decode_header_ghosts[local]:
  abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn stride st = (addr,c1) /\
  abi_decode_array_header (Var output) addr MLOAD c1 = (cnt,c2) /\
  run_inst_seq (emitted_insts st c1) s = OK r1 /\
  run_inst_seq (emitted_insts c1 c2) r1 = OK r2 /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts c1 c2) /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts c1 c2) /\
  fn_has_code st c1 func /\ fn_has_code c1 c2 func /\
  c1.cs_current_bb = st.cs_current_bb /\ c2.cs_current_bb = st.cs_current_bb /\
  st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ hi <> Lit 0w /\
  not_fresh_at st source /\ not_fresh_at st output /\
  (!x. pos = Var x ==> not_fresh_at st x) /\ (!x. hi = Var x ==> not_fresh_at st x) /\
  abi_decode_ptr_window G tn s source (n2w B) L /\ ptr_covers G tn output s cap /\
  lookup_var output s = SOME (n2w d) /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w L) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\ allocas_from lo s /\
  p < dimword (:256) /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
  maxn < dimword (:256) /\ maxn*stride < dimword (:256) /\
  32 <= cap /\ d+cap < dimword (:256) /\ d+cap <= s.vs_alloca_next /\
  (B+L <= d \/ d+cap <= B) ==>
  ?G2 tn2.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (r2 with vs_inst_idx := LENGTH c2.cs_current_insts),G2,tn2)) /\
    ~(r2 with vs_inst_idx := LENGTH c2.cs_current_insts).vs_halted /\
    (r2 with vs_inst_idx := LENGTH c2.cs_current_insts).vs_current_bb = c2.cs_current_bb /\
    (r2 with vs_inst_idx := LENGTH c2.cs_current_insts).vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo (r2 with vs_inst_idx := LENGTH c2.cs_current_insts) /\
    lookup_var output (r2 with vs_inst_idx := LENGTH c2.cs_current_insts) = SOME (n2w d) /\
    ptr_covers G2 tn2 output (r2 with vs_inst_idx := LENGTH c2.cs_current_insts) cap /\
    abi_decode_ptr_window G2 tn2 (r2 with vs_inst_idx := LENGTH c2.cs_current_insts) source (n2w B) L
      /\
    eval_operand pos (r2 with vs_inst_idx := LENGTH c2.cs_current_insts) = SOME (n2w p) /\
    eval_operand cnt (r2 with vs_inst_idx := LENGTH c2.cs_current_insts) = SOME (mload (B+p) s) /\
    op_prov G2 pos = NONE /\ op_prov G2 cnt = NONE /\
    op_taint tn2 pos = {} /\ op_taint tn2 cnt = {} /\
    w2n (mload (B+p) s) <= maxn /\ p+32+w2n (mload (B+p) s)*stride <= L /\
    (!x. not_fresh_at st x ==> FLOOKUP G2 x = FLOOKUP G x /\
       op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    tn2.t_mem = tn.t_mem DIFF {x | d <= x /\ x < d+32} /\
    tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_dynarray_position_prefix_success_joint >>
  disch_then (qspec_then `PG` (qx_choose_then `ar` (qx_choose_then `G1`
    (qx_choose_then `tn1` (map_every assume_tac o CONJUNCTS))))) >>
  qpat_x_assum `addr = Var ar` SUBST_ALL_TAC >>
  qabbrev_tac `s1 = r1 with vs_inst_idx := LENGTH c1.cs_current_insts` >>
  qabbrev_tac `u2 = r2 with vs_inst_idx := LENGTH c1.cs_current_insts` >>
  `run_inst_seq (emitted_insts c1 c2) s1 = OK u2` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2)` by fs[EVERY_MEM] >>
     simp[Abbr `s1`, Abbr `u2`, run_inst_seq_inst_idx, exec_result_map_def]) >>
  `~s1.vs_halted /\ s1.vs_current_bb = c1.cs_current_bb /\
   s1.vs_inst_idx = LENGTH c1.cs_current_insts /\ s1.vs_alloca_next = s.vs_alloca_next /\
   s1.vs_labels = s.vs_labels /\ mload (B+p) s1 = mload (B+p) s` by
    (qpat_assum `r1 = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[Abbr `s1`, mload_def] >>
     qpat_assum `r1 = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `abi_decode_ptr_window G1 tn1 s1 ar (n2w (B+p)) 32 /\
   abi_decode_ptr_window G1 tn1 s1 source (n2w B) L /\ allocas_from lo s1` by
    (fs[Abbr `s1`, abi_decode_ptr_window_def, lookup_var_def, allocas_from_def] >> (metis_tac[Abbr `s1`, abi_decode_ptr_window_def, lookup_var_def, allocas_from_def])) >>
  `lookup_var output s1 = SOME (n2w d) /\ ptr_covers G1 tn1 output s1 cap` by
    (qpat_assum `!x. not_fresh_at st x ==> _` (qspec_then `output` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
     >- (simp[Abbr `s1`, lookup_var_def] >> metis_tac[lookup_var_def]) >>
     irule ptr_covers_frame >> qexistsl [`G`,`s`,`tn`] >>
     simp[Abbr `s1`, lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `not_fresh_at c1 output /\ not_fresh_at c1 source /\
   (!x. pos = Var x ==> not_fresh_at c1 x)` by
    metis_tac[not_fresh_at_mono] >>
  `B+p+32 < dimword (:256) /\ B+p+32 <= s1.vs_alloca_next` by decide_tac >>
  `d+cap <= s1.vs_alloca_next` by simp[] >>
  `r1.vs_labels = s.vs_labels` by gvs[Abbr `s1`] >>
  `eval_operand pos s1 = SOME (n2w p) /\ op_prov G1 pos = NONE /\ op_taint tn1 pos = {}` by
    (mp_tac (Q.INST [`op` |-> `pos`, `t` |-> `r1`, `HG` |-> `G1`,
                    `u` |-> `tn1`] old_operand_ghost_frame) >>
     simp[Abbr `s1`, eval_op_inst_idx]) >>
  drule_all abi_decode_array_header_success_joint >>
  disch_then (qspec_then `PG` (qx_choose_then `G2` (qx_choose_then `tn2`
    (map_every assume_tac o CONJUNCTS o SRULE [])))) >>
  `r2.vs_halted = r1.vs_halted /\ r2.vs_current_bb = r1.vs_current_bb` by
    metis_tac[run_inst_seq_preserves_entry_control] >>
  `u2.vs_labels = s1.vs_labels` by
    (drule_all abi_valid_allocated_sequence_static >> simp[Abbr `u2`, Abbr `s1`]) >>
  `eval_operand pos u2 = SOME (n2w p) /\ op_prov G2 pos = NONE /\ op_taint tn2 pos = {}` by
    (mp_tac (Q.INST [`op` |-> `pos`, `s` |-> `s1`, `t` |-> `u2`,
                    `st` |-> `c1`, `HG` |-> `G2`, `u` |-> `tn2`,
                    `G` |-> `G1`, `tn` |-> `tn1`] old_operand_ghost_frame) >> simp[]) >>
  `abi_decode_ptr_window G2 tn2 u2 source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >> qexistsl [`G1`,`s1`,`tn1`] >>
     qpat_assum `!x. not_fresh_at c1 x ==> _` (qspec_then `source` mp_tac) >>
     simp[w2n_n2w, IN_DIFF] >> decide_tac) >>
  qexistsl [`G2`,`tn2`] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (r2 with vs_inst_idx := LENGTH c2.cs_current_insts),G2,tn2)` by
    (rpt gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s1,G1,tn1)` by
       simp[Abbr `s1`] >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s1,G1,tn1) []
        (OK (r2 with vs_inst_idx := LENGTH c2.cs_current_insts),G2,tn2)` by
       (simp[Abbr `u2`] >> (gvs[])) >>
     metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  `lookup_var output u2 = SOME (n2w d)` by
    (qpat_assum `!x. not_fresh_at c1 x ==> _` (qspec_then `output` mp_tac) >> simp[]) >>
  `!x. not_fresh_at st x ==> FLOOKUP G2 x = FLOOKUP G x /\
      op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at c1 x` by metis_tac[not_fresh_at_mono] >>
     metis_tac[]) >>
  gvs[Abbr `u2`, Abbr `s1`, lookup_var_def, eval_op_inst_idx,
      allocas_from_def, abi_decode_ptr_window_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_valid_allocated_joint_bulk:
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei ==>
  !v ctx func cenv cx es st en source hi pos output B L xs p d dstid live ceiling s H0.
  abi_valid_allocated_entry H0 ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) v ctx func cenv cx es st en (Var source) hi
    pos (Var output) B L xs p d dstid live ceiling s ==>
  !G tn PG lo.
  ~ctx_has_dalloca ctx /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
  ?u G' tn'.
    abi_valid_allocated_post (ArrayTV tv (Dynamic maxn)) v ctx func cenv cx es st en
      ceiling dstid d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s u /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,G',tn')) /\
    ptr_covers G' tn' output u (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
    abi_decode_ptr_window G' tn' u source (n2w B) L /\
    (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) v d mem) /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!a. ~(d <= a /\ a < d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
      ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
      (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
    alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next
Proof
  strip_tac >> rpt gen_tac >> disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_valid_allocated_bulk_reach_run >>
  disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
  drule_all abi_valid_allocated_bulk_count >>
  disch_then (qx_choose_then `vs` (map_every assume_tac o CONJUNCTS)) >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  `DecDynArray ei abi_sz mem_sz F maxn = type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))` by simp[] >>
  drule_all abi_decoder_bulk_metadata >> strip_tac >>
  `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
     (DecDynArray ei abi_sz mem_sz F maxn) st = ((),en)` by fs[] >>
  drule_all bulk_decode_actual_cuts >>
  disch_then (qx_choose_then `addr` (qx_choose_then `c1` (qx_choose_then `cnt`
    (qx_choose_then `c2` (qx_choose_then `r1` (qx_choose_then `r2`
      (map_every assume_tac o CONJUNCTS))))))) >>
  qabbrev_tac `cap = type_memory_bytes ce (ArrayT ty (Dynamic maxn))` >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  drule_all bulk_decode_buffer_bounds >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_var output s = SOME (n2w d)` by fs[eval_operand_def] >>
  `not_fresh_at st source /\ not_fresh_at st output /\
   (!x. pos = Var x ==> not_fresh_at st x) /\ (!x. hi = Var x ==> not_fresh_at st x)` by
    (qpat_assum `EVERY (abi_decoder_operand_live st.cs_next_var) _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `pos` >> Cases_on `hi` >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `maxn*abi_sz < dimword (:256) /\ 32 <= cap` by
    (`abi_sz = mem_sz` by simp[] >>
     qpat_assum `d+cap < dimword (:256)` mp_tac >>
     qpat_assum `cap = _ + _` (fn th => pure_rewrite_tac[th]) >>
     simp[] >> decide_tac) >>
  drule_all bulk_decode_header_ghosts >>
  disch_then (qspec_then `PG` (qx_choose_then `G2` (qx_choose_then `tn2`
    (map_every assume_tac o CONJUNCTS o BETA_RULE o PURE_REWRITE_RULE [LET_THM])))) >>
  qabbrev_tac `s2 = r2 with vs_inst_idx := LENGTH c2.cs_current_insts` >>
  qabbrev_tac `t = actual with vs_inst_idx := LENGTH c2.cs_current_insts` >>
  `s2.vs_inst_idx = LENGTH c2.cs_current_insts /\
   run_inst_seq (emitted_insts c2 en) s2 = OK t` by
    simp[Abbr `s2`, Abbr `t`, run_inst_seq_inst_idx, exec_result_map_def] >>
  `not_fresh_at c2 source /\ not_fresh_at c2 output /\
   (!x. pos = Var x ==> not_fresh_at c2 x)` by
    (`st.cs_next_var <= c2.cs_next_var` by decide_tac >> metis_tac[not_fresh_at_mono]) >>
  `LENGTH vs < dimword (:256)` by decide_tac >>
  `LENGTH vs * mem_sz <= maxn * mem_sz` by simp[LE_MULT_RCANCEL] >>
  `B+p+32 < dimword (:256) /\ d+32 < dimword (:256) /\
   LENGTH vs * mem_sz < dimword (:256) /\
   B+L <= s2.vs_alloca_next /\ d+cap <= s2.vs_alloca_next /\
   p+32+LENGTH vs*mem_sz <= L /\ 32+LENGTH vs*mem_sz <= cap` by
    (`p+32+LENGTH vs*mem_sz <= L` by
       (qpat_assum `p + 32 + w2n (mload (B+p) s)*abi_sz <= L` mp_tac >>
        gvs[w2n_n2w]) >>
     `maxn * mem_sz < dimword (:256)` by
       (qpat_assum `maxn * abi_sz < dimword (:256)` mp_tac >> gvs[]) >>
     qpat_assum `s2.vs_alloca_next = s.vs_alloca_next` (fn th => rewrite_tac[th]) >>
     decide_tac) >>
  `eval_operand cnt s2 = SOME (n2w (LENGTH vs))` by simp[] >>
  drule_all abi_decode_bulk_payload_success_joint >>
  disch_then (qspec_then `PG` (qx_choose_then `G3` (qx_choose_then `tn3`
    (map_every assume_tac o CONJUNCTS)))) >>
  qabbrev_tac `u = actual with vs_inst_idx := LENGTH en.cs_current_insts` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK u,G3,tn3)` by
    (rpt gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s2,G2,tn2)` by simp[] >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s2,G2,tn2) [] (OK u,G3,tn3)` by
       gvs[Abbr `t`, Abbr `u`] >>
     metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  `!i. d <= i /\ i < d+32+LENGTH vs*mem_sz ==> i NOTIN tn3.t_mem` by
    (simp[IN_DIFF] >> decide_tac) >>
  `!mem. mem_agree_outside tn3.t_mem u.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) v d mem` by
    (`val_in_memory (ArrayTV tv (Dynamic (LENGTH vs))) (ArrayV (DynArrayV vs)) d u.vs_memory` by
       fs[abi_valid_allocated_post_def, val_in_memory_dynarray] >>
     `val_wf (ArrayTV tv (Dynamic (LENGTH vs))) (ArrayV (DynArrayV vs))` by
       simp[val_wf_def, cj 4 value_has_type_val_wf] >>
     rpt strip_tac >>
     `val_in_memory (ArrayTV tv (Dynamic (LENGTH vs))) (ArrayV (DynArrayV vs)) d mem` by
       (irule clean_window_value_robust >> conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl [`tn3.t_mem`,`u.vs_memory`,`32+LENGTH vs*mem_sz`] >>
        conj_tac >-
          (rpt gen_tac >> disch_tac >>
           qpat_assum `!i. _ ==> i NOTIN tn3.t_mem` irule >> decide_tac) >>
        conj_tac >-
          (qpat_assum `mem_sz = type_memory_size tv` (fn th => rewrite_tac[th]) >>
           once_rewrite_tac[type_memory_size_def] >> simp[NoAsms]) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     fs[val_in_memory_dynarray]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  drule_all abi_valid_allocated_sequence_static >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en)` by fs[EVERY_MEM] >>
  `alloca_history func u` by
    (simp[Abbr `u`] >> irule entry_straight_line_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >> qexistsl [`s`,`st`] >> simp[]) >>
  `!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
    FLOOKUP G3 x = FLOOKUP G x /\ op_taint tn3 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at st x` by fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
     `st.cs_next_var <= c2.cs_next_var` by decide_tac >>
     `not_fresh_at c2 x` by metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  `ptr_covers G3 tn3 output u cap /\
   abi_decode_ptr_window G3 tn3 u source (n2w B) L /\ allocas_from lo u` by
    (qpat_assum `ptr_covers G3 tn3 output t cap` mp_tac >>
     qpat_assum `abi_decode_ptr_window G3 tn3 t source _ _` mp_tac >>
     qpat_assum `allocas_from lo t` mp_tac >>
     simp[NoAsms, Abbr `t`, Abbr `u`, abi_decode_ptr_window_def, lookup_var_def,
          allocas_from_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!a. ~(d <= a /\ a < d+cap) ==> (a IN tn3.t_mem <=> a IN tn.t_mem)` by
    ((qx_gen_tac `a` >> disch_tac >>
     `~(d <= a /\ a < d+32) /\ ~(d+32 <= a /\ a < d+32+LENGTH vs*mem_sz)` by decide_tac >>
     simp[IN_DIFF] >> (gvs[]))) >>
  qexistsl [`u`,`G3`,`tn3`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[Abbr `u`]
QED
