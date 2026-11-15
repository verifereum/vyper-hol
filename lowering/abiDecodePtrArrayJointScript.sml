(* The actual memory array count load/store carries one joint endpoint. *)
Theory abiDecodePtrArrayJoint
Ancestors
 abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiMalformedBulkArray
 abiDecodePtrBytesMember abiDecodePtrRead abiDecodePtrScalarFrame abiDecodePtrPrims
 bodyPtrBopScalarCompile bodyPtrBopScalarSeq bodyPtrBopScalarOutcome
 abiDecoderBytesBound abiDecoderRange abiDecoderGuard abiDecoderVarSequence
 abiDecoderContract abiDecoderGuards emitHelper abiDecoderReentryPointer stateFrame
 assignTuplePtrLocalBytesCopy instSeqComposePtr
 abiDecodePtrReentry abiDecodePtrReentryGhost abiDecodeMemReentry
 fragGasCopyLoop fragGasOriginPtrDead entryDecoderHistoryFrame
 abiDecoderReentry abiDecoderVarExtend abiDecoderAbortReentry
 abiDecoderArrayHeader abiDecodePtrMemberFrame decoderNavigationPtr
 decoderGhostFramePtr ghostPcTransportPtr bodyFullUnwrapRun bodyPtrBopHashSuffix fragGasOriginPtr ptrSafetyTransport
 wordLoadStorePtr valueCopy allocaFootprint emitHelperProps exprLoweringProps
 abiEncoder compileEnv loweringStateRelDefs bodyPtrDefs ptrDiscipline fragExecMem fragExec fragGasSeqPtr
 venomExecSemantics venomState venomInst venomMemDefs instIdxIndep
 finite_map pred_set words list rich_list arithmetic fragExecPtr moduleLoweringProps

Theorem abi_decode_array_header_success_joint:
 abi_decode_array_header (Var output) (Var addr) MLOAD sa = (cnt,sb) /\
 run_inst_seq (emitted_insts sa sb) s = OK u /\
 fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 not_fresh_at sa output /\ not_fresh_at sa addr /\
 lookup_var output s = SOME (n2w d) /\
 abi_decode_ptr_window G tn s addr (n2w a) 32 /\
 ptr_covers G tn output s cap /\ 32 <= cap /\
 a+32 < dimword (:256) /\ d+cap < dimword (:256) /\
 a+32 <= s.vs_alloca_next /\ d+cap <= s.vs_alloca_next /\
 allocas_from lo s ==>
 ?G' tn'.
 (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
   (s,G,tn) [] (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
 ptr_covers G' tn' output u cap /\
 abi_decode_ptr_window G' tn' u output (n2w d) 32 /\
 op_prov G' cnt = NONE /\ op_taint tn' cnt = {} /\
 eval_operand cnt u = SOME (mload a s) /\
 (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
   FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
 tn'.t_mem = tn.t_mem DIFF {x | d <= x /\ x < d+32} /\
 tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
 u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
 allocas_from lo u
Proof
 strip_tac >>
 `?middle. emit_op MLOAD [Var addr] sa = (cnt,middle) /\
    emit_void MSTORE [Var output;cnt] middle = ((),sb)` by
   (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
    simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
    pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> metis_tac[]) >>
 drule emitted_insts_emit_op >> strip_tac >>
 drule emitted_insts_emit_void >> strip_tac >>
 `inst_extends sa middle /\ inst_extends middle sb` by
   metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
 `same_blocks sa middle /\ same_blocks middle sb` by
   metis_tac[emit_op_extends, emit_void_extends] >>
 `cs_extends sa middle /\ cs_extends middle sb` by
   (conj_tac >> irule cs_extends_same_block >>
    fs[inst_extends_def, same_blocks_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
 `fn_has_code sa middle func /\ fn_has_code middle sb func` by
   metis_tac[fn_has_code_split] >>
 `emitted_insts sa sb = emitted_insts sa middle ++ emitted_insts middle sb` by
   (irule emitted_insts_append >> fs[inst_extends_def]) >>
 `?loaded. run_inst_seq (emitted_insts sa middle) s = OK loaded /\
    run_inst_seq (emitted_insts middle sb) loaded = OK u` by
   (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK u` mp_tac >>
    qpat_assum `emitted_insts sa sb = _`
      (fn th => pure_rewrite_tac[th, bop_run_inst_seq_append_ok]) >> simp[]) >>
 `a < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
 `lookup_var addr s = SOME (n2w a) /\ ptr_covers G tn addr s 32 /\
    (!i. a <= i /\ i < a+32 ==> i NOTIN tn.t_mem)` by
   fs[abi_decode_ptr_window_def] >>
 mp_tac (Q.SPECL [`sa`, `cnt`, `middle`, `addr`, `s`, `loaded`, `n2w a`,
    `G`, `tn`, `ARB`, `ctx`, `PG`, `ARB`]
    emit_mload_clean_endpoint_ptr_origin_core) >>
 (impl_tac >- simp[w2n_n2w]) >>
 disch_then (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)) >>
 qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
 qpat_x_assum `!D lower ctx' func. _ ==> !fuel. ptr_safe_run _ _ _ _ _ _ _ _ _` kall_tac >>
 `loaded = update_var (STRING #"%" (toString sa.cs_next_var)) (mload a s) s` by
   (qpat_x_assum `run_inst_seq (emitted_insts sa middle) s = OK loaded` mp_tac >>
    simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
     exec_read1_def, eval_operand_def, w2n_n2w]) >>
 `output <> STRING #"%" (toString sa.cs_next_var)` by
   metis_tac[not_fresh_at_def, LESS_EQ_REFL] >>
 `lookup_var output loaded = SOME (n2w d) /\
  eval_operand cnt loaded = SOME (mload a s)` by
   simp[eval_operand_def, lookup_var_update_var] >>
 `u = mstore d (mload a s) loaded` by
   (qpat_x_assum `run_inst_seq (emitted_insts middle sb) loaded = OK u` mp_tac >>
    simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_write2_def, eval_operand_def, lookup_var_update_var, w2n_n2w]) >>
 `loaded.vs_alloca_next = s.vs_alloca_next /\
  loaded.vs_halted = s.vs_halted /\ loaded.vs_current_bb = s.vs_current_bb` by
   simp[update_var_def] >>
 qabbrev_tac `prepared = loaded with vs_inst_idx := LENGTH middle.cs_current_insts` >>
 qabbrev_tac `inst = mk_inst middle.cs_next_id MSTORE [Var output;cnt] []` >>
 qabbrev_tac `stored = mstore d (mload a s) prepared` >>
 qabbrev_tac `tn2 = step_taint inst prepared stored tn1` >>
 `ptr_covers G1 tn1 output prepared cap /\
    lookup_var output prepared = SOME (n2w d) /\
    eval_operand cnt prepared = SOME (mload a s) /\
    prepared.vs_allocas = s.vs_allocas /\ prepared.vs_alloca_next = s.vs_alloca_next /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts` by
   (conj_tac
    >- (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
        simp[Abbr `prepared`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
        fs[lookup_var_def]) >>
    simp[Abbr `prepared`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
    fs[same_blocks_def, lookup_var_def]) >>
 `step_prov PG G1 inst stored = G1 /\
    tn2.t_var = tn1.t_var /\ tn2.t_stor = tn1.t_stor /\
    tn2.t_trans = tn1.t_trans /\
    tn2.t_mem = tn1.t_mem DIFF {i | d <= i /\ i < d+32}` by
   (mp_tac (Q.SPECL [`PG`, `G1`, `tn1`, `prepared`, `middle.cs_next_id`,
      `output`, `cnt`, `n2w d`, `mload a s`] mstore_ghost_frame) >>
    simp[Abbr `inst`, Abbr `stored`, Abbr `tn2`, w2n_n2w]) >>
 `tn2.t_imm = tn1.t_imm` by
   simp[Abbr `tn2`, Abbr `inst`, step_taint_def, imm_taint_def, mk_inst_def] >>
 `allocas_from lo prepared` by (fs[allocas_from_def] >> metis_tac[]) >>
 `ptr_covers G1 tn1 output prepared 32` by
   (qpat_assum `ptr_covers G1 tn1 output prepared cap` mp_tac >>
    qpat_assum `32 <= cap` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
    simp[ptr_covers_def] >> rpt strip_tac >>
    rename1 `FLOOKUP G1 output = SOME (site,capacity)` >>
    rename1 `lookup_var output prepared = SOME address` >>
    qexistsl_tac [`address`, `site`, `capacity`] >> simp[] >> decide_tac) >>
 `run_inst_seq (emitted_insts middle sb) prepared = OK stored` by
   (mp_tac (Q.SPECL [`middle`, `sb`, `Var output`, `cnt`, `prepared`,
      `n2w d`, `mload a s`] emit_mstore_run) >>
    (impl_tac >- simp[eval_operand_def]) >> simp[Abbr `stored`, w2n_n2w]) >>
 `step_inst_base inst prepared = OK stored` by
   (qpat_x_assum `run_inst_seq (emitted_insts middle sb) prepared = OK stored` mp_tac >>
    simp[run_inst_seq_def] >> Cases_on `step_inst_base inst prepared` >> simp[]) >>
 `inst.inst_opcode = MSTORE` by simp[Abbr `inst`, mk_inst_def] >>
 `run_inst_seq_mem_ok (emitted_insts middle sb) prepared` by
   (drule emit_mstore_mem_ok >> disch_then irule >>
    qexists_tac `n2w d` >> simp[eval_operand_def, w2n_n2w] >> decide_tac) >>
 `sb.cs_current_bb = middle.cs_current_bb` by fs[same_blocks_def] >>
 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (prepared,G1,tn1) [] (OK (stored with vs_inst_idx := LENGTH sb.cs_current_insts),G1,tn2)` by
   (rpt gen_tac >> mp_tac (Q.SPECL [`emitted_insts middle sb`, `middle`, `sb`,
      `prepared`, `stored`, `G1`, `tn1`, `G1`, `tn2`] emitted_origin_ptr_path) >>
    (impl_tac >-
      (simp[is_terminator_def, inst_seq_ptr_def, Abbr `tn2`] >>
       irule (ptr_inst_ok_lower_bound_transport |> Q.INST [`lo0` |-> `0`]) >>
       simp[Abbr `inst`] >> irule ptr_inst_ok_mstore >> gvs[])) >> simp[]) >>
 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G1,tn2)` by
   (rpt gen_tac >>
    `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK prepared,G1,tn1)` by
      (simp[Abbr `prepared`] >> first_x_assum irule >> simp[w2n_n2w]) >>
    `stored with vs_inst_idx := LENGTH sb.cs_current_insts =
       u with vs_inst_idx := LENGTH sb.cs_current_insts` by
      simp[Abbr `stored`, Abbr `prepared`, mstore_def, write_memory_with_expansion_def] >>
    metis_tac[gas_origin_ptr_path_append, APPEND]) >>
 `u.vs_vars = loaded.vs_vars /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
   simp[mstore_def, update_var_def] >>
 `!operand. op_taint tn2 operand = op_taint tn1 operand` by
   (Cases_on `operand` >> simp[op_taint_def]) >>
 `!x. lookup_var x u = lookup_var x loaded` by simp[lookup_var_def] >>
 `!operand. eval_operand operand u = eval_operand operand loaded` by
   (Cases_on `operand` >> simp[eval_operand_def]) >>
 `!x. lookup_var x u = lookup_var x prepared` by
   simp[Abbr `prepared`, lookup_var_def] >>
 `ptr_covers G1 tn2 output u cap /\ ptr_covers G1 tn2 output u 32` by
   (conj_tac >> irule ptr_covers_frame >>
    qexistsl_tac [`G1`, `prepared`, `tn1`] >> simp[]) >>
 qpat_x_assum `!x. lookup_var x u = lookup_var x prepared` kall_tac >>
 `abi_decode_ptr_window G1 tn2 u output (n2w d) 32` by
   (simp[abi_decode_ptr_window_def, w2n_n2w] >> rpt strip_tac >> simp[]) >>
 `allocas_from lo u` by
   (qpat_assum `allocas_from lo s` mp_tac >>
    qpat_assum `u.vs_allocas = s.vs_allocas` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[allocas_from_def]) >>
 qexistsl_tac [`G1`, `tn2`] >> asm_rewrite_tac[] >>
 simp[] >> rpt strip_tac >>
 qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >>
 (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[]
QED

Theorem abi_decode_dynarray_payload_guard_scalar[local]:
 abi_decode_dynarray_payload_guard head cnt stride hi sa = ((),sb) /\
 hi <> Lit 0w /\ head IN A /\ cnt IN A /\ hi IN A /\
 Lit (n2w stride) IN A /\ (!x. x IN R ==> not_fresh_at sa x) ==>
 ?B. bop_scalar_seq R A (emitted_insts sa sb) B /\ A SUBSET B
Proof
 strip_tac >>
 qpat_x_assum `abi_decode_dynarray_payload_guard _ _ _ _ _ = _` mp_tac >>
 simp[abi_decode_dynarray_payload_guard_def, comp_bind_def] >>
 pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
 rename1 `emit_op MUL [cnt; Lit (n2w stride)] sa = (payload,c1)` >>
 rename1 `emit_op ADD [head;payload] c1 = (e,c2)` >>
 `bop_scalar_seq R A (emitted_insts sa c1) (payload INSERT A)` by
   (qpat_assum `emit_op MUL _ _ = _`
      (mp_then Any mp_tac bop_scalar_seq_emit_op) >>
    disch_then (qspecl_then [`R`, `A`] mp_tac) >> simp[]) >>
 `!x. x IN R ==> not_fresh_at c1 x` by
   (qpat_assum `emit_op MUL _ _ = _`
      (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
    fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
 `!x. x IN R ==> not_fresh_at c2 x` by
   (qpat_assum `emit_op ADD _ _ = _`
      (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
    fs[not_fresh_at_def] >> rpt strip_tac >>
    metis_tac[DECIDE ``a+1 <= n ==> a <= n``]) >>
 `bop_scalar_seq R (payload INSERT A) (emitted_insts c1 c2)
    (e INSERT payload INSERT A)` by
   (qpat_assum `emit_op ADD _ _ = _`
      (mp_then Any mp_tac bop_scalar_seq_emit_op) >>
    disch_then (qspecl_then [`R`, `payload INSERT A`] mp_tac) >> simp[]) >>
 `?B. bop_scalar_seq R (e INSERT payload INSERT A)
    (emitted_insts c2 sb) B` by
   (drule abi_decode_range_scalar >>
    disch_then (qspecl_then [`R`, `e INSERT payload INSERT A`] mp_tac) >> simp[]) >>
 `inst_extends sa c1 /\ inst_extends c1 c2 /\ inst_extends c2 sb` by
   metis_tac[inst_extends_emit_op, compile_abi_decode_range_check_shape] >>
 `inst_extends sa c2` by metis_tac[inst_extends_trans] >>
 `emitted_insts sa c2 = emitted_insts sa c1 ++ emitted_insts c1 c2 /\
  emitted_insts sa sb = emitted_insts sa c2 ++ emitted_insts c2 sb` by
   (conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
 `bop_scalar_seq R A (emitted_insts sa c2) (e INSERT payload INSERT A)` by
   metis_tac[bop_scalar_seq_append] >>
 `bop_scalar_seq R A (emitted_insts sa sb) B` by
   metis_tac[bop_scalar_seq_append] >>
 qexists_tac `B` >> simp[] >> metis_tac[bop_scalar_seq_available]
QED

Theorem abi_decode_dynarray_position_prefix_joint_code:
 abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn stride sa = (addr,sb) ==>
 inst_extends sa sb /\ same_blocks sa sb /\
 sa.cs_next_var <= sb.cs_next_var /\
 EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
   i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
 strip_tac >>
 `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
 simp[same_blocks_def] >>
 qpat_x_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _` mp_tac >>
 Cases_on `hi = Lit 0w` >>
 simp[abi_decode_dynarray_position_prefix_def, abi_decode_bytes_head_def,
   compile_abi_dec_addr_def, abi_decode_count_guard_def,
   abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
   comp_bind_def, comp_ignore_bind_def, comp_return_def,
   emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
 strip_tac >> gvs[emitted_insts_def] >>
 pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
 simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def,
   is_terminator_def]
QED


Theorem abi_decode_dynarray_position_prefix_fresh_ptr[local]:
 abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn stride sa = (addr,sb) /\
 run_inst_seq (emitted_insts sa sb) s = OK u /\ fresh_vars_wrt sa s /\
 fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 not_fresh_at sa source /\ hi <> Lit 0w /\
 abi_decode_ptr_window G tn s source (n2w B) L /\
 eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w L) /\
 op_prov G pos = NONE /\ op_prov G hi = NONE /\
 op_taint tn pos = {} /\ op_taint tn hi = {} /\
 p < dimword (:256) /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
 maxn < dimword (:256) /\ maxn*stride < dimword (:256) ==>
 ?ar G' tn'. addr = Var ar /\
 inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
 run_inst_seq_mem_ok (emitted_insts sa sb) s /\
 u = s with vs_vars := u.vs_vars /\
 abi_decode_ptr_window G' tn' u source (n2w B) L /\
 abi_decode_ptr_window G' tn' u ar (n2w (B+p)) 32 /\
 not_fresh_at sb ar /\
 w2n (mload (B+p) s) <= maxn /\
 p+32+w2n (mload (B+p) s)*stride <= L /\
 (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
   FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
 tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
 tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
 strip_tac >>
 `B < dimword (:256) /\ L < dimword (:256)` by decide_tac >>
 `eval_operand (Var source) s = SOME (n2w B)` by
   fs[abi_decode_ptr_window_def, eval_operand_def] >>
 `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_malformed_dynarray_prefix_total >> strip_tac
 >- gvs[] >>
 `w2n (mload (B+p) s) <= maxn /\
  p+32+w2n (mload (B+p) s)*stride <= L` by
   gvs[abi_decode_load_def, w2n_n2w, mload_def] >>
 `p+32 <= L` by decide_tac >>
 qpat_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _`
   (strip_assume_tac o REWRITE_RULE [abi_decode_dynarray_position_prefix_trace]) >>
 rename1 `abi_decode_bytes_head pos hi sa = (head,c1)` >>
 rename1 `compile_abi_dec_addr (Var source) pos c1 = (addr,c2)` >>
 rename1 `abi_decode_count_guard MLOAD addr maxn c2 = (cnt,c4)` >>
 qpat_assum `abi_decode_count_guard _ _ _ _ = _`
   (strip_assume_tac o REWRITE_RULE [abi_decode_count_guard_trace]) >>
 rename1 `emit_op MLOAD [addr] c2 = (cnt,c3)` >>
 `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c3.cs_next_var /\
  c3.cs_next_var <= c4.cs_next_var /\ c4.cs_next_var <= sb.cs_next_var` by
   (qpat_x_assum `abi_decode_bytes_head _ _ sa = _` mp_tac >>
    qpat_x_assum `compile_abi_dec_addr _ _ c1 = _` mp_tac >>
    qpat_x_assum `abi_decode_le_guard _ _ c3 = _` mp_tac >>
    qpat_x_assum `abi_decode_dynarray_payload_guard _ _ _ _ c4 = _` mp_tac >>
    qpat_x_assum `emit_op MLOAD _ c2 = _` mp_tac >>
    qpat_assum `hi <> Lit 0w` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
    simp[abi_decode_bytes_head_def, compile_abi_dec_addr_def, abi_decode_le_guard_def,
      abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
    rpt strip_tac >> gvs[]) >>
 drule_all abi_decode_bytes_head_sequence >> strip_tac >>
 rename1 `run_inst_seq (emitted_insts sa c1) s = OK sh` >>
 `?A1. bop_scalar_seq {x | not_fresh_at sa x}
    ({pos;hi} UNION IMAGE Lit UNIV) (emitted_insts sa c1) A1 /\
    ({pos;hi} UNION IMAGE Lit UNIV) SUBSET A1 /\ head IN A1` by
   (irule abi_decode_bytes_head_scalar >> simp[] >> metis_tac[]) >>
 `!op. op IN {pos;hi} UNION IMAGE Lit UNIV ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
   (simp[IN_UNION, IN_IMAGE] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
 drule_all abi_decode_scalar_success_frame >>
 disch_then (qspecl_then [`LENGTH c1.cs_current_insts`, `func`, `PG`, `D`]
   strip_assume_tac) >>
 rename1 `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa c1) s G1 tn1` >>
 qabbrev_tac `s1 = sh with vs_inst_idx := LENGTH c1.cs_current_insts` >>
 `abi_decode_ptr_window G1 tn1 s1 source (n2w B) L` by
   (qpat_assum `!x b h. x IN {x | not_fresh_at sa x} /\ _ ==> _` irule >> simp[]) >>
 `op_prov G1 head = NONE /\ op_taint tn1 head = {} /\
  op_prov G1 hi = NONE /\ op_taint tn1 hi = {}` by
   (fs[SUBSET_DEF] >> metis_tac[]) >>
 drule abi_decode_bytes_head_fragment_shape >> strip_tac >>
 `emit_op ADD [Var source;pos] c1 = (addr,c2)` by fs[compile_abi_dec_addr_def] >>
 imp_res_tac emit_op_extends >> imp_res_tac inst_extends_emit_op >>
 drule abi_decode_le_guard_shape >> strip_tac >>
 `sb.cs_blocks = c4.cs_blocks /\ sb.cs_current_bb = c4.cs_current_bb /\
  inst_extends c4 sb` by
   (qpat_x_assum `abi_decode_dynarray_payload_guard _ _ _ _ _ = _` mp_tac >>
    simp[abi_decode_dynarray_payload_guard_def, comp_bind_def] >>
    pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    drule compile_abi_decode_range_check_fragment_shape >> strip_tac >>
    imp_res_tac emit_op_extends >> imp_res_tac inst_extends_emit_op >>
    fs[same_blocks_def] >> metis_tac[inst_extends_trans]) >>
 `same_blocks c3 c4` by
   (qpat_x_assum `abi_decode_le_guard _ _ c3 = _` mp_tac >>
    simp[abi_decode_le_guard_def, comp_bind_def, comp_ignore_bind_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, comp_return_def,
      emit_def] >> strip_tac >> gvs[same_blocks_def]) >>
 `inst_extends sa c3 /\ inst_extends c1 c3 /\
  inst_extends c1 sb /\ inst_extends c3 sb /\ inst_extends sa sb` by
   metis_tac[inst_extends_trans] >>
 `cs_extends sa c1 /\ cs_extends c1 c3 /\ cs_extends c3 sb` by
   (rpt conj_tac >> irule cs_extends_same_block >>
    fs[inst_extends_def, same_blocks_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
 `cs_extends c1 sb` by
   (irule cs_extends_trans >> qexists_tac `c3` >> simp[]) >>
 `fn_has_code c1 sb func` by
   (mp_tac (Q.SPECL [`sa`, `c1`, `sb`, `func`] fn_has_code_split) >> simp[]) >>
 `fn_has_code c1 c3 func` by
   (mp_tac (Q.SPECL [`c1`, `c3`, `sb`, `func`] fn_has_code_split) >> simp[]) >>
 `~sh.vs_halted /\ sh.vs_current_bb = sa.cs_current_bb` by
   (qpat_assum `sh = s with vs_vars := _`
      (fn th => once_rewrite_tac[th]) >> simp[]) >>
 `eval_operand pos sh = SOME (n2w p) /\
  eval_operand hi sh = SOME (n2w L)` by metis_tac[] >>
 `op_taint tn1 pos = {}` by
   (qpat_assum `!op. op IN A1 ==> _` (qspec_then `pos` mp_tac) >>
    (impl_tac >- fs[SUBSET_DEF]) >> simp[]) >>
 `~s1.vs_halted /\ s1.vs_current_bb = c1.cs_current_bb /\
  s1.vs_inst_idx = LENGTH c1.cs_current_insts /\ fresh_vars_wrt c1 s1 /\
  eval_operand pos s1 = SOME (n2w p) /\
  eval_operand head s1 = SOME (n2w (p+32)) /\
  eval_operand hi s1 = SOME (n2w L) /\ op_taint tn1 pos = {}` by
   fs[Abbr `s1`, fresh_vars_wrt_def, SUBSET_DEF, same_blocks_def,
      eval_operand_def, lookup_var_def] >>
 mp_tac (abi_decode_ptr_relative_load |> Q.INST
   [`sa` |-> `c1`, `sb` |-> `c2`, `sc` |-> `c3`,
    `src` |-> `source`, `b` |-> `n2w B`, `h` |-> `L`, `v` |-> `cnt`,
    `G` |-> `G1`, `tn` |-> `tn1`, `s` |-> `s1`,
    `PG` |-> `PG`, `D` |-> `D`]) >>
 (impl_tac >- simp[w2n_n2w]) >> strip_tac >>
 rename1 `cnt = Var countvar` >>
 rename1 `inst_seq_ptr D 0 ctx func PG G1 tn1 (emitted_insts c1 c3) s1 G2 tn2` >>
 rename1 `lookup_var countvar s3 = SOME (mload _ s1)` >>
 rename1 `addr = Var ar` >>
 `fresh_vars_wrt c3 s3` by metis_tac[] >>
 `not_fresh_at c1 source /\ not_fresh_at c3 source /\
  not_fresh_at c3 ar` by
   (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `abi_decode_ptr_window G2 tn2 s3 source (n2w B) L` by
   (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G1`, `s1`, `tn1`] >>
    simp[] >> qpat_assum `!x. not_fresh_at c1 x ==> _`
      (qspec_then `source` mp_tac) >> simp[]) >>
 `s3.vs_labels = s1.vs_labels` by
   (qpat_assum `state_frame s3 = _` mp_tac >>
    simp_tac (srw_ss()) [state_frame_def, venom_state_component_equality]) >>
 `!op. (!x. op = Var x ==> not_fresh_at c1 x) ==>
    eval_operand op s3 = eval_operand op s1 /\
    op_prov G2 op = op_prov G1 op /\ op_taint tn2 op = op_taint tn1 op` by
   (gen_tac >> disch_tac >> irule abi_decode_scalar_protected_operand >>
    simp[] >> qexists_tac `{x | not_fresh_at c1 x}` >> simp[]) >>
 `abi_decoder_operand_live c1.cs_next_var head /\
  abi_decoder_operand_live c1.cs_next_var hi` by
   (conj_tac >> irule abi_decoder_operand_live_fresh
    >- (qexistsl_tac [`s1`, `n2w (p+32)`] >> simp[]) >>
    qexistsl_tac [`s1`, `n2w L`] >> simp[]) >>
 `(!x. head = Var x ==> not_fresh_at c1 x) /\
  (!x. hi = Var x ==> not_fresh_at c1 x)` by
   (Cases_on `head` >> Cases_on `hi` >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 `op_prov G2 head = NONE /\ op_taint tn2 head = {} /\
  op_prov G2 hi = NONE /\ op_taint tn2 hi = {} /\
  eval_operand head s3 = SOME (n2w (p+32)) /\
  eval_operand hi s3 = SOME (n2w L)` by metis_tac[] >>
 `mload (B+p) s1 = mload (B+p) s /\ w2n (n2w B : bytes32) = B` by
   (simp[Abbr `s1`, w2n_n2w, mload_def] >>
    qpat_assum `sh = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
 `eval_operand (Var countvar) s3 = SOME (mload (B+p) s)` by
   simp[eval_operand_def] >>
 `eval_operand (Lit (n2w maxn)) s3 = SOME (n2w maxn)` by simp[eval_operand_def] >>
 `w2n (mload (B+p) s) <= w2n (n2w maxn : bytes32)` by simp[w2n_n2w] >>
 mp_tac (abi_decode_le_guard_sequence |> Q.INST
   [`st` |-> `c3`, `st'` |-> `c4`, `a` |-> `cnt`,
    `b` |-> `Lit (n2w maxn)`, `s` |-> `s3`,
    `va` |-> `mload (B+p) s`, `vb` |-> `n2w maxn`]) >>
 (impl_tac >- simp[]) >> strip_tac >>
 rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK sl` >>
 `eval_operand head sl = SOME (n2w (p+32)) /\
  eval_operand (Var countvar) sl = SOME (n2w (w2n (mload (B+p) s))) /\
  eval_operand hi sl = SOME (n2w L)` by metis_tac[n2w_w2n] >>
 drule abi_decode_dynarray_payload_guard_sequence >>
 disch_then (qspec_then `sl` mp_tac) >>
 (impl_tac >- (simp[] >> qexistsl_tac [`p+32`, `w2n (mload (B+p) s)`, `L`] >> simp[])) >>
 strip_tac >> rename1 `run_inst_seq (emitted_insts c4 sb) sl = OK sp` >>
 `?A2. bop_scalar_seq {x | not_fresh_at c3 x}
   ({head;Var countvar;hi} UNION IMAGE Lit UNIV) (emitted_insts c3 c4) A2 /\
   ({head;Var countvar;hi} UNION IMAGE Lit UNIV) SUBSET A2` by
   (irule abi_decode_le_guard_scalar >> simp[] >> metis_tac[]) >>
 `?A3. bop_scalar_seq {x | not_fresh_at c3 x} A2
   (emitted_insts c4 sb) A3 /\ A2 SUBSET A3` by
   (mp_tac (abi_decode_dynarray_payload_guard_scalar |> Q.INST
      [`sa` |-> `c4`, `R` |-> `{x | not_fresh_at c3 x}`, `A` |-> `A2`]) >>
    (impl_tac >- (simp[] >> fs[SUBSET_DEF, not_fresh_at_def] >>
      metis_tac[LESS_EQ_TRANS])) >> simp[]) >>
 `emitted_insts c3 sb = emitted_insts c3 c4 ++ emitted_insts c4 sb` by
   (irule emitted_insts_append >> fs[inst_extends_def]) >>
 `bop_scalar_seq {x | not_fresh_at c3 x}
   ({head;Var countvar;hi} UNION IMAGE Lit UNIV) (emitted_insts c3 sb) A3` by
   metis_tac[bop_scalar_seq_append] >>
 `run_inst_seq (emitted_insts c3 sb) s3 = OK sp` by
   (drule_all abi_decode_sequence_chain >> simp[]) >>
 `!op. op IN {head;Var countvar;hi} UNION IMAGE Lit UNIV ==>
   op_prov G2 op = NONE /\ op_taint tn2 op = {}` by
   (ho_match_mp_tac abi_decode_scalar_clean_set_literals >>
    `op_prov G2 (Var countvar) = NONE /\ op_taint tn2 (Var countvar) = {}` by
      (qpat_assum `cnt = Var countvar` (fn th => once_rewrite_tac[GSYM th]) >>
       asm_rewrite_tac[]) >>
    gen_tac >> simp_tac (srw_ss()) [IN_INSERT, NOT_IN_EMPTY] >>
    strip_tac >> pop_assum SUBST1_TAC >> asm_rewrite_tac[]) >>
 mp_tac (abi_decode_scalar_success_frame |> Q.INST
   [`R` |-> `{x | not_fresh_at c3 x}`,
    `A` |-> `{head;Var countvar;hi} UNION IMAGE Lit UNIV`,
    `B` |-> `A3`, `code` |-> `emitted_insts c3 sb`,
    `G` |-> `G2`, `tn` |-> `tn2`, `s` |-> `s3`, `u` |-> `sp`,
    `j` |-> `LENGTH sb.cs_current_insts`, `fn` |-> `func`]) >>
 (impl_tac >- simp[]) >> strip_tac >>
 rename1 `inst_seq_ptr D 0 ctx func PG G2 tn2 (emitted_insts c3 sb) s3 G3 tn3` >>
 qabbrev_tac `s5 = sp with vs_inst_idx := LENGTH sb.cs_current_insts` >>
 `abi_decode_ptr_window G3 tn3 s5 source (n2w B) L /\
  abi_decode_ptr_window G3 tn3 s5 ar (n2w B+n2w p) (L-p)` by
   (conj_tac >> qpat_assum `!x b h. x IN {x | not_fresh_at c3 x} /\ _ ==> _`
      irule >> simp[]) >>
 `abi_decode_ptr_window G3 tn3 s5 ar (n2w (B+p)) 32` by
   (qpat_assum `abi_decode_ptr_window G3 tn3 s5 ar _ _` mp_tac >>
    qpat_assum `p+32 <= L` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
    simp[abi_decode_ptr_window_def, ptr_covers_def, word_add_n2w] >>
    rpt strip_tac >> gvs[] >> metis_tac[DECIDE ``p+32 <= L ==> 32 <= L-p``]) >>
 `!x. not_fresh_at sa x ==> not_fresh_at c1 x /\ not_fresh_at c3 x` by
   (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `!x. not_fresh_at sa x ==> lookup_var x s5 = lookup_var x s /\
   FLOOKUP G3 x = FLOOKUP G x /\ op_taint tn3 (Var x) = op_taint tn (Var x)` by
   (rpt strip_tac >>
    `not_fresh_at c1 x /\ not_fresh_at c3 x` by metis_tac[] >>
    qpat_assum `!x. x IN {x | not_fresh_at sa x} ==> _`
      (qspec_then `x` mp_tac) >>
    qpat_assum `!x. not_fresh_at c1 x ==> _` (qspec_then `x` mp_tac) >>
    qpat_assum `!x. x IN {x | not_fresh_at c3 x} ==> _`
      (qspec_then `x` mp_tac) >>
    simp[Abbr `s1`, Abbr `s5`, lookup_var_def] >> metis_tac[]) >>
 `emitted_insts sa sb = emitted_insts sa c1 ++
    (emitted_insts c1 c3 ++ emitted_insts c3 sb)` by
   (qpat_assum `inst_extends sa c1` mp_tac >>
    qpat_assum `inst_extends c1 c3` mp_tac >>
    qpat_assum `inst_extends c3 sb` mp_tac >>
    qpat_assum `inst_extends c1 sb` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
    simp[inst_extends_def] >> rpt strip_tac >>
    metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
 `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa c1) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c3) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c3 sb)` by
   (drule abi_decode_dynarray_position_prefix_joint_code >>
    strip_tac >>
    qpat_assum `EVERY _ (emitted_insts sa sb)` mp_tac >>
    qpat_assum `emitted_insts sa sb = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
    simp[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
 `run_inst_seq (emitted_insts sa c1) s = OK (s1 with vs_inst_idx := s.vs_inst_idx) /\
  run_inst_seq (emitted_insts c3 sb) s3 = OK (s5 with vs_inst_idx := s3.vs_inst_idx)` by
   (simp[Abbr `s1`, Abbr `s5`, venom_state_component_equality] >>
    fs[venom_state_component_equality]) >>
 `LENGTH c1.cs_current_insts = LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa c1) /\
  LENGTH c3.cs_current_insts = LENGTH c1.cs_current_insts + LENGTH (emitted_insts c1 c3) /\
  LENGTH sb.cs_current_insts = LENGTH c3.cs_current_insts + LENGTH (emitted_insts c3 sb)` by
   (qpat_assum `inst_extends sa c1` mp_tac >>
    qpat_assum `inst_extends c1 c3` mp_tac >>
    qpat_assum `inst_extends c3 sb` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
    simp_tac bool_ss [inst_extends_def] >> rpt strip_tac >>
    metis_tac[LENGTH_APPEND]) >>
 `s1.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa c1) /\
  s3.vs_inst_idx = s1.vs_inst_idx + LENGTH (emitted_insts c1 c3) /\
  s5.vs_inst_idx = s3.vs_inst_idx + LENGTH (emitted_insts c3 sb)` by
   (simp_tac (srw_ss()) [Abbr `s1`, Abbr `s5`] >> decide_tac) >>
 `EVERY (\i. ~is_terminator i.inst_opcode)
   (emitted_insts c1 c3 ++ emitted_insts c3 sb)` by simp[EVERY_APPEND] >>
 drule_all inst_seq_ptr_append_normalized >> strip_tac >>
 qpat_assum `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa c1) s G1 tn1`
   (mp_then Any mp_tac inst_seq_ptr_append_normalized) >>
 disch_then drule_all >> strip_tac >>
 `u = s5 with vs_inst_idx := s.vs_inst_idx` by gvs[] >>
 `run_inst_seq_mem_ok (emitted_insts sa c1) s /\
  run_inst_seq_mem_ok (emitted_insts c3 sb) s3` by
   metis_tac[bop_scalar_seq_mem_ok] >>
 `sh.vs_alloca_next = s.vs_alloca_next` by
   (qpat_assum `sh = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
 `lookup_var source s1 = SOME (n2w B) /\
  w2n (n2w B : bytes32)+p < dimword (:256) /\
  w2n (n2w B : bytes32)+p+32 <= s1.vs_alloca_next` by
   (fs[abi_decode_ptr_window_def, Abbr `s1`, w2n_n2w] >> decide_tac) >>
 `run_inst_seq_mem_ok (emitted_insts c1 c3) s1` by
   (drule_all abi_decode_relative_load_mem_ok >> simp[]) >>
 `run_inst_seq_mem_ok (emitted_insts c1 c3 ++ emitted_insts c3 sb) s1` by
   (irule run_inst_seq_mem_ok_append >> simp[] >> rpt strip_tac >> gvs[]) >>
 `run_inst_seq_mem_ok (emitted_insts c1 c3 ++ emitted_insts c3 sb) sh` by
   (qpat_assum `run_inst_seq_mem_ok (emitted_insts c1 c3 ++ emitted_insts c3 sb) s1`
      mp_tac >>
    qpat_assum `EVERY _ (emitted_insts c1 c3 ++ emitted_insts c3 sb)` mp_tac >>
    simp_tac bool_ss [Abbr `s1`] >> POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
 `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
   (qpat_assum `emitted_insts sa sb = _` mp_tac >>
    qpat_assum `run_inst_seq (emitted_insts sa c1) s = OK sh` mp_tac >>
    qpat_assum `run_inst_seq_mem_ok (emitted_insts sa c1) s` mp_tac >>
    qpat_assum `run_inst_seq_mem_ok (emitted_insts c1 c3 ++ emitted_insts c3 sb) sh`
      mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
    asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
 `not_fresh_at sb ar` by
   (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `u = s with vs_vars := u.vs_vars` by
   (mp_tac (abi_malformed_dynarray_prefix_exact |> Q.INST
      [`st` |-> `sa`, `en` |-> `sb`, `src` |-> `pos`,
       `base_op` |-> `Var source`, `t` |-> `u`]) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    strip_tac >> first_assum ACCEPT_TAC) >>
 `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G3 tn3` by
   (qpat_assum `inst_seq_ptr D 0 ctx func PG G tn _ s G3 tn3` mp_tac >>
    qpat_assum `emitted_insts sa sb = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
    simp[APPEND_ASSOC]) >>
 `abi_decode_ptr_window G3 tn3 u source (n2w B) L /\
  abi_decode_ptr_window G3 tn3 u ar (n2w (B+p)) 32` by
   (qpat_assum `u = s5 with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
    fs[abi_decode_ptr_window_def, lookup_var_def, ptr_covers_inst_idx]) >>
 `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
   FLOOKUP G3 x = FLOOKUP G x /\ op_taint tn3 (Var x) = op_taint tn (Var x)` by
   (rpt strip_tac >>
    qpat_assum `u = s5 with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
    qpat_assum `!x. not_fresh_at sa x ==> lookup_var x s5 = _ /\ _`
      (qspec_then `x` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> fs[lookup_var_def]) >>
 `tn3.t_mem = tn.t_mem /\ tn3.t_stor = tn.t_stor /\
  tn3.t_trans = tn.t_trans /\ tn3.t_imm = tn.t_imm` by metis_tac[] >>
 qexistsl_tac [`ar`, `G3`, `tn3`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Proposed shared bounded MLOAD dynamic-array prefix boundary.
   Both allocated bulk and loop init use this same prefix. All additional
   numeric/freshness premises follow from their existing allocated entry
   and coherent-array capacity facts. No stage premise changes. *)
Theorem abi_decode_dynarray_position_prefix_success_joint:
 abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn stride sa = (addr,sb) /\
 run_inst_seq (emitted_insts sa sb) s = OK u /\
 fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 not_fresh_at sa source /\
 (!x. pos = Var x ==> not_fresh_at sa x) /\
 (!x. hi = Var x ==> not_fresh_at sa x) /\
 hi <> Lit 0w /\
 abi_decode_ptr_window G tn s source (n2w B) L /\
 eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w L) /\
 op_prov G pos = NONE /\ op_prov G hi = NONE /\
 op_taint tn pos = {} /\ op_taint tn hi = {} /\
 p < dimword (:256) /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
 maxn < dimword (:256) /\ maxn*stride < dimword (:256) /\ allocas_from lo s
 ==>
 ?ar G' tn'. addr = Var ar /\
 (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
   (s,G,tn) [] (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
 u = s with vs_vars := u.vs_vars /\
 abi_decode_ptr_window G' tn' u source (n2w B) L /\
 abi_decode_ptr_window G' tn' u ar (n2w (B+p)) 32 /\
 not_fresh_at sb ar /\
 w2n (mload (B+p) s) <= maxn /\
 p+32+w2n (mload (B+p) s)*stride <= L /\
 (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
   FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
 tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
 tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u

Proof
 strip_tac >>
 drule abi_decode_dynarray_position_prefix_joint_code >> strip_tac >>
 `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb)` by
   fs[EVERY_MEM] >>
 `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
   ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
 qabbrev_tac `ps = abi_decoder_prune_vars sa.cs_next_var s` >>
 `abi_decoder_operand_live sa.cs_next_var pos /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  abi_decoder_operand_live sa.cs_next_var (Var source)` by
   (Cases_on `pos` >> Cases_on `hi` >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 `B < dimword (:256) /\ L < dimword (:256)` by decide_tac >>
 `eval_operand (Var source) s = SOME (n2w B)` by
   fs[abi_decode_ptr_window_def, eval_operand_def] >>
 `eval_operand (Var source) ps = SOME (n2w B) /\
  eval_operand pos ps = SOME (n2w p) /\
  eval_operand hi ps = SOME (n2w L) /\ fresh_vars_wrt sa ps` by
   simp[Abbr `ps`, abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
 `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
 mp_tac (abi_malformed_dynarray_prefix_total |> Q.INST
   [`st` |-> `sa`, `en` |-> `sb`, `base_op` |-> `Var source`,
    `opc` |-> `MLOAD`, `s` |-> `ps`, `h` |-> `L`, `b` |-> `B`]) >>
 (impl_tac >- simp[]) >> strip_tac
 >- (rename1 `run_inst_seq _ ps = Abort Revert_abort rejected` >>
     mp_tac (abi_decoder_sequence_revert_reentry |> Q.INST
       [`initial` |-> `s`, `next` |-> `sa.cs_next_var`,
        `insts` |-> `emitted_insts sa sb`, `clean` |-> `rejected`]) >>
     (impl_tac >- simp[Abbr `ps`]) >> strip_tac >> gvs[]) >>
 rename1 `run_inst_seq (emitted_insts sa sb) ps = OK clean` >>
 `abi_decode_ptr_window G tn ps source (n2w B) L` by
   (fs[abi_decode_ptr_window_def] >>
    simp[Abbr `ps`, abi_decode_ptr_prune_covers, abi_decoder_prune_vars_def,
      lookup_var_def, FLOOKUP_DRESTRICT] >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def,
      lookup_var_def]) >>
 mp_tac (abi_decode_dynarray_position_prefix_fresh_ptr |> Q.INST
   [`s` |-> `ps`, `u` |-> `clean`,
    `D` |-> `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]) >>
 (impl_tac >- simp[Abbr `ps`, abi_decoder_prune_vars_def]) >> strip_tac >>
 `abi_decoder_vars_extend s.vs_vars ps s` by
   simp[Abbr `ps`, abi_decoder_prune_extension] >>
 drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
 rename1 `abi_decoder_vars_extend s.vs_vars clean actual` >>
 `actual = u` by gvs[] >> qpat_x_assum `actual = u` SUBST_ALL_TAC >>
 drule_all abi_decoder_vars_extend_observations >> strip_tac >>
 `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
   (drule_all abi_decode_sequence_mem_reentry >> simp[]) >>
 `inst_seq_ptr
   <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
   0 ctx func PG G tn (emitted_insts sa sb) s G' tn'` by
   (drule_all abi_decode_ptr_sequence_reentry >> simp[]) >>
 `u = s with vs_vars := u.vs_vars` by
   (drule_all abi_malformed_dynarray_prefix_exact >> simp[]) >>
 `allocas_from lo u` by
   (qpat_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
    fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
 `isPREFIX sa.cs_current_insts sb.cs_current_insts` by fs[inst_extends_def] >>
 `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
 drule_all entry_straight_line_code_slice >> strip_tac >>
 `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
   fs[EVERY_MEM] >>
 `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
   fs[inst_extends_def] >>
 `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
   simp[IS_PREFIX_APPEND] >>
 `!explicit. gas_origin_ptr_path
   (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
    lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')` by
   (gen_tac >> drule_all run_inst_seq_origin_ptr_lift >>
    disch_then (qspec_then `explicit` mp_tac) >> simp[IS_PREFIX_APPEND]) >>
 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')` by
   (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
 `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
   (drule_all abi_malformed_dynarray_prefix_exact >>
    fs[lookup_var_def]) >>
 `lookup_var ar u = lookup_var ar clean` by
   (fs[abi_decode_ptr_window_def] >>
    drule_all abi_decoder_vars_extend_eval >> fs[eval_operand_def]) >>
 `abi_decode_ptr_window G' tn' u source (n2w B) L /\
  abi_decode_ptr_window G' tn' u ar (n2w (B+p)) 32` by
   (conj_tac >> irule abi_decode_ptr_window_frame >>
    qexistsl_tac [`G'`, `clean`, `tn'`] >> simp[] >>
    fs[abi_decode_ptr_window_def, Abbr `ps`, abi_decoder_prune_vars_def,
      lookup_var_def, FLOOKUP_DRESTRICT] >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 qexistsl_tac [`ar`, `G'`, `tn'`] >> simp[] >>
 fs[Abbr `ps`, abi_decoder_prune_vars_def, mload_def] >>
 rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> _ /\ _` drule >> simp[]
QED
