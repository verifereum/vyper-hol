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
Libs
 abiDecodePtrArrayPrefixProofLib

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
 abiDecodePtrArrayPrefixProofLib.payload_guard_scalar ()
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
 qpat_x_assum `maxn*stride < dimword (:256)` kall_tac >>
 abiDecodePtrArrayPrefixProofLib.fresh_head () >>
 abiDecodePtrArrayPrefixProofLib.fresh_code () >>
 abiDecodePtrArrayPrefixProofLib.fresh_load () >>
 abiDecodePtrArrayPrefixProofLib.fresh_guards () >>
 abiDecodePtrArrayPrefixProofLib.fresh_tail () >>
 abiDecodePtrArrayPrefixProofLib.fresh_tail_frame () >>
 abiDecodePtrArrayPrefixProofLib.fresh_slice abi_decode_dynarray_position_prefix_joint_code >>
 abiDecodePtrArrayPrefixProofLib.fresh_normalize_runs () >>
 abiDecodePtrArrayPrefixProofLib.fresh_normalize_lengths () >>
 abiDecodePtrArrayPrefixProofLib.fresh_normalize () >>
 abiDecodePtrArrayPrefixProofLib.fresh_normalize_endpoint () >>
 abiDecodePtrArrayPrefixProofLib.fresh_memory () >>
 abiDecodePtrArrayPrefixProofLib.fresh_finish () >>
 abiDecodePtrArrayPrefixProofLib.fresh_finish_frame ()
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
 `B < dimword (:256) /\ L < dimword (:256)` by decide_tac >>
 `eval_operand (Var source) s = SOME (n2w B)` by
   fs[abi_decode_ptr_window_def, eval_operand_def] >>
 `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
 abiDecodePtrArrayPrefixProofLib.reentry_prune abi_decode_dynarray_position_prefix_joint_code >>
 (* Compatibility adapter for this unchanged maximum-bound declaration.
    The shared implementation below consumes only the actual-count bounds. *)
 `w2n (mload (B+p) initial) <= maxn /\
  p+32+w2n (mload (B+p) initial)*stride <= L` by
   (mp_tac (abi_malformed_dynarray_prefix_total |> Q.INST
      [`st` |-> `sa`, `en` |-> `sb`, `base_op` |-> `Var source`,
       `opc` |-> `MLOAD`, `s` |-> `s`, `h` |-> `L`, `b` |-> `B`]) >>
    (impl_tac >- simp[]) >> strip_tac
    >- (rename1 `run_inst_seq _ s = Abort Revert_abort rejected` >>
        mp_tac (abi_decoder_sequence_revert_reentry |> Q.INST
          [`initial` |-> `initial`, `next` |-> `sa.cs_next_var`,
           `insts` |-> `emitted_insts sa sb`, `clean` |-> `rejected`]) >>
        (impl_tac >- simp[Abbr `s`]) >> strip_tac >> gvs[]) >>
    gvs[abi_decode_load_def, w2n_n2w, mload_def, Abbr `s`,
      abi_decoder_prune_vars_def]) >>
 qpat_x_assum `maxn*stride < dimword (:256)` kall_tac >>
 abiDecodePtrArrayPrefixProofLib.reentry_prepare () >>
 `?ar G' tn'. addr = Var ar /\
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
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by
   (abiDecodePtrArrayPrefixProofLib.fresh_head () >>
    abiDecodePtrArrayPrefixProofLib.fresh_code () >>
    abiDecodePtrArrayPrefixProofLib.fresh_load () >>
    abiDecodePtrArrayPrefixProofLib.fresh_guards () >>
    abiDecodePtrArrayPrefixProofLib.fresh_tail () >>
    abiDecodePtrArrayPrefixProofLib.fresh_tail_frame () >>
    abiDecodePtrArrayPrefixProofLib.fresh_slice abi_decode_dynarray_position_prefix_joint_code >>
    abiDecodePtrArrayPrefixProofLib.fresh_normalize_runs () >>
    abiDecodePtrArrayPrefixProofLib.fresh_normalize_lengths () >>
    abiDecodePtrArrayPrefixProofLib.fresh_normalize () >>
    abiDecodePtrArrayPrefixProofLib.fresh_normalize_endpoint () >>
    abiDecodePtrArrayPrefixProofLib.fresh_memory () >>
    abiDecodePtrArrayPrefixProofLib.fresh_finish () >>
    abiDecodePtrArrayPrefixProofLib.fresh_finish_frame ()) >>
 abiDecodePtrArrayPrefixProofLib.reentry_lift () >>
 abiDecodePtrArrayPrefixProofLib.reentry_path ()
QED
