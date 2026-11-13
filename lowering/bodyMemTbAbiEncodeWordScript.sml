(* Memory-safe value simulation of abi_encode's single word argument: the
   argument is staged in a 32-byte buffer (ALLOCA, MSTORE), then encoded by
   the counted encoder of bodyMemTbAbiEncodeStaged. *)
Theory bodyMemTbAbiEncodeWord
Ancestors
  bodyMemTbAbiEncodeStaged bodyMemTbAbiEncodeNonwordCase bodyMemTbAbiEncodePhases
  bodyMemBiSha256Suffix bodyMemBiSha256Compose
  exprSimAbiEncodeWordCase exprSimAbiEncodeWordResult exprSimAbiEncodeWordSuccess
  exprSimAbiEncodeTupleResult exprSimAbiEncodeNonwordCase exprSimAbiEncodeNonwordResult
  exprSimAbiEncodeBytesOwnership exprSimAbiEncodeStagedObserver exprSimAbiEncodeCapacity
  exprSimAbiEncodeRuntimeInputs exprSimAbiEncodePrefixWindow exprSimAbiEncodeStagedFrame
  exprSimAbiEncodeTranslatedNoBlock exprSimAbiEncodeOriginFrame exprSimAbiEncodeOblivious
  exprSimHashBoundary exprSimHash exprSimHypsDefs exprSimDefs exprSimMemDefs exprSimSource
  exprSimAlloc exprSimProps exprLowering exprBopLowering exprLoweringProps exprBopSimProps
  exprOperandVar loweringStateRelDefs loweringPosts
  abiBuiltinAllocation abiBuiltinEncodeWord abiBuiltinEncodeCode abiBuiltinEncodeSetup
  abiEncoderCounters abiEncoderAppend abiDecoderReentry abiDecoderGuards
  fragGasPathFrameMem fragGasPathMem fragGasMode fragExecMem fragExec gasSummary
  compileEnv emitHelper emitHelperProps context venomState venomInst venomMemDefs
  vyperAST vyperState vyperContext vyperInterpreter vyperTypeSystem vyperTypeABI
  vyperTypeCallGraph vyperTypeInvariants vyperEvalExprPreservesScopesDom vyperABI
  localPtrsProps finite_map list rich_list words arithmetic

Theorem abi_encode_word_staging_mem[local]:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;op] sm = ((),sh) /\
  fn_has_code sa sm func /\ fn_has_code sa sh func /\
  stmt_state_rel ctx func ce cx es s /\
  eval_operand op s = SOME w /\ (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n staged. run_inst_seq (emitted_insts sa sh) s = OK staged /\
    gas_path_mem ctx func s n (OK (staged with vs_inst_idx := LENGTH sh.cs_current_insts)) /\
    s.vs_alloca_next <= staged.vs_alloca_next
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `!b0 cap. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b0,cap) ==> cap = 32` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
     pop_assum (qspecl_then [`mk_inst sa.cs_next_id ALLOCA [Lit 32w]
         [STRING #"%" (toString sa.cs_next_var)]`, `32w`, `b0`, `cap`] mp_tac) >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         simp_tac (srw_ss()) [mk_inst_def] >> first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [w2n_n2w, dimword_def]) >>
  `alloca_next_valid s` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def, alloca_inv_def]) >>
     first_assum ACCEPT_TAC) >>
  drule_all sha256_alloc32_mem >> strip_tac >>
  `eval_operand op t = SOME w` by metis_tac[] >>
  drule_all sha256_mstore_mem >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  `inst_extends sa sm` by (drule inst_extends_emit_op >> simp_tac bool_ss []) >>
  `inst_extends sm sh` by (drule inst_extends_emit_void >> simp_tac bool_ss []) >>
  `run_inst_seq (emitted_insts sa sh) s = OK (mstore (w2n r) w t)` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`t`, `sm`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!s1. run_inst_seq (emitted_insts sa sm) s = OK s1 ==>
     run_inst_seq_mem_ok (emitted_insts sm sh) s1` by
    (qx_gen_tac `s1` >> strip_tac >>
     `s1 = t` by
       (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK s1` mp_tac >>
        qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK t`
          (fn th => rewrite_tac [th]) >>
        simp_tac (srw_ss()) []) >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `emitted_insts sa sh = emitted_insts sa sm ++ emitted_insts sm sh` by
    (match_mp_tac emitted_insts_append >> REWRITE_TAC [GSYM inst_extends_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `run_inst_seq_mem_ok (emitted_insts sa sh) s` by
    (pop_assum SUBST1_TAC >> match_mp_tac run_inst_seq_mem_ok_append >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  `?n. gas_path_mem ctx func s n
     (OK (mstore (w2n r) w t with vs_inst_idx := LENGTH sh.cs_current_insts))` by
    (irule abi_encode_straight_path_mem >> simp_tac bool_ss [PULL_EXISTS] >>
     qexists_tac `sa` >> asm_rewrite_tac[]) >>
  qexistsl_tac [`n`, `mstore (w2n r) w t`] >>
  asm_rewrite_tac[]
QED

(* abi_encode_staged_mem with its layout equations substituted. *)
val abi_encode_staged_mem_fixed = abi_encode_staged_mem |> SPEC_ALL
  |> Q.INST [`d` |-> `p+32+m`, `outsz` |-> `32+32*word_size(maxlen+m)`]
  |> Q.INST [`m` |-> `(case method_id of NONE => 0 | SOME mid => 4)`,
             `w` |-> `(case method_id of NONE => 0 | SOME mid => 32)`]
  |> PURE_REWRITE_RULE [REFL_CLAUSE, IMP_CLAUSES, AND_CLAUSES]
  |> PURE_ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO];

Theorem abi_encode_word_encoder_mem[local]:
  is_word_type ty /\
  lower_abi_encode F mid src (type_to_abi_enc_info sf ce ty) 32 st = (out,final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es initial /\ local_ptrs_reserved ce st /\
  FLOOKUP initial.vs_allocas source_id = SOME(sb,32) /\ source_id <> st.cs_next_id /\
  abi_encoder_window_input (type_to_abi_enc_info sf ce ty) at av sb 32 initial.vs_memory /\
  LENGTH (enc at av) = 32 /\ eval_operand src initial = SOME(n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?p n actual. gas_path_mem ctx func initial n (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    initial.vs_alloca_next <= actual.vs_alloca_next /\
    abi_encode_staged_observation ctx func ce cx es st out mid
      (32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4))) p at av initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  `cs_extends st ready` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `cs_extends ready body_end` by metis_tac[cs_extends_abi_encode] >>
  `cs_extends body_end final` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `fn_has_code st ready func /\ fn_has_code ready body_end func /\
   fn_has_code body_end final func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  qpat_x_assum `out = FST ops` SUBST_ALL_TAC >>
  drule_all abi_encode_word_allocation_geometry >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?p. _` (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all abi_encode_translated_operand_liveness >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var` by
    (qpat_assum `ready.cs_next_var = _` mp_tac >> Cases_on `mid` >> simp[] >> decide_tac) >>
  `abi_encoder_admissible (type_to_abi_enc_info sf ce ty)` by
    (`type_to_abi_enc_info sf ce ty = AbiCopy 32` by
       (irule (cj 2 abi_builtin_encode_word_info) >> first_assum ACCEPT_TAC) >>
     asm_rewrite_tac [] >> simp[abiEncoderAdmissibleTheory.abi_encoder_admissible_def]) >>
  `!inst. MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids ready body_end ==>
    inst.inst_opcode <> ALLOCA` by
    metis_tac[abi_encode_word_body_no_alloca] >>
  `(0:num) < 32` by simp_tac arith_ss [] >>
  qexists_tac `p` >>
  qpat_assum `abi_builtin_encode_setup _ _ _ = _`
    (mp_tac o GEN_ALL o MATCH_MP abi_encode_staged_mem_fixed) >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_builtin_encode_finish _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_encoder_window_input _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (qspec_then `p` (mp_tac o PURE_REWRITE_RULE [AND_IMP_INTRO])) >>
  impl_tac
  >- (RULE_ASSUM_TAC (PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
      asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >>
      rpt strip_tac >> metis_tac[]) >>
  disch_then (qx_choosel_then [`n`, `actual`] strip_assume_tac) >>
  qexistsl_tac [`n`, `actual`] >> asm_rewrite_tac[]
QED

Theorem abi_encode_word_staged_counted_mem[local]:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;op] sm = ((),sh) /\
  lower_abi_encode F mid buf.buf_operand
    (type_to_abi_enc_info sf ce (expr_type e)) 32 sh = (out,final) /\
  fn_has_code sa sh func /\ fn_has_code sh final func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce origin /\ origin.cs_next_var <= sa.cs_next_var /\
  origin.cs_next_id <= sa.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p ct rv n actual initial.
    gas_path_mem ctx func s n (OK actual) /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av /\
    LENGTH (enc ct rv) = 32 /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    s.vs_alloca_next <= actual.vs_alloca_next /\
    abi_encode_staged_observation ctx func ce cx es' sh out mid
      (32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4)))
      p ct rv initial actual /\ wb_frame ce es es' origin s0 actual /\
    (~expr_has_effect e ==> pure_frame ce func es origin s0 actual)
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  `fn_has_code sa sm func` by
    (irule (cj 1 fn_has_code_split) >> conj_tac
     >- (qpat_x_assum `emit_op ALLOCA _ sa = _` mp_tac >>
         simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
           emit_def, comp_return_def] >> strip_tac >> gvs[] >>
         irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
     qexists_tac `sh` >> asm_rewrite_tac[] >>
     qpat_x_assum `emit_void MSTORE _ sm = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
     irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all abi_encode_word_expr_post >> strip_tac >>
  drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  drule_all abi_encode_word_source_window >>
  disch_then (qspecl_then [`sf`, `ce`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func ce cx es' staged` >>
  drule_all abi_encode_word_staging_path >> strip_tac >>
  `run_inst_seq (emitted_insts sa sh) s = OK staged` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`allocated`, `sm`] >>
     metis_tac[inst_extends_emit_op, inst_extends_emit_void]) >>
  `stmt_state_rel ctx func ce cx es' s /\
   eval_operand op s = SOME(typed_val_to_w256 tv v)` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  drule_all abi_encode_word_staging_mem >>
  disch_then (qx_choosel_then [`n1`, `staged1`] strip_assume_tac) >>
  `staged1 = staged` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sh) s = OK staged1` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sa sh) s = OK staged`
       (fn th => rewrite_tac [th]) >>
     simp_tac (srw_ss()) []) >>
  pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `initial = staged with vs_inst_idx := LENGTH sh.cs_current_insts` >>
  `local_ptrs_reserved ce sh` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `FLOOKUP initial.vs_allocas sa.cs_next_id = SOME(w2n addr,32)` by
    simp[Abbr `initial`, Abbr `staged`, mstore_def] >>
  `sa.cs_next_id <> sh.cs_next_id` by decide_tac >>
  `stmt_state_rel ctx func ce cx es' initial /\
   abi_encoder_window_input (type_to_abi_enc_info sf ce (expr_type e))
     ct rv (w2n addr) 32 initial.vs_memory /\
   LENGTH (enc ct rv) = 32 /\
   eval_operand buf.buf_operand initial = SOME(n2w (w2n addr)) /\
   ~initial.vs_halted /\ initial.vs_current_bb = sh.cs_current_bb /\
   initial.vs_inst_idx = LENGTH sh.cs_current_insts` by
    (simp[Abbr `initial`, stmt_state_rel_inst_idx] >>
     simp[Abbr `staged`, mstore_def, eval_operand_def] >>
     Cases_on `buf.buf_operand` >> gvs[eval_operand_def]) >>
  `(!x. buf.buf_operand = Var x ==> not_fresh_at sh x)` by
    (qpat_x_assum `emit_op ALLOCA _ sa = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `buf.buf_operand` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  drule_all hash_alloc_mstore_frame >> strip_tac >>
  `t = staged` by gvs[] >>
  qpat_x_assum `t = staged` SUBST_ALL_TAC >>
  `wb_frame ce es es' origin s0 staged` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any irule abi_encode_nonword_origin_frame) >>
     simp[] >> metis_tac[]) >>
  `wb_frame ce es es' origin s0 initial` by
    (qunabbrev_tac `initial` >>
     qpat_assum `wb_frame _ _ _ _ _ staged` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[wb_frame_def, lookup_var_def, locals_kept_def] >>
     metis_tac[]) >>
  drule_all abi_encode_word_encoder_mem >> strip_tac >>
  suspend "frame"
QED

Resume abi_encode_word_staged_counted_mem[frame]:
  `origin.cs_next_var <= sh.cs_next_var /\
   origin.cs_next_id <= sh.cs_next_id` by decide_tac >>
  drule_all abi_encode_staged_origin_frame >> strip_tac >>
  `~expr_has_effect e ==> pure_frame ce func es origin s0 actual` by
    (strip_tac >>
     qpat_assum `abi_encode_staged_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_encode_staged_observation_def]) >>
     `pure_frame ce func es' sa s initial` by
       (qpat_assum `pure_frame _ _ _ sa s staged` mp_tac >> simp[Abbr `initial`]) >>
     `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
        FLOOKUP actual.vs_allocas aid = SOME row` by
       (rpt strip_tac >>
        qpat_x_assum `!aid row. FLOOKUP initial.vs_allocas aid = SOME row ==> _` irule >>
        simp[Abbr `initial`]) >>
     `!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
        lookup_var x initial = SOME w` by
       (rpt strip_tac >>
        qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x staged = _` drule >>
        gvs[Abbr `initial`, lookup_var_def]) >>
     `pure_frame ce func es' sa s actual` by
       (match_mp_tac (Q.SPECL [`ce`, `func`, `es'`, `es'`, `sa`, `sh`, `s`, `initial`, `actual`]
                        exprSimPropsTheory.pure_frame_trans) >>
        rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
        >- decide_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
        >- simp[] >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `expr_post _ _ _ _ e _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     `pure_frame ce func es origin s0 s` by
       (qpat_x_assum `~expr_has_effect e ==> _` irule >> first_assum ACCEPT_TAC) >>
     match_mp_tac (Q.SPECL [`ce`, `func`, `es`, `es'`, `origin`, `sa`, `s0`, `s`, `actual`]
                     exprSimPropsTheory.pure_frame_trans) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_path_mem ctx func s (n1 + n) (OK actual)` by
    (qpat_assum `gas_path_mem _ _ s _ (OK initial)` (fn th1 =>
       qpat_assum `gas_path_mem _ _ initial _ (OK actual)` (fn th2 =>
         ACCEPT_TAC (MATCH_MP gas_path_mem_then (CONJ th1 th2))))) >>
  `initial.vs_alloca_next = staged.vs_alloca_next` by simp[Abbr `initial`] >>
  `s.vs_alloca_next <= actual.vs_alloca_next` by decide_tac >>
  qexistsl_tac [`p`, `ct`, `rv`, `n1 + n`, `actual`, `initial`] >>
  asm_rewrite_tac[]
QED

Finalise abi_encode_word_staged_counted_mem

Theorem abi_encode_word_success_mem:
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) target [e]) es /\
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  evaluate_type_builtin cx (AbiEncode F mid0) target [expr_type e] [v] = INL result /\
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;op] sm = ((),sh) /\
  lower_abi_encode F mid buf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e)) 32 sh = (out,final) /\
  fn_has_code sa sh func /\ fn_has_code sh final func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce origin /\ origin.cs_next_var <= sa.cs_next_var /\
  origin.cs_next_id <= sa.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s ==>
  ?cnt actual. gas_path_mem ctx func s cnt (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode F mid0) target [e])
      es origin final s0 es' (Value result)
      (LocatedValue ann (mk_ptr out LocMemory)) actual /\
    vv_store_bound cx ann
      (lowered_value_type ce (TypeBuiltin ann (AbiEncode F mid0) target [e])) es'
      (Value result) (LocatedValue ann (mk_ptr out LocMemory)) actual /\
    alloca_history func actual /\ s.vs_alloca_next <= actual.vs_alloca_next
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_word_staged_counted_mem >> strip_tac >>
  qpat_assum `expr_body_pre ce cx env e es`
    (mp_then Any strip_assume_tac exprSimHypsTheory.expr_body_pre_physical_type) >>
  `lowered_value_type ce e = expr_type e` by
    (Cases_on `expr_type e` >> Cases_on `lowered_value_type ce e` >>
     gvs[is_word_type_def, arg_type_fits_def] >>
     Cases_on `b` >> Cases_on `b'` >>
     gvs[is_word_type_def, arg_type_fits_def] >>
     Cases_on `b` >> Cases_on `b''` >>
     gvs[is_word_type_def, arg_type_fits_def]) >>
  qpat_assum `evaluate_type _ (expr_type e) = SOME tv` mp_tac >>
  qpat_assum `lowered_value_type ce e = expr_type e`
    (fn th => once_rewrite_tac[GSYM th]) >>
  disch_tac >>
  drule_all abi_encode_nonword_result_bound >> strip_tac >>
  `result = BytesV (abi_encode_method_id_bytes mid0 ++ enc ct rv)` by
    (qpat_assum `evaluate_type_builtin _ _ _ _ _ = _` mp_tac >>
     qpat_assum `vyper_to_abi _ _ _ = _` mp_tac >>
     qpat_assum `enc ct rv = _` mp_tac >>
     qpat_assum `ty = TupleT _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[evaluate_type_builtin_def, needs_external_call_wrap_def,
       evaluate_abi_encode_bytes_def]) >>
  suspend "finish"
QED

Resume abi_encode_word_success_mem[finish]:
  `well_typed_type_builtin_args (AbiEncode F mid0) target [expr_type e]` by
    fs[expr_body_pre_def, well_typed_expr_def] >>
  `local_ptrs_reserved ce sh /\ origin.cs_next_id <= sh.cs_next_id` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule abiBuiltinEncodeWordTheory.abi_builtin_encode_word_stage_shape >> strip_tac >>
     first_x_assum drule >> strip_tac >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
     decide_tac) >>
  `LENGTH (abi_encode_method_id_bytes mid0 ++ enc ct rv) <= N` by metis_tac[] >>
  drule_all abi_encode_word_observation_vv_post >> disch_tac >>
  `stmt_state_rel ctx func ce cx es' s` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [expr_post_def] >> metis_tac[]) >>
  `alloca_history func actual` by
    (`alloca_inv s` by fs[stmt_state_rel_def] >>
     drule gas_path_mem_allocation_state >>
     disch_then (qspec_then `actual` mp_tac) >> simp[]) >>
  qpat_assum `abi_encode_staged_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_staged_observation_def]) >>
  `abi_size_bound ce.ce_struct_fields (expr_type e) = 32` by
    metis_tac[abi_encode_word_size_bound] >>
  `lowered_value_type ce (TypeBuiltin ann (AbiEncode F mid0) target [e]) =
     BaseT (BytesT (Dynamic (32 + (case mid of NONE => 0 | SOME _ => 4))))` by
    (simp[lowered_value_type_def] >> Cases_on `mid0` >> gvs[]) >>
  `ann = BaseT (BytesT (Dynamic N))` by
    (qpat_assum `expr_type (TypeBuiltin _ _ _ _) = _`
       (ACCEPT_TAC o REWRITE_RULE [expr_type_def])) >>
  pop_assum SUBST_ALL_TAC >>
  qexistsl_tac [`n`, `actual`] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ (LocatedValue _ _) _` mp_tac >>
      simp[expr_type_def] >>
      match_mp_tac (DISCH_ALL (fst (EQ_IMP_RULE
        (UNDISCH abi_encode_vv_post_pointer_cong)))) >>
      simp[contextTheory.mk_ptr_def]) >>
  irule abi_encode_bytes_store_bound >>
  conj_tac >- (Cases_on `mid0` >>
    gvs[abi_encode_method_id_bytes_def, well_typed_type_builtin_args_def]) >>
  conj_tac >- simp[contextTheory.mk_ptr_def] >>
  qexistsl_tac [`out`, `p`] >>
  simp[contextTheory.mk_ptr_def] >>
  Cases_on `mid0` >> gvs[]
QED

Finalise abi_encode_word_success_mem

Theorem compile_abi_encode_word_vv_sim_mem:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  expr_sim_mem ctx func ce cx (expr_type e) e es /\
  is_word_type (expr_type e) ==>
  expr_vv_sim_mem ctx func ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_mem_def] >> rpt strip_tac >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_abi_encode_word_shape] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  suspend "compose"
QED

Resume compile_abi_encode_word_vv_sim_mem[compose]:
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits] >>
  `lowered_value_type ce e = expr_type e` by
    (Cases_on `expr_type e` >> Cases_on `lowered_value_type ce e` >>
     gvs[is_word_type_def, vyperTypeSystemTheory.arg_type_fits_def] >>
     Cases_on `b` >> Cases_on `b'` >>
     gvs[is_word_type_def, vyperTypeSystemTheory.arg_type_fits_def] >>
     Cases_on `b` >> Cases_on `b''` >>
     gvs[is_word_type_def, vyperTypeSystemTheory.arg_type_fits_def]) >>
  fs[] >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
    (abi_size_bound ce.ce_struct_fields (expr_type e)) sh` >>
  rename1 `lower_abi_encode _ _ _ _ _ sh = (out,final)` >>
  gvs[as_ptr_val_def] >>
  `abi_size_bound ce.ce_struct_fields (expr_type e) = 32` by
    metis_tac[abi_encode_word_size_bound] >>
  `!l. buf.buf_operand <> Label l` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     qpat_x_assum `emit_op ALLOCA _ sm = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >> Cases_on `buf.buf_operand` >> gvs[]) >>
  drule_all lower_abi_encode_frag_facts >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule abi_builtin_encode_word_stage_shape >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `cs_extends sm sh` by (irule cs_extends_same_block >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sh func /\ fn_has_code sh final func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  `eval_expr cx (TypeBuiltin ann (AbiEncode F mid) ty [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. ((case evaluate_type_builtin cx (AbiEncode F mid) ty [expr_type e] [v] of
        INL w => INL (Value w) | INR err => INR (Error err)),ee))` by
    (irule eval_expr_singleton_type_builtin_action >>
     simp[type_builtin_args_length_ok_def]) >>
  asm_rewrite_tac[] >> irule sha256_expr_sim_mem_suffix >>
  first_assum (irule_at (Pat `expr_sim_mem _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> Cases_on `exc` >> Cases_on `r` >> simp[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]) >>
  rpt strip_tac >> suspend "success"
QED

Resume compile_abi_encode_word_vv_sim_mem[success]:
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) abi_encode_operand_success_type) >>
  disch_then (qspecl_then [`env`,`ce`] mp_tac) >> simp[] >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at sm x` by metis_tac[compile_lower_value_var] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     drule eval_expr_preserves_scopes_dom >> strip_tac >>
     drule read_result_state >> strip_tac >> gvs[]) >>
  drule_all abi_encode_nonword_source_result >> strip_tac >>
  `?cnt actual. gas_path_mem ctx func t cnt (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode F mid) ty [e])
      es sa final s0 ee (Value (BytesV (abi_encode_method_id_bytes mid ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))
      (LocatedValue ann (mk_ptr out LocMemory)) actual /\
    vv_store_bound cx ann
      (lowered_value_type ce (TypeBuiltin ann (AbiEncode F mid) ty [e])) ee
      (Value (BytesV (abi_encode_method_id_bytes mid ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))
      (LocatedValue ann (mk_ptr out LocMemory)) actual /\
    alloca_history func actual /\ t.vs_alloca_next <= actual.vs_alloca_next` by
    (irule abi_encode_word_success_mem >>
     simp[] >> conj_tac >- (qexists `env` >> simp[]) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     gvs[]) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qexists_tac `REPLICATE cnt F` >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (Value (BytesV (abi_encode_method_id_bytes mid ++
    enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))`,
    `ee`, `OK actual`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, expr_type_def]
QED

Finalise compile_abi_encode_word_vv_sim_mem
