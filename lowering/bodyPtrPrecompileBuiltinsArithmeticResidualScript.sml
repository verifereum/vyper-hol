Theory bodyPtrPrecompileBuiltinsArithmeticResidual
Ancestors bodyPtrPrecompileBuiltinsArithmeticInput
          bodyPtrPrecompileBuiltinsArithmeticValue bodyPtrPrecompileBuiltinsArithmeticSource
          bodyPtrPrecompileBuiltinsFullOutputFrame
          bodyPtrPrecompileBuiltinsRecoveryResidual bodyPtrPrecompileBuiltinsPrefixFrames
          bodyPtrPrecompileBuiltinsContinuationFrame
          exprSimPtrLiteralBuffer ghostPcTransportPtr fragGasPathPtr fragGasSeqPtr
          exprSimDefs exprSimProps compileEnv venomState venomInst venomExecSemantics
          rich_list list byte bodyPtrDefs wordArgsPtr stmtSimDeclPath exprSimWordArgs
          venomCallOracleDefs extCallOracle bodyPtrPrecompileBuiltinsBounds exprLoweringProps valueEncoding valueEncodingProps exprSimPrecompiles

(* Shared entry normalization for both arithmetic residuals.  Runtime effects
   and the counted path refer to the same staged endpoint and ghost pair. *)
Theorem arithmetic_staging_continuation:
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) pre /\
  run_inst_seq pre s = OK t /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn pre
    (s with vs_inst_idx := k) Gf tnf) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (pre ++ post) (DROP s.vs_inst_idx bb.bb_instructions) /\
  u = t with vs_inst_idx := s.vs_inst_idx + LENGTH pre ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK u) /\
  ~u.vs_halted /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX post (DROP u.vs_inst_idx bb.bb_instructions) /\
  u.vs_outcomes = s.vs_outcomes /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
  u.vs_transient = s.vs_transient /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  strip_tac >>
  `isPREFIX pre (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  drule_all staging_counted_prefix >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i pre ==> _ \/ _` drule >> strip_tac >>
     gvs[is_terminator_def]) >>
  drule_all straightline_continuation_placement >> strip_tac >>
  drule_all staging_sequence_outcomes >> strip_tac >>
  drule_all staging_prefix_nonmemory_frames >> strip_tac >>
  gvs[]
QED

Theorem precompile_pointer_cursor:
  (ptr_val_ok cx ty v op G tn (s with vs_inst_idx := k) <=>
   ptr_val_ok cx ty v op G tn s) /\
  (ptr_buf_ok cenv e op G (s with vs_inst_idx := k) <=>
   ptr_buf_ok cenv e op G s)
Proof
  simp[ptr_val_ok_def, ptr_mem_ok_def, ptr_buf_ok_def,
       eval_operand_def, lookup_var_def]
QED

Theorem ecmul_residual_success:
  compile_ecmul_point point scalar sf = (res,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ ~ctx_has_dalloca ctx /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts fn)) /\
  ghost_inv d cenv cx es G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v point s /\
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v point G tn s /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  eval_operand point s = SOME a /\ eval_operand scalar s = SOME w /\
  op_taint tn scalar = {} /\ (!l. scalar <> Label l) /\
  (!p. MEM (Var p) [point;scalar] ==> not_fresh_at sf p) /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sf sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  vfmExecution$ecmul (w2n (mload (w2n a) s),w2n (mload (w2n a+32) s)) (w2n w) = SOME (x,y) /\
  (?co rest. s.vs_outcomes = co::rest /\ co.co_success) ==>
  ?t G' tn' out.
    gas_path_ptr D 0 ctx fn PG G tn s 1 G' tn' (OK t) /\
    eval_operand res t = SOME out /\
    mem_bytes_at (w2n out) 64 t.vs_memory =
      word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T /\
    stmt_state_rel ctx fn cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) t /\
    wb_frame cenv es sf s t /\
    ghost_inv d cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G' tn' t /\
    ghost_kept cenv es sf G tn s G' tn' /\
    ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) (mk_ec_result (x,y)) res G' tn' t /\
    ptr_buf_ok cenv (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul args) res G' t
Proof
  strip_tac >> drule_all ec_point_pointer_bound >> strip_tac >>
  drule_all ecmul_framed_input >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sf sz)` >>
  `isPREFIX (emitted_insts sf sz ++ emitted_insts sz sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sf sz)` by
    simp[Abbr `u`] >>
  drule_all arithmetic_staging_continuation >> strip_tac >>
  suspend "suffix_entry"
QED

Resume ecmul_residual_success[suffix_entry]:
  `eval_operand (Var src) u = SOME b /\ eval_operand (Var dst) u = SOME c` by
    gvs[Abbr `u`, eval_operand_def, lookup_var_def] >>
  `stmt_state_rel ctx fn cenv cx es u` by simp[Abbr `u`, stmt_state_rel_inst_idx] >>
  `ghost_inv d cenv cx es Gf tnf u` by
    simp[Abbr `u`, SRULE [] (Q.INST [`gs` |-> `es.gas_obs`]
      literal_ptr_ghost_inv_normalize)] >>
  `local_ptrs_rel fn cenv es.scopes u` by
    (qpat_assum `stmt_state_rel ctx fn cenv cx es u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[stmt_state_rel_def, state_rel_def]) >>
  `ptr_covers Gf tnf src u (w2n (96w:bytes32)) /\
   ptr_covers Gf tnf dst u (w2n (64w:bytes32))` by
    simp[Abbr `u`, wordsTheory.dimword_def] >>
  `!i. w2n b <= i /\ i < w2n b + w2n (96w:bytes32) ==> i NOTIN tnf.t_mem` by
    simp[wordsTheory.dimword_def] >>
  `precompile_result (venom_call_request u 7w 0w b 96w T).cr_target
     (venom_call_request u 7w 0w b 96w T).cr_data =
     SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T))` by
    (simp[venom_call_request_def, read_memory_def, GSYM mem_bytes_at_def,
       wordsTheory.dimword_def, wordsTheory.w2w_n2w,
       fcpLib.INDEX_CONV ``dimindex(:160)``, Abbr `u`] >>
     irule (cj 2 ec_precompile_success) >> simp[]) >>
  suspend "apply_suffix"
QED

Resume ecmul_residual_success[apply_suffix]:
  `res = Var dst` by
    (qpat_assum `_ sz = (res,sb)` (mp_then Any mp_tac (cj 1 computed_suffix_shape)) >> simp[]) >>
  `computed_precompile (venom_call_request u 7w 0w b 96w T)` by
    (qpat_assum `precompile_result _ _ = SOME (SOME _)` mp_tac >>
     simp[NoAsms, computed_precompile_def, venom_call_request_def]) >>
  drule_all return_pointer_reservation_mono >> strip_tac >>
  `(!name lo len. local_region cenv es.scopes u name lo len ==>
      regions_disjoint (w2n c) (w2n (64w:bytes32)) lo len) /\
   (!aid lo len. aid < sf.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (lo,len) ==>
      regions_disjoint (w2n c) (w2n (64w:bytes32)) lo len)` by
    (conj_tac
     >- (map_every qx_gen_tac [`name`,`b0`,`len`] >> strip_tac >>
         `local_region cenv es.scopes t name b0 len` by
           gvs[Abbr `u`, local_region_def, lookup_var_def] >>
         simp[wordsTheory.dimword_def] >> metis_tac[]) >>
     simp[Abbr `u`, wordsTheory.dimword_def] >> first_assum ACCEPT_TAC) >>
  `allocas_from 0 u /\
   tnf.t_stor SUBSET D.d_stor u.vs_call_ctx.cc_address
     (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
   tnf.t_trans SUBSET D.d_trans u.vs_call_ctx.cc_address
     (u.vs_transient u.vs_call_ctx.cc_address)` by simp[] >>
  `cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
     regions_disjoint (w2n c) (w2n (64w:bytes32)) off (type_memory_size tv)` by
    (simp[NoAsms, wordsTheory.dimword_def] >> first_assum ACCEPT_TAC) >>
  qpat_assum `res = Var dst` (fn eq =>
    qpat_assum `_ sz = (res,sb)`
      (mp_then Any drule_all computed_full_output_framed_paths o REWRITE_RULE [eq])) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "suffix_success"
QED
Resume ecmul_residual_success[suffix_success]:
  qpat_x_assum `!data. _` (qspec_then
    `word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T` mp_tac) >>
  (impl_tac
   >- (simp[NoAsms, wordsTheory.dimword_def, LENGTH_word_to_bytes,
            fcpLib.INDEX_CONV ``dimindex(:256)``] >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qexistsl [`co`,`rest`] >> simp[])) >> strip_tac >>
  `ptr_covers G2 tn2 dst q 64 /\
   (!i. w2n c <= i /\ i < w2n c+64 ==> i NOTIN tn2.t_mem) /\
   q.vs_memory = (write_memory_with_expansion (w2n c)
     (TAKE 64 (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T)) u).vs_memory` by
    (conj_tac
     >- (qpat_assum `ptr_covers G2 tn2 dst q _`
           (ACCEPT_TAC o SRULE [wordsTheory.dimword_def])) >>
     conj_tac
     >- (qpat_assum `!i. w2n c <= i /\ i < w2n c + w2n _ ==> _`
           (ACCEPT_TAC o SRULE [wordsTheory.dimword_def])) >>
     qpat_assum `q.vs_memory = _` (ACCEPT_TAC o SRULE [wordsTheory.dimword_def])) >>
  drule_all ec_builtin_result_ptr_ok >> strip_tac >>
  `mem_bytes_at (w2n c) 64 q.vs_memory =
      word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T` by
    (qpat_assum `q.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
     qspecl_then [`w2n c`, `word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T`, `u`]
       mp_tac write_memory_mem_bytes_at_same >>
     simp[NoAsms, LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``, TAKE_LENGTH_TOO_LONG]) >>
  `wb_frame cenv es sf s u` by simp[Abbr `u`, precompile_frame_cursor] >>
  `sf.cs_next_var <= sf.cs_next_var /\ sf.cs_next_id <= sf.cs_next_id /\
   MAP FDOM es.scopes = MAP FDOM es.scopes` by simp[] >>
  drule_all ghost_kept_wb_trans >> strip_tac >>
  drule_all wb_frame_trans >> strip_tac >>
  drule_all gas_path_ptr_then >> strip_tac >>
  suspend "pack_success"
QED
Resume ecmul_residual_success[pack_success]:
  qexistsl [`q with vs_inst_idx := u.vs_inst_idx+3`,`G2`,`tn2`,`c`] >>
  conj_tac >- (fs[] >> first_assum ACCEPT_TAC) >>
  simp[NoAsms, stmt_state_rel_inst_idx, precompile_frame_cursor,
       SRULE [] (Q.INST [`gs` |-> `es.gas_obs`] literal_ptr_ghost_inv_normalize)] >>
  qpat_x_assum `!cx cenv bt args. _`
    (qspecl_then [`cx`,`cenv`,`ECMul`,`args`] strip_assume_tac) >>
  qpat_x_assum `res = Var dst` SUBST_ALL_TAC >>
  qpat_x_assum `u.vs_outcomes = s.vs_outcomes` (fn eq =>
    rule_assum_tac (REWRITE_RULE [eq])) >>
  pure_rewrite_tac[precompile_pointer_cursor] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise ecmul_residual_success
