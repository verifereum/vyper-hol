Theory bodyPtrPrecompileBuiltinsArithmeticResidual
Ancestors bodyPtrPrecompileBuiltinsArithmeticInput bodyPtrPrecompileBuiltinsStagedOutput
          bodyPtrPrecompileBuiltinsArithmeticValue bodyPtrPrecompileBuiltinsArithmeticSource
          bodyPtrPrecompileBuiltinsFullOutputFrame
          bodyPtrPrecompileBuiltinsRecoveryResidual bodyPtrPrecompileBuiltinsPrefixFrames
          bodyPtrPrecompileBuiltinsContinuationFrame
          exprSimPtrLiteralBuffer ghostPcTransportPtr fragGasPathPtr fragGasSeqPtr
          exprSimECArith exprSimDefs exprSimProps compileEnv venomState venomInst venomExecSemantics
          rich_list list byte bodyPtrDefs wordArgsPtr stmtSimDeclPath exprSimWordArgs
          venomCallOracleDefs extCallOracle bodyPtrPrecompileBuiltinsBounds exprLoweringProps valueEncoding valueEncodingDefs valueEncodingProps exprSimPrecompiles


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
  ?t G' tn' out aid.
    gas_path_ptr D 0 ctx fn PG G tn s 1 G' tn' (OK t) /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sf sb) /\
    eval_operand res t = SOME out /\
    FLOOKUP t.vs_allocas aid = SOME (w2n out,64) /\
    sf.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    mem_bytes_at (w2n out) 64 t.vs_memory =
      word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T /\
    stmt_state_rel ctx fn cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) t /\
    wb_frame cenv es (es with outcomes := SOME (DROP 1 s.vs_outcomes)) sf s t /\
    ghost_inv d cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G' tn' t /\
    ghost_kept cenv es sf G tn s G' tn' /\
    ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) (mk_ec_result (x,y)) res G' tn' t /\
    ptr_buf_ok cenv (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul args) res G' t /\
    vv_post ctx fn cenv cx (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul args)
      es sf sb s (es with outcomes := SOME (DROP 1 s.vs_outcomes)) (Value (mk_ec_result (x,y)))
      (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb))) t /\
    ptr_vv_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Value (mk_ec_result (x,y)))
      (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb)))
      (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G' tn' t
Proof
  strip_tac >> drule_all ec_point_pointer_bound >> strip_tac >>
  drule_all ecmul_framed_input >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sf sz)` >>
  `isPREFIX (emitted_insts sf sz ++ emitted_insts sz sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sf sz)` by
    simp[Abbr `u`] >>
  `eval_operand (Var src) t = SOME b /\ eval_operand (Var dst) t = SOME c` by
    gvs[eval_operand_def] >>
  `precompile_result (venom_call_request u 7w 0w b 96w T).cr_target
     (venom_call_request u 7w 0w b 96w T).cr_data =
     SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T))` by
    (simp[venom_call_request_def, read_memory_def, GSYM mem_bytes_at_def,
       wordsTheory.dimword_def, wordsTheory.w2w_n2w,
       fcpLib.INDEX_CONV ``dimindex(:160)``, Abbr `u`] >>
     irule (cj 2 ec_precompile_success) >> simp[]) >>
  `res = Var dst` by
    (qpat_assum `_ sz = (res,sb)` (mp_then Any mp_tac (cj 1 computed_suffix_shape)) >> simp[]) >>
  `computed_precompile (venom_call_request u 7w 0w b 96w T)` by
    (qpat_assum `precompile_result _ _ = SOME (SOME _)` mp_tac >>
     simp[NoAsms, computed_precompile_def, venom_call_request_def]) >>
  drule_all return_pointer_reservation_mono >> strip_tac >>
  suspend "staged"
QED

Resume ecmul_residual_success[staged]:
  `ptr_covers Gf tnf src t (w2n (96w:bytes32)) /\
   ptr_covers Gf tnf dst t (w2n (64w:bytes32)) /\
   (!i. w2n b <= i /\ i < w2n b + w2n (96w:bytes32) ==> i NOTIN tnf.t_mem)` by
    simp[wordsTheory.dimword_def] >>
  `(!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n c) (w2n (64w:bytes32)) b sz) /\
   (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint (w2n c) (w2n (64w:bytes32)) b sz) /\
   (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
     regions_disjoint (w2n c) (w2n (64w:bytes32)) off (type_memory_size tv))` by
    (simp[NoAsms, wordsTheory.dimword_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `res = Var dst` (fn eq =>
    qpat_assum `_ sz = (res,sb)`
      (mp_then Any drule_all staged_full_output_paths o REWRITE_RULE [eq])) >>
  strip_tac >>
  qpat_x_assum `!data. _` (qspec_then
    `word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T` mp_tac) >>
  (impl_tac
   >- (simp[NoAsms, wordsTheory.dimword_def, LENGTH_word_to_bytes,
            fcpLib.INDEX_CONV ``dimindex(:256)``] >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qexistsl [`co`,`rest`] >> simp[])) >> strip_tac >>
  suspend "result"
QED

Resume ecmul_residual_success[result]:
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
  `mem_bytes_at (w2n c) 64 q.vs_memory =
      word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T` by
    (qpat_assum `q.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
     qspecl_then [`w2n c`, `word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T`, `u`]
       mp_tac write_memory_mem_bytes_at_same >>
     simp[NoAsms, LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``, TAKE_LENGTH_TOO_LONG]) >>
  `FLOOKUP q.vs_allocas aid = SOME (w2n c,64)` by simp[] >>
  `!name b sz. local_region cenv (es with outcomes := SOME (DROP 1 s.vs_outcomes)).scopes q name b sz ==>
      regions_disjoint (w2n c) 64 b sz` by
    (simp[NoAsms] >> qpat_assum `!name b sz. local_region _ _ q _ _ _ ==> _`
      (ACCEPT_TAC o SRULE [wordsTheory.dimword_def])) >>
  `!c. ECMul <> Concat c` by simp[] >>
  drule_all ec_builtin_result_posts >>
  disch_then (qspec_then `args` strip_assume_tac) >>
  qexistsl [`q`,`G2`,`tn2`,`c`,`aid`] >>
  qpat_x_assum `res = Var dst` SUBST_ALL_TAC >>
  simp[] >> irule ec_result_pointer_vv_ok >> first_assum ACCEPT_TAC
QED
Finalise ecmul_residual_success

Theorem ecadd_residual_success:
  compile_ecadd_points point other sf = (res,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ ~ctx_has_dalloca ctx /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts fn)) /\
  ghost_inv d cenv cx es G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vp point s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vq other s /\
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) vp point G tn s /\
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) vq other G tn s /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) vp /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) vq /\
  eval_operand point s = SOME a1 /\ eval_operand other s = SOME a2 /\
  (!p. MEM (Var p) [point;other] ==> not_fresh_at sf p) /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sf sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  vfmExecution$ecadd (w2n (mload (w2n a1) s),w2n (mload (w2n a1+32) s))
    (w2n (mload (w2n a2) s),w2n (mload (w2n a2+32) s)) = SOME (x,y) /\
  (?co rest. s.vs_outcomes = co::rest /\ co.co_success) ==>
  ?t G' tn' out aid.
    gas_path_ptr D 0 ctx fn PG G tn s 1 G' tn' (OK t) /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sf sb) /\
    eval_operand res t = SOME out /\
    FLOOKUP t.vs_allocas aid = SOME (w2n out,64) /\
    sf.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    mem_bytes_at (w2n out) 64 t.vs_memory =
      word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T /\
    stmt_state_rel ctx fn cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) t /\
    wb_frame cenv es (es with outcomes := SOME (DROP 1 s.vs_outcomes)) sf s t /\
    ghost_inv d cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G' tn' t /\
    ghost_kept cenv es sf G tn s G' tn' /\
    ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) (mk_ec_result (x,y)) res G' tn' t /\
    ptr_buf_ok cenv (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd args) res G' t /\
    vv_post ctx fn cenv cx (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd args)
      es sf sb s (es with outcomes := SOME (DROP 1 s.vs_outcomes)) (Value (mk_ec_result (x,y)))
      (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb))) t /\
    ptr_vv_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Value (mk_ec_result (x,y)))
      (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res,sb)))
      (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G' tn' t
Proof
  strip_tac >>
  qpat_assum `expr_val_at _ _ _ _ _ _ vp _ _`
    (mp_then Any (drule_all_then strip_assume_tac) ec_point_pointer_bound) >>
  qpat_assum `expr_val_at _ _ _ _ _ _ vq _ _`
    (mp_then Any (drule_all_then strip_assume_tac) ec_point_pointer_bound) >>
  drule_all ecadd_framed_input >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sf sz)` >>
  `isPREFIX (emitted_insts sf sz ++ emitted_insts sz sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sf sz)` by
    simp[Abbr `u`] >>
  `eval_operand (Var src) t = SOME b /\ eval_operand (Var dst) t = SOME c` by
    gvs[eval_operand_def] >>
  `precompile_result (venom_call_request u 6w 0w b 128w T).cr_target
     (venom_call_request u 6w 0w b 128w T).cr_data =
     SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T))` by
    (simp[venom_call_request_def, read_memory_def, GSYM mem_bytes_at_def,
       wordsTheory.dimword_def, wordsTheory.w2w_n2w,
       fcpLib.INDEX_CONV ``dimindex(:160)``, Abbr `u`] >>
     irule (cj 1 ec_precompile_success) >> simp[]) >>
  `res = Var dst` by
    (qpat_assum `_ sz = (res,sb)` (mp_then Any mp_tac (cj 1 computed_suffix_shape)) >> simp[]) >>
  `computed_precompile (venom_call_request u 6w 0w b 128w T)` by
    (qpat_assum `precompile_result _ _ = SOME (SOME _)` mp_tac >>
     simp[NoAsms, computed_precompile_def, venom_call_request_def]) >>
  drule_all return_pointer_reservation_mono >> strip_tac >>
  suspend "staged"
QED

Resume ecadd_residual_success[staged]:
  `ptr_covers Gf tnf src t (w2n (128w:bytes32)) /\
   ptr_covers Gf tnf dst t (w2n (64w:bytes32)) /\
   (!i. w2n b <= i /\ i < w2n b + w2n (128w:bytes32) ==> i NOTIN tnf.t_mem)` by
    simp[wordsTheory.dimword_def] >>
  `(!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n c) (w2n (64w:bytes32)) b sz) /\
   (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint (w2n c) (w2n (64w:bytes32)) b sz) /\
   (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
     regions_disjoint (w2n c) (w2n (64w:bytes32)) off (type_memory_size tv))` by
    (simp[NoAsms, wordsTheory.dimword_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `res = Var dst` (fn eq =>
    qpat_assum `_ sz = (res,sb)`
      (mp_then Any drule_all staged_full_output_paths o REWRITE_RULE [eq])) >>
  strip_tac >>
  qpat_x_assum `!data. _` (qspec_then
    `word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T` mp_tac) >>
  (impl_tac
   >- (simp[NoAsms, wordsTheory.dimword_def, LENGTH_word_to_bytes,
            fcpLib.INDEX_CONV ``dimindex(:256)``] >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qexistsl [`co`,`rest`] >> simp[])) >> strip_tac >>
  suspend "result"
QED

Resume ecadd_residual_success[result]:
  `ptr_covers G2 tn2 dst q 64 /\
   (!i. w2n c <= i /\ i < w2n c+64 ==> i NOTIN tn2.t_mem)` by
    (conj_tac
     >- (qpat_assum `ptr_covers G2 tn2 dst q _`
           (ACCEPT_TAC o SRULE [wordsTheory.dimword_def])) >>
     qpat_assum `!i. w2n c <= i /\ i < w2n c + w2n _ ==> _`
       (ACCEPT_TAC o SRULE [wordsTheory.dimword_def])) >>
  `mem_bytes_at (w2n c) 64 q.vs_memory =
      word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T` by
    (qpat_assum `q.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
     qspecl_then [`w2n c`, `word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T`, `u`]
       mp_tac write_memory_mem_bytes_at_same >>
     simp[NoAsms, wordsTheory.dimword_def, LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, TAKE_LENGTH_TOO_LONG]) >>
  `FLOOKUP q.vs_allocas aid = SOME (w2n c,64)` by simp[] >>
  `!name b sz. local_region cenv (es with outcomes := SOME (DROP 1 s.vs_outcomes)).scopes q name b sz ==>
      regions_disjoint (w2n c) 64 b sz` by
    (simp[NoAsms] >> qpat_assum `!name b sz. local_region _ _ q _ _ _ ==> _`
      (ACCEPT_TAC o SRULE [wordsTheory.dimword_def])) >>
  `!c. ECAdd <> Concat c` by simp[] >>
  drule_all ec_builtin_result_posts >>
  disch_then (qspec_then `args` strip_assume_tac) >>
  qexistsl [`q`,`G2`,`tn2`,`c`,`aid`] >>
  qpat_x_assum `res = Var dst` SUBST_ALL_TAC >> simp[] >>
  irule ec_result_pointer_vv_ok >> first_assum ACCEPT_TAC
QED
Finalise ecadd_residual_success

(* Failed arithmetic and oracle calls both terminate with a checked revert. *)
Theorem ecmul_residual_abort:
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
  (vfmExecution$ecmul (w2n (mload (w2n a) s),w2n (mload (w2n a+32) s)) (w2n w) = NONE \/
   s.vs_outcomes = [] \/ ?co rest. s.vs_outcomes = co::rest /\ ~co.co_success) ==>
  ?q n G' tn'. gas_path_ptr D 0 ctx fn PG G tn s n G' tn' (Abort Revert_abort q)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ec_point_pointer_bound >> strip_tac >>
  drule_all ecmul_framed_input >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sf sz)` >>
  `isPREFIX (emitted_insts sf sz ++ emitted_insts sz sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sf sz)` by
    simp[Abbr `u`] >>
  `eval_operand (Var src) t = SOME b /\ eval_operand (Var dst) t = SOME c` by
    gvs[eval_operand_def] >>
  `computed_precompile (venom_call_request u 7w 0w b 96w T)` by
    simp[computed_precompile_def, venom_call_request_def, read_memory_def,
      GSYM mem_bytes_at_def, wordsTheory.dimword_def, wordsTheory.w2w_n2w,
      fcpLib.INDEX_CONV ``dimindex(:160)``, Abbr `u`, ec_precompile_words] >>
  `res = Var dst` by
    (qpat_assum `_ sz = (res,sb)` (mp_then Any mp_tac (cj 1 computed_suffix_shape)) >> simp[]) >>
  drule_all return_pointer_reservation_mono >> strip_tac >>
  suspend "staged"
QED

Resume ecmul_residual_abort[staged]:
  `ptr_covers Gf tnf src t (w2n (96w:bytes32)) /\
   ptr_covers Gf tnf dst t (w2n (64w:bytes32)) /\
   (!i. w2n b <= i /\ i < w2n b + w2n (96w:bytes32) ==> i NOTIN tnf.t_mem)` by
    simp[wordsTheory.dimword_def] >>
  `(!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n c) (w2n (64w:bytes32)) b sz) /\
   (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint (w2n c) (w2n (64w:bytes32)) b sz) /\
   (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
     regions_disjoint (w2n c) (w2n (64w:bytes32)) off (type_memory_size tv))` by
    (simp[NoAsms, wordsTheory.dimword_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `res = Var dst` (fn eq =>
    qpat_assum `_ sz = (res,sb)`
      (mp_then Any drule_all staged_full_output_paths o REWRITE_RULE [eq])) >>
  strip_tac >>
  qpat_x_assum `(_ \/ _ \/ _) ==> _` mp_tac >>
  (impl_tac
   >- (simp[venom_call_request_def, read_memory_def, GSYM mem_bytes_at_def,
       wordsTheory.dimword_def, wordsTheory.w2w_n2w,
       fcpLib.INDEX_CONV ``dimindex(:160)``, Abbr `u`, ec_precompile_words] >>
       metis_tac[])) >>
  strip_tac >> goal_assum (drule_at Any)
QED
Finalise ecmul_residual_abort

Theorem ecadd_residual_abort:
  compile_ecadd_points point other sf = (res,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ ~ctx_has_dalloca ctx /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts fn)) /\
  ghost_inv d cenv cx es G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vp point s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vq other s /\
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) vp point G tn s /\
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) vq other G tn s /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) vp /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) vq /\
  eval_operand point s = SOME a1 /\ eval_operand other s = SOME a2 /\
  (!p. MEM (Var p) [point;other] ==> not_fresh_at sf p) /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sf sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  (vfmExecution$ecadd (w2n (mload (w2n a1) s),w2n (mload (w2n a1+32) s))
     (w2n (mload (w2n a2) s),w2n (mload (w2n a2+32) s)) = NONE \/
   s.vs_outcomes = [] \/ ?co rest. s.vs_outcomes = co::rest /\ ~co.co_success) ==>
  ?q n G' tn'. gas_path_ptr D 0 ctx fn PG G tn s n G' tn' (Abort Revert_abort q)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `expr_val_at _ _ _ _ _ _ vp _ _`
    (mp_then Any (drule_all_then strip_assume_tac) ec_point_pointer_bound) >>
  qpat_assum `expr_val_at _ _ _ _ _ _ vq _ _`
    (mp_then Any (drule_all_then strip_assume_tac) ec_point_pointer_bound) >>
  drule_all ecadd_framed_input >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sf sz)` >>
  `isPREFIX (emitted_insts sf sz ++ emitted_insts sz sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sf sz)` by
    simp[Abbr `u`] >>
  `eval_operand (Var src) t = SOME b /\ eval_operand (Var dst) t = SOME c` by
    gvs[eval_operand_def] >>
  `computed_precompile (venom_call_request u 6w 0w b 128w T)` by
    simp[computed_precompile_def, venom_call_request_def, read_memory_def,
      GSYM mem_bytes_at_def, wordsTheory.dimword_def, wordsTheory.w2w_n2w,
      fcpLib.INDEX_CONV ``dimindex(:160)``, Abbr `u`, ec_precompile_words] >>
  `res = Var dst` by
    (qpat_assum `_ sz = (res,sb)` (mp_then Any mp_tac (cj 1 computed_suffix_shape)) >> simp[]) >>
  drule_all return_pointer_reservation_mono >> strip_tac >>
  suspend "staged"
QED

Resume ecadd_residual_abort[staged]:
  `ptr_covers Gf tnf src t (w2n (128w:bytes32)) /\
   ptr_covers Gf tnf dst t (w2n (64w:bytes32)) /\
   (!i. w2n b <= i /\ i < w2n b + w2n (128w:bytes32) ==> i NOTIN tnf.t_mem)` by
    simp[wordsTheory.dimword_def] >>
  `(!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n c) (w2n (64w:bytes32)) b sz) /\
   (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint (w2n c) (w2n (64w:bytes32)) b sz) /\
   (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
     regions_disjoint (w2n c) (w2n (64w:bytes32)) off (type_memory_size tv))` by
    (simp[NoAsms, wordsTheory.dimword_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `res = Var dst` (fn eq =>
    qpat_assum `_ sz = (res,sb)`
      (mp_then Any drule_all staged_full_output_paths o REWRITE_RULE [eq])) >>
  strip_tac >>
  qpat_x_assum `(_ \/ _ \/ _) ==> _` mp_tac >>
  (impl_tac
   >- (simp[venom_call_request_def, read_memory_def, GSYM mem_bytes_at_def,
       wordsTheory.dimword_def, wordsTheory.w2w_n2w,
       fcpLib.INDEX_CONV ``dimindex(:160)``, Abbr `u`, ec_precompile_words] >>
       metis_tac[])) >>
  strip_tac >> goal_assum (drule_at Any)
QED
Finalise ecadd_residual_abort

Theorem arithmetic_source_tail_cases:
  (bt = ECAdd \/ bt = ECMul) ==>
  ec_source_tail cx ann bt tys vs es =
    case exprSimWordArgs$builtin_result cx es.accounts ann bt tys vs of
      INR ex => (INR ex,es)
    | INL v =>
        case es.outcomes of
          NONE => (INL (Value v),es)
        | SOME [] => (INR (Error (RuntimeError "precompile failed")),es)
        | SOME (co::rest) =>
            (if call_outcome_success co then INL (Value v)
             else INR (Error (RuntimeError "precompile failed")),
             es with outcomes := SOME rest)
Proof
  disch_tac >>
  `precompile_builtin bt` by gvs[vyperInterpreterTheory.precompile_builtin_def] >>
  simp[ec_source_tail_def] >>
  Cases_on `exprSimWordArgs$builtin_result cx es.accounts ann bt tys vs` >>
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       vyperInterpreterTheory.precompile_call_success_def] >>
  Cases_on `es.outcomes` >> simp[vyperStateTheory.return_def] >>
  rename1 `es.outcomes = SOME cos` >> Cases_on `cos` >>
  simp[vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  rename1 `co.co_success` >> Cases_on `co.co_success` >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED
