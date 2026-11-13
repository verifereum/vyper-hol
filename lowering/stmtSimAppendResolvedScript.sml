(* Append uses the location and element type of the resolved target. *)
Theory stmtSimAppendResolved
Ancestors
  loweringPosts stmtLowering exprLowering compileEnv emitHelper emitHelperProps
  exprLoweringProps venomState venomInst venomExecSemantics
  stateFrame list words

Theorem append_resolved_word_code_parts:
  stmt_env cenv lctx ty (Append target e) sa = (c,sf) /\
  compile_get_target_ptr compile_expr cenv target sa =
    ((bop,SOME loc,SOME (ValPT (ArrayT elem (Dynamic cap)))),st) /\
  is_word_type elem ==>
  c = cenv /\ ?vop sm.
    lower_value compile_expr cenv elem e st = (vop,sm) /\
    compile_dynarray_append cenv bop vop (word_scale loc)
      (elem_size_in_location cenv loc elem) elem (lowered_value_type cenv e)
      cap T (load_opc_for loc) (store_opc_for loc) sm = ((),sf)
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, Once compile_stmt_def] >>
  Cases_on `lower_value compile_expr cenv elem e st` >>
  rename1 `lower_value _ _ _ _ _ = (vop,sm)` >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = (u,_)` >>
  Cases_on `u` >> simp[]
QED

Theorem append_memory_step_frame[local]:
  MEM i.inst_opcode [MLOAD; LT; ADD; MUL; ASSERT] /\
  step_inst_base i s = OK t ==> state_frame t = state_frame s
Proof
  pure_rewrite_tac[listTheory.MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, opcode_case_def,
    venomInstTheory.instruction_accessors, venomInstTheory.instruction_accfupds,
    combinTheory.K_THM] >>
  simp[exec_read1_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def]
QED

Theorem append_memory_seq_frame[local]:
  EVERY (\i. MEM i.inst_opcode [MLOAD; LT; ADD; MUL; ASSERT]) code /\
  run_inst_seq code s = OK t ==> state_frame t = state_frame s
Proof
  strip_tac >> irule run_inst_seq_preserves_field >>
  goal_assum $ drule_at Any >> rpt strip_tac >>
  irule append_memory_step_frame >> gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem append_memory_check_run[local]:
  emit_op MLOAD [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  eval_operand bop s = SOME bp /\ fresh_vars_wrt st0 s /\
  cap < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st0 st2) s = OK t /\
    eval_operand valid t =
      SOME (bool_to_word (w2n (mload (w2n bp) s) < cap)) /\
    eval_operand lop t = SOME (mload (w2n bp) s) /\
    same_blocks st0 st2 /\ fresh_vars_wrt st2 t /\
    state_frame t = state_frame s /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule_all emit_op_MLOAD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 st1) s = OK s1` >>
  `eval_operand (Lit (n2w cap)) s1 = SOME (n2w cap)` by
    simp[eval_operand_def] >>
  drule_all emit_op_LT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) s1 = OK s2` >>
  imp_res_tac inst_extends_emit_op >>
  `run_inst_seq (emitted_insts st0 st2) s = OK s2` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s1`, `st1`] >> simp[]) >>
  `state_frame s2 = state_frame s` by
    (irule append_memory_seq_frame >>
     qexists_tac `emitted_insts st0 st2` >> simp[] >>
     `emitted_insts st0 st2 = emitted_insts st0 st1 ++
        emitted_insts st1 st2` by
       metis_tac[inst_extends_def, emitted_insts_append] >>
     imp_res_tac emitted_insts_emit_op >> simp[EVERY_APPEND, mk_inst_def]) >>
  qexists_tac `s2` >> gvs[same_blocks_def, wordsTheory.w2n_n2w] >> metis_tac[]
QED

Theorem append_memory_guard_run[local]:
  emit_op MLOAD [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  emit_void ASSERT [valid] st2 = ((),st3) /\
  eval_operand bop s = SOME bp /\ fresh_vars_wrt st0 s /\
  cap < dimword (:256) /\ w2n (mload (w2n bp) s) < cap ==>
  ?t. run_inst_seq (emitted_insts st0 st3) s = OK t /\
    eval_operand lop t = SOME (mload (w2n bp) s) /\
    same_blocks st0 st3 /\ fresh_vars_wrt st3 t /\
    state_frame t = state_frame s /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule_all append_memory_check_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 st2) s = OK s2` >>
  `eval_operand valid s2 = SOME 1w` by gvs[bool_to_word_def] >>
  `1w:bytes32 <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st0 st2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st0 st3) s = OK s2` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s2`, `st2`] >> simp[]) >>
  qexists_tac `s2` >> gvs[same_blocks_def] >> metis_tac[]
QED

Theorem append_memory_address_run[local]:
  emit_op ADD [bop; Lit 32w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 32w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  eval_operand bop s = SOME bp /\ eval_operand lop s = SOME len /\
  fresh_vars_wrt st3 s ==>
  ?t. run_inst_seq (emitted_insts st3 st6) s = OK t /\
    eval_operand pop t = SOME (bp + 32w + len * 32w) /\
    same_blocks st3 st6 /\ fresh_vars_wrt st6 t /\
    state_frame t = state_frame s /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st3 st4) s = OK s4` >>
  `eval_operand lop s4 = SOME len /\ eval_operand (Lit 32w) s4 = SOME 32w` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all emit_op_MUL_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st4 st5) s4 = OK s5` >>
  `eval_operand dop s5 = SOME (bp + 32w)` by metis_tac[] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st5 st6) s5 = OK s6` >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends st3 st5` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st3 st5) s = OK s5` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s4`, `st4`] >> simp[]) >>
  `run_inst_seq (emitted_insts st3 st6) s = OK s6` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s5`, `st5`] >> simp[]) >>
  `state_frame s6 = state_frame s` by
    (irule append_memory_seq_frame >>
     qexists_tac `emitted_insts st3 st6` >> simp[] >>
     `emitted_insts st3 st6 = emitted_insts st3 st4 ++
       emitted_insts st4 st5 ++ emitted_insts st5 st6` by
       metis_tac[inst_extends_trans, inst_extends_def, emitted_insts_append] >>
     imp_res_tac emitted_insts_emit_op >> simp[EVERY_APPEND, mk_inst_def]) >>
  qexists_tac `s6` >> gvs[same_blocks_def] >> metis_tac[]
QED

Theorem append_memory_store_frame[local]:
  state_frame s = state_frame t ==>
  state_frame (mstore addr w s) = state_frame (mstore addr w t)
Proof
  simp[state_frame_def, mstore_def, venom_state_component_equality]
QED

Theorem append_memory_suffix_run[local]:
  emit_op ADD [bop; Lit 32w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 32w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  emit_void MSTORE [pop; vop] st6 = ((),st7) /\
  emit_op ADD [lop; Lit 1w] st7 = (nop,st8) /\
  emit_void MSTORE [bop; nop] st8 = ((),st9) /\
  eval_operand bop s = SOME bp /\ eval_operand lop s = SOME len /\
  eval_operand vop s = SOME w /\ fresh_vars_wrt st3 s ==>
  ?t. run_inst_seq (emitted_insts st3 st9) s = OK t /\
    same_blocks st3 st9 /\ fresh_vars_wrt st9 t /\
    (!op x. eval_operand op s = SOME x ==> eval_operand op t = SOME x) /\
    state_frame t = state_frame
      (mstore (w2n bp) (len + 1w)
        (mstore (w2n (bp + 32w + len * 32w)) w s))
Proof
  strip_tac >> drule_all append_memory_address_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st3 st6) s = OK s6` >>
  `eval_operand vop s6 = SOME w` by metis_tac[] >>
  drule_all emit_void_MSTORE_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st6 st7) s6 = OK s7` >>
  `eval_operand lop s7 = SOME len /\ eval_operand (Lit 1w) s7 = SOME 1w` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st7 st8) s7 = OK s8` >>
  `eval_operand bop s8 = SOME bp` by metis_tac[] >>
  `state_frame s8 = state_frame s7` by
    (irule append_memory_seq_frame >>
     qexists_tac `emitted_insts st7 st8` >> simp[] >>
     imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def]) >>
  drule_all emit_void_MSTORE_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st8 st9) s8 = OK s9` >>
  suspend "frame_and_compose"
QED

Resume append_memory_suffix_run[frame_and_compose]:
  `state_frame s7 = state_frame
    (mstore (w2n (bp + 32w + len * 32w)) w s)` by
    (qpat_x_assum `s7 = _` SUBST1_TAC >>
     irule append_memory_store_frame >> first_assum ACCEPT_TAC) >>
  `state_frame s9 = state_frame
    (mstore (w2n bp) (len + 1w)
      (mstore (w2n (bp + 32w + len * 32w)) w s))` by
    (qpat_x_assum `s9 = _` SUBST1_TAC >>
     irule append_memory_store_frame >> metis_tac[]) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st6 st8` by metis_tac[inst_extends_trans] >>
  `inst_extends st6 st9` by metis_tac[inst_extends_trans] >>
  `inst_extends st3 st6` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st6 st8) s6 = OK s8` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s7`, `st7`] >> simp[]) >>
  `run_inst_seq (emitted_insts st6 st9) s6 = OK s9` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s8`, `st8`] >> simp[]) >>
  `run_inst_seq (emitted_insts st3 st9) s = OK s9` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s6`, `st6`] >> simp[]) >>
  qexists_tac `s9` >> gvs[same_blocks_def] >> metis_tac[]
QED

Finalise append_memory_suffix_run

Theorem append_memory_word_parts[local]:
  compile_dynarray_append cenv bop vop 32 32 dst_ty src_ty cap T
    MLOAD MSTORE sa = ((),sf) <=>
  ?lop valid dop off pop nop st1 st2 st3 st4 st5 st6 st7 st8.
    emit_op MLOAD [bop] sa = (lop,st1) /\
    emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
    emit_void ASSERT [valid] st2 = ((),st3) /\
    emit_op ADD [bop; Lit 32w] st3 = (dop,st4) /\
    emit_op MUL [lop; Lit 32w] st4 = (off,st5) /\
    emit_op ADD [dop; off] st5 = (pop,st6) /\
    emit_void MSTORE [pop; vop] st6 = ((),st7) /\
    emit_op ADD [lop; Lit 1w] st7 = (nop,st8) /\
    emit_void MSTORE [bop; nop] st8 = ((),sf)
Proof
  eq_tac
  >- (simp[compile_dynarray_append_def, comp_ignore_bind_def, comp_bind_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      metis_tac[pairTheory.PAIR, pairTheory.pair_CASES, oneTheory.one]) >>
  strip_tac >>
  simp[compile_dynarray_append_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def]
QED

Theorem append_memory_word_run:
  compile_dynarray_append cenv bop vop 32 32 dst_ty src_ty cap T
    MLOAD MSTORE sa = ((),sf) /\
  eval_operand bop s = SOME bp /\ eval_operand vop s = SOME w /\
  fresh_vars_wrt sa s /\ cap < dimword (:256) /\
  len = w2n (mload (w2n bp) s) /\ len < cap /\
  w2n bp + 32 * (1 + cap) <= dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sf) s = OK t /\
    same_blocks sa sf /\ fresh_vars_wrt sf t /\
    (!op x. eval_operand op s = SOME x ==> eval_operand op t = SOME x) /\
    state_frame t = state_frame
      (mstore (w2n bp) (n2w (len + 1))
        (mstore (w2n bp + 32 * (1 + len)) w s))
Proof
  pure_rewrite_tac[append_memory_word_parts] >> strip_tac >>
  `w2n (mload (w2n bp) s) < cap` by metis_tac[] >>
  drule_all append_memory_guard_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa st3) s = OK s3` >>
  `eval_operand bop s3 = SOME bp /\ eval_operand vop s3 = SOME w /\
   eval_operand lop s3 = SOME (n2w len)` by
    (simp[] >> metis_tac[wordsTheory.n2w_w2n]) >>
  drule_all append_memory_suffix_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st3 sf) s3 = OK fin` >>
  suspend "compose"
QED

Resume append_memory_word_run[compose]:
  `w2n bp + 32 * (1 + len) < dimword (:256) /\
   w2n bp + 32 < dimword (:256) /\ len * 32 < dimword (:256)` by decide_tac >>
  `w2n (bp + 32w + (n2w len:bytes32) * 32w) =
   w2n bp + 32 * (1 + len)` by
    (simp[wordsTheory.word_add_def, wordsTheory.word_mul_def,
          wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac) >>
  `(n2w len:bytes32) = mload (w2n bp) s` by
    metis_tac[wordsTheory.n2w_w2n] >>
  `state_frame fin = state_frame
    (mstore (w2n bp) (n2w (len + 1))
      (mstore (w2n bp + 32 * (1 + len)) w s))` by
    (qpat_x_assum `state_frame fin = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_x_assum `(n2w len:bytes32) = mload (w2n bp) s`
       (fn th => pure_rewrite_tac[GSYM th, wordsTheory.word_add_n2w]) >>
     qpat_x_assum `w2n (bp + 32w + (n2w len:bytes32) * 32w) = _`
       (fn th => pure_rewrite_tac[th]) >>
     irule append_memory_store_frame >> irule append_memory_store_frame >>
     first_assum ACCEPT_TAC) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends sa st3` by metis_tac[inst_extends_trans] >>
  `inst_extends st3 sf` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa sf) s = OK fin` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s3`, `st3`] >> simp[]) >>
  qexists_tac `fin` >> gvs[same_blocks_def] >> metis_tac[]
QED

Finalise append_memory_word_run

Theorem append_memory_word_abort:
  compile_dynarray_append cenv bop vop 32 32 dst_ty src_ty cap T
    MLOAD MSTORE sa = ((),sf) /\
  eval_operand bop s = SOME bp /\ fresh_vars_wrt sa s /\
  cap < dimword (:256) /\ cap <= w2n (mload (w2n bp) s) ==>
  ?g. state_frame g = state_frame s /\
    (!op x. eval_operand op s = SOME x ==> eval_operand op g = SOME x) /\
    run_inst_seq (emitted_insts sa sf) s =
      Abort Revert_abort (revert_state (set_returndata [] g))
Proof
  pure_rewrite_tac[append_memory_word_parts] >> strip_tac >>
  drule_all append_memory_check_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa st2) s = OK g` >>
  `eval_operand valid g = SOME 0w` by
    (gvs[bool_to_word_def] >> decide_tac) >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends sa st2 /\ inst_extends sa st3 /\
   inst_extends st3 sf` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa st3) s =
     Abort Revert_abort (revert_state (set_returndata [] g))` by
    metis_tac[run_inst_seq_emit_extend] >>
  qexists_tac `g` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule run_inst_seq_abort_extends >> qexists_tac `st3` >> simp[]
QED
