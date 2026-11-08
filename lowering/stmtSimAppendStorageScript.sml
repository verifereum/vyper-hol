(* Source and machine boundaries for word storage/transient Append. *)
Theory stmtSimAppendStorage
Ancestors
  bodyAppendStorageFacts vyperState vyperStorage
  vyperStorageBackend vyperValue valueEncoding valueEncodingProofs
  vyperTyping words exprLowering compileEnv emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomState stateFrame

Theorem append_storage_full:
  cap <= w2n (lookup_storage slot (get_storage cx es tr)) ==>
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
    (INR (Error (RuntimeError "append full storage array")), es)
Proof
  strip_tac >>
  simp[Once append_place_def, get_storage_backend_eq, bind_def,
       ignore_bind_def, check_def, assert_def, return_def]
QED

Theorem append_storage_writes:
  w2n (lookup_storage slot (get_storage cx es tr)) < cap ==>
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
  (ignore_bind
    (write_storage_slot cx tr
      (slot + n2w (1 + w2n (lookup_storage slot (get_storage cx es tr)) *
                       type_slot_size tv)) tv v)
    (write_storage_slot cx tr slot (BaseTV (UintT 256))
      (IntV &(w2n (lookup_storage slot (get_storage cx es tr)) + 1)))) es
Proof
  strip_tac >>
  simp[Once append_place_def, get_storage_backend_eq, bind_def,
       ignore_bind_def, check_def, assert_def, return_def]
QED

Theorem append_storage_word_success:
  ~cx.txn.is_static /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\
  len < cap /\ type_slot_size tv = 1 /\
  encode_value tv v = SOME [(0,w)] ==>
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
  (INL (),
   set_storage cx
     (set_storage cx es tr
       (update_storage (slot + n2w (1 + len)) w (get_storage cx es tr))) tr
     (update_storage slot (n2w (len + 1))
       (update_storage (slot + n2w (1 + len)) w (get_storage cx es tr))))
Proof
  strip_tac >> gvs[] >>
  simp[append_storage_writes, ignore_bind_def, bind_def,
       write_storage_slot_eq, apply_writes_def,
       get_storage_after_set, encode_value_def, encode_base_to_slot_def,
       integer_wordTheory.i2w_def]
QED

(* All non-register state is unchanged by the guard and address arithmetic. *)
Theorem append_storage_step_frame[local]:
  MEM i.inst_opcode [SLOAD; TLOAD; LT; ADD; MUL; ASSERT] /\
  step_inst_base i s = OK t ==> state_frame t = state_frame s
Proof
  pure_rewrite_tac[listTheory.MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, opcode_case_def, venomInstTheory.instruction_accessors, venomInstTheory.instruction_accfupds, combinTheory.K_THM] >>
  simp[exec_read1_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def]
QED

Theorem append_storage_seq_frame:
  EVERY (\i. MEM i.inst_opcode [SLOAD; TLOAD; LT; ADD; MUL; ASSERT]) code /\
  run_inst_seq code s = OK t ==> state_frame t = state_frame s
Proof
  strip_tac >> irule run_inst_seq_preserves_field >>
  goal_assum $ drule_at Any >> rpt strip_tac >>
  irule append_storage_step_frame >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem append_storage_store_frame:
  state_frame s = state_frame t ==>
  state_frame (if tr then tstore p w s else sstore p w s) =
  state_frame (if tr then tstore p w t else sstore p w t)
Proof
  Cases_on `tr` >>
  simp[state_frame_def, sstore_def, tstore_def, LET_THM,
       venom_state_component_equality]
QED

Theorem append_storage_check_run:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  eval_operand bop ss = SOME slot /\ fresh_vars_wrt st0 ss /\
  cap < dimword (:256) ==>
  ?ss'. run_inst_seq (emitted_insts st0 st2) ss = OK ss' /\
    eval_operand valid ss' =
      SOME (bool_to_word (w2n (if tr then tload slot ss else sload slot ss) < cap)) /\
    eval_operand lop ss' = SOME (if tr then tload slot ss else sload slot ss) /\
    same_blocks st0 st2 /\ fresh_vars_wrt st2 ss' /\
    state_frame ss' = state_frame ss /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w)
Proof
  strip_tac >>
  `?ss1. run_inst_seq (emitted_insts st0 st1) ss = OK ss1 /\
    eval_operand lop ss1 = SOME (if tr then tload slot ss else sload slot ss) /\
    fresh_vars_wrt st1 ss1 /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss1 = SOME w)` by
    (reverse (Cases_on `tr`) >> gvs[]
     >- (drule_all emit_op_SLOAD_correct >> metis_tac[]) >>
     qspecl_then [`TLOAD`, `tload`] mp_tac emit_op_read1_correct >>
     disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
     simp[step_inst_base_opcode_eqs, exec_read1_def] >> strip_tac >>
     first_x_assum (qspecl_then [`slot`, `ss`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `eval_operand (Lit (n2w cap)) ss1 = SOME (n2w cap)` by
    simp[eval_operand_def] >>
  drule_all emit_op_LT_correct >> strip_tac >>
  imp_res_tac emit_op_extends >>
  drule_all run_inst_seq_chain >> strip_tac >>
  `state_frame ss' = state_frame ss` by
    (irule append_storage_seq_frame >>
     qexists_tac `emitted_insts st0 st2` >>
     conj_tac >- metis_tac[] >>
     drule_all emitted_insts_append >> disch_then SUBST1_TAC >>
     imp_res_tac emitted_insts_emit_op >>
     simp[listTheory.EVERY_APPEND, mk_inst_def] >>
     Cases_on `tr` >> simp[]) >>
  gvs[same_blocks_def, wordsTheory.w2n_n2w] >>
  metis_tac[]
QED

Theorem append_storage_guard_run:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  emit_void ASSERT [valid] st2 = ((),st3) /\
  eval_operand bop ss = SOME slot /\ fresh_vars_wrt st0 ss /\
  cap < dimword (:256) ==>
  ?ss'.
    state_frame ss' = state_frame ss /\
    eval_operand lop ss' = SOME (if tr then tload slot ss else sload slot ss) /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
    (if w2n (if tr then tload slot ss else sload slot ss) < cap then
       run_inst_seq (emitted_insts st0 st3) ss = OK ss' /\
       same_blocks st0 st3 /\ fresh_vars_wrt st3 ss'
     else
       run_inst_seq (emitted_insts st0 st3) ss =
         Abort Revert_abort (revert_state (set_returndata [] ss')))
Proof
  strip_tac >> drule_all append_storage_check_run >> strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `st2.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 st2` by
    metis_tac[emitted_insts_append, listTheory.APPEND_ASSOC] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `ss'` >> simp[] >>
  Cases_on `w2n (if tr then tload slot ss else sload slot ss) < cap` >>
  gvs[bool_to_word_def]
  >- (`(1w:bytes32) <> 0w` by simp[] >>
      drule_all emit_void_ASSERT_ok_full >> strip_tac >>
      gvs[same_blocks_def]) >>
  drule_all emit_void_ASSERT_revert_full >> simp[]
QED

(* No allocation or copy-loop code is emitted in the primitive branch. *)
Theorem compile_dynarray_append_word_parts:
  compile_dynarray_append cenv bop vop 1 1 dt st cap T
    load_opc store_opc s0 = ((),s9) <=>
  ?lop valid dop off pop nop s1 s2 s3 s4 s5 s6 s7 s8.
    emit_op load_opc [bop] s0 = (lop,s1) /\
    emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
    emit_void ASSERT [valid] s2 = ((),s3) /\
    emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
    emit_op MUL [lop; Lit 1w] s4 = (off,s5) /\
    emit_op ADD [dop; off] s5 = (pop,s6) /\
    emit_void store_opc [pop; vop] s6 = ((),s7) /\
    emit_op ADD [lop; Lit 1w] s7 = (nop,s8) /\
    emit_void store_opc [bop; nop] s8 = ((),s9)
Proof
  eq_tac
  >- (simp[compile_dynarray_append_def, comp_ignore_bind_def, comp_bind_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      metis_tac[pairTheory.PAIR, pairTheory.pair_CASES, oneTheory.one]) >>
  strip_tac >>
  simp[compile_dynarray_append_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def]
QED

Theorem append_storage_store_run:
  emit_void (if tr then TSTORE else SSTORE) [aop; vop] st = ((),st') /\
  eval_operand aop ss = SOME addr /\ eval_operand vop ss = SOME w /\
  fresh_vars_wrt st ss /\ ~ss.vs_call_ctx.cc_static ==>
  run_inst_seq (emitted_insts st st') ss =
    OK (if tr then tstore addr w ss else sstore addr w ss) /\
  same_blocks st st' /\
  fresh_vars_wrt st' (if tr then tstore addr w ss else sstore addr w ss) /\
  (!op x. eval_operand op ss = SOME x ==>
    eval_operand op (if tr then tstore addr w ss else sstore addr w ss) = SOME x)
Proof
  reverse (Cases_on `tr`) >> simp[] >> strip_tac
  >- (drule_all emit_void_SSTORE_correct >> simp[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id TSTORE [aop; vop] []) ss =
    OK (tstore addr w ss)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def] >>
  gvs[run_inst_seq_def] >>
  drule emit_void_extends >> simp[same_blocks_def] >> strip_tac >>
  conj_tac >-
    (irule fresh_vars_wrt_emit_void >> goal_assum drule >>
     gvs[fresh_vars_wrt_def, lookup_var_def, tstore_def, LET_THM]) >>
  rpt gen_tac >> Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, tstore_def, LET_THM]
QED

Theorem append_storage_address_run:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 1w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  eval_operand bop ss = SOME slot /\ eval_operand lop ss = SOME len /\
  fresh_vars_wrt st3 ss ==>
  ?t. run_inst_seq (emitted_insts st3 st6) ss = OK t /\
    eval_operand pop t = SOME (slot + 1w + len) /\
    same_blocks st3 st6 /\ fresh_vars_wrt st6 t /\
    state_frame t = state_frame ss /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `eval_operand (Lit 1w) ss = SOME 1w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st3 st4) ss = OK ss4` >>
  `eval_operand lop ss4 = SOME len /\
   eval_operand (Lit 1w) ss4 = SOME 1w` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all emit_op_MUL_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st4 st5) ss4 = OK ss5` >>
  `eval_operand dop ss5 = SOME (slot + 1w)` by metis_tac[] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends st3 st5` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st3 st5) ss = OK ss5` by
    (irule run_inst_seq_compose_ok >>
     qexistsl_tac [`ss4`, `st4`] >> simp[]) >>
  `run_inst_seq (emitted_insts st3 st6) ss = OK ss'` by
    (irule run_inst_seq_compose_ok >>
     qexistsl_tac [`ss5`, `st5`] >> simp[]) >>
  `state_frame ss' = state_frame ss` by
    (irule append_storage_seq_frame >>
     qexists_tac `emitted_insts st3 st6` >> simp[] >>
     `emitted_insts st3 st6 = emitted_insts st3 st4 ++
       emitted_insts st4 st5 ++ emitted_insts st5 st6` by
       metis_tac[inst_extends_trans, inst_extends_def, emitted_insts_append] >>
     imp_res_tac emitted_insts_emit_op >>
     simp[listTheory.EVERY_APPEND, mk_inst_def]) >>
  gvs[same_blocks_def, wordsTheory.WORD_MULT_CLAUSES] >> metis_tac[]
QED

Theorem append_storage_suffix_run:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 1w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  emit_void (if tr then TSTORE else SSTORE) [pop; vop] st6 = ((),st7) /\
  emit_op ADD [lop; Lit 1w] st7 = (nop,st8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop; nop] st8 = ((),st9) /\
  eval_operand bop ss = SOME slot /\ eval_operand lop ss = SOME len /\
  eval_operand vop ss = SOME w /\ fresh_vars_wrt st3 ss /\
  ~ss.vs_call_ctx.cc_static ==>
  ?t. run_inst_seq (emitted_insts st3 st9) ss = OK t /\
    same_blocks st3 st9 /\ fresh_vars_wrt st9 t /\
    (!op x. eval_operand op ss = SOME x ==> eval_operand op t = SOME x) /\
    state_frame t = state_frame
      (if tr then tstore slot (len+1w) (tstore (slot+1w+len) w ss)
       else sstore slot (len+1w) (sstore (slot+1w+len) w ss))
Proof
  strip_tac >> drule_all append_storage_address_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st3 st6) ss = OK ss6` >>
  `eval_operand vop ss6 = SOME w` by metis_tac[] >>
  `~ss6.vs_call_ctx.cc_static` by
    (qpat_x_assum `state_frame ss6 = state_frame ss`
       (mp_tac o Q.AP_TERM `\x. x.vs_call_ctx`) >>
     simp[state_frame_def]) >>
  drule_all append_storage_store_run >> strip_tac >>
  qmatch_asmsub_abbrev_tac `fresh_vars_wrt st7 ss7` >>
  `eval_operand lop ss7 = SOME len /\
   eval_operand (Lit 1w) ss7 = SOME 1w` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st7 st8) ss7 = OK ss8` >>
  `eval_operand bop ss8 = SOME slot` by metis_tac[] >>
  `state_frame ss8 = state_frame ss7` by
    (irule append_storage_seq_frame >>
     qexists_tac `emitted_insts st7 st8` >> simp[] >>
     imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def]) >>
  `~ss8.vs_call_ctx.cc_static` by
    (qpat_x_assum `state_frame ss8 = state_frame ss7`
       (mp_tac o Q.AP_TERM `\x. x.vs_call_ctx`) >>
     qunabbrev_tac `ss7` >> Cases_on `tr` >>
     simp[state_frame_def, sstore_def, tstore_def, LET_THM]) >>
  drule_all append_storage_store_run >> strip_tac >>
  qmatch_asmsub_abbrev_tac `fresh_vars_wrt st9 ss9` >>
  `state_frame ss7 = state_frame
    (if tr then tstore (slot+1w+len) w ss else sstore (slot+1w+len) w ss)` by
    (qunabbrev_tac `ss7` >> irule append_storage_store_frame >>
     first_assum ACCEPT_TAC) >>
  `state_frame ss9 = state_frame
    (if tr then tstore slot (len+1w)
       (if tr then tstore (slot+1w+len) w ss else sstore (slot+1w+len) w ss)
     else sstore slot (len+1w)
       (if tr then tstore (slot+1w+len) w ss else sstore (slot+1w+len) w ss))` by
    (qunabbrev_tac `ss9` >> irule append_storage_store_frame >> metis_tac[]) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st3 st6` by metis_tac[inst_extends_trans] >>
  `inst_extends st6 st8` by metis_tac[inst_extends_trans] >>
  `inst_extends st6 st9` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st6 st8) ss6 = OK ss8` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`ss7`, `st7`] >> simp[]) >>
  `run_inst_seq (emitted_insts st6 st9) ss6 = OK ss9` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`ss8`, `st8`] >> simp[]) >>
  `run_inst_seq (emitted_insts st3 st9) ss = OK ss9` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`ss6`, `st6`] >> simp[]) >>
  qexists_tac `ss9` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- gvs[same_blocks_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `state_frame ss9 = _` mp_tac >>
  Cases_on `tr` >> pure_rewrite_tac [COND_CLAUSES] >> disch_then ACCEPT_TAC
QED

Theorem compile_dynarray_append_word_run:
  compile_dynarray_append cenv bop vop 1 1 dt st cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) s0 = ((),s9) /\
  eval_operand bop ss = SOME slot /\ eval_operand vop ss = SOME w /\
  fresh_vars_wrt s0 ss /\ cap < dimword (:256) /\
  len = w2n (if tr then tload slot ss else sload slot ss) /\ len < cap /\
  ~ss.vs_call_ctx.cc_static ==>
  ?t. run_inst_seq (emitted_insts s0 s9) ss = OK t /\
    same_blocks s0 s9 /\ fresh_vars_wrt s9 t /\
    (!op x. eval_operand op ss = SOME x ==> eval_operand op t = SOME x) /\
    state_frame t = state_frame
      (if tr then tstore slot (n2w len+1w) (tstore (slot+1w+n2w len) w ss)
       else sstore slot (n2w len+1w) (sstore (slot+1w+n2w len) w ss))
Proof
  pure_rewrite_tac [compile_dynarray_append_word_parts] >> strip_tac >>
  `w2n (if tr then tload slot ss else sload slot ss) < cap` by metis_tac[] >>
  drule_all append_storage_guard_run >> strip_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  asm_rewrite_tac [] >> strip_tac >>
  `eval_operand bop ss' = SOME slot /\ eval_operand vop ss' = SOME w` by
    metis_tac[] >>
  `~ss'.vs_call_ctx.cc_static` by
    (qpat_x_assum `state_frame ss' = state_frame ss`
       (mp_tac o Q.AP_TERM `\x. x.vs_call_ctx`) >>
     simp[state_frame_def]) >>
  drule_all append_storage_suffix_run >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends s0 s3 /\ inst_extends s3 s9` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts s0 s9) ss = OK t` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`ss'`, `s3`] >> simp[]) >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- gvs[same_blocks_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  pure_asm_rewrite_tac [wordsTheory.n2w_w2n] >>
  qpat_x_assum `state_frame t = _` mp_tac >>
  qpat_x_assum `state_frame ss' = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `tr` >> pure_rewrite_tac [COND_CLAUSES] >>
  metis_tac[append_storage_store_frame]
QED

Theorem compile_dynarray_append_word_abort:
  compile_dynarray_append cenv bop vop 1 1 dt st cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) s0 = ((),s9) /\
  eval_operand bop ss = SOME slot /\ fresh_vars_wrt s0 ss /\
  cap < dimword (:256) /\
  cap <= w2n (if tr then tload slot ss else sload slot ss) ==>
  ?g. state_frame g = state_frame ss /\
    (!op x. eval_operand op ss = SOME x ==> eval_operand op g = SOME x) /\
    run_inst_seq (emitted_insts s0 s9) ss =
      Abort Revert_abort (revert_state (set_returndata [] g))
Proof
  pure_rewrite_tac [compile_dynarray_append_word_parts] >> strip_tac >>
  `~(w2n (if tr then tload slot ss else sload slot ss) < cap)` by decide_tac >>
  drule_all append_storage_guard_run >> strip_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  asm_rewrite_tac [] >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends s0 s3 /\ inst_extends s3 s9` by metis_tac[inst_extends_trans] >>
  qexists_tac `ss'` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule run_inst_seq_abort_extends >> qexists_tac `s3` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >> first_assum ACCEPT_TAC
QED
