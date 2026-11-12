(* Same-witness memory framing for the Send CALL/ASSERT tail. *)
Theory bodyIntCallFamCallExtSendFrame
Ancestors
  exprSimSend exprSendPtr fragGasSeqAbort fragGasMode fragGasPath
  venomState venomExecSemantics venomInst compileEnv exprLoweringProps
  loweringPosts fragExec
Libs
  monadsyntax

Theorem call_assert_counted_ok:
  ~s.vs_halted /\ ~t.vs_halted /\
  s.vs_current_bb = t.vs_current_bb /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = CALL /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst aid ASSERT [Var out] []) /\
  step_inst_base inst s = OK (update_var out w t) /\ w <> 0w ==>
  gas_marked_path F ctx func s 0
    (OK ((update_var out w t) with vs_inst_idx := SUC (SUC s.vs_inst_idx)))
Proof
  strip_tac >>
  `0 = (if inst.inst_opcode = GAS then 1 else 0) + 0` by simp[] >>
  pop_assum SUBST1_TAC >> irule gas_marked_path_step >>
  simp[is_terminator_def] >>
  `0 = (if (mk_inst aid ASSERT [Var out] []).inst_opcode = GAS
        then 1 else 0) + 0` by simp[mk_inst_def] >>
  pop_assum SUBST1_TAC >> irule gas_marked_path_step >>
  simp[mk_inst_def, is_terminator_def, update_var_def] >>
  (conj_tac >- metis_tac[mk_inst_def]) >>
  qexists `(update_var out w t) with vs_inst_idx := SUC s.vs_inst_idx` >>
  conj_tac
  >- (simp[update_var_def] >>
      irule (SRULE [mk_inst_def] assert_true_correct) >>
      simp[eval_operand_def, lookup_var_def, update_var_def,
           finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[gas_marked_path_def, update_var_def] >>
  irule (cj 1 gas_path_rules) >> simp[]
QED

Theorem call_assert_counted_fail:
  ~s.vs_halted /\ ~t.vs_halted /\
  s.vs_current_bb = t.vs_current_bb /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = CALL /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst aid ASSERT [Var out] []) /\
  step_inst_base inst s = OK (update_var out 0w t) ==>
  gas_marked_path F ctx func s 0
    (Abort Revert_abort (revert_state (set_returndata []
      ((update_var out 0w t) with vs_inst_idx := SUC s.vs_inst_idx))))
Proof
  strip_tac >>
  `0 = (if inst.inst_opcode = GAS then 1 else 0) + 0` by simp[] >>
  pop_assum SUBST1_TAC >> irule gas_marked_path_step >>
  simp[is_terminator_def] >>
  `0 = (if (mk_inst aid ASSERT [Var out] []).inst_opcode = GAS
        then 1 else 0)` by simp[mk_inst_def] >>
  pop_assum SUBST1_TAC >> irule gas_marked_path_abort >>
  simp[mk_inst_def, is_terminator_def, update_var_def] >>
  conj_tac
  >- (qspecl_then [`aid`, `out`, `t with vs_inst_idx := SUC s.vs_inst_idx`]
        mp_tac send_assert_fail >> simp[mk_inst_def, update_var_def]) >>
  metis_tac[mk_inst_def]
QED

Theorem send_tail_framed_path:
  emit_op CALL [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
    sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (void, sb) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\
  stmt_state_rel ctx func cenv cx es1 s /\ wb_frame cenv es sa s0 s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  outcomes_accounts_typed es1.outcomes /\
  accounts_runtime_well_typed es1.accounts /\
  IS_SOME (eval_operand gas_op s) /\
  eval_operand addr_op s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand val_op s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs);
      read_result cx tv od) es1 = (res, es') /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT ==>
  ?r. gas_marked_path F ctx func s 0 r /\
    ((?u. r = OK u /\ res = INL NoneV /\
          expr_post ctx func cenv cx e es sa sb s0 es' NoneV (Lit 0w) u /\
          u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts /\
          u.vs_memory = s.vs_memory) \/
     (exit_result r /\ expr_exit res r))
Proof
  strip_tac >> drule_all call_assert_code_lookup >> strip_tac >>
  drule_all send_tail_shape >> strip_tac >>
  `~not_fresh_at sm out` by gvs[not_fresh_at_def] >>
  `es'.scopes = es1.scopes /\ es'.immutables = es1.immutables` by
    (drule eval_send_read >> strip_tac >>
     drule vyperInterpreterTheory.eval_send_preserves_non_accounts >> simp[]) >>
  drule_all send_call_read_step >>
  disch_then (qspecl_then [`out`, `sm.cs_next_id`] strip_assume_tac)
  >- suspend "normal"
  >> suspend "failed"
QED

Resume send_tail_framed_path[normal]:
  `~t'.vs_halted /\ s.vs_current_bb = t'.vs_current_bb /\
   t'.vs_memory = s.vs_memory` by
    (qpat_x_assum `t' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qexists `OK ((update_var out 1w t') with
                 vs_inst_idx := SUC (SUC s.vs_inst_idx))` >>
  conj_tac
  >- (irule call_assert_counted_ok >> simp[] >>
      gvs[mk_inst_def]) >>
  disj1_tac >> simp[] >> conj_tac
  >- (irule send_tail_none_post >> simp[] >>
      conj_tac >- (qexists `sm` >> simp[]) >>
      qexistsl [`es1`, `s`] >> gvs[venom_state_component_equality]) >>
  gvs[update_var_def, arithmeticTheory.ADD1]
QED

Resume send_tail_framed_path[failed]:
  `~t'.vs_halted /\ s.vs_current_bb = t'.vs_current_bb` by
    (qpat_x_assum `t' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qexists `Abort Revert_abort (revert_state (set_returndata []
      ((update_var out 0w t') with vs_inst_idx := SUC s.vs_inst_idx)))` >>
  conj_tac
  >- (irule call_assert_counted_fail >> simp[] >> gvs[mk_inst_def]) >>
  simp[exit_result_def, exprSimDefsTheory.expr_exit_def]
QED

Finalise send_tail_framed_path
