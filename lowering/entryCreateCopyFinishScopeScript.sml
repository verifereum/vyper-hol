(* CopyOf after the last scalar. Both branches use the witnesses of the
   preparation proof; in particular the empty branch never runs dispatch. *)
Theory entryCreateCopyFinishScope
Ancestors
  entryCreateDispatchScope entryCreateAdminSequence entryIntCallStageNeutral
  entryCreatePathScope entryCreateCompletedCut entryCreateFocusSpec
  exprSimFullBundleProps exprSimDefs exprLoweringProps loweringShapeDefs
  createSizePrefixReplay createMarkedPath fragGasOriginPtr fragGasOrigin
  createSizeCutCode createSizeCutRegion fragExec
  vyperCreate vyperInterpreter vyperState vyperTypeInvariants
  vyperStorageTrace vyperStorageFootprint gasSummary
  compileEnv venomState venomInst venomExecSemantics vfmConstants words relation list

Theorem copy_empty_scoped[local]:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. source (ee with gas_obs := tail) =
    (INR (Error (RuntimeError "create source has no deployable code")),
      ee with gas_obs := tail)) /\
  create_prefix_step sm sb E ctx func s [] u /\
  (u.vs_current_bb <> sb.cs_current_bb \/ u.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  gas_origin_edge T E ctx func u [] (Abort Revert_abort z) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s,G,tn) []
       (Abort Revert_abort z,Gh,th)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sm sb
    source (ee,s,G,tn) Q
    (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  strip_tac >>
  `create_expr_prefix sm sb E ctx func s [] u` by
    (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
     simp[create_marked_edge_def]) >>
  `create_operand_full_scope sm sb E ctx func s [] (Abort Revert_abort z)` by
    (irule (SIMP_RULE (srw_ss()) [exit_result_def]
      (Q.INST [`left` |-> `[]`, `last` |-> `[]`] create_operand_full_scope_terminal)) >>
     simp[exit_result_def] >> qexists_tac `u` >> simp[]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "create source has no deployable code"))`,
    `ee`,`Abort Revert_abort z`,`Gh`,`th`] >>
  simp[exit_result_def,create_operand_exit_post_def,expr_exit_def,halt_exit_def]
QED

Theorem copy_prepared_size_bound[local]:
  accounts_well_typed accounts ==>
  ~(w2n (n2w (LENGTH (lookup_account (word_of_bytes_be bs) accounts).code + 11)
      :bytes32) > 2 * max_code_size)
Proof
  strip_tac >>
  `LENGTH (lookup_account (word_of_bytes_be bs) accounts).code <= 24576` by
    fs[accounts_well_typed_def, account_well_typed_def] >>
  qspec_then `LENGTH (lookup_account (word_of_bytes_be bs) accounts).code + 11` mp_tac
    (INST_TYPE [``:'a`` |-> ``:256``] word_n2w_le2) >>
  fs[max_code_size_def] >> decide_tac
QED

(* The closed dispatch sequent is a law parameter, not a premise that the
   supplied prefix reached or executed CREATE. Quote its checked statement
   rather than keeping a second copy of the shared dispatch interface. *)
Theorem copy_finish_scoped_from_prepare:
  ^(concl (GEN_ALL create_dispatch_scoped_outcome)) /\
  body_inv (cx_tops cx) ctx cenv cx /\ MEM func ctx.ctx_functions /\
  storage_trace_domain cx st0 ee.storage_trace /\ storage_trace_frame source /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  fn_inst_ids_distinct func /\
  (!b. MEM b func.fn_blocks ==> phi_prefix_length b.bb_instructions = 0) /\
  ~s.vs_halted /\ create_operand_at sm s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  accounts_well_typed ee.accounts /\ outcomes_accounts_typed ee.outcomes /\
  code = (lookup_account (word_of_bytes_be bs) ee.accounts).code /\
  post_value_type cenv e = BaseT AddressT /\ expr_has_effect e /\
  (!tail. source (ee with gas_obs := tail) =
    if code = [] then (INR (Error (RuntimeError "create source has no deployable code")),
                        ee with gas_obs := tail)
    else bind (ignore_bind (check_not_static cx)
      (create_oracle_result sw (w2n aw) (create_copy_initcode code) rof))
      (read_result cx) (ee with gas_obs := tail)) /\
  (if code = [] then
    ?p u Gh th.
      create_prefix_step sm sb E ctx func s [] u /\
      (u.vs_current_bb <> sb.cs_current_bb \/ u.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
      gas_origin_edge T E ctx func u [] (Abort Revert_abort
        (revert_state (set_returndata []
          (update_var p 0w s with vs_inst_idx := SUC s.vs_inst_idx)))) /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (Abort Revert_abort (revert_state (set_returndata []
          (update_var p 0w s with vs_inst_idx := SUC s.vs_inst_idx))),Gh,th))
   else
    ?sc buf len p t Gmat tt pv sz base.
      compile_create_dispatch buf len amount sop rof sc = (result,sb) /\
      fn_has_code sc sb func /\ fn_has_code sm sc func /\
      sm.cs_next_var <= sc.cs_next_var /\
      sm.cs_next_id <= sc.cs_next_id /\ sc.cs_next_id <= sb.cs_next_id /\
      (!bb inst. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
         get_instruction bb (LENGTH sb.cs_current_insts) = SOME inst ==>
         inst.inst_id NOTIN frag_ids sm sc) /\
      create_cut_code {} sc sb /\ create_cut_region sc sb t /\
      (t.vs_current_bb <> sb.cs_current_bb \/ t.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
      sc.cs_current_bb = sm.cs_current_bb /\
      sc.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sc /\
      EVERY (\i. i.inst_id IN frag_ids sm sc /\ i.inst_opcode <> INVOKE /\
                 i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) (emitted_insts sm sc) /\
      run_inst_seq (emitted_insts sm sc) s = OK base /\
      t = (base with vs_inst_idx := LENGTH sc.cs_current_insts) /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gmat,tt)) /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      alloca_history func t /\ allocas_below_fmp t /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx ee Gmat tt t) /\
      wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt /\
      buf = Var p /\ eval_operand buf t = SOME pv /\ eval_operand len t = SOME sz /\
      sz = n2w (LENGTH code + 11) /\ ptr_covers Gmat tt p t (w2n sz) /\
      ctx_has_dalloca ctx /\ w2n t.vs_initial_fmp <= w2n pv /\ w2n pv + w2n sz <= w2n t.vs_fmp /\
      read_memory (w2n pv) (w2n sz) t = create_copy_initcode code /\
      (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tt.t_mem) /\
      op_taint tt buf = {} /\ op_taint tt len = {} /\
      eval_operand amount t = SOME aw /\ op_taint tt amount = {} /\
      (case sop of NONE => sw = NONE | SOME op =>
        ?w. sw = SOME w /\ eval_operand op t = SOME w /\ op_taint tt op = {})) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sm sb
    source (ee,s,G,tn)
    (\H res ee' G' tn' t. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sb s0 ee' v result t /\
      expr_store_bound cx (BaseT AddressT) v result t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee' G' tn' t /\
      ptr_val_ok cx (BaseT AddressT) v result G' tn' t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "dispatch")
    (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `code = []`
  >- (qpat_x_assum `if code = [] then _ else _` mp_tac >> asm_rewrite_tac[] >>
      disch_then (qx_choose_then `p` (qx_choose_then `u`
        (qx_choose_then `Gh` (qx_choose_then `th` strip_assume_tac)))) >>
      irule copy_empty_scoped >> simp[] >>
      qexistsl_tac [`Gh`,`th`,`u`,`revert_state (set_returndata []
        (update_var p 0w s with vs_inst_idx := SUC s.vs_inst_idx))`] >> simp[])
  >> qpat_x_assum `if code = [] then _ else _` mp_tac >> asm_rewrite_tac[] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `create_operand_full_scope sm sc E ctx func s [] (OK t)` by
    (qpat_assum `t = (_ with vs_inst_idx := _)` SUBST1_TAC >>
     irule create_admin_sequence_scope >> simp[]) >>
  `~(w2n sz > 2 * max_code_size)` by
    (qpat_assum `sz = n2w _` SUBST1_TAC >> irule copy_prepared_size_bound >>
     first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `(!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sc x) /\
   (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sc x)` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> simp[]) >>
  irule stage_scoped_zero_prefix >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  rpt (conj_tac >- (simp[] >> NO_TAC)) >>
  qexistsl_tac [`tt`,`t`,`sc`,`Gmat`] >>
  rpt (conj_tac >- (simp[] >> NO_TAC)) >>
  asm "dispatch" irule >>
  qpat_assum `compile_create_dispatch _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operand buf t = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand len t = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand amount t = SOME _` (irule_at Any) >>
  qexistsl_tac [`sw`,`create_copy_initcode code`] >>
  simp[] >> qpat_x_assum `ptr_covers Gmat tt p t (w2n sz)` mp_tac >> simp[]
QED
