Theory ctorReturnFrame
Ancestors
  bodySim stmtSimReturn immutableDeployExecution nonreentrantSource loweringHalt
  moduleLowering stmtLowering stmtSimDefs stmtSimProps exprLoweringProps fragExec compileEnv
  vyperInterpreter vyperState vyperContext vyperStorageLayoutSafety
  venomExecSemantics venomState venomInst

(* The epilogue returns bytes from a related snapshot after releasing the
   constructor lock. The snapshot is not an execution-success assumption. *)
Definition constructor_return_q_def:
  constructor_return_q func cenv cx runtime_size immutables_len nr nkey
    v (es:evaluation_state) r <=>
    v = NoneV /\
    ?before final codepos.
      r = Halt final /\ final.vs_halted /\
      state_rel func cenv cx
        (if nr then
           es with tStorage :=
             (cx.txn.target =+
               update_storage (n2w nkey) 0w (es.tStorage cx.txn.target))
               es.tStorage
         else es) before /\
      FLOOKUP before.vs_labels "runtime_begin" = SOME codepos /\
      final.vs_returndata =
        TAKE runtime_size
          (DROP (w2n codepos) before.vs_code ++ REPLICATE runtime_size 0w) ++
        TAKE immutables_len
          (before.vs_memory ++ REPLICATE immutables_len 0w) /\
      final.vs_accounts = before.vs_accounts /\
      final.vs_transient = before.vs_transient /\
      final.vs_logs = before.vs_logs /\
      final.vs_outcomes = before.vs_outcomes /\
      final.vs_requests = before.vs_requests /\
      final.vs_pending_deletions = before.vs_pending_deletions /\
      final.vs_call_ctx = before.vs_call_ctx /\
      final.vs_tx_ctx = before.vs_tx_ctx /\
      final.vs_block_ctx = before.vs_block_ctx /\
      final.vs_data_section = before.vs_data_section /\
      final.vs_immutables = before.vs_immutables /\
      final.vs_code = before.vs_code /\ final.vs_labels = before.vs_labels
End

Theorem constructor_unlock_stmt_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey ==>
  stmt_state_rel ctx func cenv cx
    (es with tStorage := (cx.txn.target =+
      update_storage (n2w nkey) 0w (es.tStorage cx.txn.target)) es.tStorage)
    (tstore (n2w nkey) 0w s)
Proof
  strip_tac >> irule stmt_state_rel_allocas_frame >> conj_tac
  >- (irule immutable_base_zero_frame >>
      qexists `s` >> gvs[stmt_state_rel_def, tstore_def, lookup_var_def]) >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >>
      simp[tstore_def, local_region_def, lookup_var_def] >>
      qexistsl [`s`, `es`] >> gvs[stmt_state_rel_def] >> metis_tac[]) >>
  conj_tac
  >- (irule nonreentrant_state_rel_write >> gvs[stmt_state_rel_def]) >>
  qexistsl [`es`, `s`] >> simp[tstore_def]
QED

Theorem constructor_exit_state_rel:
  same_frame cenv cenv' /\ state_rel func cenv' cx es s ==>
  state_rel func cenv cx (es with scopes := []) s
Proof
  strip_tac >> dxrule state_rel_scopes_nil >> strip_tac >>
  gvs[same_frame_def, compile_env_component_equality, state_rel_def,
      local_ptrs_rel_def, local_region_def, lookup_scopes_def,
      storage_vars_rel_def, transient_vars_rel_def, logs_rel_def,
      log_entry_equiv_def, listTheory.LIST_REL_EL_EQN, immutables_rel_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!name tv v byte_offset. _` (drule_all_then strip_assume_tac) >>
  simp[]
QED

Theorem constructor_exit_code[local]:
  (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
    st_exit = ((), st_epilogue) /\
  (nr ==> ut) /\ st_exit.cs_current_insts = [] /\
  compile_constructor_epilogue rt cap imm st_epilogue = ((), st_final) /\
  fn_has_code st_exit st_final func ==>
  fn_has_code st_exit st_epilogue func /\
  fn_has_code st_epilogue st_final func /\
  ~block_is_terminated st_epilogue
Proof
  strip_tac >> drule optional_unlock_code >> simp[] >> strip_tac >>
  `~block_is_terminated st_epilogue` by
    (gvs[block_is_terminated_def] >> Cases_on `nr` >>
     gvs[block_is_terminated_def, mk_inst_def, is_terminator_def]) >>
  `cs_extends st_exit st_epilogue` by
    (irule cs_extends_same_block >> Cases_on `nr` >> gvs[]) >>
  `cs_extends st_epilogue st_final` by
    (irule cs_extends_same_block >>
     drule_all compile_constructor_epilogue_append >> strip_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >>
     qpat_x_assum `compile_constructor_epilogue _ _ _ _ = _` mp_tac >>
     Cases_on `cap > 0` >>
     simp[compile_constructor_epilogue_def, contextTheory.compile_alloc_buffer_def,
          emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
          emitHelperTheory.emit_inst_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[]) >>
  drule_all fn_has_code_split >> gvs[]
QED

Theorem constructor_exit_run:
  cenv.ce_is_ctor /\ same_frame cenv body_cenv /\
  st_exit.cs_current_insts = [] /\
  (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
    st_exit = ((), st_epilogue) /\
  compile_constructor_epilogue rt cap imm st_epilogue = ((), st_final) /\
  fn_has_code st_exit st_final func /\ fn_inst_ids_distinct func /\
  rt + cap < dimword(:256) /\
  (nr ==> ut /\ storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey) /\
  (cap <> 0 ==> cenv.ce_imm_alloca = SOME imm /\
    (!x. imm = Var x ==> not_fresh_at st_epilogue x)) /\
  stmt_state_rel ctx func body_cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = st_exit.cs_current_bb /\ s.vs_inst_idx = 0 ==>
  ?fuel final. run_from fuel ctx func s = Halt final /\
    constructor_return_q func cenv cx rt cap nr nkey NoneV
      (es with scopes := []) (Halt final)
Proof
  strip_tac >>
  `nr ==> ut` by simp[] >>
  drule_all constructor_exit_code >> strip_tac >>
  qmatch_goalsub_abbrev_tac `constructor_return_q _ _ _ _ _ _ _ _ es0 _` >>
  qabbrev_tac `es1 = if nr then
    es with tStorage := (cx.txn.target =+
      update_storage (n2w nkey) 0w (es.tStorage cx.txn.target)) es.tStorage
    else es` >>
  qabbrev_tac `s1 = (if nr then tstore (n2w nkey) 0w s else s) with
    vs_inst_idx := LENGTH st_epilogue.cs_current_insts` >>
  `stmt_state_rel ctx func body_cenv cx es1 s1` by
    (simp[Abbr `s1`, stmt_state_rel_inst_idx] >>
     Cases_on `nr` >> gvs[Abbr `es1`] >>
     irule constructor_unlock_stmt_state_rel >> simp[]) >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule optional_unlock_frag >>
  disch_then (qspecl_then [`ctx`, `\s0. s0 = s`, `\s2. s2 = s1`, `\r. F`] mp_tac) >>
  simp[Abbr `s1`] >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func body_cenv cx es1 s1` >>
  `body_cenv.ce_is_ctor /\
   (cap <> 0 ==> body_cenv.ce_imm_alloca = SOME imm /\
      (!x. imm = Var x ==> not_fresh_at st_epilogue x))` by
    gvs[same_frame_def, compile_env_component_equality] >>
  `~s1.vs_halted /\ s1.vs_current_bb = st_epilogue.cs_current_bb /\
   s1.vs_inst_idx = LENGTH st_epilogue.cs_current_insts` by
    simp[Abbr `s1`] >>
  drule_all compile_constructor_epilogue_padded_run_from >> strip_tac >>
  qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  goal_assum (drule_at Any) >>
  `state_rel func cenv cx (es1 with scopes := []) s1` by
    (irule constructor_exit_state_rel >> qexists `body_cenv` >>
     gvs[stmt_state_rel_def]) >>
  ` (if nr then es0 with tStorage := (cx.txn.target =+
       update_storage (n2w nkey) 0w (es0.tStorage cx.txn.target)) es0.tStorage
     else es0) = es1 with scopes := []` by
    (Cases_on `nr` >> simp[Abbr `es0`, Abbr `es1`]) >>
  simp[constructor_return_q_def] >>
  qexistsl [`s1`, `codepos`] >> simp[]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then
       print ("CTOR_RETURN_KERNEL_CLOSED " ^ name ^ "\n")
     else raise Fail ("Unclosed constructor Return theorem: " ^ name)
  end) (DB.thms "ctorReturnFrame");
