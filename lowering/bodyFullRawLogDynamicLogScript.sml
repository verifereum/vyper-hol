(* RawLog LOG endpoint, uniform in the storage horizon and fixed-region base. *)
Theory bodyFullRawLogDynamicLog
Ancestors
  bodySimFull rawLogPtrInst exprLoweringProps instMemFrontier
  vyperEvent vyperStorageFootprint venomMemDefs
  words list rich_list finite_map pred_set loweringStateRelDefs venomExecSemantics venomInst
  arithmetic valueEncodingDefs memSafeRun bodyPtrDefs ptrSafeRun ptrDiscipline
  memLocDefs compileEnv vyperStorage vyperState venomState
  sourceLogFrames vyperStorageBackend

Theorem raw_log_dynamic_log_joint:
  LENGTH ops < dimword (:256) /\
  eval_operands ops t = SOME (MAP event_value_to_word vals) /\
  eval_operand ptr_op t = SOME (n2w p) /\
  eval_operand len_op t = SOME (n2w (LENGTH bs)) /\
  p < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  EVERY (\op. op_taint tn op = {}) (ptr_op::len_op::ops) /\
  (LENGTH bs <> 0 ==> ?x. ptr_op = Var x /\ ptr_covers G tn x t (LENGTH bs)) /\
  p + LENGTH bs <= t.vs_alloca_next /\
  (!j. p <= j /\ j < p + LENGTH bs ==> j NOTIN tn.t_mem) /\
  mem_bytes_at p (LENGTH bs) t.vs_memory = bs /\
  stmt_state_rel H ctx func cenv cx ee t /\
  storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at D lo d cenv cx ee G tn t /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst id LOG
    (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [];
      ee' = ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs];
      u = t with vs_logs := t.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs]
  in
    step_inst_base i t = OK u /\
    inst_mem_below_frontier i t /\ inst_dload_in_section i t /\
    ptr_inst_ok D lo 0 ctx func G tn i t /\
    step_prov PG G i u = G /\ step_taint i t u tn = tn /\
    (u with vs_logs := t.vs_logs) = t /\
    stmt_state_rel H ctx func cenv cx ee' u /\
    storage_well_formed_on cx ee' (FST H) /\
    ghost_inv_at D lo d cenv cx ee' G tn u
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  `~t.vs_call_ctx.cc_static /\ t.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `step_inst_base (mk_inst id LOG
     (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) []) t =
     OK (t with vs_logs := t.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs])` by
    (simp[step_inst_base_def, mk_inst_def, REVERSE_APPEND,
          w2n_n2w, LESS_MOD, GSYM mem_bytes_at_def,
          encode_raw_event_values_def, encode_raw_event_def]) >>
  rpt conj_tac
  >- simp[]
  >- (simp[below_frontier_LOG] >> rpt strip_tac >> gvs[w2n_n2w, LESS_MOD])
  >- simp[inst_dload_in_section_def, mk_inst_def]
  >- (`access_ok 0 G func (mk_inst id LOG
         (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) []) t` by
        (irule log_access_ok >> simp[w2n_n2w, LESS_MOD] >>
         rpt strip_tac >> gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
      `access_ok lo G func (mk_inst id LOG
         (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) []) t` by
        (fs[access_ok_def] >> metis_tac[LESS_EQ_TRANS, DECIDE ``0 <= n:num``]) >>
      `taint_ok func tn (mk_inst id LOG
         (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) []) t` by
        (irule log_taint_ok >> simp[w2n_n2w, LESS_MOD] >> gvs[]) >>
      fs[ptr_inst_ok_def, ghost_inv_at_def, stor_taint_ok_at_def,
         mk_inst_def, step_inst_non_invoke])
  >- simp[log_ghost]
  >- simp[log_ghost]
  >- simp[]
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
      simp[stmt_state_rel_def, state_rel_def, immutable_base_zero_alt,
           logs_rel_eq, local_ptrs_rel_def, local_region_def, local_backed_def,
           storage_rel_def, transient_rel_def, accounts_rel_def,
           immutables_rel_def, immutable_alloca_sep_def, alloca_room_def,
           fmp_room_def, pending_alloca_size_def, alloca_inv_def,
           lookup_var_def, contract_storage_def, contract_transient_def,
           allocas_non_overlapping_def, alloca_next_valid_def] >>
      strip_tac >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC)
  >- (fs[storage_well_formed_on_def] >> rpt strip_tac >>
      Cases_on `b` >> fs[get_storage_def] >> metis_tac[get_storage_def])
  >> (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[ghost_inv_at_def, ptr_covers_def, return_buf_ptr_def,
           stor_taint_ok_at_def, lookup_var_def, allocas_from_def] >>
      Cases_on `d`
      >- (simp[return_buf_ptr_def] >> strip_tac >>
          rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
      PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def] >>
      strip_tac >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC)
QED
