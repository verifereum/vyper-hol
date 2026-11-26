(* Close the copy preparation at its actual revert or dispatch landing. *)
Theory bodyCreateCopyFinishMods
Ancestors
  bodyFullPostsMods gasOutcomeFullPostMods gasOutcomeFullZeroPrefixMods
  builtinCreate vfmConstants vyperTypeInvariants vyperCreate vyperState
  vyperStorageFootprint loweringPosts loweringShapeDefs exprLoweringProps
  exprSimDefs bodyPtrDefs bodyFullShadowBodyInv fragExec compileEnv words
  venomState venomInst venomMemDefs ptrDiscipline allocaHistory

val copy_post = ``\(H:(bool # 256 word # type_value) list # num list) (res:value + exception) ee' G' tn' t. ?v. res = INL v /\
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee' v result t /\
  expr_store_bound cx (BaseT AddressT) v result t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee' G' tn' t /\
  ptr_val_ok cx (BaseT AddressT) v result G' tn' t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'``;
val copy_exit = ``\(H:(bool # 256 word # type_value) list # num list) (res:value + exception) ee' (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee' res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem create_copy_finish_mods:
  ~s.vs_halted /\ fn_inst_ids_distinct func /\
  storage_trace_domain cx st0 ee.storage_trace /\
  accounts_well_typed ee.accounts /\ outcomes_accounts_typed ee.outcomes /\
  code = (lookup_account (word_of_bytes_be bs) ee.accounts).code /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  post_value_type cenv e = BaseT AddressT /\ expr_has_effect e /\
  (!tail. source (ee with gas_obs := tail) =
    if code = [] then (INR (Error (RuntimeError "create source has no deployable code")),
                        ee with gas_obs := tail)
    else bind (ignore_bind (check_not_static cx)
      (create_oracle_result sw (w2n aw) (create_copy_initcode code) rof))
      (read_result cx) (ee with gas_obs := tail)) /\
  (if code = [] then
    ?p Gh th. !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort (revert_state (set_returndata []
        (update_var p 0w s with vs_inst_idx := SUC s.vs_inst_idx))),Gh,th)
   else
    ?sc buf len p t Gmat tt pv sz.
      compile_create_dispatch buf len amount sop rof sc = (result,sb) /\
      fn_has_code sc sb func /\ cs_extends sm sc /\ sm.cs_next_var <= sc.cs_next_var /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gmat,tt)) /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      alloca_history func t /\ allocas_below_fmp t /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
        storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gmat tt t) /\
      wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt /\
      return_buf_frame d cenv sm t /\
      buf = Var p /\ eval_operand buf t = SOME pv /\ eval_operand len t = SOME sz /\
      sz = n2w (LENGTH code + 11) /\ ptr_covers Gmat tt p t (w2n sz) /\
      ctx_has_dalloca ctx /\ w2n t.vs_initial_fmp <= w2n pv /\ w2n pv + w2n sz <= w2n t.vs_fmp /\
      read_memory (w2n pv) (w2n sz) t = create_copy_initcode code /\
      (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tt.t_mem) /\
      op_taint tt buf = {} /\ op_taint tt len = {} /\
      eval_operand amount t = SOME aw /\ op_taint tt amount = {} /\
      (case sop of NONE => sw = NONE | SOME op =>
        ?w. sw = SOME w /\ eval_operand op t = SOME w /\ op_taint tt op = {})) /\
  (!sc buf len t Gmat tt pv sz.
      compile_create_dispatch buf len amount sop rof sc = (result,sb) /\
      fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sc /\ sa.cs_next_var <= sc.cs_next_var /\
      (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sc x) /\
      (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sc x) /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ storage_trace_domain cx st0 ee.storage_trace /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
        storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gmat tt t) /\
      wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt /\
      outcomes_accounts_typed ee.outcomes /\
      eval_operand buf t = SOME pv /\ eval_operand len t = SOME sz /\
      (sz <> 0w ==> ?p. buf = Var p /\ ptr_covers Gmat tt p t (w2n sz)) /\
      (sz <> 0w ==> w2n pv + w2n sz <= t.vs_alloca_next \/
        (ctx_has_dalloca ctx /\ w2n t.vs_initial_fmp <= w2n pv /\ w2n pv + w2n sz <= w2n t.vs_fmp)) /\
      read_memory (w2n pv) (w2n sz) t = create_copy_initcode code /\
      (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tt.t_mem) /\
      op_taint tt buf = {} /\ op_taint tt len = {} /\
      eval_operand amount t = SOME aw /\ op_taint tt amount = {} /\
      (case sop of NONE => sw = NONE | SOME op =>
        ?w. sw = SOME w /\ eval_operand op t = SOME w /\ op_taint tt op = {}) /\
      post_value_type cenv e = BaseT AddressT /\ expr_has_effect e /\
      (!tail. source (ee with gas_obs := tail) =
        if w2n sz > 2 * max_code_size then
          (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
        else bind (ignore_bind (check_not_static cx)
          (create_oracle_result sw (w2n aw) (create_copy_initcode code) rof))
          (read_result cx) (ee with gas_obs := tail)) ==>
      gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
        source (ee,t,Gmat,tt) ^copy_post ^copy_exit) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    source (ee,s,G,tn) ^copy_post ^copy_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH code <= 24576` by fs[accounts_well_typed_def,account_well_typed_def] >>
  qpat_x_assum `code = _` kall_tac >>
  Cases_on `code = []` >>
  qpat_x_assum `if code = [] then _ else _` mp_tac >> asm_rewrite_tac[]
  >- (disch_then (qx_choosel_then [`p`,`Gh`,`th`] assume_tac) >>
      irule gas_outcome_full_mods_exit_revert >> BETA_TAC >>
      (reverse conj_tac >- first_assum ACCEPT_TAC) >>
      qexistsl_tac [`Gh`,`ee`,`INR (Error (RuntimeError "create source has no deployable code"))`,`th`,
        `revert_state (set_returndata [] (update_var p 0w s with vs_inst_idx := SUC s.vs_inst_idx))`] >>
      simp[exit_result_def,expr_exit_def,halt_exit_def]) >>
  disch_then (qx_choosel_then [`sc`,`buf`,`len`,`p`,`t`,`Gmat`,`tt`,`pv`,`sz`]
    (map_every assume_tac o CONJUNCTS)) >>
  irule gas_outcome_full_mods_zero_prefix >>
  (qexistsl_tac [`Gmat`,`t`,`tt`] >> conj_tac >- simp[]) >>
  `~(w2n sz > 2 * max_code_size)` by
    (qpat_assum `sz = _` SUBST1_TAC >>
     qspec_then `LENGTH code + 11` mp_tac (INST_TYPE [alpha |-> ``:256``] word_n2w_le2) >>
     pure_rewrite_tac[max_code_size_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sc` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  qpat_assum `!sc buf len t Gmat tt pv sz. _ ==> _` irule >>
  qpat_assum `compile_create_dispatch _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operand buf t = SOME pv` (irule_at Any) >>
  qpat_assum `eval_operand len t = SOME sz` (irule_at Any) >>
  simp[] >> conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ t /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  disch_tac >> qpat_assum `ptr_covers Gmat tt p t (w2n sz)` mp_tac >>
  qpat_assum `sz = _` (fn th => pure_rewrite_tac[th,w2n_n2w]) >>
  simp_tac bool_ss []
QED
