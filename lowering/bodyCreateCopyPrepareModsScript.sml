(* The prepared linked copy buffer is chosen before the horizon. *)
Theory bodyCreateCopyPrepareMods
Ancestors
  bodyCreateCopyEmitCutsMods bodyCreateCopyCutBoundMods
  bodyCreateCopyAllocatedCutMods bodyCreateCopyWrittenFootprintMods
  bodyCreateCopyMaterializedFrameMods
  bodyFullIfExpReach[qualified] bodyFullHashKeccakFixed[qualified]
  bodyBinopFragMemory[qualified] stateRelProj[qualified] accountsRelProps[qualified]
  exprSimSliceExtcode[qualified]
  bodyFullPostsMods bodyFullShadowBodyInv builtinCreate vyperCreate
  vyperStorageFootprint exprLoweringProps fragExec loweringShapeDefs
  venomState venomExecSemantics ptrDiscipline finite_map rich_list list words

Theorem copy_prepared_history[local]:
  fn_has_code sm sc func /\
  s.vs_current_bb = sc.cs_current_bb /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_allocas = s.vs_allocas /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  t.vs_inst_idx = LENGTH sc.cs_current_insts /\
  sc.cs_current_insts = sm.cs_current_insts ++ is /\
  EVERY (\i. i.inst_opcode <> ALLOCA) is /\ alloca_history func s ==>
  alloca_history func t
Proof
  strip_tac >>
  qpat_assum `fn_has_code sm sc func`
    (strip_assume_tac o REWRITE_RULE[fn_has_code_def,IS_PREFIX_APPEND]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `DROP s.vs_inst_idx bb.bb_instructions = is ++ l` by
    (map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
       [`s.vs_inst_idx = _`,`bb.bb_instructions = _`,`sc.cs_current_insts = _`] >>
     PURE_REWRITE_TAC[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >> REFL_TAC) >>
  `t.vs_inst_idx = s.vs_inst_idx + LENGTH is` by simp[] >>
  drule_all_then mp_tac bodyBinopFragMemoryTheory.alloca_history_no_alloca_slice >>
  qpat_assum `t.vs_inst_idx = s.vs_inst_idx + LENGTH is`
    (fn th => simp[NoAsms,GSYM th])
QED

Theorem copy_prepared_operand[local]:
  (!x. not_fresh_at sm x ==>
       lookup_var x t = lookup_var x s /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
  t.vs_labels = s.vs_labels /\ (!x. opr = Var x ==> not_fresh_at sm x) ==>
  eval_operand opr t = eval_operand opr s /\ op_taint tt opr = op_taint tn opr
Proof
  Cases_on `opr` >> simp[eval_operand_def,op_taint_def] >> metis_tac[]
QED

Theorem create_copy_prepared_mods:
  compile_create_copy target amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\ contract_inv mods exps ctx cenv cx /\ MEM func ctx.ctx_functions /\
  gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG)
    (s0,G0,tn0) marks (OK s,G,tn) /\
  (!fn i v. contextRawReachable$frag_reachable ctx func s0 fn i v ==>
            dalloca_fmp_headroom i v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  accounts_well_typed ee.accounts /\ LENGTH bs = 20 /\
  eval_operand target s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  op_taint tn target = {} /\
  eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  (case sop of NONE => sw = NONE | SOME op =>
    ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  (!x. target = Var x \/ amount = Var x \/ sop = SOME (Var x) ==> not_fresh_at sm x) /\
  code = (lookup_account (word_of_bytes_be bs) ee.accounts).code ==>
  if code = [] then
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
        ?w. sw = SOME w /\ eval_operand op t = SOME w /\ op_taint tt op = {})
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then
    (qx_choosel_then [`code_op`,`a1`,`a2`,`shift`,`a3`,`pre`,`a4`,`req`,`a5`,`p`,`a6`,
                     `a7`,`dst`,`a8`,`a9`,`buf`,`a10`,`len`,`sc`]
      (map_every assume_tac o CONJUNCTS)) create_copy_emit_cuts_mods >>
  suspend "entry"
QED

Resume create_copy_prepared_mods[entry]:
  qpat_assum `storage_trace_domain _ _ _` (assume_tac o REWRITE_RULE[storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
    (mp_then Any (mp_then Any (map_every assume_tac o CONJUNCTS)
       accountsRelPropsTheory.state_rel_accounts)
       stateRelProjTheory.stmt_state_rel_state_rel) >>
  qabbrev_tac `address = typed_val_to_w256 (BaseTV AddressT) (BytesV bs)` >>
  `LENGTH code <= 24576 /\ (lookup_account (w2w address) s.vs_accounts).code = code` by
    (qpat_assum `accounts_agree _ _ ee.accounts s.vs_accounts`
       (mp_then Any mp_tac exprSimSliceExtcodeTheory.slice_extcode_account) >>
     disch_then (qspec_then `bs` mp_tac) >> simp[Abbr `address`]) >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  `allocas_below_fmp s` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx ee s`
      (mp_then Any (drule_then ACCEPT_TAC) bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `w2n s.vs_initial_fmp <= w2n s.vs_fmp` by fs[allocas_below_fmp_def] >>
  suspend "allocation"
QED

Resume create_copy_prepared_mods[allocation]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (gen_tac >> disch_tac >>
     qpat_assum `contract_inv mods exps ctx cenv cx`
       (mp_then Any (drule_all_then ACCEPT_TAC) bodyFullIfExpReachTheory.body_inv_no_phi_mods)) >>
  `!pre Ga ta bb i.
      gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s,G,tn) [] (OK pre,Ga,ta) /\
      lookup_block pre.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb pre.vs_inst_idx = SOME i /\ i.inst_opcode = DALLOCA ==>
      w2n pre.vs_fmp + venomLayout$ceil32 (LENGTH code + 32) < dimword (:256)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks _`
       (mp_then Any (drule_all_then ACCEPT_TAC) create_copy_cut_bound_mods)) >>
  qabbrev_tac `B = w2n s.vs_fmp` >>
  `B = w2n s.vs_fmp /\ w2n s.vs_initial_fmp <= B` by simp[Abbr `B`] >>
  `sm.cs_next_var <= a5.cs_next_var /\ sm.cs_next_var <= a6.cs_next_var` by decide_tac >>
  `!x. target = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  qpat_assum `emit_op EXTCODESIZE _ _ = _`
    (mp_then Any (drule_all_then mp_tac) create_copy_allocated_cut_mods) >>
  Cases_on `code = []`
  >- (qpat_assum `code = []` (fn th => PURE_REWRITE_TAC[th,boolTheory.REFL_CLAUSE,boolTheory.COND_CLAUSES]) >>
      disch_then (qx_choose_then `q` strip_assume_tac) >>
      qexistsl_tac [`q`,`G \\ q`,`tn with t_var := tn.t_var |+ (q,{})`] >> first_assum ACCEPT_TAC) >>
  qpat_assum `code <> []` (fn th => PURE_REWRITE_TAC[th,boolTheory.COND_CLAUSES]) >>
  disch_then (qx_choosel_then [`al`,`Gb`,`tb`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "writing"
QED

Resume create_copy_prepared_mods[writing]:
  qpat_x_assum `code = (lookup_account _ _).code` kall_tac >>
  `0 < LENGTH code` by
    (pure_rewrite_tac[GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,listTheory.LENGTH_NIL] >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `emit_void MSTORE _ _ = _`
    (mp_then Any (drule_all_then
      (qx_choosel_then [`q`,`t`,`Gmat`,`tt`] (map_every assume_tac o CONJUNCTS)))
      create_copy_written_footprint_mods) >>
  suspend "horizons"
QED

Resume create_copy_prepared_mods[horizons]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gmat tt t /\
    wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt /\
    return_buf_frame d cenv sm t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ s`
       (mp_then Any (drule_all_then strip_assume_tac) create_copy_materialized_frame_mods) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  suspend "frame"
QED

Resume create_copy_prepared_mods[frame]:
  `t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels` by
    (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|> = s`
       (mp_tac o AP_TERM ``\z:venom_state. (z.vs_allocas,z.vs_current_bb,z.vs_alloca_next,z.vs_labels)``) >>
     simp[NoAsms]) >>
  `alloca_history func t` by
    (`s.vs_current_bb = sc.cs_current_bb` by metis_tac[same_blocks_def] >>
     qpat_x_assum `?is. sc.cs_current_insts = _ /\ _` strip_assume_tac >>
     qpat_assum `fn_has_code sm sc func`
       (mp_then Any (drule_all_then ACCEPT_TAC) copy_prepared_history)) >>
  `!opr. (!x. opr = Var x ==> not_fresh_at sm x) ==>
     eval_operand opr t = eval_operand opr s /\ op_taint tt opr = op_taint tn opr` by
    (gen_tac >> disch_tac >> irule copy_prepared_operand >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `sm` >> conj_tac >- first_assum ACCEPT_TAC >>
     gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `eval_operand amount t = SOME aw /\ op_taint tt amount = {}` by
    (qpat_assum `!opr. _ ==> eval_operand opr t = _ /\ _` (qspec_then `amount` mp_tac) >>
     impl_tac >- metis_tac[] >> simp[]) >>
  `(case sop of NONE => sw = NONE | SOME op =>
      ?w. sw = SOME w /\ eval_operand op t = SOME w /\ op_taint tt op = {})` by
    (qpat_assum `case sop of NONE => _ | SOME op => _` mp_tac >>
     namedCases_on `sop` ["","salt_op"] >> simp[NoAsms] >> strip_tac >>
     qpat_assum `!opr. _ ==> eval_operand opr t = _ /\ _` (qspec_then `salt_op` mp_tac) >>
     impl_tac >- metis_tac[] >> strip_tac >> qexists `w` >> metis_tac[]) >>
  suspend "pack"
QED

Resume create_copy_prepared_mods[pack]:
  qexistsl_tac [`sc`,`buf`,`len`,`q`,`t`,`Gmat`,`tt`,`n2w (B+21)`,`n2w (LENGTH code+11)`] >>
  map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
    [`w2n (n2w (B+21):bytes32) = _`,`w2n (n2w (LENGTH code+11):bytes32) = _`] >>
  rpt conj_tac >>
  FIRST [REFL_TAC, first_assum ACCEPT_TAC,
    gen_tac >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
      (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC]
QED

Finalise create_copy_prepared_mods
