(* The selected callee's capture and fixed-region reserve execute before
   any parameter is materialized in its local frame. *)
Theory bodySelectedCaptureReserveMods
Ancestors
  intCallEntryFull intCallMaterializeFull storageCopyGasPath context
  exprLoweringProps entryInternalAppend fragGasOriginPtr compileVyper
  intCallCallee compileEnv emitHelper fragExec contextProps
  loweringStateRelDefs ptrDiscipline bodyPtrDefs
  venomExecSemantics venomExecProps venomMemProofs venomState venomInst
  finite_map rich_list list loweringPosts bodyFullShadowBodyInv bodyInvSplit
  memoryValueEncoding vyperState

Theorem capture_layout[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) ==>
  same_blocks entry capture /\
  MAP (\c. (FST c,FST (SND c))) caps = params /\ MAP FST caps = MAP FST params
Proof
  Cases_on `has_rb` >>
  simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, emit_def, fresh_var_def, fresh_id_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_internal_param_decls _ _ _ = (pr,mid)` >> PairCases_on `pr` >>
  drule internal_param_decls_projection >> simp[same_blocks_def] >> strip_tac >> gvs[]
QED

Theorem capture_entered_cursor[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) /\
  fn_has_code entry capture callee /\
  entry.cs_current_insts = [] /\ setup.vs_current_bb = entry.cs_current_bb /\
  setup.vs_inst_idx = 0 /\
  lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
  eval_phis setup first.bb_instructions = OK phi_state /\
  entered = phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions ==>
  entered = setup /\ entered.vs_inst_idx = LENGTH entry.cs_current_insts /\
  lookup_block entered.vs_current_bb callee.fn_blocks = SOME first /\
  isPREFIX (emitted_insts entry capture) (DROP entered.vs_inst_idx first.bb_instructions)
Proof
  strip_tac >>
  drule_then (strip_assume_tac o REWRITE_RULE [same_blocks_def]) (cj 1 capture_layout) >>
  `isPREFIX (emitted_insts entry capture) first.bb_instructions` by
    gvs[fn_has_code_def, emitted_insts_def] >>
  `emitted_insts entry capture <> []` by
    (drule compile_internal_entry_prefix_shape >> simp[]) >>
  drule_then assume_tac compile_internal_entry_prefix_capture_code >>
  gvs[IS_PREFIX_APPEND] >>
  Cases_on `emitted_insts entry capture` >>
  gvs[eval_phis_def, phi_prefix_length_def, venom_state_component_equality]
QED

Theorem capture_next_cursor[local]:
  same_blocks entry capture /\ entry.cs_current_insts = [] /\
  s.vs_current_bb = entry.cs_current_bb /\
  s.vs_inst_idx = LENGTH entry.cs_current_insts ==>
  s.vs_inst_idx + LENGTH (emitted_insts entry capture) = LENGTH capture.cs_current_insts /\
  s.vs_current_bb = capture.cs_current_bb
Proof
  simp[same_blocks_def, emitted_insts_def]
QED

Theorem capture_fixed_reserve[local]:
  (if reserve then
     comp_bind (compile_fixed_region_with_id ilen)
       (\ar. comp_return (SOME (SND ar).buf_operand))
   else comp_return NONE) sa = (imm,sb) /\
  fn_has_code sa sb func /\ fresh_vars_wrt sa s /\ ~s.vs_halted /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u G' tn'.
    u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    u.vs_current_bb = sb.cs_current_bb /\ fresh_vars_wrt sb u /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x) /\ not_fresh_at sb x) /\
    (if reserve then
       ?x. imm = SOME (Var x) /\ ~not_fresh_at sa x /\ not_fresh_at sb x /\
           lookup_var x u = SOME 0w /\ FLOOKUP G' x = NONE /\
           op_taint tn' (Var x) = {}
     else imm = NONE) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
                   (OK u,G',tn')
Proof
  reverse (Cases_on `reserve`)
  >- (simp[comp_return_def] >> strip_tac >> gvs[] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[venom_state_component_equality, gas_origin_ptr_path_rules]) >>
  simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  PairCases_on `ar` >>
  rename1 `compile_fixed_region_with_id ilen sa = ((id,buf),sb)` >>
  drule compile_fixed_region_as_assign >>
  disch_then (assume_tac o MATCH_MP (SPEC_ALL emit_op_same_blocks)) >>
  drule_then strip_assume_tac compile_fixed_region_with_id_result >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[IS_PREFIX_APPEND] >>
  drule_all storage_copy_code_prefix >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qexists_tac `bb` >> asm_rewrite_tac[]) >>
  pop_assum strip_assume_tac >>
  drule_all compile_internal_fixed_region_joint >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK v` >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id ASSIGN [Lit 0w]
         [STRING #"%" (toString sa.cs_next_var)]]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `!x. not_fresh_at sa x ==>
    lookup_var x v = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x) /\ not_fresh_at sb x` by
    (rpt strip_tac >>
     `x <> STRING #"%" (toString sa.cs_next_var) /\ not_fresh_at sb x` by
       fs[not_fresh_at_def] >>
     qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `D` strip_assume_tac) >>
     `EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; ASSIGN] /\
       ?idx out. i.inst_operands = [Lit idx] /\ i.inst_outputs = [out])
       (emitted_insts sa sb)` by simp[mk_inst_def] >>
     drule_all internal_capture_seq_ghost_frame >> strip_tac >>
     first_x_assum (qspec_then `x` mp_tac) >> simp[mk_inst_def] >>
     gvs[run_inst_seq_def, mk_inst_def, step_inst_base_opcode_eqs,
         eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`v with vs_inst_idx := LENGTH sb.cs_current_insts`,`G'`,`tn'`] >>
  fs[same_blocks_def, fresh_vars_wrt_def, venom_state_component_equality,
     eval_operand_def, lookup_var_def, op_prov_def] >>
  gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj,
      eval_operand_def, lookup_var_def, op_prov_def]
QED

Theorem setup_capture_resources[local]:
  setup_callee callee argv t = SOME setup /\ lo <= t.vs_alloca_next ==>
  fresh_vars_wrt entry setup /\ setup.vs_params = argv /\ ~setup.vs_halted /\
  allocas_from lo setup /\ setup.vs_allocas = FEMPTY /\
  setup.vs_alloca_next = t.vs_alloca_next /\ setup.vs_memory = t.vs_memory /\
  setup.vs_call_ctx = t.vs_call_ctx /\ setup.vs_accounts = t.vs_accounts /\
  setup.vs_transient = t.vs_transient /\ setup.vs_immutables = t.vs_immutables /\
  setup.vs_tx_ctx = t.vs_tx_ctx /\ setup.vs_block_ctx = t.vs_block_ctx /\
  setup.vs_logs = t.vs_logs /\ setup.vs_outcomes = t.vs_outcomes /\
  setup.vs_requests = t.vs_requests /\
  setup.vs_pending_deletions = t.vs_pending_deletions /\
  setup.vs_data_section = t.vs_data_section /\ setup.vs_code = t.vs_code /\
  setup.vs_labels = t.vs_labels
Proof
  Cases_on `NULL callee.fn_blocks` >> simp[setup_callee_def] >>
  strip_tac >> qpat_x_assum `_ = setup` (SUBST1_TAC o SYM) >>
  simp[allocas_from_def, fresh_vars_wrt_def]
QED

Theorem capture_reserve_pre_fmp[local]:
  s.vs_allocas = FEMPTY /\ fmp_room ctx callee s ==>
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
   s.vs_alloca_next + pending_alloca_size callee s <= w2n s.vs_initial_fmp)
Proof
  rw[fmp_room_def, allocas_below_fmp_def] >>
  qpat_x_assum `(_ \/ _) ==> _` mp_tac >> simp[] >> decide_tac
QED

Theorem capture_buffer_lookup[local]:
  compile_internal_entry_prefix ce params T st = ((ce',caps,rpc),st') /\
  0 < LENGTH s.vs_params /\ fresh_vars_wrt st' u /\
  run_inst_seq (emitted_insts st st') s = OK u ==>
  lookup_var (STRING #"%" (toString st.cs_next_var)) u = SOME (HD s.vs_params) /\
  not_fresh_at st' (STRING #"%" (toString st.cs_next_var))
Proof
  strip_tac >> drule compile_internal_entry_prefix_shape >> simp[] >>
  disch_then (strip_assume_tac o REWRITE_RULE [GSYM arithmeticTheory.ADD1]) >>
  qabbrev_tac `p = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `v = update_var p (HD s.vs_params) s` >>
  `step_inst_base (mk_inst st.cs_next_id PARAM [Lit 0w] [p]) s = OK v` by
    simp[Once step_inst_base_def, mk_inst_def, Abbr `v`, EL] >>
  qpat_x_assum `run_inst_seq (emitted_insts _ _) _ = _` mp_tac >>
  simp[GENLIST_CONS, combinTheory.o_DEF, run_inst_seq_def] >>
  strip_tac >>
  `lookup_var p u = lookup_var p v` by
    (irule appendStorageStageTransportPtrTheory.run_inst_seq_non_output_vars >>
     goal_assum (drule_at Any) >>
     simp[EVERY_GENLIST, mk_inst_def, is_terminator_def, Abbr `p`,
          ASCIInumbersTheory.toString_inj]) >>
  `lookup_var p v = SOME (HD s.vs_params)` by
    simp[Abbr `v`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  asm_rewrite_tac[] >>
  `p IN FDOM u.vs_vars` by
    (qpat_assum `lookup_var p u = lookup_var p v` (rewrite_tac o single o GSYM) >>
     qpat_assum `lookup_var p v = SOME _` mp_tac >>
     qpat_assum `lookup_var p u = lookup_var p v` (rewrite_tac o single o GSYM) >>
     simp[lookup_var_def, flookup_thm, NoAsms]) >>
  qpat_assum `fresh_vars_wrt st' u`
    (qspec_then `st.cs_next_var` mp_tac o REWRITE_RULE [fresh_vars_wrt_def]) >>
  simp[Abbr `p`, not_fresh_at_def, ASCIInumbersTheory.toString_inj, NoAsms] >>
  qpat_assum `p IN FDOM u.vs_vars` mp_tac >> simp[]
QED

Theorem capture_then_reserve[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) /\
  (if reserve then
     comp_bind (compile_fixed_region_with_id ilen)
       (\ar. comp_return (SOME (SND ar).buf_operand))
   else comp_return NONE) capture = (imm,reserved) /\
  fn_has_code entry capture callee /\
  fn_has_code capture reserved callee /\ entry.cs_current_insts = [] /\
  setup_callee callee argv t = SOME setup /\
  setup.vs_current_bb = entry.cs_current_bb /\ setup.vs_inst_idx = 0 /\
  lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
  eval_phis setup first.bb_instructions = OK phi_state /\
  entered = phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions /\
  eval_operands arg_ops t = SOME argv /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH argv /\
  LENGTH argv < dimword (:256) /\ lo <= t.vs_alloca_next /\
  fmp_room ctx callee setup ==>
  ?u J N x.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
       (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK u,J,N)) /\
    entered = setup /\
    u = setup with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH reserved.cs_current_insts|> /\
    fresh_vars_wrt reserved u /\ ~u.vs_halted /\ u.vs_current_bb = reserved.cs_current_bb /\
    u.vs_inst_idx = LENGTH reserved.cs_current_insts /\ u.vs_allocas = FEMPTY /\
    u.vs_alloca_next = t.vs_alloca_next /\ u.vs_memory = t.vs_memory /\
    u.vs_call_ctx = t.vs_call_ctx /\ u.vs_accounts = t.vs_accounts /\
    u.vs_transient = t.vs_transient /\ u.vs_immutables = t.vs_immutables /\
    u.vs_tx_ctx = t.vs_tx_ctx /\ u.vs_block_ctx = t.vs_block_ctx /\
    u.vs_logs = t.vs_logs /\ u.vs_outcomes = t.vs_outcomes /\
    u.vs_requests = t.vs_requests /\ u.vs_pending_deletions = t.vs_pending_deletions /\
    u.vs_data_section = t.vs_data_section /\ u.vs_code = t.vs_code /\ u.vs_labels = t.vs_labels /\
    allocas_from lo u /\ fmp_room ctx callee u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
     u.vs_alloca_next + pending_alloca_size callee u <= w2n u.vs_initial_fmp) /\
    pc = Var x /\ ce1.ce_return_pc = SOME (PtrVar (Var x) 0) /\
    not_fresh_at reserved x /\ lookup_var x u = SOME entered.vs_return_pc_token /\
    FLOOKUP J x = NONE /\ op_taint N (Var x) = {} /\
    (if reserve then ?q. imm = SOME (Var q) /\ ~not_fresh_at capture q /\
       not_fresh_at reserved q /\ lookup_var q u = SOME 0w /\ FLOOKUP J q = NONE /\
       op_taint N (Var q) = {} else imm = NONE) /\
    (has_rb ==> ?q. q = STRING #"%" (toString entry.cs_next_var) /\
       not_fresh_at reserved q /\ lookup_var q u = SOME (HD argv) /\
       FLOOKUP J q = op_prov G (HD arg_ops) /\ op_taint N (Var q) = {}) /\
    (!i. i < LENGTH params ==> ?p. SND (SND (EL i caps)) = Var p /\
       not_fresh_at reserved p /\
       lookup_var p u = SOME (EL ((if has_rb then 1 else 0) + i) argv) /\
       FLOOKUP J p = op_prov G (EL ((if has_rb then 1 else 0) + i) arg_ops) /\
       op_taint N (Var p) = {}) /\
    N.t_mem = tn.t_mem /\ N.t_stor = tn.t_stor /\ N.t_trans = tn.t_trans /\ N.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all_then strip_assume_tac capture_entered_cursor >>
  drule_all setup_capture_resources >> disch_then (qspec_then `entry` strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp setup` by
    (disch_tac >> drule_all capture_reserve_pre_fmp >> simp[]) >>
  `fresh_vars_wrt entry entered /\
   (if has_rb then 1 else 0) + LENGTH params <= LENGTH entered.vs_params /\
   LENGTH entered.vs_params < dimword (:256) /\ ~entered.vs_halted /\
   allocas_from lo entered /\ (ctx_has_dalloca ctx ==> allocas_below_fmp entered) /\
   entered.vs_current_bb = entry.cs_current_bb` by asm_rewrite_tac[] >>
  drule_all compile_internal_entry_prefix_joint >>
  disch_then (qspecl_then [`tn with t_var := FEMPTY`, `MAP (op_prov G) arg_ops`, `FEMPTY`]
    (qx_choose_then `captured` (qx_choose_then `Gcap`
      (qx_choose_then `tncap` (qx_choose_then `x` strip_assume_tac))))) >>
  drule_then strip_assume_tac capture_layout >>
  drule_all_then strip_assume_tac capture_next_cursor >>
  qabbrev_tac `at_capture = captured with vs_inst_idx := LENGTH capture.cs_current_insts` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
       (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK at_capture,Gcap,tncap)` by
    (rpt gen_tac >> qunabbrev_tac `at_capture` >>
     qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `D` (qspec_then `explicit` mp_tac o CONJUNCT2)) >>
     qpat_assum `entered.vs_inst_idx + _ = _` (rewrite_tac o single)) >>
  `fresh_vars_wrt capture at_capture /\ ~at_capture.vs_halted /\ allocas_from lo at_capture /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp at_capture) /\
   at_capture.vs_current_bb = capture.cs_current_bb /\
   at_capture.vs_inst_idx = LENGTH capture.cs_current_insts` by
    (qunabbrev_tac `at_capture` >> conj_tac
     >- (qpat_assum `fresh_vars_wrt capture captured` mp_tac >> simp[NoAsms, fresh_vars_wrt_def]) >>
     qpat_assum `captured = _` (once_rewrite_tac o single) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp setup` mp_tac >>
     simp[IgnAsm `ctx_has_dalloca ctx ==> allocas_below_fmp setup`,
          allocas_from_def, allocas_below_fmp_def]) >>
  drule_all capture_fixed_reserve >>
  disch_then (qspecl_then [`tncap`, `MAP (op_prov G) arg_ops`, `Gcap`]
    (qx_choose_then `u` (qx_choose_then `J` (qx_choose_then `N` strip_assume_tac)))) >>
  `u = setup with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH reserved.cs_current_insts|>` by
    (qpat_assum `u = at_capture with <|vs_vars := _; vs_inst_idx := _|>` (fn th => CONV_TAC (LAND_CONV (REWR_CONV th))) >>
     qunabbrev_tac `at_capture` >>
     qpat_assum `captured = _` (once_rewrite_tac o single) >> simp[]) >>
  `fmp_room ctx callee u` by
    (qspecl_then [`ctx`, `callee`, `setup`, `u`] mp_tac fmp_room_fields_cong >>
     qpat_assum `u = setup with <|vs_vars := _; vs_inst_idx := _|>` (once_rewrite_tac o single) >> simp[]) >>
  `u.vs_allocas = FEMPTY` by
    (qpat_assum `u = setup with <|vs_vars := _; vs_inst_idx := _|>` (once_rewrite_tac o single) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size callee u <= w2n u.vs_initial_fmp` by
    (disch_tac >> drule_all capture_reserve_pre_fmp >> simp[]) >>
  drule_then strip_assume_tac compile_internal_entry_prefix_shape >>
  drule_then assume_tac compile_internal_entry_prefix_capture_code >>
  qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `ARB` (assume_tac o CONJUNCT1)) >>
  drule_all_then strip_assume_tac compile_internal_entry_prefix_ghost_outputs >>
  drule_all_then strip_assume_tac internal_capture_seq_ghost_frame >>
  `LENGTH arg_ops = LENGTH argv` by
    (drule tupleLoadPropsTheory.eval_operands_length >> simp[]) >>
  `!i. i < (if has_rb then 1 else 0) + LENGTH params ==>
     FLOOKUP Gcap (STRING #"%" (toString (entry.cs_next_var + i))) =
       op_prov G (EL i arg_ops) /\
     op_taint tncap (Var (STRING #"%" (toString (entry.cs_next_var + i)))) = {}` by
    (gen_tac >> disch_tac >> `i < LENGTH arg_ops` by (Cases_on `has_rb` >> fs[] >> decide_tac) >>
     qpat_assum `!i. i < _ ==> FLOOKUP Gcap _ = (if _ then _ else _) /\ _`
       (qspec_then `i` mp_tac) >> simp[EL_MAP]) >>
  `!p. not_fresh_at capture p ==>
     lookup_var p u = lookup_var p captured /\ FLOOKUP J p = FLOOKUP Gcap p /\
     op_taint N (Var p) = op_taint tncap (Var p) /\ not_fresh_at reserved p` by
    (qunabbrev_tac `at_capture` >>
     qpat_assum `!p. not_fresh_at capture p ==> _` mp_tac >> simp[NoAsms, lookup_var_def]) >>
  `entered.vs_params = argv` by asm_rewrite_tac[] >>
  `!i. i < LENGTH params ==> ?p. SND (SND (EL i caps)) = Var p /\
       not_fresh_at reserved p /\
       lookup_var p u = SOME (EL ((if has_rb then 1 else 0) + i) argv) /\
       FLOOKUP J p = op_prov G (EL ((if has_rb then 1 else 0) + i) arg_ops) /\
       op_taint N (Var p) = {}` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH params ==> ?p. _` (drule_then strip_assume_tac) >>
     qpat_assum `!p. not_fresh_at capture p ==> lookup_var p u = lookup_var p captured /\ _`
       (drule_then strip_assume_tac) >>
     `p = STRING #"%" (toString (entry.cs_next_var + ((if has_rb then 1 else 0) + i)))` by
       (qpat_assum `!i. i < LENGTH params ==> SND (SND _) = Var _` (drule_then mp_tac) >>
        qpat_assum `SND (SND (EL i caps)) = Var p` (pure_rewrite_tac o single) >>
        pure_once_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >> simp[NoAsms]) >>
     qpat_assum `!i. i < _ ==> FLOOKUP Gcap _ = op_prov G _ /\ _`
       (qspec_then `(if has_rb then 1 else 0) + i` mp_tac) >>
     (impl_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC)) >>
     qpat_assum `p = STRING #"%" _` (pure_rewrite_tac o single o SYM) >> strip_tac >>
     qexists_tac `p` >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       asm_rewrite_tac[])) >>
  `has_rb ==> ?q. q = STRING #"%" (toString entry.cs_next_var) /\
       not_fresh_at reserved q /\ lookup_var q u = SOME (HD argv) /\
       FLOOKUP J q = op_prov G (HD arg_ops) /\ op_taint N (Var q) = {}` by
    (disch_tac >> `0 < LENGTH entered.vs_params` by (fs[] >> decide_tac) >>
     qpat_assum `compile_internal_entry_prefix _ _ has_rb _ = _` mp_tac >>
     qpat_assum `has_rb` (pure_rewrite_tac o single o EQT_INTRO) >> disch_tac >>
     drule_all_then strip_assume_tac capture_buffer_lookup >>
     qpat_assum `!p. not_fresh_at capture p ==> lookup_var p u = lookup_var p captured /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!i. i < _ ==> FLOOKUP Gcap _ = op_prov G _ /\ _`
       (qspec_then `0` mp_tac) >>
     (impl_tac >- simp[]) >>
     Cases_on `arg_ops` >- fs[] >>
     simp[NoAsms, EL] >> strip_tac >> asm_rewrite_tac[]) >>
  qpat_assum `!p. not_fresh_at capture p ==> lookup_var p u = lookup_var p captured /\ _`
    (qspec_then `x` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `FLOOKUP Gcap x = NONE /\ op_taint tncap (Var x) = {}` by
    (qpat_assum `op_prov Gcap pc = NONE` mp_tac >>
     qpat_assum `op_taint tncap pc = {}` mp_tac >>
     qpat_assum `pc = Var x` (pure_rewrite_tac o single) >> simp[NoAsms, op_prov_def]) >>
  `ce1.ce_return_pc = SOME (PtrVar (Var x) 0)` by
    (qpat_assum `ce1.ce_return_pc = _` mp_tac >>
     qpat_assum `pc = Var x` (pure_rewrite_tac o single) >> simp[NoAsms]) >>
  qpat_assum `u = setup with <|vs_vars := _; vs_inst_idx := _|>`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  qexistsl_tac [`u`,`J`,`N`,`x`] >>
  conj_tac
  >- (rpt gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gcap`,`at_capture`,`tncap`] >> simp[]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[allocas_from_def])
QED

Theorem reserve_param_regions[local]:
  internal_args_rel ce params penv idx argv t.vs_alloca_next t.vs_memory /\
  u.vs_memory = t.vs_memory /\ u.vs_alloca_next = t.vs_alloca_next /\
  u.vs_allocas = FEMPTY /\ fresh_vars_wrt reserved u /\
  MAP (\c. (FST c,FST (SND c))) caps = params /\
  (!i. i < LENGTH params ==> ?p. SND (SND (EL i caps)) = Var p /\
    not_fresh_at reserved p /\ lookup_var p u = SOME (EL (idx + i) argv)) ==>
  ?mr. mat_pending ce penv reserved u t.vs_alloca_next mr caps /\
       mat_inv callee ce penv reserved u t.vs_alloca_next mr /\
       (!n1 n2 b1 sz1 b2 sz2. n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\
         mr n2 = SOME (b2,sz2) ==> regions_disjoint b1 sz1 b2 sz2) /\
       (!n b sz. mr n = SOME (b,sz) <=>
         ?i off. i < LENGTH params /\ ~SND (EL i params) /\
           FST (EL i params) = n /\ FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) /\
           b = w2n (EL (idx + i) argv))
Proof
  strip_tac >>
  `LENGTH caps = LENGTH params` by metis_tac[LENGTH_MAP] >>
  `!i. i < LENGTH params ==> FST (EL i caps) = FST (EL i params) /\
      FST (SND (EL i caps)) = SND (EL i params) /\
      ?p. SND (SND (EL i caps)) = Var p /\ not_fresh_at reserved p /\
          lookup_var p u = SOME (EL (idx + i) argv)` by
    (gen_tac >> disch_tac >>
     `EL i (MAP (\c. (FST c,FST (SND c))) caps) = EL i params` by asm_rewrite_tac[] >>
     pop_assum mp_tac >> Cases_on `EL i params` >>
     simp[EL_MAP, IgnAsm `MAP _ caps = params`]) >>
  drule_all internal_args_materialization_pre >>
  disch_then (qspec_then `callee` strip_assume_tac) >>
  qexists_tac `mr` >> asm_rewrite_tac[]
QED

Theorem reserve_capture_coverage[local]:
  MAP (\c. (FST c,FST (SND c))) caps = params /\
  (!i. i < LENGTH params ==> ?p. SND (SND (EL i caps)) = Var p /\
     lookup_var p u = SOME (EL (idx + i) argv) /\
     FLOOKUP J p = op_prov G (EL (idx + i) arg_ops) /\
     op_taint N (Var p) = {}) /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
     ?b bsz. op_prov G (EL (idx + i) arg_ops) = SOME (b,bsz) /\
       b <= w2n (EL (idx + i) argv) /\ w2n (EL (idx + i) argv) + sz <= b + bsz) /\
  (!mem. mem_agree_outside N.t_mem u.vs_memory mem ==>
     internal_args_rel ce params penv idx argv frontier mem) /\
  (!nm e. FLOOKUP penv nm = SOME e ==> value_has_type e.type e.value) ==>
  EVERY (\c. op_taint N (SND (SND c)) = {} /\
     (!p off sz e. ~FST (SND c) /\ SND (SND c) = Var p /\
       FLOOKUP ce.ce_vars (FST c) = SOME (MemLoc off sz) /\
       FLOOKUP penv (FST c) = SOME e ==>
       ptr_covers J N p u sz /\
       !w mem. lookup_var p u = SOME w /\
         mem_agree_outside N.t_mem u.vs_memory mem ==>
         val_in_memory e.type e.value (w2n w) mem)) caps
Proof
  strip_tac >> simp[EVERY_EL] >> qx_gen_tac `i` >> disch_tac >>
  `i < LENGTH params` by metis_tac[LENGTH_MAP] >>
  `FST (EL i caps) = FST (EL i params) /\
   FST (SND (EL i caps)) = SND (EL i params)` by
    (`EL i (MAP (\c. (FST c,FST (SND c))) caps) = EL i params` by asm_rewrite_tac[] >>
     pop_assum mp_tac >> Cases_on `EL i params` >>
     simp[EL_MAP, IgnAsm `MAP _ caps = params`]) >>
  qpat_assum `!i. i < LENGTH params ==> ?p. _` drule >>
  disch_then (qx_choose_then `q` strip_assume_tac) >> simp[] >>
  rpt strip_tac
  >- (simp[ptr_covers_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qpat_assum `!mem. mem_agree_outside _ _ mem ==> _` drule >>
  rewrite_tac[internal_args_rel_def] >> strip_tac >>
  qpat_assum `!i. i < LENGTH params ==> ?off sz e. _` drule >>
  strip_tac >> gvs[] >>
  mp_tac (CONJUNCT1 memory_encoding_bridges) >>
  rewrite_tac[memory_encoding_bridge_def] >> metis_tac[]
QED

Theorem reserve_buffer_frame[local]:
  (has_rb ==> ?p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) /\
     not_fresh_at reserved p /\ lookup_var p u = SOME (HD argv) /\
     FLOOKUP J p = op_prov G (HD arg_ops) /\ op_taint N (Var p) = {}) /\
  (~has_rb ==> ce.ce_return_buf = NONE) /\
  (has_rb ==> ?b sz. op_prov G (HD arg_ops) = SOME (b,sz) /\
     b <= w2n (HD argv) /\ w2n (HD argv) + type_memory_size rtv <= b + sz /\
     b + sz <= u.vs_alloca_next) ==>
  return_buf_ptr (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) ce J N u /\
  return_buf_frame (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) ce reserved u /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at reserved p)
Proof
  Cases_on `has_rb` >> simp[return_buf_frame_def, return_buf_ptr_def, ptr_covers_def] >>
  strip_tac >> simp[] >> decide_tac
QED

(* Capture leaves the physical linked section and all non-variable taints
   unchanged. Only the return destination and token require new local facts. *)
Theorem reserve_linked_ghost[local]:
  ce.ce_modules = caller.ce_modules /\ ce.ce_module_vars = caller.ce_module_vars /\
  (!n p sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar p sz)) /\
  (!x. imm = SOME (Var x) ==> FLOOKUP J x = NONE /\ op_taint N (Var x) = {}) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> op_taint N (Var x) = {}) /\
  return_buf_ptr d ce J N u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
  u.vs_memory = t.vs_memory /\ u.vs_call_ctx = t.vs_call_ctx /\
  u.vs_accounts = t.vs_accounts /\ u.vs_transient = t.vs_transient /\
  u.vs_immutables = t.vs_immutables /\
  N.t_mem = tn.t_mem /\ N.t_stor = tn.t_stor /\ N.t_trans = tn.t_trans /\ N.t_imm = tn.t_imm /\
  ghost_inv_at_mods D lo dc caller cx ec G tn t ==>
  ghost_inv_at_mods D lo d (ce with ce_imm_alloca := imm) cx' es J N u
Proof
  strip_tac >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  qpat_x_assum `return_buf_ptr d ce J N u` mp_tac >>
  qpat_x_assum `stor_taint_ok_at D tn t` mp_tac >>
  qpat_x_assum `!i. i < lo /\ _ ==> imm_section_dead_mods caller _ i` mp_tac >>
  Cases_on `d` >>
  TRY (rename1 `return_buf_ptr (SOME bp) _ _ _ _ ==> _` >> PairCases_on `bp`) >>
  simp[ghost_inv_at_mods_def, return_buf_ptr_def, stor_taint_ok_at_def,
       imm_section_dead_mods_def]
QED

Theorem capture_env_pins[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) ==>
  ce1.ce_vars = ce.ce_vars /\ ce1.ce_modules = ce.ce_modules /\
  ce1.ce_module_vars = ce.ce_module_vars /\
  (~has_rb ==> ce1.ce_return_buf = ce.ce_return_buf)
Proof
  Cases_on `has_rb` >>
  simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem reserve_mat_vars[local]:
  ce1.ce_vars = ce.ce_vars ==>
  (mat_pending ce1 penv reserved u f0 mr caps <=>
   mat_pending ce penv reserved u f0 mr caps) /\
  (mat_inv callee ce1 penv reserved u f0 mr <=>
   mat_inv callee ce penv reserved u f0 mr)
Proof
  simp[mat_pending_def, mat_inv_def, local_ptrs_rel_def, local_region_def]
QED

(* Compilation cuts and the cursor describe the same decoded function. The
   materialization certificates below all refer to the one reached triple. *)
Theorem selected_capture_reserve_run_mods:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) /\
  (if ctor /\ 0 < ilen then
     comp_bind (compile_fixed_region_with_id ilen)
       (\ar. comp_return (SOME (SND ar).buf_operand))
   else comp_return NONE) capture = (imm,reserved) /\
  fn_has_code entry capture callee /\
  fn_has_code capture reserved callee /\ entry.cs_current_insts = [] /\
  setup_callee callee argv t = SOME setup /\
  setup.vs_current_bb = entry.cs_current_bb /\ setup.vs_inst_idx = 0 /\
  lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
  eval_phis setup first.bb_instructions = OK phi_state /\
  entered = phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions /\
  eval_operands arg_ops t = SOME argv /\
  lo <= t.vs_alloca_next /\ fmp_room ctx callee setup /\
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
     internal_args_rel ce params penv (if has_rb then 1 else 0) argv t.vs_alloca_next mem) /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
     ?b bsz. op_prov G (EL ((if has_rb then 1 else 0) + i) arg_ops) = SOME (b,bsz) /\
       b <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
       w2n (EL ((if has_rb then 1 else 0) + i) argv) + sz <= b + bsz) /\
  (has_rb ==> ?b sz. op_prov G (HD arg_ops) = SOME (b,sz) /\
     b <= w2n (HD argv) /\ w2n (HD argv) + type_memory_size rtv <= b + sz /\
     b + sz <= t.vs_alloca_next) /\
  (has_rb ==> ?off sz. ce.ce_return_buf = SOME (MemLoc off sz)) /\
  (~has_rb ==> ce.ce_return_buf = NONE) /\
  t.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  fn_inst_ids_distinct callee /\ es.scopes = [penv] /\
  (!nm e. FLOOKUP penv nm = SOME e ==> value_has_type e.type e.value) /\
  (!n p sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar p sz)) /\
  ce.ce_modules = caller.ce_modules /\ ce.ce_module_vars = caller.ce_module_vars /\
  (!D. D IN Ds ==> ghost_inv_at_mods D lo dc caller cx ec G tn t) ==>
  ?u J N x mr.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
       (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK u,J,N)) /\
    entered = setup /\
    u = setup with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH reserved.cs_current_insts|> /\
    fresh_vars_wrt reserved u /\ ~u.vs_halted /\ u.vs_current_bb = reserved.cs_current_bb /\
    u.vs_inst_idx = LENGTH reserved.cs_current_insts /\ u.vs_allocas = FEMPTY /\
    u.vs_alloca_next = t.vs_alloca_next /\ u.vs_memory = t.vs_memory /\
    u.vs_call_ctx = t.vs_call_ctx /\ u.vs_accounts = t.vs_accounts /\
    u.vs_transient = t.vs_transient /\ u.vs_immutables = t.vs_immutables /\
    u.vs_tx_ctx = t.vs_tx_ctx /\ u.vs_block_ctx = t.vs_block_ctx /\
    u.vs_logs = t.vs_logs /\ u.vs_outcomes = t.vs_outcomes /\
    u.vs_requests = t.vs_requests /\ u.vs_pending_deletions = t.vs_pending_deletions /\
    u.vs_data_section = t.vs_data_section /\ u.vs_code = t.vs_code /\ u.vs_labels = t.vs_labels /\
    allocas_from lo u /\ fmp_room ctx callee u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
     u.vs_alloca_next + pending_alloca_size callee u <= w2n u.vs_initial_fmp) /\
    pc = Var x /\ ce1.ce_return_pc = SOME (PtrVar (Var x) 0) /\
    not_fresh_at reserved x /\ lookup_var x u = SOME entered.vs_return_pc_token /\
    FLOOKUP J x = NONE /\ op_taint N (Var x) = {} /\ ret_pc_ok ce1 reserved u /\
    (if ctor /\ 0 < ilen then ?q. imm = SOME (Var q) /\ ~not_fresh_at capture q /\
       not_fresh_at reserved q /\ lookup_var q u = SOME 0w /\ FLOOKUP J q = NONE /\
       op_taint N (Var q) = {} else imm = NONE) /\
    (!p. imm = SOME (Var p) ==> not_fresh_at reserved p) /\
    (has_rb ==> ?p sz. ce1.ce_return_buf = SOME (PtrVar (Var p) sz) /\
       not_fresh_at reserved p /\ lookup_var p u = SOME (HD argv) /\
       FLOOKUP J p = op_prov G (HD arg_ops) /\ op_taint N (Var p) = {}) /\
    (!p sz. ce1.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at reserved p) /\
    return_buf_ptr (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) ce1 J N u /\
    return_buf_frame (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) ce1 reserved u /\
    (!i. i < LENGTH params ==> ?p. SND (SND (EL i caps)) = Var p /\
       not_fresh_at reserved p /\
       lookup_var p u = SOME (EL ((if has_rb then 1 else 0) + i) argv) /\
       FLOOKUP J p = op_prov G (EL ((if has_rb then 1 else 0) + i) arg_ops) /\
       op_taint N (Var p) = {}) /\
    N.t_mem = tn.t_mem /\ N.t_stor = tn.t_stor /\ N.t_trans = tn.t_trans /\ N.t_imm = tn.t_imm /\
    ce1.ce_vars = ce.ce_vars /\ ce1.ce_modules = ce.ce_modules /\
    ce1.ce_module_vars = ce.ce_module_vars /\
    (!mem. mem_agree_outside N.t_mem u.vs_memory mem ==>
       internal_args_rel ce1 params penv (if has_rb then 1 else 0) argv t.vs_alloca_next mem) /\
    fn_inst_ids_distinct callee /\ ALL_DISTINCT (MAP FST caps) /\
    mat_pending (ce1 with ce_imm_alloca := imm) penv reserved u t.vs_alloca_next mr caps /\
    mat_inv callee (ce1 with ce_imm_alloca := imm) penv reserved u t.vs_alloca_next mr /\
    (!n1 n2 b1 sz1 b2 sz2. n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\
       mr n2 = SOME (b2,sz2) ==> regions_disjoint b1 sz1 b2 sz2) /\
    (!n b sz. mr n = SOME (b,sz) <=>
       ?i off. i < LENGTH params /\ ~SND (EL i params) /\
         FST (EL i params) = n /\ FLOOKUP ce1.ce_vars n = SOME (MemLoc off sz) /\
         b = w2n (EL ((if has_rb then 1 else 0) + i) argv)) /\
    u.vs_alloca_next + internal_stack_size (ce1 with ce_imm_alloca := imm)
      (MAP (\c. (FST c,FST (SND c))) caps) < dimword (:256) /\
    (!nm p sz. FLOOKUP ce1.ce_vars nm = SOME (PtrVar (Var p) sz) ==> not_fresh_at reserved p) /\
    (!p sz. ce1.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at reserved p) /\
    es.scopes = [penv] /\
    (!nm e. FLOOKUP penv nm = SOME e ==> value_has_type e.type e.value) /\
    EVERY (\c. op_taint N (SND (SND c)) = {} /\
       (!p off sz e. ~FST (SND c) /\ SND (SND c) = Var p /\
         FLOOKUP ce1.ce_vars (FST c) = SOME (MemLoc off sz) /\
         FLOOKUP penv (FST c) = SOME e ==>
         ptr_covers J N p u sz /\
         !w mem. lookup_var p u = SOME w /\
           mem_agree_outside N.t_mem u.vs_memory mem ==>
           val_in_memory e.type e.value (w2n w) mem)) caps /\
    (!D. D IN Ds ==>
       ghost_inv_at_mods D lo (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE)
         (ce1 with ce_imm_alloca := imm) cx' es J N u)
Proof
  strip_tac >>
  `internal_args_rel ce params penv (if has_rb then 1 else 0) argv t.vs_alloca_next t.vs_memory` by
    (first_assum irule >> simp[mem_agree_outside_def]) >>
  qpat_assum `internal_args_rel _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [internal_args_rel_def]) >>
  drule_all capture_then_reserve >>
  disch_then (qspecl_then [`tn`,`G`]
    (qx_choose_then `u` (qx_choose_then `J` (qx_choose_then `N`
      (qx_choose_then `x` strip_assume_tac))))) >>
  drule_then strip_assume_tac capture_layout >>
  drule_then strip_assume_tac capture_env_pins >>
  drule_then assume_tac (cj 6 compile_internal_entry_prefix_shape) >>
  `has_rb ==> ?p sz. ce1.ce_return_buf = SOME (PtrVar (Var p) sz) /\
     not_fresh_at reserved p /\ lookup_var p u = SOME (HD argv) /\
     FLOOKUP J p = op_prov G (HD arg_ops) /\ op_taint N (Var p) = {}` by
    (disch_tac >>
     qpat_assum `has_rb ==> ?off sz. ce.ce_return_buf = _` (drule_then strip_assume_tac) >>
     qpat_assum `has_rb ==> ?q. q = STRING _ _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!off sz. has_rb /\ ce.ce_return_buf = _ ==> _`
       (drule_all_then assume_tac) >>
     qexistsl_tac [`q`,`sz`] >> simp[]) >>
  `~has_rb ==> ce1.ce_return_buf = NONE` by (strip_tac >> simp[]) >>
  `(has_rb ==> ?b sz. op_prov G (HD arg_ops) = SOME (b,sz) /\
     b <= w2n (HD argv) /\ w2n (HD argv) + type_memory_size rtv <= b + sz /\
     b + sz <= u.vs_alloca_next)` by asm_rewrite_tac[] >>
  drule_all_then strip_assume_tac reserve_buffer_frame >>
  `!p. imm = SOME (Var p) ==> FLOOKUP J p = NONE /\ op_taint N (Var p) = {}` by
    (Cases_on `ctor /\ 0 < ilen` >>
     qpat_assum `(if _ then ?q. imm = _ /\ _ else imm = NONE)` mp_tac >>
     simp[NoAsms] >> gvs[]) >>
  `!p sz. ce1.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
     op_taint N (Var p) = {}` by simp[] >>
  `ret_pc_ok ce1 reserved u` by simp[ret_pc_ok_def] >>
  `(!n p sz. FLOOKUP ce1.ce_vars n <> SOME (PtrVar p sz)) /\
   ce1.ce_modules = caller.ce_modules /\ ce1.ce_module_vars = caller.ce_module_vars /\
   lo <= u.vs_alloca_next` by asm_rewrite_tac[] >>
  `!D. D IN Ds ==>
    ghost_inv_at_mods D lo (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE)
      (ce1 with ce_imm_alloca := imm) cx' es J N u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!D. D IN Ds ==> ghost_inv_at_mods D lo dc caller _ _ _ _ _`
       (drule_then assume_tac) >>
     drule_all reserve_linked_ghost >> simp[]) >>
  qabbrev_tac `idx = if has_rb then 1 else 0` >>
  `!mem. mem_agree_outside N.t_mem u.vs_memory mem ==>
       internal_args_rel ce1 params penv idx argv t.vs_alloca_next mem` by
    (gen_tac >> asm_rewrite_tac[] >> disch_tac >>
     qpat_assum `!mem. mem_agree_outside tn.t_mem _ mem ==> internal_args_rel ce _ _ _ _ _ mem`
       (drule_then mp_tac) >>
     pure_rewrite_tac[internal_args_rel_def] >> asm_rewrite_tac[]) >>
  `!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce1.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
     ?b bsz. op_prov G (EL (idx + i) arg_ops) = SOME (b,bsz) /\
       b <= w2n (EL (idx + i) argv) /\ w2n (EL (idx + i) argv) + sz <= b + bsz` by
    asm_rewrite_tac[] >>
  `!i. i < LENGTH params ==> ?p. SND (SND (EL i caps)) = Var p /\
     lookup_var p u = SOME (EL (idx + i) argv) /\
     FLOOKUP J p = op_prov G (EL (idx + i) arg_ops) /\ op_taint N (Var p) = {}` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH params ==> ?p. _ /\ not_fresh_at reserved p /\ _`
       (drule_then strip_assume_tac) >> qexists_tac `p` >> asm_rewrite_tac[]) >>
  drule_all_then assume_tac reserve_capture_coverage >>
  `!i. i < LENGTH params ==> ?p. SND (SND (EL i caps)) = Var p /\
    not_fresh_at reserved p /\ lookup_var p u = SOME (EL (idx + i) argv)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH params ==> ?p. _ /\ not_fresh_at reserved p /\ _`
       (drule_then strip_assume_tac) >> qexists_tac `p` >> asm_rewrite_tac[]) >>
  drule_all reserve_param_regions >>
  disch_then (qspec_then `callee` (qx_choose_then `mr` strip_assume_tac)) >>
  `internal_stack_size (ce1 with ce_imm_alloca := imm) params = internal_stack_size ce params` by
    (irule internal_stack_size_vars >> simp[]) >>
  qexistsl_tac [`u`,`J`,`N`,`x`,`mr`] >>
  `((ce1 with ce_imm_alloca := imm).ce_vars = ce.ce_vars)` by simp[] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> first_assum irule)
  >- (Cases_on `ctor /\ 0 < ilen` >>
      qpat_assum `(if _ then ?q. imm = _ /\ _ else imm = NONE)` mp_tac >>
      simp[NoAsms] >> gvs[])
  >- asm_rewrite_tac[]
  >- (qpat_assum `(ce1 with ce_imm_alloca := imm).ce_vars = _`
        (fn eq => pure_rewrite_tac[MATCH_MP reserve_mat_vars eq]) >> first_assum ACCEPT_TAC)
  >- (qpat_assum `(ce1 with ce_imm_alloca := imm).ce_vars = _`
        (fn eq => pure_rewrite_tac[MATCH_MP reserve_mat_vars eq]) >> first_assum ACCEPT_TAC)
  >- (qpat_assum `ce1.ce_vars = ce.ce_vars` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC)
  >- asm_rewrite_tac[]
  >- (rpt gen_tac >> qpat_assum `!n p sz. FLOOKUP ce1.ce_vars n <> _`
        (qspecl_then [`nm`,`Var p`,`sz`] mp_tac) >> simp[NoAsms])
  >- simp[]
QED
