(* One actual passing-checks endpoint and its memory-safe continuation. *)
Theory entryCheckEndpointMem
Ancestors
  entryPrefixMem entrySelectedEndpointMem entryRegistrationCursorHistory
  moduleLowering emitHelper compileEnv exprLoweringProps fragExec fragExecMem
  instMemFrontier venomInst list rich_list finite_map words venomExecSemantics
  venomState moduleLoweringProps entryDispatchMem
Libs
  wordsLib

Theorem compile_entry_checks_endpoint:
  compile_entry_checks mc pay sc = ((),sk) /\
  fn_has_code sc sk fn /\ fresh_vars_wrt sc s /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  mc <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ sc.cs_current_insts = [] ==>
  ?t. vars_pc_only s t /\ fresh_vars_wrt sk t /\
      (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sk.cs_current_bb /\
      t.vs_inst_idx = LENGTH sk.cs_current_insts /\
      (((!n. mem_safe_run n ctx fn t) /\
        (t.vs_inst_idx = 0 ==> !n. mem_safe_blocks n ctx fn t)) ==>
       !n. mem_safe_blocks n ctx fn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `pay /\ mc <= 4`
  >- ( `sk = sc` by
         (qpat_x_assum `compile_entry_checks _ _ _ = _` mp_tac >>
          simp[compile_entry_checks_def, comp_bind_def,
               comp_ignore_bind_def, comp_return_def]) >>
       gvs[] >> qexists_tac `s` >> simp[vars_pc_only_def, venom_state_component_equality]) >>
  `?u. run_inst_seq (emitted_insts sc sk) s = OK u /\
       vars_pc_only s u /\ fresh_vars_wrt sk u /\
       (!x. not_fresh_at sc x ==> lookup_var x u = lookup_var x s) /\
       sk.cs_current_bb = sc.cs_current_bb /\
       EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
         (emitted_insts sc sk)` by suspend "sequence" >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX sk.cs_current_insts bb.bb_instructions /\
        eval_phis s bb.bb_instructions = OK s /\
        phi_prefix_length bb.bb_instructions = 0` by suspend "code" >>
  qexists_tac `u with vs_inst_idx := LENGTH sk.cs_current_insts` >>
  drule vars_pc_only_fields >> strip_tac >>
  simp[vars_pc_only_inst_idx, fresh_vars_wrt_def, control_moves_keep_vars] >>
  suspend "safety"
QED

Resume compile_entry_checks_endpoint[sequence]:
  markerLib.RESUME_TAC >>
  `mc < dimword (:256)` by decide_tac >>
  Cases_on `pay` >> Cases_on `4 < mc` >>
  gvs[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def] >>
  fs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[run_inst_seq_def, step_inst_base_def, mk_inst_def,
                   instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read0_def, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       bool_to_word_def, is_terminator_def] >>
  simp[vars_pc_only_def, venom_state_component_equality] >>
  (conj_tac
   >- (fs[fresh_vars_wrt_def] >> rpt strip_tac >> fs[]) >>
   rw[FLOOKUP_UPDATE] >> gvs[not_fresh_at_def])
QED

Resume compile_entry_checks_endpoint[code]:
  markerLib.RESUME_TAC >>
  Cases_on `pay` >> Cases_on `4 < mc` >>
  gvs[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def] >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[eval_phis_def, phi_prefix_length_def, mk_inst_def]
QED

Resume compile_entry_checks_endpoint[safety]:
  `emitted_insts sc sk = sk.cs_current_insts` by
    simp[emitted_insts_def] >>
  `u.vs_current_bb = s.vs_current_bb` by
    (qspecl_then [`emitted_insts sc sk`, `s`, `0`, `ctx`, `bb`]
       mp_tac exec_block_run_inst_seq >> fs[] >> metis_tac[]) >>
  simp[] >> strip_tac >>
  irule mem_safe_blocks_no_phi >>
  reverse conj_tac >- metis_tac[] >>
  `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
  simp[] >> gen_tac >>
  qspecl_then [`emitted_insts sc sk`, `s`, `n`, `ctx`, `fn`, `bb`]
    mp_tac mem_safe_run_inst_seq >>
  simp[] >> impl_tac
  >- metis_tac[compile_entry_checks_mem_ok] >>
  strip_tac >> first_x_assum (qspec_then `u` mp_tac) >> simp[]
QED

Finalise compile_entry_checks_endpoint

Theorem selected_dispatch_checks_endpoint:
  compile_selector_dispatch_linear sels fl sf = ((),sd) /\
  fn_has_code sf sd fn /\ EVERY (\(sel,lbl). sel < 2 ** 32) sels /\
  compile_entry_checks mc pay sc = ((),sk) /\ fn_has_code sc sk fn /\
  sd.cs_next_var <= sc.cs_next_var /\ sc.cs_current_insts = [] /\
  linear_dispatch_target s.vs_call_ctx.cc_calldata sels fl = sc.cs_current_bb /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  mc <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  fresh_vars_wrt sf s /\ ~s.vs_halted /\
  s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts /\ sf.cs_current_insts = [] ==>
  ?t. vars_pc_only s t /\ fresh_vars_wrt sk t /\
      ~t.vs_halted /\ t.vs_current_bb = sk.cs_current_bb /\
      t.vs_inst_idx = LENGTH sk.cs_current_insts /\
      (s.vs_allocas = FEMPTY ==> alloca_history fn t) /\
      (((!n. mem_safe_run n ctx fn t) /\
        (t.vs_inst_idx = 0 ==> !n. mem_safe_blocks n ctx fn t)) ==>
       !n. mem_safe_blocks n ctx fn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_selector_dispatch_linear_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `fresh_vars_wrt sc t` by gvs[fresh_vars_wrt_def] >>
  `t.vs_call_ctx = s.vs_call_ctx` by metis_tac[vars_pc_only_fields] >>
  drule compile_entry_checks_endpoint >>
  disch_then (qspecl_then [`t`, `fn`, `ctx`] mp_tac) >> simp[] >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  conj_tac >- metis_tac[vars_pc_only_trans] >>
  strip_tac >> irule entry_checks_cursor_alloca_history >>
  simp[] >> conj_tac
  >- metis_tac[actualEntryAllocationFrameTheory.vars_pc_only_allocas] >>
  qexistsl_tac [`mc`, `pay`, `sc`, `sk`] >> simp[]
QED
