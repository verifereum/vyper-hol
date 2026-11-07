(* Memory footprints of external entry prefixes. *)
Theory entryPrefixMem
Ancestors
  moduleLowering emitHelper compileEnv exprLoweringProps fragExec fragExecMem instMemFrontier venomInst list rich_list
  finite_map words venomExecSemantics venomState moduleLoweringProps
  entryDispatchMem
Libs
  wordsLib

Theorem compile_entry_checks_mem_ok:
  compile_entry_checks min_cds is_payable st = ((), st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  Cases_on `is_payable` >> Cases_on `4 < min_cds` >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem compile_entry_checks_pass_run[local]:
  compile_entry_checks min_cds is_payable st = ((), st') /\
  fresh_vars_wrt st s0 /\
  (is_payable \/ s0.vs_call_ctx.cc_callvalue = 0w) /\
  min_cds <= LENGTH s0.vs_call_ctx.cc_calldata /\
  LENGTH s0.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s0 = OK t /\
      vars_pc_only s0 t /\ fresh_vars_wrt st' t /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0)
Proof
  strip_tac >>
  `min_cds < dimword (:256)` by decide_tac >>
  Cases_on `is_payable` >> Cases_on `4 < min_cds` >>
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
       bool_to_word_def] >>
  simp[vars_pc_only_def] >>
  (conj_tac
   >- (fs[fresh_vars_wrt_def] >> rpt strip_tac >> fs[]) >>
   rw[FLOOKUP_UPDATE] >> gvs[not_fresh_at_def])
QED

Theorem compile_entry_checks_structure[local]:
  compile_entry_checks min_cds is_payable st = ((), st') ==>
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  Cases_on `is_payable` >> Cases_on `4 < min_cds` >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[IS_PREFIX_APPEND, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem compile_entry_checks_pass_mem:
  !min_cds is_payable st st' ctx s0.
    compile_entry_checks min_cds is_payable st = ((), st') /\
    fresh_vars_wrt st s0 /\
    (is_payable \/ s0.vs_call_ctx.cc_callvalue = 0w) /\
    min_cds <= LENGTH s0.vs_call_ctx.cc_calldata /\
    LENGTH s0.vs_call_ctx.cc_calldata < dimword (:256) ==>
    frag_exec_mem ctx st st' (\s. s = s0)
      (\t. vars_pc_only s0 t /\ fresh_vars_wrt st' t /\
           (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0))
      (\r. F)
Proof
  rpt strip_tac >>
  drule compile_entry_checks_structure >> strip_tac >>
  (irule frag_exec_mem_run_inst_seq >> simp[] >>
   conj_tac >- metis_tac[compile_entry_checks_mem_ok] >>
   drule compile_entry_checks_pass_run >>
   disch_then (qspec_then `s0` mp_tac) >> simp[] >> strip_tac >>
   qexists_tac `t` >>
   simp[vars_pc_only_inst_idx, control_moves_keep_vars] >>
   gvs[fresh_vars_wrt_def])
QED

Theorem compile_entry_checks_pass_mem_safe_run:
  compile_entry_checks mc pay sc = ((),sk) /\
  fn_has_code sc sk fn /\ fresh_vars_wrt sc s /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  mc <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!t. vars_pc_only s t /\ fresh_vars_wrt sk t /\
       (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s) /\
       ~t.vs_halted /\ t.vs_current_bb = sk.cs_current_bb /\
       t.vs_inst_idx = LENGTH sk.cs_current_insts ==>
       !n. mem_safe_run n ctx fn t) ==>
  !n. mem_safe_run n ctx fn s
Proof
  strip_tac >> (
  drule compile_entry_checks_structure >> strip_tac >>
  drule compile_entry_checks_pass_run >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
  `?bb. lookup_block sc.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX sk.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `?is. sk.cs_current_insts = sc.cs_current_insts ++ is /\
        emitted_insts sc sk = is` by
    (qpat_x_assum `isPREFIX sc.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX sk.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (qspecl_then [`is`, `s`, `0`, `ctx`, `bb`] mp_tac
       exec_block_run_inst_seq >> fs[] >> metis_tac[]) >>
  drule vars_pc_only_fields >> strip_tac >>
  `!n. mem_safe_run n ctx fn
        (t with vs_inst_idx := LENGTH sk.cs_current_insts)` by
    (first_x_assum irule >>
     fs[vars_pc_only_inst_idx, fresh_vars_wrt_def,
        control_moves_keep_vars]) >>
  gen_tac >>
  qspecl_then [`is`, `s`, `n`, `ctx`, `fn`, `bb`] mp_tac
    mem_safe_run_inst_seq >>
  simp[] >> impl_tac
  >- metis_tac[compile_entry_checks_mem_ok] >>
  strip_tac >>
  first_x_assum (qspec_then `t` mp_tac) >> gvs[arithmeticTheory.ADD_COMM])
QED

Theorem entry_checks_nonempty_no_phi[local]:
  compile_entry_checks mc pay sc = ((),sk) /\
  ~(pay /\ mc <= 4) /\ sc.cs_current_insts = [] /\
  fn_has_code sc sk fn ==>
  ?bb. lookup_block sc.cs_current_bb fn.fn_blocks = SOME bb /\
       (!s. eval_phis s bb.bb_instructions = OK s) /\
       phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `pay` >> Cases_on `4 < mc` >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[eval_phis_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem compile_entry_checks_pass_mem_safe_blocks:
  compile_entry_checks mc pay sc = ((),sk) /\
  fn_has_code sc sk fn /\ fresh_vars_wrt sc s /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  mc <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  sc.cs_current_insts = [] /\
  (pay /\ mc <= 4 ==> !n. mem_safe_blocks n ctx fn s) /\
  (!t. vars_pc_only s t /\ fresh_vars_wrt sk t /\
       (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s) /\
       ~t.vs_halted /\ t.vs_current_bb = sk.cs_current_bb /\
       t.vs_inst_idx = LENGTH sk.cs_current_insts ==>
       !n. mem_safe_run n ctx fn t) ==>
  !n. mem_safe_blocks n ctx fn s
Proof
  strip_tac >> (
  Cases_on `pay /\ mc <= 4` >- metis_tac[] >>
  drule_all entry_checks_nonempty_no_phi >> strip_tac >>
  `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
  irule mem_safe_blocks_no_phi >> simp[] >>
  irule compile_entry_checks_pass_mem_safe_run >>
  simp[] >> qexistsl_tac [`mc`, `pay`, `sc`, `sk`] >> simp[])
QED
