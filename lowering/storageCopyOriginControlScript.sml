(* Joint control and scalar segments for the counted storage copy. *)
Theory storageCopyOriginControl
Ancestors
  storageCopyControlRaisePtr fragGasSeqPtr fragGasOriginPtr fragGasOrigin
  ptrSafetyTransport fragExecMem memSafeRun gasEvents fragGasPathPtr ptrSafeRun
  ptrDiscipline gasCount venomInst venomState venomExecSemantics
  venomExecProofs venomInstProofs exprLoweringProps codegenRel contextCodegenRel
  instMemFrontier

Theorem storage_copy_control_origin_ptr[local]:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  ptr_inst_ok D lo 0 ctx func G tn inst s /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to lbl s),G,tn)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
   is_terminator inst.inst_opcode` by gvs[is_terminator_def] >>
  `inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    (conj_tac >- (irule below_frontier_no_ranges >> gvs[]) >>
     gvs[inst_dload_in_section_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to lbl s),G,tn)` by
    (simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
     conj_tac >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_events_step_def, gas_count_step_def,
          mem_safe_step_non_invoke, ptr_safe_step_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  simp[gas_origin_ptr_path_rules]
QED

Theorem storage_copy_jump_origin_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to lbl s),G,tn)
Proof
  strip_tac >> irule storage_copy_control_origin_ptr >> simp[] >>
  simp[mk_inst_def, step_inst_base_def, ptr_inst_ok_def, access_ok_def,
       taint_ok_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_taint_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  simp[mk_inst_def, step_jmp_behavior, jump_to_def]
QED

Theorem storage_copy_branch_origin_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JNZ [op;Label lt;Label lf] []) /\
  eval_operand op s = SOME (if test then 1w else 0w) /\ op_taint tn op = {} ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to (if test then lt else lf) s),G,tn)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id JNZ [op;Label lt;Label lf] []) s =
     OK (jump_to (if test then lt else lf) s)` by
    (drule step_jnz_behavior >>
     disch_then (qspecl_then [`lt`, `lf`, `id`] mp_tac) >>
     Cases_on `test` >> simp[mk_inst_def]) >>
  irule storage_copy_control_origin_ptr >> simp[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_taint_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  simp[mk_inst_def, step_jnz_behavior, jump_to_def] >>
  Cases_on `test` >> gvs[op_taint_def] >>
  gen_tac >> Cases_on `op' = op` >> gvs[] >>
  Cases_on `op' = Label lt` >> gvs[] >>
  Cases_on `op' = Label lf` >> gvs[]
QED

Theorem storage_copy_scalar_origin_ptr[local]:
  (opc = ASSIGN /\ (?v. ops = [Lit v]) \/
   opc = EQ /\ (?v k. ops = [Var v;Lit k])) /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u /\
  u.vs_requests = s.vs_requests /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     DRESTRICT G (COMPL {out}),tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (irule storage_copy_scalar_check >> simp[] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists_tac `0` >> gvs[]) >>
  `step_prov PG G (mk_inst id opc ops [out]) u = DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc ops [out]) s u tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule storage_copy_scalar_ghost >> simp[] >> metis_tac[]) >>
  `inst_mem_below_frontier (mk_inst id opc ops [out]) s /\
   inst_dload_in_section (mk_inst id opc ops [out]) s` by
    (gvs[inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     DRESTRICT G (COMPL {out}),tn with t_var := tn.t_var |+ (out,{}))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_origin_ptr_edge >>
     gvs[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `step_inst 0 ctx (mk_inst id opc ops [out]) s = OK u` by
    gvs[step_inst_non_invoke, mk_inst_def] >>
  `~u.vs_halted` by
    (drule step_preserves_halted >> gvs[mk_inst_def, is_terminator_def]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >> simp[gas_origin_ptr_path_rules]
QED

Theorem storage_copy_init_origin_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit 0w] [cv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst jid JMP [Label hdr] []) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (jump_to hdr (update_var cv 0w s with vs_inst_idx := SUC s.vs_inst_idx)),
     DRESTRICT G (COMPL {cv}),tn with t_var := tn.t_var |+ (cv,{}))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSIGN [Lit 0w] [cv]) s = OK (update_var cv 0w s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def, eval_operand_def] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (update_var cv 0w s with vs_inst_idx := SUC s.vs_inst_idx),
     DRESTRICT G (COMPL {cv}),tn with t_var := tn.t_var |+ (cv,{}))` by
    (irule storage_copy_scalar_origin_ptr >> simp[update_var_def] >>
     qexistsl_tac [`id`,`ASSIGN`,`[Lit 0w]`] >> simp[op_taint_def] >>
     gvs[update_var_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (update_var cv 0w s with vs_inst_idx := SUC s.vs_inst_idx,
     DRESTRICT G (COMPL {cv}),tn with t_var := tn.t_var |+ (cv,{})) []
    (OK (jump_to hdr (update_var cv 0w s with vs_inst_idx := SUC s.vs_inst_idx)),
     DRESTRICT G (COMPL {cv}),tn with t_var := tn.t_var |+ (cv,{}))` by
    (irule storage_copy_jump_origin_ptr >> simp[update_var_def] >>
     conj_tac >- (qexists_tac `jid` >> simp[]) >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  rev_drule gas_origin_ptr_path_append >> simp[] >> disch_then drule >> simp[]
QED

Theorem storage_copy_header_origin_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [Var cv;Lit (n2w n)] [test]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst jid JNZ [Var test;Label exit;Label body_lbl] []) /\
  lookup_var cv s = SOME (n2w k) /\ k <= n /\ n < dimword(:256) /\
  op_taint tn (Var cv) = {} ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (jump_to (if k = n then exit else body_lbl)
       (update_var test (bool_to_word (k = n)) s with vs_inst_idx := SUC s.vs_inst_idx)),
     DRESTRICT G (COMPL {test}),tn with t_var := tn.t_var |+ (test,{}))
Proof
  strip_tac >> drule_all storage_copy_counter_steps >> strip_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (update_var test (bool_to_word (k = n)) s with vs_inst_idx := SUC s.vs_inst_idx),
     DRESTRICT G (COMPL {test}),tn with t_var := tn.t_var |+ (test,{}))` by
    (irule storage_copy_scalar_origin_ptr >> simp[update_var_def] >>
     qexistsl_tac [`id`,`EQ`,`[Var cv;Lit (n2w n)]`] >>
     simp[op_taint_def, DISJ_IMP_THM, FORALL_AND_THM] >>
     gvs[op_taint_def, update_var_def] >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (update_var test (bool_to_word (k = n)) s with vs_inst_idx := SUC s.vs_inst_idx,
     DRESTRICT G (COMPL {test}),tn with t_var := tn.t_var |+ (test,{})) []
    (OK (jump_to (if k = n then exit else body_lbl)
       (update_var test (bool_to_word (k = n)) s with vs_inst_idx := SUC s.vs_inst_idx)),
     DRESTRICT G (COMPL {test}),tn with t_var := tn.t_var |+ (test,{}))` by
    (irule storage_copy_branch_origin_ptr >>
     simp[update_var_def, allocas_from_def, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, op_taint_def, bool_to_word_def] >>
     reverse conj_tac >- (gvs[allocas_from_def] >> metis_tac[]) >>
     qexistsl_tac [`jid`,`Var test`] >>
     simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `k = n` >> simp[bool_to_word_def]) >>
  rev_drule gas_origin_ptr_path_append >> simp[] >> disch_then drule >> simp[]
QED
