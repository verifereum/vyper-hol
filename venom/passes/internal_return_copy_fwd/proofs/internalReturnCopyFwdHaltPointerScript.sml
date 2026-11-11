Theory internalReturnCopyFwdHaltPointer
Ancestors
  internalReturnCopyFwdHaltProbe ptrDiscipline pointerConfinedDefs
  venomExecSemantics venomState venomInst finite_map words list memLocDefs unitShapeDefs venomWf relation contextCodegenRel codegenRel

Theorem ircf_halt_pointer_roots:
  ptr_roots (\nm. {}) ircf_halt_probe_fn = {"%p"}
Proof
  simp[ptr_roots_def, alloca_roots_def, ircf_halt_probe_fn_def,
    ircf_halt_probe_bb_def, mk_raw_function_def, fn_insts_def,
    mk_inst_def, fn_insts_blocks_def, EXISTS_OR_THM, inst_output_def] >>
  simp[venomInstTheory.EXISTS_instruction]
QED

Theorem ircf_halt_pointer_pv:
  fn_pv (\nm. {}) ircf_halt_probe_fn = {"%p"}
Proof
  simp[fn_pv_def, ircf_halt_pointer_roots, pointer_derived_vars_def] >>
  EVAL_TAC >> pure_once_rewrite_tac[WhileTheory.OWHILE_THM] >>
  simp[] >> pure_once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[]
QED

Theorem ircf_halt_pointer_fn_ok:
  fn_ptr_ok (\nm. {}) ircf_halt_probe_fn
Proof
  simp[fn_ptr_ok_def, ircf_halt_pointer_roots, ircf_halt_pointer_pv] >>
  simp[ircf_halt_probe_fn_def, ircf_halt_probe_bb_def, mk_raw_function_def,
    fn_insts_def, fn_insts_blocks_def, mk_inst_def] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, ptr_use_ok_def,
    affine_pointer_ops_def, phi_pv_all_var_def, is_pointer_preserving_op_def,
    fn_insts_def, fn_insts_blocks_def,
    mem_write_ops_def, mem_read_ops_def, inst_output_def] >>
  rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem ircf_halt_pointer_reachable_fn:
  reachable_fn ircf_halt_probe_fn = ircf_halt_probe_fn
Proof
  `fn_cfg_edge ircf_halt_probe_fn "main" "sink"` by
    (simp[fn_cfg_edge_def] >> qexists_tac `ircf_halt_probe_bb` >> EVAL_TAC) >>
  `RTC (fn_cfg_edge ircf_halt_probe_fn) "main" "sink"` by
    metis_tac[RTC_SINGLE] >>
  `fn_entry_label ircf_halt_probe_fn = SOME "main"` by EVAL_TAC >>
  `fn_reachable ircf_halt_probe_fn "main" /\
   fn_reachable ircf_halt_probe_fn "sink"` by
    simp[fn_reachable_def, RTC_REFL] >>
  simp[reachable_fn_def, ircf_halt_probe_fn_def, ircf_halt_probe_bb_def,
    mk_raw_function_def] >>
  fs[ircf_halt_probe_fn_def, ircf_halt_probe_bb_def, mk_raw_function_def] >>
  simp[reachable_inst_def, mk_inst_def]
QED

(* Only the fields needed for pointer safety are tracked.  The loaded
   value and the storage taint are intentionally unrestricted. *)
Definition ircf_halt_pointer_inv_def:
  ircf_halt_pointer_inv stk PG G tn fn s <=>
    stk = [] /\ PG = [] /\ fn = ircf_halt_probe_fn /\
    s.vs_halted /\ s.vs_current_bb = "main" /\ s.vs_inst_idx < 4 /\
    op_taint tn (Var "%p") = {} /\
    (s.vs_inst_idx = 0 ==> s.vs_alloca_next = 0 /\ s.vs_allocas = FEMPTY) /\
    (0 < s.vs_inst_idx ==> lookup_var "%p" s = SOME 0w /\
                              FLOOKUP G "%p" = SOME (0:num,32:num))
End

Theorem ircf_halt_pointer_entry:
  ircf_halt_probe_ctx.ctx_entry = SOME name /\
  lookup_function name ircf_halt_probe_ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn ((ircf_halt_probe_state q b) with
    <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s /\
  active_inst fn inst s ==>
  ircf_halt_pointer_inv [] [] FEMPTY entry_taint fn s
Proof
  simp[ircf_halt_probe_ctx_def, ircf_halt_probe_fn_def,
       mk_raw_function_def, lookup_function_def, FIND_thm] >> strip_tac >> gvs[] >>
  fs[fn_entry_label_def, entry_block_def, ircf_halt_probe_bb_def] >>
  fs[enters_block_def, lookup_block_def, FIND_thm, ircf_halt_probe_bb_def,
     eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  gvs[ircf_halt_pointer_inv_def, ircf_halt_probe_fn_def, mk_raw_function_def,
      ircf_halt_probe_state_def, entry_taint_def, op_taint_def,
      ircf_halt_probe_bb_def, mk_inst_def, eval_phis_def,
      phi_prefix_length_def]
QED

Theorem ircf_halt_pointer_active:
  s.vs_current_bb = "main" /\ s.vs_inst_idx < 4 /\
  active_inst ircf_halt_probe_fn inst s ==>
  (s.vs_inst_idx = 0 /\ inst = mk_inst 1 ALLOCA [Lit 32w] ["%p"]) \/
  (s.vs_inst_idx = 1 /\ inst = mk_inst 2 MLOAD [Var "%p"] ["%v"]) \/
  (s.vs_inst_idx = 2 /\ inst = mk_inst 3 SSTORE [Lit 0w; Var "%v"] []) \/
  (s.vs_inst_idx = 3 /\ inst = mk_inst 4 JMP [Label "sink"] [])
Proof
  strip_tac >>
  `s.vs_inst_idx = 0 \/ s.vs_inst_idx = 1 \/
   s.vs_inst_idx = 2 \/ s.vs_inst_idx = 3` by decide_tac >>
  gvs[active_inst_def, ircf_halt_probe_fn_def, mk_raw_function_def,
      ircf_halt_probe_bb_def] >> gvs[]
QED

Theorem ircf_halt_pointer_next:
  ircf_halt_pointer_inv stk PG G tn fn s /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ircf_halt_probe_ctx inst s = OK s' ==>
  ircf_halt_pointer_inv stk PG (step_prov PG G inst s')
    (step_taint inst s s' tn) fn (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  gvs[ircf_halt_pointer_inv_def] >>
  drule_all ircf_halt_pointer_active >> strip_tac >> gvs[] >>
  fs[mk_inst_def, is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_opcode_eqs] >>
  gvs[exec_alloca_def, exec_read1_def, exec_write2_def,
      eval_operands_def, eval_operand_def, AllCaseEqs(), update_var_def,
      sstore_def, lookup_var_def, step_prov_def, set_prov_def, out_prov_def,
      step_taint_def, op_taint_def, set_var_taint_def, out_taint_def] >>
  strip_tac >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, wordsTheory.dimword_def]
QED

Theorem ircf_halt_pointer_reach:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    !q b. vs = ircf_halt_probe_state q b /\ C = ircf_halt_probe_ctx ==>
    ircf_halt_pointer_inv stk PG G tn fn s
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> irule ircf_halt_pointer_entry >>
      metis_tac[])
  >- (rpt strip_tac >> gvs[] >> irule ircf_halt_pointer_next >>
      metis_tac[])
  >- (rpt strip_tac >> gvs[] >>
      `ircf_halt_pointer_inv stk PG G tn fn s` by metis_tac[] >>
      gvs[ircf_halt_pointer_inv_def] >>
      drule_all ircf_halt_pointer_active >> strip_tac >> gvs[] >>
      fs[mk_inst_def, is_terminator_def] >>
      gvs[Once step_inst_def, step_inst_base_opcode_eqs, jump_to_def])
  >- (rpt strip_tac >> gvs[] >>
      `ircf_halt_pointer_inv stk PG G tn fn s` by metis_tac[] >>
      gvs[ircf_halt_pointer_inv_def] >>
      drule_all ircf_halt_pointer_active >> strip_tac >> gvs[mk_inst_def])
  >> rpt strip_tac >> gvs[] >>
  `ircf_halt_pointer_inv (f::stk) PG G tn fn s` by metis_tac[] >>
  gvs[ircf_halt_pointer_inv_def]
QED

Theorem ircf_halt_pointer_safe:
  ircf_halt_pointer_inv stk PG G tn fn s /\ active_inst fn inst s ==>
  access_ok 0 G fn inst s /\ taint_ok fn tn inst s /\
  allocas_from 0 s /\
  (ctx_has_dalloca ircf_halt_probe_ctx ==> allocas_below_fmp s)
Proof
  strip_tac >> gvs[ircf_halt_pointer_inv_def] >>
  drule_all ircf_halt_pointer_active >> strip_tac >> gvs[] >>
  simp[access_ok_def, taint_ok_def, allocas_from_def,
       ctx_has_dalloca_def, ircf_halt_probe_ctx_def,
       ircf_halt_probe_fn_def, ircf_halt_probe_bb_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       mem_write_ops_def, mem_read_ops_def, op_taint_def,
       eval_operand_def, eval_operands_def] >>
  rpt strip_tac >> gvs[op_taint_def]
QED

Theorem ircf_halt_pointer_discipline:
  !q. ptr_discipline 0 ircf_halt_probe_ctx
    (ircf_halt_probe_state q (0w:word8))
Proof
  gen_tac >> simp[ptr_discipline_def, ircf_halt_probe_state_def] >>
  qexists_tac `\nm. {}` >>
  conj_tac
  >- simp[ircf_halt_probe_ctx_def, ircf_halt_pointer_fn_ok,
          ircf_halt_pointer_reachable_fn] >>
  rpt gen_tac >> strip_tac >>
  drule ircf_halt_pointer_reach >>
  disch_then (qspecl_then [`q`, `(0w:word8)`] mp_tac) >>
  simp[ircf_halt_probe_state_def] >> strip_tac >>
  drule o1ContractSimplifyCfgSrcFrameTheory.scfg_frame_reachable_active >>
  metis_tac[ircf_halt_pointer_safe]
QED
