Theory concretizeLayoutCanonicalBaseTerminalExit
Ancestors concretizeLayoutCutSafe concretizeLayoutCanonicalBase concretizeLayoutCanonicalDriver
  concretizeLayoutSelectedBaseInterface concretizeLayoutCompletedJump
  concretizeStepStructure frameFiniteJointDecoration
  concretizeLayoutLocalTerminals concretizeLayoutPhaseOrigin
  frameRelocationLocal frameRelocationEnvironment
  concretizeLayoutPhaseHalt concretizeLayoutPhaseReturn
  concretizeLayoutPhaseSelfdestruct concretizeLayoutLocalSelfdestruct
  ptrDiscipline venomExecSemantics venomInst list
  frameResolvedTrace frameRelocationReachableSupport frameRelocationValues
  frameRelocationCleanOperands pointerConfinedDefs memLocDefs

Theorem layout_ordinary_revert_empty:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  ptr_static_support P fn G /\
  resolved_frame_ok birth cache PG G om rp rv ids frames /\
  taint_ok fn tn inst s /\ inst.inst_opcode = REVERT /\
  s.vs_labels = t.vs_labels /\ variable_domains s t /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t /\
  step_inst_base inst s = Abort Revert_abort post /\
  post.vs_returndata = [] ==>
  ?post'. step_inst_base inst t = Abort Revert_abort post' /\
    post'.vs_returndata = []
Proof
  strip_tac >>
  `!v. FLOOKUP rv v <> NONE ==> v IN fn_pv P fn` by
    (drule resolved_frame_erasure >> strip_tac >>
     metis_tac[resolved_static_support]) >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `!op. eval_operand op s = NONE <=> eval_operand op t = NONE` by
    (gen_tac >> irule operand_domain_agreement >> simp[]) >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `!v. sz_op = Var v ==> FLOOKUP rv v = NONE` by
    (rpt strip_tac >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_read_ops_def, mem_write_ops_def] >>
     disch_then (qspec_then `v` mp_tac) >>
     Cases_on `off_op = Var v` >> gvs[] >> metis_tac[]) >>
  `eval_operand sz_op s = eval_operand sz_op t` by
    (`MEM sz_op inst.inst_operands` by simp[] >>
     `~MEM inst.inst_opcode
       [ASSIGN; PHI; RET; MUL; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE]`
       by simp[] >>
     drule_all disciplined_scalar_operand >> simp[]) >>
  fs[venomStateTheory.revert_state_def, venomStateTheory.set_returndata_def] >>
  (Cases_on `eval_operand off_op t`
   >- metis_tac[optionTheory.NOT_NONE_SOME] >> gvs[] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   simp[venomStateTheory.revert_state_def, venomStateTheory.set_returndata_def])
QED

Theorem layout_canonical_ordinary_revert_empty:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\ decoration_at fn i s q /\
  i.inst_opcode = REVERT /\ step_inst_base i s = Abort Revert_abort post /\
  post.vs_returndata = [] /\ step_inst fuel C' j t = Abort Revert_abort post' ==>
  post'.vs_returndata = []
Proof
  strip_tac >> drule_all layout_canonical_ordinary_environment >>
  strip_tac >> gvs[concretize_positions_unchanged] >>
  `layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `resolved_config_ok (JointConfig stk PG G tn fn i s oms om hs h)
     (birth::ids) ((rp,rv)::anns)` by
    (fs[layout_ordinary_trace_def] >> metis_tac[]) >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >>
  `variable_domains s t /\ s.vs_labels = t.vs_labels` by
    fs[local_rel_def, relocation_env_def] >>
  drule_all concretizePtrParamSupportTheory.ptr_frame_current_static >> strip_tac >>
  fs[resolved_config_ok_def] >>
  drule_all layout_ordinary_revert_empty >> gvs[step_inst_non_invoke]
QED

Theorem terminal_exit_cases[local]:
  is_terminator i.inst_opcode /\ i.inst_opcode <> DRET /\
  i.inst_opcode <> RETFMP /\ step_inst_base i s = r /\
  (!p. r <> OK p) /\ (!e. r <> Error e) ==>
  (?post. r = Halt post /\ MEM i.inst_opcode [STOP; SINK; RETURN; SELFDESTRUCT]) \/
  (?a post. r = Abort a post /\ MEM i.inst_opcode [INVALID; REVERT; SELFDESTRUCT]) \/
  (?ret post. r = IntRet ret post /\ i.inst_opcode = RET)
Proof
  Cases_on `i.inst_opcode` >> simp[is_terminator_def] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Leaf of the exhaustive base certificate: a terminator that halts, aborts
   or returns (STOP, RETURN, SINK, REVERT, INVALID, SELFDESTRUCT, RET). *)

Theorem layout_canonical_terminal_exit:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\
  layout_cut_safe D lo ncut vs0 C qend /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  i.inst_opcode <> INVOKE /\
  is_terminator i.inst_opcode /\
  step_inst_base i s = r /\ (!p. r <> OK p) /\ (!e. r <> Error e) ==>
  ?r'. step_inst_base j t = r' /\
    layout_canonical_result D lo vs0 C C' q0 es qs ass qend q n r r'
Proof
  strip_tac >> drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `gas_cut ncut vs0 s /\ ptr_discipline_upto lo ncut C vs0` by
    (drule_all layout_ordinary_entry_cut >> simp[]) >>
  `i.inst_opcode <> ALLOCA` by
    (strip_tac >> fs[is_terminator_def]) >>
  `j = i` by gvs[concretize_positions_unchanged] >>
  gvs[is_terminator_def] >>
  `i.inst_opcode <> DRET /\ i.inst_opcode <> RETFMP` by
    metis_tac[fn_ptr_ok_def] >>
  `active_inst fn i s` by fs[decoration_at_def] >>
  mp_tac (Q.INST [`r` |-> `step_inst_base i s`] terminal_exit_cases) >>
  (impl_tac >- simp[]) >> strip_tac
  >- suspend "halt"
  >- suspend "abort"
  >> suspend "ret"
QED

Resume layout_canonical_terminal_exit[halt]:
  `step_inst 0 C i s = Halt post` by simp[step_inst_non_invoke] >>
  `?tpost. step_inst_base i t = Halt tpost /\
    dead_result_rel D (Halt post) (Halt tpost)` by
    (Cases_on `i.inst_opcode = RETURN`
     >- (drule_all (Q.INST [`fuel` |-> `0`, `fuel'` |-> `0`]
           layout_return_halt) >> simp[step_inst_non_invoke]) >>
     Cases_on `i.inst_opcode = SELFDESTRUCT`
     >- (drule_all layout_selfdestruct_halt >> simp[]) >>
     `MEM i.inst_opcode [STOP; SINK]` by fs[] >>
     drule_all (Q.INST [`fuel` |-> `0`, `fuel'` |-> `0`]
       layout_stop_sink_halt) >> simp[step_inst_non_invoke]) >>
  simp[layout_canonical_result_def]
QED

Resume layout_canonical_terminal_exit[abort]:
  `?tpost. step_inst_base i t = Abort a tpost /\
    dead_result_rel D (Abort a post) (Abort a tpost)` by
    (Cases_on `i.inst_opcode = INVALID`
     >- (drule_all concretize_invalid_complete >> simp[]) >>
     `layout_ordinary_state D lo C' q0 (MAP FST path) (MAP SND path) g s t` by
       fs[layout_ordinary_entry_def] >>
     `resolved_config_ok (JointConfig stk PG G tn fn i s oms om hs h)
        (birth::ids) ((rp,rv)::anns)` by
       (fs[layout_ordinary_trace_def] >> metis_tac[]) >>
     qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >>
     Cases_on `i.inst_opcode = REVERT`
     >- (`variable_domains s t /\ s.vs_labels = t.vs_labels` by
           fs[local_rel_def, relocation_env_def] >>
         drule_all concretize_revert_complete >> simp[]) >>
     `i.inst_opcode = SELFDESTRUCT` by fs[] >>
     drule_all concretize_selfdestruct_abort_complete >> simp[]) >>
  simp[layout_canonical_result_def]
QED

Resume layout_canonical_terminal_exit[ret]:
  `step_inst 0 C i s = IntRet ret post` by simp[step_inst_non_invoke] >>
  drule_all (Q.INST [`fuel` |-> `0`, `fuel'` |-> `0`]
    concretizeLayoutCallResultTheory.layout_ret_endpoint_produce) >>
  strip_tac >> gvs[step_inst_non_invoke] >>
  irule layout_canonical_ret_intro >> simp[] >>
  qexists `g` >> simp[]
QED

Finalise layout_canonical_terminal_exit
