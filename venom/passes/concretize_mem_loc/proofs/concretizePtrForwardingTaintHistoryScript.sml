Theory concretizePtrForwardingTaintHistory
Ancestors
  concretizePtrForwardingTaint concretizePtrCoverageStaticMem
  concretizePtrChronologicalHistory concretizePtrChronologicalDemand
  frameAllocationOwnership frameHistoryCfg contextCodegenRel ptrDiscipline
  venomInstProofs1 venomInstProofs venomExecProofs venomWf venomExecSemantics
  venomState venomInst finite_map list rich_list pred_set arithmetic

Theorem ptr_chrono_forward_window_predecessor:
  ptr_chrono_step C a b /\
  EVERY (\f. active_inst f.cf_fn f.cf_inst f.cf_state /\
    f.cf_inst.inst_opcode = INVOKE) a.po_stack /\
  ALL_DISTINCT (fn_labels b.po_fn) /\
  lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\
  i < b.po_state.vs_inst_idx /\ b.po_state.vs_inst_idx <= j ==>
  a.po_fn = b.po_fn /\ a.po_state.vs_current_bb = b.po_state.vs_current_bb /\
  b.po_state.vs_inst_idx = SUC a.po_state.vs_inst_idx /\
  i <= a.po_state.vs_inst_idx /\ a.po_state.vs_inst_idx < j /\
  (a.po_state.vs_inst_idx = i ==> a.po_inst.inst_opcode = RETURNDATACOPY) /\
  (i < a.po_state.vs_inst_idx ==> a.po_inst.inst_opcode = ASSIGN) /\
  ~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
  b.po_taint.t_var = set_var_taint a.po_taint.t_var a.po_inst.inst_outputs
    (out_taint a.po_taint a.po_inst a.po_state)
Proof
  simp[Once ptr_chrono_step_cases] >> strip_tac >> gvs[ptr_observe_def]
  >- (`step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
      `s'.vs_current_bb = s.vs_current_bb` by
        (drule_all step_inst_base_preserves_all >> simp[]) >>
      qpat_x_assum `active_inst fn inst s` mp_tac >>
      simp[active_inst_def] >> disch_then (qx_choose_then `bb0` strip_assume_tac) >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb0` by
        (irule MEM_lookup_block >> fs[fn_labels_def]) >>
      `bb0 = bb` by gvs[] >>
      `get_instruction bb s.vs_inst_idx = SOME inst` by gvs[get_instruction_def] >>
      qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
      simp[revert_forward_pair_def, step_taint_def] >> strip_tac >>
      rpt conj_tac >> rpt strip_tac >> gvs[] >>
      first_x_assum irule >> qexists_tac `s.vs_inst_idx` >> simp[])
  >- (drule_all enters_block_before_revert_window >> decide_tac)
  >- (drule_all enters_block_before_revert_window >> decide_tac) >>
  drule return_binding_current_bb >> strip_tac >>
  qpat_x_assum `active_inst f.cf_fn f.cf_inst f.cf_state` mp_tac >>
  simp[active_inst_def] >> disch_then (qx_choose_then `bb0` strip_assume_tac) >>
  `lookup_block f.cf_state.vs_current_bb f.cf_fn.fn_blocks = SOME bb0` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `bb0 = bb` by gvs[] >>
  `get_instruction bb f.cf_state.vs_inst_idx = SOME f.cf_inst` by
    gvs[get_instruction_def] >>
  qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
  simp[revert_forward_pair_def] >> strip_tac >>
  Cases_on `f.cf_state.vs_inst_idx = i` >- gvs[] >>
  first_x_assum (qspecl_then [`f.cf_state.vs_inst_idx`,`f.cf_inst`] mp_tac) >> simp[]
QED

Theorem ptr_chrono_assign_resolve_taint[local]:
  ptr_chrono_step C a b /\ inst_wf a.po_inst /\
  a.po_inst.inst_opcode = ASSIGN /\
  (!op. op_taint a.po_taint op =
    op_taint tn (resolve_block_assigns xs op)) ==>
  !op. op_taint b.po_taint op =
    op_taint tn (resolve_block_assigns (a.po_inst::xs) op)
Proof
  strip_tac >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  drule_all ptr_chrono_ordinary_step_success >> strip_tac >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases] >> strip_tac >> gvs[ptr_observe_def]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke] >>
    disch_then (mp_tac o MATCH_MP opcodeClassTheory.step_inst_base_intret_opcodes) >>
    simp[]) >>
  `LENGTH inst.inst_outputs = 1 /\ LENGTH inst.inst_operands = 1` by
    gvs[inst_wf_def] >>
  rename1 `!op. op_taint source_taint op = op_taint tn (resolve_block_assigns xs op)` >>
  namedCases_on `inst.inst_outputs` ["", "out rest"] >> gvs[] >>
  namedCases_on `inst.inst_operands` ["", "input inputs"] >> gvs[] >>
  `?value. eval_operand input s = SOME value` by
    (gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >> metis_tac[]) >>
  namedCases_on `op` ["literal", "readvar", "label"] >>
  simp[resolve_block_assigns_def, step_taint_def, op_taint_def] >>
  rpt strip_tac >> Cases_on `readvar = out`
  >- (simp[out_taint_def,set_var_taint_def,FLOOKUP_UPDATE,op_taint_def] >>
      qpat_assum `!op. op_taint source_taint op = _`
        (ACCEPT_TAC o SIMP_RULE (srw_ss()) [op_taint_def] o Q.SPEC `input`)) >>
  simp[set_var_taint_def,FLOOKUP_UPDATE,op_taint_def] >>
  qpat_assum `!op. op_taint source_taint op = _`
    (ACCEPT_TAC o SIMP_RULE (srw_ss()) [op_taint_def] o Q.SPEC `Var readvar`)
QED

Theorem ptr_chrono_forward_window_taint[local]:
  !vs C h a. ptr_chrono_history vs C h a ==>
  EVERY wf_function C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions ==>
  !bb i j.
  lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\
  i < a.po_state.vs_inst_idx /\ a.po_state.vs_inst_idx <= j ==>
  ?opener.
    MEM opener h /\ opener.po_fn = a.po_fn /\
    opener.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    opener.po_state.vs_inst_idx = i /\
    opener.po_inst.inst_opcode = RETURNDATACOPY /\
    !op. op_taint a.po_taint op = op_taint opener.po_taint
      (resolve_block_assigns
        (REVERSE (TAKE (a.po_state.vs_inst_idx - SUC i)
          (DROP (SUC i) bb.bb_instructions))) op)
Proof
  ho_match_mp_tac ptr_chrono_history_strongind >> conj_tac
  >- (rpt strip_tac >> gvs[ptr_observe_def] >>
      drule lookup_function_MEM >> strip_tac >>
      `ALL_DISTINCT (fn_labels fn)` by metis_tac[EVERY_MEM,wf_function_def] >>
      drule_all enters_block_before_revert_window >> decide_tac) >>
  suspend "snoc"
QED

Resume ptr_chrono_forward_window_taint[snoc]:
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `ptr_chrono_step C before after` >>
  qpat_x_assum `EVERY wf_function _ /\ _ ==> _` mp_tac >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  `ptr_observation_reachable vs C before /\
   ptr_observation_reachable vs C after` by
    metis_tac[ptr_chrono_history_reachable,ptr_chrono_step_reachable] >>
  `MEM after.po_fn C.ctx_functions /\ MEM before.po_fn C.ctx_functions /\
   MEM before.po_inst (fn_insts before.po_fn)` by
    (fs[ptr_observation_reachable_def] >>
     metis_tac[frame_reachable_functions_member,ptr_frame_operand_instructions]) >>
  `ALL_DISTINCT (fn_labels after.po_fn) /\ inst_wf before.po_inst` by
    (conj_tac
     >- (qpat_assum `EVERY wf_function C.ctx_functions`
           (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
         disch_then (qspec_then `after.po_fn` mp_tac) >> simp[wf_function_def]) >>
     qpat_assum `EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `before.po_fn` mp_tac) >> simp[EVERY_MEM]) >>
  `EVERY (\f. active_inst f.cf_fn f.cf_inst f.cf_state /\
    f.cf_inst.inst_opcode = INVOKE) before.po_stack` by
    metis_tac[ptr_chrono_history_suspended_invokes] >>
  mp_tac (Q.INST [`a` |-> `before`, `b` |-> `after`]
    ptr_chrono_forward_window_predecessor) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `active_inst before.po_fn before.po_inst before.po_state` by
    (qpat_assum `ptr_chrono_step C before after` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[Once ptr_chrono_step_cases] >> rpt strip_tac >> gvs[ptr_observe_def]) >>
  `get_instruction bb before.po_state.vs_inst_idx = SOME before.po_inst` by
    (qpat_x_assum `active_inst before.po_fn before.po_inst before.po_state` mp_tac >>
     PURE_REWRITE_TAC [active_inst_def] >>
     disch_then (qx_choose_then `preceding_bb` strip_assume_tac) >>
     `lookup_block before.po_state.vs_current_bb before.po_fn.fn_blocks =
        SOME preceding_bb` by
       (irule MEM_lookup_block >> fs[fn_labels_def]) >>
     `preceding_bb = bb` by gvs[] >> gvs[get_instruction_def]) >>
  Cases_on `before.po_state.vs_inst_idx = i`
  >- suspend "copy"
  >> suspend "assign"
QED

Resume ptr_chrono_forward_window_taint[copy]:
  `before.po_inst.inst_opcode = RETURNDATACOPY` by metis_tac[] >>
  `before.po_inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf before.po_inst` mp_tac >> simp[inst_wf_def]) >>
  `MEM before h` by
    (drule ptr_chrono_history_end >> strip_tac >> metis_tac[LAST_MEM]) >>
  qexists_tac `before` >> simp[] >>
  rpt gen_tac >> Cases_on `op` >>
  simp[op_taint_def,set_var_taint_def,resolve_block_assigns_def,FLOOKUP_DRESTRICT]
QED

Resume ptr_chrono_forward_window_taint[assign]:
  `i < before.po_state.vs_inst_idx /\ before.po_state.vs_inst_idx <= j` by decide_tac >>
  qpat_x_assum `!bb i j. _ ==> _` (qspecl_then [`bb`,`i`,`j`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `before.po_inst.inst_opcode = ASSIGN` by metis_tac[] >>
  `REVERSE (TAKE (after.po_state.vs_inst_idx - SUC i)
      (DROP (SUC i) bb.bb_instructions)) =
    before.po_inst :: REVERSE (TAKE (before.po_state.vs_inst_idx - SUC i)
      (DROP (SUC i) bb.bb_instructions))` by
    (qpat_x_assum `get_instruction bb before.po_state.vs_inst_idx = SOME before.po_inst`
       mp_tac >> simp[get_instruction_def] >> strip_tac >>
     `before.po_state.vs_inst_idx - i =
       SUC (before.po_state.vs_inst_idx - SUC i)` by decide_tac >>
     `before.po_state.vs_inst_idx - SUC i < LENGTH (DROP (SUC i) bb.bb_instructions)` by
       simp[LENGTH_DROP] >>
     qpat_assum `before.po_state.vs_inst_idx - i = _`
       (fn th => once_rewrite_tac[th]) >>
     asm_simp_tac bool_ss [TAKE_SUC_BY_TAKE,REVERSE_SNOC] >>
     `before.po_state.vs_inst_idx - SUC i + SUC i =
       before.po_state.vs_inst_idx` by decide_tac >> simp[EL_DROP]) >>
  qexists_tac `opener` >> simp[] >>
  mp_tac (Q.INST [`a` |-> `before`, `b` |-> `after`,
    `tn` |-> `opener.po_taint`,
    `xs` |-> `REVERSE (TAKE (before.po_state.vs_inst_idx - SUC i)
      (DROP (SUC i) bb.bb_instructions))`] ptr_chrono_assign_resolve_taint) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED

Finalise ptr_chrono_forward_window_taint

Theorem ptr_chrono_forward_revert_operands_clean:
  ptr_chrono_history vs C h a /\
  EVERY wf_function C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  (!b op. MEM b h /\ b.po_inst.inst_opcode = RETURNDATACOPY /\
    MEM op b.po_inst.inst_operands ==> op_taint b.po_taint op = {}) /\
  lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\ a.po_state.vs_inst_idx = j ==>
  !op. MEM op a.po_inst.inst_operands ==> op_taint a.po_taint op = {}
Proof
  strip_tac >>
  `i < j` by fs[revert_forward_pair_def] >>
  drule ptr_chrono_forward_window_taint >>
  disch_then (qspecl_then [`bb`,`i`,`j`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `opener` strip_assume_tac) >>
  `MEM a h` by
    (drule ptr_chrono_history_end >> strip_tac >> metis_tac[LAST_MEM]) >>
  `!b. MEM b h ==>
    frame_reachable vs C b.po_stack b.po_params b.po_prov b.po_taint
      b.po_fn b.po_inst b.po_state` by
    (drule ptr_chrono_history_reachable >>
     simp[EVERY_MEM,ptr_observation_reachable_def]) >>
  `frame_reachable vs C opener.po_stack opener.po_params opener.po_prov
      opener.po_taint opener.po_fn opener.po_inst opener.po_state` by metis_tac[] >>
  `MEM a.po_fn C.ctx_functions` by
    metis_tac[frame_reachable_functions_member] >>
  `wf_function a.po_fn` by
    (qpat_assum `EVERY wf_function C.ctx_functions`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
  `!b. MEM b h /\ b.po_fn = a.po_fn /\
      b.po_state.vs_current_bb = a.po_state.vs_current_bb ==>
    get_instruction bb b.po_state.vs_inst_idx = SOME b.po_inst` by
    (rpt strip_tac >>
     `frame_reachable vs C b.po_stack b.po_params b.po_prov b.po_taint
        b.po_fn b.po_inst b.po_state` by metis_tac[] >>
     `active_inst b.po_fn b.po_inst b.po_state` by
       (qpat_x_assum `frame_reachable vs C b.po_stack _ _ _ _ _ _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[Once frame_reachable_cases] >> metis_tac[]) >>
     qpat_x_assum `active_inst b.po_fn b.po_inst b.po_state` mp_tac >>
     PURE_REWRITE_TAC [active_inst_def] >>
     disch_then (qx_choose_then `actual_bb` strip_assume_tac) >>
     `lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME actual_bb` by
       (irule MEM_lookup_block >> fs[wf_function_def,fn_labels_def]) >>
     `actual_bb = bb` by gvs[] >> gvs[get_instruction_def]) >>
  `get_instruction bb i = SOME opener.po_inst /\
   get_instruction bb j = SOME a.po_inst` by
    metis_tac[] >>
  `MEM bb opener.po_fn.fn_blocks /\
   bb.bb_label = opener.po_state.vs_current_bb` by
    metis_tac[lookup_block_MEM,lookup_block_label] >>
  qpat_x_assum `revert_forward_pair bb i j` mp_tac >>
  simp[revert_forward_pair_def] >> strip_tac >>
  `!p q. same_after_assigns (REVERSE (TAKE i bb.bb_instructions)) p q ==>
    op_taint opener.po_taint p = op_taint opener.po_taint q` by
    (rpt strip_tac >> irule ptr_reachable_same_after_assigns_taint >>
     qexistsl [`C`,`opener.po_prov`,`opener.po_params`,`bb`,`opener.po_fn`,
       `opener.po_inst`,`opener.po_state`,`opener.po_stack`,`vs`] >> simp[]) >>
  `!op. MEM op opener.po_inst.inst_operands ==>
      op_taint opener.po_taint op = {}` by metis_tac[] >>
  `op_taint opener.po_taint p = {} /\ op_taint opener.po_taint rds = {}` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  `op_taint a.po_taint p' = {} /\ op_taint a.po_taint rds' = {}` by
    metis_tac[] >> rpt strip_tac >>
  `op = p' \/ op = rds'` by
    (qpat_assum `a.po_inst.inst_operands = [p';rds']` (fn ops =>
       qpat_assum `MEM op a.po_inst.inst_operands`
         (ACCEPT_TAC o SIMP_RULE bool_ss [ops,MEM]))) >> metis_tac[]
QED
