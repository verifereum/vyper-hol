(* Correlated internal-call setup support; no independent target setup choice. *)
Theory lowerDloadReturnInvokePush
Ancestors
  lowerDloadReturnInvokeArguments lowerDloadReturnInvokeStack lowerDloadSafetyArguments
  lowerDloadSafetyEntry lowerDloadReturnStable lowerDloadReturnAlignment
  venomExecSemantics venomState venomInst finite_map list pred_set
  ptrDiscipline contextCodegenRel o1ContractLowerDload venomExecProofs
  lowerDloadLiveAllocation
Libs
  lowerDloadReturnPackageLib

Theorem ld_setup_pair_effect:
  setup_callee callee argsS s = SOME cs /\
  setup_callee calleeT argsT t = SOME ct /\
  ld_memory lo A tn s t /\ ld_nonghost tn s t ==>
  ld_memory lo A (tn with t_var := FEMPTY) cs ct /\
  ld_nonghost (tn with t_var := FEMPTY) cs ct
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[lowerDloadSafetyKernelTheory.ld_memory_def,
      lowerDloadSafetyKernelTheory.ld_nonghost_def] >>
  first_assum ACCEPT_TAC
QED

Theorem ld_setup_pair_vars:
  setup_callee callee argsS s = SOME cs /\
  setup_callee calleeT argsT t = SOME ct /\
  LENGTH argsS = LENGTH argsT /\ LENGTH Q = LENGTH argsS /\
  (!j. j < LENGTH argsS ==>
    ld_wordrel A (EL j Q) (EL j argsS) (EL j argsT)) ==>
  ld_vars P A <|lf_serial := N; lf_supply := u; lf_fn := callee;
    lf_src := cs; lf_tgt := ct; lf_H := FEMPTY; lf_Q := Q;
    lf_E := {}; lf_tv := FEMPTY|>
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[ld_vars_def]
QED

Theorem ld_setup_source_exists:
  fn_labels callee = fn_labels calleeT /\
  setup_callee calleeT argsT t = SOME ct ==>
  ?cs. setup_callee callee argsS s = SOME cs /\
    cs.vs_current_bb = ct.vs_current_bb /\
    cs.vs_prev_bb = ct.vs_prev_bb
Proof
  simp[setup_callee_def, AllCaseEqs()] >> strip_tac >>
  `~NULL callee.fn_blocks /\
   (HD callee.fn_blocks).bb_label = (HD calleeT.fn_blocks).bb_label` by
    (Cases_on `callee.fn_blocks` >> Cases_on `calleeT.fn_blocks` >>
     gvs[fn_labels_def]) >>
  gvs[]
QED

Theorem ld_invoke_callee_ambient:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME calleeT ==>
  ?callee. lookup_function nm C.ctx_functions = SOME callee /\
    callee.fn_name = nm /\
    calleeT = FST (lower_dload_function_supply (Sigma nm) callee) /\
    ^ld_covered_ambient lo C C' vs0 Sigma names callee calleeT
Proof
  simp[] >> strip_tac >>
  `fn_invoke_ok (ctx_fn_names C) fn` by
    (gvs[o1PassContractTheory.o1_ctx_shape_def, EVERY_MEM,
         o1PassContractTheory.o1_fn_shape_def] >> metis_tac[]) >>
  `MEM nm (ctx_fn_names C)` by
    (qpat_x_assum `fn_invoke_ok _ _` mp_tac >>
     simp[o1PassContractTheory.fn_invoke_ok_def] >>
     disch_then (qspec_then `inst` mp_tac) >>
     gvs[decode_invoke_def, AllCaseEqs()]) >>
  `?callee. lookup_function nm C.ctx_functions = SOME callee` by
    (Cases_on `lookup_function nm C.ctx_functions` >> simp[] >>
     drule lookup_function_not_mem >> gvs[ctx_fn_names_def]) >>
  `MEM callee C.ctx_functions /\ callee.fn_name = nm` by
    (conj_tac >- metis_tac[lookup_function_MEM] >>
     qpat_x_assum `lookup_function nm C.ctx_functions = SOME callee` mp_tac >>
     simp[lookup_function_def] >>
     disch_then (mp_tac o MATCH_MP venomExecProofsTheory.FIND_P) >> simp[]) >>
  `calleeT = FST (lower_dload_function_supply (Sigma nm) callee)` by
    metis_tac[optionTheory.SOME_11] >>
  qexists_tac `callee` >> simp[]
QED

Theorem ld_invoke_correlated_setup:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME calleeT /\
  eval_operands ops t = SOME argsT /\
  setup_callee calleeT argsT t = SOME ct ==>
  ?callee argsS cs.
    lookup_function nm C.ctx_functions = SOME callee /\ callee.fn_name = nm /\
    eval_operands ops s = SOME argsS /\ setup_callee callee argsS s = SOME cs /\
    ^ld_covered_ambient lo C C' vs0 Sigma names callee calleeT /\
    cs.vs_current_bb = ct.vs_current_bb /\ cs.vs_prev_bb = ct.vs_prev_bb /\
    ld_memory lo A (tn with t_var := FEMPTY) cs ct /\
    ld_nonghost (tn with t_var := FEMPTY) cs ct /\
    ld_vars P A <|lf_serial := N; lf_supply := Sigma nm; lf_fn := callee;
      lf_src := cs; lf_tgt := ct; lf_H := FEMPTY;
      lf_Q := MAP (op_prov f.lf_H) ops; lf_E := {}; lf_tv := FEMPTY|> /\
    (!a. MEM (SOME a) (MAP (op_prov f.lf_H) ops) ==> a IN FDOM A) /\
    (!j a. j < LENGTH ops /\ EL j (MAP (op_prov f.lf_H) ops) = SOME a ==>
      j IN P nm)
Proof
  qabbrev_tac `Ambient = ^ld_covered_ambient` >>
  strip_tac >>
  `o1_ctx_shape C /\ ptr_discipline lo C vs0` by
    fs[Abbr `Ambient`] >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  `MEM fn C.ctx_functions /\ ld_vars P A f` by
    gvs[ld_sync_def] >>
  `MEM inst (fn_insts fn)` by
    metis_tac[ld_sync_source,
              lowerDloadOracleCallAssemblyTheory.ld_active_inst_member] >>
  `?callee. lookup_function nm C.ctx_functions = SOME callee /\
    callee.fn_name = nm /\
    calleeT = FST (lower_dload_function_supply (Sigma nm) callee) /\
    Ambient lo C C' vs0 Sigma names callee calleeT` by
    (qunabbrev_tac `Ambient` >> drule_all ld_invoke_callee_ambient >> simp[]) >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> strip_tac >>
     metis_tac[o1_fn_shape_components]) >>
  `opaque_use_ok fn` by fs[unitShapeDefsTheory.fn_shape_ok_def] >>
  `taint_ok fn tn inst s` by
    (drule ld_sync_source >> strip_tac >>
     fs[ptrDisciplineTheory.ptr_discipline_def] >> metis_tac[]) >>
  `f.lf_src.vs_labels = f.lf_tgt.vs_labels` by
    metis_tac[ld_sync_labels] >>
  `opaque_use_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
   taint_ok f.lf_fn tn inst f.lf_src /\
   eval_operands ops f.lf_tgt = SOME argsT` by metis_tac[] >>
  drule_all ld_invoke_arguments_related >> strip_tac >>
  `fn_labels callee = fn_labels calleeT` by
    (gvs[] >> metis_tac[o1ContractLowerDloadTheory.lower_dload_function_supply_labels,
                       pairTheory.PAIR]) >>
  drule_all ld_setup_source_exists >>
  disch_then (qspec_then `s` (qspec_then `argsS` strip_assume_tac)) >>
  drule ld_sync_memory >> strip_tac >>
  drule_all ld_setup_pair_effect >>
  disch_then (strip_assume_tac o SRULE []) >>
  qexistsl_tac [`callee`,`argsS`,`cs`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (irule ld_setup_pair_vars >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule ld_arguments_live >>
      qexistsl_tac [`f.lf_H`,`ops`] >> simp[] >>
      metis_tac[ld_global_selected, MEM, finite_mapTheory.FRANGE_FLOOKUP]) >>
  rpt strip_tac >> irule ld_arguments_permission >>
  qexistsl_tac [`A`,`a`,`ops`,`f`,`inst`] >> simp[] >>
  drule lowerDloadOracleCallAssemblyTheory.ld_sync_ptr_ok >>
  simp[] >> strip_tac >>
  gvs[ptrDisciplineTheory.fn_ptr_ok_def]
QED

val _ = List.app (fn th => if null (hyp th) then ()
        else raise Fail "paired setup effect has kernel hypotheses")
  [ld_setup_pair_effect, ld_setup_pair_vars, ld_setup_source_exists,
   ld_invoke_callee_ambient, ld_invoke_correlated_setup];

(* Structural constructor: semantic entry/reachability is supplied separately. *)
Theorem ld_sync_call_push:
  ld_sync lo P C vs0 stk PG G tn fn calli s t A (f::fs) N /\
  saved = <|cf_fn := fn; cf_inst := calli; cf_state := s;
    cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> /\
  g.lf_serial = N /\ g.lf_tv = tn1.t_var /\
  g.lf_src.vs_allocas = FEMPTY /\ g.lf_tgt.vs_allocas = FEMPTY /\
  g.lf_E = {} /\ ld_maps A g /\ ld_vars P A g /\
  ld_intervals lo g.lf_src /\ ld_intervals lo g.lf_tgt /\
  g.lf_src.vs_prev_bb = g.lf_tgt.vs_prev_bb /\
  g.lf_src.vs_current_bb = g.lf_tgt.vs_current_bb /\
  MEM g.lf_fn C.ctx_functions /\
  g.lf_src.vs_alloca_next = f.lf_src.vs_alloca_next /\
  g.lf_tgt.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
  frame_reachable vs0 C (saved::stk)
    (MAP (OPTION_MAP (ld_erase A)) g.lf_Q) (ld_erase A o_f g.lf_H)
    tn1 g.lf_fn i g.lf_src /\
  active_inst g.lf_fn i g.lf_src /\
  ld_envelope g.lf_supply g.lf_fn g.lf_src g.lf_src.vs_inst_idx X p /\
  g.lf_tgt.vs_inst_idx = p /\
  ld_memory lo A tn1 g.lf_src g.lf_tgt /\
  ld_nonghost tn1 g.lf_src g.lf_tgt ==>
  ld_sync lo P C vs0 (saved::stk)
    (MAP (OPTION_MAP (ld_erase A)) g.lf_Q) (ld_erase A o_f g.lf_H)
    tn1 g.lf_fn i g.lf_src g.lf_tgt A (g::f::fs) (SUC N)
Proof
  strip_tac >>
  `ld_charge (g::f::fs) = ld_charge (f::fs)` by
    metis_tac[ld_charge_empty_push] >>
  `ld_slots A (g::f::fs) = ld_slots A (f::fs)` by
    metis_tac[ld_slots_empty_push] >>
  `f.lf_tgt.vs_alloca_next =
     f.lf_src.vs_alloca_next + 32 * ld_charge (f::fs)` by
    (drule ld_sync_active >> simp[] >> strip_tac >>
     drule ld_sync_frontier >> simp[]) >>
  qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ld_sync_def] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `EVERY _ fs` mp_tac >> rpt (pop_assum kall_tac) >>
      simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >>
      first_x_assum drule >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `EVERY _ fs` mp_tac >> rpt (pop_assum kall_tac) >>
      simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac
  >- (gen_tac >> Cases_on `j` >> simp[ld_charge_empty_push] >>
      first_x_assum (irule o SPEC_ALL) >> simp[]) >>
  conj_tac
  >- (gen_tac >> Cases_on `j` >> simp[] >- metis_tac[] >>
      first_x_assum (irule o SPEC_ALL) >> simp[]) >>
  gen_tac >> Cases_on `j` >> simp[]
QED

val _ = if null (hyp ld_sync_call_push) then ()
        else raise Fail "structural call push has kernel hypotheses";

(* Activity, not successful future execution, is the entry boundary. *)
Theorem ld_setup_active_entry:
  setup_callee callee argsS s = SOME cs /\
  setup_callee calleeT argsT t = SOME ct /\
  cs.vs_current_bb = ct.vs_current_bb /\
  lower_dload_function_supply u callee = (calleeT,v) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
  enters_block calleeT ct tp /\ active_inst calleeT ti tp ==>
  tp = ct /\ enters_block callee cs cs /\ enters_block calleeT ct ct /\
  ?i X. active_inst callee i cs /\
    ld_envelope u callee cs cs.vs_inst_idx X ct.vs_inst_idx /\
    X <> [] /\ active_inst calleeT (HD X) ct /\ ti = HD X
Proof
  strip_tac >>
  `cs.vs_prev_bb = NONE /\ ct.vs_prev_bb = NONE /\
   cs.vs_inst_idx = 0 /\ ct.vs_inst_idx = 0` by
    gvs[setup_callee_def, AllCaseEqs()] >>
  `tp = ct` by metis_tac[ld_enters_entry] >> gvs[] >>
  `enters_block callee ct ct` by
    metis_tac[lowerDloadConfiguredOriginsTheory.lower_dload_function_supply_enters_block_origin] >>
  `enters_block callee cs cs` by
    (qpat_x_assum `enters_block callee ct ct` mp_tac >>
     simp[enters_block_def] >> strip_tac >>
     qexistsl_tac [`bb`,`cs`] >> simp[] >>
     Cases_on `bb.bb_instructions` >>
     gvs[phi_prefix_length_def, eval_phis_def, AllCaseEqs()]) >>
  drule_all ld_entry_active_envelope >> strip_tac >>
  metis_tac[]
QED

Theorem ld_setup_guarded_entry:
  setup_callee callee argsS s = SOME cs /\
  setup_callee calleeT argsT t = SOME ct /\
  cs.vs_current_bb = ct.vs_current_bb /\
  lower_dload_function_supply u callee = (calleeT,v) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
  lookup_block ct.vs_current_bb calleeT.fn_blocks = SOME bb /\
  eval_phis ct bb.bb_instructions = OK tp /\
  ^ld_probe_guard C' k bb
    (tp with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
  tp = ct /\ phi_prefix_length bb.bb_instructions = 0 /\
  (tp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = ct /\
  enters_block callee cs cs /\ enters_block calleeT ct ct /\
  ?i X. active_inst callee i cs /\
    ld_envelope u callee cs cs.vs_inst_idx X ct.vs_inst_idx /\
    X <> [] /\ active_inst calleeT (HD X) ct
Proof
  strip_tac >>
  `ct.vs_prev_bb = NONE /\ ct.vs_inst_idx = 0` by
    gvs[setup_callee_def, AllCaseEqs()] >>
  drule_all ld_entry_phis >> strip_tac >>
  `tp with vs_inst_idx := phi_prefix_length bb.bb_instructions = ct` by gvs[] >>
  `enters_block calleeT ct ct` by
    (simp[enters_block_def] >> metis_tac[]) >>
  `?ti. get_instruction bb ct.vs_inst_idx = SOME ti` by
    (drule ld_successful_body_fetch >> gvs[]) >>
  `active_inst calleeT ti ct` by
    (simp[active_inst_def] >> qexists_tac `bb` >> gvs[get_instruction_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  drule_all ld_setup_active_entry >> simp[] >> metis_tac[]
QED

Theorem ld_call_stable_push:
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  FDOM A = ld_slots A (f::fs) /\
  fc.lf_src.vs_allocas = FEMPTY /\ fc.lf_tgt.vs_allocas = FEMPTY /\
  fc.lf_src.vs_alloca_next = f.lf_src.vs_alloca_next /\
  fc.lf_tgt.vs_alloca_next = f.lf_tgt.vs_alloca_next /\ fc.lf_H = FEMPTY /\
  (!a. MEM (SOME a) fc.lf_Q ==> a IN FDOM A) /\
  fc.lf_supply = Sigma fc.lf_fn.fn_name /\
  (!j a. j < LENGTH fc.lf_Q /\ EL j fc.lf_Q = SOME a ==>
    j IN P fc.lf_fn.fn_name) /\
  (!g. MEM g (f::fs) ==>
    list_precedes fc.lf_fn.fn_name g.lf_fn.fn_name names) ==>
  ^ld_probe_stable lo P Sigma names (f::fs) fc A A (fc::f::fs)
Proof
  qabbrev_tac `Stable = ^ld_probe_stable` >> strip_tac >>
  `ld_global lo A (f::fs)` by fs[Abbr `Stable`] >>
  `ld_global lo A (fc::f::fs)` by
    (irule ld_global_empty_push >> simp[]) >>
  `!j k. j < k /\ k < LENGTH (fc::f::fs) ==>
    list_precedes (EL j (fc::f::fs)).lf_fn.fn_name
      (EL k (fc::f::fs)).lf_fn.fn_name names` by
    (rpt strip_tac >> irule ld_order_fresh_push >>
     fs[Abbr `Stable`] >> metis_tac[]) >>
  `!g. MEM g (f::fs) ==> FRANGE g.lf_H SUBSET FDOM A /\
      (!a. MEM (SOME a) g.lf_Q ==> a IN FDOM A)` by
    (qpat_assum `ld_global lo A (f::fs)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[ld_global_def, SUBSET_DEF] >> metis_tac[]) >>
  gvs[Abbr `Stable`] >> metis_tac[]
QED

Theorem ld_setup_empty_shape:
  setup_callee fn args s = SOME cs ==>
  cs.vs_allocas = FEMPTY /\ cs.vs_alloca_next = s.vs_alloca_next /\
  cs.vs_prev_bb = NONE /\ cs.vs_inst_idx = 0
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem ld_invoke_active_push:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME calleeT /\
  eval_operands ops t = SOME argsT /\
  setup_callee calleeT argsT t = SOME ct /\
  enters_block calleeT ct tp /\ active_inst calleeT ti tp /\
  lookup_block tp.vs_current_bb calleeT.fn_blocks = SOME bb ==>
  ?callee argsS cs fc.
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME argsS /\ setup_callee callee argsS s = SOME cs /\
    ^ld_covered_ambient lo C C' vs0 Sigma names callee calleeT /\
    fc = <|lf_serial := N; lf_supply := Sigma nm; lf_fn := callee;
      lf_src := cs; lf_tgt := ct; lf_H := FEMPTY;
      lf_Q := MAP (op_prov f.lf_H) ops; lf_E := {}; lf_tv := FEMPTY|> /\
    ^ld_probe_point lo P C C' vs0
      (<|cf_fn := fn; cf_inst := inst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
      callee calleeT cs (f::fs) fc A Sigma names bb tp
Proof
  qabbrev_tac `Ambient = ^ld_covered_ambient` >>
  qabbrev_tac `Stable = ^ld_probe_stable` >>
  qabbrev_tac `Point = ^ld_probe_point` >> strip_tac >>
  `ld_global lo A (f::fs)` by fs[Abbr `Stable`] >>
  qunabbrev_tac `Ambient` >> drule_all ld_invoke_correlated_setup >>
  disch_then (strip_assume_tac o SRULE []) >>
  qabbrev_tac `fc = <|lf_serial := N; lf_supply := Sigma nm; lf_fn := callee;
    lf_src := cs; lf_tgt := ct; lf_H := FEMPTY;
    lf_Q := MAP (op_prov f.lf_H) ops; lf_E := {}; lf_tv := FEMPTY|>` >>
  qexistsl_tac [`callee`,`argsS`,`cs`,`fc`] >>
  simp[NoAsms] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- simp[Abbr `fc`] >>
  simp[Abbr `Point`] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks)` by
    (`MEM callee C.ctx_functions` by metis_tac[lookup_function_MEM] >>
     `o1_fn_shape C callee` by
       (qpat_assum `MEM callee C.ctx_functions` mp_tac >>
        qpat_assum `o1_ctx_shape C` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[o1PassContractTheory.o1_ctx_shape_def, EVERY_MEM] >>
        metis_tac[]) >>
     drule o1_fn_shape_components >> simp[]) >>
  `lower_dload_function_supply (Sigma nm) callee =
      (calleeT, SND (lower_dload_function_supply (Sigma nm) callee))` by
    metis_tac[pairTheory.PAIR] >>
  drule_all ld_setup_active_entry >> strip_tac >> fs[] >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  `cs.vs_allocas = FEMPTY /\ cs.vs_alloca_next = s.vs_alloca_next /\
   cs.vs_prev_bb = NONE /\ cs.vs_inst_idx = 0` by
    metis_tac[ld_setup_empty_shape] >>
  `ct.vs_allocas = FEMPTY /\ ct.vs_alloca_next = t.vs_alloca_next /\
   ct.vs_prev_bb = NONE /\ ct.vs_inst_idx = 0` by
    metis_tac[ld_setup_empty_shape] >>
  qabbrev_tac `saved = <|cf_fn := fn; cf_inst := inst; cf_state := s;
    cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>` >>
  `frame_reachable vs0 C (saved::stk)
    (MAP (OPTION_MAP (ld_erase A)) fc.lf_Q) FEMPTY
    (tn with t_var := FEMPTY) callee i cs` by
    suspend "reach" >>
  `ld_sync lo P C vs0 (saved::stk)
    (MAP (OPTION_MAP (ld_erase A)) fc.lf_Q) FEMPTY
    (tn with t_var := FEMPTY) callee i cs ct A (fc::f::fs) (SUC N)` by
    suspend "sync" >>
  `Stable lo P Sigma names (f::fs) fc A A (fc::f::fs)` by
    suspend "stable" >>
  `ld_return_cont C callee cs cs` by
    (irule ld_return_cont_entry >> simp[]) >>
  qexistsl_tac [`MAP (OPTION_MAP (ld_erase A)) fc.lf_Q`,`FEMPTY`,
    `tn with t_var := FEMPTY`,`i`,`cs`,`ct`,`A`,`fc::f::fs`,
    `SUC N`,`X`,`ct.vs_inst_idx`,`0`] >>
  simp[NoAsms, lowerDloadSafetyKernelTheory.ld_prefix_zero] >>
  fs[Abbr `fc`, Abbr `saved`, ld_image_def] >>
  metis_tac[listTheory.NOT_NIL_EQ_LENGTH_NOT_0]
QED

Resume ld_invoke_active_push[reach]:
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  simp[Abbr `fc`, Abbr `saved`, ld_arguments_erasure] >>
  irule frame_reachable_call >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[ld_sync_source, ld_sync_ghosts]
QED

Resume ld_invoke_active_push[sync]:
  `ld_sync lo P C vs0 (saved::stk)
    (MAP (OPTION_MAP (ld_erase A)) fc.lf_Q) (ld_erase A o_f fc.lf_H)
    (tn with t_var := FEMPTY) fc.lf_fn i fc.lf_src fc.lf_tgt
    A (fc::f::fs) (SUC N)` suffices_by simp[Abbr `fc`] >>
  irule ld_sync_call_push >>
  goal_assum (drule_at Any) >>
  simp[Abbr `fc`, Abbr `saved`, ld_maps_def, ld_intervals_def] >>
  conj_tac >-
    (qpat_assum `lookup_function nm C.ctx_functions = SOME callee` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[lookup_function_MEM]) >>
  conj_tac >- (qexists_tac `X` >> fs[]) >>
  conj_tac >- fs[] >>
  qexistsl_tac [`t`,`tn`] >> simp[]
QED

Resume ld_invoke_active_push[stable]:
  qpat_assum `ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N`
    (strip_assume_tac o MATCH_MP ld_sync_source) >>
  `MEM fn C.ctx_functions` by
    (drule_all frame_reachable_live_order >> simp[]) >>
  `MEM nm (fn_invoke_targets fn)` by
    (irule active_invoke_target >> goal_assum (drule_at Any) >> simp[]) >>
  `list_precedes nm fn.fn_name names` by
    (qpat_assum `callee_first names C.ctx_functions` mp_tac >>
     qpat_assum `MEM fn C.ctx_functions` mp_tac >>
     qpat_assum `MEM nm (fn_invoke_targets fn)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[o1PassContractTheory.callee_first_def]) >>
  `!g. MEM g (f::fs) ==> list_precedes nm g.lf_fn.fn_name names` by
    (gen_tac >> simp[] >> strip_tac >- simp[] >>
     `?j. j < LENGTH fs /\ g = EL j fs` by metis_tac[MEM_EL] >>
     `list_precedes f.lf_fn.fn_name g.lf_fn.fn_name names` by
       (qpat_assum `Stable lo P Sigma names fs0 f0 A0 A (f::fs)` mp_tac >>
        simp[NoAsms, Abbr `Stable`] >> strip_tac >>
        qpat_x_assum `!j k. _ ==> list_precedes _ _ names`
          (qspecl_then [`0`,`SUC j`] mp_tac) >> simp[]) >>
     metis_tac[lowerDloadSafetyBoundaryTheory.list_precedes_transitive]) >>
  qunabbrev_tac `Stable` >> irule ld_call_stable_push >>
  qpat_assum `ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N`
    (mp_tac o MATCH_MP lowerDloadOracleCallAssemblyTheory.ld_sync_slots) >>
  strip_tac >> simp[Abbr `fc`] >>
  qexistsl_tac [`A0`,`f0`] >> fs[] >>
  qpat_assum `!g. MEM g _ ==> FRANGE g.lf_H SUBSET _ /\ _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED

Finalise ld_invoke_active_push

val _ = List.app (fn th => if null (hyp th) then ()
        else raise Fail "guarded call push has kernel hypotheses")
  [ld_setup_guarded_entry, ld_call_stable_push, ld_setup_empty_shape,
   ld_invoke_active_push];

(* Successful-run clients derive activity, then use the same push boundary. *)
Theorem ld_invoke_guarded_push:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME calleeT /\
  eval_operands ops t = SOME argsT /\
  setup_callee calleeT argsT t = SOME ct ==>
  ?callee argsS cs fc.
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME argsS /\ setup_callee callee argsS s = SOME cs /\
    ^ld_covered_ambient lo C C' vs0 Sigma names callee calleeT /\
    fc = <|lf_serial := N; lf_supply := Sigma nm; lf_fn := callee;
      lf_src := cs; lf_tgt := ct; lf_H := FEMPTY;
      lf_Q := MAP (op_prov f.lf_H) ops; lf_E := {}; lf_tv := FEMPTY|> /\
    ^ld_probe_entry C' calleeT
      (^ld_probe_point lo P C C' vs0
        (<|cf_fn := fn; cf_inst := inst; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
        callee calleeT cs (f::fs) fc A Sigma names) ct
Proof
  qabbrev_tac `Ambient = ^ld_covered_ambient` >>
  qabbrev_tac `Stable = ^ld_probe_stable` >>
  qabbrev_tac `Point = ^ld_probe_point` >>
  qabbrev_tac `Guard = ^ld_probe_guard` >>
  qabbrev_tac `Entry = ^ld_probe_entry` >> strip_tac >>
  `ld_global lo A (f::fs)` by fs[Abbr `Stable`] >>
  qunabbrev_tac `Ambient` >> drule_all ld_invoke_correlated_setup >>
  disch_then (strip_assume_tac o SRULE []) >>
  qexistsl_tac [`callee`,`argsS`,`cs`,
    `<|lf_serial := N; lf_supply := Sigma nm; lf_fn := callee;
       lf_src := cs; lf_tgt := ct; lf_H := FEMPTY;
       lf_Q := MAP (op_prov f.lf_H) ops; lf_E := {}; lf_tv := FEMPTY|>`] >>
  simp[Abbr `Entry`] >> rpt gen_tac >> strip_tac >>
  `enters_block calleeT ct
     (tp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[enters_block_def] >> metis_tac[]) >>
  `?ti. get_instruction bb
     (tp with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_inst_idx = SOME ti` by
    (qunabbrev_tac `Guard` >> drule ld_successful_body_fetch >> simp[]) >>
  `ct.vs_prev_bb = NONE /\ ct.vs_inst_idx = 0` by
    metis_tac[ld_setup_empty_shape] >>
  drule_all ld_entry_phis >> strip_tac >>
  `active_inst calleeT ti
     (tp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[active_inst_def] >> qexists_tac `bb` >>
     gvs[get_instruction_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `lookup_block
     (tp with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_current_bb
     calleeT.fn_blocks = SOME bb` by
    simp[] >>
  qunabbrev_tac `Stable` >>
  drule_all ld_invoke_active_push >> strip_tac >>
  gvs[Abbr `Point`] >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED
