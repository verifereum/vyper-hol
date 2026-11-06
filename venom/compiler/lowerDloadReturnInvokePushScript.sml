(* Correlated internal-call setup support; no independent target setup choice. *)
Theory lowerDloadReturnInvokePush
Ancestors
  lowerDloadReturnInvokeArguments lowerDloadReturnInvokeStack lowerDloadSafetyArguments
  lowerDloadSafetyEntry lowerDloadReturnStable lowerDloadReturnAlignment
  venomExecSemantics venomState venomInst finite_map list pred_set
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
