(* Active callee entry with readings correlated in the pushed frame. *)
Theory gasFocusLowerDloadCallEntry
Ancestors
  gasFocusLowerDloadInvokeSetup lowerDloadReturnInvokePush
  lowerDloadReturnStable lowerDloadReturnAlignment lowerDloadLiveAllocation
  lowerDloadSafetyRelation lowerDloadSafetyAmbient lowerDloadSafetyKernel
  lowerDloadOracleCallAssembly o1PassContract o1ContractLowerDload
  calleeTransport ptrDiscipline venomExecSemantics venomState venomInst
  finite_map list pred_set
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_invoke_active_entry:
  o1_ctx_shape C /\
  (!g. MEM g C.ctx_functions ==>
    lookup_function g.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma g.fn_name) g))) /\
  taint_ok fn tn inst s /\
  s.vs_gas_readings = t.vs_gas_readings /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME calleeT /\
  eval_operands ops t = SOME argsT /\
  setup_callee calleeT argsT t = SOME ct /\
  callee_first names C.ctx_functions /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  enters_block calleeT ct tp /\ active_inst calleeT ti tp /\
  EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs) ==>
  ?callee argsS cs saved fc PG1 tn1 i X.
    lookup_function nm C.ctx_functions = SOME callee /\ callee.fn_name = nm /\
    eval_operands ops s = SOME argsS /\ setup_callee callee argsS s = SOME cs /\
    calleeT = FST (lower_dload_function_supply (Sigma nm) callee) /\
    saved = <|cf_fn := fn; cf_inst := inst; cf_state := s;
      cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> /\
    tp = ct /\
    fc.lf_serial = N /\ fc.lf_fn = callee /\ fc.lf_supply = Sigma nm /\
    fc.lf_src = cs /\ fc.lf_tgt = ct /\ fc.lf_Q = MAP (op_prov f.lf_H) ops /\
    ld_sync lo P C vs0 (saved::stk) PG1 FEMPTY tn1 callee i cs ct A
      (fc::f::fs) (SUC N) /\
    ^ld_probe_stable lo P Sigma names (f::fs) fc A A (fc::f::fs) /\
    ld_envelope fc.lf_supply callee cs cs.vs_inst_idx X ct.vs_inst_idx /\
    ld_prefix C' calleeT X ct.vs_inst_idx 0 ct tp /\ ti = EL 0 X /\
    cs.vs_gas_readings = ct.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH cs.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (fc::f::fs)
Proof
  qabbrev_tac `Stable = ^ld_probe_stable` >> strip_tac >>
  drule_all ld_focus_invoke_correlated_setup >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks)` by
    (`MEM callee C.ctx_functions` by metis_tac[lookup_function_MEM] >>
     `o1_fn_shape C callee` by
       (gvs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
     drule o1_fn_shape_components >> simp[]) >>
  `lower_dload_function_supply (Sigma nm) callee =
      (calleeT, SND (lower_dload_function_supply (Sigma nm) callee))` by
    metis_tac[pairTheory.PAIR] >>
  drule_all ld_setup_active_entry >> strip_tac >> fs[] >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  `cs.vs_allocas = FEMPTY /\ cs.vs_alloca_next = s.vs_alloca_next /\
   ct.vs_allocas = FEMPTY /\ ct.vs_alloca_next = t.vs_alloca_next` by
    metis_tac[ld_setup_empty_shape] >>
  qabbrev_tac `fc = <|lf_serial := N; lf_supply := Sigma nm; lf_fn := callee;
    lf_src := cs; lf_tgt := ct; lf_H := FEMPTY;
    lf_Q := MAP (op_prov f.lf_H) ops; lf_E := {}; lf_tv := FEMPTY|>` >>
  qabbrev_tac `saved = <|cf_fn := fn; cf_inst := inst; cf_state := s;
    cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>` >>
  `frame_reachable vs0 C (saved::stk) (MAP (op_prov G) ops) FEMPTY
    (tn with t_var := FEMPTY) callee i cs` by suspend "reach" >>
  `ld_sync lo P C vs0 (saved::stk) (MAP (op_prov G) ops) FEMPTY
    (tn with t_var := FEMPTY) callee i cs ct A (fc::f::fs) (SUC N)` by
    suspend "sync" >>
  `Stable lo P Sigma names (f::fs) fc A A (fc::f::fs)` by suspend "stable" >>
  qexistsl_tac [`fc`,`MAP (op_prov G) ops`,
    `tn with t_var := FEMPTY`,`i`,`X`] >>
  fs[Abbr `fc`, Abbr `saved`, ld_prefix_zero] >>
  metis_tac[NOT_NIL_EQ_LENGTH_NOT_0]
QED

Resume ld_focus_invoke_active_entry[reach]:
  simp[Abbr `saved`] >> irule frame_reachable_call >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[ld_sync_source, ld_sync_ghosts]
QED

Resume ld_focus_invoke_active_entry[sync]:
  `ld_sync lo P C vs0 (saved::stk) (MAP (op_prov G) ops)
    (ld_erase A o_f fc.lf_H) (tn with t_var := FEMPTY) fc.lf_fn i
    fc.lf_src fc.lf_tgt A (fc::f::fs) (SUC N)` suffices_by simp[Abbr `fc`] >>
  irule ld_sync_call_push >> goal_assum (drule_at Any) >>
  simp[Abbr `fc`, Abbr `saved`, ld_maps_def, ld_intervals_def] >>
  conj_tac >- metis_tac[lookup_function_MEM] >>
  rpt conj_tac
  >~ [`ld_dyn_agree _ _ _ _`]
  >- (qpat_assum `setup_callee _ _ s = SOME cs`
        (strip_assume_tac o MATCH_MP setup_callee_shared_fields) >>
      qpat_assum `setup_callee _ _ t = SOME ct`
        (strip_assume_tac o MATCH_MP setup_callee_shared_fields) >>
      drule ld_sync_dyn_agree >> fs[])
  >~ [`ld_params_ok _ _ _ _`]
  >- (drule ld_sync_ghosts >> simp[] >> strip_tac >>
      rw[ld_params_ok_def, EL_MAP] >>
      Cases_on `EL k ops` >> simp[op_prov_def] >>
      rename1 `FLOOKUP f.lf_H v` >> Cases_on `FLOOKUP f.lf_H v` >> simp[] >>
      fs[ld_ghost_ok_def] >> metis_tac[])
  >- (qexists_tac `X` >> fs[]) >>
  qexistsl_tac [`t`,`tn`] >> simp[]
QED

Resume ld_focus_invoke_active_entry[stable]:
  qpat_assum `ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N`
    (strip_assume_tac o MATCH_MP ld_sync_source) >>
  `MEM fn C.ctx_functions` by gvs[ld_sync_def] >>
  `MEM nm (fn_invoke_targets fn)` by
    (irule active_invoke_target >> goal_assum (drule_at Any) >> simp[]) >>
  `list_precedes nm fn.fn_name names` by
    (gvs[callee_first_def] >> metis_tac[]) >>
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
    (mp_tac o MATCH_MP ld_sync_slots) >>
  strip_tac >> simp[Abbr `fc`] >>
  qexistsl_tac [`A0`,`f0`] >> fs[] >>
  qpat_assum `!g. MEM g _ ==> FRANGE g.lf_H SUBSET _ /\ _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED

Finalise ld_focus_invoke_active_entry
