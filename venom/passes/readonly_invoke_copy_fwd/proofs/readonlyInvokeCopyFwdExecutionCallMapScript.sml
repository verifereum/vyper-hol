(* Selected positive translations agree on their actual source endpoint. *)
Theory readonlyInvokeCopyFwdExecutionCallMap
Ancestors
  readonlyInvokeCopyFwdExecutionCallArgs readonlyInvokeCopyFwdExecutionCallSites
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdOpaqueReturn
  readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHistoryVisitAccess readonlyInvokeCopyFwdHistoryCopyUniqueness
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdPlan
  internalReturnCopyFwdPlan invokeCopyFwdCommonDefs occurrenceGeometry
  o1LowerDloadOccurrence o1LowerDloadRelocationKernel ptrDiscipline
  taintAgree unitShapeDefs venomExecSemantics contextCodegenRel
  allocaRemapSSA mem2varProofs o1PassContract venomWf venomInst
  list finite_map pred_set arithmetic words

Theorem ricf_call_original_copy_member[local]:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) ==>
  b < LENGTH original.fn_blocks /\
  e.rfe_index < LENGTH (EL b original.fn_blocks).bb_instructions /\
  MEM (ricf_event_copy e (EL b original.fn_blocks)) (fn_insts original) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_opcode = MCOPY
Proof
  strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule ricf_event_copy_shape >> strip_tac >>
  `e.rfe_index < LENGTH (EL b original.fn_blocks).bb_instructions /\
   ricf_inst_edit (ricf_event_copy e (EL b original.fn_blocks))
     (ricf_event_copy e current)` by
    (gvs[ricf_block_edit_def, LIST_REL_EL_EQN, ricf_event_copy_def] >>
     metis_tac[]) >>
  simp[fn_insts_def, fn_insts_blocks_MEM, ricf_event_copy_def] >>
  fs[ricf_inst_edit_def, ricf_event_copy_def] >> metis_tac[EL_MEM]
QED

Theorem ricf_call_destination_copy_equal[local]:
  ricf_located_event ctxP original logP roundP bp esP pp e currentP /\
  ricf_located_event ctxQ original logQ roundQ bq esQ pq f currentQ /\
  ssa_form original /\ fn_inst_wf original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  (ricf_event_copy e (EL bp original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  (ricf_event_copy f (EL bq original.fn_blocks)).inst_operands = [Var qdst;qsrc;qsz] /\
  icf_assign_root (dfg_build_function original) {} dst =
    icf_assign_root (dfg_build_function original) {} qdst ==>
  ricf_event_copy e (EL bp original.fn_blocks) =
    ricf_event_copy f (EL bq original.fn_blocks)
Proof
  strip_tac >>
  qpat_assum `ricf_located_event ctxP original logP roundP bp esP pp e currentP`
    (mp_then Any mp_tac ricf_call_original_copy_member) >> simp[] >> strip_tac >>
  qpat_assum `ricf_located_event ctxQ original logQ roundQ bq esQ pq f currentQ`
    (mp_then Any mp_tac ricf_call_original_copy_member) >> simp[] >> strip_tac >>
  `ircf_alias original
    (icf_assign_root (dfg_build_function original) {} dst) qdst` by
    metis_tac[ircf_assign_root_alias] >>
  `(ricf_event_copy f (EL bq original.fn_blocks)).inst_id =
   (ricf_event_copy e (EL bp original.fn_blocks)).inst_id` by
    (qspecl_then [`ctxP`,`original`,`logP`,`roundP`,`bp`,`esP`,`pp`,`e`,`currentP`,
       `dst`,`src`,`sz`,`bq`,`f.rfe_index`,
       `ricf_event_copy f (EL bq original.fn_blocks)`,`qdst`]
       mp_tac ricf_located_event_destination_unique >>
     simp[GSYM ricf_event_copy_def]) >>
  irule (Q.ISPEC `\i:instruction. i.inst_id` ALL_DISTINCT_MAP_IMP) >>
  simp[] >> qexists_tac `fn_insts original` >> simp[]
QED

Theorem ricf_call_payload_source_key[local]:
  ricf_history_origin vs C ctxP logP p stkP PGP GP tnP /\
  ricf_history_origin vs C ctxQ logQ q stkQ PGQ GQ tnQ /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ssa_form p.rpe_fn /\ fn_inst_wf p.rpe_fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) /\
  ricf_full_alloca_copies p.rpe_fn /\ ricf_src_alloca p.rpe_fn /\
  p.rpe_fn = q.rpe_fn /\ p.rpe_dst = q.rpe_dst ==>
  p.rpe_src = q.rpe_src
Proof
  strip_tac >>
  qpat_assum `ricf_history_origin vs C ctxP logP p stkP PGP GP tnP`
    (mp_then Any mp_tac ricf_history_origin_original_allocas) >>
  simp[] >> strip_tac >>
  rename1 `(ricf_event_copy p.rpe_event p.rpe_block).inst_operands =
    [Var pdst;Var psv;Lit psz]` >>
  rename1 `da.inst_outputs = [icf_assign_root (dfg_build_function q.rpe_fn) {} pdst]` >>
  rename1 `sa.inst_outputs = [psv]` >>
  qpat_assum `ricf_history_origin vs C ctxQ logQ q stkQ PGQ GQ tnQ`
    (mp_then Any mp_tac ricf_history_origin_original_allocas) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  rename1 `(ricf_event_copy q.rpe_event q.rpe_block).inst_operands =
    [Var qdst;Var qsv;Lit qsz]` >>
  rename1 `da'.inst_outputs = [icf_assign_root (dfg_build_function q.rpe_fn) {} qdst]` >>
  rename1 `sa'.inst_outputs = [qsv]` >>
  `da = da'` by
    (irule (Q.ISPEC `\i:instruction. i.inst_id` ALL_DISTINCT_MAP_IMP) >>
     conj_tac >- gvs[] >> qexists_tac `fn_insts p.rpe_fn` >> metis_tac[]) >>
  `?roundP bp esP pp currentP.
    ricf_located_event ctxP p.rpe_fn logP roundP bp esP pp p.rpe_event currentP /\
    p.rpe_block = EL bp p.rpe_fn.fn_blocks` by
    (fs[ricf_history_origin_def] >> metis_tac[]) >>
  `?roundQ bq esQ pq currentQ.
    ricf_located_event ctxQ p.rpe_fn logQ roundQ bq esQ pq q.rpe_event currentQ /\
    q.rpe_block = EL bq p.rpe_fn.fn_blocks` by
    (fs[ricf_history_origin_def] >> metis_tac[]) >>
  `ricf_event_copy p.rpe_event p.rpe_block =
    ricf_event_copy q.rpe_event q.rpe_block` by
    (fs[] >> irule ricf_call_destination_copy_equal >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `psv = qsv` by gvs[] >>
  `sa = sa'` by (irule ssa_unique_output >> metis_tac[MEM]) >>
  qpat_assum `p.rpe_src = (p.rpe_owner,sa.inst_id)` mp_tac >>
  qpat_assum `q.rpe_src = (q.rpe_owner,sa'.inst_id)` mp_tac >>
  qpat_assum `q.rpe_dst = (p.rpe_owner,da.inst_id)` mp_tac >>
  qpat_assum `q.rpe_dst = (q.rpe_owner,da'.inst_id)` mp_tac >>
  qpat_assum `da = da'` mp_tac >> qpat_assum `sa = sa'` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[]
QED

Theorem ricf_call_payload_source_unique:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  MEM (p,[]) certificates /\ MEM (q,[]) certificates /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occurrence_natural_geometry lo a U B stk s /\ p.rpe_db = q.rpe_db ==>
  p.rpe_sb = q.rpe_sb
Proof
  strip_tac >>
  `?ctxP logP. ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B (p,[])` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def,
        EVERY_MEM] >> metis_tac[]) >>
  `?ctxQ logQ. ricf_phase_entry vs C ctxQ logQ stk PG G tn fn s a U B (q,[])` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def,
        EVERY_MEM] >> metis_tac[]) >>
  fs[ricf_phase_entry_def] >>
  `p.rpe_fn = fn /\ q.rpe_fn = fn` by
    metis_tac[ricf_history_cursor_owner_function] >>
  `p.rpe_dst = q.rpe_dst` by
    (irule occurrence_geometry_positive_site_unique >> metis_tac[]) >>
  `p.rpe_src = q.rpe_src` by
    (fs[ricf_history_cursor_def] >>
     irule ricf_call_payload_source_key >> metis_tac[]) >>
  qpat_assum `FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size)` mp_tac >>
  qpat_assum `FLOOKUP B q.rpe_src = SOME (q.rpe_sb,q.rpe_size)` mp_tac >>
  qpat_assum `p.rpe_src = q.rpe_src` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[]
QED

Theorem ricf_call_payload_fold_lookup[local]:
  !ps sites p.
  MEM p ps /\
  (!q. MEM q ps /\ q.rpe_db = p.rpe_db ==> q.rpe_sb = p.rpe_sb) ==>
  FLOOKUP (FOLDR (\q m.
    m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites ps)
    (p.rpe_db,p.rpe_size) = SOME (p.rpe_db,p.rpe_sb,p.rpe_size)
Proof
  Induct >> simp[FOLDR, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `(h.rpe_db,h.rpe_size) = (p.rpe_db,p.rpe_size)` >>
  gvs[] >> metis_tac[MEM]
QED

Theorem ricf_call_selected_payload_lookup:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  EVERY (\q. MEM (q,[]) certificates) ps /\ MEM p ps /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occurrence_natural_geometry lo a U B stk s ==>
  FLOOKUP (FOLDR (\q m.
    m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites ps)
    (p.rpe_db,p.rpe_size) = SOME (p.rpe_db,p.rpe_sb,p.rpe_size)
Proof
  strip_tac >> irule ricf_call_payload_fold_lookup >> simp[] >>
  rpt strip_tac >> irule ricf_call_payload_source_unique >>
  goal_assum (drule_at Any) >> simp[] >> fs[EVERY_MEM] >> metis_tac[]
QED

(* A zero-sized rewrite still evaluates its actual source operand.  Value
   agreement then follows from the original argument's zero provenance. *)
Theorem ricf_call_zero_argument_values:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\
  inst.inst_opcode = INVOKE /\ MEM (Var dv) inst.inst_operands /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  e.rfe_index <= s.vs_inst_idx /\
  e.rfe_index < LENGTH bb.bb_instructions /\
  (ricf_event_copy e bb).inst_opcode = MCOPY /\
  (ricf_event_copy e bb).inst_operands = [Var dst;Var sv;Lit sz] /\
  MEM da (fn_insts fn) /\ da.inst_opcode = ALLOCA /\
  da.inst_outputs = [dr] /\ da.inst_operands = [Lit sz] /\
  MEM sa (fn_insts fn) /\ sa.inst_opcode = ALLOCA /\
  sa.inst_outputs = [sv] /\ sa.inst_operands = [Lit sz] /\
  ircf_alias fn dr dv /\ w2n sz = 0 ==>
  ?db y.
    eval_operand (Var dv) s = SOME (n2w db) /\
    eval_operand (Var sv) t = SOME y /\ FLOOKUP G dv = SOME (db,0) /\
    !callsites. ricf_opaque_value_agree callsites (op_prov G (Var dv)) {}
      (n2w db) y
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  drule_all ricf_call_earlier_copy_values >> strip_tac >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  `?y. eval_operand (Var sv) t = SOME y` by
    (drule ricf_opaque_frame_operand_defined >>
     disch_then (qspec_then `Var sv` mp_tac) >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  qexistsl_tac [`db`,`y`] >>
  simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def, op_prov_def]
QED

Theorem ricf_call_opaque_value_same_lookup[local]:
  ricf_opaque_value_agree sites p m x y /\
  (!id. p = SOME id ==> FLOOKUP callsites id = FLOOKUP sites id) ==>
  ricf_opaque_value_agree callsites p m x y
Proof
  Cases_on `p`
  >- simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
       ricf_value_agree_def, ld_value_agree_def] >>
  rename1 `ricf_opaque_value_agree sites (SOME id) m x y` >> strip_tac >>
  `id IN FDOM callsites <=> id IN FDOM sites` by
    (Cases_on `id IN FDOM callsites` >> Cases_on `id IN FDOM sites` >>
     gvs[FLOOKUP_DEF]) >>
  Cases_on `id IN FDOM sites` >>
  fs[ricf_opaque_value_agree_def, ricf_value_agree_def, ld_value_agree_def]
QED

Theorem ricf_call_unchanged_argument_values:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\ MEM op inst.inst_operands /\
  eval_operand op s = SOME x /\
  (!id. op_prov G op = SOME id ==>
    FLOOKUP callsites id = FLOOKUP sites id) ==>
  ?y. eval_operand op t = SOME y /\
    ricf_opaque_value_agree callsites (op_prov G op) {} x y
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `op_taint tn op = {}` by metis_tac[taint_ok_invoke_operand] >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt strip_tac >> gvs[] >>
     drule_all opaque_use_ok_retpc_use >> simp[retpc_use_ok_def]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  drule_all ricf_opaque_frame_operand >> strip_tac >>
  qexists_tac `y` >> simp[] >>
  irule ricf_call_opaque_value_same_lookup >> metis_tac[]
QED

Theorem ricf_call_payload_fold_no_hit[local]:
  !ps sites id.
  (!q. MEM q ps ==> (q.rpe_db,q.rpe_size) <> id) ==>
  FLOOKUP (FOLDR (\q m.
    m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites ps) id =
  FLOOKUP sites id
Proof
  Induct >> simp[FOLDR, FLOOKUP_UPDATE] >> metis_tac[MEM]
QED

Theorem ricf_call_unchanged_fold_argument_values:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\ MEM op inst.inst_operands /\
  eval_operand op s = SOME x /\
  (!q. MEM q ps ==> op_prov G op <> SOME (q.rpe_db,q.rpe_size)) ==>
  ?y. eval_operand op t = SOME y /\
    ricf_opaque_value_agree
      (FOLDR (\q m.
        m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites ps)
      (op_prov G op) {} x y
Proof
  strip_tac >>
  mp_tac (SPEC_ALL ricf_call_unchanged_argument_values |>
    Q.INST [`callsites` |-> `FOLDR (\q m.
      m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites ps`]) >>
  (impl_tac >-
    (simp[] >> rpt strip_tac >>
     irule ricf_call_payload_fold_no_hit >> metis_tac[])) >> simp[]
QED
