(* Actual calls install their selected translations before entering a callee. *)
Theory readonlyInvokeCopyFwdExecutionCallInstall
Ancestors
  readonlyInvokeCopyFwdExecutionCallAggregate readonlyInvokeCopyFwdExecutionCallArgs
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdExecutionHistory
  readonlyInvokeCopyFwdExecutionCoverage readonlyInvokeCopyFwdLiveCertificates
  readonlyInvokeCopyFwdMapCoverage readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdHeterogeneousMapOrigins readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdPlan
  invokeCopyFwdCommonDefs readonlyMemoryArgsDefs occurrenceGeometry
  o1LowerDloadOccurrence ptrDiscipline contextCodegenRel venomExecSemantics
  venomExecProofs venomWf venomInst list finite_map pred_set words

Theorem ricf_call_argument_provenance_keys[local]:
  MEM (SOME key) (MAP (op_prov G) ops) ==> ?v. FLOOKUP G v = SOME key
Proof
  simp[MEM_MAP] >> rpt strip_tac >> rename1 `MEM op ops` >>
  Cases_on `op` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem ricf_call_current_argument_mapped[local]:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_chosen_support vs C log_of a fn B E /\
  ricf_certificate_coverage s history certificates /\
  ctx0 = icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
    (readonly_mem_analyze C) fn /\
  ricf_copy_coverage ctx0 fn (log_of fn) a history s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ssa_form fn /\ wf_function fn /\ fn_inst_wf fn /\
  fn_inst_ids_distinct fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occurrence_syntax_origin fn a H /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  occurrence_natural_geometry lo a U B stk s /\
  cb < LENGTH fn.fn_blocks /\
  s.vs_inst_idx < LENGTH (EL cb fn.fn_blocks).bb_instructions /\
  inst = EL s.vs_inst_idx (EL cb fn.fn_blocks).bb_instructions /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL cb fn.fn_blocks) /\
  ps = MAP FST (FILTER (\entry.
    SND entry = [] /\ s.vs_current_bb = (FST entry).rpe_block.bb_label /\
    ricf_selected_position (FST entry).rpe_event
      (FST entry).rpe_block s.vs_inst_idx) history) /\
  callsites = FOLDR (\q m.
    m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites ps ==>
  !id b z. id IN E /\ FLOOKUP B id = SOME (b,z) /\ 0 < z /\
    FST id = a /\ MEM (SOME (b,z)) (MAP (op_prov G) ops) ==>
    (b,z) IN FDOM callsites
Proof
  strip_tac >> rpt strip_tac >>
  qpat_assum `ricf_chosen_support vs C log_of a fn B E`
    (mp_tac o REWRITE_RULE [ricf_chosen_support_def]) >>
  disch_then (qspec_then `id` mp_tac) >> simp[] >> strip_tac >>
  `(b,z) = (p.rpe_db,p.rpe_size)` by
    metis_tac[optionTheory.SOME_11] >>
  `?op. MEM op ops /\ op_prov G op = SOME (p.rpe_db,p.rpe_size)` by
    (fs[MEM_MAP] >> metis_tac[]) >>
  `?j. j < LENGTH ops /\ op = EL j ops` by metis_tac[MEM_EL] >>
  `inst.inst_operands = Label nm::ops` by fs[decode_invoke_def, AllCaseEqs()] >>
  `(p.rpe_db,p.rpe_size) IN
    FDOM (FOLDR (\q m.
      m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites
      (MAP FST (FILTER (\entry.
        SND entry = [] /\ s.vs_current_bb = (FST entry).rpe_block.bb_label /\
        ricf_selected_position (FST entry).rpe_event
          (FST entry).rpe_block s.vs_inst_idx) history)))` by
    (mp_tac (SPEC_ALL ricf_call_passed_support_mapped |>
       Q.INST [`witness` |-> `p`,`j` |-> `SUC j`,
         `log` |-> `log_of (fn:ir_function)`,
         `ostk` |-> `stk0`,`OPG` |-> `PG0`,`OG` |-> `G0`,`OT` |-> `tn0`]) >>
     (impl_tac >- (simp[] >> metis_tac[])) >> simp[]) >>
  metis_tac[]
QED

Theorem ricf_call_install:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_history_certificates vs C log_of stk PG G tn fn inst s a U B
    history certificates /\
  ricf_chosen_support vs C log_of a fn B E /\
  ricf_mapped_support a B E PG G sites /\
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  ctx0 = icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
    (readonly_mem_analyze C) fn /\
  ricf_logged_function_trace ctx0 fn (log_of fn) mid /\
  ricf_copy_coverage ctx0 fn (log_of fn) a history s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\ opaque_use_ok fn /\
  wf_ssa fn /\ ssa_form fn /\ wf_function fn /\ fn_inst_wf fn /\
  fn_inst_ids_distinct fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occurrence_syntax_origin fn a H /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  occurrence_natural_geometry lo a U B stk s /\
  cb < LENGTH fn.fn_blocks /\
  s.vs_inst_idx < LENGTH (EL cb fn.fn_blocks).bb_instructions /\
  inst = EL s.vs_inst_idx (EL cb fn.fn_blocks).bb_instructions /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL cb fn.fn_blocks) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  ps = MAP FST (FILTER (\entry.
    SND entry = [] /\ s.vs_current_bb = (FST entry).rpe_block.bb_label /\
    ricf_selected_position (FST entry).rpe_event
      (FST entry).rpe_block s.vs_inst_idx) history) ==>
  ?callsites ops' args'.
    callsites = FOLDR (\q m.
      m |+ ((q.rpe_db,q.rpe_size),(q.rpe_db,q.rpe_sb,q.rpe_size))) sites ps /\
    decode_invoke (EL s.vs_inst_idx (EL cb mid.fn_blocks).bb_instructions) =
      SOME (nm,ops') /\ eval_operands ops' t = SOME args' /\
    ricf_opaque_params_agree callsites (MAP (op_prov G) ops) args args' /\
    ricf_sites_ok callsites /\ ircf_cross tn (ricf_site_triples callsites) s t /\
    ricf_mapped_support n B E (MAP (op_prov G) ops) FEMPTY callsites /\
    (!s1 ci. enters_block callee cs s1 /\ active_inst callee ci s1 ==>
      ricf_analyzed_map_origins vs C
        (<|cf_fn := fn; cf_inst := inst; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
        (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee ci s1
        (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B callsites /\
      ricf_heterogeneous_map_origins vs C
        (<|cf_fn := fn; cf_inst := inst; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
        (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee ci s1
        (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B callsites)
Proof
  strip_tac >>
  `ricf_certificate_coverage s history certificates` by
    fs[ricf_history_certificates_def] >>
  `active_inst fn inst s` by
    (simp[active_inst_def] >> qexists_tac `EL cb fn.fn_blocks` >>
     simp[EL_MEM] >> metis_tac[lookup_block_label]) >>
  `EVERY (\p. MEM (p,[]) history /\
    s.vs_current_bb = p.rpe_block.bb_label /\
    ricf_selected_position p.rpe_event p.rpe_block s.vs_inst_idx) ps` by
    (qpat_x_assum `ps = _` SUBST_ALL_TAC >>
     simp[EVERY_MEM, MEM_MAP, MEM_FILTER, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  mp_tac (SPEC_ALL ricf_call_selected_payloads_map |>
    Q.INST [`callinst` |-> `inst`]) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `ricf_mapped_support n B E (MAP (op_prov G) ops) FEMPTY callsites` by
    (mp_tac (SPEC_ALL (INST_TYPE
       [alpha |-> ``:string``, beta |-> ``:num # num # num``,
        ``:'c`` |-> ``:num # num # num``, ``:'d`` |-> ``:string``]
       ricf_mapped_support_call) |>
       Q.INST [`child` |-> `n`,`argsPG` |-> `MAP (op_prov G) ops`,
         `callee_sites` |-> `callsites`]) >>
     (impl_tac >-
       (simp[] >> conj_tac
        >- (mp_tac (SPEC_ALL ricf_call_current_argument_mapped) >>
            (impl_tac >- metis_tac[]) >> simp[]) >>
        metis_tac[ricf_call_argument_provenance_keys])) >>
     simp[ricf_mapped_support_def]) >>
  mp_tac (SPEC_ALL ricf_call_actual_argument_values) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexistsl_tac [`callsites`,`ops'`,`args'`] >> fs[] >> metis_tac[]
QED
