(* Support entries retain their own original function's transformation context. *)
Theory readonlyInvokeCopyFwdHeterogeneousSupport
Ancestors
  readonlyInvokeCopyFwdGlobalSupport readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdSupportSeparation readonlyInvokeCopyFwdHistoryOrigin
  readonlyInvokeCopyFwdHistoryAvailability readonlyInvokeCopyFwdHistoryReadExceptions
  readonlyInvokeCopyFwdOccurrenceAlias o1LowerDloadOccurrence occurrenceGeometry
  readonlyInvokeCopyFwdPlan internalReturnCopyFwdPlan invokeCopyFwdCommonDefs
  venomWfProps mem2varProofs finite_map list pred_set pair

Definition ricf_heterogeneous_support_origins_def:
  ricf_heterogeneous_support_origins vs C a fn U stk B E <=>
    !id. id IN E ==> ?ctxP log p pstk PG G tn.
      ricf_history_origin vs C ctxP log p pstk PG G tn /\
      p.rpe_dst = id /\ FLOOKUP B id = SOME (p.rpe_db,p.rpe_size) /\
      ricf_live_owner_function a fn U stk (FST id) p.rpe_fn
End

Theorem ricf_heterogeneous_support_singletons[local]:
  ricf_heterogeneous_support_origins vs C a fn U stk B E <=>
  !id. id IN E ==> ?ctxP.
    ricf_global_support_origins vs C ctxP a fn U stk B {id}
Proof
  simp[ricf_heterogeneous_support_origins_def, ricf_global_support_origins_def]
QED

Theorem ricf_heterogeneous_support_empty:
  ricf_heterogeneous_support_origins vs C a fn U stk B {}
Proof
  simp[ricf_heterogeneous_support_origins_def]
QED

Theorem ricf_heterogeneous_support_activate:
  ricf_heterogeneous_support_origins vs C a fn U stk B E /\
  ricf_history_origin vs C ctxP log p pstk PG G tn /\
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
  FST p.rpe_dst = a /\ p.rpe_fn = fn ==>
  ricf_heterogeneous_support_origins vs C a fn U stk B (E UNION {p.rpe_dst})
Proof
  rw[ricf_heterogeneous_support_origins_def] >>
  metis_tac[ricf_live_owner_function_def, MEM]
QED

Theorem ricf_heterogeneous_support_next:
  ricf_heterogeneous_support_origins vs C a fn U stk B E /\
  occurrence_allocas_ok B a s /\ step_inst fuel C inst s = OK s' ==>
  ricf_heterogeneous_support_origins vs C a fn U stk
    (occurrence_sites_step a B inst s') E
Proof
  rw[ricf_heterogeneous_support_singletons] >>
  metis_tac[ricf_global_support_next]
QED

Theorem ricf_heterogeneous_support_call:
  ricf_heterogeneous_support_origins vs C a fn U stk B E ==>
  ricf_heterogeneous_support_origins vs C n callee
    (<|of_owner := a; of_prov := H; of_params := HP |> :: U)
    (<|cf_fn := fn; cf_inst := inst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk) B E
Proof
  rw[ricf_heterogeneous_support_singletons] >>
  metis_tac[ricf_global_support_call]
QED

Theorem ricf_heterogeneous_support_return:
  ricf_heterogeneous_support_origins vs C a fn (u::U) (f::stk) B E ==>
  ricf_heterogeneous_support_origins vs C u.of_owner f.cf_fn U stk
    (DRESTRICT B {id | FST id <> a}) {id | id IN E /\ FST id <> a}
Proof
  rw[ricf_heterogeneous_support_origins_def, FLOOKUP_DRESTRICT] >>
  first_x_assum drule >> strip_tac >>
  metis_tac[ricf_live_owner_function_pop]
QED

Theorem ricf_heterogeneous_source_support_separation:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ricf_heterogeneous_support_origins vs C a fn U stk B E /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\ icf_is_alloca di /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sv] /\
  FLOOKUP B (a,ai.inst_id) = SOME (sb,len) /\
  occurrence_natural_geometry lo a U B stk s ==>
  (a,ai.inst_id) NOTIN E /\
  !q. q < len ==> sb+q NOTIN ricf_support_bytes B E
Proof
  strip_tac >>
  `(a,ai.inst_id) NOTIN E` by
    (strip_tac >> fs[ricf_heterogeneous_support_singletons] >>
     first_x_assum drule >> strip_tac >>
     drule_all ricf_global_source_support_separation >> simp[]) >>
  simp[] >> rpt strip_tac >> gvs[ricf_support_bytes_def] >>
  `0 < len /\ 0 < z` by decide_tac >>
  `(a,ai.inst_id) <> id` by (strip_tac >> gvs[]) >>
  drule_all occurrence_geometry_sites_disjoint >> decide_tac
QED

Theorem ricf_heterogeneous_located_copy_source_support_agree:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ssa_form fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  ricf_heterogeneous_support_origins vs C a fn U stk B E /\
  occurrence_natural_geometry lo a U B stk s /\
  ricf_support_agree B E tn0 s t ==>
  ?dst sv z sa db sb.
    (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands =
      [Var dst;Var sv;Lit z] /\
    eval_operands (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands s =
      SOME [n2w db;n2w sb;z] /\
    MEM sa (fn_insts fn) /\ sa.inst_opcode = ALLOCA /\
    sa.inst_outputs = [sv] /\ sa.inst_operands = [Lit z] /\
    FLOOKUP B (a,sa.inst_id) = SOME (sb,w2n z) /\
    (a,sa.inst_id) NOTIN E /\
    (!q. q < w2n z ==> sb+q NOTIN ricf_support_bytes B E) /\
    (!q. q < w2n z /\ sb+q NOTIN tn0.t_mem ==>
      read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory)
Proof
  strip_tac >> drule_all ricf_located_event_operands_available >> strip_tac >>
  drule_all ricf_located_event_original_destination_alloca >> strip_tac >>
  drule_all ricf_heterogeneous_source_support_separation >> strip_tac >>
  `sb+w2n z <= s.vs_alloca_next` by metis_tac[occurrence_geometry_site_bounds] >>
  metis_tac[ricf_support_separated_source_agree]
QED
