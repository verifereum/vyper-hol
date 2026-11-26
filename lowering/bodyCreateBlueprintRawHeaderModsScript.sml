(* Read the length and advance to the payload of a prepared bytes buffer. *)
Theory bodyCreateBlueprintRawHeaderMods
Ancestors
  bodyFullCreateHeld bodyForRangeScalarFrameMods assignTuplePtrLoadStep
  bodyFullPathHistory bodyFullIfExpReach exprSimWordArgs exprLoweringProps
  stateFrame stateRelProj bodyMemoryDefs bodyPtrDefs bodyFullShadowBodyInv
  freshWrites loweringShapeDefs venomState ptrDiscipline finite_map words
  vyperStorageFootprint fragExec fragGasOriginPtr venomInst exprLowering

Triviality blueprint_header_unchanged:
  (z with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s ==>
  state_frame z = state_frame (s with vs_inst_idx := z.vs_inst_idx) /\
  z.vs_memory = s.vs_memory /\ z.vs_allocas = s.vs_allocas /\
  z.vs_alloca_next = s.vs_alloca_next /\ z.vs_fmp = s.vs_fmp /\
  z.vs_initial_fmp = s.vs_initial_fmp /\ z.vs_halted = s.vs_halted /\
  z.vs_data_section = s.vs_data_section /\ z.vs_call_ctx = s.vs_call_ctx /\
  z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
  z.vs_immutables = s.vs_immutables
Proof
  simp[state_frame_def,venom_state_component_equality]
QED

Triviality blueprint_header_linked_frame:
  stmt_state_rel H ctx func cenv cx es s /\
  immutable_frame_mods func cenv cx es s /\
  ghost_inv_at_mods (DF H) lo d cenv cx es G tn s /\
  state_frame z = state_frame (s with vs_inst_idx := z.vs_inst_idx) /\
  z.vs_memory = s.vs_memory /\ z.vs_allocas = s.vs_allocas /\
  z.vs_alloca_next = s.vs_alloca_next /\ z.vs_data_section = s.vs_data_section /\
  z.vs_call_ctx = s.vs_call_ctx /\ z.vs_accounts = s.vs_accounts /\
  z.vs_transient = s.vs_transient /\ z.vs_immutables = s.vs_immutables /\
  tz.t_mem = tn.t_mem /\ tz.t_stor = tn.t_stor /\ tz.t_trans = tn.t_trans /\
  tz.t_imm = tn.t_imm /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) ==>
  stmt_state_rel H ctx func cenv cx es z /\
  immutable_frame_mods func cenv cx es z /\
  ghost_inv_at_mods (DF H) lo d cenv cx es Gz tz z
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by simp[] >>
  conj_tac
  >- (irule stmt_state_rel_old_vars_frame_ptr >> qexistsl [`s`,`sa`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule immutable_frame_mods_exterior_frame >> qexistsl [`es`,`s`,`sa`] >>
      rpt conj_tac >> (REFL_TAC ORELSE first_assum ACCEPT_TAC)) >>
  irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G`,`es`,`s`,`sa`,`tn`] >>
  rpt conj_tac >> (REFL_TAC ORELSE first_assum ACCEPT_TAC)
QED

Triviality blueprint_header_saved_frames:
  sa.cs_next_var <= sb.cs_next_var /\
  z.vs_memory = s.vs_memory /\ z.vs_allocas = s.vs_allocas /\
  z.vs_alloca_next = s.vs_alloca_next /\ tz.t_mem = tn.t_mem /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
  return_buf_frame d cenv sa s ==>
  wb_frame cenv es es sa s z /\
  ghost_kept_at lo cenv es sa G tn s Gz tz /\
  return_buf_frame d cenv sb z
Proof
  strip_tac >>
  `!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
          lookup_var x z = SOME w` by simp[] >>
  conj_tac
  >- (irule wb_frame_readonly_tail >> qexistsl [`sa`,`s`] >> simp[wb_frame_refl]) >>
  conj_tac >- simp[ghost_kept_at_def] >>
  irule return_buf_frame_frame >> qexistsl [`cenv`,`s`,`sa`] >> simp[]
QED

Theorem blueprint_raw_header_frame_mods:
  emit_op MLOAD [Var p] sa = (len,sm) /\ emit_op ADD [Var p;Lit 32w] sm = (data,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ not_fresh_at sa p /\
  eval_operand (Var p) s = SOME (n2w b) /\ mload b s = n2w (LENGTH bs) /\
  ptr_covers G tn p s (32 + LENGTH bs) /\ b + 32 < dimword (:256) /\
  b + 32 + LENGTH bs <= s.vs_alloca_next /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  (!i. b <= i /\ i < b + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) ==>
  ?l q z Gz tz.
    len = Var l /\ data = Var q /\ not_fresh_at sb l /\ not_fresh_at sb q /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    eval_operand len z = SOME (n2w (LENGTH bs)) /\ op_prov Gz len = NONE /\ op_taint tz len = {} /\
    eval_operand data z = SOME (n2w (b + 32)) /\ op_prov Gz data = op_prov G (Var p) /\
    op_taint tz data = {} /\ ptr_covers Gz tz q z (LENGTH bs) /\
    b + 32 + LENGTH bs <= z.vs_alloca_next /\
    mem_bytes_at (b + 32) (LENGTH bs) z.vs_memory = bs /\
    (!i. b + 32 <= i /\ i < b + 32 + LENGTH bs ==> i NOTIN tz.t_mem) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    z.vs_memory = s.vs_memory /\ z.vs_allocas = s.vs_allocas /\
    z.vs_alloca_next = s.vs_alloca_next /\ tz.t_mem = tn.t_mem /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv es es sa s z /\ ghost_kept_at lo cenv es sa G tn s Gz tz /\
    return_buf_frame d cenv sb z /\ local_ptrs_reserved cenv sb /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!fn inst u. frag_reachable ctx func z fn inst u ==> dalloca_fmp_headroom inst u) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es z /\ immutable_frame_mods func cenv cx es z /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es Gz tz z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  drule_then (assume_tac o CONJUNCT2) stmt_state_rel_local_ptrs_alloca >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  drule_all_then (qspec_then `PG` (qx_choosel_then [`l`,`q`,`z`,`Gz`,`tz`]
    (map_every assume_tac o CONJUNCTS))) blueprint_raw_header_path >>
  drule_then (map_every assume_tac o CONJUNCTS) blueprint_header_unchanged >>
  qpat_assum `tz with t_var := _ = tn` mp_tac >>
  simp_tac (srw_ss()) [taint_component_equality] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`MLOAD`,`[Var p]`,`sa`] mp_tac ci_mono_emit_op >>
     qspecl_then [`ADD`,`[Var p; Lit 32w]`,`sm`] mp_tac ci_mono_emit_op >>
     asm_rewrite_tac[pairTheory.SND,ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es es sa s z /\ ghost_kept_at lo cenv es sa G tn s Gz tz /\
   return_buf_frame d cenv sb z` by
    (irule blueprint_header_saved_frames >> simp[]) >>
  suspend "endpoint"
QED

Resume blueprint_raw_header_frame_mods[endpoint]:
  qpat_assum `!D explicit. gas_origin_ptr_path _ _ [] (OK z,Gz,tz)`
    (qspecl_then [`DF (storage_trace_horizon es.storage_trace)`,`ARB`] assume_tac) >>
  `alloca_history func z` by (drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  `!fn inst u. frag_reachable ctx func z fn inst u ==> dalloca_fmp_headroom inst u` by
    (drule (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_origin_ptr_path_dalloca_fmp_headroom) >>
     disch_then drule >> disch_then drule >> disch_then ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (pure_rewrite_tac[allocas_below_fmp_def] >>
     qpat_assum `z.vs_allocas = s.vs_allocas` (once_rewrite_tac o single) >>
     qpat_assum `z.vs_initial_fmp = s.vs_initial_fmp` (pure_rewrite_tac o single) >>
     qpat_assum `z.vs_fmp = s.vs_fmp` (once_rewrite_tac o single) >>
     first_assum (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def])) >>
  `local_ptrs_reserved cenv sb` by (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `op_taint tz data = {}` by fs[ptr_covers_def] >>
  `b + 32 + LENGTH bs <= z.vs_alloca_next /\ ~z.vs_halted` by simp[] >>
  qexistsl [`l`,`q`,`z`,`Gz`,`tz`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) blueprint_header_linked_frame >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise blueprint_raw_header_frame_mods
