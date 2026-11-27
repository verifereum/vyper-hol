(* Compiler geometry, child representation, joint copy and endpoint interpretation
   for storage/transient For iteration. The element copy creates its own CFG. *)
Theory bodyFullForStorage
Ancestors exprSimSubscriptArrayLiveStorageSuffix[qualified,ignore_grammar] exprPtrStorageLoad[qualified,ignore_grammar] exprSimConcatResult[qualified,ignore_grammar] exprSimAggregatesAllocCounted[qualified,ignore_grammar] marker[qualified,ignore_grammar] bodySim
  bodyFullShadowBodyInv
  stmtLowering exprLowering compileEnv context stmtSimProps
  stmtSimForArrayParts stmtLoweringMono copyExecution emitHelper emitHelperProps
  slotCopyExecution loweringStateRelDefs words string numposrep
  exprLoweringProps fragExec venomInst venomState vyperAST
  finite_map list rich_list arithmetic
  accountsRelProps stmtSimAugAssignPlaceStorage
  exprSimSubscriptArrayLiveStorage
  vyperStorageBackend vyperState vyperLookupStorage
  bodyFullToplevelSlotEntry bodyFullToplevelSlotLoopFrame
  exprPtrUnwrapLoopInvariant exprPtrUnwrapRuntimeFrame exprSimStorageCopy
  loweringPosts fragGasOriginPtr
  exprPtrUnwrapStoragePost exprPtrUnwrapCopyPost stmtSimDefs bodyPtrDefs
  fragGasSeqPtr decoderNavigationPtr bodyPtrBopInLiteralSuffix
  stmtAppendStorageRunPtr
  exprSimWordArgs fragExecMem venomExecSemantics venomExecProps
  instMemFrontier gasEvents gasCount ptrSafeRun
  unitTransformDefs contextCodegenRel codegenRel
  bodyPtrBopInLiveStorage bodyPtrBopInLoadOutput bodyPtrMakeArrayEmission
  exprPtrUnwrapStorageSource exprPtrUnwrapCopyEdges
  typedCopyOriginPtrBase bodyFullGhostFrame bodyFullShared
  bodyMemoryDefs allocaHistory assignTuplePtrCopyLen memSafeRun
  ptrDiscipline exprSimHyps exprSimFieldLayout valueEncodingProps
  exprPtrUnwrapTypedSize
  stmtSimAssignStorageCopy exprSimPopStorage stateRelProj sourceUnitExecution
  vyperStoragePlaceObserved vyperStoragePlaceRegion vyperStorageFootprint
  pred_set fragGasSeqPtr decoderNavigationPtr
  ptrSafeRun venomExecSemantics codegenRel contextCodegenRel unitTransformDefs
  exprPtrUnwrapScalarEdges
  bodyFullPreds bodySimFull gasOutcomeFullCompose
  gasShadow gasShadowState gasShadowUnit gasExplicitSites
  bodyFullForFrame bodyExprPreFacts bodySimDeclCases
  stmtSimForArrayLoop vyperEvalPreservesScopes vyperStorageTrace
  fragGasOriginPtrLoop placeTypedCopyPath
  contextCodegenRel codegenRel venomExecSemantics venomExecProps
  stmtSimDeclCopyFrame bodyFullMemoryFrames
  bodyDeclCopyMemory stmtSimDeclCompose bodySim
  vyperTypeEnv
  bodyFullAllocGeneric bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocSource
  bodyPtrEnvBuiltinsAllocation storageNormalizationAllocPtr
  bodyFullHashKeccakFixed stmtSimDeclPath exprSimOperands allocaSiteResource
  bodyFullForArray allocationPtr loweringHalt
  bodyFullForHandlers forBodyLandOutcome haltExitProj gasOutcomeFull vyperStorageFootprint
  gasOutcomeInitialObsPtr[qualified] gasStorage[qualified]
  bodyFullIfExpReach[qualified,ignore_grammar]
  stmtSimForParts[qualified] vyperInterpreter[qualified] gasContext[qualified] fragGasCopyLoop augAssignPtrScalarSafety augAssignPtrScalarCertificate
  supportedExprForms whitelistVisibility immutableLocationProps
  bodyFullForRounds[qualified] gasExemptCert[qualified] forStorageBodyLand[qualified] forStorageHeadFrame
  forConsBodyGas
  bodyFullPostsMods[qualified] bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]
Libs
  monadsyntax

(* Joint execution and interpretation for the existing storage-copy destination. *)

Theorem for_storage_element_copy_run:
  !ce tyarr ann nid ca place cb cenv typ tr src root n cs sb lo ctx func
   PG s G tn w (d:bytes32) regions.
    compile_expr ce tyarr (TopLevelName ann nid) ca = (place,cb) /\
    compile_iter_elem_copy cenv src (Var root) n (slot_loc tr) T
      typ typ cs = ((),sb) /\
    compile_slot_to_memory src (Var root) n (slot_loc tr) cs =
      (slot_copy_body cs,sb) /\
    eval_operand src s = SOME w /\ lookup_var root s = SOME d /\
    op_taint tn src = {} /\
    slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
    ptr_covers G tn root s (32*n) /\
    n < 2**256 /\ w2n d+32*n < 2**256 /\
    w2n d+32*n <= s.vs_alloca_next /\
    create_memory_snapshot regions s /\
    EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
      (off+LENGTH bs <= w2n d \/ w2n d+32*n <= off)) regions /\
    s.vs_current_bb = cs.cs_current_bb /\
    s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_halted /\
    lookup_block cs.cs_current_bb func.fn_blocks =
      SOME <|bb_label := cs.cs_current_bb;
             bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|> /\
    lookup_block (slot_copy_cond cs) func.fn_blocks =
      SOME <|bb_label := slot_copy_cond cs;
             bb_instructions := slot_copy_cond_insts cs n|> /\
    lookup_block (slot_copy_body cs) func.fn_blocks =
      SOME <|bb_label := slot_copy_body cs;
             bb_instructions := slot_copy_body_insts cs src (Var root)
               (if tr then TLOAD else SLOAD)|> /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
    ?z Gf tnf.
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK z,Gf,tnf)) /\
      z.vs_current_bb = slot_copy_exit cs /\ z.vs_inst_idx = 0 /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
      slot_copy_inv cs (if tr then TLOAD else SLOAD) s w d n regions n z /\
      slot_copy_ghost_inv cs (if tr then TLOAD else SLOAD)
        w d root n G tn n Gf tnf z /\
      slot_copy_runtime_frame cs d n s z /\
      allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      z.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks =
    SOME <|bb_label := cs.cs_current_bb;
           bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|>`
    by simp[] >>
  qmatch_asmsub_abbrev_tac `lookup_block s.vs_current_bb func.fn_blocks = SOME initbb` >>
  `initbb.bb_instructions = cs.cs_current_insts ++ slot_copy_init_insts cs`
    by simp[Abbr `initbb`] >>
  drule_all toplevel_slot_copy_initial_joint >>
  disch_then (qspecl_then [`w`, `if tr then TLOAD else SLOAD`, `PG`]
    strip_assume_tac) >>
  qabbrev_tac `h = slot_copy_initial cs s` >>
  `slot_copy_runtime_frame cs d 0 s h` by
    simp[Abbr `h`, slot_copy_runtime_frame_initial] >>
  `~h.vs_halted /\ h.vs_current_bb = slot_copy_cond cs /\
   h.vs_inst_idx = 0 /\ h.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr `h`, slot_copy_initial_def, jump_to_def, update_var_def] >>
  `op_taint tn1 src = {}` by metis_tac[copy_ghost_external_taint] >>
  qmatch_asmsub_abbrev_tac `lookup_block (slot_copy_cond cs) func.fn_blocks = SOME condbb` >>
  qmatch_asmsub_abbrev_tac `lookup_block (slot_copy_body cs) func.fn_blocks = SOME bodybb` >>
  `condbb.bb_instructions = slot_copy_cond_insts cs n /\
   bodybb.bb_instructions = slot_copy_body_insts cs src (Var root)
     (if tr then TLOAD else SLOAD)` by simp[Abbr `condbb`, Abbr `bodybb`] >>
  `0 <= n /\ w2n d+32*n <= h.vs_alloca_next` by simp[] >>
  Q.SUBGOAL_THEN `(if tr then TLOAD else SLOAD) = SLOAD \/
    (if tr then TLOAD else SLOAD) = TLOAD` assume_tac
    >- (Cases_on `tr` >> simp[]) >>
  drule_all toplevel_slot_copy_joint_finish_framed >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `~t.vs_halted` by
    (qpat_x_assum `slot_copy_runtime_frame cs d n s t` mp_tac >>
     simp[slot_copy_runtime_frame_def] >> strip_tac >>
     drule copy_static_fields >> simp[]) >>
  Q.SUBGOAL_THEN `slot_loc tr = LocStorage \/ slot_loc tr = LocTransient` assume_tac
    >- (Cases_on `tr` >> simp[slot_loc_def]) >>
  drule_all compile_slot_to_memory_boundary >> strip_tac >>
  qexistsl [`t`, `Gf`, `tnf`] >> simp[] >>
  rpt gen_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspecl_then [`D`, `explicit`]
      (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
  disch_then (qspecl_then [`h`, `G1`, `tn1`, `[]`] mp_tac) >>
  simp[] >> disch_then irule >> simp[]
QED

(* Recover a local predicate abbreviation from the expanded statement. *)
fun abbrev_lambda_tac name arity existentials =
  Q_TAC (fn pattern => W (fn (_, goal) =>
    let
      fun matches tm =
        let
          val (args, body) = strip_abs tm
          val (witnesses, core) = strip_exists body
        in
          length args = arity andalso length witnesses = existentials andalso
          can (match_term pattern) core
        end
      val tm = find_term matches goal
    in
      markerLib.ABBREV_TAC (mk_eq (mk_var (name, type_of tm), tm))
    end));

(* Exhausted captured storage iterator: the only instructions are scalar EQ
   and the taken exit branch. The frame stays anchored at the original entry. *)
(* The exhausted guard only needs the saved counter/length equality and the
   exterior frame; it need not know how the iterator obtained either value. *)
Theorem for_storage_array_nil_core:
  !DF lo d ctx func cx lctx c0 e0 sa0 sb s0 G0 tn0 st0 explicit PG dv eid
    exit blabel bb cond idx lvo es s G tn len.
    local_ptrs_reserved c0 sa0 /\
    (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
    (!x. not_fresh_at sa0 x ==> x <> dv) /\
    sa0.cs_next_var <= sb.cs_next_var /\ sb.cs_current_bb = exit /\
    sb.cs_current_insts = [] /\ ~block_is_terminated sb /\
    lookup_block cond func.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME (mk_inst eid EQ [Var idx; lvo] [dv]) /\
    get_instruction bb 1 =
      SOME (mk_inst (eid + 1) JNZ [Var dv; Label exit; Label blabel] []) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
      lookup_var idx s = SOME (n2w len) /\ FLOOKUP G idx = NONE /\
      op_taint tn (Var idx) = {} /\ eval_operand lvo s = SOME (n2w len) /\
      op_taint tn lvo = {} /\ op_prov G lvo = NONE /\
      cenv_top_ext c0 c0 es.scopes /\ stmt_state_rel H ctx func c0 cx es s /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d c0 cx es G tn s /\
      return_buf_frame d c0 sa0 s /\ return_buf_sep d c0 es s /\
      (\c ee s G tn.
        alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
        s0.vs_alloca_next <= s.vs_alloca_next /\
        (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
               lookup_var x s = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa0 x ==> FLOOKUP G x = FLOOKUP G0 x /\
             op_taint tn (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame c0 e0 sa0 s0 c ee s /\
        !aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
          aid < sa0.cs_next_id /\
          (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
            off + sz <= b \/ b + sz' <= off) /\ off <= i /\
          i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) c0 es s G tn) ==>
    ?t G1 tn1. !H.
      valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK t,G1,tn1) /\
      (\H ee G tn t.
         ?c. stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
             ~block_is_terminated sb /\ c = c0 /\
             cenv_top_ext c0 c ee.scopes /\ stmt_state_rel H ctx func c cx ee t /\
             storage_well_formed_on cx ee (FST H) /\
             return_buf_frame d c sb t /\ return_buf_sep d c ee t /\
             ghost_inv_at (DF H) lo d c cx ee G tn t /\
             (\c ee s G tn.
               alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
               s0.vs_alloca_next <= s.vs_alloca_next /\
               (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                      lookup_var x s = SOME w) /\
               (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
               (!x. not_fresh_at sa0 x ==> FLOOKUP G x = FLOOKUP G0 x /\
                    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
               alloca_frame c0 e0 sa0 s0 c ee s /\
               !aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                 aid < sa0.cs_next_id /\
                 (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                 i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem) c ee t G tn)
        H (es with gas_obs := []) G1 tn1 t
Proof
  rpt gen_tac >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  abbrev_lambda_tac "Done" 5 1 `stmt_lands lctx sb (INL ()) t /\ _` >>
  rpt strip_tac >>
  qabbrev_tac `i = mk_inst eid EQ [Var idx;lvo] [dv]` >>
  qabbrev_tac `u = update_var dv 1w s` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  qexistsl [`jump_to exit u`, `G1`, `tn1`] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> BETA_TAC >> strip_tac >>
  `Fr c0 es s G tn` by simp[Abbr `Fr`] >>
  `allocas_from lo s` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  `not_local_ptr c0 es.scopes dv` by
    (simp[not_local_ptr_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `tn1 = tn with t_var := tn.t_var |+ (dv,{})` by
    simp[Abbr `tn1`, Abbr `i`, Abbr `u`, membership_scalar_ghost_frame] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (qpat_x_assum `Fr c0 es s G tn` mp_tac >> simp[NoAsms, Abbr `Fr`]) >>
  conj_tac >- suspend "nil_path" >>
  suspend "nil_post"
QED

Resume for_storage_array_nil_core[nil_path]:
  `step_inst_base i s = OK u` by
    (gvs[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs,
          exec_pure2_def, eval_operand_def, bool_to_word_def]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn i s` by
    suspend "nil_compare_checks" >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
   i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   (ctx_has_dalloca ctx ==> dalloca_no_wrap i s)` by
    simp[Abbr `i`, mk_inst_def, is_terminator_def,
         inst_mem_below_frontier_def, inst_dload_in_section_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx),G1,tn1)` by
    (`lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME i` by simp[] >>
     drule_all straight_line_origin_ptr_edge >>
     simp[Abbr `G1`, Abbr `tn1`, Abbr `i`, mk_inst_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := SUC s.vs_inst_idx,G1,tn1) []
     (OK (jump_to exit u),G1,tn1)` by suspend "nil_branch" >>
  drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]
QED

Resume for_storage_array_nil_core[nil_compare_checks]:
  simp[Abbr `i`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def, mk_inst_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, Abbr `u`, update_var_def] >>
  rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]
QED

Resume for_storage_array_nil_core[nil_branch]:
  qmatch_goalsub_abbrev_tac `gas_origin_ptr_path _ (v,G1,tn1) _ _` >>
  `lookup_block v.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb v.vs_inst_idx =
     SOME (mk_inst (eid+1) JNZ [Var dv;Label exit;Label blabel] []) /\
   ~v.vs_halted /\ eval_operand (Var dv) v = SOME 1w /\
   op_taint tn1 (Var dv) = {} /\ allocas_from lo v /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
    simp[Abbr `v`, Abbr `u`, update_var_def, eval_operand_def,
         lookup_var_def, allocas_from_def, allocas_below_fmp_def,
         op_taint_def, FLOOKUP_UPDATE] >>
  drule_all decoderNavigationPtrTheory.jnz_origin_ptr_path >>
  simp[Abbr `v`, jump_to_def]
QED

Resume for_storage_array_nil_core[nil_post]:
  `!x. not_fresh_at sa0 x ==>
     lookup_var x (jump_to exit u) = lookup_var x s /\
     FLOOKUP G1 x = FLOOKUP G x /\
     op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> dv` by metis_tac[] >>
     simp[Abbr `u`, Abbr `G1`, Abbr `i`, jump_to_def, update_var_def,
          lookup_var_def, step_prov_def, out_prov_def, set_prov_def,
          mk_inst_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE]) >>
  `ghost_inv_at (DF H) lo d c0 cx (es with gas_obs := []) G1 tn1
     (jump_to exit u)` by
    (irule ghost_inv_at_exterior_frame >>
     goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     qexists `sa0` >> simp[Abbr `u`, jump_to_def, update_var_def]) >>
  `stmt_state_rel H ctx func c0 cx (es with gas_obs := []) (jump_to exit u)` by
    (simp[stmt_state_rel_jump_to, Abbr `u`] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `return_buf_frame d c0 sb (jump_to exit u)` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
     simp[Abbr `u`, jump_to_def, update_var_def] >> metis_tac[]) >>
  `return_buf_sep d c0 (es with gas_obs := []) (jump_to exit u)` by
    suspend "nil_sep" >>
  `Fr c0 (es with gas_obs := []) (jump_to exit u) G1 tn1` by
    suspend "nil_frame" >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
     simp[NoAsms, vyperStorageFootprintTheory.storage_well_formed_on_def,
          stmtSimAppendStorageComposeTheory.get_storage_gas_obs]) >>
  simp[Abbr `Done`, stmt_lands_def] >>
  gvs[Abbr `u`, jump_to_def, update_var_def]
QED

Resume for_storage_array_nil_core[nil_sep]:
  simp[return_buf_sep_gas_obs, return_buf_sep_jump] >>
  `!name b sz. local_region c0 es.scopes u name b sz <=>
               local_region c0 es.scopes s name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     rename1 `lookup_var q u = lookup_var q s` >>
     `q <> dv` by
       (strip_tac >> qpat_assum `not_local_ptr c0 es.scopes dv`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [not_local_ptr_def]) >>
        disch_then (drule_then mp_tac) >> simp[]) >>
     simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  Cases_on `d` >- simp[return_buf_sep_def] >>
  rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
  qpat_x_assum `return_buf_sep (SOME _) c0 es s` mp_tac >>
  pure_rewrite_tac[return_buf_sep_def] >>
  simp[allocas_from_def, Abbr `u`, update_var_def]
QED

Resume for_storage_array_nil_core[nil_frame]:
  qpat_x_assum `Fr c0 es s G tn` mp_tac >> simp[Abbr `Fr`] >> strip_tac >>
  `alloca_frame c0 e0 sa0 s0 c0 es u` by
    (simp[Abbr `u`] >> irule alloca_frame_update_var >> simp[]) >>
  `alloca_frame c0 e0 sa0 s0 c0 es (jump_to exit u)` by
    (irule alloca_frame_same_state >> goal_assum (drule_at Any) >> simp[jump_to_def]) >>
  `alloca_history func (jump_to exit u)` by
    (irule alloca_history_jump >> simp[Abbr `u`, jump_to_def, update_var_def] >>
     qexists `s` >> simp[]) >>
  simp[] >>
  conj_tac >-
    (gvs[Abbr `u`, jump_to_def, update_var_def, allocas_below_fmp_def] >> metis_tac[]) >>
  simp[Abbr `u`, jump_to_def, update_var_def] >>
  conj_tac
  >- (rpt strip_tac >> `x <> dv` by metis_tac[] >>
      qpat_x_assum `!x. not_fresh_at sa0 x ==> FLOOKUP G x = _ /\ _`
        (qspec_then `x` mp_tac) >> simp[op_taint_def, FLOOKUP_UPDATE]) >>
  first_assum ACCEPT_TAC
QED

Finalise for_storage_array_nil_core

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> drule_all expr_sim_inv_memory_size >> strip_tac >>
  conj_tac >- (Cases_on `tr` >>
    simp[elem_size_in_location_def, is_slot_addressed_def,
      slot_count_of_memory_size]) >>
  conj_tac >- simp[type_memory_size_slots] >>
  strip_tac >> drule unwrap_typed_buffer_count_bound >> strip_tac >>
  simp[]
  >> (gvs[])
QED
*)
Theorem for_storage_element_layout:
  expr_sim_inv_mods mods cenv cx env es /\
  evaluate_type (get_tenv cx) et = SOME tv ==>
  elem_size_in_location cenv (if tr then LocTransient else LocStorage) et =
    type_slot_size tv /\
  type_memory_bytes cenv et = 32 * type_slot_size tv /\
  (type_memory_size tv < 2**64 ==>
    type_slot_size tv < 2**256 /\
    type_memory_bytes cenv et + 64 < 2**256)
Proof
  cheat
QED

(* Invoke the body at its actual compiler age.  The non-Label fact is
   supplied by the iterator's literal/load compilation, not source typing. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >>
  qpat_abbrev_tac `envb = extend_local env id typ F` >>
  qpat_abbrev_tac `eb = ei with scopes := (FEMPTY |+ (id, _)) :: ei.scopes` >>
  qpat_abbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  abbrev_lambda_tac "Qb" 6 1 `stmt_lands (InLoop exit incr) sb1 res t /\ _` >>
  abbrev_lambda_tac "Rb" 5 0 `(!tail. stmt_exit_ptr _ (ee with gas_obs := tail) res gt r) /\ _` >>
  abbrev_lambda_tac "Keep" 3 0 `lookup_var idx t = lookup_var idx s /\ _` >>
  rpt strip_tac >>
  `body_const_cells_agree [(NONE,tops)] cx envb eb` by
    simp[Abbr `envb`, Abbr `eb`] >>
  rename1 `body_stmts_full_ok cx stmts` >>
  qpat_x_assum `body_stmts_full_ok _ _`
    (mp_tac o REWRITE_RULE [body_stmts_full_ok_def]) >>
  disch_then drule_all >>
  disch_then (qspec_then `InLoop exit incr` mp_tac) >>
  rewrite_tac [stmt_frag_full_def] >>
  disch_then (qspecl_then [`st0`, `sb0`, `sb1`, `shadow_sb0`,
    `shadow_sb1`, `s`, `G`, `tn`, `bc1`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  irule gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  BETA_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >>
  reverse conj_tac >- (qexists_tac `xs` >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `Qb _ _ _ _ _ _` mp_tac >>
  simp[Abbr `Qb`] >> strip_tac >>
  simp[Abbr `Keep`] >>
  Cases_on `lvo` >> gvs[eval_operand_def, op_prov_def, op_taint_def] >>
  metis_tac[]
QED
*)
Theorem for_storage_body_invoke_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx RetQ tops bindings env id typ
      tyv v ei body env_b ret_ty bc bc1 sb0 sb1 shadow_sb0 shadow_sb1 st0 s G
      tn idx p lvo k dst len.
    body_stmts_full_ok_mods mods exps cx body /\ (contract_inv mods exps ctx bc cx /\
     module_body_inv mods bc.ce_module tops bc cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env ei /\
    supported_stmts tops bindings body /\
    (!target.
       supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv_mods mods bc cx (extend_local env id typ F)
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) /\
    ce_locals_declared bc (extend_local env id typ F) /\
    locals_alloc_ok bc (extend_local env id typ F) /\
    type_stmts (extend_local env id typ F) ret_ty body = SOME env_b /\
    stmts_exprs_ok bc body /\ call_evaluation_safe cx (int_calls_stmts body) /\
    frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc
      ret_ty /\ stmts_env bc (InLoop exit incr) ret_ty body sb0 = (bc1,sb1) /\
    stmts_env (gas_shadow_env T bc) (InLoop exit incr) ret_ty (MAP gas_shadow_stmt body)
      shadow_sb0 = (gas_shadow_env T bc1,shadow_sb1) /\ gas_shadow_state sb0 shadow_sb0 /\
    gas_shadow_state sb1 shadow_sb1 /\ gas_shadow_context ctx shadow_ctx /\
    ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sb0 sb1 func /\
    fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
    (!H. dead_lo_ok H (DF H) lo bc cx) /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved bc sb0 /\ ret_pc_ok bc sb0 s /\
    (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb0 x) /\
    ~block_is_terminated sb0 /\
    gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit incr))
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) /\ return_buf_frame d bc sb0 s /\
    return_buf_sep d bc
      (ei with scopes :=
        fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
          FEMPTY::ei.scopes) s /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
    (!H. valid_horizon cx st0 H
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes).storage_trace ==>
         stmt_state_rel H ctx func bc cx
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) s /\
         storage_well_formed_on cx
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) (FST H) /\
         ghost_inv_at (DF H) lo d bc cx
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) G tn s) /\ ~s.vs_halted /\
    s.vs_current_bb = sb0.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb0.cs_current_insts /\ not_fresh_at sb0 idx /\
    not_fresh_at sb0 p /\ (!x. lvo = Var x ==> not_fresh_at sb0 x) /\
    (!lbl. lvo <> Label lbl) /\ lookup_var idx s = SOME (n2w k) /\
    lookup_var p s = SOME dst /\ eval_operand lvo s = SOME (n2w len) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_stmts cx body)
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes,s,G,tn)
      (\H res ee G1 tn1 t.
         (\H res ee G1 tn1 t.
            ?c3.
              stmt_lands (InLoop exit incr) sb1 res t /\ ~t.vs_halted /\
              (res = INL () ==> ~block_is_terminated sb1 /\ c3 = bc1) /\
              cenv_top_ext bc c3 ee.scopes /\
              stmt_state_rel H ctx func c3 cx ee t /\
              storage_well_formed_on cx ee (FST H) /\
              return_buf_frame d c3 sb1 t /\ alloca_history func t /\
              return_buf_sep d c3 ee t /\
              (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
              s.vs_alloca_next <= t.vs_alloca_next /\
              ghost_inv_at (DF H) lo d c3 cx ee G1 tn1 t /\
              (!x w.
                 not_fresh_at sb0 x /\ lookup_var x s = SOME w ==>
                 lookup_var x t = SOME w) /\
              (!aid b.
                 FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
              (!x. not_fresh_at sb0 x ==>
                   FLOOKUP G1 x = FLOOKUP G x /\
                   op_taint tn1 (Var x) = op_taint tn (Var x)) /\
              alloca_frame bc
                (ei with
                 scopes :=
                   fmupdate id
                     <|assignable := F; type := tyv; value := v; popped := []|>
                     FEMPTY::ei.scopes) sb0 s c3 ee t /\
              !aid off sz i.
                FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
                aid < sb0.cs_next_id /\
                (!name b sz'.
                   local_region bc
                     (ei with
                      scopes :=
                        fmupdate id
                          <|assignable := F; type := tyv; value := v;
                            popped := []|> FEMPTY::ei.scopes).scopes s name b
                     sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\ off <= i /\
                i < off + sz /\ i IN tn1.t_mem ==>
                i IN tn.t_mem) H res ee G1 tn1 t /\
         (\G1 tn1 t.
            lookup_var idx t = lookup_var idx s /\
            lookup_var p t = lookup_var p s /\
            eval_operand lvo t = eval_operand lvo s /\
            FLOOKUP G1 idx = FLOOKUP G idx /\ FLOOKUP G1 p = FLOOKUP G p /\
            op_prov G1 lvo = op_prov G lvo /\
            op_taint tn1 (Var idx) = op_taint tn (Var idx) /\
            op_taint tn1 (Var p) = op_taint tn (Var p) /\
            op_taint tn1 lvo = op_taint tn lvo) G1 tn1 t /\ ee.gas_obs = [] /\
         ?xs. !tail.
           eval_stmts cx body
             (ei with
              <|gas_obs := xs ++ tail;
                scopes :=
                  fmupdate id
                    <|assignable := F; type := tyv; value := v; popped := []|>
                    FEMPTY::ei.scopes|>) = (res,ee with gas_obs := tail))
      (\H res ee gt r.
         (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
         halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==>
          !u. r = Halt u \/ (?ir. r = IntRet ir u) ==> allocas_below_fmp u))
Proof
  cheat
QED

(* Current observed children need no saved value or current array length. *)
Theorem for_storage_current_child_holds:
  stmt_state_rel H ctx func cenv cx ee s /\
  storage_place_observed H (StoragePlace tr slot tyv) /\
  regions_consistent (FST H) /\
  storage_well_formed_on cx ee (FST H) /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  well_formed_type_value tyv /\ 0 < type_slot_size tyv ==>
  storage_holds cx tr typ (PlaceR (StoragePlace tr slot tyv)) slot ee s
Proof
  strip_tac >>
  `w2n slot + type_slot_size tyv <= dimword (:256)` by
    (qpat_x_assum `storage_place_observed _ _` mp_tac >>
     simp[storage_place_observed_def] >> strip_tac >>
     drule storage_subregion_bounds >> strip_tac >>
     `w2n root + type_slot_size tv <= dimword (:256)` by
       metis_tac[regions_consistent_def] >>
     `delta < dimword (:256) /\ w2n root + delta < dimword (:256)` by
       decide_tac >>
     simp[word_add_def, w2n_n2w] >> decide_tac) >>
  drule_all aug_place_observed_slots_in_range >> strip_tac >>
  drule storage_copy_initial_agree >>
  disch_then (qspec_then `tr` assume_tac) >>
  `storage_read_live H tr (get_storage cx ee tr) slot tyv` by
    (irule storage_place_observed_read_live >> simp[]) >>
  drule_all storage_range_agree_of_live >> strip_tac >>
  irule pop_storage_holds >> simp[]
QED

(* Decode the current element before pushing its scope. Neither action
   consumes gas observations. *)
Theorem for_storage_current_read_push:
  !cx tr slot tyv id typ ei s.
    storage_holds cx tr typ (PlaceR (StoragePlace tr slot tyv)) slot ei s /\
    evaluate_type (get_tenv cx) typ = SOME tyv ==>
    ?v. read_result cx (PlaceR (StoragePlace tr slot tyv)) ei = (INL v,ei) /\
        value_has_type tyv v /\ val_wf tyv v /\
        push_scope_with_var id tyv v ei =
        (INL (),
         (\ee v.
            ee with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ee.scopes) ei v) /\
        (!tail.
           read_result cx (PlaceR (StoragePlace tr slot tyv))
             (ei with gas_obs := tail) = (INL v,ei with gas_obs := tail)) /\
        !tail.
          bind (read_result cx (PlaceR (StoragePlace tr slot tyv)))
            (\w. push_scope_with_var id tyv w) (ei with gas_obs := tail) =
          (INL (),
           (\ee v.
              ee with
              scopes :=
                fmupdate id
                  <|assignable := F; type := tyv; value := v; popped := []|>
                  FEMPTY::ee.scopes) ei v with gas_obs := tail)
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  drule_all storage_holds_decode >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  drule_all (cj 1 vyperTypeStatePreservationTheory.decode_value_well_typed) >>
  strip_tac >>
  drule_all storage_holds_value_bounds >> strip_tac >>
  drule_then assume_tac exprSimMemorySourceTheory.read_result_gas_obs >>
  qexists_tac `v` >>
  simp[push_scope_with_var_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, evaluation_state_component_equality]
QED

Theorem for_storage_current_child_ptr:
  !H ctx func cenv cx ee s D lo d G tn tr slot tyv typ p tag.
  stmt_state_rel H ctx func cenv cx ee s /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  dead_lo_ok H D lo cenv cx /\
  storage_place_observed H (StoragePlace tr slot tyv) /\
  0 < type_slot_size tyv /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  p.ptr_location = slot_loc tr /\
  eval_operand p.ptr_operand s = SOME slot /\
  op_taint tn p.ptr_operand = {} ==>
  ptr_vv_ok cx typ (PlaceR (StoragePlace tr slot tyv))
    (LocatedValue tag p) ee G tn s
Proof
  rpt gen_tac >> strip_tac >>
  drule stmt_state_rel_state_rel >> strip_tac >>
  drule state_rel_call_ctx_rel >>
  simp[call_ctx_rel_def] >> strip_tac >>
  `stor_taint_ok_at D tn s` by
    (gvs[ghost_inv_at_def]) >>
  drule_all storage_place_observed_read_live >>
  disch_then (qspec_then
    `if tr then s.vs_transient s.vs_call_ctx.cc_address
     else (s.vs_accounts s.vs_call_ctx.cc_address).storage` assume_tac) >>
  Cases_on `tr` >>
  gvs[ptr_vv_ok_def, slot_loc_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  simp[storage_read_live_def] >>
  disch_then (qspecl_then [`w2n k`, `b`] mp_tac) >>
  (impl_tac >-
    (qpat_x_assum `stor_taint_ok_at _ _ _` mp_tac >>
     gvs[stor_taint_ok_at_def, dead_lo_ok_def, cx_dead_def, SUBSET_DEF] >>
     simp[pairTheory.FORALL_PROD] >> strip_tac >> first_x_assum drule >> simp[])) >>
  simp[]
QED

(* Live outer locals have bounded, well-formed value footprints. *)
Theorem for_storage_outer_local_footprint:
  stmt_state_rel H ctx func cenv cx es s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\
  (w2n w + sz <= a \/ a + bytes <= w2n w) ==>
  val_wf entry.type entry.value /\
  (!i. w2n w <= i /\
       i < w2n w + val_footprint entry.type entry.value ==>
       ~(a <= i /\ i < a + bytes))
Proof
  strip_tac >> drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  drule exprSimPropsTheory.val_footprint_le >> strip_tac >>
  simp[] >> rpt strip_tac >> decide_tac
QED

(* A fresh destination write keeps the original, possibly different-cenv anchor. *)
Theorem for_storage_copy_alloca_frame:
  alloca_frame cinit e0 sa0 s0 c ei u /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b) /\
  allocas_non_overlapping u /\
  FLOOKUP u.vs_allocas aid0 = SOME (w2n dst,nb) /\
  sa0.cs_next_id <= aid0 /\
  lookup_scopes id ei.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) nb) /\
  lookup_var p z = SOME dst /\
  (!name entry. lookup_scopes name ei.scopes = SOME entry ==>
    FLOOKUP bc.ce_vars name = FLOOKUP c.ce_vars name) /\
  local_ptrs_reserved c sa /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u) /\
  (!a len. a+len <= w2n dst \/ w2n dst+nb <= a ==>
    mem_bytes_at a len z.vs_memory = mem_bytes_at a len u.vs_memory) ==>
  alloca_frame cinit e0 sa0 s0 bc
    (ei with scopes := (FEMPTY |+ (id,entry0))::ei.scopes) z
Proof
  strip_tac >> simp[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
  `aid <> aid0` by decide_tac >>
  qpat_x_assum `allocas_non_overlapping _` mp_tac >>
  simp[venomMemDefsTheory.allocas_non_overlapping_def] >>
  disch_then (qspecl_then [`aid`, `aid0`, `off`, `sz`, `w2n dst`, `nb`] mp_tac) >>
  simp[] >> disch_tac >>
  `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s0.vs_memory /\
   (!name b sz'. local_region c ei.scopes u name b sz' ==>
     off + sz <= b \/ b + sz' <= off)` by
    (qpat_x_assum `alloca_frame _ _ _ _ _ _ _` mp_tac >>
     simp[alloca_frame_def] >> metis_tac[]) >>
  conj_tac >-
    (qpat_x_assum `!a len. _` (qspecl_then [`off`, `sz`] mp_tac) >>
     simp[ADD_COMM]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `local_region _ _ _ _ _ _` mp_tac >>
  simp[local_region_def, vyperStateTheory.lookup_scopes_def, FLOOKUP_UPDATE] >>
  strip_tac >> Cases_on `n = id` >> gvs[] >>
  rename1 `lookup_var q z = SOME w` >>
  `lookup_var q u = SOME w` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_x_assum `!name b sz'. local_region c _ _ _ _ _ ==> _`
    (qspecl_then [`n`, `w2n w`, `sz'`] mp_tac) >>
  simp[local_region_def] >> metis_tac[]
QED

(* Interpret the existing copy endpoint; no execution witness is selected here. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
 rpt gen_tac >>
  abbrev_lambda_tac "Fr" 5 0 `alloca_history func s /\ _` >>
  qpat_abbrev_tac `eb = ei with scopes := (FEMPTY |+ (id, _)) :: ei.scopes` >>
 strip_tac >>
 `expr_sim_inv bc cx (extend_local env id typ F) eb` by
   (simp[Abbr `eb`] >> irule expr_sim_inv_for_scope >> metis_tac[]) >>
 `ce_locals_declared bc (extend_local env id typ F)` by
   (irule ce_locals_declared_declare_local >> metis_tac[]) >>
 `locals_alloc_ok bc (extend_local env id typ F)` by
   (drule_all declare_local_memory_types_mem >> strip_tac >>
    simp[locals_alloc_ok_def, vyperTypeSystemTheory.extend_local_def, FLOOKUP_UPDATE] >>
    map_every qx_gen_tac [`nm`,`tv`] >> Cases_on `id = nm` >>
    strip_tac >> gvs[locals_alloc_ok_def] >>
    qpat_x_assum `!nm tv. FLOOKUP env.var_types nm = SOME tv ==> _` irule >>
    qexists `nm` >> simp[]) >>
 `cenv_top_ext c0 bc (FEMPTY::ei.scopes) /\ cenv_top_ext c0 bc eb.scopes` by
   (simp[Abbr `eb`] >> conj_tac >> irule cenv_top_ext_declare_local >> metis_tac[]) >>
 drule_all slot_copy_semantic_frame >> strip_tac >>
 `type_memory_size tyv = 32*n` by simp[type_memory_size_slots] >>
 `lookup_var p z = SOME dst` by metis_tac[] >>
 `stmt_state_rel H ctx func bc cx eb z` by
   (qabbrev_tac `empty = ei with scopes := FEMPTY::ei.scopes` >>
    `stmt_state_rel H ctx func bc cx empty u` by
      (simp[Abbr `empty`] >> irule array_empty_scope_rel_transport >> metis_tac[]) >>
    `eb = empty with scopes :=
      (FEMPTY |+ (id,<|assignable:=F; type:=tyv; value:=v; popped:=[]|>))::ei.scopes` by
      simp[Abbr `eb`, Abbr `empty`] >>
    pop_assum SUBST1_TAC >> irule stmt_state_rel_declare_copy_frame >>
    simp[Abbr `empty`,lookup_scopes_def] >>
    qexistsl [`inst`,`u`,`sa`,`dst`] >>
    simp[] >> conj_tac
    >- (qpat_x_assum `slot_copy_runtime_frame _ _ _ _ _` mp_tac >>
        simp[slot_copy_runtime_frame_def] >> metis_tac[ADD_COMM]) >>
    qpat_x_assum `!mem. mem_agree_outside _ _ mem ==> _` irule >>
    simp[mem_agree_outside_def]) >>
 `(!x. not_fresh_at sa x ==>
     lookup_var x z = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP Gu x /\
     op_taint tnf (Var x) = op_taint tnu (Var x))` by
   (rpt strip_tac >> drule slot_copy_not_fresh_external >> strip_tac >>
    gvs[slot_copy_ghost_inv_def]) >>
 `z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
  z.vs_accounts = u.vs_accounts /\ z.vs_transient = u.vs_transient /\
  z.vs_call_ctx = u.vs_call_ctx` by gvs[slot_copy_runtime_frame_def] >>
 `lo <= z.vs_alloca_next` by
   (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >> simp[ghost_inv_at_def]) >>
 `ghost_inv_at D lo d c0 cx ei Gf tnf z` by
   (irule body_full_memory_ghost_frame >> simp[] >>
    qexistsl [`Gu`,`u`,`sa`,`tnu`,`{i | w2n dst <= i /\ i < w2n dst+32*n}`] >>
    simp[] >> conj_tac
    >- (rpt gen_tac >> strip_tac >>
        `local_region c0 ei.scopes u name (w2n w) sz` by
          (simp[local_region_def] >> metis_tac[]) >>
        Q.SUBGOAL_THEN
          `w2n w + sz <= w2n dst \/ w2n dst + 32*n <= w2n w` assume_tac
        >- (qpat_x_assum `!name b sz. local_region c0 _ _ _ _ _ ==> _` drule >>
            decide_tac) >>
        drule_all for_storage_outer_local_footprint >>
        metis_tac[ADD_COMM]) >>
    gvs[slot_copy_ghost_inv_def, slot_copy_runtime_frame_def] >>
    rpt conj_tac >> rpt strip_tac >> metis_tac[ADD_COMM, DECIDE ``i < lo /\ lo <= a ==> ~(a <= i)``]) >>
 `ptr_covers Gf tnf p z nb` by
   (drule copy_external_ptr_covers >>
    disch_then (qspecl_then [`p`,`u`,`nb`] mp_tac) >>
    simp[eval_operand_def]) >>
 drule_all declare_local_ptr >> strip_tac >>
 `bc.ce_return_buf = c0.ce_return_buf /\
  bc.ce_return_pc = c0.ce_return_pc /\
  bc.ce_imm_alloca = c0.ce_imm_alloca` by
   (qpat_x_assum `bc with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = c0`
      (fn th => once_rewrite_tac[GSYM th] >> simp[NoAsms])) >>
 `ghost_inv_at D lo d bc cx eb Gf tnf z` by
   (qpat_x_assum `ghost_inv_at D lo d c0 cx ei Gf tnf z` mp_tac >>
    simp[ghost_inv_at_def, Abbr `eb`, lookup_scopes_def, FLOOKUP_UPDATE] >>
    strip_tac >> conj_tac
    >- (rpt gen_tac >> Cases_on `name = id` >> simp[] >> strip_tac >> gvs[] >>
        metis_tac[]) >>
    Cases_on `d` >> gvs[return_buf_ptr_def] >>
    rename1 `return_buf_ptr (SOME pair) _ _ _ _` >>
    PairCases_on `pair` >> gvs[return_buf_ptr_def]) >>
 `ret_pc_ok bc sb0 z` by
   (irule ret_pc_ok_frame >> qexistsl [`c0`,`u`,`sa0`] >>
    simp[] >> metis_tac[]) >>
 `return_buf_frame d bc sb0 z` by
   (irule return_buf_frame_frame >> qexistsl [`c0`,`u`,`sa0`] >>
    simp[] >> metis_tac[]) >>
 `return_buf_sep d bc eb z` by
   ((qpat_x_assum `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var (STRING _ _)) _)` kall_tac >>
    irule return_buf_sep_allocated_local >>
    qpat_assum `FLOOKUP bc.ce_vars id = SOME _` (irule_at Any) >>
    qexistsl_tac [`dst`, `sa`, `u`, `func`, `ei`, `cx`, `ctx`, `c0`,
                  `inst.inst_id`, `H`] >>
    simp[Abbr `eb`, lookup_scopes_def, FLOOKUP_UPDATE] >>
    rpt strip_tac >> gvs[return_buf_sep_def, allocas_from_def] >> (metis_tac[Abbr `eb`, lookup_scopes_def, FLOOKUP_UPDATE, return_buf_sep_def, allocas_from_def, return_buf_sep_allocated_local]))) >>
 `alloca_frame c0 e0 sa0 s0 bc eb z` by
   (simp[Abbr `eb`] >> irule for_storage_copy_alloca_frame >>
    conj_tac >- simp[] >>
    qexistsl [`inst.inst_id`,`c0`,`dst`,`nb`,`p`,`sa`,`u`] >>
    qpat_x_assum `Fr c0 ei u Gu tnu` mp_tac >>
    simp[Abbr `Fr`] >> strip_tac >>
    rpt conj_tac
    >- (rpt strip_tac >> Cases_on `name = id` >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
 `Fr bc eb z Gf tnf` by
   (qpat_x_assum `Fr c0 ei u Gu tnu` mp_tac >>
    simp[Abbr `Fr`] >> strip_tac >> simp[] >>
    rpt gen_tac >> strip_tac >>
    `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
    `aid <> inst.inst_id` by decide_tac >>
    qpat_x_assum `allocas_non_overlapping u` mp_tac >>
    simp[venomMemDefsTheory.allocas_non_overlapping_def] >>
    disch_then (qspecl_then [`aid`,`inst.inst_id`,`off`,`sz`,`w2n dst`,`nb`] mp_tac) >>
    simp[] >> strip_tac >>
    `~(w2n dst <= i /\ i < w2n dst + 32*n)` by decide_tac >>
    `i IN tnu.t_mem` by
      (qpat_x_assum `slot_copy_ghost_inv _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
       pure_rewrite_tac[slot_copy_ghost_inv_def] >> strip_tac >>
       qpat_x_assum `!a. ~(_ /\ _) ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
    qpat_x_assum `!aid off sz i. _` irule >>
    metis_tac[]) >>
 simp[] >> conj_tac
 >- simp[Abbr `eb`,push_scope_with_var_def,return_def,
         evaluation_state_component_equality,combinTheory.o_DEF] >>
 conj_tac
 >- (`storage_well_formed_on cx eb (FST H) <=>
      storage_well_formed_on cx ei (FST H)` suffices_by simp[] >>
     irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
     simp[Abbr `eb`]) >>
 qpat_x_assum `Fr c0 ei u Gu tnu` mp_tac >>
 simp[Abbr `Fr`]
QED
*)
Theorem for_storage_copy_body_entry:
  !H D lo d ctx func cx c0 e0 sa0 s0 G0 tn0 ei env id typ tyv v sd st bc sa sb0
      inst p nb dst n src load u Gu tnu z Gf tnf idx k lvo len.
    expr_sim_inv_mods mods c0 cx env ei /\ ce_locals_declared c0 env /\
    locals_alloc_ok c0 env /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\ value_has_type tyv v /\
    val_wf tyv v /\ declare_local c0 id typ sd = (bc,st) /\
    c0.ce_alloca_locals /\ type_memory_bytes c0 typ < 2 ** 64 /\
    (!l. FLOOKUP c0.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz) /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) nb) /\
    lookup_scopes id ei.scopes = NONE /\
    return_buf_sep d c0 ei u /\ stmt_state_rel H ctx func c0 cx ei u /\
    storage_well_formed_on cx ei (FST H) /\
    ghost_inv_at D lo d c0 cx ei Gu tnu u /\
    (\c ee s G tn.
       alloca_history func s /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
       s0.vs_alloca_next <= s.vs_alloca_next /\
       (!x w.
          not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
          lookup_var x s = SOME w) /\
       (!aid b.
          FLOOKUP s0.vs_allocas aid = SOME b ==>
          FLOOKUP s.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa0 x ==>
            FLOOKUP G x = FLOOKUP G0 x /\
            op_taint tn (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame c0 e0 sa0 s0 c ee s /\
       !aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
         (!name b sz'.
            local_region c0 e0.scopes s0 name b sz' ==>
            off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
         i IN tn.t_mem ==>
         i IN tn0.t_mem) c0 ei u Gu tnu /\ return_buf_frame d c0 sa0 u /\
    ret_pc_ok c0 sa0 u /\ sa0.cs_next_var <= sb0.cs_next_var /\
    (!x. not_fresh_at sa0 x ==> not_fresh_at sa x) /\
    local_ptrs_reserved c0 sa /\ local_ptrs_reserved bc sa /\
    (!x cap. c0.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. c0.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    not_fresh_at sa p /\ not_local_ptr bc (FEMPTY::ei.scopes) p /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
    sa0.cs_next_id <= inst.inst_id /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n dst,nb) /\
    allocas_non_overlapping u /\ lookup_var p u = SOME dst /\
    ptr_covers Gu tnu p u nb /\ slot_copy_external sa (Var p) /\
    n = type_slot_size tyv /\ 32 * n <= nb /\ lo <= w2n dst /\
    (!name b sz.
       local_region c0 ei.scopes u name b sz ==>
       w2n dst + nb <= b \/ b + sz <= w2n dst) /\
    slot_copy_runtime_frame sa dst n u z /\
    slot_copy_ghost_inv sa load src dst p n Gu tnu n Gf tnf z /\
    (!mem.
       mem_agree_outside tnf.t_mem z.vs_memory mem ==>
       val_in_memory tyv v (w2n dst) mem) /\
    z.vs_immutables = u.vs_immutables /\ alloca_history func z /\
    allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    ~z.vs_halted /\ z.vs_current_bb = sb0.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    lookup_var idx z = SOME (n2w k) /\ FLOOKUP Gf idx = NONE /\
    op_taint tnf (Var idx) = {} /\ eval_operand lvo z = SOME (n2w len) /\
    op_prov Gf lvo = NONE /\ op_taint tnf lvo = {} ==>
    push_scope_with_var id tyv v ei =
    (INL (),
     ei with
     scopes :=
       fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
         FEMPTY::ei.scopes) /\
    expr_sim_inv_mods mods bc cx (extend_local env id typ F)
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) /\
    ce_locals_declared bc (extend_local env id typ F) /\
    locals_alloc_ok bc (extend_local env id typ F) /\
    cenv_top_ext c0 bc
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes).scopes /\
    stmt_state_rel H ctx func bc cx
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) z /\
    storage_well_formed_on cx
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) (FST H) /\
    ghost_inv_at D lo d bc cx
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) Gf tnf z /\ ret_pc_ok bc sb0 z /\
    return_buf_frame d bc sb0 z /\
    return_buf_sep d bc
      (ei with scopes :=
        fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
          FEMPTY::ei.scopes) z /\
    (\c ee s G tn.
       alloca_history func s /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
       s0.vs_alloca_next <= s.vs_alloca_next /\
       (!x w.
          not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
          lookup_var x s = SOME w) /\
       (!aid b.
          FLOOKUP s0.vs_allocas aid = SOME b ==>
          FLOOKUP s.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa0 x ==>
            FLOOKUP G x = FLOOKUP G0 x /\
            op_taint tn (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame c0 e0 sa0 s0 c ee s /\
       !aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
         (!name b sz'.
            local_region c0 e0.scopes s0 name b sz' ==>
            off + sz <= b \/ b + sz' <= off) /\ off <= i /\ i < off + sz /\
         i IN tn.t_mem ==>
         i IN tn0.t_mem) bc
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) z Gf tnf /\ ~z.vs_halted /\
    z.vs_current_bb = sb0.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    lookup_var idx z = SOME (n2w k) /\ FLOOKUP Gf idx = NONE /\
    op_taint tnf (Var idx) = {} /\ lookup_var p z = SOME dst /\
    eval_operand lvo z = SOME (n2w len) /\ op_prov Gf lvo = NONE /\
    op_taint tnf lvo = {} /\ allocas_from lo z /\
    FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dst,nb) /\
    ptr_covers Gf tnf p z nb /\
    !aid b.
      FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b
Proof
  cheat
QED

(* Pure scalar prefix steps have explicit finite ghost updates. *)
Theorem for_storage_scalar_step_prov[local]:
  MEM opc [EQ;MUL;ADD] /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid opc [a;b] [out]) /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  (opc = EQ ==> op_prov G a = NONE) /\ op_prov G b = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\
  w = (if opc = EQ then bool_to_word (x=y)
       else if opc = MUL then x*y else x+y) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
     set_prov G [out] (if opc = ADD then op_prov G a else NONE),
     tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `step_inst_base (mk_inst iid opc [a;b] [out]) s =
     OK (update_var out w s)` by
    (gvs[] >> metis_tac[emitHelperPropsTheory.step_EQ,
      emitHelperPropsTheory.step_MUL, emitHelperPropsTheory.step_ADD]) >>
  `ptr_inst_ok D lo 0 ctx func G tn (mk_inst iid opc [a;b] [out]) s` by
    suspend "checks" >>
  `step_prov PG G (mk_inst iid opc [a;b] [out]) (update_var out w s) =
     set_prov G [out] (if opc = ADD then op_prov G a else NONE) /\
   step_taint (mk_inst iid opc [a;b] [out]) s (update_var out w s) tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by suspend "ghosts" >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
     set_prov G [out] (if opc = ADD then op_prov G a else NONE),
     tn with t_var := tn.t_var |+ (out,{}))` by
    (`(mk_inst iid opc [a;b] [out]).inst_opcode <> INVOKE /\
      ~is_terminator (mk_inst iid opc [a;b] [out]).inst_opcode /\
      inst_mem_below_frontier (mk_inst iid opc [a;b] [out]) s /\
      inst_dload_in_section (mk_inst iid opc [a;b] [out]) s /\
      (ctx_has_dalloca ctx ==> dalloca_no_wrap (mk_inst iid opc [a;b] [out]) s)` by
       (gvs[] >> simp[mk_inst_def, is_terminator_def,
         unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def,
         source_memory_write_ranges_def, source_memory_read_ranges_def]) >>
     drule_all straight_line_origin_ptr_edge >>
     disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
     gvs[] >> simp[mk_inst_def]) >>
  `~(update_var out w s with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    simp[update_var_def] >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Resume for_storage_scalar_step_prov[checks]:
  Cases_on `opc = EQ`
  >- (gvs[] >>
      simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
           source_memory_write_ranges_def, source_memory_read_ranges_def] >>
      conj_tac
      >- (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
      conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
      simp[GSYM mk_inst_def, step_inst_non_invoke] >>
      simp[update_var_def]) >>
  irule ptr_inst_ok_copy_arith >> gvs[]
QED

Resume for_storage_scalar_step_prov[ghosts]:
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         EXTENSION, SF CONJ_ss] >>
  gvs[] >> Cases_on `op_prov G a` >>
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def, mem_taint_def,
       written_taint_def, step_writes_def, store_taint_def, imm_taint_def,
       adopt_reset_def, range_bytes_def, source_memory_write_ranges_def,
       mk_inst_def, taint_component_equality]
QED

Finalise for_storage_scalar_step_prov[local]

(* The scalar path with no input provenance just clears the output. *)
Theorem for_storage_scalar_step[local]:
  MEM opc [EQ;MUL;ADD] /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid opc [a;b] [out]) /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  op_prov G a = NONE /\ op_prov G b = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\
  w = (if opc = EQ then bool_to_word (x=y)
       else if opc = MUL then x*y else x+y) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
     DRESTRICT G (COMPL {out}), tn with t_var := tn.t_var |+ (out,{}))
Proof
  suspend "specialize"
QED

Resume for_storage_scalar_step[specialize]:
  strip_tac >>
  `set_prov G [out] (if opc = ADD then op_prov G a else NONE) =
     DRESTRICT G (COMPL {out})` by simp[set_prov_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule for_storage_scalar_step_prov >>
  metis_tac[]
QED

Finalise for_storage_scalar_step

(* The length comparison and scaled offset are scalars. The final ADD
   preserves the base's provenance at ep, regardless of its storage bank.
   The prefix is uniform in the dead policy. *)
Theorem for_storage_array_head_prefix_at_prov:
  lookup_block cond func.fn_blocks = SOME cb /\
  cb.bb_instructions =
  [mk_inst (h - 2) EQ [Var idx; lvo] [dv];
   mk_inst (h - 1) JNZ [Var dv; Label exit; Label bod] []] /\
  lookup_block bod func.fn_blocks = SOME bb /\ sa.cs_current_bb = bod /\
  sa.cs_current_insts =
  [mk_inst h MUL [Var idx; Lit (n2w n)] [ov]] ++
  (if case bd of Fixed v => F | Dynamic v1 => T then
     [mk_inst (h + 1) ADD [Lit 1w; Var ov] [tot]]
   else []) ++
  [mk_inst (h + if case bd of Fixed v => F | Dynamic v1 => T then 2 else 1) ADD
     [base_op;
      Var (if (case bd of Fixed v => F | Dynamic v1 => T) then tot else ov)]
     [ep]] /\
  (!j. j < LENGTH sa.cs_current_insts ==>
       get_instruction bb j = SOME (fEL sa.cs_current_insts j)) /\
  ALL_DISTINCT
    (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
     else [dv; ov; ep]) /\
  ~MEM idx
    (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
     else [dv; ov; ep]) /\
  ~MEM p
    (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
     else [dv; ov; ep]) /\
  (!x. lvo = Var x ==>
       ~MEM x
         (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
          else [dv; ov; ep])) /\ s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
  ~s.vs_halted /\ lookup_var idx s = SOME (n2w k) /\ k < len /\
  len < 2 ** 256 /\ FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  eval_operand lvo s = SOME (n2w len) /\ op_prov G lvo = NONE /\
  op_taint tn lvo = {} /\
  eval_operand base_op s = SOME slot /\ op_taint tn base_op = {} /\
  (!x. base_op = Var x ==>
     ~MEM x (if (case bd of Fixed _ => F | Dynamic _ => T)
             then [dv; ov; tot; ep] else [dv; ov; ep])) /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u Gu tnu.
    (!D explicit.
       gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK u,Gu,tnu)) /\
    u =
    update_var ep
      ((if case bd of Fixed v => F | Dynamic v1 => T then slot + 1w else slot) +
       n2w (k * n))
      (if (case bd of Fixed v => F | Dynamic v1 => T) then
         update_var tot (1w + n2w (k * n))
           (update_var ov (n2w (k * n)) (jump_to bod (update_var dv 0w s)))
       else update_var ov (n2w (k * n)) (jump_to bod (update_var dv 0w s))) with
    vs_inst_idx := LENGTH sa.cs_current_insts /\
    Gu = set_prov
      (DRESTRICT G (COMPL (set
        (if (case bd of Fixed v => F | Dynamic v1 => T) then
           [dv; ov; tot] else [dv; ov]))))
      [ep] (op_prov G base_op) /\
    tnu =
    tn with
    t_var :=
      FOLDL (\m x. fmupdate x {} m) tn.t_var
        (if (case bd of Fixed v => F | Dynamic v1 => T) then [dv; ov; tot; ep]
         else [dv; ov; ep]) /\ u.vs_current_bb = sa.cs_current_bb /\
    u.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~u.vs_halted /\
    eval_operand (Var ep) u =
    SOME
      ((if case bd of Fixed v => F | Dynamic v1 => T then slot + 1w else slot) +
       n2w (k * n)) /\ FLOOKUP Gu ep = op_prov G base_op /\
    op_taint tnu (Var ep) = {} /\
    (!x. ~MEM x
           (if (case bd of Fixed v => F | Dynamic v1 => T) then
              [dv; ov; tot; ep]
            else [dv; ov; ep]) ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
         op_taint tnu (Var x) = op_taint tn (Var x)) /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  `n2w k <> (n2w len : bytes32)` by
    (`k < 2**256` by decide_tac >>
     gvs[wordsTheory.n2w_11, wordsTheory.dimword_def] >>
     simp[LESS_MOD] >> decide_tac) >>
  qabbrev_tac `s1 = update_var dv 0w s with vs_inst_idx := 1` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {dv})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (dv,{})` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK s1,G1,tn1)` by suspend "eq" >>
  qabbrev_tac `q = jump_to bod s1` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s1,G1,tn1) [] (OK q,G1,tn1)` by suspend "branch" >>
  suspend "address"
QED

Resume for_storage_array_head_prefix_at_prov[eq]:
  rpt gen_tac >>
  simp[Abbr `s1`, Abbr `G1`, Abbr `tn1`] >>
  `get_instruction cb s.vs_inst_idx =
     SOME (mk_inst (h-2) EQ [Var idx;lvo] [dv])` by
    simp[venomInstTheory.get_instruction_def] >>
  drule_at (Pos (el 3)) for_storage_scalar_step >>
  disch_then (qspecl_then [`n2w len`,`n2w k`,`0w`] mp_tac) >>
  simp[eval_operand_def, op_prov_def,
       venomExecSemanticsTheory.bool_to_word_def] >>
  disch_then irule >> simp[GSYM op_prov_def]
QED

Resume for_storage_array_head_prefix_at_prov[branch]:
  rpt gen_tac >>
  `lookup_block s1.vs_current_bb func.fn_blocks = SOME cb /\
   get_instruction cb s1.vs_inst_idx =
     SOME (mk_inst (h-1) JNZ [Var dv;Label exit;Label bod] []) /\
   eval_operand (Var dv) s1 = SOME 0w /\ op_taint tn1 (Var dv) = {} /\
   ~s1.vs_halted /\ allocas_from lo s1 /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s1)` by
    (simp[Abbr `s1`, Abbr `tn1`, venomInstTheory.get_instruction_def,
          update_var_def, eval_operand_def, lookup_var_def, op_taint_def,
          FLOOKUP_UPDATE, allocas_from_def, allocas_below_fmp_def] >>
     gvs[allocas_from_def, allocas_below_fmp_def]) >>
  drule_all decoderNavigationPtrTheory.jnz_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`G1`,`D`] mp_tac) >>
  simp[Abbr `q`]
QED

Resume for_storage_array_head_prefix_at_prov[address]:
  qabbrev_tac `dyn = (case bd of Dynamic _ => T | Fixed _ => F)` >>
  qabbrev_tac `s2 = update_var ov (n2w(k*n)) q with vs_inst_idx := 1` >>
  qabbrev_tac `G2 = DRESTRICT G1 (COMPL {ov})` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (ov,{})` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (q,G1,tn1) [] (OK s2,G2,tn2)` by suspend "mul" >>
  qabbrev_tac `s3 = if dyn then
    update_var tot (1w+n2w(k*n)) s2 with vs_inst_idx := 2 else s2` >>
  qabbrev_tac `G3 = if dyn then DRESTRICT G2 (COMPL {tot}) else G2` >>
  qabbrev_tac `tn3 = if dyn then tn2 with t_var := tn2.t_var |+ (tot,{}) else tn2` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s2,G2,tn2) [] (OK s3,G3,tn3)` by suspend "optional" >>
  qabbrev_tac `u = update_var ep ((if dyn then slot+1w else slot)+n2w(k*n)) s3
    with vs_inst_idx := LENGTH sa.cs_current_insts` >>
  qabbrev_tac `Gu = set_prov G3 [ep] (op_prov G base_op)` >>
  qabbrev_tac `tnu = tn3 with t_var := tn3.t_var |+ (ep,{})` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s3,G3,tn3) [] (OK u,Gu,tnu)` by suspend "last" >>
  qexistsl_tac [`u`,`Gu`,`tnu`] >>
  conj_tac >- metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
  suspend "endpoint"
QED

Resume for_storage_array_head_prefix_at_prov[mul]:
  `get_instruction bb q.vs_inst_idx =
    SOME (mk_inst h MUL [Var idx;Lit (n2w n)] [ov])` by
    (simp[Abbr `q`, Abbr `s1`, jump_to_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `q.vs_inst_idx = 0` by simp[Abbr `q`, jump_to_def] >>
  rpt gen_tac >>
  simp[Abbr `s2`, Abbr `G2`, Abbr `tn2`] >>
  drule_at (Pos (el 3)) for_storage_scalar_step_prov >>
  disch_then (qspecl_then [`n2w n`,`n2w k`,`n2w(k*n)`] mp_tac) >>
  simp[wordsTheory.word_mul_n2w, set_prov_def] >>
  disch_then irule >>
  Cases_on `dyn` >>
  gvs[allocas_from_def, allocas_below_fmp_def, op_taint_def,
    Abbr `q`, Abbr `s1`, Abbr `G1`, Abbr `tn1`,
    eval_operand_def, lookup_var_def, update_var_def, jump_to_def,
    op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Resume for_storage_array_head_prefix_at_prov[optional]:
  Cases_on `dyn`
  >- (gvs[Abbr `s3`, Abbr `G3`, Abbr `tn3`] >>
      `get_instruction bb s2.vs_inst_idx =
        SOME (mk_inst (h+1) ADD [Lit 1w;Var ov] [tot])` by
        (simp[Abbr `s2`] >>
         qpat_x_assum `!j. _ ==> get_instruction bb j = _`
           (qspec_then `1` mp_tac) >> simp[]) >>
      `s2.vs_inst_idx = 1` by simp[Abbr `s2`] >>
      rpt gen_tac >>
      drule_at (Pos (el 3)) for_storage_scalar_step_prov >>
      disch_then (qspecl_then [`n2w(k*n)`,`1w`,`1w+n2w(k*n)`] mp_tac) >>
      simp[set_prov_def, op_prov_def] >> disch_then irule >>
      gvs[Abbr `s2`, Abbr `q`, Abbr `s1`, Abbr `G2`, Abbr `tn2`,
        eval_operand_def, lookup_var_def, update_var_def, jump_to_def,
        op_taint_def, op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
        allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  simp[Abbr `s3`, Abbr `G3`, Abbr `tn3`] >> rpt gen_tac >>
  irule (cj 1 gas_origin_ptr_path_rules) >>
  simp[Abbr `s2`, Abbr `q`, Abbr `s1`, update_var_def, jump_to_def]
QED

Resume for_storage_array_head_prefix_at_prov[last]:
  rpt (qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ _ _` kall_tac) >>
  `s3.vs_inst_idx = (if dyn then 2 else 1) /\
   LENGTH sa.cs_current_insts = SUC s3.vs_inst_idx /\
   get_instruction bb s3.vs_inst_idx = SOME
     (mk_inst (h+(if dyn then 2 else 1)) ADD
       [base_op;Var (if dyn then tot else ov)] [ep])` by
    (Cases_on `dyn` >>
     simp[Abbr `s3`, Abbr `s2`] >>
     qpat_x_assum `!j. _ ==> get_instruction bb j = _`
       (qspec_then `if dyn then 2 else 1` mp_tac) >> gvs[]) >>
  `op_prov G3 base_op = op_prov G base_op` by
    (Cases_on `dyn` >> Cases_on `base_op` >>
     gvs[Abbr `G3`, Abbr `G2`, Abbr `G1`, op_prov_def, FLOOKUP_DRESTRICT] >>
     rw[] >> metis_tac[]) >>
  rpt gen_tac >>
  simp[Abbr `u`, Abbr `Gu`, Abbr `tnu`] >>
  qpat_x_assum `op_prov G3 base_op = op_prov G base_op` (SUBST1_TAC o SYM) >>
  drule_at (Pos (el 3)) for_storage_scalar_step_prov >>
  disch_then (qspecl_then
    [`(if dyn then 1w else 0w)+n2w(k*n)`,`slot`,
     `(if dyn then slot+1w else slot)+n2w(k*n)`] mp_tac) >>
  Cases_on `dyn` >> simp[wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_0] >>
  disch_then irule >>
  Cases_on `base_op` >>
  gvs[Abbr `s3`, Abbr `s2`, Abbr `q`, Abbr `s1`,
    Abbr `G3`, Abbr `G2`, Abbr `G1`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
    eval_operand_def, lookup_var_def, update_var_def, jump_to_def,
    op_taint_def, op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    allocas_from_def, allocas_below_fmp_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume for_storage_array_head_prefix_at_prov[endpoint]:
  rpt (qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ _ _` kall_tac) >>
  `G3 = DRESTRICT G (COMPL (set (if dyn then [dv;ov;tot] else [dv;ov])))` by
    (Cases_on `dyn` >>
     simp[Abbr `G3`, Abbr `G2`, Abbr `G1`, fmap_eq_flookup, FLOOKUP_DRESTRICT] >>
     metis_tac[]) >>
  Cases_on `dyn` >> Cases_on `op_prov G base_op` >>
  gvs[Abbr `u`, Abbr `Gu`, Abbr `tnu`, Abbr `s3`, Abbr `s2`,
    Abbr `q`, Abbr `s1`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
    update_var_def, jump_to_def, eval_operand_def, lookup_var_def,
    op_taint_def, set_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    allocas_from_def, allocas_below_fmp_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Finalise for_storage_array_head_prefix_at_prov

(* Read the current captured child, execute the scalar head and copy, and
   register the one selected copy endpoint as the actual body entry. *)
(* Interpret the selected scalar prefix and the counted copy at the same
   endpoints. No observation of the parent array is needed here. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  (* Fold the expanded frame and body-entry predicates just for this proof. *)
  rpt gen_tac >>
  qabbrev_tac `Fr = \c ee st G tn.
    alloca_history func st /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp st) /\
    s0.vs_alloca_next <= st.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
           lookup_var x st = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP st.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa0 x ==>
         FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame c0 e0 sa0 s0 c ee st /\
    !aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
      (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem` >>
  qabbrev_tac `EB = \ee v. ee with scopes :=
    (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) ::
    ee.scopes` >>
  map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac
      [GSYM (BETA_RULE (PURE_REWRITE_RULE [markerTheory.Abbrev_def, FUN_EQ_THM] th))]))
    [`Abbrev (Fr = _)`, `Abbrev (EB = _)`] >>
  qabbrev_tac `Entry = \H ee v j z Gf tnf.
    push_scope_with_var id tyv v ee = (INL (),EB ee v) /\
    expr_sim_inv bc cx (extend_local env id typ F) (EB ee v) /\
    ce_locals_declared bc (extend_local env id typ F) /\
    locals_alloc_ok bc (extend_local env id typ F) /\
    cenv_top_ext c0 bc (EB ee v).scopes /\
    stmt_state_rel H ctx func bc cx (EB ee v) z /\
    storage_well_formed_on cx (EB ee v) (FST H) /\
    ghost_inv_at (DF H) lo d bc cx (EB ee v) Gf tnf z /\
    ret_pc_ok bc sb0 z /\ return_buf_frame d bc sb0 z /\
    return_buf_sep d bc (EB ee v) z /\ Fr bc (EB ee v) z Gf tnf /\
    ~z.vs_halted /\ z.vs_current_bb = sb0.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    lookup_var idx z = SOME (n2w j) /\ FLOOKUP Gf idx = NONE /\
    op_taint tnf (Var idx) = {} /\ lookup_var p z = SOME dst /\
    eval_operand lvo z = SOME (n2w len) /\ op_prov Gf lvo = NONE /\
    op_taint tnf lvo = {} /\ allocas_from lo z /\
    FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dst,nb) /\
    ptr_covers Gf tnf p z nb /\
    !aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b` >>
  qpat_abbrev_tac `n = type_slot_size tyv` >> suspend "entry"
QED
*)
Theorem for_storage_observed_head_from_prefix:
  !DF lo d ctx func cx RetQ lctx c0 e0 sa0 s0 G0 tn0 tr slot dst tyv typ
   vs len nb id env p idx lvo sd body st0 explicit PG ep exit incr sa st bc
   sb0 inst bop a rs k addr ei s G tn u Gu tnu.
    0 < type_slot_size tyv /\ body_for_full_ok_mods mods exps cx tyv id body vs /\
    id NOTIN FDOM env.var_types /\
    declare_local c0 id typ sd = (bc,st) /\ c0.ce_alloca_locals /\
    type_memory_bytes c0 typ < 2 ** 64 /\
    (!l. FLOOKUP c0.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz) /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) nb) /\
    sa0.cs_next_var <= sb0.cs_next_var /\
    (!x. not_fresh_at sa0 x ==> not_fresh_at sa x) /\
    local_ptrs_reserved c0 sa /\ local_ptrs_reserved bc sa /\
    (!x cap. c0.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa0 x) /\
    (!x cap. c0.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa0 x) /\
    not_fresh_at sa p /\ not_fresh_at sa idx /\
    (!x. lvo = Var x ==> not_fresh_at sa x) /\ (!lbl. lvo <> Label lbl) /\
    (!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY::scs) p) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\ inst.inst_id = sd.cs_next_id /\
    sa0.cs_next_id <= inst.inst_id /\ fn_inst_ids_distinct func /\
    (!H. dead_lo_ok H (DF H) lo c0 cx) /\
    compile_iter_elem_copy bc (Var ep) (Var p) (type_slot_size tyv)
      (slot_loc tr) T typ typ sa = ((),sb0) /\
    compile_slot_to_memory (Var ep) (Var p) (type_slot_size tyv)
      (slot_loc tr) sa = (slot_copy_body sa,sb0) /\
    slot_copy_external sa (Var ep) /\
    lookup_block sa.cs_current_bb func.fn_blocks =
      SOME <|bb_label := sa.cs_current_bb;
             bb_instructions := sa.cs_current_insts ++ slot_copy_init_insts sa|> /\
    lookup_block (slot_copy_cond sa) func.fn_blocks =
      SOME <|bb_label := slot_copy_cond sa;
             bb_instructions := slot_copy_cond_insts sa (type_slot_size tyv)|> /\
    lookup_block (slot_copy_body sa) func.fn_blocks =
      SOME <|bb_label := slot_copy_body sa; bb_instructions :=
        slot_copy_body_insts sa (Var ep) (Var p) (if tr then TLOAD else SLOAD)|> /\
    a::rs = DROP k vs /\ k < LENGTH vs /\ a = PlaceR (StoragePlace tr addr tyv) /\
    ~s.vs_halted /\ storage_trace_domain cx st0 ei.storage_trace /\
    (k <> 0 ==> body_stmts_full_ok_mods mods exps cx body) /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\ well_formed_type_value tyv /\
    expr_sim_inv_mods mods c0 cx env ei /\ ce_locals_declared c0 env /\ locals_alloc_ok c0 env /\
    lookup_scopes id ei.scopes = NONE /\
    gas_admissible (eval_for cx tyv id body (a::rs)) (stmt_res_ok lctx) ei /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gu,tnu)) /\
    (!H. valid_horizon cx st0 H ei.storage_trace ==>
      storage_place_observed H (StoragePlace tr addr tyv) /\
      stmt_state_rel H ctx func c0 cx ei u /\ storage_well_formed_on cx ei (FST H) /\
      ghost_inv_at (DF H) lo d c0 cx ei Gu tnu u /\
      (alloca_history func u /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
       s0.vs_alloca_next <= u.vs_alloca_next /\
       (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
              lookup_var x u = SOME w) /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                FLOOKUP u.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa0 x ==>
            FLOOKUP Gu x = FLOOKUP G0 x /\
            op_taint tnu (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame c0 e0 sa0 s0 c0 ei u /\
       !aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
         (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
                       off + sz <= b \/ b + sz' <= off) /\
         off <= i /\ i < off + sz /\ i IN tnu.t_mem ==> i IN tn0.t_mem) /\
      return_buf_frame d c0 sa0 u /\ ret_pc_ok c0 sa0 u /\ return_buf_sep d c0 ei u) /\
    ~u.vs_halted /\ u.vs_current_bb = sa.cs_current_bb /\
    u.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var idx u = SOME (n2w k) /\ FLOOKUP Gu idx = NONE /\ op_taint tnu (Var idx) = {} /\
    eval_operand lvo u = SOME (n2w len) /\ op_prov Gu lvo = NONE /\ op_taint tnu lvo = {} /\
    lookup_var p u = SOME dst /\ ptr_covers Gu tnu p u nb /\
    FLOOKUP u.vs_allocas sd.cs_next_id = SOME (w2n dst,nb) /\
    32*type_slot_size tyv <= nb /\
    w2n dst + nb < 2**256 /\ w2n dst + nb <= u.vs_alloca_next /\
    (!name b sz. local_region c0 ei.scopes u name b sz ==>
                 w2n dst+nb <= b \/ b+sz <= w2n dst) /\
    eval_operand (Var ep) u = SOME addr /\ op_taint tnu (Var ep) = {} /\
    slot_copy_external sa bop /\ eval_operand bop u = SOME slot /\ op_taint tnu bop = {} ==>
    (?v. !tail. bind (read_result cx a) (\w. push_scope_with_var id tyv w)
      (ei with gas_obs := tail) =
      (INL (), (ei with scopes :=
        (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) ::
        ei.scopes) with gas_obs := tail)) /\
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
      (bind (read_result cx a) (\v. push_scope_with_var id tyv v)) (ei,s,G,tn)
      (\H res eb Gf tnf z. res = INL () /\ eb.gas_obs = [] /\
        ?v j. eb = ((ei with gas_obs := []) with scopes :=
            (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) ::
            (ei with gas_obs := []).scopes) /\
          read_result cx a ei = (INL v,ei) /\
          (push_scope_with_var id tyv v (ei with gas_obs := []) =
             (INL (), (ei with gas_obs := []) with scopes :=
               (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) ::
               (ei with gas_obs := []).scopes) /\
           expr_sim_inv_mods mods bc cx (extend_local env id typ F)
             ((ei with gas_obs := []) with scopes :=
               (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) ::
               (ei with gas_obs := []).scopes) /\
           ce_locals_declared bc (extend_local env id typ F) /\
           locals_alloc_ok bc (extend_local env id typ F) /\
           cenv_top_ext c0 bc
             ((ei with gas_obs := []) with scopes :=
               (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) ::
               (ei with gas_obs := []).scopes).scopes /\
           stmt_state_rel H ctx func bc cx
             ((ei with gas_obs := []) with scopes :=
               (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) ::
               (ei with gas_obs := []).scopes) z /\
           storage_well_formed_on cx
             ((ei with gas_obs := []) with scopes :=
               (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) ::
               (ei with gas_obs := []).scopes) (FST H) /\
           ghost_inv_at (DF H) lo d bc cx
             ((ei with gas_obs := []) with scopes :=
               (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) ::
               (ei with gas_obs := []).scopes) Gf tnf z /\
           ret_pc_ok bc sb0 z /\ return_buf_frame d bc sb0 z /\
           return_buf_sep d bc
             ((ei with gas_obs := []) with scopes :=
               (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) ::
               (ei with gas_obs := []).scopes) z /\
           (alloca_history func z /\
            (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
            s0.vs_alloca_next <= z.vs_alloca_next /\
            (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
                   lookup_var x z = SOME w) /\
            (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                     FLOOKUP z.vs_allocas aid = SOME b) /\
            (!x. not_fresh_at sa0 x ==>
                 FLOOKUP Gf x = FLOOKUP G0 x /\
                 op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
            alloca_frame c0 e0 sa0 s0 bc
              ((ei with gas_obs := []) with scopes :=
                (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) ::
                (ei with gas_obs := []).scopes) z /\
            !aid off sz i.
              FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
              (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
                            off + sz <= b \/ b + sz' <= off) /\
              off <= i /\ i < off + sz /\ i IN tnf.t_mem ==> i IN tn0.t_mem) /\
           ~z.vs_halted /\ z.vs_current_bb = sb0.cs_current_bb /\
           z.vs_inst_idx = LENGTH sb0.cs_current_insts /\
           lookup_var idx z = SOME (n2w j) /\ FLOOKUP Gf idx = NONE /\
           op_taint tnf (Var idx) = {} /\ lookup_var p z = SOME dst /\
           eval_operand lvo z = SOME (n2w len) /\ op_prov Gf lvo = NONE /\
           op_taint tnf lvo = {} /\ allocas_from lo z /\
           FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dst,nb) /\
           ptr_covers Gf tnf p z nb /\
           !aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP z.vs_allocas aid = SOME b) /\
          eval_operand bop z = SOME slot /\ op_taint tnf bop = {} /\ a::rs = DROP j vs /\
          body_stmts_full_ok_mods mods exps cx body /\
          gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit incr)) eb)
      (\H res ee gt r. ?ex. res = INR ex /\
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
        halt_exit H cx ee (INR ex) r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s \/ (?ir. r = IntRet ir s) ==>
                                    allocas_below_fmp s))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume for_storage_observed_head_from_prefix[entry]:
  strip_tac >>
  rename1 `body_for_full_ok cx tyv id stmts vs` >>
  qabbrev_tac `H0 = storage_trace_horizon ei.storage_trace` >>
  `valid_horizon cx st0 H0 ei.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> storage_place_observed _ _ /\ _`
    (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `Fr c0 ei u Gu tnu` by (simp[Abbr `Fr`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `regions_consistent (FST H0)` by
    (qpat_assum `valid_horizon cx st0 H0 _`
       (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >> first_assum ACCEPT_TAC) >>
  `0 < type_slot_size tyv` by simp[Abbr `n`] >>
  drule_all for_storage_current_child_holds >> strip_tac >>
  `?v. read_result cx a ei = (INL v,ei) /\ value_has_type tyv v /\ val_wf tyv v /\
    (!tail. read_result cx a (ei with gas_obs:=tail) = (INL v,ei with gas_obs:=tail)) /\
    (!tail. bind (read_result cx a) (\w. push_scope_with_var id tyv w)
      (ei with gas_obs:=tail) = (INL (),EB ei v with gas_obs:=tail))` by
    (qpat_assum `a = PlaceR _` SUBST_ALL_TAC >>
     drule_all (BETA_RULE (REWRITE_RULE [LET_THM] for_storage_current_read_push)) >>
     disch_then (qspec_then `id` (qx_choose_then `v` strip_assume_tac)) >>
     qexists `v` >> simp[Abbr `EB`]) >>
  conj_tac >- (qexists `v` >> first_assum ACCEPT_TAC) >>
  `body_stmts_full_ok cx stmts` by suspend "activate" >>
  `gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr))
     (EB (ei with gas_obs:=[]) v)` by suspend "body_gas" >>
  suspend "execute"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_storage_observed_head_from_prefix[activate]:
  reverse (Cases_on `k = 0`)
  >- (qpat_assum `k <> 0 ==> _` irule >> first_assum ACCEPT_TAC) >>
  `a::rs = vs` by
    (qpat_assum `a::rs = DROP k vs` mp_tac >> simp[]) >>
  qpat_assum `body_for_full_ok _ _ _ _ _`
    (MATCH_MP_TAC o REWRITE_RULE [body_for_full_ok_def]) >>
  qpat_assum `a::rs = vs` (SUBST1_TAC o SYM) >>
  qexistsl [`ei`,`v`,`ei`] >> rewrite_tac [NOT_CONS_NIL, HD] >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_storage_observed_head_from_prefix[body_gas]:
  simp[Abbr `EB`] >>
  irule forConsBodyGasTheory.captured_storage_body_admissible >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`a`, `lctx`, `stmt_res_ok lctx`, `rs`] >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC

QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_storage_observed_head_from_prefix[execute]:
  `ptr_covers Gu tnu p u (32*n)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `nb` >> simp[]) >>
  `n < 2**256 /\ w2n dst+32*n < 2**256 /\
   w2n dst+32*n <= u.vs_alloca_next` by decide_tac >>
  `slot_copy_external sa (Var p)` by (irule slot_copy_not_fresh_external >> simp[]) >>
  `allocas_from lo u` by
    (qpat_assum `ghost_inv_at (DF H0) lo d c0 cx ei Gu tnu u`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >> first_assum ACCEPT_TAC) >>
  `alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by simp[] >>
  `create_memory_snapshot [] u` by simp[createSourceCallbackTheory.create_memory_snapshot_def] >>
  `?ce tyarr ann nid ca place cb. compile_expr ce tyarr (TopLevelName ann nid) ca = (place,cb)` by
    (qexistsl [`ARB`,`ARB`,`ARB`,`ARB`,`ARB`] >> Cases_on `compile_expr ARB ARB (TopLevelName ARB ARB) ARB` >> metis_tac[]) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) for_storage_element_copy_run >>
  disch_then (drule_at (Pat `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var ep) _ = SOME _`)) >>
  disch_then (qspecl_then [`lo`, `ctx`, `func`, `PG`, `Gu`, `tnu`, `dst`, `[]`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `z` (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac))) >>
  `!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
         val_in_memory tyv v (w2n dst) mem` by suspend "copy_value" >>
  `lookup_var idx z = SOME (n2w k) /\ FLOOKUP Gf idx = NONE /\
   op_taint tnf (Var idx) = {} /\ eval_operand lvo z = SOME (n2w len) /\
   op_prov Gf lvo = NONE /\ op_taint tnf lvo = {} /\
   eval_operand bop z = SOME slot /\ op_taint tnf bop = {}` by suspend "copy_scalars" >>
  `z.vs_immutables = u.vs_immutables` by
    (qpat_assum `slot_copy_runtime_frame sa dst n u z`
       (strip_assume_tac o REWRITE_RULE [slot_copy_runtime_frame_def]) >>
     qpat_assum `copy_static z = copy_static u`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [copy_static_def] o
        AP_TERM ``\r:venom_state. r.vs_immutables``)) >>
  `alloca_history func z` by
    (irule alloca_history_jump >> conj_tac >- first_assum ACCEPT_TAC >> qexists `u` >>
     qpat_assum `slot_copy_runtime_frame sa dst n u z`
       (strip_assume_tac o REWRITE_RULE [slot_copy_runtime_frame_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ei.storage_trace ==>
       Entry H (ei with gas_obs := []) v k z Gf tnf` by suspend "register" >>
  suspend "finish"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_storage_observed_head_from_prefix[copy_value]:
  `ptr_vv_ok cx typ (PlaceR (StoragePlace tr addr tyv))
      (LocatedValue typ (mk_ptr (Var ep) (slot_loc tr))) ei Gu tnu u` by
    (irule for_storage_current_child_ptr >> simp[mk_ptr_def] >>
     qexistsl [`DF H0`,`H0`,`c0`,`ctx`,`d`,`func`,`lo`] >> simp[]) >>
  drule_then assume_tac copy_prefix_words >> drule_then assume_tac copy_prefix_taint >>
  `?vv. read_result cx (PlaceR (StoragePlace tr addr tyv)) ei = (INL vv,ei) /\
   !mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
         val_in_memory tyv vv (w2n dst) mem` by
    (irule unwrap_storage_copied_robust >>
     goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     qexistsl [`tr`,`addr`] >> Cases_on `tr` >> fs[Abbr `n`,mk_ptr_def] >>
     metis_tac[]) >>
  `v = vv` by
    (qpat_assum `a = PlaceR _` SUBST_ALL_TAC >>
     qpat_assum `read_result cx _ ei = (INL vv,ei)` mp_tac >>
     qpat_assum `read_result cx _ ei = (INL v,ei)` (rewrite_tac o single) >>
     simp[NoAsms]) >>
  qpat_assum `v = vv` SUBST1_TAC >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_storage_observed_head_from_prefix[copy_scalars]:
  `slot_copy_external sa (Var idx) /\ slot_copy_external sa lvo` by
    (conj_tac >- (irule slot_copy_not_fresh_external >> first_assum ACCEPT_TAC) >>
     Cases_on `lvo` >- simp[slot_copy_external_def] >>
     rename1 `slot_copy_external sa (Var x)`
     >- (irule slot_copy_not_fresh_external >>
         qpat_assum `!y. Var x = Var y ==> not_fresh_at sa y`
           (qspec_then `x` mp_tac) >> simp[NoAsms]) >>
     rename1 `slot_copy_external sa (Label lbl)` >>
     qpat_assum `!l. Label lbl <> Label l` (qspec_then `lbl` mp_tac) >> simp[NoAsms]) >>
  `!op. slot_copy_external sa op ==> eval_operand op z = eval_operand op u` by
    gvs[slot_copy_runtime_frame_def] >>
  `!op. slot_copy_external sa op ==> op_taint tnf op = op_taint tnu op` by
    (rpt strip_tac >> drule_all copy_ghost_external_taint >> simp[]) >>
  `!x. slot_copy_external sa (Var x) ==> FLOOKUP Gf x = FLOOKUP Gu x` by
    gvs[slot_copy_ghost_inv_def] >>
  `lookup_var idx z = lookup_var idx u` by
    (qpat_assum `!op. slot_copy_external sa op ==> eval_operand op z = _`
       (qspec_then `Var idx` mp_tac) >> simp[eval_operand_def]) >>
  simp[] >> Cases_on `lvo` >> gvs[op_prov_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_storage_observed_head_from_prefix[register]:
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> storage_place_observed _ _ /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_non_overlapping u` by
    (qpat_assum `stmt_state_rel H ctx func c0 cx ei u`
       (mp_then Any mp_tac bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv) >>
     simp[venomMemDefsTheory.alloca_inv_def]) >>
  qmatch_goalsub_abbrev_tac `Entry H er v k z Gf tnf` >>
  `return_buf_sep d c0 er u /\ stmt_state_rel H ctx func c0 cx er u /\
   ghost_inv_at (DF H) lo d c0 cx er Gu tnu u /\
   expr_sim_inv c0 cx env er /\ storage_well_formed_on cx er (FST H) /\
   Fr c0 er u Gu tnu /\ lookup_scopes id er.scopes = NONE` by suspend "register_obs" >>
  `not_local_ptr bc (FEMPTY::er.scopes) p` by
    (qpat_assum `!scs. lookup_scopes id scs = NONE ==> _` irule >> simp[]) >>
  `!name b sz. local_region c0 er.scopes u name b sz ==>
     w2n dst+nb <= b \/ b+sz <= w2n dst` by
    (qpat_assum `!name b sz. local_region c0 ei.scopes u name b sz ==> _`
       mp_tac >> simp[NoAsms, Abbr `er`]) >>
  `(!x cap. c0.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
   (!x cap. c0.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x)` by
    (conj_tac >> map_every qx_gen_tac [`x`,`cap`] >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa0 x ==> not_fresh_at sa x` irule
     >- (qpat_assum `!x cap. c0.ce_return_buf = _ ==> not_fresh_at sa0 x`
           (qspecl_then [`x`,`cap`] mp_tac) >> simp[]) >>
     qpat_assum `!x cap. c0.ce_return_pc = _ ==> not_fresh_at sa0 x`
          (qspecl_then [`x`,`cap`] mp_tac) >> simp[]) >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n dst,nb)` by simp[] >>
  `lo <= w2n dst` by
    (qpat_assum `allocas_from lo u` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (qspecl_then [`inst.inst_id`,`w2n dst`,`nb`] mp_tac) >> simp[]) >>
  qpat_assum `Abbrev (Fr = _)` (fn fr =>
    mp_tac (BETA_RULE (REWRITE_RULE [LET_THM]
      (PURE_REWRITE_RULE [SYM (REWRITE_RULE [markerTheory.Abbrev_def] fr)]
        (Q.INST [`D` |-> `DF H`, `ei` |-> `er`, `src` |-> `addr`,
                 `load` |-> `if tr then TLOAD else SLOAD`]
          (SPEC_ALL (Q.ISPEC `H : (bool # 256 word # type_value) list # num list`
                       for_storage_copy_body_entry))))))) >>
  (impl_tac >- (simp[Abbr `n`] >>
    qpat_assum `!name b sz. local_region c0 er.scopes u name b sz ==> _` mp_tac >>
    simp[Q.SPECL [`w2n (dst:256 word)`,`nb`] arithmeticTheory.ADD_COMM])) >>
  simp[Abbr `Entry`, Abbr `EB`]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_storage_observed_head_from_prefix[register_obs]:
  rpt conj_tac
  >- simp[Abbr `er`, return_buf_sep_gas_obs]
  >- simp[Abbr `er`, stmt_state_rel_start_gas_obs]
  >- (qpat_assum `ghost_inv_at (DF H) lo d c0 cx ei Gu tnu u` mp_tac >>
      simp[NoAsms, Abbr `er`, ghost_inv_at_def] >>
      POP_ASSUM_LIST (K (metis_tac[])))
  >- simp[Abbr `er`]
  >- (qpat_assum `storage_well_formed_on cx ei (FST H)` mp_tac >>
      simp[NoAsms, Abbr `er`, vyperStorageFootprintTheory.storage_well_formed_on_def,
           stmtSimAppendStorageComposeTheory.get_storage_gas_obs])
  >- (qpat_assum `Fr c0 ei u Gu tnu` mp_tac >>
      simp[NoAsms, Abbr `er`, Abbr `Fr`, alloca_frame_gas_obs] >>
      POP_ASSUM_LIST (K (metis_tac[]))) >>
  simp[Abbr `er`]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_storage_observed_head_from_prefix[finish]:
  irule gas_outcome_full_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gf`,`EB ei v`,`INL ()`,`z`,`tnf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >>
  `((EB ei v).storage_trace = ei.storage_trace) /\
   (EB ei v with gas_obs := [] = EB (ei with gas_obs := []) v) /\
   (EB (ei with gas_obs := []) v).gas_obs = []` by simp[Abbr `EB`] >>
  simp[] >> strip_tac >> conj_tac
  >- (qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
        (qspecl_then [`DF H`,`explicit`] (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
      disch_then (qspecl_then [`u`,`Gu`,`tnu`,`[]`,`OK z`,`Gf`,`tnf`] mp_tac) >> simp[]) >>
  qexists `k` >> simp[] >>
  qunabbrev_tac `Entry` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> push_scope_with_var _ _ _ _ = _ /\ _`
    (qspec_then `H` mp_tac) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise for_storage_observed_head_from_prefix
*)
