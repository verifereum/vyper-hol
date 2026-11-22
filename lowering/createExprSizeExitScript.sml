(* Relate an oversized CREATE reached in a single expression invocation
   to the source initcode-size check. Completed INVOKEs contribute their
   own GAS observations to the caller's prefix. *)
Theory createExprSizeExit
Ancestors
  abiEncoderProps bodyFullPreds e2eDefs exprSimFullBundleProps fragExec
  fragGasOrigin fragGasOriginPtr gasExplicitSites gasSummary s1PrefixDefs
  venomExecSemantics venomInst venomState vyperCreate vyperInterpreter
  vyperState relation list words createMarkedPath pair
  createResultTail bodyFullIfExpReach builtinCreate arithmetic createSizeDispatch exprLowering stmtLoweringMono vfmConstants createSizeCutRegion createSizeCutEntry createSizeCutCode compilerInstructionSuffix loweringShapeRules externalEntryShape compileEnv createSizeItinerary exprLoweringProps fragFuel exprBodyPreProps exprSimCopy exprSimSource bodySimStmtFacts vyperStorageTrace fragGasOriginPtrExec gasSummaryCompose bodyMemoryDefs exprOperandVar freshWrites rich_list exprSimHypsDefs createSizeBlueprintOffset vyperTypeEvalProofs vyperTypeSystem vyperTypeExprSoundness exprSimWordArgs createCtorSavedSimple accountsRelProps gasCount exprSimHyps gasOutcomeFull bodyPtrDefs loweringPosts createSizeOperandCode createSizeCtorCutSpine createSizeFixedPreparation createSizeConcreteSnapshots createSizeLocationCode createSizeEncodeCode context createSizeRawSource createSizeSnapshotLength fragGasPath bodyInvCodeProps vyperAST vyperStorageFootprint vyperStorageBackend supportedExprTraverse allocLimits vyperTypeCallGraph vyperTyping vyperValue createSizeStraightPrefix createSizeCopyLength createSizeCopyScalarCode ghostPcTransportPtr exprSimSend integer_word valueEncoding createCtorPrivateSnapshot createCtorSegmentArrival createSizeEdgePC abiBufferAllocationCode bodyFullExtCallPosList bodyFullExtCallPosAggregate abiEncodeArgsSim abiEncodeArgsCase exprSimMemorySource bodyFullHashKeccakFixed aggregateEvaluatedLayout exprSimIfExpWidenedPhysicalType exprSimSubscriptArrayCompose loweringStateRelDefs exprSimMemDefs createSizeBlueprintRawLength bodyFullGhostFrame assignTuplePtrLoadStep augAssignFullLoadFrame contextRawReachable stateFrame ptrDiscipline stmtReasonMemory emitHelperProps createSizeRawStraightBands createSizeRawSlotBand createSizeRawCodeSiteBound createSizeRawHeaderGeometry reasonEndpointResourcesPtr createBlueprintRawCopyLayout venomExecProofs createSizeRawSnapshotEntry
  createCtorObservedSilence createCtorPayloadLength bodyFullExtCallDirectState
  bodyPtrMakeArrayPrimitiveInstall bodyPtrMakeArrayEmission venomInstProofs1 gasEvents dallocaBlueprintArgs compileUnit structFieldsProps bodySim loweringShapeDefs createSizeBlueprintOuterPairedCode createSizeBlueprintRawPayloadCode createSizeBlueprintAbiPayloadCode
  createSizeBlueprintExtent createSizeRawPairedCode createSizeRawExtent createOperandSizeReject

(* Restrict caller edges to this invocation's emitted fragment. An INVOKE
 * which returns is one caller edge, with its children's GAS marks. *)
Definition create_expr_prefix_def:
  create_expr_prefix sa sb explicit ctx func s0 marks s <=>
    RTC
      (\(u, left) (v, all).
         ?bb inst right.
           (u.vs_current_bb <> sb.cs_current_bb \/
            u.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
           lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
           get_instruction bb u.vs_inst_idx = SOME inst /\
           inst.inst_id IN frag_ids sa sb /\
           gas_origin_edge F explicit ctx func u right (OK v) /\
           all = left ++ right)
      (s0, []) (s, marks)
End

(* A completed operand replays the GAS observations of this invocation.
   Its successful arm carries the same value and ghost posts as full
   expression simulation. An exempt source error can happen before the cut. *)
Definition gas_completed_operand_def:
  gas_completed_operand (DF, lo, explicit, ctx, func, PG)
      tops cx st0 sa sb source (es, s0, G0, tn0) Q <=>
    !H0 marks s tail res ee.
      create_expr_prefix sa sb explicit ctx func s0 marks s /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      source (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (res, ee) /\
      valid_horizon cx st0 H0 ee.storage_trace ==>
      (?G tn.
         ee.gas_obs = tail /\
         !H. valid_horizon cx st0 H ee.storage_trace ==>
           gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
             (s0,G0,tn0) marks (OK s,G,tn) /\
           Q H res (ee with gas_obs := []) G tn s) \/
      (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err)
End

Definition create_operand_completed_ok_def:
  create_operand_completed_ok cx e <=>
    !DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      expr_body_pre cenv cx env e es ==>
      (!st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
        expr_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
          cenv cx ty e es (st0, sa, sb, shadow_sa, shadow_sb, op, s0, G0, tn0) ==>
        gas_completed_operand
          (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
          tops cx st0 sa sb (bind (eval_expr cx e) (read_result cx))
          (es, s0, G0, tn0)
          (expr_sim_full_post (DF, lo, d, ctx, func) cenv cx e
            (es, sa, sb, s0, op, G0, tn0))) /\
      (!st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
        expr_vv_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
          cenv cx ty e es (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) ==>
        gas_completed_operand
          (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
          tops cx st0 sa sb (eval_expr cx e) (es, s0, G0, tn0)
          (\H res ee G tn t. ?tv. res = INL tv /\
            vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
            vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
              ee tv vv t /\
            alloca_history func t /\
            (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
            s0.vs_alloca_next <= t.vs_alloca_next /\
            ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
            ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
            (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
               ~is_bytestring_type (post_value_type cenv e) ==>
               vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
               (!t' p. vv = LocatedValue t' p ==>
                       p.ptr_location = LocMemory)) /\
            (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
             ?val. read_result cx tv ee = (INL val, ee) /\
                 !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) =
                          SOME rt /\
                        eval_operand (vv_operand vv) t = SOME w ==>
                        w2n w + type_memory_size rt <= lo /\
                        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                               val_in_memory rt val (w2n w) mem)) /\
            (!t' op. vv = StackValue t' op /\
                   ~is_word_type (post_value_type cenv e) ==>
                     ptr_buf_ok cenv e op G t) /\
            (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv e p.ptr_operand G t) /\
            ghost_kept_at lo cenv es sa G0 tn0 s0 G tn))
End

Definition create_expr_size_exit_def:
  create_expr_size_exit cx e <=>
    !DF lo d (PG : (num # num) option list) tops
      ctx shadow_ctx func shadow_func cenv env ty es
      st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      expr_body_pre cenv cx env e es /\
      expr_vv_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) ==>
      !H marks s bb inst value off sz salt w tail res ee.
        create_expr_prefix sa sb (gas_explicit_sites ctx shadow_ctx)
          ctx func s0 marks s /\
        (s.vs_current_bb <> sb.cs_current_bb \/
         s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
        lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst /\
        inst.inst_id IN frag_ids sa sb /\
        (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
             MEM j.inst_opcode [CREATE; CREATE2] ==> j.inst_id <= inst.inst_id) /\
        ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value; off; sz]) \/
         (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value; off; sz; salt])) /\
        eval_operand sz s = SOME w /\ 2 * max_code_size < w2n w /\
        eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (res, ee) /\
        valid_horizon cx st0 H ee.storage_trace ==>
        res = INR (Error (RuntimeError "create initcode too large")) \/
        (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err)
End

Definition create_prefix_step_def:
  create_prefix_step sa sb explicit ctx func u right v <=>
    ?bb inst.
      (u.vs_current_bb <> sb.cs_current_bb \/
       u.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
      lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME inst /\
      inst.inst_id IN frag_ids sa sb /\
      gas_origin_edge F explicit ctx func u right (OK v)
End

Theorem create_expr_prefix_marked:
  create_expr_prefix sa sb explicit ctx func u ms v <=>
    RTC (create_marked_edge (create_prefix_step sa sb explicit ctx func))
      (u,[]) (v,ms)
Proof
  rewrite_tac[create_expr_prefix_def] >> AP_THM_TAC >> AP_THM_TAC >>
  AP_TERM_TAC >>
  simp[FUN_EQ_THM, FORALL_PROD, create_marked_edge_def, create_prefix_step_def] >>
  metis_tac[]
QED

(* P is the region of the next compiler action, including its entry. The
   local successor fact is needed only off its continuation PC. *)

Theorem create_size_prefix_first_cut:
  create_expr_prefix sa sb explicit ctx func s ms t /\
  (s.vs_current_bb = m.cs_current_bb /\
   s.vs_inst_idx = LENGTH m.cs_current_insts \/ P s) /\
  ((t.vs_current_bb = m.cs_current_bb /\
    t.vs_inst_idx = LENGTH m.cs_current_insts) \/ ~P t) /\
  (!u right v. P u /\ create_prefix_step sa sb explicit ctx func u right v /\
     (u.vs_current_bb <> m.cs_current_bb \/
      u.vs_inst_idx <> LENGTH m.cs_current_insts) ==>
     create_prefix_step a m explicit ctx func u right v /\
     (v.vs_current_bb = m.cs_current_bb /\
      v.vs_inst_idx = LENGTH m.cs_current_insts \/ P v)) ==>
  ?w left right.
    w.vs_current_bb = m.cs_current_bb /\
    w.vs_inst_idx = LENGTH m.cs_current_insts /\
    create_expr_prefix a m explicit ctx func s left w /\
    create_expr_prefix sa sb explicit ctx func w right t /\
    ms = left ++ right
Proof
  rewrite_tac[create_expr_prefix_marked] >>
  disch_then (CONJUNCTS_THEN2 (assume_tac o MATCH_MP create_marked_rtc_first_cut)
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `!A Inv Q. _`
    (qspecl_then [`create_prefix_step a m explicit ctx func`, `P`,
       `\v. v.vs_current_bb = m.cs_current_bb /\
            v.vs_inst_idx = LENGTH m.cs_current_insts`] mp_tac) >>
  simp[] >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qx_choose_then `wms` strip_assume_tac) >>
  PairCases_on `wms` >> fs[] >>
  drule create_marked_rtc_rebase >> disch_then (qspec_then `[]` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem create_size_replay_value_cut:
  !cx e DF lo d (PG : (num # num) option list) tops
    ctx shadow_ctx func shadow_func cenv env ty es
    st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    expr_body_pre cenv cx env e es /\
    expr_sim_full_pre
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e es
      (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) /\
    create_operand_completed_ok cx e ==>
    gas_completed_operand
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      tops cx st0 sa sb (bind (eval_expr cx e) (read_result cx))
      (es,s0,G0,tn0)
      (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e
        (es,sa,sb,s0,op,G0,tn0))
Proof
  strip_tac >> metis_tac[create_operand_completed_ok_def]
QED

(* Used by create_expr_size_exit: value-valued operand replay. *)

Theorem create_size_replay_vv_cut:
  !cx e DF lo d (PG : (num # num) option list) tops
    ctx shadow_ctx func shadow_func cenv env ty es
    st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    expr_body_pre cenv cx env e es /\
    expr_vv_sim_full_pre
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e es
      (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
    create_operand_completed_ok cx e ==>
    gas_completed_operand
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      tops cx st0 sa sb (eval_expr cx e) (es,s0,G0,tn0)
      (\H res ee G tn t. ?tv. res = INL tv /\
        vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
        vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
          ee tv vv t /\
        alloca_history func t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
        ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
        (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
           ~is_bytestring_type (post_value_type cenv e) ==>
           vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
           (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
        (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
         ?val. read_result cx tv ee = (INL val,ee) /\
             !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
               eval_operand (vv_operand vv) t = SOME w ==>
               w2n w + type_memory_size rt <= lo /\
               (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                  val_in_memory rt val (w2n w) mem)) /\
        (!t' op. vv = StackValue t' op /\
           ~is_word_type (post_value_type cenv e) ==>
             ptr_buf_ok cenv e op G t) /\
        (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
             ptr_buf_ok cenv e p.ptr_operand G t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
Proof
  strip_tac >> metis_tac[create_operand_completed_ok_def]
QED

Theorem create_dispatch_no_return:
  cs_extends sa sc /\ emit_op opc ops sc = (created,sd) /\
  MEM opc [CREATE;CREATE2] /\
  compile_check_create_result created rof sd = (result,sb) /\
  fn_has_code sa sb func /\ body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  create_expr_prefix sa sb explicit ctx func s marks t /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (t.vs_current_bb <> sb.cs_current_bb \/ t.vs_inst_idx <> LENGTH sb.cs_current_insts) ==>
  t = s /\ marks = []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_result_tail_dispatch_code >> strip_tac >>
  `~is_terminator i.inst_opcode` by
    fs[is_terminator_def] >>
  qpat_x_assum `MEM opc _` kall_tac >>
  `~(t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)`
    by metis_tac[] >>
  qpat_x_assum `_ \/ _` kall_tac >>
  qpat_x_assum `create_expr_prefix _ _ _ _ _ _ _ _` mp_tac >>
  simp[create_expr_prefix_marked] >> once_rewrite_tac[RTC_CASES1] >>
  strip_tac
  >- (fs[] >> metis_tac[]) >>
  rename1 `RTC _ mid (t,marks)` >>
  PairCases_on `mid` >> gvs[create_marked_edge_def] >>
  rename1 `RTC _ (mid0,mid1) (t,marks)` >>
  `gas_origin_edge F explicit ctx func s mid1 (OK mid0)` by
    fs[create_prefix_step_def] >>
  `mid0.vs_current_bb = sd.cs_current_bb /\ mid0.vs_inst_idx = LENGTH sd.cs_current_insts` by
    (`lookup_block s.vs_current_bb func.fn_blocks = SOME cb /\
      get_instruction cb s.vs_inst_idx = SOME i` by simp[] >>
     drule_all createSizeEdgePCTheory.create_ok_edge_pc >> simp[]) >>
  reverse (Cases_on `rof`)
  >- (gvs[compile_check_create_result_def, compileEnvTheory.comp_return_def] >>
      qpat_x_assum `RTC _ (mid0,mid1) _` mp_tac >>
      once_rewrite_tac[RTC_CASES1] >> simp[] >>
      simp[EXISTS_PROD, create_marked_edge_def, create_prefix_step_def] >> strip_tac >> gvs[]) >>
  drule_all create_result_check_layout >> strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  rename1 `j.inst_operands = [created; Label sb.cs_current_bb; Label fail_lab]` >>
  `fail_lab <> sd.cs_current_bb` by
    (strip_tac >> gvs[] >>
     qpat_x_assum `MAP _ _ = _` (mp_tac o AP_TERM ``LAST : opcode list -> opcode``) >>
     simp[]) >>
  `get_instruction cb (LENGTH sd.cs_current_insts) = SOME j` by
    gvs[get_instruction_def, EL_APPEND_EQN] >>
  qabbrev_tac `region = \u:venom_state.
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = 0 \/
    u.vs_current_bb = fail_lab /\ u.vs_inst_idx < 4 \/
    u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts` >>
  `!u ms v. region u /\ create_prefix_step sa sb explicit ctx func u ms v ==>
     region v` by
    (simp[Abbr `region`] >> rpt gen_tac >> strip_tac >>
     fs[create_prefix_step_def] >> gvs[]
     >- (drule_all create_result_tail_fail_step >> simp[]) >>
     `lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME inst'` by simp[] >>
     drule_all create_result_tail_branch >> strip_tac >> simp[]) >>
  `region t` by
    (`region mid0` by simp[Abbr `region`] >>
     drule_all create_result_marked_invariant >> simp[]) >>
  gvs[Abbr `region`]
QED

Theorem create_size_exit_proxy:
  !cx ann has_salt rof ks args dflt.
    create_expr_size_exit cx
      (Call ann (CreateTarget CreateMinimalProxy has_salt rof ks) args dflt)
Proof
  rewrite_tac[create_expr_size_exit_def] >>
  rpt (gen_tac ORELSE disch_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  qpat_x_assum `compile_expr _ _ (Call _ _ _ _) _ = _` mp_tac >>
  rewrite_tac[exprSimSendTheory.compile_expr_call, compile_call_def] >>
  Cases_on `compile_create_call compile_expr cenv CreateMinimalProxy has_salt rof args sa` >>
  pure_rewrite_tac[as_stack_val_def, pairTheory.PAIR_EQ] >>
  disch_then (SUBST_ALL_TAC o CONJUNCT2) >>
  `!ce ty e st. ci_mono st (SND (compile_expr ce ty e st))` by
    simp[ci_mono_compile_expr_sa] >>
  `MEM inst.inst_opcode [CREATE; CREATE2]` by
    (simp[] >> metis_tac[]) >>
  drule_all create_size_dispatch_identification >> strip_tac >>
  qmatch_asmsub_rename_tac `create_size_dispatch_tail _ _ _ _ _ _ _ dispatch_salt _ _` >>
  `~(2 * max_code_size < w2n (54w:256 word))` by
    (rewrite_tac[max_code_size_def, w2n_n2w, dimword_def,
                 venomLayoutTheory.dimindex_256] >> EVAL_TAC) >>
  Cases_on `dispatch_salt` >> gvs[mk_inst_def, eval_operand_def]
QED

Theorem create_copy_operand_body_pre[local]:
  expr_body_pre cenv cx env
    (Call ann (CreateTarget CreateCopyOf hs rof ks) args dflt) es /\
  MEM e args /\ expr_sim_inv cenv cx env em ==>
  expr_body_pre cenv cx env e em
Proof
  rw[expr_body_pre_split_def, expr_body_pre_mods_def,
     well_typed_expr_def, int_calls_expr_def, byte_widths_expr_def,
     alloc_limits_expr_def, supported_expr_exists_def,
     supported_exprs_exists_every, EXISTS_MEM, expr_has_evm_run_thm] >>
  TRY (first_assum ACCEPT_TAC) >>
  FIRST [metis_tac[expr_sim_inv_split_def],
         metis_tac[well_typed_exprs_member], metis_tac[byte_widths_exprs_mem],
         metis_tac[alloc_limits_exprs_mem], metis_tac[call_evaluation_safe_exprs_mem],
         metis_tac[int_calls_exprs_every_mem], metis_tac[]]
QED

Theorem create_copy_first_scalar_pre[local]:
  expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty call es (st0,sa,sb,sha,shb,vv,s,G,tn) /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,a) /\
  lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) sha = (op,b) /\
  gas_shadow_state a b /\ fn_has_code sa a func /\ fn_has_code sha b shadow_func /\
  expr_body_pre cenv cx env e es ==>
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es (st0,sa,a,sha,b,op,s,G,tn)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_gas_admissible >>
  fs[expr_vv_sim_full_pre_def, expr_sim_full_pre_def] >> metis_tac[]
QED

Theorem create_copy_next_scalar_pre[local]:
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es (st0,sa,sb,sha,shb,op,s,G,tn) /\
  lower_value compile_expr cenv (expr_type f) f sb = (operand,sc) /\
  lower_value compile_expr cenv (expr_type f) (gas_shadow_expr f) shb = (operand,shc) /\
  gas_shadow_state sc shc /\ fn_has_code sb sc func /\ fn_has_code shb shc shadow_func /\
  expr_body_pre cenv cx env f (em with gas_obs := []) /\
  valid_horizon cx st0 H em.storage_trace /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) marks (OK t,G1,tn1) /\
    expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e
      (es,sa,sb,s,op,G,tn) H (res : value + vyperState$exception)
      (em with gas_obs := []) G1 tn1 t) ==>
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type f) f (em with gas_obs := []) (st0,sb,sc,shb,shc,operand,t,G1,tn1)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_gas_admissible >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[expr_sim_full_pre_def]) >>
  `ci_mono sa sb` by (metis_tac[ci_mono_lower_value_compile_expr, SND]) >>
  `sa.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
  qpat_assum `!h. valid_horizon _ _ h em.storage_trace ==> _`
    (qspec_then `H` (fn th => drule_then strip_assume_tac th)) >>
  qpat_x_assum `expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def,expr_post_def]) >>
  drule_then strip_assume_tac expr_sim_full_endpoint_fields >>
  `~t.vs_halted` by
    (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `!fn inst s'. frag_reachable ctx func t fn inst s' ==> dalloca_no_wrap inst s'` by
    (drule gas_origin_ptr_path_dalloca_no_wrap >> simp[] >>
     disch_then (fn th => rpt gen_tac >> strip_tac >> irule th) >>
     conj_tac >- first_assum ACCEPT_TAC >> goal_assum drule) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s` (irule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv sb` by (drule_all compiler_ci_mono_reserved >> simp[]) >>
  simp[expr_sim_full_pre_def] >>
  conj_tac >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!h. valid_horizon _ _ h em.storage_trace ==> _`
    (fn th => first_x_assum (fn h => assume_tac (MATCH_MP th h))) >>
  qpat_x_assum `_ /\ expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def,expr_post_def]) >> simp[]
QED

(* Evaluate one actual source head. The continuation need only preserve the
   trace prefix; neither its successful return nor its own GAS use is assumed. *)

Theorem create_copy_scalar_cut[local]:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env e es /\ create_operand_completed_ok cx e /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es (st0,sa,sb,sha,shb,op,s,G,tn) /\
  create_expr_prefix sa sb (gas_explicit_sites ctx shadow_ctx) ctx func s marks t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!v. storage_trace_frame (k v)) /\
  bind (bind (eval_expr cx e) (read_result cx)) k
    (es with gas_obs := gas_explicit (marks ++ rest) s.vs_gas_readings ++ tail) = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  (?v em G1 tn1.
    k v ((em with gas_obs := []) with gas_obs := gas_explicit rest t.vs_gas_readings ++ tail) = (res,ee) /\
    expr_sim_inv cenv cx env em /\ valid_horizon cx st0 H em.storage_trace /\
    accounts_agree H cx.txn.target em.accounts t.vs_accounts /\ accounts_well_typed em.accounts /\
    !h. valid_horizon cx st0 h em.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1) /\
      expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e
        (es,sa,sb,s,op,G,tn) h (INL v : value + vyperState$exception)
        (em with gas_obs := []) G1 tn1 t)
Proof
  strip_tac >> drule_all_then assume_tac create_size_replay_value_cut >>
  qabbrev_tac `inp = es with gas_obs := gas_explicit (marks ++ rest) s.vs_gas_readings ++ tail` >>
  namedCases_on `bind (eval_expr cx e) (read_result cx) inp` ["r em"] >>
  `valid_horizon cx st0 H em.storage_trace` by
    (Cases_on `r` >> fs[bind_def] >>
     qpat_assum `!v. storage_trace_frame (k v)` (qspec_then `x` assume_tac) >>
     drule_all_then strip_assume_tac storage_trace_frame_prefix >>
     metis_tac[valid_horizon_append]) >>
  qpat_x_assum `gas_completed_operand _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[gas_completed_operand_def]) >>
  disch_then (qspecl_then [`H`,`marks`,`t`,
    `gas_explicit rest (DROP (LENGTH marks) s.vs_gas_readings) ++ tail`,`r`,`em`] mp_tac) >>
  impl_tac
  >- (simp[] >> metis_tac[Abbr `inp`, gas_explicit_append, APPEND_ASSOC]) >>
  strip_tac
  >- (qpat_assum `!h. valid_horizon _ _ h em.storage_trace ==> _`
        (qspec_then `H` (fn th => drule_then strip_assume_tac th)) >>
      qpat_assum `expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def,expr_post_def]) >>
      drule_then assume_tac gas_origin_ptr_path_erase >>
      `gas_explicit rest (DROP (LENGTH marks) s.vs_gas_readings) =
       gas_explicit rest t.vs_gas_readings` by
        (drule_then (qspec_then `rest` mp_tac) gas_explicit_append_path >>
         simp[gas_explicit_append]) >>
      `expr_sim_inv cenv cx env em` by
        (`expr_body_pre cenv cx env e inp` by
           simp[Abbr `inp`] >>
         drule_all (REWRITE_RULE[ETA_THM] expr_body_pre_eval) >> simp[]) >>
      disj2_tac >> map_every qexists_tac [`v`,`em`,`G'`,`tn'`] >>
      `em with gas_obs := gas_explicit rest t.vs_gas_readings ++ tail = em` by
        simp[evaluation_state_component_equality] >>
      `k v em = (res,ee)` by fs[bind_def] >>
      simp[] >>
      conj_tac >- (fs[stmt_state_rel_def] >> drule state_rel_accounts >> simp[]) >>
      conj_tac >- fs[expr_sim_inv_def] >>
      qpat_x_assum `!h. valid_horizon _ _ h em.storage_trace ==> _` mp_tac >>
      qpat_x_assum `r = INL _` SUBST_ALL_TAC >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  fs[bind_def] >> metis_tac[]
QED

Theorem create_copy_source_cons[local]:
  bind (eval_exprs cx (e::args)) k =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. bind (eval_exprs cx args) (\vs. k (v::vs)))
Proof
  simp[eval_exprs_cons_action, bind_assoc, bind_return]
QED

Theorem create_copy_list_cut[local]:
  bind (eval_exprs cx (e::args)) k
    (es with gas_obs := gas_explicit whole s.vs_gas_readings ++ tail) = (res,ee) ==>
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es (st0,sa,sb,sha,shb,op,s,G,tn) ==>
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env e es /\ create_operand_completed_ok cx e /\
  create_expr_prefix sa sb (gas_explicit_sites ctx shadow_ctx) ctx func s marks t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!vs. storage_trace_frame (k vs)) /\ valid_horizon cx st0 H ee.storage_trace /\
  whole = marks ++ rest ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  (?v em G1 tn1.
    bind (eval_exprs cx args) (\vs. k (v::vs))
      ((em with gas_obs := []) with gas_obs := gas_explicit rest t.vs_gas_readings ++ tail) = (res,ee) /\
    expr_sim_inv cenv cx env em /\ valid_horizon cx st0 H em.storage_trace /\
    accounts_agree H cx.txn.target em.accounts t.vs_accounts /\ accounts_well_typed em.accounts /\
    !h. valid_horizon cx st0 h em.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1) /\
      expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e
        (es,sa,sb,s,op,G,tn) h (INL v : value + vyperState$exception)
        (em with gas_obs := []) G1 tn1 t)
Proof
  rpt strip_tac >> qpat_x_assum `whole = _` SUBST_ALL_TAC >>
  qpat_x_assum `bind (eval_exprs _ _) _ _ = _` (assume_tac o REWRITE_RULE[create_copy_source_cons]) >>
  `!v. storage_trace_frame (bind (eval_exprs cx args) (\vs. k (v::vs)))` by
    (gen_tac >> irule storage_trace_frame_bind_all >> simp[evaluate_storage_trace_frame]) >>
  drule_at (Pat `bind (bind _ _) _ _ = _`) create_copy_scalar_cut >>
  disch_then (irule o BETA_RULE) >>
  qpat_assum `expr_sim_full_pre _ _ _ _ _ _ _` (irule_at Any) >> simp[]
QED

(* After the last scalar, the continuation's result is irrelevant unless
   it carries an exemption. The successful head already supplies accounts. *)

Theorem create_copy_last_accounts[local]:
  bind (eval_exprs cx [e]) k
    (es with gas_obs := gas_explicit (marks ++ rest) s.vs_gas_readings ++ tail) = (res,ee) ==>
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,(PG : (num # num) option list),func,shadow_func)
    cenv cx (expr_type e) e es (st0,sa,sb,sha,shb,op,s,G,tn) ==>
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env e es /\ create_operand_completed_ok cx e /\
  create_expr_prefix sa sb (gas_explicit_sites ctx shadow_ctx) ctx func s marks t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!vs. storage_trace_frame (k vs)) /\ valid_horizon cx st0 H ee.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  (?acc. accounts_agree H cx.txn.target acc t.vs_accounts /\ accounts_well_typed acc)
Proof
  rpt strip_tac >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   (?v em G1 tn1.
     bind (eval_exprs cx []) (\vs. k (v::vs))
       ((em with gas_obs := []) with gas_obs := gas_explicit rest t.vs_gas_readings ++ tail) = (res,ee) /\
     expr_sim_inv cenv cx env em /\ valid_horizon cx st0 H em.storage_trace /\
     accounts_agree H cx.txn.target em.accounts t.vs_accounts /\ accounts_well_typed em.accounts /\
     !h. valid_horizon cx st0 h em.storage_trace ==>
       gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s,G,tn) marks (OK t,G1,tn1) /\
       expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e
         (es,sa,sb,s,op,G,tn) h (INL v : value + vyperState$exception)
         (em with gas_obs := []) G1 tn1 t)` suffices_by metis_tac[] >>
  irule create_copy_list_cut >>
  qpat_assum `expr_sim_full_pre _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem create_copy_empty_cut[local]:
  create_expr_prefix a a explicit ctx func s marks t /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  t = s /\ marks = []
Proof
  simp[create_expr_prefix_marked] >>
  once_rewrite_tac[RTC_CASES1] >>
  simp[EXISTS_PROD, create_marked_edge_def, create_prefix_step_def, frag_ids_def] >> metis_tac[]
QED

Theorem create_copy_source_call[local]:
  eval_expr cx (Call ann (CreateTarget CreateCopyOf hs rof ks) args dflt) =
  bind (eval_exprs cx args)
    (eval_create_operands cx CreateCopyOf hs rof (MAP expr_type args)
      (blueprint_literal_offset cx hs args))
Proof
  PURE_ONCE_REWRITE_TAC [evaluate_def] >> Cases_on `args` >>
  simp[create_operand_order_def, FUN_EQ_THM, bind_def]
QED

Theorem create_copy_replay_accounts_at_cuts:
  has_salt = IS_SOME salt_e /\
  args = target_e::value_e::(case salt_e of NONE => [] | SOME e => [e]) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt) es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,(PG : (num # num) option list),func,shadow_func)
    cenv cx ty (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt) es
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
  EVERY (create_operand_completed_ok cx) (create_operand_order CreateCopyOf has_salt args) /\
  lower_value compile_expr cenv (expr_type target_e) target_e sa = (target,a1) /\
  lower_value compile_expr cenv (expr_type value_e) value_e a1 = (value,a2) /\
  compile_create_salt compile_expr cenv salt_e a2 = (salt,a3) /\
  lower_value compile_expr cenv (expr_type target_e) (gas_shadow_expr target_e) shadow_sa = (target,b1) /\
  lower_value compile_expr cenv (expr_type value_e) (gas_shadow_expr value_e) b1 = (value,b2) /\
  compile_create_salt compile_expr cenv (OPTION_MAP gas_shadow_expr salt_e) b2 = (salt,b3) /\
  gas_shadow_state a1 b1 /\ gas_shadow_state a2 b2 /\ gas_shadow_state a3 b3 /\
  fn_has_code sa a1 func /\ fn_has_code a1 a2 func /\ fn_has_code a2 a3 func /\
  fn_has_code shadow_sa b1 shadow_func /\ fn_has_code b1 b2 shadow_func /\ fn_has_code b2 b3 shadow_func /\
  create_expr_prefix sa a1 (gas_explicit_sites ctx shadow_ctx) ctx func s0 m1 u1 /\
  create_expr_prefix a1 a2 (gas_explicit_sites ctx shadow_ctx) ctx func u1 m2 u2 /\
  create_expr_prefix a2 a3 (gas_explicit_sites ctx shadow_ctx) ctx func u2 m3 u3 /\
  u1.vs_current_bb = a1.cs_current_bb /\ u1.vs_inst_idx = LENGTH a1.cs_current_insts /\
  u2.vs_current_bb = a2.cs_current_bb /\ u2.vs_inst_idx = LENGTH a2.cs_current_insts /\
  u3.vs_current_bb = a3.cs_current_bb /\ u3.vs_inst_idx = LENGTH a3.cs_current_insts /\
  eval_expr cx (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt)
    (es with gas_obs := gas_explicit (m1 ++ (m2 ++ (m3 ++ mr))) s0.vs_gas_readings ++ tail) = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  (?acc. accounts_agree H cx.txn.target acc u3.vs_accounts /\ accounts_well_typed acc)
Proof
  strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule body_inv_no_phi >> fs[expr_vv_sim_full_pre_def] >>
     disch_then (qspec_then `func` mp_tac) >> simp[]) >>
  `!e em. MEM e args /\ expr_sim_inv cenv cx env em ==> expr_body_pre cenv cx env e em` by
    (rpt strip_tac >> irule create_copy_operand_body_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env target_e es` by
    (qpat_assum `!e em. MEM e args /\ _ ==> _` irule >> simp[] >>
     drule expr_body_pre_static_facts >> simp[]) >>
  drule_all_then assume_tac create_copy_first_scalar_pre >>
  qpat_x_assum `eval_expr _ _ _ = _` (assume_tac o REWRITE_RULE [create_copy_source_call]) >>
  gvs[create_operand_order_def] >>
  qmatch_asmsub_abbrev_tac `bind (eval_exprs cx _) k _` >>
  `!vs. storage_trace_frame (k vs)` by simp[Abbr `k`,storage_trace_frame_create_operands] >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   (?v em G1 tn1.
     bind (eval_exprs cx (value_e::(case salt_e of NONE => [] | SOME e => [e])))
       (\vs. k (v::vs))
       ((em with gas_obs := []) with gas_obs := gas_explicit (m2 ++ (m3 ++ mr)) u1.vs_gas_readings ++ tail) = (res,ee) /\
     expr_sim_inv cenv cx env em /\ valid_horizon cx st0 H em.storage_trace /\
     accounts_agree H cx.txn.target em.accounts u1.vs_accounts /\ accounts_well_typed em.accounts /\
     !h. valid_horizon cx st0 h em.storage_trace ==>
       gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) m1 (OK u1,G1,tn1) /\
       expr_sim_full_post (DF,lo,d,ctx,func) cenv cx target_e
         (es,sa,a1,s0,target,G0,tn0) h (INL v : value + vyperState$exception)
         (em with gas_obs := []) G1 tn1 u1)` by
    (irule create_copy_list_cut >>
     qpat_assum `expr_sim_full_pre _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> goal_assum (drule_at Any) >> simp[APPEND_ASSOC])
  >- (disj1_tac >> goal_assum drule >> simp[]) >>
  rename1 `expr_sim_inv cenv cx env em1` >>
  `expr_body_pre cenv cx env value_e (em1 with gas_obs := [])` by
    (simp[] >> qpat_assum `!e em. _ /\ expr_sim_inv _ _ _ em ==> _` irule >> simp[]) >>
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (s0,G0,tn0) m1 (OK u1,Ga,tna)` >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type value_e) value_e (em1 with gas_obs := [])
     (st0,a1,a2,b1,b2,value,u1,Ga,tna)` by
    (irule create_copy_next_scalar_pre >>
     qpat_assum `expr_sim_full_pre _ _ _ _ target_e _ _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `bind (eval_exprs cx (target_e::_)) _ _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `bind (eval_exprs cx (value_e::_)) k1 _` >>
  `!vs. storage_trace_frame (k1 vs)` by simp[Abbr `k1`] >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   (?v2 em G2 tn2.
     bind (eval_exprs cx (case salt_e of NONE => [] | SOME e => [e]))
       (\vs. k1 (v2::vs))
       ((em with gas_obs := []) with gas_obs := gas_explicit (m3 ++ mr) u2.vs_gas_readings ++ tail) = (res,ee) /\
     expr_sim_inv cenv cx env em /\ valid_horizon cx st0 H em.storage_trace /\
     accounts_agree H cx.txn.target em.accounts u2.vs_accounts /\ accounts_well_typed em.accounts /\
     !h. valid_horizon cx st0 h em.storage_trace ==>
       gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (u1,Ga,tna) m2 (OK u2,G2,tn2) /\
       expr_sim_full_post (DF,lo,d,ctx,func) cenv cx value_e
         ((em1 with gas_obs := []),a1,a2,u1,value,Ga,tna) h (INL v2 : value + vyperState$exception)
         (em with gas_obs := []) G2 tn2 u2)` by
    (irule create_copy_list_cut >>
     qpat_assum `expr_sim_full_pre _ _ _ _ value_e _ _` (irule_at Any) >>
     simp[] >> goal_assum (drule_at Any) >> simp[APPEND_ASSOC])
  >- (disj1_tac >> goal_assum drule >> simp[]) >>
  rename1 `accounts_agree H cx.txn.target em2.accounts u2.vs_accounts` >>
  Cases_on `salt_e`
  >- (gvs[compile_create_salt_def,compileEnvTheory.comp_return_def] >>
      drule_all create_copy_empty_cut >> strip_tac >>
      disj2_tac >> qexists_tac `em2.accounts` >> simp[]) >>
  rename1 `compile_create_salt _ _ (SOME salt_e) a2 = _` >>
  Cases_on `lower_value compile_expr cenv (expr_type salt_e) salt_e a2` >>
  Cases_on `lower_value compile_expr cenv (expr_type salt_e) (gas_shadow_expr salt_e) b2` >>
  gvs[compile_create_salt_def,compileEnvTheory.comp_bind_def,compileEnvTheory.comp_return_def] >>
  `expr_body_pre cenv cx env salt_e (em2 with gas_obs := [])` by
    (simp[] >> qpat_assum `!e em. _ /\ expr_sim_inv _ _ _ em ==> _` irule >> simp[]) >>
  rename1 `lower_value compile_expr cenv (expr_type salt_e) salt_e a2 = (salt_op,a3)` >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type salt_e) salt_e (em2 with gas_obs := [])
     (st0,a2,a3,b2,b3,salt_op,u2,G2,tn2)` by
    (irule create_copy_next_scalar_pre >>
     qpat_assum `expr_sim_full_pre _ _ _ _ value_e _ _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `bind (eval_exprs cx (value_e::_)) _ _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `bind (eval_exprs cx [salt_e]) k2 _` >>
  `!vs. storage_trace_frame (k2 vs)` by simp[Abbr `k2`] >>
  irule create_copy_last_accounts >>
  qpat_assum `expr_sim_full_pre _ _ _ _ salt_e _ _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem create_size_cut_segment[local]:
  cs_extends sa a /\ create_cut_code {} a m /\ create_cut_code {} m sc /\
  cs_extends sc sb /\ fn_has_code sa sb func /\
  LIST_REL create_cut_first (m::cuts) (cuts ++ [sc]) /\
  lookup_block sc.cs_current_bb func.fn_blocks = SOME db /\
  get_instruction db (LENGTH sc.cs_current_insts) = SOME dispatch /\
  dispatch.inst_id = sc.cs_next_id /\ MEM dispatch.inst_opcode [CREATE;CREATE2] /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  create_expr_prefix sa sb explicit ctx func u marks s ==>
  ?v left right.
    v.vs_current_bb = m.cs_current_bb /\ v.vs_inst_idx = LENGTH m.cs_current_insts /\
    create_expr_prefix a m explicit ctx func u left v /\
    create_expr_prefix sa sb explicit ctx func v right s /\ marks = left ++ right
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends a m /\ cs_extends m sc /\ m.cs_next_id <= sc.cs_next_id` by
    fs[create_cut_code_def] >>
  `cs_extends m sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code a m func` by metis_tac[fn_has_code_mid] >>
  `fn_has_code m sb func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all create_cut_region_rules >> strip_tac >>
  `!bb. lookup_block m.cs_current_bb func.fn_blocks = SOME bb ==>
       phi_prefix_length bb.bb_instructions <= LENGTH m.cs_current_insts` by
    (rpt strip_tac >> drule_all create_pre_dispatch_phi_bound >> simp[]) >>
  irule create_size_prefix_first_cut >> reverse conj_tac >- simp[] >>
  qexists_tac `create_cut_region a m` >>
  `create_cut_region a m u` by metis_tac[] >>
  simp[] >> reverse conj_tac
  >- (CCONTR_TAC >> gvs[] >>
      `dispatch.inst_id IN frag_ids a m` by metis_tac[] >>
      fs[frag_ids_def]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  fs[create_prefix_step_def] >> metis_tac[]
QED

Theorem create_size_cut_code_chain[local]:
  !cuts a. LIST_REL (create_cut_code {}) (FRONT (a::cuts)) cuts ==>
    create_cut_code {} a (LAST (a::cuts))
Proof
  Induct >- simp[] >>
  simp[FRONT_CONS_NOT_NIL] >> metis_tac[create_cut_code_join]
QED

Theorem create_size_prefix_cut_walk[local]:
  !cuts a u marks.
    cs_extends sa a /\ LAST (a::cuts) = sc /\
    LIST_REL (create_cut_code {}) (FRONT (a::cuts)) cuts /\
    LIST_REL create_cut_first (FRONT (a::cuts)) cuts /\
    cs_extends sc sb /\ fn_has_code sa sb func /\
    lookup_block sc.cs_current_bb func.fn_blocks = SOME db /\
    get_instruction db (LENGTH sc.cs_current_insts) = SOME dispatch /\
    dispatch.inst_id = sc.cs_next_id /\ MEM dispatch.inst_opcode [CREATE;CREATE2] /\
    emit_op opc ops sc = (created,sd) /\ MEM opc [CREATE;CREATE2] /\
    compile_check_create_result created rof sd = (result,sb) /\
    body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
    u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
    create_expr_prefix sa sb explicit ctx func u marks s ==>
    ?states chunks.
      HD states = u /\ LAST states = s /\ LENGTH chunks = LENGTH cuts /\
      LIST_REL (\c v. v.vs_current_bb = c.cs_current_bb /\
                      v.vs_inst_idx = LENGTH c.cs_current_insts) (a::cuts) states /\
      (!i. i < LENGTH cuts ==>
        create_expr_prefix (EL i (a::cuts)) (EL i cuts) explicit ctx func
          (EL i states) (EL i chunks) (EL (SUC i) states)) /\
      marks = FLAT chunks
Proof
  Induct
  >- (pure_rewrite_tac[LAST_CONS, FRONT_CONS, LIST_REL_def] >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `a = sc` SUBST_ALL_TAC >>
      drule_all create_dispatch_no_return >> strip_tac >>
      qexistsl_tac [`[u]`,`[]`] >> gvs[]) >>
  pure_rewrite_tac[FRONT_CONS, LAST_CONS, LIST_REL_def] >>
  rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `create_cut_code {} a m` >>
  `create_cut_code {} m sc` by (drule create_size_cut_code_chain >> simp[]) >>
  `?inner. LIST_REL create_cut_first (m::inner) (inner ++ [sc])` by
    (Cases_on `cuts` >- (qexists_tac `[]` >> gvs[]) >>
     rename1 `LAST (m::n::ns) = sc` >>
     qexists_tac `FRONT (n::ns)` >>
     `FRONT (n::ns) ++ [sc] = n::ns` by
       metis_tac[LAST_CONS, APPEND_FRONT_LAST, NOT_CONS_NIL] >>
     fs[FRONT_CONS]) >>
  drule_all create_size_cut_segment >> strip_tac >>
  `cs_extends sa m` by metis_tac[create_cut_code_def, cs_extends_trans] >>
  first_x_assum (qspec_then `m` mp_tac) >>
  disch_then (qspecl_then [`v`,`right`] mp_tac) >>
  simp[] >>
  disch_then (qx_choosel_then [`rest_states`,`rest_chunks`]
    (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `rest_states`
  >- (qpat_x_assum `?v ys. [] = v::ys /\ _` mp_tac >> simp[]) >>
  rename1 `LAST (head::stk) = s` >>
  qexistsl_tac [`u::head::stk`,`left::rest_chunks`] >>
  fs[] >> gen_tac >> Cases_on `i` >> gvs[]
QED

Theorem create_size_itinerary_at_emit[local]:
  create_itinerary_code sa cuts sc /\
  emit_op opc ops sc = (created,sd) /\ MEM opc [CREATE;CREATE2] /\
  compile_check_create_result created rof sd = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  create_expr_prefix sa sb explicit ctx func s0 marks s /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
       MEM j.inst_opcode [CREATE;CREATE2] ==> j.inst_id <= inst.inst_id) ==>
  ?out states chunks.
    created = Var out /\ inst = mk_inst sc.cs_next_id opc ops [out] /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    LAST (sa::cuts) = sc /\
    HD states = s0 /\ LAST states = s /\ LENGTH chunks = LENGTH cuts /\
    LIST_REL (\c v. v.vs_current_bb = c.cs_current_bb /\
                    v.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
    (!i. i < LENGTH cuts ==>
      create_expr_prefix (EL i (sa::cuts)) (EL i cuts) explicit ctx func
        (EL i states) (EL i chunks) (EL (SUC i) states)) /\
    marks = FLAT chunks
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac create_itinerary_code_relations >>
  drule_all lookup_block_get_instruction_fn_insts >> strip_tac >>
  drule_all create_size_identify_emit >> strip_tac >>
  `s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts` by
    metis_tac[create_dispatch_pc_unique] >>
  `inst.inst_id = sc.cs_next_id` by simp[mk_inst_def] >>
  `cs_extends sc sb` by
    (irule cs_extends_trans >> qexists_tac `sd` >>
     metis_tac[ci_mono_def,ci_mono_emit_op,compile_check_create_result_labels,pairTheory.SND]) >>
  `cs_extends sa sa` by simp[cs_extends_refl] >>
  drule_all create_size_prefix_cut_walk >> strip_tac >>
  rpt (goal_assum (drule_at Any))
QED

(* The input gives the fetched outer CREATE; this theorem exposes the actual
   compiler run and decomposes the original execution, with its exact marks. *)

Theorem create_size_prefix_cuts_from_code:
  create_itinerary_suppliers /\ create_itinerary_rows_supplier /\
  compile_create_call compile_expr cenv ck salted rof args sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  create_expr_prefix sa sb explicit ctx func s0 marks s /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
       MEM j.inst_opcode [CREATE;CREATE2] ==> j.inst_id <= inst.inst_id) ==>
  ?cuts value salt bufop len sc sd created out states chunks.
    create_call_itinerary cenv ck salted args sa cuts value salt bufop len /\
    create_size_dispatch_tail rof sc sd created bufop len value salt result sb /\
    created = Var out /\
    inst = (case salt of
             NONE => mk_inst sc.cs_next_id CREATE [value;bufop;len] [out]
           | SOME x => mk_inst sc.cs_next_id CREATE2 [value;bufop;len;x] [out]) /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    LAST (sa::cuts) = sc /\
    HD states = s0 /\ LAST states = s /\ LENGTH chunks = LENGTH cuts /\
    LIST_REL (\c v. v.vs_current_bb = c.cs_current_bb /\
                    v.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
    (!i. i < LENGTH cuts ==>
      create_expr_prefix (EL i (sa::cuts)) (EL i cuts) explicit ctx func
        (EL i states) (EL i chunks) (EL (SUC i) states)) /\
    marks = FLAT chunks /\ create_itinerary_code sa cuts sc
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_call_itinerary_run >> strip_tac
  >- (drule_all lookup_block_get_instruction_fn_insts >> strip_tac >>
      drule added_insts_emit_inst >> strip_tac >>
      `~MEM inst.inst_opcode [CREATE;CREATE2]` suffices_by simp[] >>
      irule (BETA_RULE (Q.INST [`P` |-> `\i. ~MEM i.inst_opcode [CREATE;CREATE2]`]
         added_insts_function_property)) >>
      qexistsl_tac [`func`,`sa`,`sb`] >> fs[mk_inst_def,ci_mono_def,frag_ids_def]) >>
  Cases_on `salt` >>
  qpat_assum `create_size_dispatch_tail _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss
      [create_size_dispatch_tail_def, optionTheory.option_case_def]) >>
  `MEM CREATE [CREATE;CREATE2] /\ MEM CREATE2 [CREATE;CREATE2]` by simp[] >>
  drule_all create_size_itinerary_at_emit >> strip_tac >>
  rename1 `marks = FLAT all_chunks` >>
  qexistsl_tac [`cuts`,`value`] >>
  (FIRST [rename1 `create_call_itinerary _ _ _ _ _ _ _ (SOME salt_op) _ _` >>
          qexists_tac `SOME salt_op`, qexists_tac `NONE`]) >>
  qexistsl_tac [`bufop`,`len`,`sc`,`sd`,`created`,`out`,`states`,`all_chunks`] >>
  asm_rewrite_tac[optionTheory.option_case_def] >> simp[]
QED

Theorem blueprint_prefix_gas_path[local]:
  !x y. RTC (create_marked_edge (create_prefix_step ca cb explicit ctx fnc)) x y ==>
    !u. x = (u,[]) /\ ~u.vs_halted ==>
    gas_path ctx fnc u (LENGTH (SND y)) (OK (FST y))
Proof
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> simp[] >> conj_tac
  >- simp[gas_path_rules] >>
  simp[FORALL_PROD, create_marked_edge_def, create_prefix_step_def] >>
  rpt strip_tac >> gvs[] >>
  drule gas_origin_edge_erase >> strip_tac >>
  rename1 `gas_path_edge ctx fnc mid (LENGTH ms) (OK t)` >>
  `gas_path ctx fnc t 0 (OK t)` by metis_tac[gas_path_edge_normal, cj 1 gas_path_rules] >>
  `gas_path ctx fnc mid (LENGTH ms) (OK t)` by
    metis_tac[cj 2 gas_path_rules, ADD_0] >>
  once_rewrite_tac[ADD_COMM] >> metis_tac[gas_path_then]
QED

Theorem blueprint_read_at_cut[local]:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\ create_operand_completed_ok cx e /\
  lower_value compile_expr ce (expr_type e) e ca = (op,cb) /\
  lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) sca = (op,scb) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cb,sca,scb) /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  create_expr_prefix ca cb (gas_explicit_sites ctx shctx) ctx fnc u chunk t /\
  t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts /\
  (!v. storage_trace_frame (k v)) /\
  bind (bind (eval_expr cx e) (read_result cx)) k p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v q G' tn'.
    bind (eval_expr cx e) (read_result cx) p = (INL v,q) /\ k v q = (res,out) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    valid_horizon cx st0 H q.storage_trace /\
    expr_sim_inv ce cx env q /\ value_runtime_typed env (expr_type e) v /\
    expr_val_rel cx (post_value_type ce e) v op t /\
    ca.cs_next_var <= cb.cs_next_var /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
    return_buf_frame d ce cb t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_no_wrap i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q G' tn' t) /\ ~t.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
     tops cx st0 ca cb (bind (eval_expr cx e) (read_result cx)) (p,u,G,tn)
     (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx e (p,ca,cb,u,op,G,tn))` by
    (irule create_size_replay_value_cut >> simp[] >>
     conj_tac >- (qexists_tac `env` >> simp[]) >>
     qexistsl [`shfnc`, `sca`, `scb`, `expr_type e`] >>
     fs[expr_sim_full_pre_def, expr_sim_full_code_def] >>
     conj_tac >- (drule expr_body_pre_gas_admissible >> simp[]) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!f i z. frag_reachable _ _ _ f i z ==> _` drule >> simp[]) >>
  `gas_path ctx fnc u (LENGTH chunk) (OK t)` by
    (qpat_assum `create_expr_prefix ca cb _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE[create_expr_prefix_marked]) >>
     disch_then (mp_tac o MATCH_MP blueprint_prefix_gas_path) >> simp[]) >>
  `p.gas_obs = gas_explicit chunk u.vs_gas_readings ++
               (gas_explicit rest t.vs_gas_readings ++ tail)` by
    (drule gas_explicit_append_path >> simp[APPEND_ASSOC]) >>
  Cases_on `bind (eval_expr cx e) (read_result cx) p` >>
  qmatch_asmsub_rename_tac `bind (eval_expr cx e) (read_result cx) p = (rr,mid)` >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (Cases_on `rr` >> fs[bind_def] >> metis_tac[vyperStorageFootprintTheory.valid_horizon_frame]) >>
  `p with gas_obs := gas_explicit chunk u.vs_gas_readings ++
                       (gas_explicit rest t.vs_gas_readings ++ tail) = p`
    by (qpat_assum `p.gas_obs = gas_explicit chunk _ ++ _`
          (once_rewrite_tac o single o SYM) >> simp[]) >>
  qhdtm_x_assum `gas_completed_operand` mp_tac >>
  simp[gas_completed_operand_def] >>
  disch_then (qspecl_then [`H`,`chunk`,`t`,
    `gas_explicit rest t.vs_gas_readings ++ tail`,`rr`,`mid`] mp_tac) >>
  simp[] >> strip_tac
  >- (disj2_tac >>
      `?v. rr = INL v` by
        (qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (qspec_then `H` mp_tac) >>
         (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
         rewrite_tac[expr_sim_full_post_def] >> simp[] >> strip_tac >> metis_tac[]) >>
      gvs[] >> rename1 `_ = (INL v,mid)` >>
      `k v mid = (res,out)` by fs[bind_def] >>
      drule_all (REWRITE_RULE[ETA_AX] bodySimStmtFactsTheory.expr_body_pre_eval) >>
      simp[] >> strip_tac >>
      qexistsl [`G'`, `tn'`] >> simp[] >>
      `ci_mono ca cb` by
        (qspecl_then [`ce`, `expr_type e`, `e`, `ca`] mp_tac
           ci_mono_lower_value_compile_expr >> simp[]) >>
      `ca.cs_next_var <= cb.cs_next_var` by fs[ci_mono_def] >>
      `!h. valid_horizon cx st0 h mid.storage_trace ==>
        gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
          (u,G,tn) chunk (OK t,G',tn') /\
        expr_post h ctx fnc ce cx e p ca cb u (mid with gas_obs := []) v op t /\
        expr_sim_full_endpoint fnc cb u t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        ghost_inv_at (DF h) lo d ce cx (mid with gas_obs := []) G' tn' t` by
        (qx_gen_tac `h` >> disch_tac >>
         qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (qspec_then `h` mp_tac) >> (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
         disch_then (CONJUNCTS_THEN2 assume_tac
           (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def])) >> simp[]) >>
      qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `H` mp_tac) >> (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
      disch_then (strip_assume_tac o SIMP_RULE (srw_ss())
        [expr_post_def, expr_sim_full_endpoint_def]) >>
      `return_buf_frame d ce cb t` by
        (irule return_buf_frame_frame >> qexistsl [`ce`,`u`,`ca`] >> simp[]) >>
      `MEM fnc ctx.ctx_functions` by fs[expr_sim_full_code_def] >>
      `!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
        by metis_tac[body_inv_no_phi] >>
      `!f i z. frag_reachable ctx fnc t f i z ==> dalloca_no_wrap i z` by
        (drule gas_origin_ptr_path_dalloca_no_wrap >> simp[] >> metis_tac[]) >>
      simp[] >> (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >> conj_tac
      >- (qx_gen_tac `h` >> disch_tac >>
          qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
            (qspec_then `h` mp_tac) >> (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
          disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_post_def]) >>
          conj_tac >- FIRST_ASSUM ACCEPT_TAC >> conj_tac
          >- (irule (iffLR storage_well_formed_on_backends) >>
              qexists_tac `mid with gas_obs := []` >> simp[]) >>
          qpat_assum `ghost_inv_at (DF h) _ _ _ _ _ _ _ _`
            (strip_assume_tac o SIMP_RULE (srw_ss()) [ghost_inv_at_def]) >>
          simp[ghost_inv_at_def] >> FIRST_ASSUM ACCEPT_TAC) >>
      drule gas_path_normal >> simp[]) >>
  fs[bind_def] >> metis_tac[]
QED

Theorem blueprint_keyword_body_pre[local]:
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) before /\
  MEM e args /\ expr_sim_inv ce cx env p ==>
  expr_body_pre ce cx env e p
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  fs[expr_body_pre_split_def, expr_body_pre_mods_def,
     expr_sim_inv_split_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def,
     supported_expr_exists_def, supported_exprs_exists_every,
     expr_has_evm_run_thm, EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
    alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem, int_calls_exprs_every_mem]
QED

Theorem blueprint_read_list_frame[local]:
  (!xs. storage_trace_frame (k xs)) ==>
  !v. storage_trace_frame (bind (eval_exprs cx es) (\vs. k (v::vs)))
Proof
  simp[evaluate_storage_trace_frame, storage_trace_frame_bind_all]
QED

Theorem blueprint_keyword_uint[local]:
  value_runtime_typed env (BaseT (UintT 256)) v ==>
  ?i. v = IntV i /\ dest_NumV v = SOME (w2n (i2w i : bytes32))
Proof
  Cases_on `v` >> simp[value_runtime_typed_def, evaluate_type_def, value_has_type_def,
                       dimword_def] >> rpt strip_tac >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  simp[dest_NumV_def, i2w_def, w2n_n2w, dimword_def]
QED

Theorem blueprint_keyword_uint_word[local]:
  value_runtime_typed env (BaseT (UintT 256)) v /\
  expr_val_rel cx (BaseT (UintT 256)) v op t ==>
  ?w. dest_NumV v = SOME (w2n w) /\ eval_operand op t = SOME w
Proof
  strip_tac >> drule blueprint_keyword_uint >> strip_tac >>
  gvs[expr_val_rel_def, evaluate_type_def, is_word_type_def,
      typed_val_to_w256_def, val_to_w256_def]
QED

Theorem blueprint_keyword_salt[local]:
  value_runtime_typed env (BaseT (BytesT (Fixed 32))) v ==>
  ?w. dest_create_salt v = SOME w
Proof
  Cases_on `v` >> simp[value_runtime_typed_def, evaluate_type_def, value_has_type_def,
                        dest_create_salt_def, dest_BytesV_def]
QED

Theorem blueprint_lookup_code[local]:
  stmt_state_rel H ctx fnc ce cx st t ==>
  (lookup_account addr st.accounts).code = (lookup_account addr t.vs_accounts).code
Proof
  simp[stmt_state_rel_def] >> strip_tac >> drule state_rel_accounts >>
  strip_tac >> drule accounts_agree_lookup >> simp[]
QED

Theorem blueprint_offset_at_cut[local]:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  create_operand_completed_ok cx off /\
  expr_sim_inv ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  ((?oty i. origin_fold_value off = Literal oty (IntL i) /\
     op = Lit (i2w i) /\ cb = ca /\ scb = sca /\ t = u /\ chunk = []) \/
   (lower_value compile_expr ce (expr_type off) off ca = (op,cb) /\
    lower_value compile_expr ce (expr_type off) (gas_shadow_expr off) sca = (op,scb) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cb,sca,scb) /\
    create_expr_prefix ca cb (gas_explicit_sites ctx shctx) ctx fnc u chunk t /\
    t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts)) /\
  (!v. storage_trace_frame (k v)) /\
  bind (bind (eval_expr cx off) (read_result cx)) k p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v q w.
    bind (eval_expr cx off) (read_result cx) p = (INL v,q) /\ k v q = (res,out) /\
    dest_NumV v = SOME (w2n w) /\ eval_operand op t = SOME w /\
    stmt_state_rel H ctx fnc ce cx q t /\
    (!x. op = Var x ==> not_fresh_at cb x) /\
    (!x k. not_fresh_at ca x /\ lookup_var x u = SOME k ==> lookup_var x t = SOME k)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type off = BaseT (UintT 256)` by
    (drule expr_body_pre_static_facts >> strip_tac >>
     Cases_on `hs` >> gvs[well_typed_expr_def, create_arg_types_ok_def]) >>
  qpat_x_assum `(?oty i. _) \/ _` strip_assume_tac
  >- (drule_all create_blueprint_offset_bridge >> strip_tac >>
      gvs[eval_operand_def] >>
      disj2_tac >> `k (IntV i) p = (res,out)` by
        (qpat_assum `!st. bind _ _ st = (INL _,st)` (qspec_then `p` assume_tac) >>
         fs[bind_def]) >>
      `valid_horizon cx st0 H p.storage_trace` by metis_tac[vyperStorageFootprintTheory.valid_horizon_frame] >>
      metis_tac[]) >>
  `expr_body_pre ce cx env off p` by
    (irule blueprint_keyword_body_pre >> simp[] >>
     goal_assum (drule_at Any) >> Cases_on `hs` >> simp[]) >>
  drule_all blueprint_read_at_cut >> strip_tac >- metis_tac[] >>
  disj2_tac >> qexistsl [`v`,`q`] >> simp[] >>
  `is_word_type (expr_type off)` by simp[is_word_type_def] >>
  `?w. dest_NumV v = SOME (w2n w) /\ eval_operand op t = SOME w` by
    (irule blueprint_keyword_uint_word >> gvs[post_value_type_word] >>
     metis_tac[]) >>
  `!x. op = Var x ==> not_fresh_at cb x` by
    (qpat_assum `lower_value compile_expr ce _ off ca = _`
       (mp_tac o MATCH_MP (SRULE[GSYM AND_IMP_INTRO] exprOperandVarTheory.compile_lower_value_var)) >>
     simp[]) >>
  qexists_tac `w` >> simp[] >> metis_tac[]
QED

Theorem blueprint_keyword_mono[local]:
  local_ptrs_reserved ce ca /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  ca.cs_next_var <= cb.cs_next_var ==>
  local_ptrs_reserved ce cb /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x)
Proof
  metis_tac[local_ptrs_reserved_next_var, freshWritesTheory.not_fresh_at_mono]
QED

Theorem blueprint_eval_nil_action[local]:
  eval_exprs cx [] = return []
Proof
  simp[FUN_EQ_THM, eval_exprs_nil, return_def]
QED

Theorem blueprint_bind_success[local]:
  f p = (INL v,q) ==> bind f k p = k v q
Proof
  simp[bind_def]
QED

Theorem blueprint_eval_join_cons[local]:
  bind (eval_expr cx e) (read_result cx) p = (INL v,q) /\
  eval_exprs cx es q = (INL vs,r) ==>
  eval_exprs cx (e::es) p = (INL (v::vs),r)
Proof
  strip_tac >> simp[eval_exprs_cons_action, GSYM bind_assoc, return_def] >>
  qpat_assum `bind _ _ p = (INL _,_)`
    (pure_once_rewrite_tac o single o MATCH_MP blueprint_bind_success) >>
  simp[bind_def, return_def]
QED

Theorem blueprint_optional_salt_at_cut[local]:
  (hs ==> expr_body_pre ce cx env salt p /\ create_operand_completed_ok cx salt /\
      expr_type salt = BaseT (BytesT (Fixed 32))) /\
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_sim_inv ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  (if hs then
      lower_value compile_expr ce (expr_type salt) salt ca = (op,cb) /\
      lower_value compile_expr ce (expr_type salt) (gas_shadow_expr salt) sca = (op,scb) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cb,sca,scb) /\
      create_expr_prefix ca cb (gas_explicit_sites ctx shctx) ctx fnc u chunk t /\
      t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts
   else cb = ca /\ scb = sca /\ t = u /\ chunk = []) /\
  (!vs. storage_trace_frame (k vs)) /\
  bind (eval_exprs cx (if hs then [salt] else [])) k p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?svs q G' tn'.
    eval_exprs cx (if hs then [salt] else []) p = (INL svs,q) /\ k svs q = (res,out) /\
    (if hs then ?sv w. svs = [sv] /\ dest_create_salt sv = SOME w else svs = []) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    expr_sim_inv ce cx env q /\ ca.cs_next_var <= cb.cs_next_var /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
    return_buf_frame d ce cb t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_no_wrap i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q G' tn' t) /\ ~t.vs_halted
Proof
  reverse (Cases_on `hs`) >> simp[blueprint_eval_nil_action, return_def, bind_return] >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (disj2_tac >> qexistsl [`G`, `tn`] >> simp[] >> FIRST_ASSUM ACCEPT_TAC) >>
  `bind (bind (eval_expr cx salt) (read_result cx)) (\v. k [v]) p = (res,out)` by
    fs[create_copy_source_cons, blueprint_eval_nil_action, bind_return] >>
  `!v. storage_trace_frame ((\v. k [v]) v)` by simp[] >>
  drule_all blueprint_read_at_cut >> strip_tac >- metis_tac[] >>
  `?w. dest_create_salt v = SOME w` by
    (irule blueprint_keyword_salt >> metis_tac[]) >>
  `eval_exprs cx [salt] p = (INL [v],q)` by
    (irule blueprint_eval_join_cons >> metis_tac[eval_exprs_nil]) >>
  disj2_tac >> qexistsl [`[v]`,`q`,`G'`,`tn'`] >> fs[] >> FIRST_ASSUM ACCEPT_TAC
QED

Theorem blueprint_eval_salt_offset[local]:
  bind (eval_exprs cx ((if hs then [salt] else []) ++ [off])) k =
  bind (eval_exprs cx (if hs then [salt] else []))
    (\svs. bind (eval_exprs cx [off]) (\ovs. k (svs ++ ovs)))
Proof
  Cases_on `hs` >> simp[create_copy_source_cons, blueprint_eval_nil_action, bind_return, ETA_AX]
QED

Theorem blueprint_eval_join_salt_offset[local]:
  eval_exprs cx (if hs then [salt] else []) pa = (INL salts,ps) /\
  eval_exprs cx [off] ps = (INL [ov],qp) ==>
  eval_exprs cx ((if hs then [salt] else []) ++ [off]) pa = (INL (salts ++ [ov]),qp)
Proof
  strip_tac >>
  qabbrev_tac `act = eval_exprs cx ((if hs then [salt] else []) ++ [off])` >>
  `bind act return = act` by
    (simp[FUN_EQ_THM, bind_def, return_def] >> qx_gen_tac `s` >>
     Cases_on `act s` >> rename1 `act s = (rr,s')` >> Cases_on `rr` >> simp[]) >>
  `bind (eval_exprs cx ((if hs then [salt] else []) ++ [off])) return pa =
      (INL (salts ++ [ov]),qp)` by
    (pure_once_rewrite_tac[blueprint_eval_salt_offset] >> simp[bind_def, return_def]) >>
  qpat_x_assum `bind (eval_exprs cx _) return pa = _` mp_tac >>
  simp[Abbr `act`]
QED

Theorem blueprint_decoded_keywords[local]:
  dest_AddressV av = SOME addr /\ dest_NumV amount = SOME value /\
  dest_NumV ov = SOME n /\
  (if hs then ?sv w. svs = [sv] /\ dest_create_salt sv = SOME w else svs = []) ==>
  ?ops. dest_create_args (CreateFromBlueprint raw) hs
      (create_operand_layout (CreateFromBlueprint raw) hs (av::(cvs ++ amount::(svs ++ [ov])))) = SOME ops /\
    ops.co_code_src = AddressCodeSource addr /\ ops.co_ctor_args = cvs /\
    ops.co_code_offset = SOME n
Proof
  Cases_on `hs` >> simp[] >> strip_tac >>
  gvs[create_operand_layout_def, dest_create_args_def, make_create_operands_def,
      dest_optional_num_def, dest_optional_salt_def, LENGTH_APPEND,
      DROP_PREFIX, TAKE_APPEND1]
QED

Theorem blueprint_prefix_labels[local]:
  create_expr_prefix ca cb explicit ctx fnc u marks t /\ ~u.vs_halted ==>
  t.vs_labels = u.vs_labels
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  drule blueprint_prefix_gas_path >> simp[] >> metis_tac[gas_path_labels]
QED

Theorem blueprint_eval_operand_frame[local]:
  eval_operand op u = SOME aw /\ (!x. op = Var x ==> not_fresh_at ca x) /\
  (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
  t.vs_labels = u.vs_labels ==> eval_operand op t = SOME aw
Proof
  Cases_on `op` >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem create_blueprint_keywords_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  EVERY (create_operand_completed_ok cx) (create_operand_order (CreateFromBlueprint raw) hs args) /\
  LENGTH cvs = LENGTH ctors /\ dest_AddressV av = SOME (w2w aw) /\
  eval_operand target_op u = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at ca x) /\
  expr_sim_inv ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  lower_value compile_expr ce (expr_type amount) amount ca = (amount_op,cm) /\
  lower_value compile_expr ce (expr_type amount) (gas_shadow_expr amount) sca = (amount_op,scm) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cm,sca,scm) /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc u ma m /\
  m.vs_current_bb = cm.cs_current_bb /\ m.vs_inst_idx = LENGTH cm.cs_current_insts /\
  (if hs then
      lower_value compile_expr ce (expr_type salt) salt cm = (salt_op,cn) /\
      lower_value compile_expr ce (expr_type salt) (gas_shadow_expr salt) scm = (salt_op,scn) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (cm,cn,scm,scn) /\
      create_expr_prefix cm cn (gas_explicit_sites ctx shctx) ctx fnc m ms n /\
      n.vs_current_bb = cn.cs_current_bb /\ n.vs_inst_idx = LENGTH cn.cs_current_insts
   else cn = cm /\ scn = scm /\ n = m /\ ms = []) /\
  ((?oty i. origin_fold_value off = Literal oty (IntL i) /\
     offset_op = Lit (i2w i) /\ cb = cn /\ scb = scn /\ t = n /\ mo = []) \/
   (lower_value compile_expr ce (expr_type off) off cn = (offset_op,cb) /\
    lower_value compile_expr ce (expr_type off) (gas_shadow_expr off) scn = (offset_op,scb) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (cn,cb,scn,scb) /\
    create_expr_prefix cn cb (gas_explicit_sites ctx shctx) ctx fnc n mo t /\
    t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts)) /\
  bind (eval_exprs cx (amount::((if hs then [salt] else []) ++ [off])))
    (\kvs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (ma ++ (ms ++ (mo ++ rest))) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?kvs q ops ow.
    eval_exprs cx (amount::((if hs then [salt] else []) ++ [off])) p = (INL kvs,q) /\
    eval_create_operands cx (CreateFromBlueprint raw) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs)) q = (res,out) /\
    dest_create_args (CreateFromBlueprint raw) hs
      (create_operand_layout (CreateFromBlueprint raw) hs (av::(cvs ++ kvs))) = SOME ops /\
    ops.co_code_src = AddressCodeSource (w2w aw) /\ ops.co_ctor_args = cvs /\
    ops.co_code_offset = SOME (w2n ow) /\
    eval_operand target_op t = SOME aw /\ eval_operand offset_op t = SOME ow /\
    (!x. offset_op = Var x ==> not_fresh_at cb x) /\
    (lookup_account (w2w aw) q.accounts).code = (lookup_account (w2w aw) t.vs_accounts).code /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `kfinal = \kvs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))` >>
  `!kvs. storage_trace_frame (kfinal kvs)` by simp[Abbr `kfinal`, storage_trace_frame_create_operands] >>
  `create_operand_completed_ok cx amount /\ (hs ==> create_operand_completed_ok cx salt) /\
     create_operand_completed_ok cx off` by
    (qpat_assum `args = _` (fn th => qhdtm_assum `EVERY` (mp_tac o REWRITE_RULE[th])) >>
     Cases_on `hs` >> simp[create_operand_order_def, EVERY_APPEND]) >>
  `expr_type amount = BaseT (UintT 256) /\ (hs ==> expr_type salt = BaseT (BytesT (Fixed 32)))` by
    (drule expr_body_pre_static_facts >> strip_tac >>
     Cases_on `hs` >> gvs[well_typed_expr_def, create_arg_types_ok_def]) >>
  `expr_body_pre ce cx env amount p` by
    (irule blueprint_keyword_body_pre >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  qabbrev_tac `ka = \v. bind (eval_exprs cx ((if hs then [salt] else []) ++ [off])) (\vs. kfinal (v::vs))` >>
  `bind (bind (eval_expr cx amount) (read_result cx)) ka p = (res,out)` by fs[Abbr `ka`,create_copy_source_cons] >>
  `!v. storage_trace_frame (ka v)` by simp[Abbr `ka`, blueprint_read_list_frame] >>
  drule_all blueprint_read_at_cut >> strip_tac >- metis_tac[] >>
  rename1 `bind (eval_expr cx amount) (read_result cx) p = (INL avalue,pa)` >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  `hs ==> expr_body_pre ce cx env salt pa /\ create_operand_completed_ok cx salt /\
      expr_type salt = BaseT (BytesT (Fixed 32))` by
    (strip_tac >> simp[] >> irule blueprint_keyword_body_pre >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qabbrev_tac `ksalt = \svs. bind (eval_exprs cx [off]) (\ovs. kfinal (avalue::(svs ++ ovs)))` >>
  `bind (eval_exprs cx (if hs then [salt] else [])) ksalt pa = (res,out)` by
    fs[Abbr `ka`, Abbr `ksalt`, blueprint_eval_salt_offset] >>
  `!svs. storage_trace_frame (ksalt svs)` by
    simp[Abbr `ksalt`, evaluate_storage_trace_frame, storage_trace_frame_bind_all] >>
  drule_all blueprint_optional_salt_at_cut >> strip_tac >- metis_tac[] >>
  rename1 `eval_exprs cx (if hs then [salt] else []) pa = (INL salts,ps)` >>
  `ca.cs_next_var <= cn.cs_next_var` by decide_tac >>
  drule_all (Q.INST [`cb` |-> `cn`] blueprint_keyword_mono) >> strip_tac >>
  `n.vs_current_bb = cn.cs_current_bb /\ n.vs_inst_idx = LENGTH cn.cs_current_insts` by
    (qpat_assum `if hs then _ else _` mp_tac >> Cases_on `hs` >> simp[] >> metis_tac[]) >>
  qabbrev_tac `koff = \ov. kfinal (avalue::(salts ++ [ov]))` >>
  `bind (bind (eval_expr cx off) (read_result cx)) koff ps = (res,out)` by
    fs[Abbr `ksalt`, Abbr `koff`, create_copy_source_cons, blueprint_eval_nil_action, bind_return] >>
  `!ov. storage_trace_frame (koff ov)` by simp[Abbr `koff`] >>
  drule_all blueprint_offset_at_cut >> strip_tac >- metis_tac[] >>
  rename1 `bind (eval_expr cx off) (read_result cx) ps = (INL ov,qp)` >>
  `eval_exprs cx [off] ps = (INL [ov],qp)` by
    (irule blueprint_eval_join_cons >> metis_tac[eval_exprs_nil]) >>
  drule_all blueprint_eval_join_salt_offset >> strip_tac >>
  `?amt. dest_NumV avalue = SOME amt` by
    (qpat_assum `expr_type amount = _` (fn th =>
       qpat_assum `value_runtime_typed env (expr_type amount) avalue`
         (mp_tac o MATCH_MP blueprint_keyword_uint o REWRITE_RULE[th])) >> metis_tac[]) >>
  `?ops. dest_create_args (CreateFromBlueprint raw) hs
       (create_operand_layout (CreateFromBlueprint raw) hs (av::(cvs ++ avalue::(salts ++ [ov])))) = SOME ops /\
     ops.co_code_src = AddressCodeSource (w2w aw) /\ ops.co_ctor_args = cvs /\
     ops.co_code_offset = SOME (w2n w)` by
    (irule blueprint_decoded_keywords >> simp[] >> metis_tac[]) >>
  `!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at cm x /\ not_fresh_at cn x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     metis_tac[]) >>
  `m.vs_labels = u.vs_labels` by
    (qpat_assum `create_expr_prefix ca cm _ _ _ u ma m` (mp_tac o MATCH_MP (SRULE[GSYM AND_IMP_INTRO] blueprint_prefix_labels)) >> simp[]) >>
  `n.vs_labels = m.vs_labels` by
    (qpat_x_assum `if hs then lower_value _ _ _ salt cm = _ /\ _ else _` mp_tac >>
     reverse (Cases_on `hs`) >> pure_rewrite_tac[COND_CLAUSES]
     >- (strip_tac >> fs[]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `create_expr_prefix cm cn _ _ _ m ms n`
       (mp_tac o MATCH_MP (SRULE[GSYM AND_IMP_INTRO] blueprint_prefix_labels)) >> simp[]) >>
  `t.vs_labels = n.vs_labels` by
    (qpat_x_assum `(?oty i. origin_fold_value off = _ /\ _) \/ _` strip_assume_tac
     >- simp[] >>
     qpat_assum `create_expr_prefix cn cb _ _ _ n mo t`
       (mp_tac o MATCH_MP (SRULE[GSYM AND_IMP_INTRO] blueprint_prefix_labels)) >> simp[]) >>
  `eval_operand target_op t = SOME aw` by
    (irule blueprint_eval_operand_frame >> qexistsl [`ca`,`u`] >> simp[] >>
     FIRST_ASSUM ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`avalue::(salts ++ [ov])`, `qp`, `ops`, `w`] >> simp[] >>
  conj_tac >- (irule blueprint_eval_join_cons >> qexists_tac `pa` >> simp[]) >>
  drule blueprint_lookup_code >> simp[]
QED

Theorem create_size_prefix_cuts:
  compile_create_call compile_expr cenv ck salted rof args sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  create_expr_prefix sa sb explicit ctx func s0 marks s /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
       MEM j.inst_opcode [CREATE;CREATE2] ==> j.inst_id <= inst.inst_id) ==>
  ?cuts value salt bufop len sc sd created out states chunks.
    create_call_itinerary cenv ck salted args sa cuts value salt bufop len /\
    create_size_dispatch_tail rof sc sd created bufop len value salt result sb /\
    created = Var out /\
    inst = (case salt of
             NONE => mk_inst sc.cs_next_id CREATE [value;bufop;len] [out]
           | SOME x => mk_inst sc.cs_next_id CREATE2 [value;bufop;len;x] [out]) /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    LAST (sa::cuts) = sc /\
    HD states = s0 /\ LAST states = s /\ LENGTH chunks = LENGTH cuts /\
    LIST_REL (\c v. v.vs_current_bb = c.cs_current_bb /\
                    v.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
    (!i. i < LENGTH cuts ==>
      create_expr_prefix (EL i (sa::cuts)) (EL i cuts) explicit ctx func
        (EL i states) (EL i chunks) (EL (SUC i) states)) /\
    marks = FLAT chunks /\ create_itinerary_code sa cuts sc
Proof
  `create_itinerary_suppliers` by
    (simp[create_itinerary_suppliers_def, create_operand_cut_code,
          create_vv_snapshot_cut_code, create_unwrap_cut_code,
          create_encode_values_cut_code, cj 1 create_fixed_preparation_intervals,
          cj 4 create_fixed_preparation_intervals, cj 5 create_fixed_preparation_intervals] >>
     rpt gen_tac >> rewrite_tac[compile_alloc_buffer_def] >>
     irule create_cut_code_bind >>
     conj_tac >- (irule create_cut_code_emit_op >> simp[create_cut_targets_def]) >>
     simp[]) >>
  `create_itinerary_rows_supplier` by
    (rw[create_itinerary_rows_supplier_def, create_itinerary_ctor_rows_def] >>
     irule create_ctor_cut_spine >> first_assum ACCEPT_TAC) >>
  strip_tac >> irule create_size_prefix_cuts_from_code >> simp[] >>
  rpt (goal_assum (drule_at Any))
QED

Theorem create_prefix_readings[local]:
  create_expr_prefix sa sb explicit ctx func s ms t ==>
  t.vs_gas_readings = DROP (LENGTH ms) s.vs_gas_readings
Proof
  simp[create_expr_prefix_marked] >>
  `!x y. RTC (create_marked_edge (create_prefix_step sa sb explicit ctx func)) x y ==>
    ?n. LENGTH (SND y) = LENGTH (SND x) + n /\
        (FST y).vs_gas_readings = DROP n (FST x).vs_gas_readings`
    suffices_by (disch_then (qspecl_then [`(s,[])`,`(t,ms)`] mp_tac) >> simp[]) >>
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> simp[] >>
  map_every qx_gen_tac [`x`,`y`,`z`] >>
  map_every PairCases_on [`x`,`y`,`z`] >>
  simp[create_marked_edge_def, create_prefix_step_def, PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  drule gas_origin_edge_erase >> strip_tac >>
  drule gas_path_edge_suffix >> simp[gas_count_suffix_def] >> strip_tac >>
  qexists_tac `LENGTH ms + n` >> simp[DROP_DROP_T, AC ADD_ASSOC ADD_COMM]
QED

Theorem raw_decoded_keywords[local]:
  dest_NumV av = SOME amount /\
  (if hs then ?sv w. svs = [sv] /\ dest_create_salt sv = SOME w else svs = []) ==>
  ?ops. dest_create_args RawCreate hs
    (create_operand_layout RawCreate hs (BytesV code::(cvs ++ av::svs))) = SOME ops /\
    ops.co_code_src = BytecodeCodeSource code /\ ops.co_ctor_args = cvs
Proof
  Cases_on `hs` >> simp[] >> strip_tac >>
  gvs[create_operand_layout_def, dest_create_args_def, make_create_operands_def,
      dest_BytesV_def, dest_optional_num_def, dest_optional_salt_def,
      DROP_PREFIX, TAKE_APPEND1, FRONT_APPEND, LAST_APPEND_CONS]
QED

Theorem create_raw_keywords_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) args df) entry /\
  args = e::av::(xs ++ (if hs then [salt] else [])) /\
  EVERY (create_operand_completed_ok cx) (create_operand_order RawCreate hs args) /\
  LENGTH cvs = LENGTH xs /\ expr_sim_inv ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  lower_value compile_expr ce (expr_type av) av ca = (amount_op,cm) /\
  lower_value compile_expr ce (expr_type av) (gas_shadow_expr av) sca = (amount_op,scm) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cm,sca,scm) /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc u ma m /\
  m.vs_current_bb = cm.cs_current_bb /\ m.vs_inst_idx = LENGTH cm.cs_current_insts /\
  (if hs then
      lower_value compile_expr ce (expr_type salt) salt cm = (salt_op,cn) /\
      lower_value compile_expr ce (expr_type salt) (gas_shadow_expr salt) scm = (salt_op,scn) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (cm,cn,scm,scn) /\
      create_expr_prefix cm cn (gas_explicit_sites ctx shctx) ctx fnc m ms n /\
      n.vs_current_bb = cn.cs_current_bb /\ n.vs_inst_idx = LENGTH cn.cs_current_insts
   else cn = cm /\ scn = scm /\ n = m /\ ms = []) /\
  bind (eval_exprs cx (av::(if hs then [salt] else [])))
    (\kvs. eval_create_operands cx RawCreate hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args)
      (BytesV code::(cvs ++ kvs))) p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (ma ++ ms) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?vs ops q.
    eval_create_operands cx RawCreate hs rof (MAP expr_type args)
      (blueprint_literal_offset cx hs args) vs q = (res,out) /\
    dest_create_args RawCreate hs (create_operand_layout RawCreate hs vs) = SOME ops /\
    ops.co_code_src = BytecodeCodeSource code /\ ops.co_ctor_args = cvs /\
    create_arg_ctor_types RawCreate hs (MAP expr_type args) = SOME (MAP expr_type xs) /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x m = SOME w) /\
    ca.cs_next_var <= cm.cs_next_var /\
    (!x w. not_fresh_at cm x /\ lookup_var x m = SOME w ==> lookup_var x n = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `kfinal = \kvs. eval_create_operands cx RawCreate hs rof
    (MAP expr_type args) (blueprint_literal_offset cx hs args) (BytesV code::(cvs ++ kvs))` >>
  `!kvs. storage_trace_frame (kfinal kvs)` by simp[Abbr `kfinal`, storage_trace_frame_create_operands] >>
  `create_operand_completed_ok cx av /\ (hs ==> create_operand_completed_ok cx salt)` by
    (qpat_assum `args = _` (fn th => qhdtm_assum `EVERY` (mp_tac o REWRITE_RULE[th])) >>
     Cases_on `hs` >> simp[create_operand_order_def, EVERY_APPEND,
                          DROP_PREFIX, TAKE_APPEND1]) >>
  `expr_type av = BaseT (UintT 256) /\ (hs ==> expr_type salt = BaseT (BytesT (Fixed 32)))` by
    (drule expr_body_pre_static_facts >> strip_tac >>
     Cases_on `hs` >> gvs[well_typed_expr_def, create_arg_types_ok_def,
                          LAST_APPEND_CONS, FRONT_APPEND]) >>
  `expr_body_pre ce cx env av p` by
    (irule create_raw_arg_body_pre >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  qabbrev_tac `ka = \v. bind (eval_exprs cx (if hs then [salt] else [])) (\vs. kfinal (v::vs))` >>
  `bind (bind (eval_expr cx av) (read_result cx)) ka p = (res,out)` by
    fs[Abbr `ka`,create_copy_source_cons] >>
  `!v. storage_trace_frame (ka v)` by simp[Abbr `ka`, blueprint_read_list_frame] >>
  drule_all blueprint_read_at_cut >> strip_tac >- metis_tac[] >>
  rename1 `bind (eval_expr cx av) (read_result cx) p = (INL avalue,pa)` >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  `hs ==> expr_body_pre ce cx env salt pa /\ create_operand_completed_ok cx salt /\
      expr_type salt = BaseT (BytesT (Fixed 32))` by
    (strip_tac >> simp[] >> irule create_raw_arg_body_pre >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qabbrev_tac `ksalt = \svs. kfinal (avalue::svs)` >>
  `bind (eval_exprs cx (if hs then [salt] else [])) ksalt pa = (res,out)` by
    fs[Abbr `ka`, Abbr `ksalt`] >>
  `!svs. storage_trace_frame (ksalt svs)` by simp[Abbr `ksalt`] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`rest` |-> `[]`] blueprint_optional_salt_at_cut)) >>
  strip_tac >- metis_tac[] >>
  `?amt. dest_NumV avalue = SOME amt` by
    (qpat_assum `expr_type av = _` (fn th =>
       qpat_assum `value_runtime_typed env (expr_type av) avalue`
         (mp_tac o MATCH_MP blueprint_keyword_uint o REWRITE_RULE[th])) >> metis_tac[]) >>
  drule_all raw_decoded_keywords >> disch_then (qspecl_then [`cvs`,`code`] strip_assume_tac) >>
  disj2_tac >> qexistsl [`BytesV code::(cvs ++ avalue::svs)`,`ops`,`q`] >>
  Cases_on `hs` >> gvs[create_arg_ctor_types_def, FRONT_APPEND]
QED

Theorem create_raw_first_full_pre[local]:
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_a) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,a,shadow_sa,shadow_a) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty parent es (st0,sa,sb,shadow_sa,shadow_sb,parent_vv,s0,G0,tn0) ==>
  expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es (st0,sa,a,shadow_sa,shadow_a,vv,s0,G0,tn0)
Proof
  simp[expr_vv_sim_full_pre_def, expr_sim_full_code_def] >>
  metis_tac[expr_body_pre_vv_gas_admissible]
QED

Theorem create_raw_bytecode_replay:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es /\
  EVERY (create_operand_completed_ok cx) (create_operand_order RawCreate hs (e::v::rest)) /\
  expr_vv_sim_full_pre (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es
    (st0,sa,sb,shadow_sa,shadow_sb,parent_vv,s0,G0,tn0) /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_a) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,a,shadow_sa,shadow_a) /\
  create_expr_prefix sa a (gas_explicit_sites ctx shadow_ctx) ctx func s0 ms u /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_expr cx (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df)
    (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?p tv code G tn n.
    expr_type e = BaseT (BytesT (Dynamic n)) /\ LENGTH code <= n /\ n <= 49152 /\
    eval_expr cx e (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL tv,p) /\
    p.gas_obs = gas_explicit later u.vs_gas_readings ++ tail /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
    bind (eval_exprs cx (TAKE (LENGTH rest - (if hs then 1 else 0)) rest ++
                       v :: DROP (LENGTH rest - (if hs then 1 else 0)) rest))
      (\vs. eval_create_operands cx RawCreate hs rof (MAP expr_type (e::v::rest))
        (blueprint_literal_offset cx hs (e::v::rest)) (BytesV code::vs)) p = (res,ee) /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv ce cx env p /\
    !h. valid_horizon cx st0 h p.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) ms (OK u,G,tn) /\
      vv_post h ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) (p with gas_obs := []) tv vv u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF h) lo dep ce cx (p with gas_obs := []) G tn u /\
      ptr_vv_ok cx (post_value_type ce e) tv vv (p with gas_obs := []) G tn u /\
      (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
              eval_operand (vv_operand vv) u = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
                      val_in_memory rt (BytesV code) (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G u) /\
      (!t' ptr. vv = LocatedValue t' ptr /\ ptr.ptr_location = LocMemory ==>
               ptr_buf_ok ce e ptr.ptr_operand G u) /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre ce cx env e es` by
    (drule exprBodyPrePropsTheory.expr_body_pre_static_facts >> strip_tac >>
     `MEM e (e::v::rest)` by simp[] >> metis_tac[create_raw_arg_body_pre]) >>
  `create_operand_completed_ok cx e` by fs[create_operand_order_def] >>
  drule_all create_raw_first_full_pre >> strip_tac >>
  drule_all create_size_replay_vv_cut >> strip_tac >>
  qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _`
    (assume_tac o REWRITE_RULE[create_raw_call_split]) >>
  qmatch_asmsub_abbrev_tac `es with gas_obs := gs` >>
  `?head_res p. eval_expr cx e (es with gas_obs := gs) = (head_res,p)` by
    (Cases_on `eval_expr cx e (es with gas_obs := gs)` >> simp[]) >>
  `valid_horizon cx st0 H p.storage_trace` by metis_tac[create_raw_cont_horizon] >>
  `gs = gas_explicit ms s0.vs_gas_readings ++ (gas_explicit later u.vs_gas_readings ++ tail)` by
    (drule create_prefix_readings >> simp[Abbr `gs`, gas_explicit_append, APPEND_ASSOC]) >>
  qpat_x_assum `gas_completed_operand _ _ _ _ _ _ _ _ _`
    (qspecl_then [`H`,`ms`,`u`,`gas_explicit later u.vs_gas_readings ++ tail`,`head_res`,`p`] mp_tac
      o REWRITE_RULE[gas_completed_operand_def]) >>
  (impl_tac >- (qpat_assum `gs = gas_explicit _ _ ++ (_ ++ _)`
      (fn th => PURE_REWRITE_TAC[GSYM th]) >> simp[])) >>
  strip_tac
  >- (`well_typed_expr env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df)` by
        metis_tac[exprBodyPrePropsTheory.expr_body_pre_static_facts] >>
      drule create_raw_first_type >> strip_tac >>
      qpat_assum `!h. valid_horizon _ _ h _ ==> _`
        (mp_tac o BETA_RULE o Q.SPEC `H`) >>
      asm_rewrite_tac[] >> disch_then strip_assume_tac >>
      qpat_x_assum `head_res = INL _` SUBST_ALL_TAC >>
      drule_all create_raw_read_bytes >> strip_tac >>
      `expr_sim_inv ce cx env p` by
        (`expr_body_pre ce cx env e (es with gas_obs := gs)` by
          simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
         metis_tac[exprSimSourceTheory.expr_body_pre_eval_result]) >>
      disj2_tac >> qexistsl_tac [`p`,`tv`,`code`,`G`,`tn`,`n`] >>
      simp[] >> conj_tac
      >- (qpat_x_assum `bind (eval_expr _ _) _ _ = _` mp_tac >>
          simp[bind_def]) >>
      rpt strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >> gvs[]) >>
  disj1_tac >> qexists_tac `err` >>
  qpat_x_assum `bind (eval_expr _ _) _ _ = _` mp_tac >> simp[bind_def]
QED

(* A retained operand is replayed through its unwrap as one scalar read. *)
Theorem blueprint_raw_nonword_tag[local]:
  expr_body_pre ce cx env e p /\ expr_type e = BaseT (BytesT (Dynamic k)) /\
  compile_expr ce (expr_type e) e ca = (vv,cm) ==>
  ~is_word_type (vv_type vv)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule expr_body_pre_static_facts >> strip_tac >>
  drule expr_body_pre_lowered_fits >> strip_tac >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `~is_word_type (lowered_value_type ce e)` by
    (drule aggregateEvaluatedLayoutTheory.arg_type_fits_word_type >> simp[]) >>
  `reason_uniform_shape compile_expr ce (expr_type e) e` by
    (irule exprReasonOperandTheory.compile_expr_reason_uniform >>
     qexists_tac `env` >> fs[expr_sim_inv_def]) >>
  pop_assum (strip_assume_tac o REWRITE_RULE[exprReasonOperandTheory.reason_uniform_shape_def]) >>
  qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _`
    (drule_then assume_tac) >>
  Cases_on `vv` >> gvs[exprReasonOperandTheory.reason_result_shape_def,vv_type_def]
QED

Theorem blueprint_raw_empty_snapshot_prefix[local]:
  create_expr_prefix c c explicit ctx fn s ms t ==> t = s /\ ms = []
Proof
  simp[create_expr_prefix_marked] >> once_rewrite_tac[RTC_CASES1] >>
  simp[EXISTS_PROD,create_marked_edge_def,create_prefix_step_def,frag_ids_def]
QED

Theorem blueprint_raw_widen_prefix[local]:
  a.cs_next_id <= b.cs_next_id /\ c.cs_next_id <= d.cs_next_id /\
  lookup_block d.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH d.cs_current_insts) = SOME i /\
  i.inst_id = d.cs_next_id /\
  create_expr_prefix b c explicit ctx fn s ms t ==>
  create_expr_prefix a d explicit ctx fn s ms t
Proof
  rewrite_tac[create_expr_prefix_marked] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `RTC _ _ _` mp_tac >> match_mp_tac RTC_MONOTONE >>
  simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def,frag_ids_def] >>
  rpt strip_tac >> rpt (goal_assum (drule_at Any)) >> simp[] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem blueprint_raw_join_prefix[local]:
  a.cs_next_id <= b.cs_next_id /\ b.cs_next_id <= c.cs_next_id /\
  lookup_block c.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH c.cs_current_insts) = SOME i /\
  i.inst_id = c.cs_next_id /\
  create_expr_prefix a b explicit ctx fn s ms m /\
  create_expr_prefix b c explicit ctx fn m ns t ==>
  create_expr_prefix a c explicit ctx fn s (ms ++ ns) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `create_expr_prefix a c explicit ctx fn s ms m /\
   create_expr_prefix a c explicit ctx fn m ns t` by
    (conj_tac
     >- (irule blueprint_raw_widen_prefix >> conj_tac
         >- (qexistsl [`bb`,`i`] >> simp[]) >> qexistsl [`a`,`b`] >> simp[]) >>
     irule blueprint_raw_widen_prefix >> conj_tac
     >- (qexistsl [`bb`,`i`] >> simp[]) >> qexistsl [`b`,`c`] >> simp[]) >>
  qpat_x_assum `create_expr_prefix a c _ _ _ m ns t`
    (mp_tac o MATCH_MP create_marked_rtc_rebase o REWRITE_RULE[create_expr_prefix_marked]) >>
  disch_then (qspec_then `ms` mp_tac) >> simp[create_expr_prefix_marked] >>
  strip_tac >> irule RTC_TRANS >> qexists_tac `(m,ms)` >>
  fs[create_expr_prefix_marked]
QED

Theorem blueprint_raw_retained_at_cut:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\ create_operand_completed_ok cx e /\
  expr_type e = BaseT (BytesT (Dynamic k)) /\ ~exprs_can_mutate ce later /\
  eval_operand target_op s = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at ca x) /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca s /\ alloca_history fnc s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx fnc s f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p s /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) sca = (vv,scm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce (MAP gas_shadow_expr later)) vv scm = (ssaved,scs) /\
  unwrap_value ce ssaved scs = (raw_op,scu) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cu,sca,scu) /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\ fn_has_code cu cl fnc /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc s mc m /\
  create_expr_prefix cm cs (gas_explicit_sites ctx shctx) ctx fnc m ms v /\
  create_expr_prefix cs cu (gas_explicit_sites ctx shctx) ctx fnc v mu u /\
  u.vs_current_bb = cu.cs_current_bb /\ u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  (!v. storage_trace_frame (kont v)) /\
  bind (bind (eval_expr cx e) (read_result cx)) kont p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (mc ++ (ms ++ (mu ++ rest))) s.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?bs q G' tn'.
    bind (eval_expr cx e) (read_result cx) p = (INL (BytesV bs),q) /\
    kont (BytesV bs) q = (res,out) /\ valid_horizon cx st0 H q.storage_trace /\
    q.gas_obs = gas_explicit rest u.vs_gas_readings ++ tail /\
    expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bs) raw_op u /\
    eval_operand target_op u = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at cu x) /\
    expr_sim_inv ce cx env q /\ local_ptrs_reserved ce cu /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
    return_buf_frame d ce cu u /\ alloca_history fnc u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_no_wrap i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q u /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q G' tn' u) /\
    ~u.vs_halted /\ u.vs_current_bb = cu.cs_current_bb /\
    u.vs_inst_idx = LENGTH cu.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all blueprint_raw_nonword_tag >> strip_tac >>
  gvs[gasShadowCompileHelpersTheory.gas_shadow_expr_can_mutate,
      compile_snapshot_vv_def,comp_return_def] >>
  qpat_x_assum `create_expr_prefix cm cm _ _ _ m ms v`
    (strip_assume_tac o MATCH_MP blueprint_raw_empty_snapshot_prefix) >>
  gvs[] >>
  `lower_value compile_expr ce (expr_type e) e ca = (raw_op,cu) /\
   lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) sca = (raw_op,scu)` by
    simp[lower_value_def,comp_bind_def] >>
  `ca.cs_next_id <= cm.cs_next_id /\ cm.cs_next_id <= cu.cs_next_id` by
    (conj_tac
     >- (qspecl_then [`ce`,`expr_type e`,`e`,`ca`] mp_tac
           (cj 1 ci_mono_compile_expr_sa) >> simp[ci_mono_def]) >>
     qspecl_then [`ce`,`saved`,`cm`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
  `create_expr_prefix ca cu (gas_explicit_sites ctx shctx) ctx fnc s (mc ++ mu) u` by
    (drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
     irule blueprint_raw_join_prefix >> conj_tac
     >- (qexistsl [`bb`,`mk_inst cu.cs_next_id MLOAD [raw_op] [tmp]`] >>
         gvs[mk_inst_def]) >>
     qexistsl [`cm`,`m`] >> simp[]) >>
  `p.gas_obs = gas_explicit ((mc ++ mu) ++ rest) s.vs_gas_readings ++ tail` by
    simp[APPEND_ASSOC] >>
  drule_all blueprint_read_at_cut >> strip_tac >- metis_tac[] >>
  rename1 `bind (eval_expr cx e) (read_result cx) p = (INL bv,q)` >>
  `?bs. bv = BytesV bs` by
    (`value_has_type (BaseTV (BytesT (Dynamic k))) bv` by
       (qpat_x_assum `value_runtime_typed env _ bv` mp_tac >>
        simp[value_runtime_typed_def,evaluate_type_def]) >>
     drule_then strip_assume_tac exprSimConvertFromBytesTheory.dynamic_bytes_value_typed >>
     goal_assum (drule_at Any)) >>
  pop_assum strip_assume_tac >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  `u.vs_labels = s.vs_labels` by (drule_all blueprint_prefix_labels >> simp[]) >>
  `eval_operand target_op u = SOME aw` by
    (irule blueprint_eval_operand_frame >> qexistsl [`ca`,`s`] >> simp[] >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `post_value_type ce e = expr_type e` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  disj2_tac >> qexistsl [`bs`,`q`,`G'`,`tn'`] >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

(* A silent straight-line operand of raw blueprint preparation has only one
   successful machine step.  Read that step from the supplied prefix. *)
Theorem blueprint_raw_scalar_step[local]:
  emit_op opc args a = (op,b) /\ fn_has_code a b fn /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  opc <> GAS /\ opc <> INVOKE /\ ~is_terminator opc /\
  create_expr_prefix a b explicit ctx fn s ms t ==>
  ?x raw. op = Var x /\ not_fresh_at b x /\ a.cs_next_var <= b.cs_next_var /\
    step_inst_base (mk_inst a.cs_next_id opc args [x]) s = OK raw /\
    t = (raw with vs_inst_idx := SUC s.vs_inst_idx) /\
    ms = [] /\ ~t.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
  drule emit_op_facts >> strip_tac >> gvs[] >>
  qpat_x_assum `create_expr_prefix _ _ _ _ _ _ _ _` mp_tac >>
  simp[create_expr_prefix_marked] >> once_rewrite_tac[RTC_CASES1] >>
  simp[EXISTS_PROD, create_marked_edge_def, create_prefix_step_def] >>
  strip_tac >- (gvs[] >> decide_tac) >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
  simp[gas_origin_edge_def] >> strip_tac >>
  gvs[step_inst_non_invoke, exit_result_def, Once gasEventsTheory.gas_events_step_def]
  >- (drule_all (SIMP_RULE (srw_ss()) []
        (Q.SPEC `mk_inst id opc ops outs` venomInstProofs1Theory.step_inst_base_preserves_all)) >>
      strip_tac >>
      qpat_x_assum `RTC _ _ _` mp_tac >> once_rewrite_tac[RTC_CASES1] >>
      simp[EXISTS_PROD, create_marked_edge_def, create_prefix_step_def, ADD1,
           Once gasEventsTheory.gas_events_step_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `OK _ = step_inst_base _ _` (assume_tac o SYM) >>
  fs[exit_result_def]
QED

Theorem blueprint_raw_load_add[local]:
  emit_op MLOAD [raw_op] cu = (len,cl) /\
  emit_op ADD [raw_op;Lit 32w] cl = (data_op,(cprep:compile_state)) /\
  fn_has_code cu cl fn /\ fn_has_code cl cprep fn /\
  a.vs_current_bb = cu.cs_current_bb /\ a.vs_inst_idx = LENGTH cu.cs_current_insts /\
  b.vs_current_bb = cl.cs_current_bb /\ b.vs_inst_idx = LENGTH cl.cs_current_insts /\
  u.vs_current_bb = cprep.cs_current_bb /\ u.vs_inst_idx = LENGTH cprep.cs_current_insts /\
  create_expr_prefix cu cl explicit ctx fn a ml b /\
  create_expr_prefix cl cprep explicit ctx fn b ma u ==>
  run_inst_seq (emitted_insts cu cprep) a = OK (u with vs_inst_idx := a.vs_inst_idx) /\
  state_frame u = state_frame (a with vs_inst_idx := u.vs_inst_idx) /\
  cprep.cs_current_bb = cu.cs_current_bb /\
  cprep.cs_current_insts = cu.cs_current_insts ++ emitted_insts cu cprep /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts cu cprep) /\
  (!x. not_fresh_at cu x ==> lookup_var x u = lookup_var x a) /\
  (!x. len = Var x ==> not_fresh_at cprep x) /\ cu.cs_next_var <= cprep.cs_next_var /\
  ml = [] /\ ma = [] /\ u.vs_gas_readings = a.vs_gas_readings /\ ~u.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (Q.INST [`opc` |-> `MLOAD`] blueprint_raw_scalar_step |> SIMP_RULE (srw_ss()) [is_terminator_def]) >>
  disch_then (qx_choosel_then [`lvar`,`ra`] (map_every assume_tac o CONJUNCTS)) >>
  drule_all (Q.INST [`opc` |-> `ADD`] blueprint_raw_scalar_step |> SIMP_RULE (srw_ss()) [is_terminator_def]) >>
  disch_then (qx_choosel_then [`pvar`,`rb`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `cl.cs_current_insts = cu.cs_current_insts ++ emitted_insts cu cl /\
   cprep.cs_current_insts = cl.cs_current_insts ++ emitted_insts cl cprep /\
   cprep.cs_current_bb = cu.cs_current_bb` by
    (drule_all emit_op_facts >> strip_tac >>
     qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
     fs[]) >>
  `emitted_insts cu cprep = emitted_insts cu cl ++ emitted_insts cl cprep` by
    (irule emitted_insts_append >> metis_tac[]) >>
  `~not_fresh_at cu lvar /\ ~not_fresh_at cl pvar` by metis_tac[emit_op_facts, operand_11] >>
  `!x. not_fresh_at cu x ==> x <> lvar /\ x <> pvar` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `not_fresh_at cprep lvar /\ cu.cs_next_var <= cprep.cs_next_var` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, LESS_EQ_TRANS] >>
  gvs[stmtReasonMemoryTheory.step_mload_eq, stmtReasonMemoryTheory.step_add_eq,
      AllCaseEqs(), eval_operand_def] >>
  simp[run_inst_seq_def, stmtReasonMemoryTheory.step_mload_eq, stmtReasonMemoryTheory.step_add_eq,
       eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       state_frame_def, mk_inst_def, APPEND_ASSOC] >>
  fs[update_var_def, venom_state_component_equality]
QED

Theorem blueprint_raw_load_add_frame[local]:
  fn_has_code cu cprep fn /\ cprep.cs_current_bb = cu.cs_current_bb /\
  cprep.cs_current_insts = cu.cs_current_insts ++ emitted_insts cu cprep /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts cu cprep) /\
  a.vs_current_bb = cu.cs_current_bb /\ a.vs_inst_idx = LENGTH cu.cs_current_insts /\
  u.vs_inst_idx = LENGTH cprep.cs_current_insts /\ cu.cs_next_var <= cprep.cs_next_var /\
  state_frame u = state_frame (a with vs_inst_idx := u.vs_inst_idx) /\
  (!x. not_fresh_at cu x ==> lookup_var x u = lookup_var x a) /\
  local_ptrs_reserved ce cu /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  return_buf_frame d ce cu a /\ alloca_history fn a /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fn ce cx p a /\ ghost_inv_at (DF h) lo d ce cx p G tn a) ==>
  return_buf_frame d ce cprep u /\ alloca_history fn u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fn ce cx p u /\ ghost_inv_at (DF h) lo d ce cx p G tn u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `u.vs_allocas = a.vs_allocas /\ u.vs_alloca_next = a.vs_alloca_next /\
   u.vs_call_ctx = a.vs_call_ctx /\ u.vs_memory = a.vs_memory /\
   u.vs_accounts = a.vs_accounts /\ u.vs_transient = a.vs_transient /\
   u.vs_immutables = a.vs_immutables /\ u.vs_fmp = a.vs_fmp /\
   u.vs_initial_fmp = a.vs_initial_fmp` by
    (qpat_assum `state_frame _ = _` mp_tac >> simp[state_frame_def]) >>
  rpt conj_tac
  >- (irule return_buf_frame_frame >> qexistsl [`ce`,`a`,`cu`] >> simp[])
  >- (irule augassign_load_endpoint_history >> qexistsl [`a`,`cu`,`cprep`] >>
      PURE_ASM_REWRITE_TAC [] >> simp[])
  >- (`allocas_below_fmp u = allocas_below_fmp a` by simp[allocas_below_fmp_def] >> simp[]) >>
  rpt strip_tac >> first_x_assum (drule_then strip_assume_tac)
  >- (irule stmt_state_rel_old_vars_frame_ptr >> metis_tac[]) >>
  irule ghost_inv_at_exterior_frame >> metis_tac[]
QED

Theorem blueprint_raw_reach_at_cut[local]:
  create_expr_prefix ca cb explicit ctx fn u chunk t /\ ~u.vs_halted /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!f i z. frag_reachable ctx fn u f i z ==> dalloca_no_wrap i z) ==>
  !f i z. frag_reachable ctx fn t f i z ==> dalloca_no_wrap i z
Proof
  strip_tac >>
  `gas_path ctx fn u (LENGTH chunk) (OK t)` by
    (qpat_assum `create_expr_prefix _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE[create_expr_prefix_marked]) >>
     disch_then (mp_tac o MATCH_MP blueprint_prefix_gas_path) >> simp[]) >>
  `!j. active_inst fn j t ==> frag_reachable ctx fn u fn j t` by
    (drule gas_path_reach >> disch_then (qspecl_then [`fn`,`u`,`t`] mp_tac) >>
     simp[contextRawReachableTheory.frag_reachable_start]) >>
  metis_tac[contextRawReachableTheory.frag_reachable_trans]
QED

(* The raw bytes have already been read on the source side.  The two
   observed machine steps only expose their length and advance the cut. *)
Theorem blueprint_raw_finish_at_cut:
  expr_type e = BaseT (BytesT (Dynamic k)) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_create_blueprint_args compile_expr ce T later [e] ca = ((data,len),cprep) /\
  expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bs) raw_op u /\
  eval_operand target_op u = SOME aw /\
  (!x. target_op = Var x ==> not_fresh_at cu x) /\
  expr_sim_inv ce cx env q /\
  local_ptrs_reserved ce cu /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  return_buf_frame d ce cu u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h q.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx q u /\ storage_well_formed_on cx q (FST h) /\
    ghost_inv_at (DF h) lo d ce cx q G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = cu.cs_current_bb /\
  u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\
  emit_op ADD [raw_op;Lit 32w] cl = (data,cprep) /\ fn_has_code cu cprep fnc /\
  b.vs_current_bb = cl.cs_current_bb /\ b.vs_inst_idx = LENGTH cl.cs_current_insts /\
  t.vs_current_bb = cprep.cs_current_bb /\ t.vs_inst_idx = LENGTH cprep.cs_current_insts /\
  create_expr_prefix cu cl explicit ctx fnc u ml b /\
  create_expr_prefix cl cprep explicit ctx fnc b ma t /\
  (!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  q.gas_obs = gas_explicit (ml ++ ma ++ rest) u.vs_gas_readings ++ tail ==>
  eval_operand len t = SOME (n2w (LENGTH bs)) /\
  (!x. len = Var x ==> not_fresh_at cprep x) /\
  eval_operand target_op t = SOME aw /\
  (!x. target_op = Var x ==> not_fresh_at cprep x) /\
  expr_sim_inv ce cx env q /\
  local_ptrs_reserved ce cprep /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cprep x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cprep x) /\
  return_buf_frame d ce cprep t /\ alloca_history fnc t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h q.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
    ghost_inv_at (DF h) lo d ce cx q G tn t) /\
  ~t.vs_halted /\ t.vs_current_bb = cprep.cs_current_bb /\
  t.vs_inst_idx = LENGTH cprep.cs_current_insts /\
  q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends cu cl /\ cs_extends cl cprep` by
    metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all blueprint_raw_load_add >> strip_tac >>
  `eval_operand len (t with vs_inst_idx := u.vs_inst_idx) = SOME (n2w (LENGTH bs))` by
    (irule create_blueprint_raw_arg_actual_length >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `u` >> fs[]) >>
  `!h. valid_horizon cx st0 h q.storage_trace ==>
     stmt_state_rel h ctx fnc ce cx q u /\ ghost_inv_at (DF h) lo d ce cx q G tn u` by
    metis_tac[] >>
  drule_all blueprint_raw_load_add_frame >> strip_tac >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  `~b.vs_halted` by
    (drule_all (Q.INST [`opc` |-> `MLOAD`] blueprint_raw_scalar_step |>
      SIMP_RULE (srw_ss()) [is_terminator_def]) >> strip_tac >> simp[]) >>
  `!f i z. frag_reachable ctx fnc b f i z ==> dalloca_no_wrap i z` by
    (qpat_assum `create_expr_prefix cu cl _ _ _ _ _ _`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] blueprint_raw_reach_at_cut)) >>
     rpt (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  `!f i z. frag_reachable ctx fnc t f i z ==> dalloca_no_wrap i z` by
    (qpat_assum `create_expr_prefix cl cprep _ _ _ _ _ _`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] blueprint_raw_reach_at_cut)) >>
     rpt (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  `t.vs_labels = u.vs_labels` by
    (qpat_assum `state_frame t = _` mp_tac >> simp[state_frame_def]) >>
  `eval_operand target_op t = SOME aw` by
    (irule blueprint_eval_operand_frame >> qexistsl [`cu`,`u`] >> simp[]) >>
  fs[ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem create_raw_header_bands[local]:
  compile_create_snapshot ce vv ty a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ emit_op ADD [snap; Lit 32w] c = (data,d) /\
  fn_has_code a d fn /\ fn_inst_ids_distinct fn /\
  vv_location vv <> SOME LocCalldata /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts /\
  l.vs_current_bb = c.cs_current_bb /\ l.vs_inst_idx = LENGTH c.cs_current_insts /\
  r.vs_current_bb = d.cs_current_bb /\ r.vs_inst_idx = LENGTH d.cs_current_insts /\
  create_expr_prefix a b explicit ctx fn u msS z /\
  create_expr_prefix b c explicit ctx fn z msL l /\
  create_expr_prefix c d explicit ctx fn l msD r ==>
  msS = [] /\ msL = [] /\ msD = [] /\
  r.vs_gas_readings = u.vs_gas_readings /\
  run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx) /\
  run_inst_seq (emitted_insts c d) l = OK (r with vs_inst_idx := l.vs_inst_idx) /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
   run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx) /\
   run_inst_seq (emitted_insts a c) u = OK (l with vs_inst_idx := u.vs_inst_idx)) /\
  (!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?buf sm x exit.
      compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,sm) /\
      fn_has_code a sm fn /\ fn_has_code sm b fn /\
      lookup_block b.cs_current_bb fn.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
      z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx fn v ms (OK w)) x z)
Proof
  pure_rewrite_tac[create_expr_prefix_marked] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d` by
    metis_tac[ci_mono_def, ci_mono_compile_create_snapshot, ci_mono_emit_op, SND] >>
  `fn_has_code a c fn /\ fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c d fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!p ms q. create_prefix_step a b explicit ctx fn p ms q ==>
     (p.vs_current_bb <> b.cs_current_bb \/ p.vs_inst_idx <> LENGTH b.cs_current_insts) /\
     gas_origin_edge F explicit ctx fn p ms (OK q)` by
    simp[create_prefix_step_def, PULL_EXISTS] >>
  `!p ms q. create_prefix_step b c explicit ctx fn p ms q ==>
     (p.vs_current_bb <> c.cs_current_bb \/ p.vs_inst_idx <> LENGTH c.cs_current_insts) /\
     gas_origin_edge F explicit ctx fn p ms (OK q)` by
    simp[create_prefix_step_def, PULL_EXISTS] >>
  `!p ms q. create_prefix_step c d explicit ctx fn p ms q ==>
     (p.vs_current_bb <> d.cs_current_bb \/ p.vs_inst_idx <> LENGTH d.cs_current_insts) /\
     gas_origin_edge F explicit ctx fn p ms (OK q)` by
    simp[create_prefix_step_def, PULL_EXISTS] >>
  drule_all (Q.INST [`ES` |-> `create_prefix_step a b explicit ctx fn`,
                     `length_edge` |-> `create_prefix_step b c explicit ctx fn`,
                     `ED` |-> `create_prefix_step c d explicit ctx fn`]
                    create_raw_snapshot_straight_bands) >> strip_tac >>
  `!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?buf sm x exit.
      compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,sm) /\
      fn_has_code sm b fn /\ lookup_block b.cs_current_bb fn.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
      z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx fn v ms (OK w)) x z /\
      msS = [] /\ z.vs_gas_readings = u.vs_gas_readings` by
    (rpt strip_tac >>
     `!p ms q. create_prefix_step a b explicit ctx fn p ms q ==>
        (p.vs_current_bb <> b.cs_current_bb \/ p.vs_inst_idx <> LENGTH b.cs_current_insts) /\
        ?bb i. lookup_block p.vs_current_bb fn.fn_blocks = SOME bb /\
               get_instruction bb p.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
               gas_origin_edge F explicit ctx fn p ms (OK q)` by
       (simp[create_prefix_step_def] >> metis_tac[]) >>
     drule_all (Q.INST [`E` |-> `create_prefix_step a b explicit ctx fn`]
                 create_raw_snapshot_slot_band) >> simp[]) >>
  `vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/
   vv_location vv = SOME LocCode \/ ?tr. vv_location vv = SOME (slot_loc tr)` by
    (Cases_on `vv` >> gvs[vv_location_def] >>
     rename1 `p.ptr_location <> LocCalldata` >>
     Cases_on `p.ptr_location` >> gvs[slot_loc_def] >> metis_tac[]) >>
  `msS = [] /\ z.vs_gas_readings = u.vs_gas_readings` by metis_tac[] >>
  `r.vs_gas_readings = u.vs_gas_readings` by simp[] >>
  `((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
     run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx) /\
     run_inst_seq (emitted_insts a c) u = OK (l with vs_inst_idx := u.vs_inst_idx))` by
    (qpat_assum `_ ==> run_inst_seq _ _ = _ /\ _ /\ msS = [] /\ _` mp_tac >> metis_tac[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _`
    (drule_then strip_assume_tac) >>
  `fn_has_code a sm fn` by metis_tac[create_raw_snapshot_alloc_interval] >>
  qexistsl_tac [`buf`,`sm`,`x`,`exit`] >> asm_rewrite_tac[]
QED

Theorem create_raw_bytecode_header_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es /\
  EVERY (create_operand_completed_ok cx) (create_operand_order RawCreate hs (e::v::rest)) /\
  expr_vv_sim_full_pre (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es
    (st0,sa,sb,shadow_sa,shadow_sb,parent_vv,s0,G0,tn0) /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_a) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,a,shadow_sa,shadow_a) /\
  compile_create_snapshot ce vv (lowered_value_type ce e) a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ emit_op ADD [snap; Lit 32w] c = (data,d) /\
  fn_has_code a d func /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts /\
  l.vs_current_bb = c.cs_current_bb /\ l.vs_inst_idx = LENGTH c.cs_current_insts /\
  r.vs_current_bb = d.cs_current_bb /\ r.vs_inst_idx = LENGTH d.cs_current_insts /\
  create_expr_prefix sa a (gas_explicit_sites ctx shadow_ctx) ctx func s0 ms u /\
  create_expr_prefix a b (gas_explicit_sites ctx shadow_ctx) ctx func u msS z /\
  create_expr_prefix b c (gas_explicit_sites ctx shadow_ctx) ctx func z msL l /\
  create_expr_prefix c d (gas_explicit_sites ctx shadow_ctx) ctx func l msD r /\
  eval_expr cx (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df)
    (es with gas_obs := gas_explicit (ms ++ (msS ++ msL ++ msD ++ later)) s0.vs_gas_readings ++ tail) = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?p tv code G tn n.
    expr_body_pre ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic n)) /\
    LENGTH code <= n /\ n <= 49152 /\
    eval_expr cx e (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL tv,p) /\
    p.gas_obs = gas_explicit later r.vs_gas_readings ++ tail /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
    bind (eval_exprs cx (TAKE (LENGTH rest - (if hs then 1 else 0)) rest ++
                       v :: DROP (LENGTH rest - (if hs then 1 else 0)) rest))
      (\vs. eval_create_operands cx RawCreate hs rof (MAP expr_type (e::v::rest))
        (blueprint_literal_offset cx hs (e::v::rest)) (BytesV code::vs)) p = (res,ee) /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv ce cx env p /\
    eval_operand len l = SOME (n2w (LENGTH code)) /\
    local_ptrs_reserved ce a /\ fn_has_code a b func /\
    msS = [] /\ msL = [] /\ msD = [] /\ r.vs_gas_readings = u.vs_gas_readings /\
    run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx) /\
    run_inst_seq (emitted_insts c d) l = OK (r with vs_inst_idx := l.vs_inst_idx) /\
    ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
     run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx)) /\
    (!tr. vv_location vv = SOME (slot_loc tr) ==>
      ?buf sm x exit.
        compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,sm) /\
        fn_has_code sm b func /\ lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
        phi_prefix_length exit.bb_instructions = 0 /\
        x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
        z.vs_inst_idx = 0 /\
        run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
        RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                   ?ms. gas_origin_edge F (gas_explicit_sites ctx shadow_ctx) ctx func v ms (OK w)) x z) /\
    !h. valid_horizon cx st0 h p.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) ms (OK u,G,tn) /\
      vv_post h ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) (p with gas_obs := []) tv vv u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF h) lo dep ce cx (p with gas_obs := []) G tn u /\
      ptr_vv_ok cx (post_value_type ce e) tv vv (p with gas_obs := []) G tn u /\
      (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
              eval_operand (vv_operand vv) u = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
                      val_in_memory rt (BytesV code) (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G u) /\
      (!t' ptr. vv = LocatedValue t' ptr /\ ptr.ptr_location = LocMemory ==>
               ptr_buf_ok ce e ptr.ptr_operand G u) /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (Q.INST [`later` |-> `msS ++ msL ++ msD ++ later`] create_raw_bytecode_replay) >>
  strip_tac >- (disj1_tac >> metis_tac[]) >>
  `expr_body_pre ce cx env e es` by
    (drule exprBodyPrePropsTheory.expr_body_pre_static_facts >> strip_tac >>
     `MEM e (e::v::rest)` by simp[] >> metis_tac[create_raw_arg_body_pre]) >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  `vv_location vv <> SOME LocCalldata` by
    (Cases_on `vv` >> gvs[vv_location_def] >> metis_tac[exprPtrUnwrapMarkedTheory.vv_post_not_calldata]) >>
  `fn_inst_ids_distinct func /\ MEM func ctx.ctx_functions /\ local_ptrs_reserved ce sa` by
    fs[expr_vv_sim_full_pre_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  drule_all create_raw_header_bands >> strip_tac >>
  `local_ptrs_reserved ce a` by
    metis_tac[local_ptrs_reserved_next_var, compile_expr_ci_mono, ci_mono_def, SND] >>
  `copy_old_operand a (vv_operand vv)` by metis_tac[compile_expr_old_operand] >>
  `fn_has_code a b func` by
    metis_tac[fn_has_code_split, cs_extends_trans, ci_mono_def,
              ci_mono_compile_create_snapshot, ci_mono_emit_op, SND] >>
  `post_value_type ce e = BaseT (BytesT (Dynamic n))` by
    (irule EQ_TRANS >> qexists_tac `expr_type e` >>
     simp[post_value_type_bytestring,is_bytestring_type_def]) >>
  qabbrev_tac `obs = gas_explicit (ms ++ (msS ++ msL ++ msD ++ later)) s0.vs_gas_readings ++ tail` >>
  `expr_body_pre ce cx env e (es with gas_obs := obs)` by simp[expr_body_pre_gas_obs] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
    (INL (BytesV code),p)` by simp[bind_def] >>
  drule_all create_blueprint_raw_copy_layout >> strip_tac >>
  `LENGTH code + 32 < dimword (:256)` by
    (qpat_assum `LENGTH code <= n` mp_tac >>
     qpat_assum `n <= 49152` mp_tac >> simp[dimword_def] >> decide_tac) >>
  `eval_operand len l = SOME (n2w (LENGTH code))` by
    (suspend "snapshot_length") >>
  disj2_tac >> qexistsl_tac [`p`,`tv`,`code`,`G`,`tn`,`n`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _`
       (fn th => mp_tac th) >> metis_tac[] >> NO_TAC) >>
  fs[Abbr `obs`]
QED

Resume create_raw_bytecode_header_at_cuts[snapshot_length]:
  `vv_location vv = SOME LocCode ==>
     local_ptrs_reserved ce a /\
     (ce.ce_is_ctor ==> !w. eval_operand (vv_operand vv) u = SOME w ==>
        val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV code) (w2n w) u.vs_memory) /\
     w2n (n2w (buffer_allocation_base u a.cs_next_id) : bytes32) +
       32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) < dimword (:256)` by
    (disch_tac >> conj_tac >- first_assum ACCEPT_TAC >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` mp_tac >>
         simp[bodyPtrDefsTheory.mem_agree_outside_def] >> metis_tac[]) >>
     Cases_on `compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a` >>
     rename1 `_ = (buf,sm)` >> drule_all create_raw_snapshot_alloc_interval >> strip_tac >>
     drule_all create_raw_code_snapshot_site_bound >> simp[]) >>
  `!tr. vv_location vv = SOME (slot_loc tr) ==>
     ?buf sm x exit.
       compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,sm) /\
       32 <= type_memory_bytes ce (lowered_value_type ce e) /\
       w2n (n2w (buffer_allocation_base u a.cs_next_id) : bytes32) +
         32 * ((type_memory_bytes ce (lowered_value_type ce e) + 31) DIV 32) < dimword (:256) /\
       fn_has_code sm b func /\ lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
       phi_prefix_length exit.bb_instructions = 0 /\
       x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
       z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = 0 /\
       run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
       RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                  ?ms. gas_origin_edge F (gas_explicit_sites ctx shadow_ctx) ctx func v ms (OK w)) x z /\
       run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _`
       (drule_then strip_assume_tac) >>
     `stmt_state_rel H ctx func ce cx (p with gas_obs := []) u` by fs[vv_post_def] >>
     drule_all create_raw_header_capacity >> strip_tac >>
     qexistsl_tac [`buf`,`sm`,`x`,`exit`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     metis_tac[create_raw_header_slot_nonwrap]) >>
  pop_assum (mk_asm "slot_length") >>
  `((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
     run_inst_seq (emitted_insts a c) u = OK (l with vs_inst_idx := u.vs_inst_idx))` by
    (qpat_assum `_ ==> run_inst_seq (emitted_insts a b) _ = _ /\ _` mp_tac >> metis_tac[]) >>
  `((vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==> LENGTH code + 32 < dimword (:256))` by simp[] >>
  let fun consume 0 th = irule th
        | consume n th = drule_then (consume (n - 1)) th
  in consume 7 create_snapshot_length_word end >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac `gas_explicit_sites ctx shadow_ctx` >>
  gen_tac >> disch_tac >> asm "slot_length" (drule_then strip_assume_tac) >>
  qexistsl_tac [`buf`,`sm`,`x`,`z`,`exit`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise create_raw_bytecode_header_at_cuts

Theorem create_prefix_band_rtc[local]:
  lo <= a.cs_next_id /\ b.cs_next_id <= hi /\
  create_expr_prefix a b explicit ctx fn u marks v ==>
  RTC (\p q. ?bb i ms. lookup_block p.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME i /\ lo <= i.inst_id /\ i.inst_id < hi /\
    gas_origin_edge F explicit ctx fn p ms (OK q)) u v
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  `!x y. RTC (create_marked_edge (create_prefix_step a b explicit ctx fn)) x y ==>
         RTC (\p q. ?bb i ms. lookup_block p.vs_current_bb fn.fn_blocks = SOME bb /\
           get_instruction bb p.vs_inst_idx = SOME i /\ lo <= i.inst_id /\ i.inst_id < hi /\
           gas_origin_edge F explicit ctx fn p ms (OK q)) (FST x) (FST y)`
    suffices_by (disch_then drule >> simp[]) >>
  ho_match_mp_tac RTC_INDUCT >> simp[FORALL_PROD, create_marked_edge_def, create_prefix_step_def] >>
  rpt strip_tac >> irule (cj 2 RTC_RULES) >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `ms` >>
  fs[frag_ids_def] >> decide_tac
QED

Theorem create_indexed_rtc_join[local]:
  !n k (states:'a list) R.
    (!i. k <= i /\ i < k+n ==> RTC R (EL i states) (EL (SUC i) states)) ==>
    RTC R (EL k states) (EL (k+n) states)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `RTC R (EL k states) (EL (k+n) states)` by (first_x_assum irule >> simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `RTC R (EL (k+n) states) (EL (SUC (k+n)) states)` by (first_x_assum irule >> decide_tac) >>
  simp[ADD_CLAUSES] >> metis_tac[RTC_TRANS]
QED

Theorem create_copy_fixed_run[local]:
  cuts = ac::bc::c::prep /\ LAST (c::prep) = sc /\
  EVERY (\z. c.cs_next_id <= z.cs_next_id /\ z.cs_next_id <= sc.cs_next_id) (c::prep) /\
  LIST_REL (\z u. u.vs_current_bb = z.cs_current_bb /\ u.vs_inst_idx = LENGTH z.cs_current_insts)
    (sa::cuts) states /\ LAST states = s /\
  (!i. i < LENGTH cuts ==> create_expr_prefix (EL i (sa::cuts)) (EL i cuts)
    explicit ctx fn (EL i states) (EL i chunk_rows) (EL (SUC i) states)) /\
  fn_has_code c sc fn /\ sc.cs_current_bb = c.cs_current_bb /\
  sc.cs_current_insts = c.cs_current_insts ++ emitted_insts c sc /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts c sc) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id = sc.cs_next_id ==>
  run_inst_seq (emitted_insts c sc) (EL 3 states) = OK (s with vs_inst_idx := (EL 3 states).vs_inst_idx)
Proof
  strip_tac >> qpat_x_assum `cuts = _` SUBST_ALL_TAC >>
  qpat_x_assum `LIST_REL _ _ _` (strip_assume_tac o REWRITE_RULE[LIST_REL_EL_EQN]) >>
  `LENGTH states = SUC (3 + LENGTH prep)` by fs[] >>
  `EL (3 + LENGTH prep) states = s /\
   EL (3 + LENGTH prep) (sa::ac::bc::c::prep) = sc` by
    (conj_tac
     >- (`states <> []` by (Cases_on `states` >> fs[]) >> fs[LAST_EL]) >>
     qspec_then `sa::ac::bc::c::prep` mp_tac LAST_EL >>
     simp[LAST_CONS_cond, ADD_CLAUSES] >> fs[LAST_CONS_cond, ADD_CLAUSES]) >>
  `((EL 3 states).vs_current_bb = c.cs_current_bb /\
    (EL 3 states).vs_inst_idx = LENGTH c.cs_current_insts) /\
   s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts` by
    (qpat_assum `!n. n < LENGTH (sa::_) ==> _`
       (fn th => mp_tac (Q.SPEC `3` th) >> mp_tac (Q.SPEC `3 + LENGTH (prep:compile_state list)` th)) >>
     BETA_TAC >>
     qpat_assum `EL _ (sa::_) = (sc:compile_state)`
       (fn th => PURE_REWRITE_TAC[th]) >>
     qpat_assum `EL _ states = (s:venom_state)`
       (fn th => PURE_REWRITE_TAC[th]) >>
     simp[EL_CONS, ADD_CLAUSES]) >>
  qabbrev_tac `R = \p q. ?bb i ms. lookup_block p.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME i /\ c.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
    gas_origin_edge F explicit ctx fn p ms (OK q)` >>
  `RTC R (EL 3 states) (EL (3 + LENGTH prep) states)` by
    (irule create_indexed_rtc_join >> rpt strip_tac >>
     `i < LENGTH (ac::bc::c::prep)` by simp[] >>
     qpat_assum `!i. i < LENGTH (ac::_) ==> create_expr_prefix _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     `EL (i-3) (c::prep) = EL i (sa::ac::bc::c::prep) /\
      EL (i+1-3) (c::prep) = EL i (ac::bc::c::prep)` by
       (`?j. i = SUC (SUC (SUC j))` by (qexists_tac `i-3` >> decide_tac) >>
        `SUC (SUC (SUC j)) - 3 = j /\ SUC (SUC (SUC j)) + 1 - 3 = SUC j` by decide_tac >>
        asm_rewrite_tac[] >> simp[]) >>
     qpat_x_assum `EVERY (\z. _ <= z.cs_next_id /\ _) (c::prep)`
       (assume_tac o SIMP_RULE bool_ss [EVERY_EL, BETA_THM]) >>
     `i-3 < LENGTH (c::prep) /\ i+1-3 < LENGTH (c::prep)` by (simp[] >> decide_tac) >>
     rw[Abbr `R`] >> irule create_prefix_band_rtc >> goal_assum (drule_at Any) >>
     qpat_x_assum `!n. n < LENGTH (c::_) ==> _`
       (fn th => mp_tac (Q.SPEC `i-3` th) >> mp_tac (Q.SPEC `i+1-3` th)) >>
     asm_rewrite_tac[] >> simp[]) >>
  irule create_straight_prefix_run >>
  simp[] >>
  qpat_x_assum `fn_has_code c sc fn` (strip_assume_tac o REWRITE_RULE[fn_has_code_def]) >>
  qexistsl_tac [`R`,`bb`,`ctx`,`explicit`,`fn`] >>
  `lookup_block c.cs_current_bb fn.fn_blocks = SOME bb` by metis_tac[] >>
  `?rest. bb.bb_instructions = c.cs_current_insts ++ (emitted_insts c sc ++ rest)` by
    (qpat_x_assum `_ ≼ bb'.bb_instructions` mp_tac >> fs[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  `!p q. p.vs_current_bb = s.vs_current_bb /\ p.vs_inst_idx = s.vs_inst_idx ==> ~R p q` by
    (simp[Abbr `R`] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  conj_tac >- (simp[Abbr `R`, PULL_EXISTS] >> metis_tac[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> first_x_assum irule >> fs[]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (PURE_REWRITE_TAC[DROP_LENGTH_APPEND, IS_PREFIX_APPEND] >> qexists_tac `rest` >> simp[]) >>
  metis_tac[]
QED

Theorem create_copy_scalar_prefix_rows[local]:
  cuts = a::b::c::prep /\ HD states = s0 /\ LENGTH chunk_rows = LENGTH cuts /\
  LIST_REL (\z u. u.vs_current_bb = z.cs_current_bb /\ u.vs_inst_idx = LENGTH z.cs_current_insts)
    (sa::cuts) states /\
  (!i. i < LENGTH cuts ==> create_expr_prefix (EL i (sa::cuts)) (EL i cuts)
    explicit ctx fn (EL i states) (EL i chunk_rows) (EL (SUC i) states)) /\
  marks = FLAT chunk_rows ==>
  create_expr_prefix sa a explicit ctx fn s0 (EL 0 chunk_rows) (EL 1 states) /\
  create_expr_prefix a b explicit ctx fn (EL 1 states) (EL 1 chunk_rows) (EL 2 states) /\
  create_expr_prefix b c explicit ctx fn (EL 2 states) (EL 2 chunk_rows) (EL 3 states) /\
  (EL 1 states).vs_current_bb = a.cs_current_bb /\ (EL 1 states).vs_inst_idx = LENGTH a.cs_current_insts /\
  (EL 2 states).vs_current_bb = b.cs_current_bb /\ (EL 2 states).vs_inst_idx = LENGTH b.cs_current_insts /\
  (EL 3 states).vs_current_bb = c.cs_current_bb /\ (EL 3 states).vs_inst_idx = LENGTH c.cs_current_insts /\
  marks = EL 0 chunk_rows ++ (EL 1 chunk_rows ++ (EL 2 chunk_rows ++ FLAT (DROP 3 chunk_rows)))
Proof
  strip_tac >> qpat_x_assum `cuts = _` SUBST_ALL_TAC >>
  qpat_x_assum `LIST_REL _ _ _` (strip_assume_tac o REWRITE_RULE[LIST_REL_EL_EQN]) >>
  `EL 0 states = s0` by (Cases_on `states` >> fs[]) >>
  qpat_x_assum `!i. _ ==> create_expr_prefix _ _ _ _ _ _ _ _`
    (fn th => map_every (fn k => qspec_then k mp_tac th) [`0`,`1`,`2`]) >>
  qpat_x_assum `!i. i < LENGTH _ ==> _`
    (fn th => map_every (fn k => qspec_then k mp_tac th) [`1`,`2`,`3`]) >>
  `3 < LENGTH states` by fs[] >>
  simp[EL_CONS] >> rpt strip_tac >> simp[] >>
  `2 < LENGTH chunk_rows` by fs[] >>
  `TAKE 3 chunk_rows = [EL 0 chunk_rows; EL 1 chunk_rows; EL 2 chunk_rows]` by
    (map_every (fn k => qspecl_then [`chunk_rows:bool list list`,k] mp_tac TAKE_EL_SNOC)
       [`2`,`1`] >>
     `chunk_rows <> []` by (Cases_on `chunk_rows` >> fs[]) >>
     simp[TAKE1, SNOC] >> decide_tac) >>
  `FLAT (TAKE 3 (chunk_rows:bool list list) ++ DROP 3 chunk_rows) = FLAT chunk_rows` by
    (PURE_REWRITE_TAC[TAKE_DROP] >> REFL_TAC) >>
  pop_assum mp_tac >> simp[FLAT_APPEND, APPEND_ASSOC] >> metis_tac[]
QED

Theorem create_size_exit_copy:
  !cx ann has_salt rof ks args dflt.
    EVERY (create_operand_completed_ok cx) (create_operand_order CreateCopyOf has_salt args) ==>
    create_expr_size_exit cx (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt)
Proof
  rewrite_tac[create_expr_size_exit_def] >>
  rpt (gen_tac ORELSE disch_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  `?result. compile_create_call compile_expr cenv CreateCopyOf has_salt rof args sa = (result,sb)` by
    (qpat_assum `compile_expr _ _ (Call _ _ _ _) _ = _` mp_tac >>
     rewrite_tac[exprSimSendTheory.compile_expr_call, compile_call_def] >>
     Cases_on `compile_create_call compile_expr cenv CreateCopyOf has_salt rof args sa` >>
     simp[as_stack_val_def]) >>
  `MEM inst.inst_opcode [CREATE; CREATE2]` by fs[] >>
  drule_all create_size_prefix_cuts >> strip_tac >>
  qpat_x_assum `create_call_itinerary _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [create_call_itinerary_def, create_kind_case_def, create_copy_itinerary_def]) >>
  rename1 `lower_value compile_expr cenv (expr_type target_e) target_e sa = (target,a)` >>
  rename1 `lower_value compile_expr cenv (expr_type value_e) value_e a = (value_op,b)` >>
  rename1 `create_itinerary_salt _ _ b salt_op c` >>
  rename1 `create_size_dispatch_tail rof dispatch sd created bufop len value_op salt_op result sb` >>
  `well_typed_expr env (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt)` by
    (drule exprBodyPrePropsTheory.expr_body_pre_static_facts >> simp[]) >>
  qabbrev_tac `salt_e = if has_salt then SOME (HD rest) else NONE` >>
  `has_salt = IS_SOME salt_e /\
   args = target_e::value_e::(case salt_e of NONE => [] | SOME e => [e])` by
    (qpat_x_assum `well_typed_expr _ _` mp_tac >>
     qpat_assum `args = target_e::value_e::rest` (fn th => PURE_REWRITE_TAC[th]) >>
     Cases_on `has_salt` >> simp[Abbr `salt_e`, well_typed_expr_def, create_arg_types_ok_def] >>
     Cases_on `rest` >> simp[] >> rename1 `MAP expr_type rs = _ ==> _` >> Cases_on `rs` >> simp[]) >>
  `compile_create_salt compile_expr cenv salt_e b = (salt_op,c)` by
    (qpat_x_assum `create_itinerary_salt _ _ b salt_op c` mp_tac >>
     qpat_assum `Abbrev (salt_e = _)` (fn th => PURE_REWRITE_TAC[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
     Cases_on `salt_e` >> simp[create_itinerary_salt_def, compile_create_salt_def, comp_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[]) >>
  rename1 `emit_op ADD [code; Lit 11w] _ = (len,sc)` >>
  rename1 `marks = FLAT chunk_rows` >>
  drule_all create_copy_preparation_code >>
  disch_then (strip_assume_tac o Q.SPEC `value_op`) >>
  `dispatch = sc` by
    (qpat_assum `LAST (sa::cuts) = dispatch` mp_tac >>
     qpat_assum `cuts = _` (fn th => PURE_REWRITE_TAC[th]) >> simp[]) >>
  qpat_x_assum `dispatch = sc` SUBST_ALL_TAC >>
  `compile_create_dispatch bufop len value_op salt_op rof sc = (result,sb)` by
    (Cases_on `salt_op` >>
     qpat_assum `create_size_dispatch_tail _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE bool_ss [create_size_dispatch_tail_def, optionTheory.option_case_def]) >>
     qpat_x_assum `created = Var out` SUBST_ALL_TAC >>
     simp[compile_create_dispatch_def, comp_bind_def]) >>
  `compile_create_copy target value_op salt_op rof c = (result,sb)` by
    (first_x_assum irule >> simp[]) >>
  drule_all create_copy_scalar_code >> strip_tac >>
  drule_all create_copy_scalar_prefix_rows >> strip_tac >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?acc. accounts_agree H cx.txn.target acc (EL 3 states).vs_accounts /\ accounts_well_typed acc` by
    (irule create_copy_replay_accounts_at_cuts >>
     qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `args = target_e::value_e::(case salt_e of NONE => [] | SOME e => [e])`
       (irule_at Any) >>
     qpat_assum `lower_value _ _ _ target_e sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ value_e a = _` (irule_at Any) >>
     qpat_assum `compile_create_salt _ _ salt_e b = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr target_e) shadow_sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr value_e) b1 = _` (irule_at Any) >>
     qpat_assum `compile_create_salt _ _ (OPTION_MAP gas_shadow_expr salt_e) b2 = _` (irule_at Any) >>
     qpat_assum `create_expr_prefix sa a _ _ _ s0 _ _` (irule_at Any) >>
     qpat_assum `create_expr_prefix a b _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `create_expr_prefix b c _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> qexistsl_tac [`tail`,`FLAT (DROP 3 chunk_rows)`,`env`,`ee`] >>
     fs[APPEND_ASSOC])
  >- (disj2_tac >> goal_assum (drule_at Any) >> simp[]) >>
  `cs_extends sa c` by
    (`!ce ty e u. cs_extends u (SND (lower_value compile_expr ce ty e u))` by
       simp[lower_value_labels, compile_expr_labels] >>
     `cs_extends b c` by metis_tac[compile_create_salt_labels, compile_expr_labels, SND] >>
     metis_tac[cs_extends_trans, SND]) >>
  `cs_extends sc sb` by
    (irule cs_extends_trans >> qexists_tac `sd` >>
     Cases_on `salt_op` >>
     qpat_assum `create_size_dispatch_tail _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE bool_ss [create_size_dispatch_tail_def, optionTheory.option_case_def]) >>
     (conj_tac
      >- (qpat_assum `emit_op _ _ sc = _` (fn th =>
            mp_tac (SIMP_RULE bool_ss [ci_mono_def, th, SND] ci_mono_emit_op)) >>
          simp[ci_mono_def] >> metis_tac[SND]) >>
      qspecl_then [`created`,`rof`,`sd`] mp_tac compile_check_create_result_labels >>
      asm_rewrite_tac[SND] >> simp[])) >>
  `fn_has_code c sc func` by metis_tac[fn_has_code_mid] >>
  `inst.inst_id = sc.cs_next_id /\ eval_operand len s = SOME w` by
    (Cases_on `salt_op` >> fs[mk_inst_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts c sc) (EL 3 states) =
    OK (s with vs_inst_idx := (EL 3 states).vs_inst_idx)` by
    (irule create_copy_fixed_run >> asm_rewrite_tac[] >>
     qpat_assum `(cuts:compile_state list) = _::_::_::_` (irule_at Any) >>
     qpat_assum `fn_has_code c sc func` (irule_at Any) >>
     `get_instruction bb (LENGTH (c.cs_current_insts ++ emitted_insts c sc)) = SOME inst` by fs[] >>
     pop_assum (irule_at Any) >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`sa`,`gas_explicit_sites ctx shadow_ctx`,`ctx`,`chunk_rows`] >>
     fs[]) >>
  `eval_operand len (s with vs_inst_idx := (EL 3 states).vs_inst_idx) = SOME w` by
    simp[ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  drule_all create_copy_pre_dispatch_length_bound >> simp[GSYM NOT_LESS_EQUAL]
QED

(* Replay the first operand on the observed address cut. The returned source
   state still carries the marks of the unexecuted payload and keywords. *)
Theorem create_blueprint_address_at_cut:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,(PG : (num # num) option list),fnc,shfnc)
    ce cx ty (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
  EVERY (create_operand_completed_ok cx) (create_operand_order (CreateFromBlueprint raw) hs args) /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  later = amount::((if hs then [salt] else []) ++ [off]) /\
  lower_value compile_expr ce (expr_type target) target sa = (target_op,ca) /\
  lower_value compile_expr ce (expr_type target) (gas_shadow_expr target) shadow_sa = (target_op,sca) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (sa,ca,shadow_sa,sca) /\
  create_expr_prefix sa ca (gas_explicit_sites ctx shctx) ctx fnc s0 chunk u /\
  u.vs_current_bb = ca.cs_current_bb /\ u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  eval_expr cx (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df)
    (es with gas_obs := gas_explicit (chunk ++ rest) s0.vs_gas_readings ++ tail) = (res,out) /\
  valid_horizon cx st0 H out.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?av aw p G tn.
    dest_AddressV av = SOME (w2w aw) /\ eval_operand target_op u = SOME aw /\
    (!x. target_op = Var x ==> not_fresh_at ca x) /\
    bind (eval_exprs cx (ctors ++ later))
      (\vs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p = (res,out) /\
    p.gas_obs = gas_explicit rest u.vs_gas_readings ++ tail /\
    valid_horizon cx st0 H p.storage_trace /\
    expr_sim_inv ce cx env p /\
    local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
    return_buf_frame d ce ca u /\ alloca_history fnc u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_no_wrap i z) /\
    (!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
      ghost_inv_at (DF h) lo d ce cx p G tn u) /\
    ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\ u.vs_inst_idx = LENGTH ca.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type target = BaseT AddressT /\ expr_sim_inv ce cx env es` by
    (drule expr_body_pre_static_facts >> strip_tac >> simp[] >>
     Cases_on `hs` >> gvs[well_typed_expr_def,create_arg_types_ok_def]) >>
  `create_operand_order (CreateFromBlueprint raw) hs args = target::(ctors ++ later)` by
    (qpat_assum `args = _` (pure_rewrite_tac o single) >>
     qpat_assum `later = _` (pure_rewrite_tac o single) >>
     Cases_on `hs` >> simp[create_operand_order_def]) >>
  `create_operand_completed_ok cx target` by fs[] >>
  qabbrev_tac `start = es with gas_obs := gas_explicit (chunk ++ rest) s0.vs_gas_readings ++ tail` >>
  `expr_body_pre ce cx env target start` by
    (`MEM target args` by (qpat_assum `args = _` (pure_rewrite_tac o single) >> simp[]) >>
     simp[Abbr `start`] >> irule blueprint_keyword_body_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  qabbrev_tac `k = \av. bind (eval_exprs cx (ctors ++ later))
      (\vs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs))` >>
  `!av. storage_trace_frame (k av)` by
    simp[Abbr `k`,blueprint_read_list_frame,storage_trace_frame_create_operands] >>
  `bind (bind (eval_expr cx target) (read_result cx)) k start = (res,out)` by
    (qpat_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
     PURE_ONCE_REWRITE_TAC [evaluate_def] >>
     simp[create_copy_source_cons,Abbr `k`]) >>
  qpat_x_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  `start.gas_obs = gas_explicit (chunk ++ rest) s0.vs_gas_readings ++ tail` by simp[Abbr `start`] >>
  `!h. valid_horizon cx st0 h start.storage_trace ==>
       stmt_state_rel h ctx fnc ce cx start s0 /\ storage_well_formed_on cx start (FST h) /\
       ghost_inv_at (DF h) lo d ce cx start G0 tn0 s0` by
    (qx_gen_tac `h` >>
     `storage_well_formed_on cx start (FST h) <=> storage_well_formed_on cx es (FST h)` by
       (irule storage_well_formed_on_backends >> simp[Abbr `start`]) >>
     `ghost_inv_at (DF h) lo d ce cx start G0 tn0 s0 <=>
      ghost_inv_at (DF h) lo d ce cx es G0 tn0 s0` by
       simp[Abbr `start`,ghost_inv_at_def] >>
     `stmt_state_rel h ctx fnc ce cx start s0 <=> stmt_state_rel h ctx fnc ce cx es s0`
       by simp[Abbr `start`] >>
     `start.storage_trace = es.storage_trace` by simp[Abbr `start`] >>
     asm_rewrite_tac[]) >>
  drule_all blueprint_read_at_cut >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  rename1 `k av p = (res,out)` >>
  `post_value_type ce target = BaseT AddressT` by simp[is_word_type_def] >>
  `?aw. dest_AddressV av = SOME (w2w aw) /\ eval_operand target_op u = SOME aw` by suspend "decode" >>
  `!x. target_op = Var x ==> not_fresh_at ca x` by
    (qpat_assum `lower_value _ _ _ target sa = _`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] compile_lower_value_var)) >> simp[]) >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  disj2_tac >> qexistsl_tac [`av`,`aw`,`p`,`G'`,`tn'`] >> fs[Abbr `k`] >>
  first_assum ACCEPT_TAC
QED

Resume create_blueprint_address_at_cut[decode]:
  qpat_assum `value_runtime_typed _ _ av` mp_tac >>
  qpat_assum `expr_val_rel _ _ av _ _` mp_tac >>
  qpat_assum `expr_type target = _` (mp_tac) >>
  qpat_assum `post_value_type ce target = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[value_runtime_typed_def,vyperValueTheory.evaluate_type_def] >>
  strip_tac >> strip_tac >> Cases_on `av` >> simp[value_has_type_def] >>
  simp[expr_val_rel_def, is_word_type_def, vyperValueTheory.evaluate_type_def,
       typed_val_to_w256_def, dest_AddressV_def] >>
  rpt strip_tac >>
  qspec_then `l` mp_tac
    (venomMemPropsTheory.w2w_word_of_bytes_be_pad_left
     |> INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``]) >>
  simp[dividesTheory.compute_divides, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  disch_then (rewrite_tac o single o SYM) >> wordsLib.WORD_DECIDE_TAC
QED
Finalise create_blueprint_address_at_cut

(* Visit the calls in the original suffix, while carrying their reached
   source states. The continuation is kept under its actual bind. *)
Theorem blueprint_ctor_source_walk[local]:
  !n i p k.
    i + n = LENGTH es /\ P i p /\
    bind (eval_exprs cx (DROP i es)) k p = (res,out) /\
    (!vs. storage_trace_frame (k vs)) /\
    (!j q l. j < LENGTH es /\ P j q /\ (!v. storage_trace_frame (l v)) /\
       bind (bind (eval_expr cx (EL j es)) (read_result cx)) l q = (res,out) ==>
       (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
       ?v q'. bind (eval_expr cx (EL j es)) (read_result cx) q = (INL v,q') /\
              l v q' = (res,out) /\ P (SUC j) q') ==>
    (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
    ?vs E. E i = p /\ LENGTH vs = n /\
       eval_exprs cx (DROP i es) p = (INL vs,E (LENGTH es)) /\
       k vs (E (LENGTH es)) = (res,out) /\
       (!j. i <= j /\ j <= LENGTH es ==> P j (E j)) /\
       (!j. i <= j /\ j < LENGTH es ==>
         bind (eval_expr cx (EL j es)) (read_result cx) (E j) =
           (INL (EL (j-i) vs),E (SUC j)))
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[blueprint_eval_nil_action, bind_return] >>
      disj2_tac >> qexists_tac `\j. p` >> simp[return_def] >>
      metis_tac[LESS_EQUAL_ANTISYM]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `i < LENGTH es /\ SUC i + n = LENGTH es` by decide_tac >>
  `DROP i es = EL i es :: DROP (SUC i) es` by metis_tac[DROP_CONS_EL] >>
  qabbrev_tac `l = \v. bind (eval_exprs cx (DROP (SUC i) es)) (\vs. k (v::vs))` >>
  `!v. storage_trace_frame (l v)` by simp[Abbr `l`, blueprint_read_list_frame] >>
  `bind (bind (eval_expr cx (EL i es)) (read_result cx)) l p = (res,out)` by
    (qpat_x_assum `bind (eval_exprs cx (DROP i es)) k p = _` mp_tac >>
     simp[create_copy_source_cons, Abbr `l`]) >>
  first_assum (qspecl_then [`i`,`p`,`l`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >- metis_tac[] >>
  rename1 `l v q = (res,out)` >>
  first_x_assum (qspecl_then [`SUC i`,`q`,`\vs. k (v::vs)`] mp_tac) >>
  (impl_tac >- fs[Abbr `l`]) >> strip_tac >- metis_tac[] >>
  rename1 `E (SUC i) = q` >>
  disj2_tac >> qexistsl [`v::vs`,`\j. if j = i then p else E j`] >>
  simp[] >> rpt conj_tac
  >- (irule blueprint_eval_join_cons >> metis_tac[])
  >- gvs[]
  >- (rpt strip_tac >> Cases_on `j = i` >> simp[] >> first_assum irule >> decide_tac) >>
  rpt strip_tac >> Cases_on `j = i` >> gvs[] >>
  `?z. j-i = SUC z /\ j-SUC i = z` by (qexists_tac `j - SUC i` >> decide_tac) >>
  `SUC j <> i /\ SUC i <= j` by decide_tac >>
  qpat_assum `!j. SUC i <= j /\ j < LENGTH es ==> _` (qspec_then `j` mp_tac) >> simp[]
QED

(* Apply the completed-operand judgment to a source state that already
   carries the full residual stream, without changing the input of its post. *)
Theorem blueprint_ctor_complete[local]:
  gas_completed_operand (DF,lo,explicit,ctx,func,PG)
    tops cx st0 a b source (p,s,G,tn) Q /\
  create_expr_prefix a b explicit ctx func s marks t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  source p = (rr,q) /\ valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit marks s.vs_gas_readings ++ suffix ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?G' tn'. q.gas_obs = suffix /\
    !h. valid_horizon cx st0 h q.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G',tn') /\
      Q h rr (q with gas_obs := []) G' tn' t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p with gas_obs := gas_explicit marks s.vs_gas_readings ++ suffix = p` by
    (qpat_assum `p.gas_obs = _` (once_rewrite_tac o single o SYM) >> simp[]) >>
  qhdtm_x_assum `gas_completed_operand`
    (qspecl_then [`H`,`marks`,`t`,`suffix`,`rr`,`q`] mp_tac o
     REWRITE_RULE [gas_completed_operand_def]) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem blueprint_ctor_segment_rtc[local]:
  create_expr_prefix m b explicit ctx func mid snap t ==>
  RTC (\u r. (u.vs_current_bb,u.vs_inst_idx) <>
                (b.cs_current_bb,LENGTH b.cs_current_insts) /\
       ?i ms. ctor_segment_fetch func u = SOME i /\
              m.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id /\
              gas_origin_edge F explicit ctx func u ms (OK r)) mid t
Proof
  simp[create_expr_prefix_marked] >>
  `!x y. RTC (create_marked_edge (create_prefix_step m b explicit ctx func)) x y ==>
    RTC (\u r. (u.vs_current_bb,u.vs_inst_idx) <>
                  (b.cs_current_bb,LENGTH b.cs_current_insts) /\
      ?i ms. ctor_segment_fetch func u = SOME i /\
        m.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id /\
        gas_origin_edge F explicit ctx func u ms (OK r)) (FST x) (FST y)`
    suffices_by (disch_then (qspecl_then [`(mid,[])`,`(t,snap)`] mp_tac) >> simp[]) >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[FORALL_PROD, create_marked_edge_def, create_prefix_step_def] >>
  rpt strip_tac >> irule (cj 2 RTC_RULES) >> goal_assum (drule_at Any) >>
  simp[ctor_segment_fetch_def] >>
  qexists_tac `ms` >> fs[frag_ids_def]
QED

(* The value-view post is at the expression cut, not at the private copy's
   return. Only the next row's entry uses the copy's new ghosts. *)
Theorem blueprint_ctor_vv_row:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\ create_operand_completed_ok cx e /\
  ~is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  expr_sim_full_code (ctx,shctx,func,shfunc) (a,m,sha,shm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) m = (saved,b) /\
  local_ptrs_reserved ce a /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx func s f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
     stmt_state_rel h ctx func ce cx p s /\ storage_well_formed_on cx p (FST h) /\
     ghost_inv_at (DF h) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  create_expr_prefix a m (gas_explicit_sites ctx shctx) ctx func s chunk mid /\
  mid.vs_current_bb = m.cs_current_bb /\ mid.vs_inst_idx = LENGTH m.cs_current_insts /\
  create_expr_prefix m b (gas_explicit_sites ctx shctx) ctx func mid snap t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  (exprs_can_mutate ce xs ==>
    fn_has_code m b func /\
    (?j. ctor_segment_fetch func t = SOME j /\ j.inst_opcode <> PHI /\
         b.cs_next_id <= j.inst_id) /\
    (gas_origin_path T (gas_explicit_sites ctx shctx) ctx func mid [] (OK t) ==> snap = [])) /\
  bind (eval_expr cx e) (read_result cx) p = (rr,q) /\
  valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ (snap ++ rest)) s.vs_gas_readings ++ tail ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v raw Gm tm tv ann Gt tt.
    rr = INL v /\ eval_expr cx e p = (INL raw,q) /\ read_result cx raw q = (INL v,q) /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME ann /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) /\
    value_has_type tv v /\ value_has_type ann v /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
       vv_post h ctx func ce cx e p a m s (q with gas_obs := []) raw vv mid /\
       vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
         (q with gas_obs := []) raw vv mid /\
       ptr_vv_ok cx (post_value_type ce e) raw vv (q with gas_obs := []) Gm tm mid /\
       alloca_history func mid /\ s.vs_alloca_next <= mid.vs_alloca_next /\
       ghost_inv_at (DF h) lo d ce cx (q with gas_obs := []) Gm tm mid /\
       ghost_kept_at lo ce p a G tn s Gm tm /\
       (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
         ptr_buf_ok ce e op Gm mid) /\
       (!tag p0. vv = LocatedValue tag p0 /\ p0.ptr_location = LocMemory ==>
         ptr_buf_ok ce e p0.ptr_operand Gm mid) /\
       (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
         ?val. read_result cx raw (q with gas_obs := []) = (INL val,q with gas_obs := []) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) mid = SOME w ==>
             w2n w + type_memory_size rt <= lo /\
             (!mem. mem_agree_outside tm.t_mem mid.vs_memory mem ==>
                val_in_memory rt val (w2n w) mem))) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    expr_sim_inv ce cx env q /\ return_buf_frame d ce b t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_no_wrap i z) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx func ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q Gt tt t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG:(num # num) option list,func,shfunc)
     ce cx (expr_type e) e p (st0,a,m,sha,shm,vv,s,G,tn)` by
    (fs[expr_vv_sim_full_pre_def, expr_sim_full_code_def] >>
     metis_tac[expr_body_pre_vv_gas_admissible]) >>
  drule_all create_size_replay_vv_cut >> strip_tac >>
  Cases_on `eval_expr cx e p` >>
  qmatch_asmsub_rename_tac `eval_expr cx e p = (rv,rq)` >>
  `rq = q` by (Cases_on `rv` >> fs[bind_def] >> metis_tac[read_result_state]) >>
  qpat_x_assum `rq = q` SUBST_ALL_TAC >>
  `p.gas_obs = gas_explicit chunk s.vs_gas_readings ++
     (gas_explicit (snap ++ rest) mid.vs_gas_readings ++ tail)` by
    (qpat_assum `create_expr_prefix a m _ _ _ s chunk mid`
       (assume_tac o MATCH_MP create_prefix_readings) >>
     qpat_assum `p.gas_obs = gas_explicit (chunk ++ (snap ++ rest)) _ ++ _`
       (pure_once_rewrite_tac o single) >>
     CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV gas_explicit_append))) >>
     simp[APPEND_ASSOC]) >>
  drule_all blueprint_ctor_complete >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> fs[bind_def]) >>
  suspend "read"
QED

Resume blueprint_ctor_vv_row[read]:
  qpat_x_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (assume_tac o BETA_RULE) >>
  qpat_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `rv = INL _` SUBST_ALL_TAC >>
  rename1 `eval_expr cx e p = (INL raw,q)` >>
  drule abi_args_vv_post_read >> strip_tac >>
  `read_result cx raw q = (INL v,q)` by
    (drule read_result_gas_obs >> disch_then (qspec_then `q.gas_obs` mp_tac) >>
     simp[IgnAsm `q.gas_obs = _`]) >>
  `rr = INL v` by fs[bind_def] >>
  qpat_x_assum `rr = INL v` SUBST_ALL_TAC >>
  disj2_tac >> qexistsl [`v`,`raw`,`G'`,`tn'`] >> simp[] >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (expr_type e)` by metis_tac[arg_type_fits_word_type] >>
  drule_all (REWRITE_RULE [ETA_AX] abi_args_success_ready) >> simp[] >> strip_tac >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv` >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME ann` >>
  qexistsl [`tv`,`ann`] >> simp[] >>
  suspend "advance"
QED
Resume blueprint_ctor_vv_row[advance]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (fs[expr_sim_full_code_def] >> metis_tac[body_inv_no_phi]) >>
  `!f i z. frag_reachable ctx func mid f i z ==> dalloca_no_wrap i z` by
    (drule gas_origin_ptr_path_dalloca_no_wrap >> simp[] >> metis_tac[]) >>
  `~mid.vs_halted` by (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  Cases_on `exprs_can_mutate ce xs`
  >- suspend "copy" >>
  suspend "retain"
QED
Resume blueprint_ctor_vv_row[retain]:
  `vv_type (ext_call_arg_value (lowered_value_type ce e) vv) = lowered_value_type ce e`
     by metis_tac[extcall_operand_snapshot_type] >>
  `b = m` by
    (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     simp[compile_snapshot_vv_def,comp_return_def]) >>
  qpat_x_assum `b = m` SUBST_ALL_TAC >>
  drule_all create_copy_empty_cut >> strip_tac >>
  `a.cs_next_var <= m.cs_next_var` by
    metis_tac[ci_mono_compile_expr_sa,SND,ci_mono_def] >>
  `return_buf_frame d ce m mid` by
    (irule return_buf_frame_frame >>
     qexistsl [`ce`,`s`,`a`] >> fs[vv_post_def]) >>
  qexistsl [`G'`,`tn'`] >> gvs[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `h` >> disch_tac >>
  qpat_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `h` (drule_then strip_assume_tac)) >>
  fs[vv_post_def] >> conj_tac
  >- (irule (iffLR storage_well_formed_on_backends) >>
      qexists_tac `q with gas_obs := []` >> simp[]) >>
  qpat_x_assum `ghost_inv_at (DF h) _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [ghost_inv_at_def,ghost_inv_def,local_region_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED
Resume blueprint_ctor_vv_row[copy]:
  qpat_x_assum `exprs_can_mutate ce xs ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `create_expr_prefix m b _ _ _ mid snap t`
    (assume_tac o MATCH_MP blueprint_ctor_segment_rtc) >>
  `storage_trace_domain cx st0 q.storage_trace` by
    (qpat_x_assum `valid_horizon cx st0 H q.storage_trace` mp_tac >>
     simp[valid_horizon_def, storage_trace_domain_def, storage_trace_horizon_def,
          storage_observations_ok_def, EVERY_MEM, regions_consistent_def,
          storage_locks_separated_def, storage_well_formed_on_def] >>
     strip_tac >> rpt conj_tac >> TRY (metis_tac[] >> NO_TAC) >>
     qpat_x_assum `storage_trace_backends_well_formed _ _ _` mp_tac >>
     simp[storage_trace_backends_well_formed_def, EVERY_MEM] >>
     rpt strip_tac >> first_x_assum drule >> Cases_on `observation` >>
     simp[storage_well_formed_on_def] >> metis_tac[]) >>
  `!h. valid_horizon cx st0 h q.storage_trace ==>
    vv_post h ctx func ce cx e p a m s q raw vv mid /\
    ghost_inv_at (DF h) lo d ce cx q G' tn' mid` by
    (rpt strip_tac >>
     qpat_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
     gvs[vv_post_final_gas,ghost_inv_at_def,ghost_inv_def,local_region_def] >>
     first_assum ACCEPT_TAC) >>
  `vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) q raw vv mid /\
   ptr_vv_ok cx (post_value_type ce e) raw vv q G' tn' mid` by
    (qpat_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >> Cases_on `vv` >>
     simp_tac (srw_ss()) [vv_store_bound_def, ptr_vv_ok_def, read_result_success_gas_iff] >>
     disch_then strip_assume_tac >> disch_then strip_assume_tac >>
     simp[]) >>
  `~is_word_type (post_value_type ce e)` by metis_tac[post_value_type_nonword] >>
  `!tag op. vv = StackValue tag op ==> ptr_buf_ok ce e op G' mid` by simp[] >>
  `compile_snapshot_vv ce T (ext_call_arg_value (lowered_value_type ce e) vv) m = (saved,b)` by fs[] >>
  `eval_expr cx e (p with gas_obs := p.gas_obs) = (INL raw,q)` by
    simp[IgnAsm `p.gas_obs = _`] >>
  `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx raw q = (INL val,q) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
         eval_operand (vv_operand vv) mid = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tn'.t_mem mid.vs_memory mem ==>
                val_in_memory rt val (w2n w) mem)` by fs[read_result_success_gas_iff] >>
  `fn_inst_ids_distinct func` by fs[expr_sim_full_code_def] >>
  drule_all (INST_TYPE [alpha |-> ``:exception``] ctor_private_snapshot_actual) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  suspend "copied_entry"
QED
Resume blueprint_ctor_vv_row[copied_entry]:
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (mid,G',tn') [] (OK t,Gout,tout)` >>
  qpat_assum `!h. _ ==> gas_origin_ptr_path _ (mid,_,_) [] _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `snap = []` by
    (qpat_assum `gas_origin_ptr_path _ (mid,_,_) [] _`
       (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     first_assum (drule_then ACCEPT_TAC)) >>
  `mid.vs_gas_readings = t.vs_gas_readings` by
    (qpat_assum `create_expr_prefix m b _ _ _ mid snap t`
       (mp_tac o MATCH_MP create_prefix_readings) >> simp[]) >>
  `!f i z. frag_reachable ctx func t f i z ==> dalloca_no_wrap i z` by
    (qpat_assum `gas_origin_ptr_path _ (mid,_,_) [] _` mp_tac >>
     qpat_assum `!f i z. frag_reachable ctx func mid f i z ==> _` mp_tac >>
     qpat_assum `!bb. MEM bb func.fn_blocks ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[gas_origin_ptr_path_dalloca_no_wrap]) >>
  `!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx func ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q Gout tout t /\ return_buf_frame d ce b t /\
      alloca_history func t /\ ~t.vs_halted` by
    (qx_gen_tac `h` >> disch_tac >>
     qpat_assum `!h. _ ==> gas_origin_ptr_path _ (mid,_,_) [] _ /\ _`
       (qspec_then `h` (drule_then strip_assume_tac)) >>
     qpat_x_assum `!kw. extcall_positional_post T _ _ _ _ _ _ _ _ kw [e] _ _ _ _ _ _ _ h _ q _ _ t`
       (qspec_then `[]` (strip_assume_tac o SIMP_RULE (srw_ss())
          [extcall_positional_post_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!h. _ ==> stmt_state_rel h _ _ _ _ _ t /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  qexistsl [`Gout`,`tout`] >> simp[] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!h. _ ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
        (drule_then strip_assume_tac) >> gvs[]) >>
  first_assum ACCEPT_TAC
QED
Finalise blueprint_ctor_vv_row

(* Forget the mark accumulator, keeping the same target execution. *)
Theorem raw_prefix_origin_rtc[local]:
  create_expr_prefix a b explicit ctx fn u marks v ==>
    RTC (\p q. ?ms. gas_origin_edge F explicit ctx fn p ms (OK q)) u v
Proof
  simp[create_expr_prefix_marked] >>
  `!x y. RTC (create_marked_edge (create_prefix_step a b explicit ctx fn)) x y ==>
    RTC (\p q. ?ms. gas_origin_edge F explicit ctx fn p ms (OK q)) (FST x) (FST y)`
    suffices_by (disch_then (qspecl_then [`(u,[])`,`(v,marks)`] mp_tac) >> simp[]) >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[FORALL_PROD, create_marked_edge_def, create_prefix_step_def] >>
  rpt strip_tac >> irule (cj 2 RTC_RULES) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem raw_prefix_gas_path[local]:
  create_expr_prefix a b explicit ctx fn u marks v /\ ~u.vs_halted ==>
  gas_path ctx fn u (LENGTH marks) (OK v)
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  drule blueprint_prefix_gas_path >> simp[]
QED

Theorem create_raw_data_entry_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es /\
  EVERY (create_operand_completed_ok cx) (create_operand_order RawCreate hs (e::v::rest)) /\
  expr_vv_sim_full_pre (DF,lo,dep,ctx,shadow_ctx,PG : (num # num) option list,func,shadow_func)
    ce cx ty (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es
    (st0,sa,sb,shadow_sa,shadow_sb,parent_vv,s0,G0,tn0) /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_a) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,a,shadow_sa,shadow_a) /\
  compile_create_snapshot ce vv (lowered_value_type ce e) a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ emit_op ADD [snap; Lit 32w] c = (data,d) /\
  fn_has_code a d func /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts /\
  l.vs_current_bb = c.cs_current_bb /\ l.vs_inst_idx = LENGTH c.cs_current_insts /\
  r.vs_current_bb = d.cs_current_bb /\ r.vs_inst_idx = LENGTH d.cs_current_insts /\
  create_expr_prefix sa a (gas_explicit_sites ctx shadow_ctx) ctx func s0 ms u /\
  create_expr_prefix a b (gas_explicit_sites ctx shadow_ctx) ctx func u msS z /\
  create_expr_prefix b c (gas_explicit_sites ctx shadow_ctx) ctx func z msL l /\
  create_expr_prefix c d (gas_explicit_sites ctx shadow_ctx) ctx func l msD r /\
  eval_expr cx (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df)
    (es with gas_obs := gas_explicit (ms ++ (msS ++ msL ++ msD ++ later)) s0.vs_gas_readings ++ tail) = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?p tv code Gr tnr lenvar datavar.
    eval_expr cx e (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL tv,p) /\
    p.gas_obs = gas_explicit later r.vs_gas_readings ++ tail /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
    bind (eval_exprs cx ((if hs then FRONT rest else rest) ++
                       v :: (if hs then [LAST rest] else [])))
      (\vs. eval_create_operands cx RawCreate hs rof (MAP expr_type (e::v::rest))
        (blueprint_literal_offset cx hs (e::v::rest)) (BytesV code::vs)) p = (res,ee) /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv ce cx env p /\
    eval_operand len l = SOME (n2w (LENGTH code)) /\
    w2n (n2w (LENGTH code) : bytes32) <= bytelike_type_bound (lowered_value_type ce e) /\
    msS = [] /\ msL = [] /\ msD = [] /\
    len = Var lenvar /\ data = Var datavar /\
    return_buf_frame dep ce d r /\ alloca_history func r /\ ~r.vs_halted /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\
    r.vs_current_bb = d.cs_current_bb /\ r.vs_inst_idx = LENGTH d.cs_current_insts /\
    local_ptrs_reserved ce d /\
    (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at d x) /\
    (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at d x) /\
    (!fn i s. frag_reachable ctx func r fn i s ==> dalloca_no_wrap i s) /\
    (!h. valid_horizon cx st0 h p.storage_trace ==>
       stmt_state_rel h ctx func ce cx p r /\
       storage_well_formed_on cx p (FST h) /\
       ghost_inv_at (DF h) lo dep ce cx p Gr tnr r) /\
    FLOOKUP r.vs_allocas a.cs_next_id =
      SOME (buffer_allocation_base u a.cs_next_id,type_memory_bytes ce (lowered_value_type ce e)) /\
    lookup_var lenvar r = SOME (n2w (LENGTH code)) /\
    lookup_var datavar r = SOME (n2w (buffer_allocation_base u a.cs_next_id + 32)) /\
    not_fresh_at d lenvar /\ not_fresh_at d datavar /\
    op_taint tnr (Var lenvar) = {} /\ ptr_covers Gr tnr datavar r (LENGTH code) /\
    w2n (n2w (buffer_allocation_base u a.cs_next_id + 32) : bytes32) + LENGTH code <= r.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL create_raw_bytecode_header_at_cuts) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac
  >- (disj1_tac >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  qpat_assum `!h. valid_horizon _ _ h p.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `ci_mono sa a` by metis_tac[ci_mono_compile_expr_sa, SND] >>
  `sa.cs_next_var <= a.cs_next_var` by fs[ci_mono_def] >>
  `!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx func ce cx (p with gas_obs := []) u /\
      storage_well_formed_on cx (p with gas_obs := []) (FST h) /\
      ghost_inv_at (DF h) lo dep ce cx (p with gas_obs := []) G tn u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h p.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_def])) >> simp[]) >>
  `return_buf_frame dep ce a u` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame dep ce sa s0` (irule_at Any) >>
     fs[vv_post_def]) >>
  `~u.vs_halted` by
    (drule bodyFullIfExpReachTheory.gas_origin_ptr_path_erase >>
     disch_then (mp_tac o MATCH_MP gas_path_normal) >> simp[]) >>
  `(!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
   (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x)` by
     metis_tac[not_fresh_at_mono] >>
  `RTC (\x t. ?ms. gas_origin_edge F (gas_explicit_sites ctx shadow_ctx) ctx func x ms (OK t)) u r` by
    (imp_res_tac raw_prefix_origin_rtc >> metis_tac[RTC_TRANS]) >>
  mp_tac (Q.INST [`k` |-> `n`, `ac` |-> `d`, `len_op` |-> `len`, `data_op` |-> `data`,
                  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
                  `obs` |-> `gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail`]
           (Q.INST [`d` |-> `dep`] create_raw_snapshot_payload_entry)) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     gen_tac >> disch_tac >>
     qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _`
       (drule_then strip_assume_tac) >>
     qexistsl [`buf`,`sm`,`x`,`exit`] >> asm_rewrite_tac[])) >> strip_tac >>
  suspend "entry"
QED
Resume create_raw_data_entry_at_cuts[entry]:
  `ci_mono a d` by
    metis_tac[ci_mono_trans, ci_mono_compile_create_snapshot, ci_mono_emit_op, SND] >>
  `a.cs_next_var <= d.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved ce d` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at d x) /\
   (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at d x)` by
    metis_tac[not_fresh_at_mono] >>
  `?nm. gas_path ctx func s0 nm (OK r)` by
    (`gas_path ctx func s0 (LENGTH ms) (OK u)` by
       metis_tac[bodyFullIfExpReachTheory.gas_origin_ptr_path_erase] >>
     `gas_path ctx func u (LENGTH msS) (OK z)` by metis_tac[raw_prefix_gas_path] >>
     `~z.vs_halted` by metis_tac[gas_path_normal] >>
     `gas_path ctx func z (LENGTH msL) (OK l)` by metis_tac[raw_prefix_gas_path] >>
     `~l.vs_halted` by metis_tac[gas_path_normal] >>
     `gas_path ctx func l (LENGTH msD) (OK r)` by metis_tac[raw_prefix_gas_path] >>
     qexists_tac `LENGTH ms + (LENGTH msS + (LENGTH msL + LENGTH msD))` >>
     irule gas_path_then >> qexists_tac `u` >> conj_tac >- first_assum ACCEPT_TAC >>
     irule gas_path_then >> qexists_tac `z` >> conj_tac >- first_assum ACCEPT_TAC >>
     irule gas_path_then >> qexists_tac `l` >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!i. active_inst func i r ==> frag_reachable ctx func s0 func i r` by
    (drule gas_path_reach >> disch_then (qspecl_then [`func`,`s0`,`r`] mp_tac) >>
     simp[contextRawReachableTheory.frag_reachable_start]) >>
  `!fn i s. frag_reachable ctx func r fn i s ==> dalloca_no_wrap i s` by
    metis_tac[contextRawReachableTheory.frag_reachable_trans] >>
  suspend "source"
QED
Resume create_raw_data_entry_at_cuts[source]:
  `w2n (n2w (LENGTH code) : bytes32) <= bytelike_type_bound (lowered_value_type ce e)` by
    (`expr_body_pre ce cx env e
         (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail)` by
       simp[expr_body_pre_gas_obs] >>
     `bind (eval_expr cx e) (read_result cx)
         (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL (BytesV code),p)` by
       simp[bind_def] >>
     drule_all create_blueprint_raw_copy_layout >> strip_tac >>
     `LENGTH code <= bytelike_type_bound (lowered_value_type ce e)` by
       fs[value_has_type_def, bytelike_type_bound_def, bound_length_def] >>
     `w2n (n2w (LENGTH code) : bytes32) <= LENGTH code` by
       simp[w2n_n2w, MOD_LESS_EQ, ZERO_LT_dimword] >> decide_tac) >>
  `hs ==> rest <> []` by
    (qpat_assum `expr_body_pre ce cx env (Call _ _ _ _) es`
       (strip_assume_tac o MATCH_MP (GEN_ALL exprBodyPrePropsTheory.expr_body_pre_static_facts)) >>
     drule create_raw_first_type >> simp[]) >>
  `TAKE (LENGTH rest - (if hs then 1 else 0)) rest ++
      v :: DROP (LENGTH rest - (if hs then 1 else 0)) rest =
    (if hs then FRONT rest else rest) ++ v :: (if hs then [LAST rest] else [])` by
    (reverse (Cases_on `hs`) >- simp[] >>
     `rest <> []` by fs[] >>
     `0 < LENGTH rest` by (Cases_on `rest` >> fs[]) >>
     simp[FRONT_BY_TAKE, DROP_PREn_LAST_CONS]) >>
  pop_assum (fn eq => qpat_x_assum `bind (eval_exprs cx _) _ p = (res,ee)`
    (assume_tac o PURE_REWRITE_RULE [eq])) >>
  disj2_tac >>
  rename1 `lookup_var datavar r = SOME (n2w (buffer_allocation_base u a.cs_next_id + 32))` >>
  rename1 `lookup_var lenvar r = SOME (n2w (LENGTH code))` >>
  qexistsl [`p`,`tv`,`code`,`Gr`,`tnr`,`lenvar`,`datavar`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h p.storage_trace ==> stmt_state_rel _ _ _ _ _ _ r /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >- fs[stmt_state_rel_gas_obs] >> conj_tac
  >- (irule (iffLR storage_well_formed_on_backends) >>
      qexists_tac `p with gas_obs := []` >> simp[]) >>
  qpat_assum `ghost_inv_at (DF h) _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  simp[ghost_inv_at_def] >> strip_tac >> first_assum ACCEPT_TAC
QED
Finalise create_raw_data_entry_at_cuts

(* A word constructor completes at the snapshot cut, which includes its
   unwrap. Keep the full scalar post for the payload-length proof. *)
Theorem blueprint_ctor_word_row:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\ create_operand_completed_ok cx e /\
  is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) m = (sv,b) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  compile_snapshot_vv ce shcopy (ext_call_arg_value (lowered_value_type ce e) vv) shm = (sv,shb) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (a,b,sha,shb) /\
  local_ptrs_reserved ce a /\ (!K. dead_lo_ok K (DF K) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history fnc s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx fnc s f i z ==> dalloca_no_wrap i z) /\
  (!K. valid_horizon cx st0 K p.storage_trace ==>
    stmt_state_rel K ctx fnc ce cx p s /\ storage_well_formed_on cx p (FST K) /\
    ghost_inv_at (DF K) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  create_expr_prefix a b (gas_explicit_sites ctx shctx) ctx fnc s chunk t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  bind (eval_expr cx e) (read_result cx) p = (rr,q) /\
  valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) s.vs_gas_readings ++ tail ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v G' tn'. rr = INL v /\ q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    (!K op. valid_horizon cx st0 K q.storage_trace /\
      lower_value compile_expr ce (expr_type e) e a = (op,b) ==>
      expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx e (p,a,b,s,op,G,tn)
        K (INL v : value + exception) (q with gas_obs := []) G' tn' t) /\
    expr_sim_inv ce cx env q /\
    (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME ann /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) /\
      value_has_type tv v /\ value_has_type ann v) /\
    return_buf_frame d ce b t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_no_wrap i z) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!K. valid_horizon cx st0 K q.storage_trace ==>
      stmt_state_rel K ctx fnc ce cx q t /\ storage_well_formed_on cx q (FST K) /\
      ghost_inv_at (DF K) lo d ce cx q G' tn' t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_snapshot_word_lower_value >> strip_tac >>
  drule expr_body_pre_lowered_fits >> strip_tac >>
  `is_word_type (expr_type e) /\ lowered_value_type ce e = expr_type e` by
    metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type,
              abiEncodeArgsSimTheory.abi_args_word_fits_eq] >>
  `lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) sha = (op,shb)` by
    (suspend "shadow") >>
  `gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
     tops cx st0 a b (bind (eval_expr cx e) (read_result cx)) (p,s,G,tn)
     (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx e (p,a,b,s,op,G,tn))` by
    (irule create_size_replay_value_cut >> simp[] >>
     conj_tac >- (qexists_tac `env` >> simp[]) >>
     qexistsl [`shfnc`, `sha`, `shb`, `expr_type e`] >>
     fs[expr_sim_full_pre_def, expr_sim_full_code_def] >>
     conj_tac >- (drule expr_body_pre_gas_admissible >> simp[]) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!f i z. frag_reachable _ _ _ f i z ==> _` drule >> simp[]) >>
  `gas_path ctx fnc s (LENGTH chunk) (OK t)` by
    (qpat_assum `create_expr_prefix a b _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE[create_expr_prefix_marked]) >>
     disch_then (mp_tac o MATCH_MP blueprint_prefix_gas_path) >> simp[]) >>
  `p.gas_obs = gas_explicit chunk s.vs_gas_readings ++
               (gas_explicit rest t.vs_gas_readings ++ tail)` by
    (drule gas_explicit_append_path >> simp[APPEND_ASSOC]) >>
  drule_all blueprint_ctor_complete >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  disj2_tac >> suspend "finish"
QED

Resume blueprint_ctor_word_row[shadow]:
  `reason_uniform_shape compile_expr ce (expr_type e) e` by
    (irule exprReasonOperandTheory.compile_expr_reason_uniform >> qexists_tac `env` >>
     drule expr_body_pre_static_facts >> simp[expr_sim_inv_def]) >>
  `vv_type vv = expr_type e` by
    (fs[exprReasonOperandTheory.reason_uniform_shape_def] >> first_x_assum drule >>
     Cases_on `vv` >> gvs[exprReasonOperandTheory.reason_result_shape_def, vv_type_def]) >>
  `ext_call_arg_value (lowered_value_type ce e) vv = vv` by
    (Cases_on `vv` >> gvs[ext_call_arg_value_def, vv_type_def]) >>
  Cases_on `unwrap_value ce vv shm` >>
  gvs[lower_value_def, compile_snapshot_vv_def, comp_bind_def, comp_return_def]
QED

Resume blueprint_ctor_word_row[finish]:
  pop_assum (mk_asm "replay") >>
  asm "replay" (qspec_then `H` mp_tac) >> (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [expr_sim_full_post_def, expr_sim_full_endpoint_def, expr_post_def])) >>
  qexistsl_tac [`v`,`G'`,`tn'`] >> simp[] >>
  `expr_sim_inv ce cx env q /\ value_runtime_typed env (expr_type e) v` by
    (drule_all (REWRITE_RULE [ETA_AX] bodySimStmtFactsTheory.expr_body_pre_eval) >> simp[]) >>
  `env.type_defs = get_tenv cx` by metis_tac[expr_body_pre_env_type_defs] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    fs[value_runtime_typed_def] >>
  `a.cs_next_var <= b.cs_next_var` by
    (qspecl_then [`ce`,`expr_type e`,`e`,`a`] mp_tac ci_mono_lower_value_compile_expr >>
     simp[ci_mono_def]) >>
  `return_buf_frame d ce b t` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s`,`a`] >> simp[]) >>
  `MEM fnc ctx.ctx_functions` by fs[expr_sim_full_code_def] >>
  `!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
    by metis_tac[body_inv_no_phi] >>
  `!f i z. frag_reachable ctx fnc t f i z ==> dalloca_no_wrap i z` by
    (drule gas_origin_ptr_path_dalloca_no_wrap >> simp[] >> metis_tac[]) >>
  `~t.vs_halted` by (drule gas_path_normal >> simp[]) >>
  simp[] >> conj_tac
  >- (qx_gen_tac `hor` >> strip_tac >> asm "replay" (qspec_then `hor` mp_tac) >>
      (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
      qpat_assum `rr = INL v` (fn th => disch_then (ACCEPT_TAC o REWRITE_RULE [th] o CONJUNCT2))) >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  qx_gen_tac `hor` >> disch_tac >>
  asm "replay" (qspec_then `hor` mp_tac) >> (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def, expr_post_def]) >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >> conj_tac
  >- (irule (iffLR storage_well_formed_on_backends) >>
      qexists_tac `q with gas_obs := []` >> simp[]) >>
  qpat_assum `ghost_inv_at (DF hor) _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [ghost_inv_at_def]) >>
  simp[ghost_inv_at_def] >> FIRST_ASSUM ACCEPT_TAC
QED

Finalise blueprint_ctor_word_row

Theorem raw_observed_prefix_cases[local]:
  create_expr_prefix a b explicit ctx fn s ms t ==>
  (t = s /\ ms = []) \/
  ?u left. create_prefix_step a b explicit ctx fn s left u /\
    RTC (create_marked_edge (create_prefix_step a b explicit ctx fn)) (u,left) (t,ms)
Proof
  simp[create_expr_prefix_marked] >>
  disch_then (mp_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >>
  simp[EXISTS_PROD,create_marked_edge_def] >> metis_tac[]
QED

Theorem raw_observed_prefix_fetch[local]:
  create_expr_prefix a b explicit ctx fn s ms t /\
  a.cs_next_id <= b.cs_next_id /\
  ctor_segment_fetch fn t = SOME j /\ j.inst_opcode <> PHI /\ b.cs_next_id <= j.inst_id ==>
  ?i. ctor_segment_fetch fn s = SOME i /\ i.inst_opcode <> PHI /\ a.cs_next_id <= i.inst_id
Proof
  strip_tac >> drule raw_observed_prefix_cases >> strip_tac
  >- (qexists_tac `j` >> fs[] >> decide_tac) >>
  qpat_x_assum `create_prefix_step _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[create_prefix_step_def]) >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
  simp[gas_origin_edge_def,exit_result_def] >> strip_tac >> gvs[] >>
  fs[ctor_segment_fetch_def,frag_ids_def] >> metis_tac[step_inst_ok_imp_not_phi]
QED

Theorem raw_observed_prefix_live[local]:
  create_expr_prefix a b explicit ctx fn s ms t /\ ~s.vs_halted ==> ~t.vs_halted
Proof
  simp[create_expr_prefix_marked] >>
  `!x y. RTC (create_marked_edge (create_prefix_step a b explicit ctx fn)) x y ==>
    ~(FST x).vs_halted ==> ~(FST y).vs_halted` suffices_by
    (disch_then (qspecl_then [`(s,[])`,`(t,ms)`] mp_tac) >> simp[]) >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def,PULL_EXISTS] >>
  rpt strip_tac >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [gas_origin_edge_def]) >>
  gvs[jump_to_def,exit_result_def] >>
  qpat_x_assum `OK _ = step_inst _ _ _ _` (fs o single o SYM) >>
  fs[exit_result_def]
QED

Theorem raw_observed_prefix_join[local]:
  create_expr_prefix a b explicit ctx fn s left u /\
  create_expr_prefix b c explicit ctx fn u right t /\
  a.cs_next_id <= b.cs_next_id /\ b.cs_next_id <= c.cs_next_id /\
  t.vs_current_bb = c.cs_current_bb /\ t.vs_inst_idx = LENGTH c.cs_current_insts /\
  ctor_segment_fetch fn t = SOME i /\ c.cs_next_id <= i.inst_id ==>
  create_expr_prefix a c explicit ctx fn s (left ++ right) t
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  `!x y. create_marked_edge (create_prefix_step a b explicit ctx fn) x y ==>
         create_marked_edge (create_prefix_step a c explicit ctx fn) x y` by
    (simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def,frag_ids_def,PULL_EXISTS] >>
     rpt gen_tac >> strip_tac >> TRY (goal_assum (drule_at Any)) >>
     TRY (first_assum ACCEPT_TAC) >> TRY (decide_tac) >>
     rpt strip_tac >> gvs[ctor_segment_fetch_def] >> decide_tac) >>
  `RTC (create_marked_edge (create_prefix_step a c explicit ctx fn)) (s,[]) (u,left)` by
    metis_tac[RTC_MONOTONE] >>
  `!x y. create_marked_edge (create_prefix_step b c explicit ctx fn) x y ==>
         create_marked_edge (create_prefix_step a c explicit ctx fn) x y` by
    (simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def,frag_ids_def,PULL_EXISTS] >>
     metis_tac[LESS_EQ_TRANS]) >>
  qpat_assum `RTC (create_marked_edge (create_prefix_step b c _ _ _)) _ _`
    (mp_tac o MATCH_MP create_marked_rtc_rebase) >>
  disch_then (qspec_then `left` mp_tac) >> simp[] >> strip_tac >>
  `RTC (create_marked_edge (create_prefix_step a c explicit ctx fn)) (u,left) (t,left ++ right)` by
    metis_tac[RTC_MONOTONE] >> metis_tac[RTC_TRANS]
QED

Theorem raw_observed_prefix_single[local]:
  fn_has_code a b fn /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ [i] /\ ~is_terminator i.inst_opcode /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  create_expr_prefix a b explicit ctx fn s ms t ==>
  gas_origin_edge F explicit ctx fn s ms (OK t)
Proof
  strip_tac >>
  `s <> t` by (strip_tac >> gvs[]) >>
  drule raw_observed_prefix_cases >> strip_tac >- fs[] >>
  qpat_x_assum `create_prefix_step a b _ _ _ s _ _`
    (strip_assume_tac o REWRITE_RULE[create_prefix_step_def]) >>
  drule_all fn_has_code_same_block >> strip_tac >> gvs[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ get_instruction bb s.vs_inst_idx = SOME i` by simp[] >>
  drule_all create_ok_edge_pc >> strip_tac >> gvs[] >>
  qpat_x_assum `RTC _ _ _` (mp_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
  simp[EXISTS_PROD,create_marked_edge_def,create_prefix_step_def] >> metis_tac[]
QED

(* Following any number of empty bands does not lose the next actual fetch. *)

Theorem raw_observed_index_fetch[local]:
  !n k.
    (!i. k <= i /\ i < k+n ==>
      (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
      create_expr_prefix (C i) (C (SUC i)) explicit ctx fn (St i) (M i) (St (SUC i))) /\
    ctor_segment_fetch fn (St (k+n)) = SOME j /\ j.inst_opcode <> PHI /\
    (C (k+n)).cs_next_id <= j.inst_id ==>
  ?x. ctor_segment_fetch fn (St k) = SOME x /\ x.inst_opcode <> PHI /\
      (C k).cs_next_id <= x.inst_id
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `k + SUC n = SUC k + n` by decide_tac >>
  `?x. ctor_segment_fetch fn (St (SUC k)) = SOME x /\ x.inst_opcode <> PHI /\
     (C (SUC k)).cs_next_id <= x.inst_id` by
    (first_x_assum irule >>
     qpat_assum `k + SUC n = SUC k + n` (pure_rewrite_tac o single o SYM) >>
     asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
     first_assum irule >> decide_tac) >>
  `k <= k /\ k < k+SUC n` by decide_tac >>
  qpat_x_assum `!i. k <= i /\ i < k+SUC n ==> _`
    (qspec_then `k` mp_tac) >> asm_rewrite_tac[] >> strip_tac >>
  drule_all raw_observed_prefix_fetch >> simp[]
QED

Theorem raw_observed_index_live[local]:
  !i. i <= n /\ ~ (St 0).vs_halted /\
    (!j. j < n ==> create_expr_prefix (C j) (C (SUC j)) explicit ctx fn
                    (St j) (M j) (St (SUC j))) ==>
    ~(St i).vs_halted
Proof
  Induct >> simp[] >> strip_tac >>
  `i <= n /\ i < n` by decide_tac >>
  metis_tac[raw_observed_prefix_live]
QED

Theorem raw_observed_pairs[local]:
  !n f g.
    LENGTH (FLAT (GENLIST (\i. [f i; g i]) n)) = 2*n /\
    (!i. i < n ==>
       EL (2*i) (FLAT (GENLIST (\i. [f i; g i]) n)) = f i /\
       EL (SUC (2*i)) (FLAT (GENLIST (\i. [f i; g i]) n)) = g i)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> first_x_assum (qspecl_then [`f o SUC`,`g o SUC`] mp_tac) >>
  simp[GENLIST_CONS,combinTheory.o_DEF,ADD_CLAUSES] >>
  strip_tac >> Cases >- simp[] >>
  `!j. 2 * SUC j = SUC (SUC (2*j))` by (simp[MULT_CLAUSES] >> decide_tac) >>
  rewrite_tac[LESS_MONO_EQ] >> strip_tac >>
  qpat_assum `!i. i < n ==> _` (drule_then strip_assume_tac) >>
  asm_simp_tac bool_ss [EL,HD,TL] >>
  qpat_assum `EL (SUC (2 * _)) _ = _` (mp_tac o REWRITE_RULE [EL]) >> simp[]
QED

Theorem raw_observed_prefix_emit[local]:
  emit_op opc ops a = (out,b) /\ ~is_terminator opc /\ fn_has_code a b fn /\
  (s.vs_current_bb,s.vs_inst_idx) = (a.cs_current_bb,LENGTH a.cs_current_insts) /\
  (t.vs_current_bb,t.vs_inst_idx) = (b.cs_current_bb,LENGTH b.cs_current_insts) /\
  create_expr_prefix a b explicit ctx fn s ms t ==>
  gas_origin_edge F explicit ctx fn s ms (OK t)
Proof
  strip_tac >> drule exprLoweringPropsTheory.emit_op_extends >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  irule raw_observed_prefix_single >>
  qexistsl_tac [`a`,`b`,`mk_inst a.cs_next_id opc ops [STRING #"%" (toString a.cs_next_var)]`] >>
  gvs[mk_inst_def,exprLoweringPropsTheory.same_blocks_def]
QED

Theorem raw_observed_prefix_copy[local]:
  compile_copy_memory_dynamic dst data len a = ((),b) /\ fn_has_code a b fn /\
  (s.vs_current_bb,s.vs_inst_idx) = (a.cs_current_bb,LENGTH a.cs_current_insts) /\
  (t.vs_current_bb,t.vs_inst_idx) = (b.cs_current_bb,LENGTH b.cs_current_insts) /\
  create_expr_prefix a b explicit ctx fn s ms t ==>
  gas_origin_edge F explicit ctx fn s ms (OK t)
Proof
  simp[contextTheory.compile_copy_memory_dynamic_def] >> strip_tac >>
  drule exprLoweringPropsTheory.emit_void_extends >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  irule raw_observed_prefix_single >>
  qexistsl_tac [`a`,`b`,`mk_inst a.cs_next_id MCOPY [dst;data;len] []`] >>
  gvs[mk_inst_def,is_terminator_def,exprLoweringPropsTheory.same_blocks_def]
QED

Theorem raw_observed_prefix_alloc[local]:
  compile_alloc_buffer cap a = (buf,b) /\ fn_has_code a b fn /\
  (s.vs_current_bb,s.vs_inst_idx) = (a.cs_current_bb,LENGTH a.cs_current_insts) /\
  (t.vs_current_bb,t.vs_inst_idx) = (b.cs_current_bb,LENGTH b.cs_current_insts) /\
  create_expr_prefix a b explicit ctx fn s ms t ==>
  gas_origin_edge F explicit ctx fn s ms (OK t)
Proof
  strip_tac >> drule compile_alloc_buffer_code >> strip_tac >>
  irule raw_observed_prefix_single >>
  qexistsl_tac [`a`,`b`,
    `mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [STRING #"%" (toString a.cs_next_var)]`] >>
  gvs[mk_inst_def,is_terminator_def]
QED

(* Convert the cut list once, and compute the first remaining fetch at every
   boundary. The latter justifies widening a two-band constructor row. *)

Theorem raw_observed_spine[local]:
  C = (\i. EL i code) /\ Obs = (\i. EL i states) /\ M = (\i. EL i chunks0) /\
  LENGTH code = SUC n /\ LENGTH chunks0 = n /\
  LIST_REL (\c s. s.vs_current_bb = c.cs_current_bb /\
                  s.vs_inst_idx = LENGTH c.cs_current_insts) code states /\
  ~ (Obs 0).vs_halted /\ ctor_segment_fetch fn (Obs n) = SOME dispatch /\
  dispatch.inst_opcode <> PHI /\ (C n).cs_next_id <= dispatch.inst_id /\
  (!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
      create_expr_prefix (C i) (C (SUC i)) explicit ctx fn (Obs i) (M i) (Obs (SUC i))) ==>
  (!i. i <= n ==> ~ (Obs i).vs_halted /\
    ((Obs i).vs_current_bb,(Obs i).vs_inst_idx) =
      ((C i).cs_current_bb,LENGTH (C i).cs_current_insts) /\
    ?j. ctor_segment_fetch fn (Obs i) = SOME j /\ j.inst_opcode <> PHI /\
       (C i).cs_next_id <= j.inst_id) /\
  (!i. SUC i < n ==>
    create_expr_prefix (C i) (C (SUC (SUC i))) explicit ctx fn
      (Obs i) (M i ++ M (SUC i)) (Obs (SUC (SUC i)))) /\
  (!i. i < n ==> FLAT (DROP i chunks0) = M i ++ FLAT (DROP (SUC i) chunks0))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Q.SUBGOAL_THEN `!i. i <= n ==> ~ (Obs i).vs_halted /\
    ((Obs i).vs_current_bb,(Obs i).vs_inst_idx) =
      ((C i).cs_current_bb,LENGTH (C i).cs_current_insts) /\
    ?j. ctor_segment_fetch fn (Obs i) = SOME j /\ j.inst_opcode <> PHI /\
       (C i).cs_next_id <= j.inst_id` assume_tac
  >- (rpt gen_tac >> disch_tac >> conj_tac
      >- (irule (Q.INST [`St` |-> `Obs`, `C` |-> `C`, `M` |-> `M`,
                         `explicit` |-> `explicit`, `ctx` |-> `ctx`, `fn` |-> `fn`, `n` |-> `n`]
                raw_observed_index_live) >>
          qpat_assum `!i. i < n ==> _` mp_tac >> metis_tac[]) >>
      conj_tac >- (fs[LIST_REL_EL_EQN] >> first_assum irule >> decide_tac) >>
      `i + (n-i) = n` by decide_tac >>
      match_mp_tac (Q.SPECL [`n-i`,`i`] (Q.INST [`St` |-> `Obs`, `C` |-> `C`, `M` |-> `M`,
           `explicit` |-> `explicit`, `ctx` |-> `ctx`, `fn` |-> `fn`, `j` |-> `dispatch`]
           raw_observed_index_fetch)) >>
      qpat_assum `i + (n-i) = n` (pure_rewrite_tac o single) >>
      conj_tac >- (rpt gen_tac >> strip_tac >> first_assum irule >> decide_tac) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `i < n /\ SUC (SUC i) <= n` by decide_tac >>
      qpat_assum `!i. i <= n ==> _` (qspec_then `SUC (SUC i)` (drule_then strip_assume_tac)) >>
      qpat_assum `!i. i < n ==> _`
        (fn th => map_every (fn q => qspec_then q (drule_then strip_assume_tac) th) [`i`,`SUC i`]) >>
      irule raw_observed_prefix_join >> gvs[] >>
      rpt (goal_assum (drule_at Any)) >>
      qexistsl_tac [`EL (SUC i) code`,`EL (SUC i) states`] >> simp[] >>
      metis_tac[LESS_MONO_EQ, LESS_OR_EQ]) >>
  rpt strip_tac >> qspecl_then [`i`,`chunks0`] mp_tac rich_listTheory.DROP_CONS_EL >> simp[]
QED

(* A containing function contains every ordered interval of this very
   itinerary, including zero-code bands. *)
Theorem blueprint_itinerary_index_mono[local]:
  !cuts a b. create_itinerary_code a cuts b ==>
    !i j. i <= j /\ j <= LENGTH cuts ==>
      ci_mono (EL i (a::cuts)) (EL j (a::cuts))
Proof
  Induct >- simp[ci_mono_refl] >>
  simp[create_itinerary_code_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum (drule_then assume_tac) >>
  Cases_on `j` >- simp[ci_mono_refl] >>
  Cases_on `i` >> simp[EL] >> strip_tac
  >- (irule ci_mono_trans >> qexists_tac `h` >> simp[] >>
      first_x_assum (qspecl_then [`0`,`n`] mp_tac) >> simp[EL]) >>
  first_x_assum irule >> simp[]
QED

Theorem blueprint_preparation_coordinates[local]:
  create_blueprint_args_itinerary ce raw later ctors ca prep data len b /\
  cuts = ca :: (prep ++ [c;d;e;f] ++ app) /\
  j = SUC (LENGTH prep) ==>
  EL j (sa::cuts) = b /\ EL (SUC j) (sa::cuts) = c /\
  EL (j+2) (sa::cuts) = d /\ EL (j+3) (sa::cuts) = e /\
  EL (j+4) (sa::cuts) = f /\ DROP (j+4) cuts = app
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LAST (ca::prep) = b` by
    (qpat_assum `create_blueprint_args_itinerary _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [create_blueprint_args_itinerary_def]) >>
     fs[LAST_CONS_cond]) >>
  `sa::cuts = ([sa;ca] ++ prep) ++ ([c;d;e;f] ++ app)` by simp[APPEND_ASSOC] >>
  `SUC j = LENGTH ([sa;ca] ++ prep)` by simp[] >>
  `j+4 = LENGTH (ca::(prep ++ [c;d;e;f]))` by simp[] >>
  conj_tac
  >- (`EL (LENGTH prep) (ca::prep) = b` by
        (qspec_then `ca::prep` mp_tac LAST_EL >> simp[]) >>
      `cuts = (ca::prep) ++ ([c;d;e;f] ++ app)` by simp[] >>
      qpat_assum `j = SUC _` (pure_rewrite_tac o single) >>
      rewrite_tac[EL,TL] >> pop_assum (pure_once_rewrite_tac o single) >>
      simp[EL_APPEND1]) >>
  conj_tac
  >- (qpat_assum `sa::cuts = _` (pure_rewrite_tac o single) >>
      qpat_assum `SUC j = LENGTH _` (pure_once_rewrite_tac o single) >>
      pure_once_rewrite_tac[EL_APPEND_EQN] >> simp[]) >>
  `j+2 = LENGTH ([sa;ca] ++ prep)+1 /\ j+3 = LENGTH ([sa;ca] ++ prep)+2 /\
   j+4 = LENGTH ([sa;ca] ++ prep)+3` by decide_tac >>
  map_every (fn q => conj_tac >-
    (qpat_assum `sa::cuts = _` (pure_rewrite_tac o single) >>
     qpat_assum q (pure_once_rewrite_tac o single) >>
     pure_once_rewrite_tac[EL_APPEND_EQN] >> simp[EL]))
    [`j+2 = LENGTH _ + 1`,`j+3 = LENGTH _ + 2`,`j+4 = LENGTH _ + 3`] >>
  qpat_assum `j+4 = LENGTH _` (pure_rewrite_tac o single) >>
  `cuts = (ca::(prep ++ [c;d;e;f])) ++ app` by simp[APPEND_ASSOC] >>
  pop_assum (pure_once_rewrite_tac o single) >> pure_rewrite_tac[DROP_LENGTH_APPEND] >> REFL_TAC
QED

Theorem blueprint_ctor_observed_coordinates[local]:
  create_itinerary_ctor_rows ce ctors vals ca k cs mid vv /\
  prep = create_itinerary_ctor_cuts cs mid (LENGTH ctors) ++ [a;b] /\
  code = sa::ca::(prep ++ suffix) /\ p = 1+2*LENGTH ctors ==>
  LENGTH prep = 2*LENGTH ctors+2 /\
  EL p code = k /\ EL (SUC p) code = a /\ EL (p+2) code = b /\
  (!i. i <= LENGTH ctors ==> EL (1+2*i) code = EL i cs) /\
  (!i. i < LENGTH ctors ==> EL (SUC (1+2*i)) code = EL i mid)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `n = LENGTH ctors` >>
  qabbrev_tac `rows = create_itinerary_ctor_cuts cs mid n` >>
  qspecl_then [`n`,`\i. EL i mid`,`\i. EL (SUC i) cs`] (strip_assume_tac o BETA_RULE) raw_observed_pairs >>
  `LENGTH rows = 2*n /\ (!i. i < n ==> EL (2*i) rows = EL i mid /\ EL (SUC (2*i)) rows = EL (SUC i) cs)` by
    simp[Abbr `rows`,create_itinerary_ctor_cuts_def] >>
  qpat_x_assum `create_itinerary_ctor_rows _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [create_itinerary_ctor_rows_def]) >>
  `EL 0 cs = ca /\ EL n cs = k` by (Cases_on `cs` >> gvs[EL,LAST_EL]) >>
  `code = [sa;ca] ++ rows ++ [a;b] ++ suffix` by fs[APPEND_ASSOC] >>
  `!i. i < 2*n ==> EL (SUC (SUC i)) code = EL i rows` by
    (rpt strip_tac >> pop_assum mp_tac >> simp[EL,EL_APPEND_EQN]) >>
  `!i. i < n ==> EL (SUC (1+2*i)) code = EL i mid /\ EL (1+2*SUC i) code = EL (SUC i) cs` by
    (rpt strip_tac >>
     `1+2*SUC i = SUC (SUC (SUC (2*i)))` by (simp[MULT_CLAUSES] >> decide_tac) >>
     `SUC (1+2*i) = SUC (SUC (2*i)) /\ 2*i < 2*n /\ SUC (2*i) < 2*n` by decide_tac >>
     metis_tac[]) >>
  `!i. i <= n ==> EL (1+2*i) code = EL i cs` by
    (Cases >- simp[EL] >> strip_tac >> `n' < n` by decide_tac >> metis_tac[]) >>
  `SUC p = LENGTH ([sa;ca] ++ rows) /\ p+2 = LENGTH ([sa;ca] ++ rows)+1` by
    (simp[] >> decide_tac) >>
  `code = ([sa;ca] ++ rows) ++ a::b::suffix` by simp[APPEND_ASSOC] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[LESS_EQ_REFL] >>
  conj_tac
  >- (pop_assum (pure_rewrite_tac o single) >>
      qpat_assum `SUC p = LENGTH _` (pure_once_rewrite_tac o single) >>
      pure_rewrite_tac[EL_LENGTH_APPEND_0] >> REFL_TAC) >>
  conj_tac
  >- (pop_assum (pure_rewrite_tac o single) >>
      qpat_assum `p+2 = LENGTH _ + 1` (pure_once_rewrite_tac o single) >>
      pure_rewrite_tac[EL_LENGTH_APPEND_1] >> REFL_TAC) >>
  metis_tac[]
QED

(* The case-specific coordinates are projections of one observed traversal.
   In particular, M is indexed by edges, while C and Obs index vertices. *)
Theorem create_blueprint_observed_bands:
  cuts = ca :: (prep ++ [c;d;e;f] ++ app) /\
  create_blueprint_args_itinerary ce raw later ctors ca prep data len b /\
  create_itinerary_code sa cuts sc /\ cs_extends sc sb /\ fn_has_code sa sb fn /\
  C = (\i. EL i (sa::cuts)) /\ Obs = (\i. EL i states) /\ M = (\i. EL i chunks0) /\
  R = (\i. FLAT (DROP i chunks0)) /\ n = LENGTH cuts /\ j = SUC (LENGTH prep) /\
  HD states = s0 /\ LAST states = s /\ ~s0.vs_halted /\
  LENGTH chunks0 = n /\ marks = FLAT chunks0 /\
  LIST_REL (\c u. u.vs_current_bb = c.cs_current_bb /\
                  u.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
  (!i. i < n ==> create_expr_prefix (C i) (C (SUC i)) explicit ctx fn
                   (Obs i) (M i) (Obs (SUC i))) /\
  ctor_segment_fetch fn s = SOME dispatch /\ dispatch.inst_opcode <> PHI /\
  dispatch.inst_id = sc.cs_next_id ==>
  C 0 = sa /\ C 1 = ca /\ C j = b /\ C (SUC j) = c /\ C (j+2) = d /\
  C (j+3) = e /\ C (j+4) = f /\ C n = sc /\ j+4 <= n /\ DROP (j+4) cuts = app /\
  Obs 0 = s0 /\ Obs n = s /\ R n = [] /\ marks = M 0 ++ R 1 /\
  create_expr_prefix sa ca explicit ctx fn s0 (M 0) (Obs 1) /\
  (!i. i <= n ==> ~(Obs i).vs_halted /\
    (Obs i).vs_current_bb = (C i).cs_current_bb /\
    (Obs i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    ?x. ctor_segment_fetch fn (Obs i) = SOME x /\ x.inst_opcode <> PHI /\
        (C i).cs_next_id <= x.inst_id) /\
  (!i k. i <= k /\ k <= n ==> ci_mono (C i) (C k) /\ fn_has_code (C i) (C k) fn) /\
  (!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
    create_expr_prefix (C i) (C (SUC i)) explicit ctx fn (Obs i) (M i) (Obs (SUC i)) /\
    R i = M i ++ R (SUC i) /\
    (C i = C (SUC i) ==> Obs (SUC i) = Obs i /\ M i = [])) /\
  (!i. SUC i < n ==> create_expr_prefix (C i) (C (SUC (SUC i))) explicit ctx fn
    (Obs i) (M i ++ M (SUC i)) (Obs (SUC (SUC i)))) /\
  (!cm cs cu cl. prep = [cm;cs;cu;cl;b] ==>
    j = 6 /\ C 2 = cm /\ C 3 = cs /\ C 4 = cu /\ C 5 = cl /\
    R 1 = M 1 ++ (M 2 ++ (M 3 ++ (M 4 ++ M 5 ++ R j)))) /\
  (~raw /\ ctors = [] ==> prep = [] /\ j = 1 /\ b = ca) /\
  (!vals k cs mid vv a p.
    create_itinerary_ctor_rows ce ctors vals ca k cs mid vv /\
    prep = create_itinerary_ctor_cuts cs mid (LENGTH ctors) ++ [a;b] /\
    p = 1+2*LENGTH ctors ==>
    j = p+2 /\ C p = k /\ C (SUC p) = a /\ R p = M p ++ M (SUC p) ++ R j /\
    (!i. i <= LENGTH ctors ==> C (1+2*i) = EL i cs) /\
    (!i. i < LENGTH ctors ==> C (SUC (1+2*i)) = EL i mid /\
      R (1+2*i) = (M (1+2*i) ++ M (SUC (1+2*i))) ++ R (1+2*SUC i) /\
      create_expr_prefix (EL i cs) (EL (SUC i) cs) explicit ctx fn
        (Obs (1+2*i)) (M (1+2*i) ++ M (SUC (1+2*i))) (Obs (1+2*SUC i))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH states = SUC n /\ LENGTH (sa::cuts) = SUC n` by fs[LIST_REL_EL_EQN] >>
  `Obs 0 = s0 /\ Obs n = s` by (Cases_on `states` >> gvs[EL,LAST_EL]) >>
  `C 0 = sa /\ C 1 = ca` by fs[EL] >>
  `C n = sc` by
    (drule create_itinerary_code_relations >> strip_tac >>
     qpat_assum `C = _` (pure_rewrite_tac o single) >>
     qspec_then `sa::cuts` mp_tac LAST_EL >> simp[]) >>
  `j+4 <= n /\ 0 < n` by
    (`n = LENGTH prep + LENGTH app + 5` by (simp[] >> decide_tac) >> decide_tac) >>
  `C j = b /\ C (SUC j) = c /\ C (j+2) = d /\ C (j+3) = e /\
   C (j+4) = f /\ DROP (j+4) cuts = app` by
    (qpat_assum `C = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     drule_all blueprint_preparation_coordinates >> disch_then (qspec_then `sa` ACCEPT_TAC)) >>
  pop_assum strip_assume_tac >>
  `!i k. i <= k /\ k <= n ==> ci_mono (C i) (C k)` by
    (drule blueprint_itinerary_index_mono >> fs[]) >>
  `!i k. i <= k /\ k <= n ==> fn_has_code (C i) (C k) fn` by
    (rpt gen_tac >> strip_tac >>
     `ci_mono (C 0) (C i) /\ ci_mono (C i) (C k) /\ ci_mono (C k) (C n)` by
       (rpt conj_tac >> first_assum irule >> decide_tac) >>
     map_every (fn q => qpat_x_assum q (strip_assume_tac o REWRITE_RULE [ci_mono_def]))
       [`ci_mono (C 0) (C i)`,`ci_mono (C i) (C k)`,`ci_mono (C k) (C n)`] >>
     `cs_extends (C k) sb` by metis_tac[cs_extends_trans] >>
     irule fn_has_code_mid >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`sb`,`sa`] >> metis_tac[]) >>
  `!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
      create_expr_prefix (C i) (C (SUC i)) explicit ctx fn (Obs i) (M i) (Obs (SUC i))` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (`ci_mono (C i) (C (SUC i))` by (first_assum irule >> decide_tac) >>
         qpat_assum `ci_mono (C i) (C (SUC i))` (ACCEPT_TAC o cj 3 o REWRITE_RULE[ci_mono_def])) >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  `~(Obs 0).vs_halted /\ ctor_segment_fetch fn (Obs n) = SOME dispatch /\
     (C n).cs_next_id <= dispatch.inst_id` by simp[] >>
  drule_all raw_observed_spine >> strip_tac >>
  suspend "project"
QED

Resume create_blueprint_observed_bands[project]:
  `!i. i < n ==> R i = M i ++ R (SUC i)` by simp[] >>
  `!i. i <= n ==> ~(Obs i).vs_halted /\
    (Obs i).vs_current_bb = (C i).cs_current_bb /\
    (Obs i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    ?x. ctor_segment_fetch fn (Obs i) = SOME x /\ x.inst_opcode <> PHI /\
        (C i).cs_next_id <= x.inst_id` by fs[PAIR_EQ] >>
  `R 0 = marks` by
    (qpat_assum `R = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     pure_rewrite_tac[DROP_0] >> qpat_assum `marks = FLAT _` (ACCEPT_TAC o SYM)) >>
  `marks = M 0 ++ R 1` by
    (qpat_assum `!i. i < n ==> R i = _` (qspec_then `0` (drule_then mp_tac)) >>
     pure_rewrite_tac[arithmeticTheory.ONE] >>
     qpat_assum `R 0 = marks` (pure_rewrite_tac o single) >> simp_tac bool_ss []) >>
  `create_expr_prefix sa ca explicit ctx fn s0 (M 0) (Obs 1)` by
    (qpat_assum `!i. i < n ==> create_expr_prefix _ _ _ _ _ _ _ _`
       (qspec_then `0` (drule_then mp_tac)) >>
     pure_rewrite_tac [GSYM arithmeticTheory.ONE] >>
     map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
       [`C 0 = sa`,`C 1 = ca`,`Obs 0 = s0`] >> simp_tac bool_ss []) >>
  `!i. i < n /\ C i = C (SUC i) ==> Obs (SUC i) = Obs i /\ M i = []` by
    (rpt gen_tac >> strip_tac >> `i <= n` by decide_tac >>
     qpat_assum `!i. i <= n ==> _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!i. i < n ==> create_expr_prefix _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >> metis_tac[create_copy_empty_cut]) >>
  `R n = []` by
    (qpat_assum `R = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     qpat_assum `LENGTH chunks0 = n` (pure_rewrite_tac o single o SYM) >> simp[]) >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
       (rpt gen_tac >> disch_tac >> rpt conj_tac >> metis_tac[]))) >>
  suspend "modes"
QED

Resume create_blueprint_observed_bands[modes]:
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `j = 6 /\ C 2 = cm /\ C 3 = cs /\ C 4 = cu /\ C 5 = cl` by simp[EL] >>
      `1<n /\ 2<n /\ 3<n /\ 4<n /\ 5<n` by decide_tac >>
      qpat_assum `!i. i < n ==> R i = _`
        (fn th => map_every (fn q => qspec_then q
          (drule_then (assume_tac o SIMP_RULE (srw_ss()) [])) th) [`1`,`2`,`3`,`4`,`5`]) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qpat_assum `j = 6` (pure_rewrite_tac o single) >>
      map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
        [`R 1 = _`,`R 2 = _`,`R 3 = _`,`R 4 = _`,`R 5 = _`] >> simp_tac bool_ss [APPEND_ASSOC]) >>
  conj_tac
  >- (disch_tac >>
      qpat_assum `create_blueprint_args_itinerary _ _ _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [create_blueprint_args_itinerary_def]) >> simp[]) >>
  suspend "ctor"
QED

Resume create_blueprint_observed_bands[ctor]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH prep = 2*LENGTH ctors+2 /\ C p = k /\ C (SUC p) = a /\
   (!i. i <= LENGTH ctors ==> C (1+2*i) = EL i cs) /\
   (!i. i < LENGTH ctors ==> C (SUC (1+2*i)) = EL i mid)` by
    (qpat_assum `C = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     `sa::cuts = sa::ca::(prep ++ ([c;d;e;f] ++ app))` by simp[APPEND_ASSOC] >>
     drule_all blueprint_ctor_observed_coordinates >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `j = p+2 /\ p < n /\ SUC p < n /\ j = SUC (SUC p)` by decide_tac >>
  `R p = M p ++ M (SUC p) ++ R j` by
    (qpat_assum `!i. i < n ==> R i = _`
       (fn th => map_every (fn q => qspec_then q (drule_then assume_tac) th) [`p`,`SUC p`]) >>
     metis_tac[APPEND_ASSOC]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  `1+2*SUC i = SUC (SUC (1+2*i))` by (simp[MULT_CLAUSES] >> decide_tac) >>
  `i <= LENGTH ctors /\ SUC i <= LENGTH ctors /\ 1+2*i < n /\ SUC (1+2*i) < n` by decide_tac >>
  qpat_assum `!i. i <= LENGTH ctors ==> C _ = _`
    (fn th => map_every (fn q => qspec_then q (drule_then assume_tac) th) [`i`,`SUC i`]) >>
  qpat_assum `!i. i < LENGTH ctors ==> C _ = _` (drule_then assume_tac) >>
  qpat_assum `!i. i < n ==> R i = _`
    (fn th => map_every (fn q => qspec_then q (drule_then assume_tac) th)
      [`1+2*i`,`SUC (1+2*i)`]) >>
  qpat_assum `!i. SUC i < n ==> create_expr_prefix _ _ _ _ _ _ _ _`
    (qspec_then `1+2*i` (drule_then assume_tac)) >>
  rpt conj_tac >> metis_tac[APPEND_ASSOC]
QED

Finalise create_blueprint_observed_bands

Theorem raw_observed_ctor_coordinates[local]:
  n = LENGTH xs /\ create_itinerary_ctor_rows ce xs vals d k cs mid vv /\
  code = [sa;a;b;c;d] ++ create_itinerary_ctor_cuts cs mid n ++ suffix ==>
  LENGTH (create_itinerary_ctor_cuts cs mid n) = 2*n /\
  EL (4+2*n) code = k /\
  (!i. i <= n ==> EL (4+2*i) code = EL i cs) /\
  (!i. i < n ==> EL (SUC (4+2*i)) code = EL i mid)
Proof
  strip_tac >> qpat_x_assum `n = LENGTH xs` (assume_tac o SYM) >>
  qspecl_then [`n`,`\i. EL i mid`,`\i. EL (SUC i) cs`] (strip_assume_tac o BETA_RULE) raw_observed_pairs >>
  qpat_x_assum `create_itinerary_ctor_rows _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [createSizeItineraryTheory.create_itinerary_ctor_rows_def]) >>
  `EL 0 cs = d /\ EL n cs = k` by (Cases_on `cs` >> gvs[EL,LAST_EL]) >>
  qabbrev_tac `rows = create_itinerary_ctor_cuts cs mid n` >>
  `LENGTH rows = 2*n /\ (!i. i < n ==> EL (2*i) rows = EL i mid /\ EL (SUC (2*i)) rows = EL (SUC i) cs)` by
    simp[Abbr `rows`,createSizeItineraryTheory.create_itinerary_ctor_cuts_def] >>
  `!j. j < 2*n ==> EL (5+j) code = EL j rows` by
    (rpt strip_tac >> qpat_assum `code = _` (pure_rewrite_tac o single) >>
     pure_rewrite_tac [EL_APPEND_EQN] >> simp[]) >>
  `!i. i < n ==> EL (SUC (4+2*i)) code = EL i mid /\ EL (4+2*SUC i) code = EL (SUC i) cs` by
    (rpt strip_tac >>
     `SUC (4+2*i) = 5+2*i /\ 4+2*SUC i = 5+SUC (2*i)` by (simp[MULT_CLAUSES] >> decide_tac) >>
     `2*i < 2*n /\ SUC (2*i) < 2*n` by decide_tac >> metis_tac[]) >>
  `!i. i <= n ==> EL (4+2*i) code = EL i cs` by
    (Cases >- (qpat_assum `code = _` (pure_rewrite_tac o single) >> simp[]) >>
     strip_tac >> `n' < n` by decide_tac >> metis_tac[]) >>
  simp[] >>
  metis_tac[LESS_EQ_REFL]
QED

Theorem raw_observed_prefix_labels[local]:
  create_expr_prefix a b explicit ctx fn s ms t ==> t.vs_labels = s.vs_labels
Proof
  simp[create_expr_prefix_marked] >>
  `!x y. RTC (create_marked_edge (create_prefix_step a b explicit ctx fn)) x y ==>
       (FST y).vs_labels = (FST x).vs_labels` suffices_by
    (disch_then (qspecl_then [`(s,[])`,`(t,ms)`] mp_tac) >> simp[]) >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def,PULL_EXISTS] >>
  rpt strip_tac >> drule gas_origin_edge_erase >>
  metis_tac[fragGasPathTheory.gas_path_edge_labels]
QED

Theorem raw_observed_suffix_coordinates[local]:
  prep = rows ++ [ca;cb;cc;ce;cv] /\ LENGTH rows = 2*n /\
  code = [sa;a;b;c;d] ++ prep ++ [cq;sc] /\ p = 4+2*n ==>
  EL (p+1) code = ca /\ EL (p+2) code = cb /\ EL (p+3) code = cc /\
  EL (p+4) code = ce /\ EL (p+5) code = cv /\ EL (p+6) code = cq /\
  EL (p+7) code = sc
Proof
  strip_tac >> pure_asm_rewrite_tac [EL_APPEND_EQN,LENGTH_APPEND,LENGTH] >>
  rpt conj_tac >> simp[] >>
  rpt (IF_CASES_TAC >> fs[]) >> decide_tac
QED

Theorem create_raw_observed_bands:
  cuts = [a;b;c;d] ++ prep ++ [cq;sc] /\
  C = (\i. EL i (sa::cuts)) /\ Obs = (\i. EL i states) /\ M = (\i. EL i chunks0) /\
  n = LENGTH cuts /\ vpos = 4 + LENGTH prep /\
  HD states = s0 /\ LAST states = bad /\ ~s0.vs_halted /\
  LENGTH chunks0 = n /\ marks = FLAT chunks0 /\
  LIST_REL (\c s. s.vs_current_bb = c.cs_current_bb /\
                  s.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
  (!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\ fn_has_code (C i) (C (SUC i)) fn /\
      create_expr_prefix (C i) (C (SUC i)) explicit ctx fn (Obs i) (M i) (Obs (SUC i))) /\
  ctor_segment_fetch fn bad = SOME dispatch /\ dispatch.inst_opcode <> PHI /\
  dispatch.inst_id = sc.cs_next_id /\
  emit_op ADD [snap;Lit 32w] c = (data,d) /\
  create_raw_prep_itinerary cenv xs cap data len d prep bufop size_op cv ==>
  Obs 0 = s0 /\ Obs n = bad /\
  (!i. i <= n ==> ~ (Obs i).vs_halted /\
    ((Obs i).vs_current_bb,(Obs i).vs_inst_idx) =
      ((C i).cs_current_bb,LENGTH (C i).cs_current_insts) /\
    ?j. ctor_segment_fetch fn (Obs i) = SOME j /\ j.inst_opcode <> PHI /\
       (C i).cs_next_id <= j.inst_id) /\
  (!i. i < n ==> FLAT (DROP i chunks0) = M i ++ FLAT (DROP (SUC i) chunks0)) /\
  marks = M 0 ++ M 1 ++ M 2 ++ M 3 ++ FLAT (DROP 4 chunks0) /\
  C 0 = sa /\ C 1 = a /\ C 2 = b /\ C 3 = c /\ C 4 = d /\
  C vpos = cv /\ C (SUC vpos) = cq /\ C n = sc /\
  create_expr_prefix sa a explicit ctx fn s0 (M 0) (Obs 1) /\
  create_expr_prefix a b explicit ctx fn (Obs 1) (M 1) (Obs 2) /\
  create_expr_prefix b c explicit ctx fn (Obs 2) (M 2) (Obs 3) /\
  create_expr_prefix c d explicit ctx fn (Obs 3) (M 3) (Obs 4) /\
  gas_origin_edge F explicit ctx fn (Obs 3) (M 3) (OK (Obs 4)) /\
  create_expr_prefix cv cq explicit ctx fn (Obs vpos) (M vpos) (Obs (SUC vpos)) /\
  create_expr_prefix cq sc explicit ctx fn (Obs (SUC vpos)) (M (SUC vpos)) bad /\
  FLAT (DROP vpos chunks0) = M vpos ++ M (SUC vpos) /\
  (cq = sc ==> Obs (SUC vpos) = bad /\ M (SUC vpos) = []) /\
  (if xs = [] then prep = [] /\ cv = d /\ size_op = len /\ bufop = data /\ Obs vpos = Obs 4
   else
   ?vals k cs mid vs buf ca cb dst cc alen ce p.
     compile_create_ctor_args compile_expr cenv xs d = (vals,k) /\
     create_itinerary_ctor_rows cenv xs vals d k cs mid vs /\
     compile_alloc_buffer cap k = (buf,ca) /\
     compile_copy_memory_dynamic buf.buf_operand data len ca = ((),cb) /\
     emit_op ADD [buf.buf_operand;len] cb = (dst,cc) /\
     compile_abi_encode_values_to_buf cenv dst (ZIP (vals,MAP (lowered_value_type cenv) xs)) cc = (alen,ce) /\
     emit_op ADD [len;alen] ce = (size_op,cv) /\ bufop = buf.buf_operand /\
     prep = create_itinerary_ctor_cuts cs mid (LENGTH xs) ++ [ca;cb;cc;ce;cv] /\
     p = 4+2*LENGTH xs /\ vpos = p+5 /\
     C p = k /\ C (p+1) = ca /\ C (p+2) = cb /\ C (p+3) = cc /\ C (p+4) = ce /\
     (!i. i <= LENGTH xs ==> C (4+2*i) = EL i cs) /\
     (!i. i < LENGTH xs ==>
       C (SUC (4+2*i)) = EL i mid /\
       create_expr_prefix (EL i cs) (EL i mid) explicit ctx fn
         (Obs (4+2*i)) (M (4+2*i)) (Obs (SUC (4+2*i))) /\
       create_expr_prefix (EL i mid) (EL (SUC i) cs) explicit ctx fn
         (Obs (SUC (4+2*i))) (M (SUC (4+2*i))) (Obs (4+2*SUC i)) /\
       create_expr_prefix (EL i cs) (EL (SUC i) cs) explicit ctx fn
         (Obs (4+2*i)) (M (4+2*i) ++ M (SUC (4+2*i))) (Obs (4+2*SUC i)) /\
       (Obs (4+2*SUC i)).vs_labels = (Obs (4+2*i)).vs_labels /\
       (EL i mid = EL (SUC i) cs ==>
        Obs (SUC (4+2*i)) = Obs (4+2*SUC i) /\ M (SUC (4+2*i)) = []) /\
       RTC (\u v. (u.vs_current_bb,u.vs_inst_idx) <>
               ((EL (SUC i) cs).cs_current_bb,LENGTH (EL (SUC i) cs).cs_current_insts) /\
         ?j ms. ctor_segment_fetch fn u = SOME j /\ (EL i mid).cs_next_id <= j.inst_id /\
           j.inst_id < (EL (SUC i) cs).cs_next_id /\ gas_origin_edge F explicit ctx fn u ms (OK v))
         (Obs (SUC (4+2*i))) (Obs (4+2*SUC i))) /\
     gas_origin_edge F explicit ctx fn (Obs p) (M p) (OK (Obs (p+1))) /\
     gas_origin_edge F explicit ctx fn (Obs (p+1)) (M (p+1)) (OK (Obs (p+2))) /\
     gas_origin_edge F explicit ctx fn (Obs (p+2)) (M (p+2)) (OK (Obs (p+3))) /\
     create_expr_prefix cc ce explicit ctx fn (Obs (p+3)) (M (p+3)) (Obs (p+4)) /\
     gas_origin_edge F explicit ctx fn (Obs (p+4)) (M (p+4)) (OK (Obs vpos)) /\
     (!j. j < 3 ==>
       (C (p+4+j)).cs_next_id <= (C (p+4+SUC j)).cs_next_id /\
       create_expr_prefix (C (p+4+j)) (C (p+4+SUC j)) explicit ctx fn
         (Obs (p+4+j)) (M (p+4+j)) (Obs (p+4+SUC j))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH states = SUC n /\ LENGTH (sa::cuts) = SUC n` by fs[LIST_REL_EL_EQN] >>
  `Obs 0 = s0 /\ Obs n = bad` by
    (Cases_on `states` >> gvs[EL,LAST_EL]) >>
  `n = LENGTH prep + 6` by
    (qpat_assum `n = LENGTH cuts` (pure_rewrite_tac o single) >> simp[] >> decide_tac) >>
  `n = SUC (SUC vpos)` by (fs[] >> decide_tac) >>
  `C 0 = sa /\ C 1 = a /\ C 2 = b /\ C 3 = c /\ C 4 = d` by fs[EL] >>
  `C (SUC vpos) = cq /\ C n = sc` by
    (qpat_assum `C = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     `sa::cuts = ([sa;a;b;c;d] ++ prep) ++ [cq;sc]` by fs[] >>
     pop_assum (pure_rewrite_tac o single) >>
     `SUC vpos = LENGTH ([sa;a;b;c;d] ++ prep) /\
      n = SUC (LENGTH ([sa;a;b;c;d] ++ prep))` by (fs[] >> decide_tac) >>
     qpat_assum `SUC vpos = LENGTH _` (once_rewrite_tac o single) >>
     qpat_assum `n = SUC (LENGTH _)` (once_rewrite_tac o single) >>
     pure_rewrite_tac[EL_APPEND_EQN] >> simp[]) >>
  `ctor_segment_fetch fn (Obs n) = SOME dispatch /\ (C n).cs_next_id <= dispatch.inst_id` by metis_tac[LESS_EQ_REFL] >>
  `!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
      create_expr_prefix (C i) (C (SUC i)) explicit ctx fn (Obs i) (M i) (Obs (SUC i))` by metis_tac[] >>
  `~(Obs 0).vs_halted` by metis_tac[] >>
  drule_all raw_observed_spine >> strip_tac >>
  suspend "header"
QED

Resume create_raw_observed_bands[header]:
  `C vpos = cv` by
    (qpat_assum `create_raw_prep_itinerary _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [createSizeItineraryTheory.create_raw_prep_itinerary_def])
     >- (`vpos = 4` by fs[] >> metis_tac[]) >>
     qpat_assum `C = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     qpat_assum `prep = _ ++ [_;_;_;_;_]` (fn th =>
       `sa::cuts = (([sa;a;b;c;d] ++ FRONT prep) ++ [cv;cq;sc])` by
        (simp[th,rich_listTheory.FRONT_APPEND_NOT_NIL,APPEND_ASSOC] >> fs[APPEND_ASSOC])) >>
     `vpos = LENGTH ([sa;a;b;c;d] ++ FRONT prep)` by
       (qpat_assum `prep = _ ++ [_;_;_;_;_]` (pure_rewrite_tac o single) >>
        fs[rich_listTheory.FRONT_APPEND_NOT_NIL] >> decide_tac) >>
     qpat_assum `sa::cuts = _` (pure_rewrite_tac o single) >>
     qpat_assum `vpos = LENGTH _` (once_rewrite_tac o single) >>
     pure_rewrite_tac[EL_APPEND_EQN] >> simp[]) >>
  `0<n /\ 1<n /\ 2<n /\ 3<n /\ vpos<n /\ SUC vpos<n /\ 3<=n /\ 4<=n` by decide_tac >>
  qpat_assum `!i. i < n ==> _ /\ fn_has_code _ _ _ /\ _`
    (fn th => map_every (fn q => qspec_then q
       (strip_assume_tac o SIMP_RULE arith_ss [] o UNDISCH) th)
       [`0`,`1`,`2`,`3`,`vpos`,`SUC vpos`]) >>
  `!i. i <= n ==> ((Obs i).vs_current_bb,(Obs i).vs_inst_idx) =
      ((C i).cs_current_bb,LENGTH (C i).cs_current_insts)` by metis_tac[] >>
  `gas_origin_edge F explicit ctx fn (Obs 3) (M 3) (OK (Obs 4))` by
    (irule raw_observed_prefix_emit >> qexistsl_tac [`c`,`d`,`ADD`,`[snap;Lit 32w]`,`data`] >>
     simp_tac (srw_ss()) [is_terminator_def] >>
     qpat_assum `!i. i <= n ==> _ = _` (fn th => map_every (fn q => qspec_then q
       (drule_then (strip_assume_tac o REWRITE_RULE [PAIR_EQ])) th) [`3`,`4`]) >>
     rpt conj_tac >> metis_tac[]) >>
  `marks = M 0 ++ M 1 ++ M 2 ++ M 3 ++ FLAT (DROP 4 chunks0) /\
   FLAT (DROP vpos chunks0) = M vpos ++ M (SUC vpos)` by
    (qpat_assum `!i. i < n ==> FLAT _ = _`
      (fn th => map_every (fn q => qspec_then q
         (assume_tac o SIMP_RULE arith_ss [] o UNDISCH) th) [`0`,`1`,`2`,`3`,`vpos`,`SUC vpos`]) >>
     `FLAT (DROP (SUC (SUC vpos)) chunks0) = []` by metis_tac[DROP_LENGTH_NIL,FLAT] >>
     conj_tac
     >- (qpat_assum `FLAT (DROP 0 chunks0) = _` (mp_tac o REWRITE_RULE [DROP_0]) >>
         pure_asm_rewrite_tac [APPEND_ASSOC] >> simp[]) >>
     pure_asm_rewrite_tac [APPEND_NIL] >> simp[]) >>
  `(cq = sc ==> Obs (SUC vpos) = bad /\ M (SUC vpos) = [])` by
    metis_tac[blueprint_raw_empty_snapshot_prefix] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
  suspend "prep"
QED

Resume create_raw_observed_bands[prep]:
  qpat_x_assum `create_raw_prep_itinerary _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [createSizeItineraryTheory.create_raw_prep_itinerary_def])
  >- (`vpos = 4` by fs[] >> simp[]) >>
  qpat_assum `xs <> []` (fn th => simp_tac bool_ss [th]) >>
  rename1 `compile_create_ctor_args compile_expr cenv xs d = (vals,k)` >>
  rename1 `create_itinerary_ctor_rows cenv xs vals d k cs mid vs` >>
  rename1 `compile_alloc_buffer cap k = (buf,ca)` >>
  rename1 `compile_copy_memory_dynamic buf.buf_operand data len ca = ((),cb)` >>
  rename1 `emit_op ADD [buf.buf_operand;len] cb = (dst,cc)` >>
  rename1 `emit_op ADD [len;alen] ce = (size_op,cv)` >>
  qabbrev_tac `rows = create_itinerary_ctor_cuts cs mid (LENGTH xs)` >>
  `sa::cuts = [sa;a;b;c;d] ++ rows ++ ([ca;cb;cc;ce;cv] ++ [cq;sc])` by fs[APPEND_ASSOC] >>
  `LENGTH rows = 2*LENGTH xs /\ C (4+2*LENGTH xs) = k /\
   (!i. i <= LENGTH xs ==> C (4+2*i) = EL i cs) /\
   (!i. i < LENGTH xs ==> C (SUC (4+2*i)) = EL i mid)` by
    (qpat_assum `C = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     UNABBREV_ALL_TAC >>
     `LENGTH xs = LENGTH xs` by simp[] >>
     drule_all raw_observed_ctor_coordinates >> simp[]) >>
  `LENGTH prep = 2*LENGTH xs+5` by
    (qpat_assum `prep = rows ++ _` (pure_rewrite_tac o single) >> simp[]) >>
  qabbrev_tac `p = 4+2*LENGTH xs` >>
  `vpos = p+5 /\ n = p+7` by (simp[Abbr `p`] >> decide_tac) >>
  `C (p+1) = ca /\ C (p+2) = cb /\ C (p+3) = cc /\ C (p+4) = ce` by
    (qpat_assum `C = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     `sa::cuts = [sa;a;b;c;d] ++ prep ++ [cq;sc]` by fs[] >>
     `p = 4+2*LENGTH xs` by simp[Abbr `p`] >>
     drule_all raw_observed_suffix_coordinates >>
     disch_then (map_every assume_tac o CONJUNCTS) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`vals`,`cs`,`mid`,`vs`,`buf`,`dst`,`alen`] >>
  map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
    [`C p = k`,`C (p+1) = ca`,`C (p+2) = cb`,`C (p+3) = cc`,`C (p+4) = ce`] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
       (rename1 `prep = _ ++ _` >> simp[Abbr `rows`]))) >>
  conj_tac
  >- (suspend "rows") >>
  suspend "fixed"
QED

Resume create_raw_observed_bands[rows]:
  gen_tac >> disch_tac >>
  `4+2*SUC i = SUC (SUC (4+2*i))` by (simp[MULT_CLAUSES] >> decide_tac) >>
  `4+2*i < n /\ SUC (4+2*i) < n /\ i <= LENGTH xs /\ SUC i <= LENGTH xs` by
    (simp[Abbr `p`] >> decide_tac) >>
  qpat_assum `!i. i <= LENGTH xs ==> C _ = _`
    (fn th => map_every (fn q => qspec_then q (drule_then assume_tac) th) [`i`,`SUC i`]) >>
  qpat_assum `!i. i < LENGTH xs ==> C _ = _` (drule_then assume_tac) >>
  qpat_assum `!i. i < n ==> _ /\ fn_has_code _ _ _ /\ _`
    (fn th => map_every (fn q => qspec_then q (drule_then strip_assume_tac) th)
      [`4+2*i`,`SUC (4+2*i)`]) >>
  qpat_assum `!i. SUC i < n ==> _` (qspec_then `4+2*i` (drule_then assume_tac)) >>
  metis_tac[raw_observed_prefix_labels,blueprint_raw_empty_snapshot_prefix,blueprint_ctor_segment_rtc]
QED

Resume create_raw_observed_bands[fixed]:
  `!j. j < 5 ==> fn_has_code (C (p+j)) (C (p+j+1)) fn /\
    ((Obs (p+j)).vs_current_bb,(Obs (p+j)).vs_inst_idx) =
      ((C (p+j)).cs_current_bb,LENGTH (C (p+j)).cs_current_insts) /\
    ((Obs (p+j+1)).vs_current_bb,(Obs (p+j+1)).vs_inst_idx) =
      ((C (p+j+1)).cs_current_bb,LENGTH (C (p+j+1)).cs_current_insts) /\
    create_expr_prefix (C (p+j)) (C (p+j+1)) explicit ctx fn
      (Obs (p+j)) (M (p+j)) (Obs (p+j+1))` by
    (gen_tac >> disch_tac >>
     `p+j < n /\ p+j <= n /\ p+j+1 <= n /\ SUC (p+j) = p+j+1` by decide_tac >>
     qpat_assum `!i. i <= n ==> _ = _` (fn th => map_every (fn q => qspec_then q
       (drule_then assume_tac) th) [`p+j`,`p+j+1`]) >>
     qpat_assum `!i. i < n ==> _ /\ fn_has_code _ _ _ /\ _`
       (qspec_then `p+j` (drule_then strip_assume_tac)) >>
     rpt conj_tac >> metis_tac[]) >>
  `0<5 /\ 1<5 /\ 2<5 /\ 3<5 /\ 4<5` by decide_tac >>
  qpat_assum `!j. j < 5 ==> _` (fn th => map_every (fn q => qspec_then q
    (strip_assume_tac o SIMP_RULE arith_ss [] o UNDISCH) th) [`0`,`1`,`2`,`3`,`4`]) >>
  `C (p+5) = cv` by metis_tac[] >>
  rpt conj_tac
  >- (irule raw_observed_prefix_alloc >> qexistsl_tac [`k`,`ca`] >>
      goal_assum (drule_at Any) >> simp_tac bool_ss [PAIR_EQ] >> rpt conj_tac >> metis_tac[])
  >- (irule raw_observed_prefix_copy >> qexistsl_tac [`ca`,`cb`] >>
      goal_assum (drule_at Any) >> simp_tac bool_ss [PAIR_EQ] >> rpt conj_tac >> metis_tac[])
  >- (irule raw_observed_prefix_emit >> qexistsl_tac [`cb`,`cc`,`ADD`,`[buf.buf_operand;len]`,`dst`] >>
      simp_tac (srw_ss()) [is_terminator_def] >> rpt conj_tac >> metis_tac[PAIR_EQ])
  >- metis_tac[]
  >- (irule raw_observed_prefix_emit >> qexistsl_tac [`ce`,`cv`,`ADD`,`[len;alen]`,`size_op`] >>
      simp_tac (srw_ss()) [is_terminator_def] >> rpt conj_tac >> metis_tac[PAIR_EQ]) >>
  gen_tac >> disch_tac >>
  `p+4+j < n /\ p+4+SUC j = SUC (p+4+j)` by decide_tac >>
  qpat_assum `!i. i < n ==> _ /\ create_expr_prefix _ _ _ _ _ _ _ _`
    (qspec_then `p+4+j` (drule_then strip_assume_tac)) >>
  metis_tac[]
QED

Finalise create_raw_observed_bands

(* Replay one reached row, retaining both the next entry and the producer's
   view at the expression cut. The two ghost pairs in the VV arm serve
   different purposes. *)
Theorem blueprint_ctor_row_dispatch[local]:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\ create_operand_completed_ok cx e /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) m = (saved,b) /\
  local_ptrs_reserved ce a /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx func s f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
     stmt_state_rel h ctx func ce cx p s /\ storage_well_formed_on cx p (FST h) /\
     ghost_inv_at (DF h) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  (is_word_type (lowered_value_type ce e) ==>
    compile_snapshot_vv ce (exprs_can_mutate ce xs)
      (ext_call_arg_value (lowered_value_type ce e) vv) shm = (saved,shb) /\
    expr_sim_full_code (ctx,shctx,func,shfunc) (a,b,sha,shb) /\
    create_expr_prefix a b (gas_explicit_sites ctx shctx) ctx func s (chunk ++ snap) t) /\
  (~is_word_type (lowered_value_type ce e) ==>
    expr_sim_full_code (ctx,shctx,func,shfunc) (a,m,sha,shm) /\
    create_expr_prefix a m (gas_explicit_sites ctx shctx) ctx func s chunk mid /\
    mid.vs_current_bb = m.cs_current_bb /\ mid.vs_inst_idx = LENGTH m.cs_current_insts /\
    create_expr_prefix m b (gas_explicit_sites ctx shctx) ctx func mid snap t /\
    (exprs_can_mutate ce xs ==>
      fn_has_code m b func /\
      (?j. ctor_segment_fetch func t = SOME j /\ j.inst_opcode <> PHI /\
           b.cs_next_id <= j.inst_id) /\
      (gas_origin_path T (gas_explicit_sites ctx shctx) ctx func mid [] (OK t) ==> snap = []))) /\
  bind (eval_expr cx e) (read_result cx) p = (rr,q) /\
  valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit ((chunk ++ snap) ++ rest) s.vs_gas_readings ++ tail ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v Gt tt. rr = INL v /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    expr_sim_inv ce cx env q /\ return_buf_frame d ce b t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_no_wrap i z) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx func ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q Gt tt t) /\
    (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME ann /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) /\
      value_has_type tv v /\ value_has_type ann v) /\
    (is_word_type (lowered_value_type ce e) ==>
      ?G' tn'. !K op. valid_horizon cx st0 K q.storage_trace /\
        lower_value compile_expr ce (expr_type e) e a = (op,b) ==>
        expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (p,a,b,s,op,G,tn)
          K (INL v : value + exception) (q with gas_obs := []) G' tn' t) /\
    (~is_word_type (lowered_value_type ce e) ==>
      ?Gm tm raw. eval_expr cx e p = (INL raw,q) /\
      !h. valid_horizon cx st0 h q.storage_trace ==>
        vv_post h ctx func ce cx e p a m s (q with gas_obs := []) raw vv mid /\
        vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
          (q with gas_obs := []) raw vv mid /\
        ptr_vv_ok cx (post_value_type ce e) raw vv (q with gas_obs := []) Gm tm mid /\
        alloca_history func mid /\ s.vs_alloca_next <= mid.vs_alloca_next /\
        ghost_inv_at (DF h) lo d ce cx (q with gas_obs := []) Gm tm mid /\
        ghost_kept_at lo ce p a G tn s Gm tm /\
        (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
          ptr_buf_ok ce e op Gm mid) /\
        (!tag p0. vv = LocatedValue tag p0 /\ p0.ptr_location = LocMemory ==>
          ptr_buf_ok ce e p0.ptr_operand Gm mid) /\
        (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx raw (q with gas_obs := []) = (INL val,q with gas_obs := []) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
              eval_operand (vv_operand vv) mid = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tm.t_mem mid.vs_memory mem ==>
                 val_in_memory rt val (w2n w) mem)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type (lowered_value_type ce e)`
  >- (qpat_x_assum `is_word_type _ ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
      drule_all blueprint_ctor_word_row >> strip_tac
      >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
      disj2_tac >> qexistsl [`v`,`G'`,`tn'`] >> simp[] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qexistsl [`G'`,`tn'`] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `~is_word_type _ ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `p.gas_obs = _` (assume_tac o REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all blueprint_ctor_vv_row >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`v`,`Gt'`,`tt`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`Gm`,`tm`,`raw`] >> asm_rewrite_tac[]
QED

(* Constructor rows share this replay in both payload modes. R i is the
   unconsumed mark list at row i, including the caller's continuation. *)
Theorem create_ctor_rows_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  (!K. dead_lo_ok K (DF K) lo ce cx) /\
  (!i. i < LENGTH args ==> create_operand_completed_ok cx (EL i args)) /\
  (!i p. i < LENGTH args /\ expr_sim_inv ce cx env p ==>
    expr_body_pre ce cx env (EL i args) p) /\
  (!i. i < LENGTH args ==>
    compile_expr ce (expr_type (EL i args)) (EL i args) (C i) = (V i,M i) /\
    compile_expr ce (expr_type (EL i args)) (gas_shadow_expr (EL i args)) (Sh i) = (V i,SM i) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
      (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (M i) =
      (EL i svs,C (SUC i)) /\
    local_ptrs_reserved ce (C i) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
    (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
    R i = (Chunk i ++ Snap i) ++ R (SUC i) /\
    (is_word_type (lowered_value_type ce (EL i args)) ==>
      compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
        (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (SM i) =
        (EL i svs,Sh (SUC i)) /\
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,C (SUC i),Sh i,Sh (SUC i)) /\
      create_expr_prefix (C i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
        (St i) (Chunk i ++ Snap i) (St (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i args)) ==>
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,M i,Sh i,SM i) /\
      create_expr_prefix (C i) (M i) (gas_explicit_sites ctx shctx) ctx func
        (St i) (Chunk i) (Mid i) /\
      (Mid i).vs_current_bb = (M i).cs_current_bb /\
      (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
      create_expr_prefix (M i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
        (Mid i) (Snap i) (St (SUC i)) /\
      (exprs_can_mutate ce (DROP (SUC i) args) ==>
        fn_has_code (M i) (C (SUC i)) func /\
        (?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ j.inst_opcode <> PHI /\
             (C (SUC i)).cs_next_id <= j.inst_id) /\
        (gas_origin_path T (gas_explicit_sites ctx shctx) ctx func (Mid i) [] (OK (St (SUC i))) ==>
          Snap i = [])))) /\
  bind (eval_exprs cx args) k p0 = (res,out) /\ (!vs. storage_trace_frame (k vs)) /\
  valid_horizon cx st0 H out.storage_trace /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail /\
  expr_sim_inv ce cx env p0 /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_no_wrap i z) /\
  ~(St 0).vs_halted /\ (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at (DF K) lo d ce cx p0 G0 tn0 (St 0)) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?vs E Gf tf. E 0 = p0 /\ LENGTH vs = LENGTH args /\
    eval_exprs cx args p0 = (INL vs,E (LENGTH args)) /\
    k vs (E (LENGTH args)) = (res,out) /\
    valid_horizon cx st0 H (E (LENGTH args)).storage_trace /\
    (!i. i <= LENGTH args ==>
      (E i).gas_obs = gas_explicit (R i) (St i).vs_gas_readings ++ tail /\
      expr_sim_inv ce cx env (E i) /\ return_buf_frame d ce (C i) (St i) /\
      alloca_history func (St i) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St i)) /\
      (!f j z. frag_reachable ctx func (St i) f j z ==> dalloca_no_wrap j z) /\
      ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
      (St i).vs_inst_idx = LENGTH (C i).cs_current_insts) /\
    (!K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E (LENGTH args)) (St (LENGTH args)) /\
      storage_well_formed_on cx (E (LENGTH args)) (FST K) /\
      ghost_inv_at (DF K) lo d ce cx (E (LENGTH args)) Gf tf (St (LENGTH args))) /\
    (!i. i < LENGTH args ==>
      bind (eval_expr cx (EL i args)) (read_result cx) (E i) = (INL (EL i vs),E (SUC i)) /\
      expr_body_pre ce cx env (EL i args) (E i) /\
      (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
        evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
        arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
        value_has_type tv (EL i vs) /\ value_has_type ann (EL i vs)) /\
      (!g h. (!K. valid_horizon cx st0 K (E i).storage_trace ==>
          stmt_state_rel K ctx func ce cx (E i) (St i) /\
          storage_well_formed_on cx (E i) (FST K) /\
          ghost_inv_at (DF K) lo d ce cx (E i) g h (St i)) ==>
        (is_word_type (lowered_value_type ce (EL i args)) ==>
          ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
            lower_value compile_expr ce (expr_type (EL i args)) (EL i args) (C i) =
              (op,C (SUC i)) ==>
            expr_sim_full_post (DF,lo,d,ctx,func) ce cx (EL i args)
              (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i vs) : value + exception)
              ((E (SUC i)) with gas_obs := []) g' h' (St (SUC i))) /\
        (~is_word_type (lowered_value_type ce (EL i args)) ==>
          ?g' h' raw. eval_expr cx (EL i args) (E i) = (INL raw,E (SUC i)) /\
          !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
            vv_post K ctx func ce cx (EL i args) (E i) (C i) (M i) (St i)
              ((E (SUC i)) with gas_obs := []) raw (V i) (Mid i) /\
            vv_store_bound cx (post_value_type ce (EL i args)) (lowered_value_type ce (EL i args))
              ((E (SUC i)) with gas_obs := []) raw (V i) (Mid i) /\
            ptr_vv_ok cx (post_value_type ce (EL i args)) raw (V i)
              ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
            alloca_history func (Mid i) /\ (St i).vs_alloca_next <= (Mid i).vs_alloca_next /\
            ghost_inv_at (DF K) lo d ce cx ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
            ghost_kept_at lo ce (E i) (C i) g h (St i) g' h' /\
            (!tag op. V i = StackValue tag op /\ ~is_word_type (post_value_type ce (EL i args)) ==>
              ptr_buf_ok ce (EL i args) op g' (Mid i)) /\
            (!tag p. V i = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok ce (EL i args) p.ptr_operand g' (Mid i)) /\
            (ce.ce_is_ctor /\ vv_location (V i) = SOME LocCode ==>
              ?val. read_result cx raw ((E (SUC i)) with gas_obs := []) =
                (INL val,(E (SUC i)) with gas_obs := []) /\
              !rt w. evaluate_type (get_tenv cx) (post_value_type ce (EL i args)) = SOME rt /\
                eval_operand (vv_operand (V i)) (Mid i) = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside h'.t_mem (Mid i).vs_memory mem ==>
                  val_in_memory rt val (w2n w) mem)))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `Entry = \i p g h.
    p.gas_obs = gas_explicit (R i) (St i).vs_gas_readings ++ tail /\
    expr_sim_inv ce cx env p /\ return_buf_frame d ce (C i) (St i) /\
    alloca_history func (St i) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St i)) /\
    (!f j z. frag_reachable ctx func (St i) f j z ==> dalloca_no_wrap j z) /\
    ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
    (St i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    (!K. valid_horizon cx st0 K p.storage_trace ==>
      stmt_state_rel K ctx func ce cx p (St i) /\ storage_well_formed_on cx p (FST K) /\
      ghost_inv_at (DF K) lo d ce cx p g h (St i))` >>
  `Entry 0 p0 G0 tn0` by (simp[Abbr `Entry`] >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 H p0.storage_trace` by
    (qpat_assum `bind (eval_exprs cx args) k p0 = _`
       (mp_then Any irule vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_bind_all]) >>
  qabbrev_tac `P = \i p. valid_horizon cx st0 H p.storage_trace /\ ?g h. Entry i p g h` >>
  `P 0 p0` by (simp[Abbr `P`] >> qexistsl [`G0`,`tn0`] >> first_assum ACCEPT_TAC) >>
  qspecl_then [`LENGTH args`,`0`,`p0`,`k`] mp_tac
    (Q.INST [`es` |-> `args`] blueprint_ctor_source_walk) >>
  simp[] >>
  (impl_tac >- suspend "step") >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  suspend "success"
QED

Resume create_ctor_rows_at_cuts[step]:
  map_every qx_gen_tac [`i`,`p`,`l`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `P i p` mp_tac >> simp[Abbr `P`,Abbr `Entry`] >> strip_tac >>
  qpat_x_assum `!i. _ ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `expr_body_pre ce cx env (EL i args) p` by metis_tac[] >>
  `create_operand_completed_ok cx (EL i args)` by simp[] >>
  `p.gas_obs = gas_explicit ((Chunk i ++ Snap i) ++ R (SUC i)) (St i).vs_gas_readings ++ tail`
    by fs[] >>
  `?rr q. bind (eval_expr cx (EL i args)) (read_result cx) p = (rr,q)` by
    (Cases_on `bind (eval_expr cx (EL i args)) (read_result cx) p` >> simp[]) >>
  `valid_horizon cx st0 H q.storage_trace` by
    (qpat_assum `bind (bind _ _) l p = _` mp_tac >> pure_once_rewrite_tac[bind_def] >>
     Cases_on `rr` >> simp[] >> strip_tac >>
     qpat_assum `l _ q = _` (mp_then Any irule vyperStorageFootprintTheory.valid_horizon_frame) >> simp[]) >>
  drule_all blueprint_ctor_row_dispatch >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> fs[bind_def]) >>
  disj2_tac >> qexistsl_tac [`v`,`q`] >> simp[] >>
  conj_tac
  >- (qpat_assum `bind (bind _ _) l p = _` mp_tac >> pure_once_rewrite_tac[bind_def] >> simp[]) >>
  qexistsl_tac [`Gt'`,`tt`] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Resume create_ctor_rows_at_cuts[success]:
  `!i. i <= LENGTH args ==> valid_horizon cx st0 H (E i).storage_trace /\
     ?g h. Entry i (E i) g h` by fs[Abbr `P`] >>
  `valid_horizon cx st0 H (E (LENGTH args)).storage_trace` by simp[] >>
  `?g h. Entry (LENGTH args) (E (LENGTH args)) g h` by simp[] >>
  disj2_tac >> qexistsl_tac [`vs`,`E`,`g`,`h`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!i. _ ==> _ /\ ?g h. Entry i _ g h` (qspec_then `i` mp_tac) >>
      simp[Abbr `Entry`] >> metis_tac[]) >>
  conj_tac
  >- (qpat_assum `Entry (LENGTH args) _ g h` mp_tac >>
      simp[Abbr `Entry`] >> metis_tac[]) >>
  suspend "callbacks"
QED

Resume create_ctor_rows_at_cuts[callbacks]:
  qx_gen_tac `i` >> disch_tac >>
  `i <= LENGTH args /\ SUC i <= LENGTH args` by decide_tac >>
  `valid_horizon cx st0 H (E (SUC i)).storage_trace` by simp[] >>
  qpat_assum `!i. i < LENGTH args ==> bind _ _ _ = _`
    (qspec_then `i` (drule_then assume_tac)) >>
  qpat_x_assum `!i. _ ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `?g h. Entry i (E i) g h` by simp[] >>
  qpat_x_assum `Entry i (E i) _ _` mp_tac >> simp[Abbr `Entry`] >> strip_tac >>
  `expr_body_pre ce cx env (EL i args) (E i)` by metis_tac[] >>
  `create_operand_completed_ok cx (EL i args)` by simp[] >>
  `(E i).gas_obs = gas_explicit ((Chunk i ++ Snap i) ++ R (SUC i)) (St i).vs_gas_readings ++ tail`
    by fs[] >>
  qpat_assum `bind _ _ (E i) = _` (fn th => rewrite_tac [th]) >>
  qpat_assum `expr_body_pre ce cx env (EL i args) (E i)` (fn th => rewrite_tac [th]) >>
  conj_tac
  >- (drule_all blueprint_ctor_row_dispatch >> strip_tac >- fs[] >>
      qexistsl_tac [`tv`,`ann`] >> fs[]) >>
  qpat_x_assum `!K. _ ==> stmt_state_rel K _ _ _ _ (E i) _ /\ _` (mk_asm "row_entry") >>
  map_every qx_gen_tac [`Ga`,`ta`] >> disch_tac >>
  `!K. valid_horizon cx st0 K (E i).storage_trace ==>
    stmt_state_rel K ctx func ce cx (E i) (St i) /\
    storage_well_formed_on cx (E i) (FST K) /\
    ghost_inv_at (DF K) lo d ce cx (E i) Ga ta (St i)` by
    (asm "row_entry" mp_tac >> metis_tac[]) >>
  drule_all blueprint_ctor_row_dispatch >> strip_tac >- fs[] >>
  gvs[AC ADD_ASSOC ADD_COMM]
QED

Finalise create_ctor_rows_at_cuts

Theorem blueprint_raw_copy_guarded_rtc[local]:
  create_expr_prefix a b explicit ctx fn s marks t ==>
  RTC (\x y. (x.vs_current_bb <> b.cs_current_bb \/
                x.vs_inst_idx <> LENGTH b.cs_current_insts) /\
             ?ms. gas_origin_edge F explicit ctx fn x ms (OK y)) s t
Proof
  rewrite_tac[create_expr_prefix_marked] >>
  `!x y. RTC (create_marked_edge (create_prefix_step a b explicit ctx fn)) x y ==>
    RTC (\u v. (u.vs_current_bb <> b.cs_current_bb \/
                  u.vs_inst_idx <> LENGTH b.cs_current_insts) /\
               ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)) (FST x) (FST y)`
    suffices_by (disch_then (qspecl_then [`(s,[])`,`(t,marks)`] mp_tac) >> simp[]) >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def] >>
  rpt strip_tac >> irule (cj 2 RTC_RULES) >> metis_tac[]
QED

Theorem blueprint_raw_copied_at_cut:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\ create_operand_completed_ok cx e /\
  expr_type e = BaseT (BytesT (Dynamic k)) /\ exprs_can_mutate ce later /\
  eval_operand target_op s = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at ca x) /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca s /\ alloca_history fnc s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx fnc s f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p s /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p Gi ti s) /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\ s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) sca = (vv,scm) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cm,sca,scm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\
  fn_has_code cm cs fnc /\ fn_has_code cu cl fnc /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc s mc t /\
  t.vs_current_bb = cm.cs_current_bb /\ t.vs_inst_idx = LENGTH cm.cs_current_insts /\
  create_expr_prefix cm cs (gas_explicit_sites ctx shctx) ctx fnc t ms r /\
  r.vs_current_bb = cs.cs_current_bb /\ r.vs_inst_idx = LENGTH cs.cs_current_insts /\
  create_expr_prefix cs cu (gas_explicit_sites ctx shctx) ctx fnc r mu u /\
  u.vs_current_bb = cu.cs_current_bb /\ u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  (!v. storage_trace_frame (kcont v)) /\
  bind (bind (eval_expr cx e) (read_result cx)) kcont p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (mc ++ (ms ++ (mu ++ rest))) s.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?bs q G tn.
    bind (eval_expr cx e) (read_result cx) p = (INL (BytesV bs),q) /\
    kcont (BytesV bs) q = (res,out) /\ valid_horizon cx st0 H q.storage_trace /\
    q.gas_obs = gas_explicit rest u.vs_gas_readings ++ tail /\
    expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bs) raw_op u /\
    eval_operand target_op u = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at cu x) /\
    expr_sim_inv ce cx env q /\ local_ptrs_reserved ce cu /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
    return_buf_frame d ce cu u /\ alloca_history fnc u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_no_wrap i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q u /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q G tn u) /\ ~u.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `explicit = gas_explicit_sites ctx shctx` >>
  `expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,([]:(num#num) option list),fnc,shfnc) ce cx
      (expr_type e) e p (st0,ca,cm,sca,scm,vv,s,Gi,ti)` by
    (`gas_admissible (eval_expr cx e) expr_vv_res_ok p` by
       metis_tac[expr_body_pre_vv_gas_admissible] >>
     fs[expr_vv_sim_full_pre_def,expr_sim_full_code_def] >> metis_tac[]) >>
  drule_all create_size_replay_vv_cut >> strip_tac >>
  `?rr q. eval_expr cx e p = (rr,q)` by (Cases_on `eval_expr cx e p` >> simp[]) >>
  `valid_horizon cx st0 H q.storage_trace` by
    (`!tv. storage_trace_frame (bind (read_result cx tv) kcont)` by
       simp[storage_trace_frame_bind_all,storage_trace_frame_read_result] >>
     qpat_x_assum `bind (bind (eval_expr cx e) (read_result cx)) kcont p = _` mp_tac >>
     pure_rewrite_tac[vyperStateTheory.bind_assoc] >> Cases_on `rr` >>
     simp[Once bind_def] >> strip_tac >>
     qpat_assum `bind (read_result cx _) kcont q = _`
       (mp_then Any irule vyperStorageFootprintTheory.valid_horizon_frame) >> simp[]) >>
  qabbrev_tac `suffix = gas_explicit (ms ++ (mu ++ rest)) t.vs_gas_readings ++ tail` >>
  `p.gas_obs = gas_explicit mc s.vs_gas_readings ++ suffix` by
    (qpat_assum `create_expr_prefix ca cm _ _ _ s mc t`
       (mp_then Any assume_tac create_prefix_readings) >>
     simp[Abbr `suffix`,gas_explicit_append,APPEND_ASSOC,DROP_DROP_T,
          AC ADD_ASSOC ADD_COMM]) >>
  qunabbrev_tac `explicit` >>
  drule_all blueprint_ctor_complete >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> fs[vyperStateTheory.bind_assoc,bind_def]) >>
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (s,Gi,ti) mc (OK t,Gv,tvtn)` >>
  suspend "source"
QED

Resume blueprint_raw_copied_at_cut[source]:
  qpat_assum `!h. valid_horizon cx st0 h q.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` (mp_tac o SIMP_RULE (srw_ss()) [])) >> simp[] >> strip_tac >>
  `eval_expr cx e (p with gas_obs := p.gas_obs) = (INL tv,q)` by simp[] >>
  drule_all createSizeRawSourceTheory.create_raw_read_bytes >> strip_tac >>
  rename1 `read_result cx tv q = (INL (BytesV bs),q)` >>
  `bind (eval_expr cx e) (read_result cx) p = (INL (BytesV bs),q)` by simp[bind_def] >>
  `kcont (BytesV bs) q = (res,out)` by
    (qpat_assum `bind (bind (eval_expr cx e) (read_result cx)) kcont p = _` mp_tac >>
     pure_once_rewrite_tac[bind_def] >> simp[]) >>
  qpat_x_assum `eval_expr cx e p = (rr,q)` kall_tac >>
  `eval_expr cx e p = (INL tv,q)` by fs[] >>
  `~is_word_type (vv_type vv)` by
    (drule_all createBlueprintRawCopyLayoutTheory.create_blueprint_raw_copy_layout >>
     strip_tac >> simp[is_word_type_def]) >>
  `cu = cs` by
    (`?dst. saved = LocatedValue (vv_type vv) (mk_ptr dst LocMemory)` by
       (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
        Cases_on `compile_materialize_vv ce (vv_type vv) vv cm` >>
        simp[compile_snapshot_vv_def,comp_bind_def,comp_return_def] >> metis_tac[]) >>
     fs[unwrap_value_def,mk_ptr_def,comp_return_def]) >>
  `u = r /\ mu = []` by
    (qpat_assum `create_expr_prefix cs cu _ _ _ r mu u`
       (mp_tac o REWRITE_RULE [create_expr_prefix_marked]) >>
     ONCE_REWRITE_TAC[RTC_CASES1] >>
     simp[EXISTS_PROD,create_marked_edge_def,create_prefix_step_def]) >>
  `storage_trace_domain cx st0 q.storage_trace` by
    (qpat_assum `valid_horizon cx st0 H q.storage_trace` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[valid_horizon_def,storage_trace_domain_def,storage_trace_horizon_def,
          storage_observations_ok_def,EVERY_MEM,regions_consistent_def,
          storage_locks_separated_def,storage_well_formed_on_def] >>
     strip_tac >> rpt conj_tac >> TRY (metis_tac[] >> NO_TAC) >>
     qpat_x_assum `storage_trace_backends_well_formed _ _ _` mp_tac >>
     simp[storage_trace_backends_well_formed_def,EVERY_MEM] >>
     rpt strip_tac >> first_x_assum drule >> Cases_on `observation` >>
     simp[storage_well_formed_on_def] >> metis_tac[]) >>
  `is_bytestring_type (expr_type e)` by simp[is_bytestring_type_def] >>
  `post_value_type ce e = expr_type e` by simp[post_value_type_bytestring] >>
  `~is_word_type (post_value_type ce e)` by simp[is_word_type_def] >>
  `!h. valid_horizon cx st0 h q.storage_trace ==>
    gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shctx,ctx,fnc,[]) (s,Gi,ti) mc (OK t,Gv,tvtn) /\
    vv_post h ctx fnc ce cx e p ca cm s q tv vv t /\ ghost_inv_at (DF h) lo d ce cx q Gv tvtn t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!h. valid_horizon cx st0 h q.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspecl_then [`h`] mp_tac o SIMP_RULE (srw_ss()) []) >>
     simp[exprSimSubscriptArrayComposeTheory.vv_post_final_gas,ghost_inv_at_def,
          ghost_inv_def,loweringStateRelDefsTheory.local_region_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >> FIRST_ASSUM ACCEPT_TAC) >>
  `vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) q tv vv t /\
   ptr_vv_ok cx (post_value_type ce e) tv vv q Gv tvtn t` by
    (qpat_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `vv` >>
     pure_rewrite_tac[exprSimMemDefsTheory.vv_store_bound_def,ptr_vv_ok_def,
       exprSimSubscriptArrayComposeTheory.read_result_success_gas_iff] >> simp[]) >>
  `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?v. read_result cx tv q = (INL v,q) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
                eval_operand (vv_operand vv) t = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tvtn.t_mem t.vs_memory mem ==> val_in_memory rt v (w2n w) mem)` by
    (strip_tac >>
     qpat_assum `ce.ce_is_ctor /\ vv_location vv = _ ==> _` mp_tac >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `v` strip_assume_tac) >>
     `v = BytesV bs` by fs[] >>
     qexists_tac `BytesV bs` >> (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
     pure_once_rewrite_tac[ADD_COMM] >>
     qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >> FIRST_ASSUM ACCEPT_TAC) >>
  suspend "machine"
QED

Resume blueprint_raw_copied_at_cut[machine]:
  `ci_mono ca cm` by
    (qspecl_then [`ce`,`expr_type e`,`e`,`ca`] mp_tac (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
  `ci_mono cm cs` by
    (qspecl_then [`ce`,`exprs_can_mutate ce later`,`vv`,`cm`] mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `ca.cs_next_var <= cm.cs_next_var /\ ca.cs_next_id <= cm.cs_next_id /\
   cm.cs_next_var <= cs.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved ce cm /\ local_ptrs_reserved ce cs` by
    (conj_asm1_tac >> metis_tac[local_ptrs_reserved_next_var]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at cm x` by
    (gen_tac >> disch_tac >>
     drule_all (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `!x. target_op = Var x ==> not_fresh_at cm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `MAP FDOM p.scopes = MAP FDOM q.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `expr_sim_inv ce cx env q` by (drule_all bodySimStmtFactsTheory.expr_body_pre_eval_result >> simp[]) >>
  `MEM fnc ctx.ctx_functions /\ fn_inst_ids_distinct fnc` by fs[expr_sim_full_code_def] >>
  `!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (gen_tac >> disch_tac >> drule_all body_inv_no_phi >> simp[]) >>
  `~t.vs_halted` by
    (qpat_assum `create_expr_prefix ca cm _ _ _ s mc t`
       (qspec_then `s` mp_tac o MATCH_MP blueprint_prefix_gas_path o
        REWRITE_RULE[create_expr_prefix_marked]) >>
     simp[] >> metis_tac[gas_path_normal]) >>
  `!x w. not_fresh_at ca x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w` by
    fs[vv_post_def] >>
  `eval_operand target_op t = SOME aw` by
    (`t.vs_labels = s.vs_labels` by
       (qpat_assum `create_expr_prefix ca cm _ _ _ s mc t`
          (mp_then Any mp_tac blueprint_prefix_labels) >> simp[]) >>
     irule blueprint_eval_operand_frame >> qexistsl_tac [`ca`,`s`] >> simp[]) >>
  `return_buf_frame d ce cm t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`ca`] >> simp[]) >>
  `?next. ctor_segment_fetch fnc u = SOME next /\ next.inst_opcode = MLOAD /\ cs.cs_next_id <= next.inst_id` by
    (qpat_assum `cu = cs` SUBST_ALL_TAC >> qpat_assum `u = r` SUBST_ALL_TAC >>
     drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >>
     disch_then (qx_choosel_then [`tmp`,`bb`] (map_every assume_tac o CONJUNCTS)) >>
     qexists_tac `mk_inst cs.cs_next_id MLOAD [raw_op] [tmp]` >>
     (conj_tac >-
       (pure_rewrite_tac[createCtorSegmentArrivalTheory.ctor_segment_fetch_def] >>
        qpat_assum `lookup_block r.vs_current_bb _ = SOME bb` (once_rewrite_tac o single) >>
        pure_rewrite_tac[optionTheory.OPTION_BIND_def] >> BETA_TAC >> FIRST_ASSUM ACCEPT_TAC)) >>
     simp[mk_inst_def]) >>
  `!h. valid_horizon cx st0 h q.storage_trace ==>
     vv_post h ctx fnc ce cx e p ca cm s q tv vv t /\ ghost_inv_at (DF h) lo d ce cx q Gv tvtn t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ vv_post h _ _ _ _ _ _ _ _ _ q _ _ _ /\ _`
       (qspec_then `h` mp_tac) >> simp[]) >>
  qabbrev_tac `R = \x y. (x.vs_current_bb <> cs.cs_current_bb \/
                            x.vs_inst_idx <> LENGTH cs.cs_current_insts) /\
        ?ms. gas_origin_edge F (gas_explicit_sites ctx shctx) ctx fnc x ms (OK y)` >>
  `RTC R t u` by
    (unabbrev_all_tac >> qpat_assum `create_expr_prefix cm cs _ _ _ t ms r`
       (mp_then Any mp_tac blueprint_raw_copy_guarded_rtc) >> simp[] >> metis_tac[]) >>
  `!x y. R x y ==> (x.vs_current_bb <> cs.cs_current_bb \/ x.vs_inst_idx <> LENGTH cs.cs_current_insts) /\
        ?ms. gas_origin_edge F (gas_explicit_sites ctx shctx) ctx fnc x ms (OK y)` by simp[Abbr `R`] >>
  `compile_snapshot_vv ce T vv cm = (saved,cs)` by
    (qpat_assum `exprs_can_mutate ce later` (fn th =>
       qpat_assum `compile_snapshot_vv _ _ _ _ = _`
         (ACCEPT_TAC o PURE_REWRITE_RULE [EQT_INTRO th]))) >>
  `!ty op. vv = StackValue ty op ==> ptr_buf_ok ce e op Gv t` by
    (rpt strip_tac >> qpat_assum `!ty op. vv = StackValue ty op /\ _ ==> _` (qspecl_then [`ty`,`op`] mp_tac) >> simp[is_word_type_def]) >>
  suspend "copy"
QED

Resume blueprint_raw_copied_at_cut[copy]:
  `u.vs_current_bb = cs.cs_current_bb /\ u.vs_inst_idx = LENGTH cs.cs_current_insts` by fs[] >>
  drule_all (Q.INST [`PG` |-> `[]:(num # num) option list`,
                    `explicit` |-> `gas_explicit_sites ctx shctx`]
               createBlueprintRawCopyTheory.create_blueprint_raw_copy_at_cut) >>
  disch_then (qx_choosel_then [`dst`,`w`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fnc,[]) (t,Gv,tvtn) [] (OK u,Gu,tu)` by
    (qpat_assum `!h. _ ==> gas_origin_ptr_path _ (t,Gv,tvtn) [] _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `ms = []` by
    (drule gas_origin_ptr_path_projections >> strip_tac >>
     irule ctor_observed_cut_silent >>
     qexistsl_tac [`ctx`,`(cs.cs_current_bb,LENGTH cs.cs_current_insts)`,
       `gas_explicit_sites ctx shctx`,`fnc`,`u`,`t`] >> simp[] >>
     irule RTC_MONOTONE >>
     qpat_assum `create_expr_prefix cm cs _ _ _ t ms r`
       (irule_at Any o REWRITE_RULE[create_expr_prefix_marked]) >>
     simp[create_marked_edge_def,FORALL_PROD,create_prefix_step_def] >> metis_tac[]) >>
  `q.gas_obs = gas_explicit rest u.vs_gas_readings ++ tail` by
    (qpat_assum `create_expr_prefix cm cs _ _ _ t ms r`
       (mp_then Any assume_tac create_prefix_readings) >> simp[Abbr `suffix`]) >>
  `raw_op = Var dst` by fs[unwrap_value_def,mk_ptr_def,comp_return_def] >>
  `!f i z. frag_reachable ctx fnc t f i z ==> dalloca_no_wrap i z` by
    (qpat_assum `!h. _ ==> gas_origin_ptr_path _ (s,Gi,ti) mc _ /\ _`
       (qspec_then `H` (mp_then Any mp_tac gas_origin_ptr_path_dalloca_no_wrap o CONJUNCT1 o UNDISCH)) >>
     asm_rewrite_tac[]) >>
  `!f i z. frag_reachable ctx fnc u f i z ==> dalloca_no_wrap i z` by
    (qpat_assum `gas_origin_ptr_path _ (t,Gv,tvtn) [] _`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_no_wrap) >> asm_rewrite_tac[]) >>
  `!h. valid_horizon cx st0 h q.storage_trace ==> storage_well_formed_on cx q (FST h)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!h. _ ==> vv_post h _ _ _ _ _ _ _ _ _ q _ _ _ /\ _`
       (qspec_then `h` (drule_then strip_assume_tac)) >> fs[vv_post_def]) >>
  disj2_tac >> qexistsl_tac [`bs`,`q`,`Gu`,`tu`] >> simp[] >>
  rpt conj_tac
  >- metis_tac[freshWritesTheory.not_fresh_at_mono,LESS_EQ_TRANS]
  >- metis_tac[freshWritesTheory.not_fresh_at_mono,LESS_EQ_TRANS]
  >- metis_tac[freshWritesTheory.not_fresh_at_mono,LESS_EQ_TRANS]
  >- (qpat_assum `u = r` SUBST_ALL_TAC >> FIRST_ASSUM ACCEPT_TAC)
  >- (qpat_assum `u = r` SUBST_ALL_TAC >> FIRST_ASSUM ACCEPT_TAC)
  >> qpat_assum `u = r` SUBST_ALL_TAC >> gen_tac >> disch_tac >>
  qpat_assum `!h. _ ==> gas_origin_ptr_path _ (t,Gv,tvtn) [] _ /\ _`
    (qspec_then `h` (drule_then strip_assume_tac)) >> simp[]
QED

Finalise blueprint_raw_copied_at_cut

(* A straight prologue instruction accounts for both the observed marks and
   the successor PC, without replacing the observed machine state. *)
Theorem raw_encoder_straight_edge[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  gas_origin_edge F explicit ctx func s ms (OK t) ==>
  ms = [] /\ t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = SUC s.vs_inst_idx
Proof
  rw[gas_origin_edge_def] >>
  Cases_on `step_inst_base i s` >>
  gvs[step_inst_non_invoke,exit_result_def,Once gas_events_step_def] >>
  drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem raw_encoder_prefix_rtc[local]:
  create_expr_prefix a b explicit ctx func u marks v <=>
  RTC (create_marked_edge (\p ms q. ?bb i.
    (p.vs_current_bb,p.vs_inst_idx) <> (b.cs_current_bb,LENGTH b.cs_current_insts) /\
    lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
    gas_origin_edge F explicit ctx func p ms (OK q))) (u,[]) (v,marks)
Proof
  rewrite_tac[create_expr_prefix_marked] >>
  AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, create_prefix_step_def, PAIR_EQ] >> metis_tac[]
QED

(* This application takes row-success evidence; it does not replay the
   source constructor list. s/u/t are the observed row/prologue/ABI exits. *)
Theorem create_raw_encoder_at_cuts:
  args <> [] /\ LENGTH args = LENGTH vs /\ LENGTH svs = LENGTH args /\
  compile_create_ctor_args compile_expr ce args (C 0) = (svs,C (LENGTH args)) /\
  body_inv tops ctx ce cx /\ (!K. dead_lo_ok K (DF K) lo ce cx) /\
  EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
    (int_calls_exprs args) /\
  (?H. valid_horizon cx st0 H (E (LENGTH args)).storage_trace) /\
  fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!i. i < LENGTH args ==>
    compile_expr ce (expr_type (EL i args)) (EL i args) (C i) = (V i,M i) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
      (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (M i) =
      (EL i svs,C (SUC i)) /\
    vyperState$bind (eval_expr cx (EL i args)) (read_result cx) (E i) =
      (INL (EL i vs),E (SUC i)) /\
    (expr_sim_inv ce cx env (E i) ==> expr_body_pre ce cx env (EL i args) (E i)) /\
    (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
      evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
      arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
      value_has_type tv (EL i vs) /\ value_has_type ann (EL i vs)) /\
    local_ptrs_reserved ce (C i) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    (St (SUC i)).vs_labels = (St i).vs_labels /\
    ~(St (SUC i)).vs_halted /\ (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
    (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
    (~is_word_type (lowered_value_type ce (EL i args)) ==>
      (if exprs_can_mutate ce (DROP (SUC i) args) then
        fn_has_code (M i) (C (SUC i)) func /\ ~(Mid i).vs_halted /\
        (Mid i).vs_current_bb = (M i).cs_current_bb /\
        (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
        RTC (\p q. (p.vs_current_bb,p.vs_inst_idx) <>
             ((C (SUC i)).cs_current_bb,LENGTH (C (SUC i)).cs_current_insts) /\
          ?j ms. ctor_segment_fetch func p = SOME j /\
            (M i).cs_next_id <= j.inst_id /\ j.inst_id < (C (SUC i)).cs_next_id /\
            gas_origin_edge F explicit ctx func p ms (OK q)) (Mid i) (St (SUC i)) /\
        (?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ j.inst_opcode <> PHI /\
             (C (SUC i)).cs_next_id <= j.inst_id)
       else Mid i = St (SUC i)))) /\
  expr_sim_inv ce cx env (E 0) /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ ~(St 0).vs_halted /\
  (St 0).vs_current_bb = (C 0).cs_current_bb /\ (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  (!K. valid_horizon cx st0 K (E 0).storage_trace ==>
    stmt_state_rel K ctx func ce cx (E 0) (St 0) /\
    storage_well_formed_on cx (E 0) (FST K) /\
    ghost_inv_at (DF K) lo d ce cx (E 0) G0 tn0 (St 0)) /\
  (!i g h. i < LENGTH args /\ expr_sim_inv ce cx env (E i) /\
    return_buf_frame d ce (C i) (St i) /\ alloca_history func (St i) /\
    ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
    (St i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    (!K. valid_horizon cx st0 K (E i).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E i) (St i) /\
      storage_well_formed_on cx (E i) (FST K) /\
      ghost_inv_at (DF K) lo d ce cx (E i) g h (St i)) ==>
    (is_word_type (lowered_value_type ce (EL i args)) ==>
      ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
        lower_value compile_expr ce (expr_type (EL i args)) (EL i args) (C i) =
          (op,C (SUC i)) ==>
        expr_sim_full_post (DF,lo,d,ctx,func) ce cx (EL i args)
          (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i vs) : value + exception)
            ((E (SUC i)) with gas_obs := []) g' h' (St (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i args)) ==>
      ?g' h' raw_value. eval_expr cx (EL i args) (E i) = (INL raw_value,E (SUC i)) /\
       !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
        vv_post K ctx func ce cx (EL i args) (E i) (C i) (M i) (St i)
          ((E (SUC i)) with gas_obs := []) raw_value (V i) (Mid i) /\
        vv_store_bound cx (post_value_type ce (EL i args)) (lowered_value_type ce (EL i args))
          ((E (SUC i)) with gas_obs := []) raw_value (V i) (Mid i) /\
        ptr_vv_ok cx (post_value_type ce (EL i args)) raw_value (V i)
          ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
        alloca_history func (Mid i) /\ (St i).vs_alloca_next <= (Mid i).vs_alloca_next /\
        ghost_inv_at (DF K) lo d ce cx ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
        ghost_kept_at lo ce (E i) (C i) g h (St i) g' h' /\
        (!tag op. V i = StackValue tag op /\ ~is_word_type (post_value_type ce (EL i args)) ==>
          ptr_buf_ok ce (EL i args) op g' (Mid i)) /\
        (!tag p. V i = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok ce (EL i args) p.ptr_operand g' (Mid i)) /\
        (ce.ce_is_ctor /\ vv_location (V i) = SOME LocCode ==>
          ?val. read_result cx raw_value ((E (SUC i)) with gas_obs := []) =
              (INL val,(E (SUC i)) with gas_obs := []) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type ce (EL i args)) = SOME rt /\
              eval_operand (vv_operand (V i)) (Mid i) = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside h'.t_mem (Mid i).vs_memory mem ==>
                     val_in_memory rt val (w2n w) mem)))) /\
  se = C (LENGTH args) /\ s = St (LENGTH args) /\ ee = E (LENGTH args) /\
  local_ptrs_reserved ce se /\ ci_mono (C 0) se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  capacity = prefix_bound +
    abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) /\
  capacity < dimword (:256) /\
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  gas_origin_edge F explicit ctx func s am (OK su) /\
  compile_copy_memory_dynamic buf.buf_operand (Var src) (Var len) a = ((),b) /\
  fn_has_code a b func /\ emit_op ADD [buf.buf_operand;Var len] b = (dst_op,st) /\
  fn_has_code b st func /\ w2n nword <= prefix_bound /\
  not_fresh_at (C 0) src /\ not_fresh_at (C 0) len /\
  lookup_var src (St 0) = SOME p /\ lookup_var len (St 0) = SOME nword /\
  ptr_covers G0 tn0 src (St 0) (w2n nword) /\ op_taint tn0 (Var len) = {} /\
  w2n p + w2n nword <= (St 0).vs_alloca_next /\
  gas_origin_edge F explicit ctx func su bm (OK sv) /\
  gas_origin_edge F explicit ctx func sv cm (OK u) /\
  compile_abi_encode_values_to_buf ce dst_op (ZIP (svs,MAP (lowered_value_type ce) args))
    st = (alen,en) /\ fn_has_code st en func /\
  create_expr_prefix st en explicit ctx func u encmarks t /\
  (t.vs_current_bb,t.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts) /\
  c 0 = en /\ r 0 = t /\ r n = bad /\
  (!k. k < n ==>
    (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
    create_expr_prefix (c k) (c (SUC k)) explicit ctx func (r k) (chunk k) (r (SUC k))) /\
  lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
  get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
  ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value;off;sz]) \/
   (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value;off;sz;salt])) /\
  eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w /\
  (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_no_wrap inst z) ==>
  am = [] /\ bm = [] /\ cm = [] /\ encmarks = [] /\
  ?bytes Gt tt.
    encode_create_ctor_args (get_tenv cx) (MAP expr_type args) vs = SOME bytes /\
    eval_operand alen t = SOME (n2w (LENGTH bytes)) /\
    (!x. alen = Var x ==> not_fresh_at en x) /\ op_taint tt alen = {} /\
    wb_frame ce (E 0) ee (C 0) (St 0) t /\
    lookup_var len t = SOME nword /\
    expr_sim_inv ce cx env ee /\ return_buf_frame d ce en t /\ alloca_history func t /\
    ~(t.vs_halted) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    local_ptrs_reserved ce en /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_no_wrap inst z) /\
    (!K. valid_horizon cx st0 K ee.storage_trace ==>
      stmt_state_rel K ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST K) /\
      ghost_inv_at (DF K) lo d ce cx ee Gt tt t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "payload"
QED
Resume create_raw_encoder_at_cuts[payload]:
  mp_tac (PURE_REWRITE_RULE[COND_CLAUSES,AND_CLAUSES,IMP_CLAUSES,NOT_CLAUSES]
            (Q.INST [`raw` |-> `T`] create_ctor_payload_length)) >>
  (impl_tac >- suspend "premises") >>
  qpat_assum `args <> []` (simp_tac bool_ss o single) >>
  disch_then strip_assume_tac >>
  rename1 `encode_create_ctor_args _ _ _ = SOME bytes` >>
  qpat_assum `!D. gas_origin_ptr_path _ _ [] _ /\ _`
    (qspec_then `ARB` (map_every assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (u,_,_) [] (OK t,Gexit,texit)` >>
  suspend "silence"
QED
Resume create_raw_encoder_at_cuts[premises]:
  qpat_assum `args <> []` (simp_tac bool_ss o single) >>
  pure_rewrite_tac[GSYM raw_encoder_prefix_rtc] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume create_raw_encoder_at_cuts[silence]:
  `s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts` by
    (`PRE (LENGTH args) < LENGTH args` by (Cases_on `args` >> fs[]) >>
     `SUC (PRE (LENGTH args)) = LENGTH args` by decide_tac >>
     qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `PRE (LENGTH args)` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     qpat_assum `s = St _` (fn hs => qpat_assum `se = C _` (fn hc =>
       pure_rewrite_tac [hs,hc])) >>
     qpat_assum `SUC (PRE _) = _` (SUBST_ALL_TAC) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `am = [] /\ su.vs_current_bb = a.cs_current_bb /\ su.vs_inst_idx = LENGTH a.cs_current_insts` by
    (`?tmp. emit_op ALLOCA [Lit (n2w capacity)] se = (tmp,a)` by
       (Cases_on `emit_op ALLOCA [Lit (n2w capacity)] se` >>
        qpat_assum `compile_alloc_buffer _ _ = _` (mp_tac o PURE_REWRITE_RULE
          [compile_alloc_buffer_def,comp_bind_def,comp_return_def]) >>
        qpat_assum `emit_op ALLOCA _ _ = _` (fn th => simp_tac (srw_ss()) [th,comp_return_def,LET_THM])) >>
     pop_assum strip_assume_tac >>
     drule_all (Q.INST [`opc` |-> `ALLOCA`] emit_op_fetch_boundary) >> strip_tac >>
     drule_all (SIMP_RULE (srw_ss()) [is_terminator_def]
       (Q.INST [`i` |-> `mk_inst id ALLOCA ops outs`] raw_encoder_straight_edge)) >>
     strip_tac >> fs[]) >>
  `bm = [] /\ sv.vs_current_bb = b.cs_current_bb /\ sv.vs_inst_idx = LENGTH b.cs_current_insts` by
    (`emit_void MCOPY [buf.buf_operand;Var src;Var len] a = ((),b)` by fs[compile_copy_memory_dynamic_def] >>
     drule_all emit_void_fetch_boundary >> strip_tac >>
     qmatch_asmsub_rename_tac `get_instruction copybb _ = SOME (mk_inst _ MCOPY _ _)` >>
     `?bb. lookup_block su.vs_current_bb func.fn_blocks = SOME bb /\
           get_instruction bb su.vs_inst_idx =
             SOME (mk_inst a.cs_next_id MCOPY [buf.buf_operand;Var src;Var len] [])` by
       (qexists_tac `copybb` >> fs[]) >>
     pop_assum strip_assume_tac >>
     drule_all (SIMP_RULE (srw_ss()) [is_terminator_def]
       (Q.INST [`i` |-> `mk_inst id MCOPY ops outs`] raw_encoder_straight_edge)) >> strip_tac >> fs[]) >>
  `cm = []` by
    (drule_all (Q.INST [`opc` |-> `ADD`] emit_op_fetch_boundary) >> strip_tac >>
     drule_all (SIMP_RULE (srw_ss()) [is_terminator_def]
       (Q.INST [`i` |-> `mk_inst id ADD ops outs`] raw_encoder_straight_edge)) >> simp[]) >>
  `encmarks = []` by
    (irule ctor_observed_cut_silent >>
     qexistsl_tac [`ctx`,`(en.cs_current_bb,LENGTH en.cs_current_insts)`,`explicit`,`func`,`t`,`u`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (irule RTC_MONOTONE >>
         qpat_assum `create_expr_prefix st en _ _ _ _ _ _`
           (irule_at Any o REWRITE_RULE[create_expr_prefix_marked]) >>
         simp[create_marked_edge_def,FORALL_PROD,create_prefix_step_def,PAIR_EQ] >> metis_tac[]) >>
     drule gas_origin_ptr_path_projections >> simp[]) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bytes`,`Gexit`,`texit`] >> suspend "entry"
QED
Resume create_raw_encoder_at_cuts[entry]:
  qhdtm_assum `abi_encode_saved_state`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[abi_encode_saved_state_def]) >>
  `lookup_var len t = SOME nword` by
    (qpat_assum `wb_frame ce (E 0) ee (C 0) (St 0) t`
       (irule o cj 1 o REWRITE_RULE[wb_frame_def]) >> simp[]) >>
  `!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_no_wrap inst z` by
    (qpat_assum `gas_origin_ptr_path _ _ [] (OK u,_,_)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_no_wrap) >>
     asm_rewrite_tac[]) >>
  `!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_no_wrap inst z` by
    (qpat_assum `gas_origin_ptr_path _ _ [] (OK t,_,_)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_no_wrap) >>
     asm_rewrite_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `ee = E _` (fn he =>
       qpat_assum `?H. valid_horizon cx st0 H (E _).storage_trace`
         (qx_choose_then `hz` (assume_tac o PURE_REWRITE_RULE [GSYM he]))) >>
     qpat_assum `!K. valid_horizon cx st0 K ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
       (qspec_then `hz` (drule_then
          (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp o CONJUNCT1)))) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `se` >> simp[])
  >> rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `se` >> simp[]
QED
Finalise create_raw_encoder_at_cuts

(* Join the two raw-payload replays at the input of the fixed MLOAD/ADD
   suffix.  The source continuation already contains the read address. *)
Theorem create_blueprint_raw_keyword_entry:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint T) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  EVERY (create_operand_completed_ok cx) (create_operand_order (CreateFromBlueprint T) hs args) /\
  e = HD ctors /\ later = amount::((if hs then [salt] else []) ++ [off]) /\
  eval_operand target_op s = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at ca x) /\
  expr_sim_inv ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca s /\ alloca_history fnc s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx fnc s f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p s /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p Gi ti s) /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\ s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) sca = (vv,scm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce (MAP gas_shadow_expr later)) vv scm = (ssaved,scs) /\
  unwrap_value ce ssaved scs = (raw_op,scu) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cm,sca,scm) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cu,sca,scu) /\
  fn_has_code cm cs fnc /\ fn_has_code cu cprep fnc /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\ emit_op ADD [raw_op;Lit 32w] cl = (data,cprep) /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc s mc m /\
  m.vs_current_bb = cm.cs_current_bb /\ m.vs_inst_idx = LENGTH cm.cs_current_insts /\
  create_expr_prefix cm cs (gas_explicit_sites ctx shctx) ctx fnc m ms r /\
  r.vs_current_bb = cs.cs_current_bb /\ r.vs_inst_idx = LENGTH cs.cs_current_insts /\
  create_expr_prefix cs cu (gas_explicit_sites ctx shctx) ctx fnc r mu u /\
  u.vs_current_bb = cu.cs_current_bb /\ u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  create_expr_prefix cu cl (gas_explicit_sites ctx shctx) ctx fnc u ml b /\
  b.vs_current_bb = cl.cs_current_bb /\ b.vs_inst_idx = LENGTH cl.cs_current_insts /\
  create_expr_prefix cl cprep (gas_explicit_sites ctx shctx) ctx fnc b ma t /\
  t.vs_current_bb = cprep.cs_current_bb /\ t.vs_inst_idx = LENGTH cprep.cs_current_insts /\
  bind (eval_exprs cx (ctors ++ later))
    (\vs. eval_create_operands cx (CreateFromBlueprint T) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (mc ++ (ms ++ (mu ++ (ml ++ ma ++ rest)))) s.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?bs q G tn.
    ctors = [e] /\
    bind (eval_exprs cx (amount::((if hs then [salt] else []) ++ [off])))
      (\kvs. eval_create_operands cx (CreateFromBlueprint T) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(BytesV bs::kvs))) q = (res,out) /\
    valid_horizon cx st0 H q.storage_trace /\
    eval_operand len t = SOME (n2w (LENGTH bs)) /\
    (!x. len = Var x ==> not_fresh_at cprep x) /\
    eval_operand target_op t = SOME aw /\
    (!x. target_op = Var x ==> not_fresh_at cprep x) /\
    expr_sim_inv ce cx env q /\ local_ptrs_reserved ce cprep /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cprep x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cprep x) /\
    return_buf_frame d ce cprep t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_no_wrap i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q G tn t) /\
    ~t.vs_halted /\ t.vs_current_bb = cprep.cs_current_bb /\
    t.vs_inst_idx = LENGTH cprep.cs_current_insts /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?k. ctors = [e] /\ expr_type e = BaseT (BytesT (Dynamic k))` by
    (drule expr_body_pre_static_facts >> strip_tac >>
     Cases_on `hs` >> fs[well_typed_expr_def,create_arg_types_ok_def,MAP_EQ_CONS] >>
     gvs[] >> metis_tac[]) >>
  qpat_x_assum `e = HD ctors` kall_tac >>
  `create_operand_completed_ok cx e` by
    (qpat_assum `args = _` (fn th => qhdtm_assum `EVERY` (mp_tac o REWRITE_RULE[th])) >>
     qpat_assum `ctors = [e]` (fn th => pure_rewrite_tac[th]) >>
     rpt (pop_assum kall_tac) >> Cases_on `hs` >> simp[create_operand_order_def]) >>
  `expr_body_pre ce cx env e p` by
    (irule blueprint_keyword_body_pre >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
     SOME (BaseTV (BytesT (Dynamic k)))` by
    (`well_typed_expr env e` by (drule_then strip_assume_tac expr_body_pre_static_facts >> simp[]) >>
     drule_all expr_sim_inv_type_evaluates >>
     simp[evaluate_type_def] >> reverse IF_CASES_TAC >> simp[]) >>
  `fn_has_code cu cl fnc` by
    metis_tac[fn_has_code_split,exprSimAccountsTheory.emit_op_extends_next_var] >>
  `!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (gen_tac >> disch_tac >>
     `MEM fnc ctx.ctx_functions` by fs[expr_sim_full_code_def] >>
     drule_all body_inv_no_phi >> simp[]) >>
  `compile_create_blueprint_args compile_expr ce T later [e] ca = ((data,len),cprep)` by
    (qpat_x_assum `later = _` kall_tac >>
     qpat_x_assum `expr_type e = _` kall_tac >>
     simp[compile_create_blueprint_args_def,comp_bind_def,comp_return_def]) >>
  qabbrev_tac `kont = \v. bind (eval_exprs cx later)
    (\vs. eval_create_operands cx (CreateFromBlueprint T) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::v::vs))` >>
  `!v. storage_trace_frame (kont v)` by
    simp[Abbr `kont`,evaluate_storage_trace_frame,storage_trace_frame_bind_all,
         storage_trace_frame_create_operands] >>
  `bind (bind (eval_expr cx e) (read_result cx)) kont p = (res,out)` by
    fs[Abbr `kont`,create_copy_source_cons] >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?bs q G tn.
     kont (BytesV bs) q = (res,out) /\ valid_horizon cx st0 H q.storage_trace /\
     q.gas_obs = gas_explicit (ml ++ ma ++ rest) u.vs_gas_readings ++ tail /\
     expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bs) raw_op u /\
     eval_operand target_op u = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at cu x) /\
     expr_sim_inv ce cx env q /\ local_ptrs_reserved ce cu /\
     (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
     (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
     return_buf_frame d ce cu u /\ alloca_history fnc u /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
     (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_no_wrap i z) /\
     (!h. valid_horizon cx st0 h q.storage_trace ==>
       stmt_state_rel h ctx fnc ce cx q u /\ storage_well_formed_on cx q (FST h) /\
       ghost_inv_at (DF h) lo d ce cx q G tn u) /\ ~u.vs_halted` by
    (Cases_on `exprs_can_mutate ce later`
     >- (drule_all blueprint_raw_copied_at_cut >> strip_tac
         >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
         disj2_tac >> qexistsl_tac [`bs`,`q`,`G`,`tn`] >>
         rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)
     >> drule_all blueprint_raw_retained_at_cut >> strip_tac
     >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
     disj2_tac >> qexistsl_tac [`bs`,`q`,`G'`,`tn'`] >>
     rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  pop_assum strip_assume_tac >- (disj1_tac >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all blueprint_raw_finish_at_cut >> strip_tac >>
  disj2_tac >> qexistsl_tac [`bs`,`q`,`G`,`tn`] >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `later = _` SUBST_ALL_TAC >> fs[Abbr `kont`]) >>
  rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC
QED

(* The post-encoder ADD does not consume source observations or change
   reserved variables. Its sole ghost update is at the new output. *)
Theorem create_raw_total_add_entry_at_cuts:
  emit_op ADD [lhs;rhs] a = (sum_op,b) /\ fn_has_code a b fn /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  create_expr_prefix a b explicit ctx fn s chunk t /\ ~s.vs_halted /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!f i z. frag_reachable ctx fn s f i z ==> dalloca_no_wrap i z) /\
  local_ptrs_reserved ce a /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history fn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. valid_horizon cx st0 H p.storage_trace ==>
    stmt_state_rel H ctx fn ce cx p s /\ storage_well_formed_on cx p (FST H) /\
    ghost_inv_at (DF H) lo d ce cx p G tn s) ==>
  chunk = [] /\ t.vs_gas_readings = s.vs_gas_readings /\
  return_buf_frame d ce b t /\ alloca_history fn t /\ ~t.vs_halted /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!f i z. frag_reachable ctx fn t f i z ==> dalloca_no_wrap i z) /\
  local_ptrs_reserved ce b /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at b x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at b x) /\
  ?out u v G' tn'.
    sum_op = Var out /\ not_fresh_at b out /\
    eval_operand lhs s = SOME u /\ eval_operand rhs s = SOME v /\
    eval_operand sum_op t = SOME (u + v) /\
    G' = step_prov PG G (mk_inst a.cs_next_id ADD [lhs;rhs] [out])
      (update_var out (u + v) s) /\
    tn' = step_taint (mk_inst a.cs_next_id ADD [lhs;rhs] [out]) s
      (update_var out (u + v) s) tn /\
    (!x. not_fresh_at a x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!H. valid_horizon cx st0 H p.storage_trace ==>
      stmt_state_rel H ctx fn ce cx p t /\ storage_well_formed_on cx p (FST H) /\
      ghost_inv_at (DF H) lo d ce cx p G' tn' t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (Q.INST [`opc` |-> `ADD`] blueprint_raw_scalar_step |>
             SIMP_RULE (srw_ss()) [is_terminator_def]) >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = OK _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [step_add_eq, AllCaseEqs()]) >>
  rename1 `eval_operand lhs s = SOME u` >>
  rename1 `eval_operand rhs s = SOME v` >>
  rename1 `sum_op = Var out` >>
  qpat_x_assum `update_var out _ s = raw` (SUBST_ALL_TAC o SYM) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts a b) /\
   b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
   b.cs_current_bb = a.cs_current_bb /\ ~not_fresh_at a out` by
    (drule emitted_insts_emit_op >> strip_tac >> drule emit_op_facts >>
     strip_tac >> gvs[mk_inst_def]) >>
  `state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_gas_readings = s.vs_gas_readings /\ eval_operand sum_op t = SOME (u + v) /\
   (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s)` by
    (simp[update_var_def, state_frame_def, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, SF CONJ_ss] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H p.storage_trace ==>
    stmt_state_rel H ctx fn ce cx p s /\ ghost_inv_at (DF H) lo d ce cx p G tn s` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  suspend "frames"
QED
Resume create_raw_total_add_entry_at_cuts[frames]:
  drule_all blueprint_raw_load_add_frame >> strip_tac >>
  `!f i z. frag_reachable ctx fn t f i z ==> dalloca_no_wrap i z` by
    (qpat_assum `create_expr_prefix a b explicit ctx fn s chunk t`
       (mp_tac o MATCH_MP (SRULE[GSYM AND_IMP_INTRO] blueprint_raw_reach_at_cut)) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `local_ptrs_reserved ce b /\
   (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at b x) /\
   (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at b x)` by
    metis_tac[local_ptrs_reserved_next_var, freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `t = (update_var _ _ _ with vs_inst_idx := _)` kall_tac >>
  simp[] >> suspend "ghost"
QED
Resume create_raw_total_add_entry_at_cuts[ghost]:
  qabbrev_tac `ins = mk_inst a.cs_next_id ADD [lhs;rhs] [out]` >>
  qabbrev_tac `raw = update_var out (u + v) s` >>
  qabbrev_tac `Gp = step_prov PG G ins raw` >>
  qabbrev_tac `tp = step_taint ins s raw tn` >>
  `tp.t_mem = tn.t_mem /\ tp.t_stor = tn.t_stor /\
   tp.t_imm = tn.t_imm /\ tp.t_trans = tn.t_trans /\
   (!x. x <> out ==> FLOOKUP Gp x = FLOOKUP G x /\
                     op_taint tp (Var x) = op_taint tn (Var x))` by
    simp[Abbr `Gp`, Abbr `tp`, Abbr `ins`, Abbr `raw`,
         typedCopyOriginPtrBaseTheory.typed_copy_origin_ptr_binop_ghost_frame] >>
  `!x. not_fresh_at a x ==> lookup_var x t = lookup_var x t /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tp (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (rpt strip_tac >> metis_tac[] >> NO_TAC) >>
  gen_tac >> strip_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
    (drule_then strip_assume_tac) >>
  irule ghost_inv_at_exterior_frame >>
  qexistsl_tac [`G`,`p`,`t`,`a`,`tn`] >> simp[]
QED
Finalise create_raw_total_add_entry_at_cuts

Theorem blueprint_abi_bind_append[local]:
  !xs ys k.
    bind (eval_exprs cx (xs ++ ys)) k =
    bind (eval_exprs cx xs) (\vs. bind (eval_exprs cx ys) (\ws. k (vs ++ ws)))
Proof
  Induct >- simp[blueprint_eval_nil_action,bind_return,ETA_AX] >>
  simp[create_copy_source_cons]
QED

Theorem blueprint_abi_fetch_back[local]:
  create_expr_prefix a b explicit ctx func s ms t /\
  a.cs_next_id <= b.cs_next_id /\
  (?j. ctor_segment_fetch func t = SOME j /\ b.cs_next_id <= j.inst_id) ==>
  ?j. ctor_segment_fetch func s = SOME j /\ a.cs_next_id <= j.inst_id
Proof
  simp[create_expr_prefix_marked] >> once_rewrite_tac[RTC_CASES1] >>
  simp[EXISTS_PROD,create_marked_edge_def,create_prefix_step_def,frag_ids_def] >>
  rpt strip_tac >> gvs[ctor_segment_fetch_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem blueprint_abi_rows_fetch[local]:
  !n i. i + n = N /\
    (?j. ctor_segment_fetch func (St N) = SOME j /\ (C N).cs_next_id <= j.inst_id) /\
    (!k. k < N ==> (C k).cs_next_id <= (M k).cs_next_id /\
      (M k).cs_next_id <= (C (SUC k)).cs_next_id /\
      create_expr_prefix (C k) (M k) explicit ctx func (St k) (Chunk k) (Mid k) /\
      create_expr_prefix (M k) (C (SUC k)) explicit ctx func (Mid k) (Snap k) (St (SUC k))) ==>
    ?j. ctor_segment_fetch func (St i) = SOME j /\ (C i).cs_next_id <= j.inst_id
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `i < N /\ SUC i + n = N` by decide_tac >>
  qpat_assum `!k. k < N ==> _` (qspec_then `i` (drule_then strip_assume_tac)) >>
  `?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ (C (SUC i)).cs_next_id <= j.inst_id`
    by (qpat_assum `!i. i + n = N /\ _ ==> _` (qspec_then `SUC i` mp_tac) >>
        simp_tac bool_ss [] >> metis_tac[]) >>
  metis_tac[blueprint_abi_fetch_back]
QED

Theorem blueprint_abi_silent_band[local]:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_expr_prefix a b explicit ctx func s ms t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  gas_origin_path T explicit ctx func s [] (OK t) ==>
  ms = []
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  irule ctor_observed_cut_silent >>
  qexistsl [`ctx`,`(b.cs_current_bb,LENGTH b.cs_current_insts)`,`explicit`,`func`,`t`,`s`] >>
  simp[] >> qpat_x_assum `RTC _ _ _` mp_tac >> match_mp_tac RTC_MONOTONE >>
  simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def,PULL_EXISTS]
QED

(* The nonraw payload's encoder is reached through the actual completed
   constructor rows. The final two prefixes are the allocation and encode
   bands, not part of any source operand. *)
Theorem create_blueprint_abi_keyword_entry:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint F) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  EVERY (create_operand_completed_ok cx) (create_operand_order (CreateFromBlueprint F) hs args) /\
  MEM func ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  later = amount::((if hs then [salt] else []) ++ [off]) /\
  eval_operand target_op (St 0) = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at (C 0) x) /\
  local_ptrs_reserved ce (C 0) /\ (!K. dead_lo_ok K (DF K) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  return_buf_frame d ce (C 0) (St 0) /\ alloca_history func (St 0) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_no_wrap i z) /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at (DF K) lo d ce cx p0 G0 tn0 (St 0)) /\
  expr_sim_inv ce cx env p0 /\ ~(St 0).vs_halted /\
  (St 0).vs_current_bb = (C 0).cs_current_bb /\ (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  LENGTH svs = LENGTH ctors /\
  se = C (LENGTH ctors) /\ s = St (LENGTH ctors) /\
  compile_create_ctor_args compile_expr ce ctors (C 0) = (svs,se) /\
  compile_create_blueprint_args compile_expr ce F later ctors (C 0) = ((data,len),en) /\
  (!i. i < LENGTH ctors ==>
    compile_expr ce (expr_type (EL i ctors)) (EL i ctors) (C i) = (V i,M i) /\
    compile_expr ce (expr_type (EL i ctors)) (gas_shadow_expr (EL i ctors)) (Sh i) = (V i,SM i) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) ctors))
      (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)) (M i) =
      (EL i svs,C (SUC i)) /\
    (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
    (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
    R i = (Chunk i ++ Snap i) ++ R (SUC i) /\
    create_expr_prefix (C i) (M i) (gas_explicit_sites ctx shctx) ctx func
      (St i) (Chunk i) (Mid i) /\
    (Mid i).vs_current_bb = (M i).cs_current_bb /\
    (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
    create_expr_prefix (M i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
      (Mid i) (Snap i) (St (SUC i)) /\
    fn_has_code (M i) (C (SUC i)) func /\ ci_mono (C 0) (C i) /\
    (is_word_type (lowered_value_type ce (EL i ctors)) ==>
      compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) ctors))
        (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)) (SM i) =
        (EL i svs,Sh (SUC i)) /\
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,C (SUC i),Sh i,Sh (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i ctors)) ==>
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,M i,Sh i,SM i))) /\
  (ctors = [] ==> t = St 0 /\ R 0 = rest) /\
  (ctors <> [] ==>
    capacity = abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) ctors)) /\
    capacity < dimword (:256) /\
    compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
    su.vs_current_bb = a.cs_current_bb /\ su.vs_inst_idx = LENGTH a.cs_current_insts /\
    create_expr_prefix se a (gas_explicit_sites ctx shctx) ctx func s am su /\
    compile_abi_encode_values_to_buf ce buf.buf_operand (ZIP (svs,MAP (lowered_value_type ce) ctors))
      a = (len,en) /\ fn_has_code a en func /\
    create_expr_prefix a en (gas_explicit_sites ctx shctx) ctx func su encmarks t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    R (LENGTH ctors) = am ++ encmarks ++ rest /\
    c 0 = en /\ r 0 = t /\ r n = bad /\
    (!k. k < n ==> (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
      create_expr_prefix (c k) (c (SUC k)) (gas_explicit_sites ctx shctx) ctx func
        (r k) (chunk k) (r (SUC k))) /\
    lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
    get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
    ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value;offop;sz]) \/
     (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value;offop;sz;salto])) /\
    eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w) /\
  bind (eval_exprs cx (ctors ++ later))
    (\vs. eval_create_operands cx (CreateFromBlueprint F) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p0 = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?cvs p G tn.
    LENGTH cvs = LENGTH ctors /\ eval_exprs cx ctors p0 = (INL cvs,p) /\
    bind (eval_exprs cx (amount::((if hs then [salt] else []) ++ [off])))
      (\kvs. eval_create_operands cx (CreateFromBlueprint F) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) p = (res,out) /\
    valid_horizon cx st0 H p.storage_trace /\
    (?bs. encode_create_ctor_args (get_tenv cx) (MAP expr_type ctors) cvs = SOME bs /\
      eval_operand len t = SOME (n2w (LENGTH bs))) /\
    (!x. len = Var x ==> not_fresh_at en x) /\
    eval_operand target_op t = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at en x) /\
    expr_sim_inv ce cx env p /\ local_ptrs_reserved ce en /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    return_buf_frame d ce en t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_no_wrap i z) /\
    (!K. valid_horizon cx st0 K p.storage_trace ==>
      stmt_state_rel K ctx func ce cx p t /\ storage_well_formed_on cx p (FST K) /\
      ghost_inv_at (DF K) lo d ce cx p G tn t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    p.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `k = \vs. bind (eval_exprs cx later)
    (\ws. eval_create_operands cx (CreateFromBlueprint F) hs rof
       (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(vs ++ ws)))` >>
  `bind (eval_exprs cx ctors) k p0 = (res,out)` by
    fs[Abbr `k`,blueprint_abi_bind_append] >>
  `!vs. storage_trace_frame (k vs)` by
    simp[Abbr `k`,blueprint_read_list_frame,evaluate_storage_trace_frame,
         storage_trace_frame_bind_all,storage_trace_frame_create_operands] >>
  Cases_on `ctors = []` >- suspend "empty" >>
  qpat_x_assum `ctors <> [] ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  suspend "nonempty"
QED

Resume create_blueprint_abi_keyword_entry[empty]:
  gvs[compile_create_blueprint_args_def,comp_return_def,blueprint_eval_nil_action,bind_return] >>
  `valid_horizon cx st0 H p0.storage_trace` by
    (qpat_assum `k [] p0 = _` (mp_then Any irule vyperStorageFootprintTheory.valid_horizon_frame) >> simp[]) >>
  disj2_tac >> qexistsl [`p0`,`G0`,`tn0`] >>
  simp[encode_create_ctor_args_def,eval_operand_def,return_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_blueprint_abi_keyword_entry[nonempty]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!i. MEM i (fn_insts func) ==> i.inst_opcode <> PHI` by suspend "no_phi" >>
  `!i. i < LENGTH ctors ==> create_operand_completed_ok cx (EL i ctors)` by
    (qpat_assum `args = _` (fn th => qhdtm_assum `EVERY` (mp_tac o REWRITE_RULE[th])) >>
     Cases_on `hs` >> simp[create_operand_order_def,EVERY_APPEND] >>
     metis_tac[EVERY_MEM,EL_MEM]) >>
  `!i p. i < LENGTH ctors /\ expr_sim_inv ce cx env p ==>
         expr_body_pre ce cx env (EL i ctors) p` by
    (rpt strip_tac >> irule blueprint_keyword_body_pre >> simp[] >>
     qpat_assum `expr_body_pre ce cx env (Call _ _ _ _) entry` (irule_at Any) >>
     simp[MEM_APPEND,EL_MEM]) >>
  `ci_mono (C 0) se /\ ci_mono se a /\ ci_mono a en` by
    metis_tac[ci_mono_compile_create_ctor_args,ci_mono_compile_expr_sa,
      ci_mono_compile_alloc_buffer,ci_mono_compile_abi_encode_values_to_buf,SND] >>
  `!i. i < LENGTH ctors ==> (C i).cs_next_id <= (M i).cs_next_id /\
                          (M i).cs_next_id <= (C (SUC i)).cs_next_id` by
    (rpt strip_tac >> qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     metis_tac[ci_mono_compile_expr_sa,ci_mono_compile_snapshot_vv,ci_mono_def,SND]) >>
  `gas_origin_edge F (gas_explicit_sites ctx shctx) ctx func s am (OK su) /\
   (?j. ctor_segment_fetch func s = SOME j /\ se.cs_next_id <= j.inst_id)` by suspend "alloc_edge" >>
  `!i. i <= LENGTH ctors ==> ?j. ctor_segment_fetch func (St i) = SOME j /\
     j.inst_opcode <> PHI /\ (C i).cs_next_id <= j.inst_id` by suspend "fetch" >>
  mp_tac (Q.INST [`args` |-> `ctors`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:eval_result``] create_ctor_rows_at_cuts))) >>
  (impl_tac >- suspend "row_pre") >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (qx_choosel_then [`cvs`,`E`,`gf`,`tf`] (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "payload"
QED

Resume create_blueprint_abi_keyword_entry[no_phi]:
  rpt strip_tac >> drule bodySimTheory.body_inv_contract >>
  disch_then (strip_assume_tac o MATCH_MP contractInvContextPropsTheory.contract_inv_lowering_context) >>
  fs[vyperCompilerTheory.lowering_context_ok_def,vyperCompilerTheory.ptr_ok_check_def,EVERY_MEM] >>
  qpat_assum `!fn. MEM fn _ ==> fn_ptr_ok_check _ _ /\ _`
    (qspec_then `func` (drule_then strip_assume_tac)) >> metis_tac[]
QED

Resume create_blueprint_abi_keyword_entry[alloc_edge]:
  `?op. emit_op ALLOCA [Lit (n2w capacity)] se = (op,a)` by
    (Cases_on `emit_op ALLOCA [Lit (n2w capacity)] se` >>
     fs[compile_alloc_buffer_def,comp_bind_def,comp_return_def]) >>
  `s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts` by
    (Cases_on `LENGTH ctors` >> gvs[LENGTH_NIL] >>
     qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `n'` mp_tac) >> simp[]) >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
  conj_tac
  >- (irule raw_observed_prefix_alloc >>
      qexistsl_tac [`se`,`a`,`buf`,`capacity`] >> gvs[]) >>
  qexists_tac `mk_inst se.cs_next_id ALLOCA [Lit (n2w capacity)] [tmp]` >>
  gvs[ctor_segment_fetch_def,mk_inst_def]
QED

Resume create_blueprint_abi_keyword_entry[fetch]:
  rpt strip_tac >>
  `?j. ctor_segment_fetch func (St i) = SOME j /\ (C i).cs_next_id <= j.inst_id` by
    (irule blueprint_abi_rows_fetch >>
     qexistsl [`Chunk`,`M`,`Mid`,`LENGTH ctors`,`Snap`,`ctx`,`gas_explicit_sites ctx shctx`,`LENGTH ctors - i`] >>
     rpt conj_tac >> TRY decide_tac >> TRY (metis_tac[] >> NO_TAC) >>
     gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `k'` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     simp[]) >>
  qpat_x_assum `ctor_segment_fetch func (St i) = SOME j'` (fn th =>
    qexists_tac `j'` >> conj_tac >- ACCEPT_TAC th >> simp[] >> mp_tac th) >>
  simp[ctor_segment_fetch_def,AllCaseEqs()] >>
  metis_tac[lookup_block_get_instruction_fn_insts]
QED

Resume create_blueprint_abi_keyword_entry[row_pre]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `!x. not_fresh_at (C 0) x ==> not_fresh_at (C i) x` by
     metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `local_ptrs_reserved ce (C i)` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  `SUC i <= LENGTH ctors` by decide_tac >>
  qpat_assum `!i. i <= LENGTH ctors ==> ?j. _` (qspec_then `SUC i` (drule_then strip_assume_tac)) >>
  qmatch_asmsub_rename_tac `ctor_segment_fetch func (St (SUC i)) = SOME next` >>
  qpat_assum `!i. i < LENGTH ctors ==> (C i).cs_next_id <= _ /\ _`
    (qspec_then `i` (drule_then strip_assume_tac)) >>
  simp[APPEND_ASSOC] >>
  conj_tac
  >- (disch_tac >> res_tac >> simp[] >>
      irule raw_observed_prefix_join >> simp[] >>
      qexistsl_tac [`M i`,`Mid i`] >> simp[]) >>
  disch_tac >> res_tac >> simp[] >> rpt disch_tac >>
  irule blueprint_abi_silent_band >>
  qexistsl_tac [`M i`,`C (SUC i)`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`Mid i`,`St (SUC i)`] >> simp[]
QED

Resume create_blueprint_abi_keyword_entry[payload]:
  qabbrev_tac `ee = E (LENGTH ctors)` >>
  `EVERY (\call. FST call = NONE /\ IS_SOME (supported_function_decl tops call Internal))
     (int_calls_exprs ctors)` by suspend "calls" >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by fs[expr_sim_inv_split_def,expr_sim_inv_mods_def] >>
  `((C 0):compile_state).cs_next_var <= se.cs_next_var /\ se.cs_next_var <= en.cs_next_var /\
   ((C 0):compile_state).cs_next_var <= en.cs_next_var` by
     (fs[ci_mono_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!x. not_fresh_at (C 0) x ==> not_fresh_at se x /\ not_fresh_at en x` by
     metis_tac[not_fresh_at_mono] >>
  qmatch_asmsub_rename_tac `compile_abi_encode_values_to_buf _ _ _ _ = (alen,en)` >>
  mp_tac (Q.INST [`raw` |-> `F`, `args` |-> `ctors`, `vs` |-> `cvs`,
                  `explicit` |-> `gas_explicit_sites ctx shctx`,
                  `st` |-> `a`, `dst_op` |-> `buf.buf_operand`, `u` |-> `su`,
                  `off` |-> `offop`, `salt` |-> `salto`]
    create_ctor_payload_length |>
    PURE_REWRITE_RULE[COND_CLAUSES,AND_CLAUSES,IMP_CLAUSES,NOT_CLAUSES,ADD_CLAUSES,REFL_CLAUSE]) >>
  (impl_tac >- suspend "producer_pre") >>
  qpat_assum `ctors <> []` (simp_tac bool_ss o single) >>
  disch_then strip_assume_tac >>
  rename1 `encode_create_ctor_args _ _ _ = SOME bs` >>
  qpat_assum `!D. gas_origin_ptr_path _ _ [] _ /\ _`
    (qspec_then `ARB` (map_every assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (su,_,_) [] (OK t,geout,teout)` >>
  suspend "finish"
QED

Resume create_blueprint_abi_keyword_entry[calls]:
  qpat_assum `expr_body_pre ce cx env (Call _ _ _ _) entry`
    (mp_tac o REWRITE_RULE [expr_body_pre_split_def]) >>
  strip_tac >> drule expr_body_pre_mods_int_calls >> strip_tac >>
  drule body_inv_main_code >> strip_tac >>
  simp[EVERY_MEM] >> qx_gen_tac `call` >> disch_tac >>
  `MEM call (int_calls_expr (Call ann (CreateTarget (CreateFromBlueprint F) hs rof ks) args df))` by
    (Cases_on `hs` >> gvs[int_calls_expr_def]) >>
  qpat_assum `EVERY (\c. FST c = NONE) _`
    (qspec_then `call` (drule_then assume_tac) o REWRITE_RULE[EVERY_MEM]) >>
  qpat_assum `EVERY (\c. ?tops. _) _`
    (qspec_then `call` (drule_then strip_assume_tac) o REWRITE_RULE[EVERY_MEM]) >>
  Cases_on `call` >> gvs[]
QED

Resume create_blueprint_abi_keyword_entry[producer_pre]:
  qpat_assum `ctors <> []` (simp_tac bool_ss o single) >>
  pure_rewrite_tac[GSYM raw_encoder_prefix_rtc] >>
  `local_ptrs_reserved ce se` by (irule local_ptrs_reserved_next_var >> qexists_tac `C 0` >> simp[]) >>
  `?K. valid_horizon cx st0 K (E (LENGTH ctors)).storage_trace` by (qexists_tac `H` >> fs[Abbr `ee`]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by simp[] >>
  `compile_create_ctor_args compile_expr ce ctors (C 0) = (svs,C (LENGTH ctors))` by gvs[] >>
  simp[PAIR_EQ] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qexists_tac `H` >> first_assum ACCEPT_TAC >> NO_TAC)
  >- suspend "producer_row" >>
  suspend "producer_callback"
QED

Resume create_blueprint_abi_keyword_entry[producer_row]:
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `!x. not_fresh_at (C 0) x ==> not_fresh_at (C i) x` by
     metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `local_ptrs_reserved ce (C i)` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  qpat_assum `!i. i <= LENGTH ctors ==> (E i).gas_obs = _ /\ _`
    (qspec_then `i` mp_tac) >> simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `(St (SUC i)).vs_labels = (St i).vs_labels` by
    (imp_res_tac raw_observed_prefix_labels >> metis_tac[]) >>
  simp[] >> disch_tac >> Cases_on `exprs_can_mutate ce (DROP (SUC i) ctors)` >> simp[]
  >- (conj_tac
      >- (irule raw_observed_prefix_live >>
          qexistsl_tac [`C i`,`M i`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`Chunk i`,`St i`] >> simp[]) >>
      simp[GSYM PAIR_EQ,GSYM IMP_DISJ_THM] >>
      drule blueprint_ctor_segment_rtc >> simp[PAIR_EQ]) >>
  `vv_type (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)) =
     lowered_value_type ce (EL i ctors)` by metis_tac[extcall_operand_snapshot_type] >>
  `C (SUC i) = M i` by
    (qpat_assum `compile_snapshot_vv _ _ _ (M i) = _`
        (mp_tac o PURE_REWRITE_RULE[compile_snapshot_vv_def]) >>
     simp[comp_return_def] >> metis_tac[]) >>
  qpat_assum `create_expr_prefix (M i) (C (SUC i)) _ _ _ _ _ _` mp_tac >>
  simp[] >> metis_tac[blueprint_raw_empty_snapshot_prefix]
QED

Resume create_blueprint_abi_keyword_entry[producer_callback]:
  map_every qx_gen_tac [`i`,`g`,`h`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!i. i < LENGTH ctors ==> monad_bind _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (mp_tac o List.last o CONJUNCTS))) >>
  disch_then (qspecl_then [`g`,`h`] (drule_then ACCEPT_TAC))
QED

Resume create_blueprint_abi_keyword_entry[finish]:
  qhdtm_assum `abi_encode_saved_state`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[abi_encode_saved_state_def]) >>
  qpat_assum `!i. i <= LENGTH ctors ==> (E i).gas_obs = _ /\ _`
    (qspec_then `LENGTH ctors` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `!f inst z. frag_reachable ctx func s f inst z ==> dalloca_no_wrap inst z` by
    (qpat_assum `s = St _` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `!f inst z. frag_reachable ctx func su f inst z ==> dalloca_no_wrap inst z` by
    (qpat_assum `gas_origin_ptr_path _ (s,_,_) [] (OK su,_,_)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_no_wrap) >> asm_rewrite_tac[]) >>
  `!f inst z. frag_reachable ctx func t f inst z ==> dalloca_no_wrap inst z` by
    (qpat_assum `gas_origin_ptr_path _ (su,_,_) [] (OK t,_,_)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_no_wrap) >> asm_rewrite_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `!K. valid_horizon cx st0 K ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
       (qspec_then `H` (drule_then
          (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp o CONJUNCT1)))) >>
  `t.vs_labels = (St 0).vs_labels` by suspend "exit_labels" >>
  `eval_operand target_op t = SOME aw` by
    (irule blueprint_eval_operand_frame >>
     qexistsl_tac [`C 0`,`St 0`] >> simp[] >>
     qpat_assum `wb_frame ce (E 0) ee (C 0) (St 0) t`
       (mp_tac o cj 1 o REWRITE_RULE[wb_frame_def]) >> simp[]) >>
  `ee.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail` by suspend "exit_gas" >>
  `local_ptrs_reserved ce en` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `C 0` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`cvs`,`ee`,`geout`,`teout`] >>
  gvs[Abbr `k`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qexists_tac `bs` >> simp[]
QED

Resume create_blueprint_abi_keyword_entry[exit_labels]:
  `!i. i <= LENGTH ctors ==> (St i).vs_labels = (St 0).vs_labels` by
    (Induct >> simp[] >> disch_tac >>
     rename1 `SUC i <= LENGTH ctors` >>
     `i < LENGTH ctors` by
       (pure_rewrite_tac[LESS_EQ] >> qpat_assum `SUC i <= LENGTH ctors` ACCEPT_TAC) >>
     `i <= LENGTH ctors` by simp[LESS_IMP_LESS_OR_EQ] >>
     qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     imp_res_tac raw_observed_prefix_labels >> simp[]) >>
  imp_res_tac raw_observed_prefix_labels >> simp[]
QED

Resume create_blueprint_abi_keyword_entry[exit_gas]:
  `am = [] /\ encmarks = []` by
    (imp_res_tac gas_origin_ptr_path_projections >> conj_tac >>
     irule blueprint_abi_silent_band
     >- (qexistsl_tac [`se`,`a`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`s`,`su`] >> simp[]) >>
     qexistsl_tac [`a`,`en`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`su`,`t`] >> simp[]) >>
  imp_res_tac create_prefix_readings >> fs[Abbr `ee`]
QED

Finalise create_blueprint_abi_keyword_entry

Theorem raw_payload_silent_readings[local]:
  gas_origin_edge F explicit ctx func s [] (OK t) ==>
  t.vs_gas_readings = s.vs_gas_readings
Proof
  disch_then (mp_tac o CONJUNCT1 o MATCH_MP gas_origin_edge_erase) >>
  disch_then (mp_tac o MATCH_MP gas_path_edge_suffix) >> simp[gas_count_suffix_def]
QED

Theorem create_raw_payload_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env
    (Call ann (CreateTarget RawCreate hs rof ks) (e::av::(args ++ (if hs then [saltE] else []))) df) entry /\
  EVERY (create_operand_completed_ok cx)
    (create_operand_order RawCreate hs (e::av::(args ++ (if hs then [saltE] else [])))) /\
  tys = MAP expr_type (e::av::(args ++ (if hs then [saltE] else []))) /\
  lit = blueprint_literal_offset cx hs (e::av::(args ++ (if hs then [saltE] else []))) /\
  bind (eval_exprs cx (args ++ av::(if hs then [saltE] else [])))
      (\vs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::vs)) p0 = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  (!K. dead_lo_ok K (DF K) lo ce cx) /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail /\
  expr_sim_inv ce cx env p0 /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_no_wrap i z) /\
  ~(St 0).vs_halted /\ (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\ local_ptrs_reserved ce (C 0) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at (DF K) lo d ce cx p0 G0 tn0 (St 0)) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  explicit = gas_explicit_sites ctx shctx /\
  lenop = Var lvar /\ not_fresh_at (C 0) lvar /\
  lookup_var lvar (St 0) = SOME (n2w (LENGTH code)) /\
  uval.vs_current_bb = cv.cs_current_bb /\ uval.vs_inst_idx = LENGTH cv.cs_current_insts /\
  (if args = [] then
     cv = C 0 /\ uval = St 0 /\ size_op = lenop /\ R 0 = kwmarks
   else
     LENGTH svs = LENGTH args /\
     compile_create_ctor_args compile_expr ce args (C 0) = (svs,C (LENGTH args)) /\
     EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs args) /\
     sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\ fn_inst_ids_distinct func /\
     (!i. i < LENGTH args ==>
       compile_expr ce (expr_type (EL i args)) (EL i args) (C i) = (V i,M i) /\
       compile_expr ce (expr_type (EL i args)) (gas_shadow_expr (EL i args)) (Sh i) = (V i,SM i) /\
       compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
         (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (M i) =
           (EL i svs,C (SUC i)) /\
       compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
         (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (SM i) =
           (EL i svs,Sh (SUC i)) /\
       expr_sim_full_code (ctx,shctx,func,shfunc) (C i,M i,Sh i,SM i) /\
       expr_sim_full_code (ctx,shctx,func,shfunc) (C i,C (SUC i),Sh i,Sh (SUC i)) /\
       (C 0).cs_next_var <= (C i).cs_next_var /\
       (St (SUC i)).vs_labels = (St i).vs_labels /\
       ~(St (SUC i)).vs_halted /\ (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
       (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
       R i = (Chunk i ++ Snap i) ++ R (SUC i) /\
       create_expr_prefix (C i) (C (SUC i)) explicit ctx func
         (St i) (Chunk i ++ Snap i) (St (SUC i)) /\
       create_expr_prefix (C i) (M i) explicit ctx func (St i) (Chunk i) (Mid i) /\
       ~(Mid i).vs_halted /\ (Mid i).vs_current_bb = (M i).cs_current_bb /\
       (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
       create_expr_prefix (M i) (C (SUC i)) explicit ctx func (Mid i) (Snap i) (St (SUC i)) /\
       (if exprs_can_mutate ce (DROP (SUC i) args) then
          fn_has_code (M i) (C (SUC i)) func /\
          RTC (\p q. (p.vs_current_bb,p.vs_inst_idx) <>
                  ((C (SUC i)).cs_current_bb,LENGTH (C (SUC i)).cs_current_insts) /\
                 ?j ms. ctor_segment_fetch func p = SOME j /\
                   (M i).cs_next_id <= j.inst_id /\ j.inst_id < (C (SUC i)).cs_next_id /\
                   gas_origin_edge F explicit ctx func p ms (OK q)) (Mid i) (St (SUC i)) /\
          (?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ j.inst_opcode <> PHI /\
               (C (SUC i)).cs_next_id <= j.inst_id)
        else ~is_word_type (lowered_value_type ce (EL i args)) ==> Mid i = St (SUC i))) /\
     se = C (LENGTH args) /\ s = St (LENGTH args) /\
     capacity = prefix_bound + abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) /\
     capacity < dimword (:256) /\ w2n (n2w (LENGTH code):bytes32) <= prefix_bound /\
     not_fresh_at (C 0) src /\ lookup_var src (St 0) = SOME p /\
     ptr_covers G0 tn0 src (St 0) (w2n (n2w (LENGTH code):bytes32)) /\
     op_taint tn0 (Var lvar) = {} /\ w2n p + w2n (n2w (LENGTH code):bytes32) <= (St 0).vs_alloca_next /\
     compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
     gas_origin_edge F explicit ctx func s am (OK su) /\
     compile_copy_memory_dynamic buf.buf_operand (Var src) (Var lvar) a = ((),b) /\ fn_has_code a b func /\
     emit_op ADD [buf.buf_operand;Var lvar] b = (dst_op,st) /\ fn_has_code b st func /\
     gas_origin_edge F explicit ctx func su bm (OK sv) /\ gas_origin_edge F explicit ctx func sv cm (OK u) /\
     compile_abi_encode_values_to_buf ce dst_op (ZIP (svs,MAP (lowered_value_type ce) args))
       st = (alen,en) /\ fn_has_code st en func /\
     create_expr_prefix st en explicit ctx func u encmarks t /\
     (t.vs_current_bb,t.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts) /\
     emit_op ADD [lenop;alen] en = (size_op,cv) /\ fn_has_code en cv func /\
     create_expr_prefix en cv explicit ctx func t dm uval /\
     R (LENGTH args) = am ++ bm ++ cm ++ encmarks ++ dm ++ kwmarks /\
     c 0 = en /\ r 0 = t /\ r n = bad /\
     (!k. k < n ==>
       (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
       create_expr_prefix (c k) (c (SUC k)) explicit ctx func (r k) (chunk k) (r (SUC k))) /\
     lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
     get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
     ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value;off;sz]) \/
      (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value;off;sz;salt])) /\
     eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?cvs payload ee G tn.
    LENGTH cvs = LENGTH args /\
    encode_create_ctor_args (get_tenv cx) (MAP expr_type args) cvs = SOME payload /\
    bind (eval_exprs cx (av::(if hs then [saltE] else [])))
      (\kvs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::(cvs ++ kvs))) ee = (res,out) /\
    valid_horizon cx st0 H ee.storage_trace /\
    ee.gas_obs = gas_explicit kwmarks uval.vs_gas_readings ++ tail /\
    expr_sim_inv ce cx env ee /\ return_buf_frame d ce cv uval /\ alloca_history func uval /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp uval) /\
    (!f i z. frag_reachable ctx func uval f i z ==> dalloca_no_wrap i z) /\
    ~uval.vs_halted /\ uval.vs_current_bb = cv.cs_current_bb /\
    uval.vs_inst_idx = LENGTH cv.cs_current_insts /\ local_ptrs_reserved ce cv /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cv x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cv x) /\
    (!K. valid_horizon cx st0 K ee.storage_trace ==>
      stmt_state_rel K ctx func ce cx ee uval /\ storage_well_formed_on cx ee (FST K) /\
      ghost_inv_at (DF K) lo d ce cx ee G tn uval) /\
    (if args = [] then payload = [] /\ size_op = lenop /\ cv = C 0 /\ uval = St 0
     else (!x v. not_fresh_at (C 0) x /\ lookup_var x (St 0) = SOME v ==> lookup_var x t = SOME v) /\
       eval_operand alen t = SOME (n2w (LENGTH payload)) /\
       eval_operand size_op uval = SOME (n2w (LENGTH code + LENGTH payload)) /\
       (!x. size_op = Var x ==> not_fresh_at cv x) /\ dm = [])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `args = []`
  >- (qpat_assum `args = []` (fn h =>
        qpat_x_assum `if args = [] then _ else _`
          (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [h])) >>
      fs[] >> suspend "empty") >>
  qpat_assum `args <> []` (fn h =>
    qpat_x_assum `if args = [] then _ else _`
      (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [h])) >>
  qpat_assum `args <> []` (simp_tac bool_ss o single) >>
  suspend "rows"
QED

Resume create_raw_payload_at_cuts[empty]:
  `valid_horizon cx st0 H p0.storage_trace` by
    (qpat_assum `bind (eval_exprs cx _) _ p0 = _`
       (mp_then Any irule vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_create_operands,
          storage_trace_frame_bind_all]) >>
  disj2_tac >> qexistsl_tac [`p0`,`G0`,`tn0`] >>
  qpat_assum `tys = _` (pure_once_rewrite_tac o single o SYM) >>
  qpat_assum `lit = _` (pure_once_rewrite_tac o single o SYM) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_raw_payload_at_cuts[rows]:
  qabbrev_tac `k = \vs. bind (eval_exprs cx (av::(if hs then [saltE] else [])))
    (\kvs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::(vs ++ kvs)))` >>
  `bind (eval_exprs cx args) k p0 = (res,out)` by
    (qpat_assum `bind (eval_exprs cx (args ++ _)) _ p0 = _`
       (mp_tac o REWRITE_RULE [blueprint_abi_bind_append]) >> simp[Abbr `k`]) >>
  `!vs. storage_trace_frame (k vs)` by
    simp[Abbr `k`,evaluate_storage_trace_frame,storage_trace_frame_bind_all,
         storage_trace_frame_create_operands] >>
  mp_tac (SPEC_ALL (INST_TYPE [alpha |-> ``:eval_result``] create_ctor_rows_at_cuts)) >>
  (impl_tac >- suspend "rows_premises") >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  suspend "encoder"
QED

Resume create_raw_payload_at_cuts[rows_premises]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qpat_x_assum `EVERY (create_operand_completed_ok cx) _` mp_tac >>
      Cases_on `hs` >> simp[create_operand_order_def,EVERY_APPEND,DROP_PREFIX,TAKE_APPEND1] >>
      metis_tac[EVERY_MEM,EL_MEM])
  >- (rpt strip_tac >> irule create_raw_arg_body_pre >> simp[EL_MEM] >>
      goal_assum (drule_at Any) >> simp[EL_MEM]) >>
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  qpat_assum `explicit = _` (fn he => rule_assum_tac (PURE_REWRITE_RULE[he])) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  strip_tac >> fs[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  disch_tac >> irule ctor_observed_cut_silent >>
  qexistsl_tac [`ctx`,`((C (SUC i)).cs_current_bb,LENGTH (C (SUC i)).cs_current_insts)`,
    `gas_explicit_sites ctx shctx`,`func`,`St (SUC i)`,`Mid i`] >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  irule RTC_MONOTONE >>
  qpat_assum `create_expr_prefix (M i) (C (SUC i)) _ _ _ _ _ _`
    (irule_at Any o REWRITE_RULE [create_expr_prefix_marked]) >>
  simp[create_marked_edge_def,create_prefix_step_def,FORALL_PROD,PAIR_EQ] >> metis_tac[]
QED

Resume create_raw_payload_at_cuts[encoder]:
  `ci_mono (C 0) se` by
    (qpat_assum `se = _` (pure_rewrite_tac o single) >>
     qspecl_then [`compile_expr`,`ce`,`args`,`C 0`] mp_tac ci_mono_compile_create_ctor_args >>
     (impl_tac >- simp_tac bool_ss [cj 1 ci_mono_compile_expr_sa]) >>
     qpat_assum `compile_create_ctor_args _ _ _ _ = _` (pure_rewrite_tac o single) >>
     simp[]) >>
  `local_ptrs_reserved ce se /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by
    (qpat_assum `ci_mono (C 0) se`
       (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     drule_all blueprint_keyword_mono >> simp[]) >>
  mp_tac (Q.INST [`len` |-> `lvar`,`nword` |-> `n2w (LENGTH (code:word8 list)):bytes32`,
                   `ee` |-> `E (LENGTH args)`] (SPEC_ALL create_raw_encoder_at_cuts)) >>
  (impl_tac >- suspend "encoder_premises") >> strip_tac >>
  rename1 `encode_create_ctor_args _ _ vs = SOME bytes` >>
  rename1 `op_taint tt alen = {}` >>
  suspend "add"
QED

Resume create_raw_payload_at_cuts[encoder_premises]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (sym_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qexists_tac `H` >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (REFL_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac[] >> NO_TAC) >>
  TRY (qpat_assum `E 0 = p0` (fn h => pure_rewrite_tac[h]) >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_assum `s = St _` (pure_rewrite_tac o single) >>
       qpat_assum `!i. i <= LENGTH args ==> (E i).gas_obs = _ /\ _`
         (qspec_then `LENGTH args` (map_every assume_tac o CONJUNCTS o REWRITE_RULE[LESS_EQ_REFL])) >>
       first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (map_every qx_gen_tac [`i`,`g`,`h`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
       qpat_assum `!i. i < LENGTH args ==> bind _ _ (E i) = _ /\ _`
         (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
       first_assum (qspecl_then [`g`,`h`] mp_tac) >>
       (impl_tac >- first_assum ACCEPT_TAC) >>
       disch_then ACCEPT_TAC >> NO_TAC) >>
  qx_gen_tac `i` >> disch_tac >> suspend "encoder_rows"
QED

Resume create_raw_payload_at_cuts[encoder_rows]:
  `i <= LENGTH args` by decide_tac >>
  qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!i. i < LENGTH args ==> bind _ _ (E i) = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!i. i <= LENGTH args ==> (E i).gas_obs = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (disch_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
  strip_tac >>
  qpat_x_assum `if exprs_can_mutate ce (DROP (SUC i) args) then _ else _` mp_tac >>
  Cases_on `exprs_can_mutate ce (DROP (SUC i) args)`
  >- (qpat_assum `exprs_can_mutate ce (DROP (SUC i) args)` (simp_tac bool_ss o single) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `~exprs_can_mutate ce (DROP (SUC i) args)` (simp_tac bool_ss o single) >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Resume create_raw_payload_at_cuts[add]:
  drule_all (Q.INST [`a` |-> `en`,`b` |-> `cv`,`s` |-> `t`,`t` |-> `uval`,
                     `PG` |-> `[]:(num # num) option list`]
              create_raw_total_add_entry_at_cuts) >> strip_tac >>
  rename1 `size_op = Var sumvar` >>
  rename1 `Gv = step_prov _ _ _ _` >>
  rename1 `tv = step_taint _ _ _ _` >>
  suspend "finish"
QED

Resume create_raw_payload_at_cuts[finish]:
  qpat_assum `!i. i <= LENGTH args ==> (E i).gas_obs = _ /\ _`
    (qspec_then `LENGTH args` (map_every assume_tac o CONJUNCTS o REWRITE_RULE[LESS_EQ_REFL])) >>
  map_every (fn (mark, edge) =>
    qpat_assum mark (fn h => qpat_assum edge
      (assume_tac o MATCH_MP raw_payload_silent_readings o PURE_REWRITE_RULE[h])))
    [(`am = []`,`gas_origin_edge F explicit ctx func s am (OK su)`),
     (`bm = []`,`gas_origin_edge F explicit ctx func su bm (OK sv)`),
     (`cm = []`,`gas_origin_edge F explicit ctx func sv cm (OK u)`)] >>
  qpat_assum `create_expr_prefix st en explicit ctx func u encmarks t`
    (assume_tac o MATCH_MP create_prefix_readings) >>
  `(E (LENGTH args)).gas_obs = gas_explicit kwmarks uval.vs_gas_readings ++ tail` by
    asm_rewrite_tac[APPEND,LENGTH,DROP] >>
  `eval_operand lenop t = SOME (n2w (LENGTH code))` by
    (qpat_assum `lenop = Var lvar` (pure_rewrite_tac o single) >>
     rewrite_tac[eval_operand_def] >> first_assum ACCEPT_TAC) >>
  `eval_operand size_op uval = SOME (n2w (LENGTH code + LENGTH bytes))` by
    (qpat_assum `eval_operand size_op uval = SOME (_ + _)` mp_tac >>
     rpt (qpat_x_assum `eval_operand size_op uval = _` kall_tac) >>
     metis_tac[word_add_n2w,optionTheory.SOME_11]) >>
  qunabbrev_tac `k` >> disj2_tac >>
  qexistsl_tac [`vs`,`bytes`,`E (LENGTH args)`,`Gv`,`tv`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qpat_assum `(\vs. _) vs (E (LENGTH args)) = (res,out)`
        (ACCEPT_TAC o CONV_RULE (DEPTH_CONV BETA_CONV)))
  >- (qpat_assum `wb_frame ce (E 0) _ _ _ _`
        (ACCEPT_TAC o cj 1 o REWRITE_RULE[wb_frame_def])) >>
  rpt strip_tac >> gvs[]
QED
Finalise create_raw_payload_at_cuts

Theorem raw_itinerary_index[local]:
  !cuts sa sc. create_itinerary_code sa cuts sc ==>
    (!i. i <= LENGTH cuts ==> ci_mono sa (EL i (sa::cuts)) /\
                              ci_mono (EL i (sa::cuts)) sc) /\
    (!i. i < LENGTH cuts ==> ci_mono (EL i (sa::cuts)) (EL (SUC i) (sa::cuts)))
Proof
  Induct >- simp[create_itinerary_code_def,ci_mono_refl] >>
  simp[create_itinerary_code_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  `ci_mono h sc` by metis_tac[create_itinerary_code_relations] >>
  `ci_mono sa sc` by metis_tac[ci_mono_trans] >>
  conj_tac >> gen_tac >> Cases_on `i` >> simp[ci_mono_refl] >>
  TRY (strip_tac >> qpat_assum `!i. i <= _ ==> _` (drule_then strip_assume_tac) >>
       metis_tac[ci_mono_trans] >> NO_TAC) >>
  gvs[]
QED

Theorem create_size_exit_raw:
  !cx ann hs rof ks args df.
    EVERY (create_operand_completed_ok cx) (create_operand_order RawCreate hs args) ==>
    create_expr_size_exit cx (Call ann (CreateTarget RawCreate hs rof ks) args df)
Proof
  rewrite_tac[create_expr_size_exit_def] >>
  rpt (gen_tac ORELSE disch_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb)` by
    simp[expr_sim_full_code_def] >>
  `?result. compile_create_call compile_expr cenv RawCreate hs rof args sa = (result,sb)` by
    (qpat_assum `compile_expr _ _ (Call _ _ _ _) _ = _` mp_tac >>
     rewrite_tac[exprSimSendTheory.compile_expr_call, compile_call_def] >>
     Cases_on `compile_create_call compile_expr cenv RawCreate hs rof args sa` >>
     simp[as_stack_val_def]) >>
  `MEM inst.inst_opcode [CREATE; CREATE2]` by fs[] >>
  drule_all create_size_prefix_cuts >> strip_tac >>
  qpat_x_assum `create_call_itinerary _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss
       [create_call_itinerary_def, create_kind_case_def, create_raw_itinerary_def]) >>
  rename1 `compile_expr cenv (expr_type be) be sa = (bcvv,a)` >>
  rename1 `compile_create_snapshot cenv bcvv _ a = (snap,b)` >>
  rename1 `emit_op MLOAD [snap] b = (lenop,c)` >>
  rename1 `emit_op ADD [snap; Lit 32w] c = (data,cd)` >>
  rename1 `lower_value compile_expr cenv (expr_type av) av cv = (amount,cq)` >>
  rename1 `create_itinerary_salt cenv _ cq salt_op cf` >>
  rename1 `create_size_dispatch_tail rof sc sd created bufop sizeop amount salt_op result sb` >>
  `sc = cf` by
    (qpat_assum `LAST (sa::cuts) = sc` mp_tac >>
     qpat_assum `cuts = _` (fn th => PURE_REWRITE_TAC[th]) >>
     `sa::([a;b;c;cd] ++ prep ++ [cq;cf]) = ([sa;a;b;c;cd] ++ prep) ++ [cq;cf]` by
       simp[APPEND_ASSOC] >>
     pop_assum (pure_rewrite_tac o single) >> simp[]) >>
  qpat_x_assum `sc = cf` (SUBST_ALL_TAC o SYM) >>
  `inst.inst_id = sc.cs_next_id /\ inst.inst_opcode <> PHI /\ eval_operand sizeop s = SOME w` by
    (Cases_on `salt_op` >> fs[mk_inst_def] >> metis_tac[]) >>
  `ctor_segment_fetch func s = SOME inst` by
    (qpat_assum `lookup_block s.vs_current_bb _ = SOME bb` (pure_rewrite_tac o (fn h => [ctor_segment_fetch_def,h])) >>
     pure_rewrite_tac[optionTheory.OPTION_BIND_def] >> BETA_TAC >> first_assum ACCEPT_TAC) >>
  suspend "bands"
QED

Resume create_size_exit_raw[bands]:
  qabbrev_tac `xs = if hs then FRONT rest else rest` >>
  qabbrev_tac `salte = if hs then SOME (LAST rest) else NONE` >>
  qabbrev_tac `cap = bytelike_type_bound (lowered_value_type cenv be) +
       abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) xs))` >>
  qabbrev_tac `rawcomp = \i. EL i (sa::cuts)` >>
  qabbrev_tac `rawobs = \i. EL i states` >>
  qabbrev_tac `Ms = \i. EL i chunks'` >>
  qabbrev_tac `ncut = LENGTH cuts` >>
  qabbrev_tac `vp = 4 + LENGTH prep` >>
  qabbrev_tac `explicit = gas_explicit_sites ctx shadow_ctx` >>
  `?opc ops. emit_op opc ops sc = (created,sd) /\ compile_check_create_result created rof sd = (result,sb)` by
    (Cases_on `salt_op` >> fs[create_size_dispatch_tail_def] >> metis_tac[]) >>
  `cs_extends sc sb` by
    (irule cs_extends_trans >> qexists_tac `sd` >>
     metis_tac[ci_mono_def,ci_mono_emit_op,externalEntryShapeTheory.compile_check_create_result_labels,pairTheory.SND]) >>
  drule raw_itinerary_index >> strip_tac >>
  `!i. i < ncut ==> (rawcomp i).cs_next_id <= (rawcomp (SUC i)).cs_next_id /\
    fn_has_code (rawcomp i) (rawcomp (SUC i)) func /\
    create_expr_prefix (rawcomp i) (rawcomp (SUC i)) explicit ctx func (rawobs i) (Ms i) (rawobs (SUC i))` by
    (qpat_x_assum `cuts = _` kall_tac >>
     simp[Abbr `rawcomp`,Abbr `rawobs`,Abbr `Ms`,Abbr `ncut`,Abbr `explicit`] >> rpt strip_tac >>
     `SUC i <= LENGTH cuts /\ i <= LENGTH cuts` by decide_tac >>
     qpat_assum `!i. i < LENGTH cuts ==> ci_mono _ _` (qspec_then `i` (drule_then assume_tac)) >>
     TRY (fs[ci_mono_def] >> NO_TAC) >>
     TRY (qpat_assum `!i. i < LENGTH cuts ==> create_expr_prefix _ _ _ _ _ _ _ _`
       (qspec_then `i` mp_tac) >> simp[] >> NO_TAC) >>
     qpat_assum `!i. i <= LENGTH cuts ==> _ /\ _` (fn th =>
       map_every (fn j => qspec_then j mp_tac th) [`i`,`SUC i`]) >>
     simp_tac bool_ss [EL_restricted,DECIDE ``SUC i <= n <=> i < n``] >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     `cs_extends sa (EL i (sa::cuts)) /\ cs_extends (EL i (sa::cuts)) (EL i cuts) /\
      cs_extends (EL i cuts) sc` by fs[ci_mono_def] >>
     `cs_extends (EL i cuts) sb` by metis_tac[cs_extends_trans] >>
     irule fn_has_code_mid >>
     qpat_assum `fn_has_code sa sb func` (irule_at Any) >> simp[]) >>
  mp_tac (Q.INST [`C` |-> `rawcomp`, `Obs` |-> `rawobs`, `M` |-> `Ms`, `n` |-> `ncut`,
    `vpos` |-> `vp`, `chunks0` |-> `chunks'`, `fn` |-> `func`, `bad` |-> `s`,
    `dispatch` |-> `inst`, `d` |-> `cd`, `len` |-> `lenop`, `size_op` |-> `sizeop`,
    `cenv` |-> `cenv`] (SPEC_ALL create_raw_observed_bands)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> simp[markerTheory.Abbrev_def])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "pair"
QED

Resume create_size_exit_raw[pair]:
  qpat_x_assum `args = be::av::rest` SUBST_ALL_TAC >>
  qpat_x_assum `if xs = [] then _ else _`
    (fn th =>
       let val [empty,nonempty] = CONJUNCTS (PURE_REWRITE_RULE [COND_EXPAND_IMP] th)
       in assume_tac empty >>
          strip_assume_tac (CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) nonempty)
       end) >>
  rename1 `xs <> [] ==> _ /\ _ /\ _ /\ _ /\ _ /\
    compile_abi_encode_values_to_buf _ _ _ _ = (_,en) /\ _` >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `e` |-> `be`, `v` |-> `av`, `dflt` |-> `df`,
    `hsa` |-> `shadow_sa`, `hsb` |-> `shadow_sb`, `parent_vv` |-> `vv`, `sctx` |-> `shadow_ctx`,
    `fn` |-> `func`, `sfn` |-> `shadow_func`, `vv` |-> `bcvv`, `d` |-> `cd`,
    `p` |-> `cv`, `q` |-> `cq`, `value` |-> `amount`, `salt` |-> `salt_op`,
    `vvs` |-> `vs`, `j` |-> `ca`, `m` |-> `cb`, `n` |-> `cc`, `o'` |-> `en`]
      (SPEC_ALL create_raw_paired_operand_code)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
    TRY (IF_CASES_TAC >> fs[] >> NO_TAC) >> simp[markerTheory.Abbrev_def])) >>
  disch_then (qx_choose_then `ha` (qx_choose_then `hp` (qx_choose_then `hq` (qx_choose_then `hsc`
    (map_every assume_tac o CONJUNCTS))))) >>
  suspend "header"
QED

Resume create_size_exit_raw[header]:
  `ncut = SUC (SUC vp)` by
    (simp[Abbr `ncut`,Abbr `vp`] >> decide_tac) >>
  `1 <= ncut /\ 2 <= ncut /\ 3 <= ncut /\ 4 <= ncut /\ vp <= ncut /\ SUC vp <= ncut` by
    (simp[Abbr `vp`] >> decide_tac) >>
  qpat_assum `!i. i <= ncut ==> ~(rawobs i).vs_halted /\ _`
    (fn th => map_every (fn i =>
      qspec_then i mp_tac th >> (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [pairTheory.PAIR_EQ]))
      [`1`,`2`,`3`,`4`,`vp`,`SUC vp`]) >>
  qpat_assum `Abbrev (explicit = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rename1 `return_buf_frame dep' cenv sa s0` >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `e` |-> `be`, `v` |-> `av`, `dep` |-> `dep'`,
    `parent_vv` |-> `vv`, `vv` |-> `bcvv`, `shadow_a` |-> `ha`, `d` |-> `cd`, `len` |-> `lenop`,
    `u` |-> `rawobs 1`, `z` |-> `rawobs 2`, `l` |-> `rawobs 3`, `r` |-> `rawobs 4`,
    `ms` |-> `Ms 0`, `msS` |-> `Ms 1`, `msL` |-> `Ms 2`, `msD` |-> `Ms 3`,
    `later` |-> `FLAT (DROP 4 chunks')`] (SPEC_ALL create_raw_data_entry_at_cuts)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
    pure_asm_rewrite_tac [APPEND_ASSOC] >> simp_tac bool_ss [] >>
    qpat_assum `marks = _ ++ FLAT (DROP 4 chunks')` (fn h =>
      qpat_assum `eval_expr _ (Call _ _ _ _) _ = (res,ee)`
        (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_ASSOC] o SUBS [h])))) >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `err` strip_assume_tac)
    (qx_choose_then `p0` strip_assume_tac))
  >- (disj2_tac >> qexists_tac `err` >> simp[]) >>
  suspend "payload"
QED

Resume create_size_exit_raw[payload]:
  `xs ++ (if hs then [LAST rest] else []) = rest` by
    (Cases_on `hs` >> simp_tac (srw_ss()) [Abbr `xs`] >>
     irule APPEND_FRONT_LAST >>
     qpat_assum `T ==> rest <> []` (ACCEPT_TAC o SIMP_RULE bool_ss [])) >>
  qpat_assum `Abbrev (xs = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (gen_tac >> disch_tac >> drule_all bodyFullIfExpReachTheory.body_inv_no_phi >> simp[]) >>
  rename1 `xs <> [] ==> _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ pidx = 4 + 2 * LENGTH xs /\ _` >>
  qpat_x_assum `xs <> [] ==> fn_has_code cd k func /\ _`
    (fn th =>
       let
         val split = CONV_RULE (REWR_CONV IMP_CONJ_THM)
         fun distribute h =
           case total split h of
             NONE => strip_assume_tac (CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) h)
           | SOME pair => assume_tac (CONJUNCT1 pair) >> distribute (CONJUNCT2 pair)
       in distribute th end) >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `shctx` |-> `shadow_ctx`, `shfunc` |-> `shadow_func`,
    `e` |-> `be`, `entry` |-> `es`, `args` |-> `xs`, `saltE` |-> `LAST rest`, `out` |-> `ee`,
    `tys` |-> `MAP expr_type (be::av::rest)`, `lit` |-> `blueprint_literal_offset cx hs (be::av::rest)`,
    `d` |-> `dep'`, `G0` |-> `Gr`, `tn0` |-> `tnr`, `lvar` |-> `lenvar`, `src` |-> `datavar`,
    `C` |-> `(\i:num. rawcomp (4+2*i))`, `St` |-> `(\i:num. rawobs (4+2*i))`,
    `R` |-> `(\i:num. FLAT (DROP (4+2*i) chunks'))`, `Chunk` |-> `(\i:num. Ms (4+2*i))`,
    `Snap` |-> `(\i. Ms (SUC (4+2*i)))`, `Mid` |-> `(\i. rawobs (SUC (4+2*i)))`,
    `V` |-> `(\i. EL i vs)`, `M` |-> `(\i. EL i mid)`, `Sh` |-> `(\i. EL i hcs)`, `SM` |-> `(\i. EL i hmid)`,
    `uval` |-> `rawobs (vp:num)`, `size_op` |-> `sizeop`, `kwmarks` |-> `Ms (vp:num) ++ Ms (SUC vp)`,
    `svs` |-> `vals`, `se` |-> `k`, `s` |-> `rawobs (pidx:num)`, `capacity` |-> `cap`,
    `prefix_bound` |-> `bytelike_type_bound (lowered_value_type cenv be)`,
    `p` |-> `n2w (buffer_allocation_base (rawobs 1) a.cs_next_id + 32)`,
    `a` |-> `ca`, `b` |-> `cb`, `st` |-> `cc`, `dst_op` |-> `dst`,
    `su` |-> `rawobs ((pidx:num)+1)`, `sv` |-> `rawobs ((pidx:num)+2)`,
    `u` |-> `rawobs ((pidx:num)+3)`, `t` |-> `rawobs ((pidx:num)+4)`,
    `am` |-> `Ms (pidx:num)`, `bm` |-> `Ms ((pidx:num)+1)`, `cm` |-> `Ms ((pidx:num)+2)`,
    `encmarks` |-> `Ms ((pidx:num)+3)`, `dm` |-> `Ms ((pidx:num)+4)`,
    `c` |-> `(\i:num. rawcomp (pidx+4+i))`, `r` |-> `(\i:num. rawobs (pidx+4+i))`,
    `chunk` |-> `(\i:num. Ms (pidx+4+i))`, `n` |-> `3`, `bad` |-> `s`, `bbad` |-> `bb`, `dispatch` |-> `inst`]
    (SPEC_ALL create_raw_payload_at_cuts)) >>
  BETA_TAC >>
  (impl_tac >- suspend "payload_pre") >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `err` strip_assume_tac)
    (qx_choose_then `cvs` (qx_choose_then `payload` (qx_choose_then `pval`
      (qx_choose_then `Gval` (qx_choose_then `tnval` (map_every assume_tac o CONJUNCTS)))))))
  >- (disj2_tac >> qexists_tac `err` >> simp[]) >>
  suspend "keywords"
QED

Resume create_size_exit_raw[payload_pre]:
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac [ADD_CLAUSES,MULT_CLAUSES] >> simp_tac bool_ss [] >> NO_TAC) >>
  TRY (qpat_assum `(if hs then FRONT rest else rest) = xs` (fn h =>
    qpat_assum `bind (eval_exprs cx _) _ p0 = _` (ACCEPT_TAC o SUBS [h])) >> NO_TAC) >>
  Cases_on `xs = []`
  >- (qpat_assum `xs = [] ==> prep = [] /\ _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      `vp = 4` by simp[Abbr `vp`] >>
      pure_asm_rewrite_tac [COND_CLAUSES,ADD_CLAUSES,MULT_CLAUSES] >> simp_tac bool_ss [] >>
      qpat_assum `vp = 4` (fn h =>
        qpat_assum `FLAT (DROP vp chunks') = _` (ACCEPT_TAC o SUBS [h]))) >>
  qpat_assum `xs <> []` (simp_tac bool_ss o single) >>
  suspend "payload_nonempty"
QED

Resume create_size_exit_raw[payload_nonempty]:
  qpat_x_assum `xs <> [] ==> compile_create_ctor_args _ _ _ _ = _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  rpt (qpat_x_assum `xs <> [] ==> fn_has_code _ _ _` (drule_then assume_tac)) >>
  qpat_x_assum `xs <> [] ==> LENGTH hcs = _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qhdtm_assum `create_itinerary_ctor_rows`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [create_itinerary_ctor_rows_def]) >>
  `pidx+4+3 = ncut /\ SUC (pidx+4) = vp /\ pidx+4 <= ncut` by decide_tac >>
  `!i. i < LENGTH xs ==> SUC (4+2*i) < ncut /\ 4+2*i < ncut /\ 4+2*SUC i <= ncut` by decide_tac >>
  `!j. 4 <= j /\ j <= ncut ==> ci_mono cd (rawcomp j)` by suspend "row_monotonic" >>
  `EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs xs)`
    by suspend "raw_calls" >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    (qpat_assum `expr_sim_inv cenv cx env p0` mp_tac >>
     simp_tac (srw_ss()) [expr_sim_inv_split_def,expr_sim_inv_mods_def]) >>
  `cap < dimword (:256)` by suspend "raw_capacity" >>
  `w2n (n2w (LENGTH code):bytes32) <= LENGTH code` by simp[w2n_n2w,MOD_LESS_EQ] >>
  `ptr_covers Gr tnr datavar (rawobs 4) (w2n (n2w (LENGTH code):bytes32))` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `LENGTH code` >> simp[]) >>
  `(rawobs (pidx+4)).vs_current_bb = en.cs_current_bb /\
   (rawobs (pidx+4)).vs_inst_idx = LENGTH en.cs_current_insts` by
    (qpat_assum `!i. i <= ncut ==> ~(rawobs i).vs_halted /\ _` (qspec_then `pidx+4` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  `create_expr_prefix en cv explicit ctx func (rawobs (pidx+4)) (Ms (pidx+4)) (rawobs vp)` by
    (qpat_assum `!i. i < ncut ==> _ /\ fn_has_code _ _ _ /\ _` (qspec_then `pidx+4` mp_tac) >>
     (impl_tac >- decide_tac) >>
     qpat_assum `SUC (pidx+4) = vp` (fn h =>
       qpat_assum `rawcomp (pidx+4) = en` (fn e =>
         qpat_assum `rawcomp vp = cv` (fn v =>
           disch_then (ACCEPT_TAC o SIMP_RULE bool_ss [h,e,v] o CONJUNCT2 o CONJUNCT2))))) >>
  `FLAT (DROP pidx chunks') = Ms pidx ++ Ms (pidx+1) ++ Ms (pidx+2) ++ Ms (pidx+3) ++
     Ms (pidx+4) ++ (Ms vp ++ Ms (SUC vp))` by suspend "raw_payload_marks" >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac [ADD_CLAUSES,MULT_CLAUSES,pairTheory.PAIR_EQ] >> simp_tac bool_ss [] >> NO_TAC) >>
  REWRITE_TAC [ADD_CLAUSES,MULT_CLAUSES] >>
  TRY (qpat_assum `pidx = (4:num)+2*LENGTH xs` (SUBST1_TAC o SYM) >>
       pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >> NO_TAC) >>
  TRY (qpat_assum `rawcomp (pidx:num) = k` (SUBST1_TAC) >>
       pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >> NO_TAC) >>
  TRY (simp_tac bool_ss [Abbr `cap`] >> NO_TAC) >>
  TRY (qpat_assum `pidx+4+3 = (ncut:num)` SUBST1_TAC >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (rename1 `_ + _ <= (rawobs 4).vs_alloca_next` >> decide_tac >> NO_TAC) >>
  TRY (qpat_assum `data = Var datavar` (SUBST1_TAC o SYM) >>
       qpat_assum `lenop = Var lenvar` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_assum `lenop = Var lenvar` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  suspend "payload_row"
QED

Resume create_size_exit_raw[row_monotonic]:
  Induct >- simp[] >> strip_tac >> Cases_on `j = 3`
  >- (qpat_x_assum `j = 3` SUBST_ALL_TAC >>
      simp_tac (srw_ss()) [ci_mono_refl] >>
      qpat_assum `rawcomp 4 = cd` (simp_tac (srw_ss()) o (fn th => [th,ci_mono_refl]))) >>
  `4 <= j /\ j < ncut /\ j <= ncut` by decide_tac >>
  `ci_mono cd (rawcomp j)` by (first_x_assum irule >> first_assum ACCEPT_TAC ORELSE simp[]) >>
  `ci_mono (rawcomp j) (rawcomp (SUC j))` by
    (simp_tac (srw_ss()) [Abbr `rawcomp`] >>
     qpat_assum `!i. i < LENGTH cuts ==> ci_mono _ _` (qspec_then `j` mp_tac) >>
     qpat_assum `Abbrev (ncut = LENGTH cuts)`
       (fn h => simp_tac bool_ss [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] h)]) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp_tac (srw_ss()) []) >>
  irule ci_mono_trans >> qexists_tac `rawcomp j` >> simp[]
QED

Resume create_size_exit_raw[raw_calls]:
  qpat_assum `expr_body_pre cenv cx env (Call _ _ _ _) es`
    (mp_tac o REWRITE_RULE [expr_body_pre_split_def]) >>
  strip_tac >> drule expr_body_pre_mods_int_calls >> strip_tac >>
  drule body_inv_main_code >> strip_tac >>
  simp[EVERY_MEM] >> qx_gen_tac `call` >> disch_tac >>
  `MEM call (int_calls_expr (Call ann (CreateTarget RawCreate hs rof ks) (be::av::rest) df))` by
    (`!ys zs. int_calls_exprs (ys ++ zs) = int_calls_exprs ys ++ int_calls_exprs zs` by
       (POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[int_calls_expr_def]) >>
     qpat_assum `xs ++ _ = rest` (SUBST1_TAC o SYM) >>
     simp[int_calls_expr_def]) >>
  qpat_assum `EVERY (\c. FST c = NONE) _`
    (qspec_then `call` mp_tac o REWRITE_RULE[EVERY_MEM]) >>
  qpat_assum `EVERY (\c. ?tops. _) _`
    (qspec_then `call` mp_tac o REWRITE_RULE[EVERY_MEM]) >>
  Cases_on `call` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `get_module_code cx q = SOME tops'` mp_tac >>
  pure_asm_rewrite_tac [] >> simp_tac (srw_ss()) [] >>
  disch_then SUBST1_TAC >> first_assum ACCEPT_TAC
QED

Resume create_size_exit_raw[raw_capacity]:
  qpat_assum `expr_body_pre cenv cx env (Call _ _ _ _) es`
    (strip_assume_tac o MATCH_MP expr_body_pre_static_facts) >>
  drule create_raw_first_type >> strip_tac >>
  `!e. MEM e (be::av::rest) ==> expr_body_pre cenv cx env e es` by
    (gen_tac >> disch_tac >> drule_all create_raw_arg_body_pre >> simp[]) >>
  `EVERY (\e. expr_body_pre cenv cx env e es) xs` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     first_x_assum irule >> simp[] >>
     qpat_assum `xs ++ _ = rest` (SUBST1_TAC o SYM) >> simp[]) >>
  drule create_ctor_args_abi_bound >> strip_tac >>
  `bytelike_type_bound (lowered_value_type cenv be) <= n` by
    (irule raw_create_bytecode_bound >> (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`cx`,`env`,`es`] >> simp[]) >>
  `~(LENGTH rest < if hs then 1 else 0)` by
    (Cases_on `hs` >> simp[] >> qpat_assum `T ==> rest <> []` (mp_tac) >> simp[]) >>
  qpat_assum `alloc_limits_expr cenv (Call _ _ _ _)` mp_tac >>
  simp_tac (srw_ss()) [alloc_limits_expr_def,ext_call_alloc_ok_def] >>
  qpat_assum `(if hs then FRONT rest else rest) = xs` (pure_rewrite_tac o single) >>
  qpat_assum `xs <> []` (fn h => simp_tac bool_ss [LET_THM,h]) >>
  qpat_assum `expr_type be = _` (pure_rewrite_tac o single) >>
  simp_tac (srw_ss()) [vyperTypeSystemTheory.bytelike_type_bound_def,vyperASTTheory.bound_length_def] >>
  (strip_tac >> simp[Abbr `cap`,dimword_def,venomMemPropsTheory.dimindex_256] >> decide_tac)
QED

Resume create_size_exit_raw[raw_payload_marks]:
  `pidx < ncut /\ pidx+1 < ncut /\ pidx+2 < ncut /\ pidx+3 < ncut /\ pidx+4 < ncut` by decide_tac >>
  qpat_assum `!i. i < ncut ==> FLAT (DROP i chunks') = _`
    (fn th => map_every (fn i => qspec_then i mp_tac th >> (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then assume_tac) [`pidx`,`pidx+1`,`pidx+2`,`pidx+3`,`pidx+4`]) >>
  qpat_assum `SUC (pidx+4) = vp` (fn h =>
    qpat_assum `FLAT (DROP (pidx+4) chunks') = _` (assume_tac o SUBS [h])) >>
  `FLAT (DROP ncut chunks') = []` by
    (qpat_assum `LENGTH chunks' = ncut` (SUBST1_TAC o SYM) >> simp[DROP_LENGTH_NIL]) >>
  simp[DECIDE ``SUC n = n+1``,ADD_ASSOC,APPEND_ASSOC] >>
  `2 * LENGTH xs + 11 = ncut` by decide_tac >>
  pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC
QED

Resume create_size_exit_raw[payload_row]:
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH xs ==> SUC (4+2*i) < ncut /\ _`
    (qspec_then `i` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `4 <= 4+2*i /\ 4+2*i <= ncut /\ SUC i <= LENGTH xs /\ i <= LENGTH xs /\
   SUC (SUC (4+2*i)) = 4+2*SUC i /\ SUC (4+2*i) <= ncut` by decide_tac >>
  qpat_assum `!i. i <= LENGTH xs ==> rawcomp _ = EL i cs`
    (fn th => map_every (fn j => qspec_then j mp_tac th >> (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then assume_tac) [`i`,`SUC i`]) >>
  rpt (qpat_x_assum `!i. i < LENGTH xs ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!i. i < LENGTH xs ==> rawcomp _ = EL i mid /\ _`
    (qspec_then `i` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!i. i <= ncut ==> ~(rawobs i).vs_halted /\ _`
    (fn th => map_every (fn j => qspec_then j mp_tac th >> (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [pairTheory.PAIR_EQ]))
      [`SUC (4+2*i)`,`4+2*SUC i`]) >>
  qpat_assum `!j. 4 <= j /\ j <= ncut ==> ci_mono _ _`
    (qspec_then `4+2*i` mp_tac) >> (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (assume_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ci_mono_def]) >>
  qpat_assum `!i. i < ncut ==> FLAT (DROP i chunks') = _`
    (fn th => map_every (fn j => qspec_then j mp_tac th >> (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then assume_tac) [`4+2*i`,`SUC (4+2*i)`]) >>
  qpat_assum `!i. i < ncut ==> _ /\ fn_has_code _ _ _ /\ _`
    (qspec_then `SUC (4+2*i)` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `4+(2+2*i) = 4+2*SUC i` by decide_tac >>
  pop_assum SUBST1_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac [APPEND_ASSOC] >> simp_tac bool_ss [] >> NO_TAC) >>
  TRY (qpat_assum `rawcomp 4 = cd` SUBST1_TAC >> first_assum ACCEPT_TAC >> NO_TAC) >>
  suspend "payload_row_left"
QED

Resume create_size_exit_raw[payload_row_left]:
  Cases_on `exprs_can_mutate cenv (DROP (SUC i) xs)`
  >- (qpat_assum `exprs_can_mutate cenv (DROP (SUC i) xs)` (simp_tac bool_ss o single) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >> NO_TAC) >>
      qpat_assum `SUC (SUC (4+2*i)) = (4:num)+2*SUC i` (fn index =>
        qpat_assum `rawcomp (SUC (4+2*i)) = EL i mid` (fn from =>
          qpat_assum `fn_has_code (rawcomp (SUC (4+2*i))) _ func`
            (ACCEPT_TAC o PURE_REWRITE_RULE [index,from])))) >>
  qpat_assum `~exprs_can_mutate cenv (DROP (SUC i) xs)` (simp_tac bool_ss o single) >>
  disch_tac >>
  `expr_body_pre cenv cx env (EL i xs) p0` by
    (irule create_raw_arg_body_pre >> (conj_tac >- first_assum ACCEPT_TAC) >>
     goal_assum (drule_at Any) >> simp_tac (srw_ss()) [] >>
     qpat_assum `xs ++ _ = rest` (SUBST1_TAC o SYM) >> simp[EL_MEM]) >>
  `vv_type (ext_call_arg_value (lowered_value_type cenv (EL i xs)) (EL i vs)) =
   lowered_value_type cenv (EL i xs)` by
    (irule bodyFullExtCallPosAggregateTheory.extcall_operand_snapshot_type >>
     conj_tac
     >- (qexistsl_tac [`EL i cs`,`EL i mid`] >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`cx`,`env`,`p0`] >> first_assum ACCEPT_TAC) >>
  `EL i mid = EL (SUC i) cs` by
    (qpat_assum `~exprs_can_mutate cenv (DROP (SUC i) xs)` (fn mut =>
       qpat_assum `~is_word_type (lowered_value_type cenv (EL i xs))` (fn word =>
         qpat_assum `vv_type _ = lowered_value_type cenv (EL i xs)` (fn ty =>
           qpat_assum `compile_snapshot_vv _ _ _ (EL i mid) = (_,EL (SUC i) cs)`
             (mp_tac o SIMP_RULE bool_ss [mut,word,ty,compile_snapshot_vv_def,comp_return_def])))) >>
     simp_tac (srw_ss()) [pairTheory.PAIR_EQ]) >>
  qpat_assum `EL i mid = EL (SUC i) cs ==> _` (drule_then (ACCEPT_TAC o CONJUNCT1))
QED

Resume create_size_exit_raw[keywords]:
  qabbrev_tac `opt_salt = (salt_op:operand option)` >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `shctx` |-> `shadow_ctx`,
    `fnc` |-> `func`, `shfnc` |-> `shadow_func`, `d` |-> `dep'`,
    `e` |-> `be`, `entry` |-> `es`, `args` |-> `be::av::rest`, `salt` |-> `LAST rest`,
    `p` |-> `pval`, `G` |-> `Gval`, `tn` |-> `tnval`,
    `ca` |-> `cv`, `cm` |-> `cq`, `cn` |-> `sc`,
    `sca` |-> `hp`, `scm` |-> `hq`, `scn` |-> `hsc`,
    `amount_op` |-> `amount`, `salt_op` |-> `THE (opt_salt:operand option)`,
    `u` |-> `rawobs (vp:num)`, `m` |-> `rawobs (SUC vp)`, `n` |-> `s`,
    `ma` |-> `Ms (vp:num)`, `ms` |-> `Ms (SUC vp)`, `out` |-> `ee`]
    (SPEC_ALL create_raw_keywords_at_cuts)) >>
  (impl_tac >- suspend "keywords_pre") >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `err` strip_assume_tac)
    (qx_choose_then `source_vals` (qx_choose_then `source_ops` (qx_choose_then `source_state`
      (map_every assume_tac o CONJUNCTS)))))
  >- (disj2_tac >> qexists_tac `err` >> simp[]) >>
  suspend "extent"
QED

Resume create_size_exit_raw[keywords_pre]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >> NO_TAC) >>
  suspend "keywords_left"
QED

Resume create_size_exit_raw[keywords_left]:
  qpat_assum `case salte of NONE => _ | SOME _ => _` mp_tac >>
  Cases_on `hs` >> simp_tac (srw_ss()) [Abbr `salte`,Abbr `opt_salt`] >>
  strip_tac >> TRY (qpat_assum `cq = sc ==> _` (drule_then strip_assume_tac)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (sym_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
  pure_asm_rewrite_tac [] >> simp_tac (srw_ss()) []
QED


Resume create_size_exit_raw[extent]:
  `w2n w <= LENGTH (code:word8 list) + LENGTH (payload:word8 list)` by suspend "extent_bound" >>
  `2 * max_code_size < LENGTH (code:word8 list) + LENGTH (payload:word8 list)` by decide_tac >>
  disj1_tac >>
  `eval_create_operands cx RawCreate hs rof (MAP expr_type (be::av::rest))
     (blueprint_literal_offset cx hs (be::av::rest)) source_vals source_state =
     (INR (Error (RuntimeError "create initcode too large")),source_state)` by suspend "reject" >>
  qpat_assum `eval_create_operands _ _ _ _ _ _ source_vals source_state = (res,ee)`
    (fn h => qpat_assum `eval_create_operands _ _ _ _ _ _ source_vals source_state = (INR _,_)`
      (mp_tac o PURE_REWRITE_RULE [h])) >> simp_tac (srw_ss()) []
QED

Resume create_size_exit_raw[reject]:
  irule raw_operands_size_reject >>
  qexistsl_tac [`code`,`MAP expr_type xs`,`source_ops`,`payload`,
                `create_operand_layout RawCreate hs source_vals`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  pure_asm_rewrite_tac [] >> simp_tac bool_ss []
QED

Resume create_size_exit_raw[extent_bound]:
  irule (INST_TYPE [``:β`` |-> ``:expr``] create_raw_pre_dispatch_extent) >>
  qexistsl_tac [`cd`,`b`,`c`,`cq`,`xs`,`ctx`,`cv`,`data`,`explicit`,`func`,
                `rawobs 3`,`lenop`,`Ms 3`,`rawobs 4`,`s`,`sizeop`,`snap`,
                `rawobs vp`,`rawobs (SUC vp)`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >> NO_TAC) >>
  Cases_on `xs = []`
  >- (qpat_assum `xs = [] ==> prep = [] /\ _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      qpat_assum `xs = []` (fn h =>
        qpat_assum `if xs = [] then payload = [] /\ _ else _`
          (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [h])) >>
      pure_asm_rewrite_tac [COND_CLAUSES,ADD_CLAUSES,MULT_CLAUSES] >> simp_tac bool_ss []) >>
  suspend "extent_nonempty"
QED

Resume create_size_exit_raw[extent_nonempty]:
  qpat_assum `xs <> [] ==> compile_create_ctor_args _ _ _ _ = _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `xs <> [] ==> fn_has_code en cv func` (drule_then assume_tac) >>
  qpat_assum `xs <> []` (fn h =>
    qpat_assum `if xs = [] then payload = [] /\ _ else _`
      (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [h])) >>
  qpat_assum `xs <> []` (simp_tac bool_ss o single) >>
  qexistsl_tac [`en`,`rawobs (pidx+4)`,`alen`,`Ms (pidx+4)`] >>
  `pidx+4 <= ncut` by decide_tac >>
  qpat_assum `!i. i <= ncut ==> ~(rawobs i).vs_halted /\ _` (qspec_then `pidx+4` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE[pairTheory.PAIR_EQ]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (pure_asm_rewrite_tac [ADD_CLAUSES,MULT_CLAUSES] >> simp_tac bool_ss [] >> NO_TAC) >>
  qpat_assum `pidx = (4:num)+2*LENGTH xs` (SUBST1_TAC o SYM) >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qpat_assum `rawcomp 4 = cd` (fn h =>
    qpat_assum `!x v. not_fresh_at (rawcomp (4+2*0)) x /\ _ ==> lookup_var x (rawobs (pidx+4)) = _`
      (ACCEPT_TAC o SIMP_RULE bool_ss [ADD_CLAUSES,MULT_CLAUSES,h]))
QED

Finalise create_size_exit_raw

Theorem create_blueprint_payload_inputs_at_dispatch:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,(PG : (num # num) option list),fnc,shfnc)
    ce cx ty (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es
    (st0,sa,sb,hsa,hsb,vv,s0,G0,tn0) /\
  EVERY (create_operand_completed_ok cx) (create_operand_order (CreateFromBlueprint raw) hs args) /\
  create_expr_prefix sa sb (gas_explicit_sites ctx shctx) ctx fnc s0 marks s /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb fnc.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  (!x. MEM x (fn_insts fnc) /\ x.inst_id IN frag_ids sa sb /\
       MEM x.inst_opcode [CREATE;CREATE2] ==> x.inst_id <= inst.inst_id) /\
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value;offop;sz]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value;offop;sz;saltop])) /\
  eval_operand sz s = SOME w /\ 2 * max_code_size < w2n w /\
  eval_expr cx (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) = (res,out) /\
  valid_horizon cx st0 H out.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?target amount salt off ctors later target_op ca cprep cm cn cb cf sc
   sca scprep scm scn scb data len offset_op code prep app salt_op
   C Obs M R n j av aw p G tn.
    args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
    later = amount::((if hs then [salt] else []) ++ [off]) /\
    dest_AddressV av = SOME (w2w aw) /\ eval_operand target_op (Obs 1) = SOME aw /\
    (!x. target_op = Var x ==> not_fresh_at ca x) /\
    bind (eval_exprs cx (ctors ++ later))
      (\vs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p = (res,out) /\
    p.gas_obs = gas_explicit (R 1) (Obs 1).vs_gas_readings ++ tail /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv ce cx env p /\
    local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
    (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at ca x) /\
    (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at ca x) /\
    return_buf_frame d ce ca (Obs 1) /\ alloca_history fnc (Obs 1) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs 1)) /\
    (!f i z. frag_reachable ctx fnc (Obs 1) f i z ==> dalloca_no_wrap i z) /\
    (!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx p (Obs 1) /\ storage_well_formed_on cx p (FST h) /\
      ghost_inv_at (DF h) lo d ce cx p G tn (Obs 1)) /\
    C 1 = ca /\ C j = cprep /\ C (SUC j) = cm /\ C (j+2) = cn /\
    C (j+3) = cb /\ C (j+4) = cf /\ C n = sc /\ j = SUC (LENGTH prep) /\ j+4 <= n /\
    n = j+4+LENGTH app /\ (!i. i < LENGTH app ==> C (j+5+i) = EL i app) /\
    Obs n = s /\ R n = [] /\
    (!i. i <= n ==> ~(Obs i).vs_halted /\
      (Obs i).vs_current_bb = (C i).cs_current_bb /\
      (Obs i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
      ?x. ctor_segment_fetch fnc (Obs i) = SOME x /\ x.inst_opcode <> PHI /\
        (C i).cs_next_id <= x.inst_id) /\
    (!i k. i <= k /\ k <= n ==> ci_mono (C i) (C k) /\ fn_has_code (C i) (C k) fnc) /\
    (!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
      create_expr_prefix (C i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx fnc
        (Obs i) (M i) (Obs (SUC i)) /\ R i = M i ++ R (SUC i) /\
      (C i = C (SUC i) ==> Obs (SUC i) = Obs i /\ M i = [])) /\
    compile_create_blueprint_args compile_expr ce raw later ctors ca = ((data,len),cprep) /\
    compile_create_blueprint_args compile_expr ce raw (MAP gas_shadow_expr later)
      (MAP gas_shadow_expr ctors) sca = ((data,len),scprep) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cprep,sca,scprep) /\
    lower_value compile_expr ce (expr_type amount) amount cprep = (value,cm) /\
    lower_value compile_expr ce (expr_type amount) (gas_shadow_expr amount) scprep = (value,scm) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (cprep,cm,scprep,scm) /\
    (if hs then ?sop. salt_op = SOME sop /\
      lower_value compile_expr ce (expr_type salt) salt cm = (sop,cn) /\
      lower_value compile_expr ce (expr_type salt) (gas_shadow_expr salt) scm = (sop,scn) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (cm,cn,scm,scn)
     else salt_op = NONE /\ cn = cm /\ scn = scm) /\
    ((?oty i. origin_fold_value off = Literal oty (IntL i) /\
       offset_op = Lit (i2w i) /\ cb = cn /\ scb = scn) \/
     (lower_value compile_expr ce (expr_type off) off cn = (offset_op,cb) /\
      lower_value compile_expr ce (expr_type off) (gas_shadow_expr off) scn = (offset_op,scb) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (cn,cb,scn,scb))) /\
    compile_create_blueprint_check (is_int_literal (origin_fold_value off)) target_op offset_op cb = (code,cf) /\
    create_blueprint_append_itinerary target_op offset_op code data len cf app offop sz /\
    (if raw then
      ?e v saved raw_op c0 c1 c2 c3 h0 ssaved h1 h2.
        ctors = [e] /\ prep = [c0;c1;c2;c3;cprep] /\
        j = 6 /\ C 2 = c0 /\ C 3 = c1 /\ C 4 = c2 /\ C 5 = c3 /\
        R 1 = M 1 ++ (M 2 ++ (M 3 ++ (M 4 ++ M 5 ++ R j))) /\
        compile_expr ce (expr_type e) e ca = (v,c0) /\
        compile_snapshot_vv ce (exprs_can_mutate ce later) v c0 = (saved,c1) /\
        unwrap_value ce saved c1 = (raw_op,c2) /\
        emit_op MLOAD [raw_op] c2 = (len,c3) /\ emit_op ADD [raw_op;Lit 32w] c3 = (data,cprep) /\
        compile_expr ce (expr_type e) (gas_shadow_expr e) sca = (v,h0) /\
        compile_snapshot_vv ce (exprs_can_mutate ce (MAP gas_shadow_expr later)) v h0 = (ssaved,h1) /\
        unwrap_value ce ssaved h1 = (raw_op,h2) /\
        expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,c0,sca,h0) /\
        expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,c2,sca,h2) /\
        fn_has_code c0 c1 fnc /\ fn_has_code c2 cprep fnc
     else if ctors = [] then j = 1 /\ cprep = ca /\ data = Lit 0w /\ len = Lit 0w
     else ?vals k cs mid vvs buf a hk ha hcs hmid q.
       q = 1+2*LENGTH ctors /\ j = q+2 /\ C q = k /\ C (SUC q) = a /\
       R q = M q ++ M (SUC q) ++ R j /\
       compile_create_ctor_args compile_expr ce ctors ca = (vals,k) /\
       create_itinerary_ctor_rows ce ctors vals ca k cs mid vvs /\
       compile_alloc_buffer (abi_size_bound ce.ce_struct_fields
         (TupleT (MAP (lowered_value_type ce) ctors))) k = (buf,a) /\
       compile_abi_encode_values_to_buf ce buf.buf_operand
         (ZIP (vals,MAP (lowered_value_type ce) ctors)) a = (len,cprep) /\
       data = buf.buf_operand /\
       expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,k,sca,hk) /\
       expr_sim_full_code (ctx,shctx,fnc,shfnc) (k,a,hk,ha) /\
       expr_sim_full_code (ctx,shctx,fnc,shfnc) (a,cprep,ha,scprep) /\
       (!i. i <= LENGTH ctors ==> C (1+2*i) = EL i cs) /\
       (!i. i < LENGTH ctors ==>
         C (SUC (1+2*i)) = EL i mid /\
         R (1+2*i) = (M (1+2*i) ++ M (SUC (1+2*i))) ++ R (1+2*SUC i) /\
         create_expr_prefix (EL i cs) (EL (SUC i) cs) (gas_explicit_sites ctx shctx) ctx fnc
           (Obs (1+2*i)) (M (1+2*i) ++ M (SUC (1+2*i))) (Obs (1+2*SUC i)) /\
         compile_expr ce (expr_type (EL i ctors)) (gas_shadow_expr (EL i ctors)) (EL i hcs) =
           (EL i vvs,EL i hmid) /\
         compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) ctors))
           (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (EL i vvs)) (EL i hmid) =
           (EL i vals,EL (SUC i) hcs) /\
         expr_sim_full_code (ctx,shctx,fnc,shfnc) (EL i cs,EL i mid,EL i hcs,EL i hmid) /\
         expr_sim_full_code (ctx,shctx,fnc,shfnc) (EL i cs,EL (SUC i) cs,EL i hcs,EL (SUC i) hcs)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  `?result. compile_create_call compile_expr ce (CreateFromBlueprint raw) hs rof args sa = (result,sb)` by
    (qpat_assum `compile_expr _ _ (Call _ _ _ _) _ = _` mp_tac >>
     rewrite_tac[exprSimSendTheory.compile_expr_call,compile_call_def] >>
     Cases_on `compile_create_call compile_expr ce (CreateFromBlueprint raw) hs rof args sa` >>
     simp[as_stack_val_def]) >>
  `MEM inst.inst_opcode [CREATE;CREATE2]` by fs[] >>
  drule_all create_size_prefix_cuts >>
  strip_tac >>
  suspend "layout"
QED

Resume create_blueprint_payload_inputs_at_dispatch[layout]:

  `value' = value /\ bufop = offop /\ len = sz /\ inst.inst_id = sc.cs_next_id /\ inst.inst_opcode <> PHI` by
    (Cases_on `salt` >> qpat_x_assum `inst = _` (SUBST_ALL_TAC o SIMP_RULE (srw_ss()) []) >>
     fs[mk_inst_def]) >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`value' = value`,`bufop = offop`,`len = sz`] >>
  qpat_x_assum `create_call_itinerary _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss
       [create_call_itinerary_def,vyperASTTheory.create_kind_case_def,create_blueprint_itinerary_def]) >>
  qabbrev_tac `later = value_e::TAKE (if hs then 2 else 1) rest` >>
  qabbrev_tac `suffix = if hs then TL rest else rest` >>
  `?se oe ctors. args = target_e::value_e::((if hs then [se] else []) ++ oe::ctors) /\
    TL suffix = ctors /\ HD suffix = oe /\
    later = value_e::((if hs then [se] else []) ++ [oe]) /\
    (if hs then SOME (HD rest) else NONE) = (if hs then SOME se else NONE)` by
    (Cases_on `hs` >> Cases_on `rest` >> fs[Abbr `later`,Abbr `suffix`] >>
     TRY (Cases_on `t` >> fs[])) >>
  map_every (fn q => qpat_x_assum q (fn h => rule_assum_tac (PURE_REWRITE_RULE[h])))
    [`TL suffix = ctors`,`HD suffix = oe`,
     `(if hs then SOME (HD rest) else NONE) = (if hs then SOME se else NONE)`] >>
  `LAST app = sc` by
    (`app <> []` by
       (qpat_assum `create_blueprint_append_itinerary _ _ _ _ _ _ app _ _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> Cases_on `args_len = Lit 0w` >>
        simp[create_blueprint_append_itinerary_def, PULL_EXISTS] >> metis_tac[NOT_CONS_NIL]) >>
     `sa::cuts = (sa::a::(prep ++ [c;d';e;f])) ++ app` by simp[APPEND_ASSOC] >>
     qpat_assum `LAST (sa::cuts) = sc` (mp_tac o SYM) >>
     qpat_assum `sa::cuts = _` (pure_rewrite_tac o single) >> simp[LAST_APPEND_NOT_NIL]) >>
  `expr_sim_full_code (ctx,shctx,fnc,shfnc) (sa,sb,hsa,hsb)` by simp[expr_sim_full_code_def] >>
  drule_all create_blueprint_outer_paired_code >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  suspend "observed"
QED

Resume create_blueprint_payload_inputs_at_dispatch[observed]:
  qmatch_asmsub_rename_tac `marks = FLAT mark_rows` >>
  qabbrev_tac `C = \i. EL i (sa::cuts)` >>
  qabbrev_tac `Obs = \i. EL i states` >>
  qabbrev_tac `M = \i. EL i mark_rows` >>
  qabbrev_tac `R = \i. FLAT (DROP i mark_rows)` >>
  qabbrev_tac `n = LENGTH cuts` >> qabbrev_tac `j = SUC (LENGTH prep)` >>
  `!i. i < n ==> create_expr_prefix (C i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx fnc
    (Obs i) (M i) (Obs (SUC i))` by
    (qpat_assum `!i. i < n ==> create_expr_prefix _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [Abbr `C`,Abbr `Obs`,Abbr `M`,Abbr `n`,EL,HD,TL]) >>
  map_every (fn q => qpat_assum q (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]))
    [`Abbrev (C = _)`,`Abbrev (Obs = _)`,`Abbrev (M = _)`,`Abbrev (R = _)`,
     `Abbrev (n = _)`,`Abbrev (j = _)`] >>
  `ctor_segment_fetch fnc s = SOME inst` by
    (qpat_assum `lookup_block s.vs_current_bb _ = SOME bb` (fn th =>
       simp_tac bool_ss [ctor_segment_fetch_def,th,optionTheory.OPTION_BIND_def]) >>
     first_assum ACCEPT_TAC) >>
  drule_all create_blueprint_observed_bands >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "address"
QED

Resume create_blueprint_payload_inputs_at_dispatch[address]:
  `1 <= n` by decide_tac >>
  qpat_assum `!i. i <= n ==> ~(Obs i).vs_halted /\ _`
    (qspec_then `1` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `C 1 = a` (fn th =>
    map_every (fn q => qpat_assum q (assume_tac o REWRITE_RULE[th]))
      [`(Obs 1).vs_current_bb = _`,`(Obs 1).vs_inst_idx = _`]) >>
  qpat_assum `marks = M 0 ++ R 1` (fn th =>
    qpat_assum `eval_expr cx (Call ann _ args df) _ = _`
      (assume_tac o ONCE_REWRITE_RULE[th])) >>
  drule_all create_blueprint_address_at_cut >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> suspend "pack"
QED
Resume create_blueprint_payload_inputs_at_dispatch[pack]:
  `n = j+4+LENGTH app` by
    (qpat_assum `n = LENGTH cuts` (pure_rewrite_tac o single) >>
     qpat_assum `cuts = _` (pure_rewrite_tac o single) >>
     qpat_assum `j = SUC (LENGTH prep)` (pure_rewrite_tac o single) >>
     POP_ASSUM_LIST (K all_tac) >> simp[LENGTH_APPEND] >> decide_tac) >>
  `!i. i < LENGTH app ==> C (j+5+i) = EL i app` by
    (rpt strip_tac >>
     `j+5+i = SUC (i+(j+4))` by
       (POP_ASSUM_LIST (K all_tac) >> simp[arithmeticTheory.ADD1] >> decide_tac) >>
     qpat_assum `C = _` (pure_rewrite_tac o single) >>
     qpat_assum `j+5+i = _` (pure_rewrite_tac o single) >>
     simp_tac bool_ss [EL,TL] >>
     qpat_assum `DROP (j+4) cuts = app` (pure_rewrite_tac o single o SYM) >>
     sym_tac >> irule listTheory.EL_DROP >>
     qpat_assum `n = LENGTH cuts` (pure_rewrite_tac o single o SYM) >>
     qpat_assum `n = j+4+LENGTH app` (pure_rewrite_tac o single) >>
     qpat_assum `i < LENGTH app` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qexistsl_tac [`target_e`,`value_e`,`se`,`oe`,`ctors`,`later`,`target`,`a`,`b`,`c`,`d'`,`e`,`f`,`sc`,
    `hca`,`hb`,`hc`,`hd`,`he`,`args_buf`,`args_len`,`off`,`code`,`prep`,`app`,`salt`,
    `C`,`Obs`,`M`,`R`,`n`,`j`,`av`,`aw`,`p`,`G`,`tn`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "payload"
QED
Resume create_blueprint_payload_inputs_at_dispatch[payload]:
  Cases_on `raw` >> simp_tac bool_ss [COND_CLAUSES]
  >- suspend "raw" >>
  Cases_on `ctors = []`
  >- (qpat_assum `ctors = []` (simp_tac bool_ss o single) >> suspend "empty") >>
  qpat_assum `ctors <> []` (simp_tac bool_ss o single) >> suspend "abi"
QED

Resume create_blueprint_payload_inputs_at_dispatch[raw]:
  `?ex. ctors = [ex]` by
    (drule expr_body_pre_static_facts >> disch_then (assume_tac o cj 2) >>
     qpat_assum `args = target_e::value_e::_` mp_tac >>
     qpat_assum `well_typed_expr _ (Call _ _ _ _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `hs` >>
     simp[well_typed_expr_def,create_arg_types_ok_def,MAP_EQ_CONS] >>
     rpt strip_tac >> gvs[MAP_EQ_CONS] >> metis_tac[]) >>
  qpat_assum `ctors = [ex]` (fn th =>
    qpat_assum `create_blueprint_args_itinerary _ T _ ctors _ _ _ _ _`
      (mp_tac o SIMP_RULE (srw_ss()) [create_blueprint_args_itinerary_def,th]) >>
    qpat_assum `compile_create_blueprint_args _ _ T _ ctors _ = _`
      (assume_tac o REWRITE_RULE[th]) >>
    qpat_assum `compile_create_blueprint_args _ _ T _ (MAP gas_shadow_expr ctors) _ = _`
      (assume_tac o REWRITE_RULE[th,MAP])) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!cm cs cu cl. prep = [cm;cs;cu;cl;b] ==> _`
    (fn th => drule th >> disch_then (map_every assume_tac o CONJUNCTS)) >>
  drule_all create_blueprint_raw_payload_paired_code >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_rename_tac `compile_expr ce (expr_type ex) ex a = (v0,k0)` >>
  qmatch_asmsub_rename_tac `compile_snapshot_vv ce (exprs_can_mutate ce later) v0 k0 = (snap0,k1)` >>
  qmatch_asmsub_rename_tac `unwrap_value ce snap0 k1 = (ptr0,k2)` >>
  qmatch_asmsub_rename_tac `emit_op MLOAD [ptr0] k2 = (args_len,k3)` >>
  qmatch_asmsub_rename_tac `compile_expr ce (expr_type ex) (gas_shadow_expr ex) hca = (v0,sk0)` >>
  qmatch_asmsub_rename_tac `compile_snapshot_vv ce (exprs_can_mutate ce (MAP gas_shadow_expr later)) v0 sk0 = (ssnap0,sk1)` >>
  qmatch_asmsub_rename_tac `unwrap_value ce ssnap0 sk1 = (ptr0,sk2)` >>
  qexistsl_tac [`ex`,`v0`,`snap0`,`ptr0`,`sk0`,`ssnap0`,`sk1`,`sk2`] >>
  map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
    [`C 2 = _`,`C 3 = _`,`C 4 = _`,`C 5 = _`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_blueprint_payload_inputs_at_dispatch[empty]:
  qpat_assum `ctors = []` (fn th =>
    qpat_assum `create_blueprint_args_itinerary _ F _ ctors _ _ _ _ _`
      (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [create_blueprint_args_itinerary_def,th])) >>
  conj_tac >-
    (map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
       [`j = SUC (LENGTH prep)`,`prep = []`] >> EVAL_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_blueprint_payload_inputs_at_dispatch[abi]:
  qpat_assum `ctors <> []` (fn th =>
    qpat_assum `create_blueprint_args_itinerary _ F _ ctors _ _ _ _ _`
      (mp_tac o SIMP_RULE (srw_ss()) [create_blueprint_args_itinerary_def,th])) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `args_buf = _` (fn th =>
    qpat_assum `compile_create_blueprint_args _ _ F _ (MAP gas_shadow_expr ctors) _ = _`
      (assume_tac o REWRITE_RULE[th])) >>
  drule_all create_blueprint_abi_payload_paired_code >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `1+2*LENGTH ctors = 1+2*LENGTH ctors` by REFL_TAC >>
  qpat_assum `!vals k cs mid vv a' p. create_itinerary_ctor_rows _ _ _ _ _ _ _ _ /\ _ ==> _`
    (fn th => drule_all th >> disch_then (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`vals`,`cs`,`mid`,`vs`,`buf`,`hk`,`hm`,`hcs`,`hmid`] >>
  map_every (fn q => qpat_assum q (pure_rewrite_tac o single))
    [`C (1+2*LENGTH ctors) = k`,`C (SUC (1+2*LENGTH ctors)) = m`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH ctors ==> C (SUC (1+2*i)) = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise create_blueprint_payload_inputs_at_dispatch

Theorem create_size_exit_blueprint:
  !cx ty raw hs rof ks args d.
    EVERY (create_operand_completed_ok cx) (create_operand_order (CreateFromBlueprint raw) hs args) ==>
    create_expr_size_exit cx (Call ty (CreateTarget (CreateFromBlueprint raw) hs rof ks) args d)
Proof
  rpt gen_tac >> disch_tac >>
  rewrite_tac[create_expr_size_exit_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_blueprint_payload_inputs_at_dispatch >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
  >- (disj2_tac >> first_assum ACCEPT_TAC) >>
  rename [`body_inv tops ctx ce cx`, `shadow_body_inv tops ctx shctx`,
          `eval_operand offset_word s = SOME w`, `valid_horizon cx st0 H out.storage_trace`,
          `C (j+3) = cb`, `Obs n = s`] >>
  suspend "dispatch"
QED

Resume create_size_exit_blueprint[dispatch]:
  rename [`valid_horizon cx st0 H out.storage_trace`,
    `args = target::amount::((if hs then [salt_e] else []) ++ off_e::ctors)`,
    `C j = cprep`, `C (SUC j) = cm`,
    `C (j+2) = cn`, `C (j+4) = cf`, `C n = sc`,
    `eval_operand target_op (Obs 1) = SOME aw`,
    `create_blueprint_append_itinerary target_op offset_op code data len cf app offop sz`,
    `p.gas_obs = gas_explicit (R 1) _ ++ tail`,
    `later = amount::_`, `bind _ (\vs. _ (av::vs)) p = _`] >>
  map_every (fn (i,bound) =>
    bound by decide_tac >>
    qpat_assum `!i. i <= n ==> ~(Obs i).vs_halted /\ _`
      (qspec_then i (drule_then (map_every assume_tac o CONJUNCTS))))
    [(`1`,`1 <= n`),(`j`,`j <= n`),(`SUC j`,`SUC j <= n`),
     (`j+2`,`j+2 <= n`),(`j+3`,`j+3 <= n`),(`j+4`,`j+4 <= n`)] >>
  map_every (fn (i,bound) =>
    bound by decide_tac >>
    qpat_assum `!i. i < n ==> (C i).cs_next_id <= _ /\ _`
      (qspec_then i (drule_then (map_every assume_tac o CONJUNCTS))))
    [(`j`,`j < n`),(`SUC j`,`SUC j < n`),(`j+2`,`j+2 < n`),(`j+3`,`j+3 < n`)] >>
  `SUC (SUC j) = j+2 /\ SUC (j+2) = j+3 /\ SUC (j+3) = j+4` by decide_tac >>
  `R j = M j ++ (M (SUC j) ++ (M (j+2) ++ R (j+3)))` by
    (qpat_assum `R j = _` (pure_once_rewrite_tac o single) >>
     qpat_assum `R (SUC j) = _` (pure_once_rewrite_tac o single) >>
     `SUC (SUC j) = j+2` by decide_tac >>
     qpat_assum `SUC (SUC j) = j+2` (pure_once_rewrite_tac o single) >>
     qpat_assum `R (j+2) = _` (pure_once_rewrite_tac o single) >> simp[arithmeticTheory.ADD1]) >>
  suspend "payload_join"
QED

Resume create_size_exit_blueprint[payload_join]:
  rename [`eval_expr cx (Call ty _ args d) _ = (res,srcout)`,
    `p.gas_obs = gas_explicit (R 1) _ ++ tail`, `return_buf_frame depr ce ca (Obs 1)`] >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?cvs bs qp Gp tnp.
     LENGTH cvs = LENGTH ctors /\
     (if raw then cvs = [BytesV bs] else
        encode_create_ctor_args (get_tenv cx) (MAP expr_type ctors) cvs = SOME bs) /\
     bind (eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])))
       (\kvs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
         (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) qp = (res,srcout) /\
     eval_operand len (Obs j) = SOME (n2w (LENGTH bs)) /\
     (!x. len = Var x ==> not_fresh_at cprep x) /\
     eval_operand target_op (Obs j) = SOME aw /\
     (!x. target_op = Var x ==> not_fresh_at cprep x) /\
     expr_sim_inv ce cx env qp /\ local_ptrs_reserved ce cprep /\
     (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
     (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
     return_buf_frame depr ce cprep (Obs j) /\ alloca_history func (Obs j) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs j)) /\
     (!f i z. frag_reachable ctx func (Obs j) f i z ==> dalloca_no_wrap i z) /\
     (!h. valid_horizon cx st0 h qp.storage_trace ==>
       stmt_state_rel h ctx func ce cx qp (Obs j) /\ storage_well_formed_on cx qp (FST h) /\
       ghost_inv_at (DF h) lo depr ce cx qp Gp tnp (Obs j)) /\
     qp.gas_obs = gas_explicit (R j) (Obs j).vs_gas_readings ++ tail`
    suffices_by
      (disch_then (DISJ_CASES_THEN2 assume_tac
        (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
       >- (disj2_tac >> first_assum ACCEPT_TAC) >> suspend "keywords") >>
  Cases_on `raw` >- suspend "raw_payload" >> suspend "abi_payload"
QED

Resume create_size_exit_blueprint[keywords]:
  rename [`eval_operand len (Obs j) = SOME (n2w (LENGTH payload))`,
    `expr_sim_inv ce cx env paystate`, `LENGTH cvs = LENGTH ctors`] >>
  map_every (fn q => qpat_assum q (fn th => rule_assum_tac (REWRITE_RULE[th]) >> assume_tac th))
    [`SUC (SUC j) = j+2`,`SUC (j+2) = j+3`,`SUC (j+3) = j+4`,
     `C j = cprep`,`C (SUC j) = cm`,`C (j+2) = cn`,`C (j+3) = cb`,`C (j+4) = cf`] >>
  `?sop. if hs then
      lower_value compile_expr ce (expr_type salt_e) salt_e cm = (sop,cn) /\
      lower_value compile_expr ce (expr_type salt_e) (gas_shadow_expr salt_e) scm = (sop,scn) /\
      expr_sim_full_code (ctx,shctx,func,shadow_func) (cm,cn,scm,scn) /\
      create_expr_prefix cm cn (gas_explicit_sites ctx shctx) ctx func (Obs (SUC j)) (M (SUC j)) (Obs (j+2)) /\
      (Obs (j+2)).vs_current_bb = cn.cs_current_bb /\ (Obs (j+2)).vs_inst_idx = LENGTH cn.cs_current_insts
    else cn = cm /\ scn = scm /\ Obs (j+2) = Obs (SUC j) /\ M (SUC j) = []` by
    (qpat_assum `if hs then ?sop. salt_op = SOME sop /\ _ else _` mp_tac >>
     Cases_on `hs` >> simp_tac bool_ss [COND_CLAUSES]
     >- (disch_then (qx_choose_then `sop` (map_every assume_tac o CONJUNCTS)) >>
         qexists_tac `sop` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `cm = cn` by (sym_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `cm = cn ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `(?oty i. origin_fold_value off_e = Literal oty (IntL i) /\
       offset_op = Lit (i2w i) /\ cb = cn /\ scb = scn /\ Obs (j+3) = Obs (j+2) /\ M (j+2) = []) \/
     lower_value compile_expr ce (expr_type off_e) off_e cn = (offset_op,cb) /\
     lower_value compile_expr ce (expr_type off_e) (gas_shadow_expr off_e) scn = (offset_op,scb) /\
     expr_sim_full_code (ctx,shctx,func,shadow_func) (cn,cb,scn,scb) /\
     create_expr_prefix cn cb (gas_explicit_sites ctx shctx) ctx func (Obs (j+2)) (M (j+2)) (Obs (j+3)) /\
     (Obs (j+3)).vs_current_bb = cb.cs_current_bb /\ (Obs (j+3)).vs_inst_idx = LENGTH cb.cs_current_insts`
    suffices_by (disch_then assume_tac >> suspend "keyword_apply") >>
  qpat_assum `(?oty i. origin_fold_value off_e = _ /\ _) \/ _` strip_assume_tac
     >- (`cn = cb` by (sym_tac >> first_assum ACCEPT_TAC) >>
         qpat_assum `cn = cb ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
         disj1_tac >>
         qmatch_asmsub_rename_tac `origin_fold_value off_e = Literal lit_ty (IntL lit_i)` >>
         qexistsl_tac [`lit_ty`,`lit_i`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume create_size_exit_blueprint[keyword_apply]:
  `paystate.gas_obs = gas_explicit (M j ++ (M (SUC j) ++ (M (j+2) ++ R (j+3))))
     (Obs j).vs_gas_readings ++ tail` by
    (qpat_assum `paystate.gas_obs = _` (pure_rewrite_tac o single) >>
     qpat_assum `R j = M j ++ (M (SUC j) ++ _)` (pure_once_rewrite_tac o single) >> REFL_TAC) >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?kvs q ops ow.
    eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])) paystate = (INL kvs,q) /\
    eval_create_operands cx (CreateFromBlueprint raw) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs)) q = (res,srcout) /\
    dest_create_args (CreateFromBlueprint raw) hs
      (create_operand_layout (CreateFromBlueprint raw) hs (av::(cvs ++ kvs))) = SOME ops /\
    ops.co_code_src = AddressCodeSource (w2w aw) /\ ops.co_ctor_args = cvs /\
    ops.co_code_offset = SOME (w2n ow) /\
    eval_operand target_op (Obs (j+3)) = SOME aw /\ eval_operand offset_op (Obs (j+3)) = SOME ow /\
    (!x. offset_op = Var x ==> not_fresh_at cb x) /\
    (lookup_account (w2w aw) q.accounts).code = (lookup_account (w2w aw) (Obs (j+3)).vs_accounts).code /\
    (!x w. not_fresh_at cprep x /\ lookup_var x (Obs j) = SOME w ==>
       lookup_var x (Obs (j+3)) = SOME w)` suffices_by
    (disch_then (DISJ_CASES_THEN2 assume_tac
        (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
     >- (disj2_tac >> first_assum ACCEPT_TAC) >> suspend "extent") >>
  irule create_blueprint_keywords_at_cuts >> suspend "keyword_premises"
QED
Resume create_size_exit_blueprint[keyword_premises]:
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
    (qexistsl_tac [`ctors`,`target`] >> rpt conj_tac >> first_assum ACCEPT_TAC))) >>
  qexistsl_tac [`DF`,`Gp`,`H`,`value`,`ty`,`ce`,`cm`,`cn`,`ctx`,`depr`,`d`,`es`,`env`,
    `func`,`ks`,`lo`,`Obs (SUC j)`,`M j`,`M (j+2)`,`M (SUC j)`,`Obs (j+2)`,`R (j+3)`,
    `sop`,`scprep`,`scb`,`scm`,`scn`,`shctx`,`shadow_func`,`st0`,`tail`,`tnp`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume create_size_exit_blueprint[extent]:
  rename [`ops.co_code_offset = SOME (w2n ow)`,
    `(lookup_account (w2w aw) qs.accounts).code = _`,
    `eval_create_operands _ _ _ _ _ _ (av::(cvs ++ kvs)) qs = _`] >>
  `?ca1 ca2 ca3.
    emit_op ADD [code;len] cf = (sz,ca1) /\
    compile_alloc_dynamic sz ca1 = (offop,ca2) /\
    emit_void EXTCODECOPY [target_op;offop;offset_op;code] ca2 = ((),ca3) /\
    C (j+5) = ca1 /\ j+5 <= n /\
    (if len = Lit 0w then sc = ca3 else
      ?args_dest ca4. emit_op ADD [offop;code] ca3 = (args_dest,ca4) /\
        compile_copy_memory_dynamic args_dest data len ca4 = ((),sc))` by
    (qpat_assum `create_blueprint_append_itinerary _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[create_blueprint_append_itinerary_def]) >>
     rename [`emit_op ADD [code;len] cf = (sz,ca1)`,
       `compile_alloc_dynamic sz ca1 = (offop,ca2)`,
       `emit_void EXTCODECOPY _ ca2 = ((),ca3)`] >>
     qexistsl_tac [`ca1`,`ca2`,`ca3`] >>
     Cases_on `len = Lit 0w` >>
     FIRST (map (fn pat => qpat_assum pat (fn h =>
       qpat_assum `if len = Lit 0w then app = _ else _`
         (strip_assume_tac o REWRITE_RULE[h,COND_CLAUSES])))
       [`len = Lit 0w`,`len <> Lit 0w`]) >>
     `LENGTH app = 3 \/ LENGTH app = 5` by simp[] >>
     `0 < LENGTH app /\ LENGTH app - 1 < LENGTH app /\
       j + 5 + (LENGTH app - 1) = n /\ j + 5 <= n` by decide_tac >>
     `C (j+5) = ca1` by
       (qpat_assum `!i. i < LENGTH app ==> C (j+5+i) = EL i app`
         (qspec_then `0` (drule_then mp_tac)) >>
        qpat_assum `app = ca1::ca2::ca3::_` (fn th => simp_tac (srw_ss()) [th])) >>
     `C n = EL (LENGTH app - 1) app` by
       (qpat_assum `!i. i < LENGTH app ==> C (j+5+i) = EL i app`
          (qspec_then `LENGTH app - 1` mp_tac) >> simp_tac bool_ss [] >>
        disch_then drule >> disch_then (fn th =>
          qpat_assum `j + 5 + (LENGTH app - 1) = n` (ACCEPT_TAC o C (REWRITE_RULE o single) th))) >>
     `sc = EL (LENGTH app - 1) app` by
       (qpat_assum `C n = sc` (fn th => pop_assum (ACCEPT_TAC o REWRITE_RULE[th]))) >>
     qpat_assum `app = ca1::ca2::ca3::_` (fn th =>
       pop_assum (assume_tac o SIMP_RULE (srw_ss()) [th])) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     FIRST (map (fn pat => qpat_assum pat (pure_rewrite_tac o single))
       [`len = Lit 0w`,`len <> Lit 0w`]) >>
     simp_tac bool_ss [COND_CLAUSES] >>
     (first_assum ACCEPT_TAC ORELSE
      (goal_assum (drule_at Any) >> qpat_assum `sc = _` (pure_rewrite_tac o single) >>
       first_assum ACCEPT_TAC))) >>
  rename [`C (j+5) = ca1`, `compile_alloc_dynamic sz ca1 = (offop,ca2)`,
    `emit_void EXTCODECOPY _ ca2 = ((),ca3)`] >>
  suspend "extent_geometry"
QED
Resume create_size_exit_blueprint[extent_geometry]:
  `cf.cs_current_bb = cb.cs_current_bb /\
   cf.cs_current_insts = cb.cs_current_insts ++ emitted_insts cb cf /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts cb cf)` by
    (qpat_assum `compile_create_blueprint_check _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `is_int_literal (origin_fold_value off_e)` >>
     simp[compile_create_blueprint_check_def,emitHelperTheory.emit_op_def,emitHelperTheory.emit_void_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def,fresh_id_def,fresh_var_def,emit_def] >>
     strip_tac >> gvs[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >>
     simp[mk_inst_def,is_terminator_def]) >>
  `ca1.cs_current_bb = cf.cs_current_bb /\
   ca1.cs_current_insts = cf.cs_current_insts ++ emitted_insts cf ca1 /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts cf ca1)` by
    (qpat_assum `emit_op ADD [code;len] cf = (sz,ca1)` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule emitted_insts_emit_op >> drule emit_op_facts >>
     strip_tac >> simp[mk_inst_def,is_terminator_def]) >>
  `sc.cs_current_bb = ca1.cs_current_bb /\
   sc.cs_current_insts = ca1.cs_current_insts ++ emitted_insts ca1 sc /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts ca1 sc)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`if len = Lit 0w then sc = ca3 else _`,
        `emit_void EXTCODECOPY _ ca2 = ((),ca3)`, `compile_alloc_dynamic sz ca1 = (offop,ca2)`] >>
     rpt (pop_assum kall_tac) >>
     Cases_on `len = Lit 0w` >> simp[compile_alloc_dynamic_def,compile_copy_memory_dynamic_def,
       emitHelperTheory.emit_op_def,emitHelperTheory.emit_void_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
       fresh_id_def,fresh_var_def,emit_def] >>
     rpt strip_tac >> gvs[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >>
     simp[mk_inst_def,is_terminator_def]) >>
  suspend "extent_runs"
QED
Resume create_size_exit_blueprint[extent_runs]:
  `!i k a b. i <= k /\ k <= n /\ C i = a /\ C k = b /\
    b.cs_current_bb = a.cs_current_bb /\
    b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
    EVERY (\inst. inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode)
      (emitted_insts a b) ==>
    run_inst_seq (emitted_insts a b) (Obs i) = OK ((Obs k) with vs_inst_idx := (Obs i).vs_inst_idx)`
    suffices_by (disch_then assume_tac >> suspend "extent_apply") >>
  qx_genl_tac [`i`,`k`,`a0`,`b0`] >> strip_tac >>
  map_every (fn idx =>
    qpat_assum `!r. r <= n ==> ~(Obs r).vs_halted /\ _`
      (qspec_then idx mp_tac) >> (impl_tac >- decide_tac) >>
    disch_then (map_every assume_tac o CONJUNCTS)) [`i`,`k`] >>
  qpat_assum `!l r. l <= r /\ r <= n ==> ci_mono (C l) (C r) /\ _`
    (qspecl_then [`i`,`k`] mp_tac) >> (impl_tac >- decide_tac) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `Band = \p q. ?bb x ms. lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME x /\ a0.cs_next_id <= x.inst_id /\
    x.inst_id < b0.cs_next_id /\ gas_origin_edge F (gas_explicit_sites ctx shctx) ctx func p ms (OK q)` >>
  `RTC Band (Obs i) (Obs k)` suffices_by (disch_then assume_tac >> suspend "extent_run_band") >>
  suspend "extent_join_band"
QED
Resume create_size_exit_blueprint[extent_join_band]:
  `i + (k-i) = k` by decide_tac >>
  qspecl_then [`k-i`,`i`,`GENLIST Obs (SUC n)`,`Band`] mp_tac create_indexed_rtc_join >>
  `i < SUC n /\ k < SUC n` by decide_tac >>
  qpat_assum `i + (k-i) = k` (pure_rewrite_tac o single) >>
  qpat_assum `i < SUC n` (fn l => qpat_assum `k < SUC n` (fn r =>
    simp_tac bool_ss [listTheory.EL_GENLIST,l,r])) >>
  impl_tac >- (qx_gen_tac `r` >> strip_tac >>
    `r < n /\ r < SUC n /\ SUC r < SUC n` by decide_tac >>
    qpat_assum `r < SUC n` (fn l => qpat_assum `SUC r < SUC n` (fn h =>
      simp_tac bool_ss [listTheory.EL_GENLIST,l,h])) >>
    qpat_assum `!l. l < n ==> (C l).cs_next_id <= _ /\ _`
      (qspec_then `r` (drule_then (map_every assume_tac o CONJUNCTS))) >>
    map_every (fn (a,b) => qpat_assum `!l h. l <= h /\ h <= n ==> ci_mono (C l) (C h) /\ _`
      (qspecl_then [a,b] mp_tac) >> (impl_tac >- decide_tac) >>
      disch_then (assume_tac o REWRITE_RULE[ci_mono_def] o cj 1))
      [(`i`,`r`),(`SUC r`,`k`)] >>
    simp_tac bool_ss [Abbr `Band`] >> irule create_prefix_band_rtc >>
    goal_assum (drule_at Any) >>
    qpat_assum `C i = a0` (pure_rewrite_tac o single o SYM) >>
    qpat_assum `C k = b0` (pure_rewrite_tac o single o SYM) >>
    fs[ci_mono_def]) >>
  simp_tac bool_ss []
QED
Resume create_size_exit_blueprint[extent_run_band]:
  map_every (fn pat => qpat_assum pat (fn th => rule_assum_tac (REWRITE_RULE[th])))
    [`C i = a0`,`C k = b0`] >>
  irule create_straight_prefix_run >>
  qpat_assum `fn_has_code a0 b0 func`
    (strip_assume_tac o REWRITE_RULE[fn_has_code_def]) >>
  qpat_assum `?x. ctor_segment_fetch func (Obs k) = SOME x /\ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [ctor_segment_fetch_def,AllCaseEqs()]) >>
  rename [`lookup_block b0.cs_current_bb func.fn_blocks = SOME bb_run`] >>
  `((Obs k).vs_current_bb = (Obs i).vs_current_bb) /\
   ((Obs k).vs_inst_idx = (Obs i).vs_inst_idx + LENGTH (emitted_insts a0 b0))` by
    (conj_tac >- asm_rewrite_tac[] >>
     asm_rewrite_tac[listTheory.LENGTH_APPEND]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Band`,`bb_run`,`ctx`,`gas_explicit_sites ctx shctx`,`func`] >>
  conj_tac >- (simp_tac bool_ss [Abbr `Band`,PULL_EXISTS] >> rpt strip_tac >> goal_assum drule) >>
  conj_tac
  >- (rename [`get_instruction bb_end (Obs k).vs_inst_idx = SOME x_end`] >>
      pure_rewrite_tac[markerTheory.Abbrev_def] >>
      qx_genl_tac [`u`,`v`] >> strip_tac >>
      qpat_assum `Abbrev (Band = _)` (PURE_REWRITE_TAC o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
      BETA_TAC >>
      qpat_assum `lookup_block (Obs k).vs_current_bb func.fn_blocks = SOME bb_end` mp_tac >>
      qpat_assum `get_instruction bb_end (Obs k).vs_inst_idx = SOME x_end` mp_tac >>
      qpat_assum `b0.cs_next_id <= x_end.inst_id` mp_tac >>
      qpat_assum `u.vs_current_bb = (Obs k).vs_current_bb` (pure_rewrite_tac o single) >>
      qpat_assum `u.vs_inst_idx = (Obs k).vs_inst_idx` (pure_rewrite_tac o single) >>
      rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >> decide_tac) >>
  conj_tac
  >- (qpat_assum `(Obs i).vs_current_bb = a0.cs_current_bb` (pure_rewrite_tac o single) >>
      qpat_assum `b0.cs_current_bb = a0.cs_current_bb` (pure_rewrite_tac o single o SYM) >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `b0.cs_current_insts ≼ bb_run.bb_instructions`
        (qx_choose_then `extra` assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
      qpat_assum `bb_run.bb_instructions = _` (pure_rewrite_tac o single) >>
      qpat_assum `b0.cs_current_insts = _` (pure_rewrite_tac o single) >>
      qpat_assum `(Obs i).vs_inst_idx = _` (pure_rewrite_tac o single) >>
      pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND,IS_PREFIX_APPEND] >>
      qexists_tac `extra` >> REFL_TAC) >>
  first_assum ACCEPT_TAC
QED
Resume create_size_exit_blueprint[extent_apply]:
  map_every (fn (i,k,a,b) =>
    qpat_assum `!i k a b. _ ==> run_inst_seq (emitted_insts a b) (Obs i) = _`
      (qspecl_then [i,k,a,b] mp_tac) >>
    (impl_tac >- (conj_tac >- decide_tac >> conj_tac >- decide_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac)
    [(`j+3`,`j+4`,`cb`,`cf`),(`j+4`,`j+5`,`cf`,`ca1`),(`j+5`,`n`,`ca1`,`sc`)] >>
  qabbrev_tac `tchk = (Obs (j+4)) with vs_inst_idx := (Obs (j+3)).vs_inst_idx` >>
  qabbrev_tac `pre = (Obs (j+5)) with vs_inst_idx := (Obs (j+4)).vs_inst_idx` >>
  qabbrev_tac `tf = s with vs_inst_idx := (Obs (j+4)).vs_inst_idx` >>
  `run_inst_seq (emitted_insts ca1 sc) pre = OK tf` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts ca1 sc)` by
       (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) (emitted_insts ca1 sc)` mp_tac >>
        simp_tac (srw_ss()) [EVERY_MEM]) >>
     simp_tac bool_ss [Abbr `pre`, Abbr `tf`] >>
     simp[run_inst_seq_inst_idx,instIdxIndepTheory.exec_result_map_def]) >>
  suspend "extent_len"
QED
Resume create_size_exit_blueprint[extent_len]:
  `(Obs (j+3)).vs_labels = (Obs j).vs_labels` by
    (map_every (fn (prefix,live,q) => q by
         (qpat_assum prefix mp_tac >> qpat_assum live mp_tac >>
          rpt (pop_assum kall_tac) >> metis_tac[blueprint_prefix_labels]))
       [(`create_expr_prefix _ _ _ _ _ (Obs j) _ (Obs (SUC j))`, `~(Obs j).vs_halted`,
         `(Obs (SUC j)).vs_labels = (Obs j).vs_labels`),
        (`create_expr_prefix _ _ _ _ _ (Obs (SUC j)) _ (Obs (j+2))`, `~(Obs (SUC j)).vs_halted`,
         `(Obs (j+2)).vs_labels = (Obs (SUC j)).vs_labels`),
        (`create_expr_prefix _ _ _ _ _ (Obs (j+2)) _ (Obs (j+3))`, `~(Obs (j+2)).vs_halted`,
         `(Obs (j+3)).vs_labels = (Obs (j+2)).vs_labels`)] >>
     asm_rewrite_tac[]) >>
  `eval_operand len (Obs (j+3)) = SOME (n2w (LENGTH payload))` by
    (irule blueprint_eval_operand_frame >> qexistsl_tac [`cprep`,`Obs j`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. len = Var x ==> not_fresh_at cb x` by
    (qpat_assum `!l r. l <= r /\ r <= n ==> ci_mono (C l) (C r) /\ _`
       (qspecl_then [`j`,`j+3`] mp_tac) >> (impl_tac >- decide_tac) >>
     map_every (fn q => qpat_assum q (pure_rewrite_tac o single)) [`C j = cprep`,`C (j+3) = cb`] >>
     rewrite_tac[ci_mono_def] >> strip_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `cprep` >>
     simp[]) >>
  `eval_operand len (Obs (j+4)) = SOME (n2w (LENGTH payload))` suffices_by
    (disch_then assume_tac >> suspend "extent_reject") >>
  `(eval_operand len tchk = eval_operand len (Obs (j+4)))` by
    simp[Abbr `tchk`,ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  qpat_assum `eval_operand len tchk = _` (pure_rewrite_tac o single o SYM) >>
  map_every (fn q => qpat_assum q mp_tac)
    [`eval_operand len (Obs (j+3)) = _`, `!x. len = Var x ==> not_fresh_at cb x`,
     `run_inst_seq (emitted_insts cb cf) (Obs (j+3)) = OK tchk`,
     `compile_create_blueprint_check _ _ _ _ = _`] >>
  rpt (pop_assum kall_tac) >>
  suspend "extent_len_check"
QED
Resume create_size_exit_blueprint[extent_len_check]:
  Cases_on `is_int_literal (origin_fold_value off_e)` >>
  simp[compile_create_blueprint_check_def,emitHelperTheory.emit_op_def,emitHelperTheory.emit_void_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def,fresh_id_def,fresh_var_def,emit_def] >>
  strip_tac >> gvs[] >> fs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >>
  Cases_on `len` >>
  simp[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
       exec_read1_def,exec_pure2_def,bind_outputs_def,eval_operand_def,
       lookup_var_update_var,update_var_def,lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE,fresh_var_distinct,not_fresh_at_def,AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  metis_tac[arithmeticTheory.LESS_EQ_ADD,arithmeticTheory.LESS_EQ_REFL]
QED
Resume create_size_exit_blueprint[extent_reject]:
  `blueprint_literal_offset cx hs args = is_int_literal (origin_fold_value off_e)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`args = target::amount::_`, `expr_body_pre ce cx env _ es`, `body_inv tops ctx ce cx`] >>
     rpt (pop_assum kall_tac) >> metis_tac[create_blueprint_offset_bridge]) >>
  qabbrev_tac `xs = create_operand_layout (CreateFromBlueprint raw) hs (av::(cvs ++ kvs))` >>
  `dest_create_args (CreateFromBlueprint F) hs xs = SOME ops` by
    (qpat_assum `dest_create_args (CreateFromBlueprint raw) hs xs = SOME ops` mp_tac >>
     simp_tac (srw_ss()) [dest_create_args_def]) >>
  `eval_operand code (Obs (j+4)) = eval_operand code tchk` by
    simp[Abbr `tchk`,ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  `?code_n w'.
     blueprint_prefix_size hs (is_int_literal (origin_fold_value off_e)) xs (Obs (j+3)).vs_accounts = SOME code_n /\
     eval_operand sz tf = SOME w' /\ w2n w' <= code_n + LENGTH payload` suffices_by
    (disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >> suspend "source_reject") >>
  irule create_blueprint_pre_dispatch_extent >>
  qexistsl_tac [`aw`,`offop`,`len`,`data`,`cb`,`cf`,`code`,`offset_op`,`ops`,`ow`,
    `pre`,`Obs (j+3)`,`cf`,`sc`,`ca3`,`ca1`,`ca2`,`tchk`,`target_op`,`Obs (j+4)`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC)
QED
Resume create_size_exit_blueprint[source_reject]:
  rename [`blueprint_prefix_size hs _ xs (Obs (j+3)).vs_accounts = SOME code_n`,
    `eval_operand sz tf = SOME w'`] >>
  `w' = w` by
    (qpat_assum `eval_operand sz tf = SOME w'` mp_tac >>
     simp_tac (srw_ss()) [Abbr `tf`,ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
     qpat_assum `eval_operand sz s = SOME w` (fn th => simp_tac (srw_ss()) [th])) >>
  `2 * max_code_size < code_n + LENGTH payload` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`w' = w`, `w2n w' <= code_n + LENGTH payload`,`2 * max_code_size < w2n w`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >> decide_tac) >>
  `blueprint_prefix_size hs (blueprint_literal_offset cx hs args) xs qs.accounts = SOME code_n` by
    (qpat_assum `blueprint_prefix_size hs _ xs (Obs (j+3)).vs_accounts = SOME code_n` mp_tac >>
     map_every (fn q => qpat_assum q (fn th => simp_tac bool_ss [th]))
       [`blueprint_literal_offset cx hs args = _`] >>
     pure_rewrite_tac[blueprint_prefix_size_def] >>
     map_every (fn q => qpat_assum q (fn th => simp_tac (srw_ss()) [th]))
       [`dest_create_args (CreateFromBlueprint F) hs xs = SOME ops`,
        `ops.co_code_src = _`,`ops.co_code_offset = _`,
        `(lookup_account (w2w aw) qs.accounts).code = _`]) >>
  `create_arg_ctor_types (CreateFromBlueprint raw) hs (MAP expr_type args) = SOME (MAP expr_type ctors)` by
    (qpat_assum `args = target::amount::_` (pure_rewrite_tac o single) >>
     Cases_on `hs` >> simp_tac (srw_ss()) [create_arg_ctor_types_def]) >>
  `eval_create_operands cx (CreateFromBlueprint raw) hs rof (MAP expr_type args)
      (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs)) qs =
      (INR (Error (RuntimeError "create initcode too large")),qs)` by
    (irule blueprint_operands_size_reject >>
     qexistsl_tac [`MAP expr_type ctors`,`code_n`,`ops`,`payload`,`xs`] >>
     rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE simp[Abbr `xs`])) >>
     qpat_assum `ops.co_ctor_args = cvs` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  disj1_tac >>
  qpat_assum `eval_create_operands _ _ _ _ _ _ _ qs = (res,srcout)` mp_tac >>
  qpat_assum `eval_create_operands _ _ _ _ _ _ _ qs = (INR _,qs)`
    (fn th => simp_tac (srw_ss()) [th])
QED
Resume create_size_exit_blueprint[raw_payload]:
  qpat_x_assum `if T then _ else _`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o REWRITE_RULE[COND_CLAUSES]) >>
  rename [`ctors = [raw_e]`, `C 2 = c0`, `C 3 = c1`, `C 4 = c2`, `C 5 = c3`] >>
  map_every (fn (i,bound) =>
    bound by decide_tac >>
    qpat_assum `!i. i <= n ==> ~(Obs i).vs_halted /\ _`
      (qspec_then i (drule_then (map_every assume_tac o CONJUNCTS))))
    [(`2`,`2 <= n`),(`3`,`3 <= n`),(`4`,`4 <= n`),(`5`,`5 <= n`)] >>
  map_every (fn (i,bound) =>
    bound by decide_tac >>
    qpat_assum `!i. i < n ==> (C i).cs_next_id <= _ /\ _`
      (qspec_then i (drule_then (map_every assume_tac o CONJUNCTS) o SIMP_RULE (srw_ss()) [])))
    [(`1`,`1 < n`),(`2`,`2 < n`),(`3`,`3 < n`),(`4`,`4 < n`),(`5`,`5 < n`)] >>
  `raw_e = HD ctors` by simp[] >>
  `p.gas_obs = gas_explicit (M 1 ++ (M 2 ++ (M 3 ++ (M 4 ++ M 5 ++ R j))))
    (Obs 1).vs_gas_readings ++ tail` by
    (qpat_assum `p.gas_obs = _` (pure_rewrite_tac o single) >>
     qpat_assum `R 1 = M 1 ++ (M 2 ++ _)` (pure_once_rewrite_tac o single) >> REFL_TAC) >>
  `C 6 = cprep /\ Obs 6 = Obs j` by
    (qpat_assum `j = 6` (pure_rewrite_tac o single o SYM) >> simp[]) >>
  map_every (fn q => qpat_assum q (fn th =>
      rule_assum_tac (REWRITE_RULE[th])))
    [`C 1 = ca`,`C 2 = c0`,`C 3 = c1`,`C 4 = c2`,`C 5 = c3`,`C 6 = cprep`,`C j = cprep`,`Obs 6 = Obs j`] >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?bs qp Gp tnp. ctors = [raw_e] /\
     bind (eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])))
       (\kvs. eval_create_operands cx (CreateFromBlueprint T) hs rof
         (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::BytesV bs::kvs)) qp = (res,srcout) /\
     valid_horizon cx st0 H qp.storage_trace /\
     eval_operand len (Obs j) = SOME (n2w (LENGTH bs)) /\
     (!x. len = Var x ==> not_fresh_at cprep x) /\
     eval_operand target_op (Obs j) = SOME aw /\
     (!x. target_op = Var x ==> not_fresh_at cprep x) /\
     expr_sim_inv ce cx env qp /\ local_ptrs_reserved ce cprep /\
     (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
     (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
     return_buf_frame depr ce cprep (Obs j) /\ alloca_history func (Obs j) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs j)) /\
     (!f i z. frag_reachable ctx func (Obs j) f i z ==> dalloca_no_wrap i z) /\
     (!h. valid_horizon cx st0 h qp.storage_trace ==>
       stmt_state_rel h ctx func ce cx qp (Obs j) /\ storage_well_formed_on cx qp (FST h) /\
       ghost_inv_at (DF h) lo depr ce cx qp Gp tnp (Obs j)) /\
     ~(Obs j).vs_halted /\ (Obs j).vs_current_bb = cprep.cs_current_bb /\
     (Obs j).vs_inst_idx = LENGTH cprep.cs_current_insts /\
     qp.gas_obs = gas_explicit (R j) (Obs j).vs_gas_readings ++ tail`
    suffices_by (suspend "raw_result") >>
  irule create_blueprint_raw_keyword_entry >> suspend "raw_premises"
QED
Resume create_size_exit_blueprint[raw_premises]:
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
    (goal_assum (drule_at Any) >> simp[]))) >>
  qexistsl_tac [`G`,`Obs 5`,`ca`,`c3`,`c0`,`c1`,`c2`,`data`,`later`,
    `Obs 2`,`M 5`,`M 1`,`M 4`,`M 2`,`M 3`,`p`,`Obs 3`,`raw_op`,`Obs 1`,
    `saved`,`sca`,`h0`,`h1`,`h2`,`shctx`,`shadow_func`,`ssaved`,`tn`,`Obs 4`,`v`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume create_size_exit_blueprint[raw_result]:
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choosel_then [`bytes`,`paystate`,`payG`,`paytn`] (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl_tac [`[BytesV bytes]`,`bytes`,`paystate`,`payG`,`paytn`] >>
  simp_tac (srw_ss()) [COND_CLAUSES, APPEND, LENGTH] >>
  conj_tac >- (qpat_assum `ctors = [raw_e]` (simp_tac (srw_ss()) o single)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume create_size_exit_blueprint[abi_payload]:
  qpat_x_assum `if F then _ else _` (assume_tac o REWRITE_RULE[COND_CLAUSES]) >>
  Cases_on `ctors = []` >- suspend "abi_empty" >>
  `abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) ctors)) < dimword (:256)` by
    (`EVERY (\e. expr_body_pre ce cx env e es) ctors` by
       (simp[EVERY_MEM] >> rpt strip_tac >>
        `MEM e args` by
          (qpat_assum `args = target::amount::_` (pure_rewrite_tac o single) >>
           simp[MEM_APPEND]) >>
        irule blueprint_keyword_body_pre >> conj_tac
        >- (drule expr_body_pre_static_facts >> simp[]) >>
        qexistsl_tac [`ty`,`args`,`es`,`d`,`hs`,`ks`,`F`,`rof`] >> simp[]) >>
     drule dallocaBlueprintArgsTheory.create_ctor_args_abi_bound >> disch_tac >>
     `abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type ctors)) < 2 ** 64` by
       (drule expr_body_pre_static_facts >> disch_then (mp_tac o cj 3) >>
        qpat_assum `args = target::amount::_` (pure_rewrite_tac o single) >>
        Cases_on `hs` >> simp[alloc_limits_expr_def,ext_call_alloc_ok_def]) >>
     qpat_x_assum `_ < 2 ** 64` mp_tac >>
     qpat_x_assum `abi_size_bound _ _ <= abi_size_bound _ _` mp_tac >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  qpat_assum `ctors <> []` (fn ne =>
    qpat_x_assum `if ctors = [] then _ else _`
      (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS) o
       REWRITE_RULE[ne,COND_CLAUSES])) >>
  suspend "abi_apply"
QED
Resume create_size_exit_blueprint[abi_empty]:
  qpat_assum `ctors = []` (fn empty =>
    qpat_x_assum `if ctors = [] then _ else _`
      (map_every assume_tac o CONJUNCTS o REWRITE_RULE[empty,COND_CLAUSES])) >>
  disj2_tac >> qexistsl_tac [`[]`,`[]`,`p`,`G`,`tn`] >>
  qpat_assum `j = 1` (pure_rewrite_tac o single) >>
  qpat_assum `cprep = ca` (pure_rewrite_tac o single) >>
  qpat_assum `len = Lit 0w` (pure_rewrite_tac o single) >>
  qpat_assum `ctors = []` (pure_rewrite_tac o single) >>
  simp_tac (srw_ss()) [encode_create_ctor_args_def,eval_operand_def,LET_THM,listTheory.REV_DEF] >>
  conj_tac
  >- (qpat_assum `ctors = []` (fn empty =>
       qpat_assum `later = _` (fn lat =>
         qpat_assum `bind (eval_exprs cx (ctors ++ later)) _ p = _`
           (ACCEPT_TAC o SIMP_RULE (srw_ss()) [empty,lat]))) ) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume create_size_exit_blueprint[abi_apply]:
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?cvs ps g tn1.
     LENGTH cvs = LENGTH ctors /\ eval_exprs cx ctors p = (INL cvs,ps) /\
     bind (eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])))
       (\kvs. eval_create_operands cx (CreateFromBlueprint F) hs rof
         (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) ps = (res,srcout) /\
     valid_horizon cx st0 H ps.storage_trace /\
     (?bs. encode_create_ctor_args (get_tenv cx) (MAP expr_type ctors) cvs = SOME bs /\
       eval_operand len (Obs j) = SOME (n2w (LENGTH bs))) /\
     (!x. len = Var x ==> not_fresh_at cprep x) /\
     eval_operand target_op (Obs j) = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at cprep x) /\
     expr_sim_inv ce cx env ps /\ local_ptrs_reserved ce cprep /\
     (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
     (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
     return_buf_frame depr ce cprep (Obs j) /\ alloca_history func (Obs j) /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs j)) /\
     (!f i z. frag_reachable ctx func (Obs j) f i z ==> dalloca_no_wrap i z) /\
     (!h. valid_horizon cx st0 h ps.storage_trace ==>
       stmt_state_rel h ctx func ce cx ps (Obs j) /\ storage_well_formed_on cx ps (FST h) /\
       ghost_inv_at (DF h) lo depr ce cx ps g tn1 (Obs j)) /\
     ~(Obs j).vs_halted /\ (Obs j).vs_current_bb = cprep.cs_current_bb /\
     (Obs j).vs_inst_idx = LENGTH cprep.cs_current_insts /\
     ps.gas_obs = gas_explicit (R j) (Obs j).vs_gas_readings ++ tail`
    suffices_by
      (disch_then (DISJ_CASES_THEN2 assume_tac
        (qx_choosel_then [`cvs`,`ps`,`g`,`tn1`] (map_every assume_tac o CONJUNCTS)))
       >- (disj1_tac >> first_assum ACCEPT_TAC) >>
       qpat_x_assum `?bs. encode_create_ctor_args _ _ cvs = SOME bs /\ _`
         (qx_choose_then `bytes` (map_every assume_tac o CONJUNCTS)) >>
       disj2_tac >> qexistsl_tac [`cvs`,`bytes`,`ps`,`g`,`tn1`] >>
       simp_tac bool_ss [COND_CLAUSES] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule create_blueprint_abi_keyword_entry >> suspend "abi_premises"
QED
Resume create_size_exit_blueprint[abi_premises]:
  `fn_inst_ids_distinct func /\ MEM func ctx.ctx_functions` by
    fs[expr_vv_sim_full_pre_def] >>
  `LENGTH vals = LENGTH ctors` by fs[create_itinerary_ctor_rows_def] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
    (qexists_tac `target` >> first_assum ACCEPT_TAC))) >>
  conj_tac
  >- (qexistsl_tac [
       `\i. C (1 + 2*i)`, `\i. M (1 + 2*i)`, `G`,
       `\i. C (SUC (1 + 2*i))`, `\i. Obs (SUC (1 + 2*i))`,
       `\i. R (1 + 2*i)`, `\i. EL i hmid`, `\i. EL i hcs`,
       `\i. M (SUC (1 + 2*i))`, `\i. Obs (1 + 2*i)`, `\i. EL i vvs`,
       `a`, `M q`, `s`, `bb`, `buf`, `\i. C (j+i)`,
       `abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) ctors))`,
       `\i. M (j+i)`, `data`, `inst`, `M (SUC q)`, `later`, `n-j`, `offop`,
       `\i. Obs (j+i)`, `Obs q`, `salt`, `k`, `shctx`, `shadow_func`,
       `Obs (SUC q)`, `vals`, `sz`, `tn`, `value`, `w`] >>
     BETA_TAC >> simp_tac (srw_ss()) [arithmeticTheory.MULT_CLAUSES] >>
     qpat_assum `C 1 = ca` (pure_rewrite_tac o single) >>
     qpat_assum `q = 1 + 2 * LENGTH ctors` (pure_rewrite_tac o single o SYM) >>
     qpat_assum `C q = k` (pure_rewrite_tac o single) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     suspend "abi_rows_and_tail") >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`ty`,`d`,`es`,`ks`] >> first_assum ACCEPT_TAC
QED
Resume create_size_exit_blueprint[abi_rows_and_tail]:
  conj_tac
  >- (qx_gen_tac `i` >> strip_tac >>
      `1 + (2 + 2*i) = 1 + 2*SUC i /\
       SUC (SUC (1 + 2*i)) = 1 + 2*SUC i /\ SUC (1 + 2*i) < n` by decide_tac >>
      map_every (fn idx =>
        qpat_assum `!k. k <= n ==> ~(Obs k).vs_halted /\ _`
          (qspec_then idx mp_tac) >> (impl_tac >- decide_tac) >>
        disch_then (map_every assume_tac o CONJUNCTS))
        [`SUC (1 + 2*i)`,`1 + 2*SUC i`] >>
      map_every (fn idx =>
        qpat_assum `!k. k < n ==> (C k).cs_next_id <= _ /\ _`
          (qspec_then idx mp_tac) >> (impl_tac >- decide_tac) >>
        disch_then (map_every assume_tac o CONJUNCTS))
        [`1 + 2*i`,`SUC (1 + 2*i)`] >>
      map_every (fn (l,r) =>
        qpat_assum `!a b. a <= b /\ b <= n ==> ci_mono (C a) (C b) /\ _`
          (qspecl_then [l,r] mp_tac) >> (impl_tac >- decide_tac) >>
        disch_then (map_every assume_tac o CONJUNCTS))
        [(`1`,`1 + 2*i`),(`SUC (1 + 2*i)`,`1 + 2*SUC i`)] >>
      qpat_assum `create_itinerary_ctor_rows ce ctors vals ca k cs mid vvs`
        (strip_assume_tac o REWRITE_RULE[create_itinerary_ctor_rows_def]) >>
      qpat_assum `!k. k < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
        (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
      qpat_assum `!k. k < LENGTH ctors ==> C (SUC _) = EL k mid /\ _`
        (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
      map_every (fn idx => qpat_assum `!k. k <= LENGTH ctors ==> C (1+2*k) = EL k cs`
        (qspec_then idx mp_tac) >> (impl_tac >- decide_tac) >> disch_tac)
        [`i`,`SUC i`] >>
      map_every (fn pat => qpat_assum pat (fn th =>
        rule_assum_tac (REWRITE_RULE[th]) >> pure_rewrite_tac[th]))
        [`1 + (2 + 2*i) = 1 + 2*SUC i`,`SUC (SUC (1+2*i)) = 1+2*SUC i`,
         `C 1 = ca`, `C (1+2*i) = EL i cs`, `C (1+2*SUC i) = EL (SUC i) cs`,
         `C (SUC (1+2*i)) = EL i mid`] >>
      rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (disch_tac >> rpt conj_tac >> first_assum ACCEPT_TAC))) >>
  qpat_assum `C 1 = ca` (fn th => rule_assum_tac (REWRITE_RULE[th])) >>
  simp_tac (srw_ss()) [] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "abi_suffix"
QED
Resume create_size_exit_blueprint[abi_suffix]:
  conj_tac
  >- (strip_tac >>
      map_every (fn (l,r) =>
        qpat_assum `!a b. a <= b /\ b <= n ==> ci_mono (C a) (C b) /\ _`
          (qspecl_then [l,r] mp_tac) >> (impl_tac >- decide_tac) >>
        disch_then (map_every assume_tac o CONJUNCTS))
        [(`q`,`SUC q`),(`SUC q`,`j`)] >>
      qpat_assum `!k. k <= n ==> ~(Obs k).vs_halted /\ _`
        (qspec_then `SUC q` mp_tac) >> (impl_tac >- decide_tac) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      map_every (fn idx => qpat_assum `!k. k < n ==> (C k).cs_next_id <= _ /\ _`
        (qspec_then idx mp_tac) >> (impl_tac >- decide_tac) >>
        disch_then (map_every assume_tac o CONJUNCTS)) [`q`,`SUC q`] >>
      `SUC (SUC q) = j /\ j + (n-j) = n` by decide_tac >>
      qpat_assum `abi_size_bound _ _ < dimword (:256)`
        (assume_tac o SIMP_RULE (srw_ss()) [wordsTheory.dimword_def]) >>
      map_every (fn pat => qpat_assum pat (fn th =>
        rule_assum_tac (REWRITE_RULE[th]) >> pure_rewrite_tac[th]))
        [`SUC (SUC q) = j`,`C q = k`,`C (SUC q) = a`,`C j = cprep`] >>
      qpat_assum `j + (n-j) = n` (pure_rewrite_tac o single) >>
      simp_tac bool_ss [] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac
      >- (qx_gen_tac `i` >> strip_tac >>
          qpat_assum `!k. k < n ==> (C k).cs_next_id <= _ /\ _`
            (qspec_then `j+i` mp_tac) >> (impl_tac >- decide_tac) >>
          `SUC (j+i) = j+SUC i` by decide_tac >>
          qpat_assum `SUC (j+i) = j+SUC i` (pure_rewrite_tac o single) >> simp_tac bool_ss []) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise create_size_exit_blueprint

Theorem create_expr_size_exit:
  !cx ty kind has_salt rof ks args d.
    EVERY (create_operand_completed_ok cx) (create_operand_order kind has_salt args) ==>
    create_expr_size_exit cx (Call ty (CreateTarget kind has_salt rof ks) args d)
Proof
  rpt gen_tac >> Cases_on `kind` >>
  simp[create_size_exit_proxy, create_size_exit_copy,
       create_size_exit_raw, create_size_exit_blueprint]
QED
