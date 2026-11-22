(* The raw FMP stays fixed on paths that never reach its operations. *)
Theory callRejectMemory
Ancestors
  contextRawReachable contextCodegenRel contextCodegenRelProps venomState venomInst venomExecSemantics venomInstProps
  venomExecProofs venomFnInstsProofs venomInstProofs1 ctxLookupAgreeHelpers frameAllocationEffects
  ctxLookupAgree unitTransformDefs o1PassContract vyperCalldata callRawVariant
  runtimePeakMemoryCode runtimePeakMemoryModule runtimePeakMemoryAbi loweringRuntimeOpcodes
  exprSimAbiDecodeFramed exprSimAbiDecodeResource exprSimAbiDecodeResourceMutual
  exprSimAbiDecodeTraceSafe exprSimAbiDecodeShape abiEncoder sorting pred_set
  exprSimAbiDecodeCertificate exprSimAbiDecodePrims exprSimAbiDecodeTrace
  exprSimAbiDecodeResourcePrims fragFuel fragFuelConfinement
  fragFuelExpr fragFuelRuntimeBody fragFuelLoopAbiDecDyn fragObserverCodeProps calldataNoneFallbackJoint
  registrationRejectMetadata calldataSourceSize groupedDefaultArguments vyperABIEntries
  calldataNoneDecoder fragGasOriginPtrExec abiDecoderCoherence abiDecoderReentry finite_map
  calldataNoneRegisterFold calldataNoneRegisterOne
  exprSimAbiDecodeObservedEndpoint exprSimAbiDecodeObserverReject exprSimAbiGasBridge abiEncoderObserver fragExec
  entryChecksProps entryLinearAppend entryCompileIntervals entryRejectCode entryCodeOwnership
  entrySourcePackages entryValueRevertPtr defaultDispatchRouting acceptedContextPhi
  compileVyper entryDispatchProps entryDispatchCounters
  externalEntryShape externalEntryChecks calldataNoneMetadata checkedSelectorTableProps
  calldataSelectorProps selectorCompilerProps
  venomMemDefs venomMemProps vyperTypeABI groupedInternalLabels
  ctorCallFreeRules supportedExprTraverse vyperTypeContract vyperTypeContractContext
  vyperTypeContractGetter loweringShapeSource constSubst constSubstCorrect
  whitelistCheckerConsts
  moduleLoweringProps exprLoweringProps emitHelper emitHelperProps rich_list
  loweringStateRelDefs
  allocationLookup allocaBudgetProps allocaFrontierBound vyperCompiler fcgDefs unitShapeDefs venomInstIdsProps
  loweringShapeDefs compileEnv moduleLowering context pair
  groupedEntryCounters groupedKeywordAllocas fmpStageBlockSimCode
  entryRejectAllocationIds groupedEntryPackage rejectPrefixSourceShape
  entryStateRel dispatchedValueSelection venomWf loweringShapeProps loweringShapeRules
  calldataRegistrationExec fragGasOriginPtr fragGasOrigin fragGasPathPtr
  gasEvents gasCount memSafeRun codegenRel ptrSafeRun
  groupedDispatchPath groupedEntryResources groupedKeywordReject selectedAcceptedFold
  vyperLoweringCorrect supportedProgram e2eDefs ptrDiscipline words arithmetic list relation

val _ = Parse.hide "tops";
val _ = Parse.hide "body";

Theorem no_raw_fmp_step[local]:
  ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst s = OK t ==>
  t.vs_fmp = s.vs_fmp
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
      gvs[step_inst_base_opcode_eqs, AllCaseEqs(), jump_to_def] >>
      pairarg_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      metis_tac[exec_alloca_preserves_fmp]) >>
  `~is_alloca_op inst.inst_opcode /\ inst.inst_opcode <> SETFMP /\
   inst.inst_opcode <> DALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def, is_raw_fmp_opcode_def]) >>
  drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem enters_block_fmp[local]:
  enters_block fn s t ==> t.vs_fmp = s.vs_fmp
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (mp_tac o AP_TERM (Term `\u:venom_state. u.vs_fmp`)) >>
  simp[]
QED

Theorem raw_reachable_fmp_unchanged[local]:
  !vs0 ctx fn inst s. raw_reachable vs0 ctx fn inst s ==>
    (!f i u. raw_reachable vs0 ctx f i u ==>
      ~is_raw_fmp_opcode i.inst_opcode /\ i.inst_opcode <> INVOKE) ==>
    s.vs_fmp = vs0.vs_fmp
Proof
  ho_match_mp_tac raw_reachable_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> strip_tac
  >- (drule enters_block_fmp >> simp[])
  >- (simp[] >> imp_res_tac no_raw_fmp_step >> metis_tac[])
  >- (imp_res_tac enters_block_fmp >> imp_res_tac no_raw_fmp_step >> metis_tac[])
  >> metis_tac[]
QED

Theorem runtime_reachable_raw_fmp_opcode[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  raw_reachable vs unit.cu_context fn inst s ==>
  (is_raw_fmp_opcode inst.inst_opcode <=> inst.inst_opcode = DALLOCA)
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_fn_ptr_ok >> strip_tac >>
  `!s0 ctx fn inst s. raw_reachable s0 ctx fn inst s ==>
    MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn)` by
    (ho_match_mp_tac raw_reachable_ind >>
     simp[active_inst_def, fn_labels_def] >> rpt strip_tac >>
     metis_tac[lookup_function_MEM, MEM_fn_insts, EL_MEM]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  `fn_ptr_ok P fn` by
    (qpat_assum `EVERY (fn_ptr_ok P) _`
       (qspec_then `fn` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     asm_rewrite_tac[]) >>
  qpat_assum `fn_ptr_ok _ fn` (strip_assume_tac o REWRITE_RULE [fn_ptr_ok_def]) >>
  qpat_assum `!i. MEM i (fn_insts fn) ==> _` (drule_then strip_assume_tac) >>
  `!opc. opc <> DRET /\ opc <> GETFMP /\ opc <> SETFMP /\ opc <> RETFMP ==>
     (is_raw_fmp_opcode opc <=> opc = DALLOCA)` by
    (Cases >> simp[is_raw_fmp_opcode_def]) >>
  first_x_assum irule >> simp[]
QED

Definition reject_prefix_opcode_def[local]:
  reject_prefix_opcode inst <=>
    inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> INVOKE
End

Definition reject_prefix_step_def[local]:
  reject_prefix_step ctx fn s u <=>
    ?inst t. active_inst fn inst s /\ reject_prefix_opcode inst /\
      step_inst 0 ctx inst s = OK t /\
      ((~is_terminator inst.inst_opcode /\
        u = t with vs_inst_idx := SUC s.vs_inst_idx) \/
       (is_terminator inst.inst_opcode /\ ~t.vs_halted /\ enters_block fn t u))
End

Definition reject_prefix_terminal_def[local]:
  reject_prefix_terminal ctx fn s <=>
    ?inst. active_inst fn inst s /\ reject_prefix_opcode inst /\
      !t. step_inst 0 ctx inst s <> OK t
End

Theorem reject_prefix_active[local]:
  ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s /\
  RTC (reject_prefix_step ctx fn) s z /\ reject_prefix_terminal ctx fn z ==>
  reject_prefix_opcode inst
Proof
  strip_tac >>
  qpat_x_assum `RTC _ _ _` (mp_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >>
  fs[reject_prefix_step_def, reject_prefix_terminal_def] >>
  metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique]
QED

Theorem reject_prefix_next[local]:
  ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s /\
  RTC (reject_prefix_step ctx fn) s z /\ reject_prefix_terminal ctx fn z /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK t ==>
  RTC (reject_prefix_step ctx fn) (t with vs_inst_idx := SUC s.vs_inst_idx) z
Proof
  strip_tac >>
  `reject_prefix_opcode inst` by metis_tac[reject_prefix_active] >>
  `step_inst 0 ctx inst s = OK t` by fs[reject_prefix_opcode_def,step_inst_non_invoke] >>
  qpat_x_assum `RTC _ _ _` (mp_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >>
  fs[reject_prefix_step_def, reject_prefix_terminal_def] >>
  disch_then (DISJ_CASES_THEN2 SUBST_ALL_TAC strip_assume_tac)
  >- (`inst' = inst` by metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique] >>
      pop_assum SUBST_ALL_TAC >>
      qpat_x_assum `!t. step_inst _ _ _ _ <> OK t` (qspec_then `t` mp_tac) >>
      asm_rewrite_tac[]) >>
  `inst'' = inst` by metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique] >>
  pop_assum SUBST_ALL_TAC >> fs[] >> metis_tac[]
QED

Theorem reject_jump_enters_block[local]:
  no_phi_fn fn /\ enters_block fn (jump_to l s) t ==> t = jump_to l s
Proof
  strip_tac >> fs[enters_block_def, no_phi_fn_def, EVERY_MEM] >>
  drule lookup_block_MEM >> strip_tac >> res_tac >>
  Cases_on `bb.bb_instructions` >>
  gvs[eval_phis_def, phi_prefix_length_def, jump_to_def, AllCaseEqs()]
QED

Theorem reject_prefix_replay_step[local]:
  reject_prefix_step ctx fn s t /\ ALL_DISTINCT (fn_labels fn) /\
  no_phi_fn fn /\ no_phi_fn host /\ active_inst fn i s /\
  lookup_block s.vs_current_bb host.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i ==>
  ?n. !f other. run_from (f+n) other host s = run_from f other host t
Proof
  strip_tac >> gvs[reject_prefix_step_def, reject_prefix_opcode_def] >>
  `inst = i` by metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique] >> gvs[step_inst_non_invoke] >-
    (qexists_tac `0` >> rpt gen_tac >> simp[] >>
     mp_tac (Q.SPECL [`f`,`other`,`host`,`s`,`bb`,`i`] run_from_nonterm) >>
     simp[step_inst_non_invoke]) >>
  `?l. step_inst_base i s = OK (jump_to l s)` by
    (drule_all step_inst_base_ok_terminator_jump >>
     disch_then (DISJ_CASES_THEN strip_assume_tac) >>
     gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[]) >>
  `t' = jump_to l s` by metis_tac[exec_result_11] >> gvs[] >>
  `t = jump_to l s` by metis_tac[reject_jump_enters_block] >>
  `~s.vs_halted` by fs[jump_to_def] >>
  qexists_tac `1` >> rpt gen_tac >> simp[GSYM ADD1] >>
  irule run_from_jump_exact >> simp[] >>
  qexistsl_tac [`bb`,`i`] >> simp[]
QED

Theorem reject_prefix_replay_path[local]:
  !s t. RTC (\v w. reject_prefix_step ctx fn v w /\
    ?i bb. active_inst fn i v /\ lookup_block v.vs_current_bb observer.fn_blocks = SOME bb /\
      get_instruction bb v.vs_inst_idx = SOME i) s t ==>
  ALL_DISTINCT (fn_labels fn) /\ no_phi_fn fn /\ no_phi_fn host /\
  (!l bb. lookup_block l observer.fn_blocks = SOME bb ==> lookup_block l host.fn_blocks = SOME bb) ==>
  ?n. !f other. run_from (f+n) other host s = run_from f other host t
Proof
  ho_match_mp_tac RTC_INDUCT >> conj_tac
  >- (rpt strip_tac >> qexists_tac `0` >> simp[]) >>
  map_every qx_gen_tac [`start`,`middle`,`end_state`] >> simp[] >> rpt strip_tac >>
  `lookup_block start.vs_current_bb host.fn_blocks = SOME bb` by metis_tac[] >>
  drule_all reject_prefix_replay_step >> disch_then (qx_choose_then `n` assume_tac) >>
  `?k. !f other. run_from (f+k) other host middle = run_from f other host end_state` by metis_tac[] >>
  qexists_tac `k+n` >> rpt gen_tac >> PURE_REWRITE_TAC [ADD_ASSOC] >>
  qpat_assum `!f other. run_from _ _ _ start = _`
    (qspecl_then [`f+k`,`other`] SUBST1_TAC) >>
  qpat_assum `!f other. run_from _ _ _ middle = _`
    (qspecl_then [`f`,`other`] ACCEPT_TAC)
QED

Theorem reject_prefix_block[local]:
  ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s /\
  RTC (reject_prefix_step ctx fn) s z /\ reject_prefix_terminal ctx fn z /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK t /\
  ~t.vs_halted /\ enters_block fn t u ==>
  RTC (reject_prefix_step ctx fn) u z
Proof
  strip_tac >>
  `reject_prefix_opcode inst` by metis_tac[reject_prefix_active] >>
  `step_inst 0 ctx inst s = OK t` by fs[reject_prefix_opcode_def,step_inst_non_invoke] >>
  `!v. enters_block fn t v ==> v = u` by
    (rpt strip_tac >> gvs[enters_block_def]) >>
  qpat_x_assum `RTC _ _ _` (mp_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >>
  fs[reject_prefix_step_def, reject_prefix_terminal_def] >>
  disch_then (DISJ_CASES_THEN2 SUBST_ALL_TAC strip_assume_tac)
  >- (`inst' = inst` by metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique] >>
      pop_assum SUBST_ALL_TAC >>
      qpat_x_assum `!t. step_inst _ _ _ _ <> OK t` (qspec_then `t` mp_tac) >>
      asm_rewrite_tac[]) >>
  `inst'' = inst` by metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique] >>
  pop_assum SUBST_ALL_TAC >> fs[] >> metis_tac[]
QED

Theorem reject_prefix_covers_reachable[local]:
  !vs0 ctx fn inst s. raw_reachable vs0 ctx fn inst s ==>
    !name entry lbl start z.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME entry /\
      fn_entry_label entry = SOME lbl /\
      enters_block entry
        (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                     vs_inst_idx := 0|>) start /\
      ALL_DISTINCT (fn_labels entry) /\
      RTC (reject_prefix_step ctx entry) start z /\
      reject_prefix_terminal ctx entry z ==>
      fn = entry /\ RTC (reject_prefix_step ctx fn) s z /\ reject_prefix_opcode inst
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >> strip_tac
  >- (gvs[] >>
      `s = start` by gvs[enters_block_def] >> gvs[] >>
      metis_tac[reject_prefix_active])
  >- (`fn = entry /\ RTC (reject_prefix_step ctx fn) s z` by metis_tac[] >>
      gvs[] >> drule_all reject_prefix_next >> metis_tac[reject_prefix_active])
  >- (`fn = entry /\ RTC (reject_prefix_step ctx fn) s z` by metis_tac[] >>
      gvs[] >> drule_all reject_prefix_block >> metis_tac[reject_prefix_active])
  >> fs[reject_prefix_opcode_def] >> metis_tac[]
QED

Theorem reject_prefix_invariant_reachable[local]:
  !vs0 ctx fn inst s. raw_reachable vs0 ctx fn inst s ==>
    !name entry lbl start P.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME entry /\
      fn_entry_label entry = SOME lbl /\
      enters_block entry
        (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                     vs_inst_idx := 0|>) start /\
      P start /\
      (!t i. P t /\ active_inst entry i t ==> reject_prefix_opcode i) /\
      (!t u. P t /\ reject_prefix_step ctx entry t u ==> P u) ==>
      fn = entry /\ P s /\ reject_prefix_opcode inst
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >> strip_tac
  >- (gvs[enters_block_def] >> metis_tac[])
  >- (`fn = entry /\ P s /\ reject_prefix_opcode inst` by metis_tac[] >>
      qpat_x_assum `fn = entry` SUBST_ALL_TAC >>
      qpat_x_assum `!name entry lbl start P. _` kall_tac >>
      `step_inst 0 ctx inst s = OK s'` by
        fs[reject_prefix_opcode_def, step_inst_non_invoke] >>
      `reject_prefix_step ctx entry s (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
        (simp[reject_prefix_step_def] >> qexistsl_tac [`inst`,`s'`] >> simp[]) >>
      metis_tac[])
  >- (`fn = entry /\ P s /\ reject_prefix_opcode inst` by metis_tac[] >>
      qpat_x_assum `fn = entry` SUBST_ALL_TAC >>
      qpat_x_assum `!name entry lbl start P. _` kall_tac >>
      `step_inst 0 ctx inst s = OK s'` by
        fs[reject_prefix_opcode_def, step_inst_non_invoke] >>
      `reject_prefix_step ctx entry s s''` by
        (simp[reject_prefix_step_def] >> qexistsl_tac [`inst`,`s'`] >> simp[]) >>
      metis_tac[]) >>
  `fn = entry /\ P s /\ reject_prefix_opcode inst` by metis_tac[] >>
  fs[reject_prefix_opcode_def]
QED

Theorem no_dalloca_window[local]:
  dalloca_windows (\chunk index. F) insts <=>
  EVERY (\i. i.inst_opcode <> DALLOCA) insts
Proof
  simp[dalloca_windows_def, EVERY_EL] >> metis_tac[]
QED

Theorem no_dalloca_compiler_window[local]:
  compiler_dalloca_windows (\chunk index. F) st <=>
  EVERY (\i. i.inst_opcode <> DALLOCA) (state_insts st)
Proof
  simp[compiler_dalloca_windows_def, no_dalloca_window, state_insts_def,
       all_blocks_def, EVERY_FLAT, EVERY_MAP, combinTheory.o_DEF, EVERY_MEM, MEM_FLAT, MEM_MAP, MEM_REVERSE] >>
  metis_tac[]
QED

Theorem preserves_no_dalloca[local]:
  preserves_dalloca_windows (\chunk index. F) m /\
  EVERY (\i. i.inst_opcode <> DALLOCA) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> DALLOCA) (state_insts (SND (m st)))
Proof
  simp[GSYM no_dalloca_compiler_window, preserves_dalloca_windows_def] >>
  strip_tac >>
  first_x_assum (qspecl_then [`st`,`FST (m st)`,`SND (m st)`] mp_tac) >>
  simp[]
QED

Theorem frag_code_in_state_insts[local]:
  MEM i (frag_code sa sb) ==> MEM i (state_insts sb)
Proof
  `!b. MEM b (emitted_blocks sa sb) ==> MEM b sb.cs_blocks` by
    (simp[emitted_blocks_def] >> metis_tac[MEM_TAKE]) >>
  Cases_on `emitted_blocks sa sb` >>
  simp[frag_code_def, state_insts_def, emitted_insts_def, all_blocks_def,
       MEM_FLAT, MEM_MAP, MEM_REVERSE] >>
  strip_tac
  >- metis_tac[MEM_DROP_IMP] >>
  `MEM (LAST (h::t)) sb.cs_blocks` by metis_tac[MEM_LAST_NOT_NIL, NOT_CONS_NIL] >>
  `!b. MEM b (FRONT (h::t)) ==> MEM b sb.cs_blocks` by
    metis_tac[MEM_FRONT] >>
  metis_tac[MEM_DROP_IMP]
QED

Theorem every_reject_prefix_opcode[local]:
  EVERY reject_prefix_opcode insts <=>
    EVERY (\i. i.inst_opcode <> DALLOCA) insts /\
    EVERY (\i. i.inst_opcode <> INVOKE) insts
Proof
  simp[EVERY_MEM, reject_prefix_opcode_def] >> metis_tac[]
QED

Theorem compiler_reject_prefix_opcodes[local]:
  (!st. EVERY reject_prefix_opcode (state_insts st) ==>
    EVERY reject_prefix_opcode
      (state_insts (SND (compile_selector_dispatch_linear sels fb st)))) /\
  (!st. EVERY reject_prefix_opcode (state_insts st) ==>
    EVERY reject_prefix_opcode
      (state_insts (SND (compile_entry_checks mincd pay st)))) /\
  (!st. EVERY reject_prefix_opcode (state_insts st) ==>
    EVERY reject_prefix_opcode
      (state_insts (SND (compile_register_positional_args ce args off st))))
Proof
  simp_tac bool_ss [every_reject_prefix_opcode] >>
  rpt conj_tac >> rpt strip_tac
  >- (irule preserves_no_dalloca >> simp[dalloca_windows_dispatch])
  >- (irule (SIMP_RULE (srw_ss()) [] (Q.INST [`P` |-> `\opc. opc <> INVOKE`] opcode_every_selector_dispatch_linear)) >>
      asm_rewrite_tac[])
  >- (irule preserves_no_dalloca >> simp[dalloca_windows_entry_checks])
  >- (irule (SIMP_RULE (srw_ss()) [] (Q.INST [`P` |-> `\opc. opc <> INVOKE`] opcode_every_entry_checks)) >>
      asm_rewrite_tac[])
  >- (irule preserves_no_dalloca >> simp[dalloca_windows_register_positional_args])
  >> irule (SIMP_RULE (srw_ss()) [] (Q.INST [`P` |-> `\opc. opc <> INVOKE`] opcode_every_register_positional_args)) >>
  asm_rewrite_tac[]
QED

Theorem decode_certificate_prefix_opcodes[local]:
  decode_certificate m /\ m sa = (r,sb) /\
  (!st. EVERY P (state_insts st) ==> EVERY P (state_insts (SND (m st)))) ==>
  EVERY P (frag_code sa sb)
Proof
  strip_tac >>
  qpat_x_assum `decode_certificate m`
    (qspec_then `sa` strip_assume_tac o REWRITE_RULE [decode_certificate_def]) >>
  `decode_core (decode_core sa) = decode_core sa /\
   state_insts (decode_core sa) = []` by
    simp[decode_core_def, state_insts_def, all_blocks_def] >>
  qpat_assum `!h. decode_core h = _ ==> _`
    (qspec_then `sa` mp_tac) >> simp[] >> strip_tac >>
  qabbrev_tac `trimmed = decode_history n (decode_replay es (decode_core sa))` >>
  `m (decode_core sa) = (x,trimmed)` by
    (qpat_assum `decode_core (decode_core sa) = decode_core sa` (fn core =>
       qpat_assum `!h. decode_core h = decode_core sa ==> _`
         (mp_tac o C MATCH_MP core o Q.SPEC `decode_core sa`)) >>
     simp[NoAsms, Abbr `trimmed`]) >>
  `EVERY P (state_insts trimmed)` by
    (qpat_x_assum `!st. EVERY _ _ ==> _` (qspec_then `decode_core sa` mp_tac) >>
     qpat_assum `m (decode_core sa) = (x,trimmed)` (fn run =>
       qpat_assum `state_insts (decode_core sa) = []` (fn empty =>
         simp[NoAsms, run, empty]))) >>
  `EVERY P (frag_code (decode_core sa) trimmed)` by
    (fs[EVERY_MEM] >> metis_tac[frag_code_in_state_insts]) >>
  `PERM (frag_code (decode_core sa) trimmed) (decode_instructions es)` by
    simp[Abbr `trimmed`, decode_replay_frag_code_history] >>
  `PERM (frag_code sa sb) (decode_instructions es)` by
    gvs[decode_replay_frag_code_history] >>
  metis_tac[PERM_EVERY]
QED

Theorem reject_decode_args_certificate[local]:
  !args ce off load hi base. decode_certificate (compile_decode_args ce args off load hi base)
Proof
  Induct >> simp[compile_decode_args_def, decode_certificate_return] >>
  qx_gen_tac `arg` >> PairCases_on `arg` >> rpt gen_tac >>
  simp[compile_decode_args_def] >>
  rpt (FIRST [
    irule decode_certificate_bind >> conj_tac,
    irule decode_certificate_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[decode_certificate_bind, decode_certificate_ignore_bind,
      decode_certificate_emit_op, decode_certificate_emit_void, decode_certificate_return,
      decode_certificate_to_buf, decode_certificate_abi_clamp_basetype,
      compile_abi_arg_ptr_guard_def]),
    gen_tac, BasicProvers.TOP_CASE_TAC >> gvs[]])
QED

Theorem reject_positional_registration_certificate[local]:
  !args ce off. decode_certificate (compile_register_positional_args ce args off)
Proof
  Induct >> simp[compile_register_positional_args_def, decode_certificate_return] >>
  qx_gen_tac `arg` >> PairCases_on `arg` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  rpt (FIRST [
    irule decode_certificate_bind >> conj_tac,
    irule decode_certificate_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[decode_certificate_bind, decode_certificate_ignore_bind,
      decode_certificate_return, decode_certificate_alloc_buffer,
      reject_decode_args_certificate]),
    gen_tac, BasicProvers.TOP_CASE_TAC >> gvs[]])
QED

Theorem registration_reject_prefix_code[local]:
  compile_register_positional_args ce args off sa = (ce',sb) ==>
  EVERY reject_prefix_opcode (frag_code sa sb)
Proof
  strip_tac >>
  irule (INST_TYPE [alpha |-> ``:compile_env``] decode_certificate_prefix_opcodes) >>
  qexistsl_tac [`compile_register_positional_args ce args off`,`ce'`] >>
  simp[reject_positional_registration_certificate, cj 3 compiler_reject_prefix_opcodes]
QED

Theorem reject_decode_emit_bind[local]:
  opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN /\
  ~MEM (Label ex) ops /\
  (!v. v <> Label ex ==> decode_framed ex (f v) post) ==>
  decode_framed ex (comp_bind (emit_op opc ops) f) post
Proof
  strip_tac >> irule decode_framed_bind >>
  qexists_tac `\v. v <> Label ex` >> simp[] >>
  irule decode_straight_framed >> simp[decode_straight_emit_op]
QED

Theorem reject_decode_ignore[local]:
  decode_framed ex m (\v. T) /\ decode_framed ex n post ==>
  decode_framed ex (comp_ignore_bind m n) post
Proof
  strip_tac >> irule decode_framed_ignore_bind >>
  conj_tac >- (qexists_tac `\v. T` >> simp[]) >> first_assum ACCEPT_TAC
QED

fun reject_decoder_framed_tac ths = rpt (FIRST [
  CHANGED_TAC (simp (ths @ [decode_framed_return, decode_framed_to_buf])),
  irule decode_framed_return >> simp[],
  irule reject_decode_emit_bind >> simp[],
  irule reject_decode_ignore >> conj_tac,
  gen_tac, DISCH_TAC, COND_CASES_TAC,
  irule decode_straight_framed >>
    simp[decode_straight_emit_void, decode_straight_clamp_basetype] >> NO_TAC]);

Theorem reject_decode_ptr_guard_framed[local]:
  src <> Label ex /\ p <> Label ex ==>
  decode_framed ex (compile_abi_arg_ptr_guard CALLDATALOAD src p) (\v. T)
Proof
  strip_tac >> simp[compile_abi_arg_ptr_guard_def] >> reject_decoder_framed_tac []
QED

Theorem reject_decode_singleton_framed[local]:
  FLOOKUP ce.ce_vars name = SOME (PtrVar dst cap) /\ dst <> Label ex ==>
  decode_framed ex
    (compile_decode_args ce [(name,prim,dyn,sz,info)] off CALLDATALOAD (Lit 0w) 4)
    (\v. T)
Proof
  strip_tac >>
  Cases_on `prim` >> Cases_on `dyn` >>
  simp[compile_decode_args_def, var_location_decode_operand_def] >>
  reject_decoder_framed_tac [reject_decode_ptr_guard_framed]
QED

Theorem reject_positional_registration_framed[local]:
  !args ce off. decode_framed ex (compile_register_positional_args ce args off) (\v. T)
Proof
  Induct >- (simp[compile_register_positional_args_def] >> gen_tac >>
             irule decode_framed_return >> simp[]) >>
  qx_gen_tac `arg` >> PairCases_on `arg` >> rpt gen_tac >>
  Cases_on `FLOOKUP ce.ce_vars arg0` >>
  simp[compile_register_positional_args_def] >>
  Cases_on `var_location_memory_size x` >> simp[] >>
  irule decode_framed_bind >>
  qexists_tac `\b. b.buf_operand <> Label ex` >>
  reverse conj_tac >- (irule decode_straight_framed >> simp[decode_straight_alloc_buffer]) >>
  simp[comp_bind_return] >> rpt strip_tac >>
  irule reject_decode_ignore >> simp[reject_decode_singleton_framed, FLOOKUP_UPDATE]
QED

Theorem registration_fragment_layout[local]:
  compile_register_positional_args ce args off sa = (ce',sb) /\
  sa.cs_current_bb NOTIN decode_label_range sa.cs_next_label sb.cs_next_label ==>
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  frag_ops_free sa sb
Proof
  strip_tac >>
  `decode_framed sa.cs_current_bb (compile_register_positional_args ce args off) (\v. T)` by
    simp[reject_positional_registration_framed] >>
  drule decode_framed_run >> disch_then drule >>
  disch_then (qspec_then `{}` mp_tac) >> simp[] >> strip_tac >>
  drule decode_resource_run_trace >> strip_tac >>
  `~MEM sa.cs_current_bb (decode_switches es)` by
    (qpat_assum `set (decode_switches es) SUBSET _`
       (mp_tac o SIMP_RULE (srw_ss()) [SUBSET_DEF]) >> metis_tac[]) >>
  `ALL_DISTINCT (REVERSE (decode_switches es) ++ [sa.cs_current_bb])` by
    fs[decode_trace_safe_def, ALL_DISTINCT_APPEND, MEM_REVERSE] >>
  `sb.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks sa sb) =
   REVERSE (decode_switches es) ++ [sa.cs_current_bb]` by
    (qpat_assum `sb = decode_history _ _` (fn th => ONCE_REWRITE_TAC[th]) >>
     mp_tac (Q.INST [`s` |-> `sa`] decode_replay_labels) >>
     simp[NoAsms, decode_history_def, emitted_blocks_def]) >>
  `ALL_DISTINCT (sb.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks sa sb))` by
    metis_tac[] >>
  conj_tac >- fs[] >>
  `PERM (frag_code sa sb) (decode_instructions es)` by
    (qpat_assum `sb = decode_history _ _` (fn th => ONCE_REWRITE_TAC[th]) >>
     simp[decode_replay_frag_code_history]) >>
  fs[frag_ops_free_def, decode_trace_safe_def] >>
  metis_tac[PERM_EVERY]
QED

Theorem reject_prefix_observer_instruction[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  EVERY reject_prefix_opcode (frag_code sa sb) /\
  (lbl,idx) IN frag_observer_region sa sb /\
  (lbl,idx) <> frag_observer_cut sb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  reject_prefix_opcode inst /\
  ?original. lookup_block lbl fn.fn_blocks = SOME original /\
             get_instruction original idx = SOME inst
Proof
  strip_tac >> drule_all frag_observer_code_provenance >>
  drule_all frag_observer_instruction_agrees >> fs[EVERY_MEM]
QED

Theorem reject_prefix_observer_step[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  EVERY reject_prefix_opcode (frag_code sa sb) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s t ==>
  reject_prefix_step ctx fn s t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all frag_observer_step_transfer >> strip_tac >>
  `?bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME inst /\ reject_prefix_opcode inst` by
    (qpat_x_assum `abi_observer_step ctx (frag_observer _ _ _ _) _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_observer_step_def]) >>
     drule_all reject_prefix_observer_instruction >> metis_tac[]) >>
  qpat_x_assum `abi_observer_step ctx fn _ s t`
    (strip_assume_tac o REWRITE_RULE [abi_observer_step_def]) >>
  gvs[reject_prefix_step_def,enters_block_def] >>
  metis_tac[lookup_instruction_active]
QED

Theorem reject_prefix_observer_path[local]:
  !s t. RTC (abi_observer_step ctx (frag_observer sa sb fn id)
                    (frag_observer_cut sb)) s t ==>
    cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
    (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    EVERY reject_prefix_opcode (frag_code sa sb) /\
    (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb ==>
    RTC (reject_prefix_step ctx fn) s t
Proof
  ho_match_mp_tac RTC_INDUCT >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rename1 `abi_observer_step _ _ _ s middle` >>
  irule (cj 2 RTC_RULES) >> qexists_tac `middle` >>
  conj_tac >- metis_tac[reject_prefix_observer_step] >>
  first_x_assum irule >> simp[] >>
  metis_tac[frag_observer_region_closed, observer_region_closed_def]
QED

Theorem reject_prefix_observer_revert[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  EVERY reject_prefix_opcode (frag_code sa sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  run_from fuel ctx (frag_observer sa sb fn id) s = Abort Revert_abort v ==>
  ?u. RTC (reject_prefix_step ctx fn) s u /\ reject_prefix_terminal ctx fn u
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all abi_decode_frag_observer_reject_endpoint >> strip_tac >>
  `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb` by
    metis_tac[frag_observer_start_region] >>
  qexists_tac `u` >> conj_tac
  >- (drule_all reject_prefix_observer_path >> simp[]) >>
  drule_all reject_prefix_observer_instruction >> strip_tac >>
  simp[reject_prefix_terminal_def] >> qexists_tac `inst` >>
  fs[reject_prefix_opcode_def,step_inst_non_invoke] >>
  metis_tac[lookup_instruction_active]
QED

Theorem distinct_final_blocks_avoid_cut[local]:
  cs_extends sb final /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks final)) ==>
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb))
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks sb))` by
    (drule cs_extends_labels >> strip_tac >> fs[ALL_DISTINCT_APPEND]) >>
  fs[all_blocks_def, MAP_REVERSE, ALL_DISTINCT_APPEND, MEM_REVERSE, MEM_MAP] >>
  strip_tac >> gvs[emitted_blocks_def] >> metis_tac[MEM_TAKE]
QED

Theorem reject_observer_prefix_code[local]:
  fn_has_code sa sb fn /\
  (!bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) ==>
  prefix_code_agrees (frag_observer sa sb fn id) fn (frag_observer_cut sb)
Proof
  strip_tac >> simp[prefix_code_agrees_def] >> conj_tac
  >- (rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      drule frag_observer_lookup_cases >> strip_tac
      >- (gvs[] >>
          `idx < LENGTH sb.cs_current_insts` by
            (fs[get_instruction_def, frag_observer_cut_def] >> decide_tac) >>
          fs[fn_has_code_def, IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN]) >>
      fs[fn_has_code_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> drule frag_observer_lookup_cases >> strip_tac
  >- (gvs[] >> fs[fn_has_code_def, IS_PREFIX_APPEND] >>
      Cases_on `sb.cs_current_insts` >> gvs[phi_prefix_length_def, mk_inst_def, AllCaseEqs()]) >>
  fs[fn_has_code_def] >> metis_tac[]
QED

Theorem reject_observer_inst[local]:
  fn_has_code sa sb fn /\ ALL_DISTINCT (fn_labels fn) /\ active_inst fn i s /\
  lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME ob /\
  (s.vs_current_bb = sb.cs_current_bb ==> s.vs_inst_idx < LENGTH sb.cs_current_insts) ==>
  get_instruction ob s.vs_inst_idx = SOME i
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME i` by
    (fs[active_inst_def] >> qexists_tac `bb` >>
     simp[get_instruction_def] >> irule MEM_lookup_block >> simp[GSYM fn_labels_def]) >>
  drule frag_observer_lookup_cases >> strip_tac >> fs[fn_has_code_def]
  >- (gvs[IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN] >> metis_tac[]) >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem reject_prefix_reaches_jump[local]:
  no_phi_fn fn /\ reject_prefix_step ctx fn t u ==>
  (u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = SUC t.vs_inst_idx) \/
  (u.vs_inst_idx = 0 /\ ~u.vs_halted)
Proof
  strip_tac >> fs[reject_prefix_step_def] >-
    (drule_all step_preserves_control_flow >> simp[]) >>
  `step_inst_base inst t = OK t'` by
    metis_tac[reject_prefix_opcode_def, step_inst_non_invoke] >>
  `?lbl. step_inst_base inst t = OK (jump_to lbl t)` by
    (drule_all step_inst_base_ok_terminator_jump >>
     disch_then (DISJ_CASES_THEN strip_assume_tac) >>
     gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[]) >>
  `t' = jump_to lbl t` by metis_tac[exec_result_11] >> gvs[] >>
  `u = jump_to lbl t` by metis_tac[reject_jump_enters_block] >> fs[jump_to_def]
QED

(* Every live initializer continuation either remains in this fragment or
   hits its cut. The cut instruction itself is handled by the caller. *)
Theorem reject_fuel_prefix_closed[local]:
  fuel_ok Wv {} {} m /\ m sa = (x,sb) /\ at_point sa start /\
  fn_has_code sa sb fn /\ ALL_DISTINCT (fn_labels fn) /\ no_phi_fn fn /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  observer = frag_observer sa sb fn id /\
  RTC (\v w. reject_prefix_step ctx fn v w /\
    ?i bb. active_inst fn i v /\ lookup_block v.vs_current_bb observer.fn_blocks = SOME bb /\
        get_instruction bb v.vs_inst_idx = SOME i) start t /\
  IS_SOME (lookup_block t.vs_current_bb observer.fn_blocks) /\
  (t.vs_current_bb = sb.cs_current_bb ==> t.vs_inst_idx < LENGTH sb.cs_current_insts) /\
  reject_prefix_step ctx fn t u ==>
  RTC (\v w. reject_prefix_step ctx fn v w /\
    ?i bb. active_inst fn i v /\ lookup_block v.vs_current_bb observer.fn_blocks = SOME bb /\
        get_instruction bb v.vs_inst_idx = SOME i) start u /\
  IS_SOME (lookup_block u.vs_current_bb observer.fn_blocks) /\
  (u.vs_current_bb = sb.cs_current_bb ==> u.vs_inst_idx <= LENGTH sb.cs_current_insts)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?bb. lookup_block t.vs_current_bb observer.fn_blocks = SOME bb` by
    (Cases_on `lookup_block t.vs_current_bb observer.fn_blocks` >> fs[]) >>
  `?i. active_inst fn i t /\ get_instruction bb t.vs_inst_idx = SOME i` by
    (`?i. active_inst fn i t` by
       (qpat_assum `reject_prefix_step ctx fn t u`
          (strip_assume_tac o REWRITE_RULE [reject_prefix_step_def]) >>
        qexists_tac `inst` >> simp[]) >>
     qexists_tac `i` >> simp[] >>
     qpat_x_assum `observer = _` SUBST_ALL_TAC >>
     irule reject_observer_inst >> metis_tac[]) >>
  `RTC (\v w. reject_prefix_step ctx fn v w /\
      ?i bb. active_inst fn i v /\ lookup_block v.vs_current_bb observer.fn_blocks = SOME bb /\
          get_instruction bb v.vs_inst_idx = SOME i) start u` by
    (irule (cj 2 (SPEC_ALL RTC_RULES_RIGHT1)) >> qexists_tac `t` >> simp[] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule_all reject_prefix_reaches_jump >> disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (qpat_assum `u.vs_current_bb = _` SUBST1_TAC >>
      qpat_assum `u.vs_inst_idx = _` SUBST1_TAC >> simp[GSYM LESS_EQ]) >>
  conj_tac >-
    (`?Kb. frag_fuel Wv {} {} sa sb Kb` by fs[fuel_ok_def] >>
     mp_tac (Q.INST [`sa` |-> `sa`, `sb` |-> `sb`, `Wv` |-> `Wv`,
       `s` |-> `start`, `s'` |-> `u`, `observer` |-> `observer`, `id` |-> `id`,
       `Kb` |-> `Kb`, `cut` |->
         `<|bb_label := sb.cs_current_bb; bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`]
       frag_fuel_excludes_unlisted_jump) >>
     impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
        >- (qpat_assum `observer = _` SUBST1_TAC >> irule reject_observer_has_code >> simp[])
        >- (qpat_assum `observer = _` SUBST1_TAC >> irule fragObserverCodePropsTheory.abi_dyn_observer_no_phi >> simp[])
        >- simp[frag_observer_cut_lookup]
        >- simp[frag_observer_cut_instruction] >>
        rpt strip_tac >>
        qpat_assum `RTC _ start u` (mp_tac o MATCH_MP
          (Q.INST [`host` |-> `host`] reject_prefix_replay_path)) >>
        asm_rewrite_tac[]) >>
     disch_then ACCEPT_TAC) >>
  simp[]
QED

Theorem reject_prefix_step_unique[local]:
  ALL_DISTINCT (fn_labels fn) /\ reject_prefix_step ctx fn s u /\
  reject_prefix_step ctx fn s v ==> u = v
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!i j. active_inst fn i s /\ active_inst fn j s ==> i = j` by
    metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique] >>
  fs[reject_prefix_step_def] >>
  rpt (qpat_x_assum `_ \/ _` (DISJ_CASES_THEN strip_assume_tac)) >>
  `inst = inst'` by metis_tac[] >>
  gvs[enters_block_def]
QED

Theorem reject_prefix_invariant_prepend[local]:
  ALL_DISTINCT (fn_labels fn) /\ RTC (reject_prefix_step ctx fn) start first /\
  P first /\ (!s i. P s /\ active_inst fn i s ==> reject_prefix_opcode i) /\
  (!s t. P s /\ reject_prefix_step ctx fn s t ==> P t) ==>
  ?Q. Q start /\ (!s i. Q s /\ active_inst fn i s ==> reject_prefix_opcode i) /\
    (!s t. Q s /\ reject_prefix_step ctx fn s t ==> Q t)
Proof
  strip_tac >> qexists_tac `\s. RTC (reject_prefix_step ctx fn) s first \/ P s` >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> TRY (res_tac >> NO_TAC) >>
      qpat_x_assum `RTC _ s first` (mp_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >>
      disch_then (DISJ_CASES_THEN2 SUBST_ALL_TAC strip_assume_tac) >>
      metis_tac[reject_prefix_step_def, fmpStageBlockSimCodeTheory.active_inst_unique]) >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2
    (DISJ_CASES_THEN assume_tac) assume_tac)
  >- (qpat_x_assum `RTC _ s first` (mp_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >>
      disch_then (DISJ_CASES_THEN2 SUBST_ALL_TAC strip_assume_tac) >>
      metis_tac[reject_prefix_step_unique]) >>
  metis_tac[]
QED

Theorem reject_prefix_step_cannot_continue[local]:
  ALL_DISTINCT (fn_labels fn) /\ reject_prefix_terminal ctx fn s ==>
  ~reject_prefix_step ctx fn s t
Proof
  simp[reject_prefix_terminal_def, reject_prefix_step_def] >>
  metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique]
QED

Theorem reject_prefix_terminal_path_invariant[local]:
  ALL_DISTINCT (fn_labels fn) /\ RTC (reject_prefix_step ctx fn) s z /\
  reject_prefix_terminal ctx fn z ==>
  (!i. active_inst fn i s ==> reject_prefix_opcode i) /\
  (!t. reject_prefix_step ctx fn s t ==> RTC (reject_prefix_step ctx fn) t z)
Proof
  strip_tac >>
  qpat_x_assum `RTC _ s z` (mp_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >>
  disch_then (DISJ_CASES_THEN2 SUBST_ALL_TAC strip_assume_tac)
  >- (conj_tac
      >- (gen_tac >> strip_tac >> irule reject_prefix_active >>
          qexistsl_tac [`ctx`,`fn`,`z`,`z`] >> simp[]) >>
      metis_tac[reject_prefix_step_cannot_continue]) >>
  conj_tac >- metis_tac[reject_prefix_step_def, fmpStageBlockSimCodeTheory.active_inst_unique] >>
  metis_tac[reject_prefix_step_unique]
QED

Theorem reject_prefix_step_state[local]:
  no_phi_fn fn /\ reject_prefix_step ctx fn s t ==>
  ?i r. active_inst fn i s /\ reject_prefix_opcode i /\
    step_inst 0 ctx i s = OK r /\ t = r with vs_inst_idx := t.vs_inst_idx
Proof
  strip_tac >> fs[reject_prefix_step_def]
  >- (qexistsl_tac [`inst`,`t'`] >> simp[]) >>
  qexistsl_tac [`inst`,`t'`] >> simp[] >>
  fs[enters_block_def, no_phi_fn_def, EVERY_MEM] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  gvs[eval_phis_no_phi]
QED

Theorem reject_prefix_step_allocation_frame[local]:
  no_phi_fn fn /\ fn_inst_ids_distinct fn /\ reject_prefix_step ctx fn s t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_halted = s.vs_halted /\
  (alloca_inv s ==> alloca_inv t) /\
  t.vs_alloca_next + remaining_alloca_budget (fn_insts fn) t =
  s.vs_alloca_next + remaining_alloca_budget (fn_insts fn) s
Proof
  strip_tac >> drule_all reject_prefix_step_state >> strip_tac >>
  `MEM i (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
  drule fn_inst_ids_distinct_all_distinct >> strip_tac >>
  drule_all step_inst_alloca_budget >> strip_tac >>
  `t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next` by
    (qpat_assum `t = r with vs_inst_idx := t.vs_inst_idx` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `remaining_alloca_budget (fn_insts fn) t = remaining_alloca_budget (fn_insts fn) r` by
    (irule remaining_alloca_budget_domain_cong >> simp[]) >>
  simp[] >> conj_tac
  >- (qpat_assum `t = r with vs_inst_idx := t.vs_inst_idx` (fn th => ONCE_REWRITE_TAC [th]) >>
      simp[] >> metis_tac[step_inst_ok_preserves_call_ctx]) >>
  conj_tac
  >- (qpat_assum `t = r with vs_inst_idx := t.vs_inst_idx` (fn th => ONCE_REWRITE_TAC [th]) >>
      simp[] >> fs[reject_prefix_opcode_def] >>
      qpat_assum `i.inst_opcode <> INVOKE` (fn safe =>
        qpat_assum `step_inst 0 ctx i s = OK r`
          (ACCEPT_TAC o MATCH_MP step_inst_base_OK_preserves_halted o
            PURE_REWRITE_RULE [MATCH_MP
              (Q.SPECL [`0`,`ctx`,`i`,`s`] step_inst_non_invoke) safe]))) >>
  strip_tac >> drule_all alloca_inv_step_inst >> strip_tac >>
  fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem reject_prefix_allocation_frame[local]:
  !s t. RTC (reject_prefix_step ctx fn) s t ==>
  no_phi_fn fn /\ fn_inst_ids_distinct fn ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_halted = s.vs_halted /\
  (alloca_inv s ==> alloca_inv t) /\
  t.vs_alloca_next + remaining_alloca_budget (fn_insts fn) t =
  s.vs_alloca_next + remaining_alloca_budget (fn_insts fn) s
Proof
  ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  drule_all reject_prefix_step_allocation_frame >> metis_tac[]
QED

Theorem reject_prefix_step_counters[local]:
  no_phi_fn fn /\ ALL_DISTINCT (fn_labels fn) /\
  reject_prefix_step ctx fn s t /\ active_inst fn i s /\
  (i.inst_opcode = ALLOCA ==> i.inst_id < st.cs_next_id) /\
  EVERY (not_fresh_at st) i.inst_outputs /\
  fresh_vars_wrt st s /\
  (!id e. FLOOKUP s.vs_allocas id = SOME e ==> id < st.cs_next_id) ==>
  fresh_vars_wrt st t /\
  (!id e. FLOOKUP t.vs_allocas id = SOME e ==> id < st.cs_next_id)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all reject_prefix_step_state >> strip_tac >>
  `i' = i` by metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique] >>
  pop_assum SUBST_ALL_TAC >>
  qpat_assum `t = r with vs_inst_idx := t.vs_inst_idx` (fn th => ONCE_REWRITE_TAC[th]) >>
  simp_tac bool_ss [fresh_vars_wrt_def, venom_state_accfupds] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      `~MEM (STRING #"%" (toString n)) i.inst_outputs` by
        (fs[EVERY_MEM, not_fresh_at_def] >> metis_tac[GREATER_EQ]) >>
      `lookup_var (STRING #"%" (toString n)) r =
       lookup_var (STRING #"%" (toString n)) s` by
        (Cases_on `is_terminator i.inst_opcode` >>
         metis_tac[step_preserves_non_output_vars, step_terminator_preserves_vars]) >>
      qpat_assum `fresh_vars_wrt st s`
        (qspec_then `n` mp_tac o REWRITE_RULE [fresh_vars_wrt_def]) >>
      simp_tac bool_ss [GSYM (CONJUNCT1 (SPEC_ALL finite_mapTheory.flookup_thm))] >>
      fs[lookup_var_def]) >>
  qx_gen_tac `id` >> PairCases >> strip_tac >>
  imp_res_tac step_inst_alloca_lookup_origin >> fs[reject_prefix_opcode_def] >> metis_tac[]
QED

Theorem reject_prefix_observed_counters[local]:
  !s t. RTC (\v w. reject_prefix_step ctx fn v w /\
    ?i bb. active_inst fn i v /\ lookup_block v.vs_current_bb obs.fn_blocks = SOME bb /\
       get_instruction bb v.vs_inst_idx = SOME i) s t ==>
  no_phi_fn fn /\ ALL_DISTINCT (fn_labels fn) /\
  (!i. MEM i (fn_insts obs) ==>
    (i.inst_opcode = ALLOCA ==> i.inst_id < st.cs_next_id) /\
    EVERY (not_fresh_at st) i.inst_outputs) /\
  fresh_vars_wrt st s /\
  (!id e. FLOOKUP s.vs_allocas id = SOME e ==> id < st.cs_next_id) ==>
  fresh_vars_wrt st t /\
  (!id e. FLOOKUP t.vs_allocas id = SOME e ==> id < st.cs_next_id)
Proof
  ho_match_mp_tac RTC_INDUCT >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  `MEM i (fn_insts obs)` by
    (irule lookup_block_fn_insts >>
     fs[get_instruction_def, AllCaseEqs()] >> metis_tac[EL_MEM]) >>
  `EVERY (not_fresh_at st) i.inst_outputs /\
   (i.inst_opcode = ALLOCA ==> i.inst_id < st.cs_next_id)` by metis_tac[] >>
  drule_all reject_prefix_step_counters >> metis_tac[]
QED

Theorem finalized_block_in_later_state[local]:
  new_block label before = (prev,opened) /\ cs_extends opened after ==>
  MEM <|bb_label := before.cs_current_bb; bb_instructions := before.cs_current_insts|>
    (all_blocks after)
Proof
  strip_tac >> drule new_block_props >> strip_tac >>
  fs[cs_extends_def, all_blocks_def, MEM_REVERSE]
QED

Theorem external_bodies_start_block[local]:
  exts <> [] /\ compile_external_fn_bodies exts sd = ((),sx) ==>
  ?label prev opened. new_block label sd = (prev,opened) /\ cs_extends opened sx
Proof
  Cases_on `exts` >> simp[] >> PairCases_on `h` >>
  simp[compile_external_fn_bodies_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  goal_assum (drule_at Any) >>
  drule (SRULE [cs_appends_def] cs_appends_entry_checks) >> strip_tac >>
  drule (SRULE [cs_appends_def] cs_appends_external_function_body) >> strip_tac >>
  drule (SRULE [cs_appends_def] cs_appends_external_fn_bodies) >> strip_tac >>
  metis_tac[cs_extends_trans]
QED

Theorem reject_observer_code[local]:
  cs_extends sa sb /\ EVERY reject_prefix_opcode sa.cs_current_insts /\
  EVERY reject_prefix_opcode (frag_code sa sb) ==>
  EVERY reject_prefix_opcode (fn_insts (frag_observer sa sb fn id))
Proof
  strip_tac >>
  `EVERY reject_prefix_opcode sb.cs_current_insts /\
   EVERY (\bb. EVERY reject_prefix_opcode bb.bb_instructions) (emitted_blocks sa sb)` by
    (drule frag_extends_emitted_shape >>
     Cases_on `emitted_blocks sa sb = []` >> simp[] >> strip_tac
     >- (gvs[frag_code_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_LENGTH_APPEND] >>
         simp[EVERY_APPEND]) >>
     `emitted_blocks sa sb =
      FRONT (emitted_blocks sa sb) ++ [LAST (emitted_blocks sa sb)]` by
       simp[APPEND_FRONT_LAST] >>
     fs[frag_code_def, NULL_EQ, EVERY_APPEND, EVERY_FLAT, EVERY_MAP, combinTheory.o_DEF] >>
     fs[IS_PREFIX_APPEND] >>
     qpat_x_assum `emitted_blocks sa sb = FRONT _ ++ _` (fn th => ONCE_REWRITE_TAC [th]) >>
     gvs[EVERY_APPEND, DROP_LENGTH_APPEND]) >>
  simp[frag_observer_def, fn_insts_def, fn_insts_blocks_def, EVERY_APPEND,
       reject_prefix_opcode_def, mk_inst_def, EVERY_MEM,
       MEM_fn_insts_blocks_iff, MEM_FILTER] >>
  fs[EVERY_MEM, reject_prefix_opcode_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem reject_observer_contains_start[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  at_point sa start ==>
  IS_SOME (lookup_block start.vs_current_bb (frag_observer sa sb fn id).fn_blocks) /\
  (start.vs_current_bb = sb.cs_current_bb ==> start.vs_inst_idx <= LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_all reject_observer_has_code >> strip_tac >>
  drule frag_extends_emitted_shape >>
  Cases_on `emitted_blocks sa sb = []` >> simp[] >> strip_tac >>
  fs[at_point_def, fn_has_code_def]
  >- (conj_tac >- metis_tac[optionTheory.IS_SOME_DEF] >>
      fs[IS_PREFIX_APPEND] >> simp[]) >>
  `MEM (LAST (emitted_blocks sa sb)) (emitted_blocks sa sb)` by
    metis_tac[MEM_LAST_NOT_NIL] >>
  conj_tac >- metis_tac[optionTheory.IS_SOME_DEF] >>
  fs[MEM_MAP] >> metis_tac[]
QED

Theorem reject_fuel_prefix_invariant[local]:
  fuel_ok Wv {} {} m /\ m sa = (x,sb) /\ at_point sa start /\
  cs_extends sa sb /\ fn_has_code sa sb fn /\ ALL_DISTINCT (fn_labels fn) /\ no_phi_fn fn /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  EVERY reject_prefix_opcode sa.cs_current_insts /\
  EVERY reject_prefix_opcode (frag_code sa sb) /\
  (!t. RTC (\v w. reject_prefix_step ctx fn v w /\
     ?i bb. active_inst fn i v /\
       lookup_block v.vs_current_bb (frag_observer sa sb fn 0).fn_blocks = SOME bb /\
       get_instruction bb v.vs_inst_idx = SOME i) start t /\
    at_point sb t ==>
    ?z. RTC (reject_prefix_step ctx fn) t z /\ reject_prefix_terminal ctx fn z) ==>
  ?P. P start /\ (!s i. P s /\ active_inst fn i s ==> reject_prefix_opcode i) /\
    (!s t. P s /\ reject_prefix_step ctx fn s t ==> P t)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `observer = frag_observer sa sb fn (0:num)` >>
  qabbrev_tac `observed = \v w. reject_prefix_step ctx fn v w /\
    ?i bb. active_inst fn i v /\ lookup_block v.vs_current_bb observer.fn_blocks = SOME bb /\
      get_instruction bb v.vs_inst_idx = SOME i` >>
  qabbrev_tac `confined = \t. RTC observed start t /\
    IS_SOME (lookup_block t.vs_current_bb observer.fn_blocks) /\
    (t.vs_current_bb = sb.cs_current_bb ==> t.vs_inst_idx <= LENGTH sb.cs_current_insts)` >>
  `!t. confined t /\ at_point sb t ==>
    ?z. RTC (reject_prefix_step ctx fn) t z /\ reject_prefix_terminal ctx fn z` by
    (simp[Abbr `confined`, Abbr `observed`, Abbr `observer`] >> metis_tac[]) >>
  `!t. confined t /\ ~at_point sb t ==>
    t.vs_current_bb = sb.cs_current_bb ==> t.vs_inst_idx < LENGTH sb.cs_current_insts` by
    (simp[Abbr `confined`, at_point_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  `EVERY reject_prefix_opcode (fn_insts observer)` by
    (simp[Abbr `observer`] >> irule reject_observer_code >> simp[]) >>
  qexists_tac `\t. confined t \/ ?z. RTC (reject_prefix_step ctx fn) t z /\ reject_prefix_terminal ctx fn z` >>
  simp[] >> conj_tac
  >- (disj1_tac >> simp[Abbr `confined`, Abbr `observer`] >>
      irule reject_observer_contains_start >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> disch_then (CONJUNCTS_THEN2 (DISJ_CASES_THEN strip_assume_tac) assume_tac)
      >- (Cases_on `at_point sb s` >- metis_tac[reject_prefix_active] >>
          `?bb. lookup_block s.vs_current_bb observer.fn_blocks = SOME bb` by
            (fs[Abbr `confined`] >> Cases_on `lookup_block s.vs_current_bb observer.fn_blocks` >> fs[]) >>
          `get_instruction bb s.vs_inst_idx = SOME i` by
            (qpat_x_assum `Abbrev (observer = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
             irule reject_observer_inst >> simp[] >> qexistsl_tac [`fn`,`0`,`sa`,`sb`] >> simp[]) >>
          fs[EVERY_MEM, get_instruction_def, AllCaseEqs()] >>
          metis_tac[lookup_block_fn_insts, EL_MEM]) >>
      metis_tac[reject_prefix_active]) >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 (DISJ_CASES_THEN strip_assume_tac) assume_tac)
  >- (Cases_on `at_point sb s`
      >- (disj2_tac >> metis_tac[reject_prefix_terminal_path_invariant]) >>
      disj1_tac >> fs[Abbr `confined`, Abbr `observed`] >>
      mp_tac (Q.INST [`t` |-> `s`,`u` |-> `t`,
        `observer` |-> `observer`,`id` |-> `0`] reject_fuel_prefix_closed) >>
      simp[Abbr `observer`] >> metis_tac[]) >>
  disj2_tac >> metis_tac[reject_prefix_terminal_path_invariant]
QED

Theorem installed_kwarg_initializer_invariant[local]:
  compile_init_kwargs ce vars off k (Lit 0w) init = ((),mid) /\
  cs_extends init mid /\ cs_extends mid dispatch_end /\ cs_extends dispatch_end final /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks final)) /\
  fn_has_code init mid fn /\ ALL_DISTINCT (fn_labels fn) /\ no_phi_fn fn /\
  EVERY reject_prefix_opcode (state_insts dispatch_end) /\ at_point init start /\
  (!t. RTC (\v w. reject_prefix_step ctx fn v w /\
     ?i bb. active_inst fn i v /\
       lookup_block v.vs_current_bb (frag_observer init mid fn 0).fn_blocks = SOME bb /\
       get_instruction bb v.vs_inst_idx = SOME i) start t /\
    at_point mid t ==>
    ?z. RTC (reject_prefix_step ctx fn) t z /\ reject_prefix_terminal ctx fn z) ==>
  ?P. P start /\ (!s i. P s /\ active_inst fn i s ==> reject_prefix_opcode i) /\
    (!s t. P s /\ reject_prefix_step ctx fn s t ==> P t)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `fuel_ok {} {} {} (compile_init_kwargs ce vars off k (Lit 0w))` by
    (irule fuel_ok_compile_init_kwargs >> simp[CONJUNCT1 fuel_ok_compile_expr]) >>
  `~MEM mid.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks init mid))` by
    (irule distinct_final_blocks_avoid_cut >> qexists_tac `final` >> simp[] >>
     metis_tac[cs_extends_trans]) >>
  `EVERY reject_prefix_opcode (state_insts init) /\
   EVERY reject_prefix_opcode (state_insts mid)` by
    (qpat_assum `cs_extends mid dispatch_end` (strip_assume_tac o MATCH_MP (SPEC_ALL state_insts_cs_extends)) >>
     qpat_assum `cs_extends init mid` (strip_assume_tac o MATCH_MP (SPEC_ALL state_insts_cs_extends)) >>
     qpat_assum `state_insts dispatch_end = _` (fn eq =>
       qpat_assum `EVERY _ (state_insts dispatch_end)`
         (mp_tac o PURE_REWRITE_RULE [eq])) >>
     qpat_assum `state_insts mid = _` (fn eq => PURE_REWRITE_TAC [eq]) >>
     simp[EVERY_APPEND]) >>
  `EVERY reject_prefix_opcode init.cs_current_insts` by
    fs[state_insts_def, all_blocks_def, EVERY_APPEND] >>
  `EVERY reject_prefix_opcode (frag_code init mid)` by
    (fs[EVERY_MEM] >> metis_tac[frag_code_in_state_insts]) >>
  mp_tac (Q.INST [`m` |-> `compile_init_kwargs ce vars off k (Lit 0w)`,
    `x` |-> `()`, `Wv` |-> `{}:string set`, `sa` |-> `init`, `sb` |-> `mid`]
    (Q.INST_TYPE [`:'a` |-> `:unit`] reject_fuel_prefix_invariant)) >> simp[]
QED

Theorem safe_observer_step_in_context[local]:
  prefix_code_agrees observer fn cut /\
  EVERY reject_prefix_opcode (fn_insts observer) /\
  abi_observer_step observer_ctx observer cut s t ==>
  reject_prefix_step ctx fn s t
Proof
  strip_tac >>
  drule_all abi_observer_step_transfer >> strip_tac >>
  `?bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME inst /\ reject_prefix_opcode inst` by
    (qpat_x_assum `abi_observer_step observer_ctx observer cut s t`
       (strip_assume_tac o REWRITE_RULE [abi_observer_step_def]) >>
     `reject_prefix_opcode inst` by
       (fs[EVERY_MEM, get_instruction_def, AllCaseEqs()] >> metis_tac[lookup_block_fn_insts, EL_MEM]) >>
     qpat_x_assum `prefix_code_agrees _ _ _`
       (strip_assume_tac o REWRITE_RULE [prefix_code_agrees_def]) >>
     metis_tac[]) >>
  qpat_x_assum `abi_observer_step observer_ctx fn cut s t`
    (strip_assume_tac o REWRITE_RULE [abi_observer_step_def]) >>
  gvs[reject_prefix_step_def, enters_block_def] >>
  qexistsl_tac [`inst`,`middle`] >>
  gs[step_inst_non_invoke] >> metis_tac[lookup_instruction_active]
QED

Theorem safe_observer_path_in_context[local]:
  !s t. RTC (abi_observer_step observer_ctx observer cut) s t ==>
  prefix_code_agrees observer fn cut /\
  EVERY reject_prefix_opcode (fn_insts observer) ==>
  RTC (reject_prefix_step ctx fn) s t
Proof
  ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  irule (cj 2 RTC_RULES) >> metis_tac[safe_observer_step_in_context]
QED

Theorem safe_local_prefix_in_context[local]:
  !observer_ctx observer cut s t. local_prefix observer_ctx observer cut s t ==>
  prefix_code_agrees observer fn cut /\
  EVERY reject_prefix_opcode (fn_insts observer) ==>
  RTC (reject_prefix_step ctx fn) s t
Proof
  ho_match_mp_tac local_prefix_ind >> simp[] >> rpt strip_tac >>
  irule (cj 2 RTC_RULES) >> metis_tac[safe_observer_step_in_context]
QED

Theorem safe_observer_runs_to_cut[local]:
  prefix_code_agrees observer fn (t.vs_current_bb,t.vs_inst_idx) /\
  EVERY reject_prefix_opcode (fn_insts observer) /\
  lookup_block t.vs_current_bb observer.fn_blocks = SOME cut_bb /\
  get_instruction cut_bb t.vs_inst_idx = SOME (mk_inst id STOP [] []) /\
  ~s.vs_halted /\ ~t.vs_halted /\ runs_through observer_ctx observer s t ==>
  ?u. RTC (reject_prefix_step ctx fn) s u /\ ~u.vs_halted /\
      u = t with vs_returndata := u.vs_returndata
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all run_from_stop_view >> disch_then (qspec_then `observer_ctx` assume_tac) >>
  fs[runs_through_def] >>
  `?fuel. run_from fuel observer_ctx observer s = Halt (stop_view t)` by
    (qpat_assum `run_from 0 observer_ctx observer t = Halt (stop_view t)`
       (fn halt =>
         qpat_assum `!fuel. _ ==> _`
           (mp_tac o SIMP_RULE (srw_ss()) [halt] o Q.SPEC `0`)) >>
     disch_then ACCEPT_TAC) >>
  `?bb. lookup_block s.vs_current_bb observer.fn_blocks = SOME bb` by
    (Cases_on `lookup_block s.vs_current_bb observer.fn_blocks` >> gvs[run_from_def]) >>
  `?u. local_prefix observer_ctx observer (t.vs_current_bb,t.vs_inst_idx) s u /\
       stop_view u = stop_view t` by
    (irule frag_cut_run_prefix_aux >> fs[stop_view_def, halt_state_def] >>
     conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
     conj_tac >- (qexists_tac `fuel` >> simp[]) >>
     qexists_tac `UNIV` >> simp[observer_region_closed_def] >>
     fs[EVERY_MEM, reject_prefix_opcode_def, get_instruction_def, AllCaseEqs()] >>
     metis_tac[lookup_block_fn_insts, EL_MEM]) >>
  qexists_tac `u` >>
  drule local_prefix_endpoint >> strip_tac >> simp[] >>
  conj_tac >- metis_tac[safe_local_prefix_in_context] >>
  metis_tac[stop_view_recover]
QED

Theorem safe_observer_instruction[local]:
  EVERY reject_prefix_opcode (fn_insts observer) /\
  lookup_block lbl observer.fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  reject_prefix_opcode inst
Proof
  simp[EVERY_MEM, get_instruction_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> metis_tac[lookup_block_fn_insts, EL_MEM]
QED

Theorem reject_fragment_continues[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  (!bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  EVERY reject_prefix_opcode sa.cs_current_insts /\
  EVERY reject_prefix_opcode (frag_code sa sb) /\
  ~s.vs_halted /\
  (!observer. fn_has_code sa sb observer ==>
    ?t. runs_through ctx observer s t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\ P t) ==>
  ?t u. P t /\ RTC (reject_prefix_step ctx fn) s u /\ ~u.vs_halted /\
        u = t with vs_returndata := u.vs_returndata
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `observer = frag_observer sa sb fn 0` >>
  `fn_has_code sa sb observer /\ EVERY reject_prefix_opcode (fn_insts observer) /\
   prefix_code_agrees observer fn (frag_observer_cut sb)` by
    (simp[Abbr `observer`] >> metis_tac[reject_observer_code,
      reject_observer_has_code, reject_observer_prefix_code]) >>
  qpat_assum `!obs. fn_has_code _ _ obs ==> _`
    (qspec_then `observer` (fn th =>
      qpat_assum `fn_has_code sa sb observer` (strip_assume_tac o MATCH_MP th))) >>
  qexists_tac `t` >> simp[] >>
  irule safe_observer_runs_to_cut >> simp[] >>
  qexistsl_tac [`<|bb_label := sb.cs_current_bb;
                    bb_instructions := sb.cs_current_insts ++ [mk_inst 0 STOP [] []]|>`,
                `0`,`observer`,`ctx`] >>
  simp[Abbr `observer`, frag_observer_cut_def, frag_observer_cut_lookup,
       frag_observer_cut_instruction] >>
  fs[frag_observer_cut_def]
QED

Theorem installed_legacy_selector_prefix[local]:
  compile_selector_dispatch_linear sels fb sa = ((),sb) /\
  new_block (linear_dispatch_target s.vs_call_ctx.cc_calldata sels fb) sb = (prev,sc) /\
  fn_has_code sa sc fn /\
  ~MEM sc.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sc)) /\
  (!bb. lookup_block sc.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  EVERY reject_prefix_opcode (state_insts sa) /\
  EVERY (\(sel,lbl). sel < 2 ** 32) sels /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. RTC (reject_prefix_step ctx fn) s t /\ ~t.vs_halted /\
      t.vs_call_ctx = s.vs_call_ctx /\ fresh_vars_wrt sb t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = 0
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `cs_extends sa sb /\ cs_extends sb sc` by
    metis_tac[cs_extends_new_block, cs_appends_selector_dispatch_linear, cs_appends_def] >>
  `sc.cs_current_bb = linear_dispatch_target s.vs_call_ctx.cc_calldata sels fb /\
   sc.cs_current_insts = [] /\ state_insts sc = state_insts sb` by
    (qpat_x_assum `new_block _ _ = _` mp_tac >>
     simp[NoAsms, new_block_def] >> strip_tac >>
     gvs[state_insts_def, all_blocks_def, REVERSE_DEF]) >>
  `EVERY reject_prefix_opcode (state_insts sc)` by
    (qspec_then `sa` mp_tac (cj 1 compiler_reject_prefix_opcodes) >> simp[]) >>
  `EVERY reject_prefix_opcode sa.cs_current_insts /\
   EVERY reject_prefix_opcode (frag_code sa sc)` by
    (conj_tac
     >- (fs[state_insts_def, all_blocks_def, EVERY_APPEND] >> simp[]) >>
     fs[EVERY_MEM] >> metis_tac[frag_code_in_state_insts]) >>
  mp_tac (Q.INST [`P` |-> `\u. u.vs_call_ctx = s.vs_call_ctx /\ fresh_vars_wrt sb u /\
                                     u.vs_allocas = s.vs_allocas /\
                                     u.vs_alloca_next = s.vs_alloca_next /\
                                     u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = 0`,
                 `sb` |-> `sc`] reject_fragment_continues) >>
  impl_tac
  >- (simp[] >> conj_tac >- metis_tac[cs_extends_trans] >>
      qx_gen_tac `observer` >> strip_tac >>
      `fn_has_code sa sb observer` by metis_tac[fn_has_code_split] >>
      drule_all compile_selector_dispatch_linear_correct >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      drule vars_pc_only_fields >> strip_tac >> qexists_tac `tt` >>
      fs[vars_pc_only_def, venom_state_component_equality]) >>
  disch_then (qx_choosel_then [`t`,`u`] strip_assume_tac) >>
  qexists_tac `u` >> simp[] >>
  qpat_assum `u = t with vs_returndata := _` (fn th => ONCE_REWRITE_TAC [th]) >>
  fs[fresh_vars_wrt_def]
QED

Theorem installed_dispatch_cut_code[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\
  lookup_block sb.cs_current_bb fn.fn_blocks =
    SOME <|bb_label := sb.cs_current_bb; bb_instructions := sb.cs_current_insts|> /\
  lookup_block target fn.fn_blocks = SOME bb /\
  new_block target sb = (prev,sc) ==>
  fn_has_code sa sc fn
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule new_block_props >> strip_tac >>
  `sb.cs_blocks = emitted_blocks sa sb ++ sa.cs_blocks` by
    (fs[cs_extends_def] >> metis_tac[emitted_blocks_append]) >>
  `emitted_blocks sa sc =
   <|bb_label := sb.cs_current_bb; bb_instructions := sb.cs_current_insts|> ::
     emitted_blocks sa sb` by
    (irule emitted_blocks_append >> simp[]) >>
  fs[fn_has_code_def] >> rpt strip_tac >> gvs[]
QED

Theorem installed_cut_unshadowed[local]:
  fn_has_code sa sb fn /\
  lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb 0 = SOME i /\ EVERY P (state_insts sb) /\ ~P i ==>
  ~MEM sb.cs_current_bb (MAP (\block. block.bb_label) (emitted_blocks sa sb))
Proof
  simp[MEM_MAP] >> rpt strip_tac >>
  `MEM bb (emitted_blocks sa sb)` by
    (fs[fn_has_code_def] >>
     rename1 `MEM other (emitted_blocks sa sb)` >>
     qpat_assum `!b. MEM b (emitted_blocks sa sb) ==> _`
       (qspec_then `other` (drule_then assume_tac)) >>
     gvs[]) >>
  fs[EVERY_MEM] >>
  `MEM i bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[get_instruction_def]) >>
  `MEM bb sb.cs_blocks` by
    (fs[emitted_blocks_def] >> metis_tac[MEM_TAKE]) >>
  `MEM i (state_insts sb)` by
    (simp[state_insts_def, all_blocks_def, MEM_FLAT, MEM_MAP, MEM_REVERSE] >>
     metis_tac[]) >>
  metis_tac[]
QED

Theorem installed_empty_revert_code[local]:
  emit_inst REVERT [Lit 0w; Lit 0w] [] sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id REVERT [Lit 0w; Lit 0w] [])
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. _ ==> _` (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[]
QED

Theorem installed_empty_revert_terminal[local]:
  emit_inst REVERT [Lit 0w; Lit 0w] [] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  reject_prefix_terminal ctx fn s
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all installed_empty_revert_code >> strip_tac >>
  `active_inst fn (mk_inst sa.cs_next_id REVERT [Lit 0w; Lit 0w] []) s` by
    metis_tac[lookup_instruction_active] >>
  simp[reject_prefix_terminal_def] >>
  qexists_tac `mk_inst sa.cs_next_id REVERT [Lit 0w; Lit 0w] []` >>
  simp[reject_prefix_opcode_def, step_inst_non_invoke,
       step_inst_base_opcode_eqs, eval_operand_def, mk_inst_def] >>
  fs[mk_inst_def]
QED

Theorem reject_prefix_jump[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) /\
  lookup_block lbl fn.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 /\ ~s.vs_halted ==>
  reject_prefix_step ctx fn s (jump_to lbl s)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `active_inst fn (mk_inst id JMP [Label lbl] []) s` by
    metis_tac[lookup_instruction_active] >>
  simp[reject_prefix_step_def] >>
  qexistsl_tac [`mk_inst id JMP [Label lbl] []`, `jump_to lbl s`] >>
  simp[reject_prefix_opcode_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
    is_terminator_def, mk_inst_def] >>
  simp[enters_block_def, jump_to_def] >>
  Cases_on `target.bb_instructions` >>
  gvs[eval_phis_def, phi_prefix_length_def, AllCaseEqs()]
QED

Theorem reject_prefix_scalar[local]:
  !ctx fn s u bb inst t.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~s.vs_halted /\ reject_prefix_opcode inst /\
  ~is_terminator inst.inst_opcode /\ step_inst 0 ctx inst s = OK t /\
  u = t with vs_inst_idx := SUC s.vs_inst_idx ==>
  reject_prefix_step ctx fn s u
Proof
  rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  simp[reject_prefix_step_def] >>
  qexistsl_tac [`inst`,`t`] >>
  metis_tac[lookup_instruction_active]
QED

Theorem reject_prefix_branch[local]:
  !ctx fn s lbl bb id test yes no target value.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JNZ [test; Label yes; Label no] []) /\
  eval_operand test s = SOME value /\
  lbl = (if value = 0w then no else yes) /\
  lookup_block lbl fn.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 /\ ~s.vs_halted ==>
  reject_prefix_step ctx fn s (jump_to lbl s)
Proof
  rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `active_inst fn (mk_inst id JNZ [test; Label yes; Label no] []) s` by
    metis_tac[lookup_instruction_active] >>
  simp[reject_prefix_step_def] >>
  qexistsl_tac [`mk_inst id JNZ [test; Label yes; Label no] []`, `jump_to lbl s`] >>
  simp[reject_prefix_opcode_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
    is_terminator_def, mk_inst_def] >>
  simp[enters_block_def, jump_to_def] >>
  Cases_on `target.bb_instructions` >>
  gvs[eval_phis_def, phi_prefix_length_def, AllCaseEqs()]
QED

Theorem reject_prefix_comparison[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id EQ [mid; Lit (n2w sel)] [out]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst next_id JNZ [Var out; Label yes; Label no] []) /\
  eval_operand mid s = SOME m /\ ~s.vs_halted /\
  lbl = (if m = n2w sel then yes else no) /\
  lookup_block lbl fn.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 ==>
  ?t. RTC (reject_prefix_step ctx fn) s t /\
      t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\ vars_pc_only s t /\
      (!p. p <> out ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >>
  qabbrev_tac `v:bytes32 = bool_to_word (m = n2w sel)` >>
  qabbrev_tac `u = update_var out v s` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `reject_prefix_step ctx fn s s1` by
    (qspecl_then [`ctx`,`fn`,`s`,`s1`,`bb`,`mk_inst id EQ [mid; Lit (n2w sel)] [out]`,`u`]
       mp_tac reject_prefix_scalar >>
     simp[Abbr `s1`, Abbr `u`, Abbr `v`, mk_inst_def, reject_prefix_opcode_def,
          is_terminator_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_pure2_def, eval_operand_def]) >>
  `reject_prefix_step ctx fn s1 (jump_to lbl s1)` by
    (qspecl_then [`ctx`,`fn`,`s1`,`lbl`,`bb`,`next_id`,`Var out`,`yes`,`no`,`target`,`v`]
       mp_tac reject_prefix_branch >>
     simp[Abbr `s1`, Abbr `u`, Abbr `v`, update_var_def, eval_operand_def, lookup_var_def,
          FLOOKUP_UPDATE] >>
     Cases_on `m = n2w sel` >> gvs[bool_to_word_def]) >>
  qexists_tac `jump_to lbl s1` >>
  conj_tac >-
    (pure_once_rewrite_tac[RTC_CASES1] >> disj2_tac >> qexists_tac `s1` >> simp[RTC_SINGLE]) >>
  simp[Abbr `s1`, Abbr `u`, jump_to_def, update_var_def, vars_pc_only_def,
       venom_state_component_equality, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem grouped_fallback_dispatch_code[local]:
  run_grouped_lowering groups ints NONE rp "__entry" = SOME u /\
  EVERY group_entry_labels_ok groups /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME fn ==>
  ?fl sf jobs sd sn se.
    compile_group_dispatch_linear groups fl sf = (jobs,sd) /\
    emit_inst REVERT [Lit 0w; Lit 0w] [] sn = ((),se) /\
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    sn.cs_current_bb = fl /\ sn.cs_current_insts = [] /\
    fn_has_code sf sd fn /\ fn_has_code sn se fn
Proof
  strip_tac >> drule_all run_grouped_lowering_dispatch_code >> simp[] >> metis_tac[]
QED

Theorem installed_grouped_short_reject_prefix[local]:
  run_grouped_lowering groups ints NONE rp "__entry" = SOME u /\
  EVERY group_entry_labels_ok groups /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME fn /\
  LENGTH s.vs_call_ctx.cc_calldata < 4 /\ ~s.vs_halted /\
  s.vs_current_bb = "__entry" /\ s.vs_inst_idx = 0 ==>
  ?t. RTC (reject_prefix_step u.cu_context fn) s t /\
      reject_prefix_terminal u.cu_context fn t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all grouped_fallback_dispatch_code >>
  disch_then (qx_choosel_then [`fl`,`sf`,`jobs`,`sd`,`sn`,`se`] strip_assume_tac) >>
  drule_all compile_group_dispatch_linear_layout >>
  disch_then (qx_choosel_then [`d`,`q`,`r`,`b0`,`bd`,`br`] strip_assume_tac) >>
  drule_all installed_empty_revert_code >>
  disch_then (qx_choose_then `fb` strip_assume_tac) >>
  `phi_prefix_length fb.bb_instructions = 0` by
    (Cases_on `fb.bb_instructions` >>
     gvs[get_instruction_def, phi_prefix_length_def, mk_inst_def]) >>
  qabbrev_tac `size_var = STRING #"%" (toString sf.cs_next_var)` >>
  qabbrev_tac `lt_var = STRING #"%" (toString (sf.cs_next_var + 1))` >>
  qabbrev_tac `test_var = STRING #"%" (toString (sf.cs_next_var + 2))` >>
  qabbrev_tac `s1 = (update_var size_var (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s)
    with vs_inst_idx := 1` >>
  qabbrev_tac `s2 = (update_var lt_var 1w s1) with vs_inst_idx := 2` >>
  qabbrev_tac `s3 = (update_var test_var 0w s2) with vs_inst_idx := 3` >>
  `LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)` by simp[dimword_def] >>
  `reject_prefix_step u.cu_context fn s s1` by
    (qspecl_then [`u.cu_context`,`fn`,`s`,`s1`,`b0`,
        `mk_inst sf.cs_next_id CALLDATASIZE [] [size_var]`,
        `update_var size_var (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s`] mp_tac
        reject_prefix_scalar >>
     gvs[Abbr `size_var`, reject_prefix_opcode_def, is_terminator_def, mk_inst_def,
        step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read0_def, Abbr `s1`]) >>
  `reject_prefix_step u.cu_context fn s1 s2` by
    (qspecl_then [`u.cu_context`,`fn`,`s1`,`s2`,`b0`,
        `mk_inst (sf.cs_next_id + 1) LT [Var size_var; Lit 4w] [lt_var]`,
        `update_var lt_var 1w s1`] mp_tac reject_prefix_scalar >>
     gvs[Abbr `s2`, Abbr `s1`, Abbr `size_var`, Abbr `lt_var`, reject_prefix_opcode_def,
        is_terminator_def, mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
        exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def, bool_to_word_def,
        FLOOKUP_UPDATE, dimword_def]) >>
  `reject_prefix_step u.cu_context fn s2 s3` by
    (qspecl_then [`u.cu_context`,`fn`,`s2`,`s3`,`b0`,
        `mk_inst (sf.cs_next_id + 2) ISZERO [Var lt_var] [test_var]`,
        `update_var test_var 0w s2`] mp_tac reject_prefix_scalar >>
     gvs[Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `lt_var`, Abbr `test_var`, reject_prefix_opcode_def,
        is_terminator_def, mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
        exec_pure1_def, eval_operand_def, lookup_var_def, update_var_def, bool_to_word_def,
        FLOOKUP_UPDATE]) >>
  `reject_prefix_step u.cu_context fn s3 (jump_to fl s3)` by
    (qspecl_then [`u.cu_context`,`fn`,`s3`,`fl`,`b0`,`sf.cs_next_id + 3`,
        `Var test_var`,`d`,`fl`,`fb`,`0w`] mp_tac reject_prefix_branch >>
     gvs[Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `test_var`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE]) >>
  qexists_tac `jump_to fl s3` >>
  conj_tac >-
    (MAP_EVERY (fn next =>
       pure_once_rewrite_tac[RTC_CASES1] >> disj2_tac >> qexists_tac next >>
       conj_tac >- first_assum ACCEPT_TAC) [`s1`,`s2`,`s3`] >>
     irule RTC_SINGLE >> first_assum ACCEPT_TAC) >>
  irule installed_empty_revert_terminal >>
  conj_tac >- simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, update_var_def, jump_to_def] >>
  qexistsl_tac [`sn`,`se`] >>
  gvs[jump_to_def]
QED

Theorem installed_grouped_long_dispatch_prefix[local]:
  compile_group_dispatch_linear groups fl sf = (jobs,sd) /\
  fn_has_code sf sd fn /\ EVERY group_entry_labels_ok groups /\
  4 <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  fresh_vars_wrt sf s /\ ~s.vs_halted /\
  s.vs_current_bb = sf.cs_current_bb /\ s.vs_inst_idx = LENGTH sf.cs_current_insts ==>
  ?q r t.
    compile_external_groups (Var (STRING #"%" (toString (sf.cs_next_var + 4))))
      groups q = (jobs,r) /\ fn_has_code q r fn /\ cs_extends r sd /\
    r.cs_next_var <= sd.cs_next_var /\
    RTC (reject_prefix_step u.cu_context fn) s t /\ vars_pc_only s t /\
    t.vs_current_bb = q.cs_current_bb /\ t.vs_inst_idx = LENGTH q.cs_current_insts /\
    fresh_vars_wrt q t /\
    eval_operand (Var (STRING #"%" (toString (sf.cs_next_var + 4)))) t =
      SOME (calldata_method_id s.vs_call_ctx.cc_calldata) /\
    (?br. lookup_block r.cs_current_bb fn.fn_blocks = SOME br /\
      get_instruction br (LENGTH r.cs_current_insts) =
        SOME (mk_inst r.cs_next_id JMP [Label fl] []))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all compile_group_dispatch_linear_layout >>
  disch_then (qx_choosel_then [`d`,`q`,`r`,`b0`,`bd`,`br`] strip_assume_tac) >>
  qabbrev_tac `size_var = STRING #"%" (toString sf.cs_next_var)` >>
  qabbrev_tac `lt_var = STRING #"%" (toString (sf.cs_next_var + 1))` >>
  qabbrev_tac `test_var = STRING #"%" (toString (sf.cs_next_var + 2))` >>
  qabbrev_tac `s1 = (update_var size_var (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s)
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `s2 = (update_var lt_var 0w s1) with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `s3 = (update_var test_var 1w s2) with vs_inst_idx := SUC s2.vs_inst_idx` >>
  `LENGTH s.vs_call_ctx.cc_calldata MOD dimword (:256) = LENGTH s.vs_call_ctx.cc_calldata` by
    metis_tac[LESS_MOD] >>
  `reject_prefix_step u.cu_context fn s s1` by
    (qspecl_then [`u.cu_context`,`fn`,`s`,`s1`,`b0`,
        `mk_inst sf.cs_next_id CALLDATASIZE [] [size_var]`,
        `update_var size_var (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s`] mp_tac
        reject_prefix_scalar >>
     gvs[Abbr `size_var`, reject_prefix_opcode_def, is_terminator_def, mk_inst_def,
        step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read0_def, Abbr `s1`]) >>
  `reject_prefix_step u.cu_context fn s1 s2` by
    (qspecl_then [`u.cu_context`,`fn`,`s1`,`s2`,`b0`,
        `mk_inst (sf.cs_next_id + 1) LT [Var size_var; Lit 4w] [lt_var]`,
        `update_var lt_var 0w s1`] mp_tac reject_prefix_scalar >>
     gvs[Abbr `s2`, Abbr `s1`, Abbr `size_var`, Abbr `lt_var`, reject_prefix_opcode_def,
        is_terminator_def, mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
        exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def, bool_to_word_def,
        FLOOKUP_UPDATE, WORD_LO, w2n_n2w]) >>
  `reject_prefix_step u.cu_context fn s2 s3` by
    (qspecl_then [`u.cu_context`,`fn`,`s2`,`s3`,`b0`,
        `mk_inst (sf.cs_next_id + 2) ISZERO [Var lt_var] [test_var]`,
        `update_var test_var 1w s2`] mp_tac reject_prefix_scalar >>
     gvs[Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `lt_var`, Abbr `test_var`, reject_prefix_opcode_def,
        is_terminator_def, mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
        exec_pure1_def, eval_operand_def, lookup_var_def, update_var_def, bool_to_word_def,
        FLOOKUP_UPDATE]) >>
  qabbrev_tac `s4 = jump_to d s3` >>
  `reject_prefix_step u.cu_context fn s3 s4` by
    (qspecl_then [`u.cu_context`,`fn`,`s3`,`d`,`b0`,`sf.cs_next_id + 3`,
        `Var test_var`,`d`,`fl`,`bd`,`1w`] mp_tac reject_prefix_branch >>
     gvs[Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `test_var`,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qabbrev_tac `load_var = STRING #"%" (toString (sf.cs_next_var + 3))` >>
  qabbrev_tac `method_var = STRING #"%" (toString (sf.cs_next_var + 4))` >>
  qabbrev_tac `w = word_of_bytes T (0w:bytes32)
       (TAKE 32 (s.vs_call_ctx.cc_calldata ++ REPLICATE 32 0w))` >>
  qabbrev_tac `s5 = (update_var load_var w s4) with vs_inst_idx := 1` >>
  qabbrev_tac `s6 = (update_var method_var (calldata_method_id s.vs_call_ctx.cc_calldata) s5)
                    with vs_inst_idx := 2` >>
  `s4.vs_current_bb = d /\ s4.vs_inst_idx = 0 /\ ~s4.vs_halted /\
   s4.vs_call_ctx = s.vs_call_ctx` by
    simp[Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`, jump_to_def, update_var_def] >>
  `reject_prefix_step u.cu_context fn s4 s5` by
    (qspecl_then [`u.cu_context`,`fn`,`s4`,`s5`,`bd`,
        `mk_inst (sf.cs_next_id + 4) CALLDATALOAD [Lit 0w] [load_var]`,
        `update_var load_var w s4`] mp_tac reject_prefix_scalar >>
     gvs[Abbr `s5`, Abbr `w`, Abbr `load_var`, reject_prefix_opcode_def,
       is_terminator_def, mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_read1_def, eval_operand_def]) >>
  `w >>> 224 = calldata_method_id s.vs_call_ctx.cc_calldata` by
    simp[Abbr `w`, calldataload_0_shr_224] >>
  `reject_prefix_step u.cu_context fn s5 s6` by
    (qspecl_then [`u.cu_context`,`fn`,`s5`,`s6`,`bd`,
        `mk_inst (sf.cs_next_id + 5) SHR [Lit 224w; Var load_var] [method_var]`,
        `update_var method_var (calldata_method_id s.vs_call_ctx.cc_calldata) s5`]
       mp_tac reject_prefix_scalar >>
     gvs[Abbr `s6`, Abbr `s5`, Abbr `load_var`, Abbr `method_var`,
       reject_prefix_opcode_def, is_terminator_def, mk_inst_def, step_inst_non_invoke,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, dimword_def]) >>
  `RTC (reject_prefix_step u.cu_context fn) s s6` by
    (MAP_EVERY (fn next =>
       pure_once_rewrite_tac[RTC_CASES1] >> disj2_tac >> qexists_tac next >>
       conj_tac >- first_assum ACCEPT_TAC) [`s1`,`s2`,`s3`,`s4`,`s5`] >>
     irule RTC_SINGLE >> first_assum ACCEPT_TAC) >>
  `vars_pc_only s s6` by
    simp[Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
         vars_pc_only_def, update_var_def, jump_to_def, venom_state_component_equality] >>
  `s6.vs_current_bb = q.cs_current_bb /\ s6.vs_inst_idx = LENGTH q.cs_current_insts` by
    simp[Abbr `s6`, Abbr `s5`, update_var_def] >>
  `fresh_vars_wrt q s6` by
    (fs[Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
       Abbr `method_var`, Abbr `load_var`, Abbr `test_var`, Abbr `lt_var`, Abbr `size_var`,
       fresh_vars_wrt_def, jump_to_def, update_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> simp[]) >>
  qexistsl_tac [`q`,`r`,`s6`] >>
  simp[Abbr `s6`, Abbr `method_var`, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE]
QED

fun preserve_dispatch_no_revert ths =
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac,
    CHANGED_TAC (simp (ths @ [opcode_every_emit_inst, opcode_every_emit_op,
      every_state_insts_return, every_state_insts_fresh_label, every_state_insts_new_block]))
  ]);

Theorem selector_checks_no_revert[local]:
  !sels mid st. EVERY (\i. i.inst_opcode <> REVERT) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> REVERT) (state_insts (SND (compile_selector_checks mid sels st)))
Proof
  Induct >> simp[compile_selector_checks_def, every_state_insts_return] >>
  qx_gen_tac `sel` >> PairCases_on `sel` >>
  simp[compile_selector_checks_def] >> preserve_dispatch_no_revert []
QED

Theorem selector_dispatch_no_revert[local]:
  !st. EVERY (\i. i.inst_opcode <> REVERT) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> REVERT)
      (state_insts (SND (compile_selector_dispatch_linear sels fb st)))
Proof
  simp[compile_selector_dispatch_linear_def] >>
  preserve_dispatch_no_revert [selector_checks_no_revert]
QED

Theorem legacy_fallback_dispatch_code[local]:
  run_lowering sels exts ints NONE rp bc mb db ei "__entry" = SOME u /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,ss,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME fn ==>
  ?fl sf sd sn se.
    fresh_label "fallback" (initial_compile_state "__entry") = (fl,sf) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels) fl sf = ((),sd) /\
    emit_inst REVERT [Lit 0w; Lit 0w] [] sn = ((),se) /\
    sf.cs_blocks = [] /\ sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    sn.cs_current_bb = fl /\ sn.cs_current_insts = [] /\
    fn_has_code sf sd fn /\ fn_has_code sn se fn /\
    lookup_block sd.cs_current_bb fn.fn_blocks =
      SOME <|bb_label := sd.cs_current_bb; bb_instructions := sd.cs_current_insts|>
Proof
  strip_tac >> drule_all run_lowering_retained_entry >>
  disch_then (qx_choose_then `se` strip_assume_tac) >>
  Cases_on `fresh_label "fallback" (initial_compile_state "__entry")` >>
  rename1 `fresh_label "fallback" _ = (fl,sf)` >>
  Cases_on `compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels) fl sf` >>
  rename1 `compile_selector_dispatch_linear _ fl sf = (_,sd)` >>
  Cases_on `compile_external_fn_bodies exts sd` >>
  rename1 `compile_external_fn_bodies exts sd = (_,sx)` >>
  Cases_on `new_block fl sx` >>
  rename1 `new_block fl sx = (prev,sn)` >>
  Cases_on `emit_inst REVERT [Lit 0w; Lit 0w] [] sn` >>
  qpat_x_assum `compile_generate_runtime _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_generate_runtime_def, comp_bind_def, comp_ignore_bind_def,
       compile_internal_fn_bodies_def, comp_return_def] >>
  strip_tac >> gvs[oneTheory.one] >>
  rename1 `emit_inst REVERT [Lit 0w; Lit 0w] [] sn = ((),se)` >>
  `cs_extends sf sd /\ cs_extends sd sx /\ cs_extends sx sn /\ cs_extends sn se` by
    (drule (SRULE [cs_appends_def] cs_appends_selector_dispatch_linear) >> strip_tac >>
     drule (SRULE [cs_appends_def] cs_appends_external_fn_bodies) >> strip_tac >>
     metis_tac[cs_extends_new_block, cs_extends_emit_inst]) >>
  `MEM <|bb_label := sd.cs_current_bb; bb_instructions := sd.cs_current_insts|>
     (all_blocks se)` by
    (Cases_on `exts = []`
     >- (gvs[compile_external_fn_bodies_def, comp_return_def] >>
         metis_tac[finalized_block_in_later_state]) >>
     drule_all external_bodies_start_block >>
     metis_tac[finalized_block_in_later_state, cs_extends_trans]) >>
  `sf.cs_blocks = [] /\ sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = []` by
    (`sf = SND (fresh_label "fallback" (initial_compile_state "__entry"))` by
       metis_tac[pairTheory.SND] >>
     pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[fresh_label_def, initial_compile_state_def]) >>
  `sn.cs_current_bb = fl /\ sn.cs_current_insts = []` by
    metis_tac[new_block_props] >>
  `fn_has_code sf sd fn /\ fn_has_code sn se fn` by
    metis_tac[fn_has_code_retained_interval, cs_extends_trans, cs_extends_refl] >>
  qexistsl_tac [`sd`,`sn`,`se`] >>
  simp[] >>
  qpat_assum `!bb. MEM bb (all_blocks se) ==> _`
    (qspec_then `<|bb_label := sd.cs_current_bb; bb_instructions := sd.cs_current_insts|>`
      (fn th => qpat_assum `MEM _ (all_blocks se)`
        (ACCEPT_TAC o SIMP_RULE (srw_ss()) [] o MATCH_MP th)))
QED

Theorem legacy_selected_dispatch_code[local]:
  run_lowering sels exts ints fb rp bc mb db ei "__entry" = SOME u /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,ss,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME fn /\
  exts <> [] ==>
  ?fl sf sd.
    fresh_label "fallback" (initial_compile_state "__entry") = (fl,sf) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels) fl sf = ((),sd) /\
    sf.cs_blocks = [] /\ sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    fn_has_code sf sd fn /\
    lookup_block sd.cs_current_bb fn.fn_blocks =
      SOME <|bb_label := sd.cs_current_bb; bb_instructions := sd.cs_current_insts|> /\
    (!l. l IN bound_labels sd ==> ~isPREFIX "fn_" l)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all run_lowering_retained_entry >>
  disch_then (qx_choose_then `se` strip_assume_tac) >>
  Cases_on `fresh_label "fallback" (initial_compile_state "__entry")` >>
  rename1 `fresh_label "fallback" _ = (fl,sf)` >>
  Cases_on `compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels) fl sf` >>
  rename1 `compile_selector_dispatch_linear _ fl sf = (_,sd)` >>
  Cases_on `compile_external_fn_bodies exts sd` >>
  rename1 `compile_external_fn_bodies exts sd = (_,sx)` >>
  Cases_on `new_block fl sx` >>
  rename1 `new_block fl sx = (prev,sn)` >>
  qpat_x_assum `compile_generate_runtime _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_generate_runtime_def, comp_bind_def, comp_ignore_bind_def,
       compile_internal_fn_bodies_def, comp_return_def, Excl "isPREFIX"] >>
  strip_tac >> gvs[oneTheory.one, Excl "isPREFIX"] >>
  `cs_extends sx se` by
    (mp_tac (Q.INST [`lbl` |-> `fl`] cs_appends_runtime_fallback_suffix) >>
     simp[cs_appends_def] >>
     disch_then (qspecl_then [`sx`,`se`] mp_tac) >>
     simp[comp_ignore_bind_def, comp_bind_def] >>
     Cases_on `(case fb of NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
       | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
         compile_fallback_body ce pay nr key tr view stmts rt) sn` >>
     gvs[oneTheory.one]) >>
  `cs_extends sf sd /\ cs_extends sd sx` by
    metis_tac[cs_appends_selector_dispatch_linear, cs_appends_external_fn_bodies,
      cs_appends_def] >>
  drule_all external_bodies_start_block >> strip_tac >>
  `MEM <|bb_label := sd.cs_current_bb; bb_instructions := sd.cs_current_insts|>
       (all_blocks se)` by
    metis_tac[finalized_block_in_later_state, cs_extends_trans] >>
  `sf.cs_blocks = [] /\ sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = []` by
    (`sf = SND (fresh_label "fallback" (initial_compile_state "__entry"))` by
       metis_tac[pairTheory.SND] >>
     pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[fresh_label_def, initial_compile_state_def]) >>
  `!l. l IN bound_labels sf ==> ~isPREFIX "fn_" l` by simp[bound_labels_def] >>
  qpat_assum `compile_selector_dispatch_linear _ _ _ = _` (fn dispatch =>
    qpat_assum `!l. l IN bound_labels sf ==> _` (fn labels =>
      assume_tac (MATCH_MP (SPEC_ALL compile_selector_dispatch_linear_no_fn_labels)
        (CONJ dispatch labels)))) >>
  `fn_has_code sf sd fn` by
    metis_tac[fn_has_code_retained_interval, cs_extends_trans] >>
  asm_rewrite_tac[] >>
  qpat_assum `!bb. MEM bb (all_blocks se) ==> _`
    (qspec_then `<|bb_label := sd.cs_current_bb; bb_instructions := sd.cs_current_insts|>`
      (fn th => qpat_assum `MEM _ (all_blocks se)`
        (ACCEPT_TAC o SIMP_RULE (srw_ss()) [] o MATCH_MP th)))
QED

Theorem installed_legacy_named_selector_prefix[local]:
  run_lowering sels exts ints fb rp bc mb db ei "__entry" = SOME u /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,ss,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME fn /\ exts <> [] /\
  EVERY (\(sel,lbl). sel < 2 ** 32) (MAP (\(sel,lbl,z). (sel,lbl)) sels) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  (!st. fresh_vars_wrt st s) /\ ~s.vs_halted /\ s.vs_current_bb = "__entry" /\ s.vs_inst_idx = 0 /\
  (!fl. linear_dispatch_target s.vs_call_ctx.cc_calldata
    (MAP (\(sel,lbl,z). (sel,lbl)) sels) fl = "fn_" ++ name) /\
  lookup_block ("fn_" ++ name) fn.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions = 0 ==>
  ?fl sf sd t.
    fresh_label "fallback" (initial_compile_state "__entry") = (fl,sf) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels) fl sf = ((),sd) /\
    RTC (reject_prefix_step u.cu_context fn) s t /\ ~t.vs_halted /\
    t.vs_call_ctx = s.vs_call_ctx /\ fresh_vars_wrt sd t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_current_bb = "fn_" ++ name /\ t.vs_inst_idx = 0
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all legacy_selected_dispatch_code >>
  disch_then (qx_choosel_then [`fl`,`sf`,`sd`] strip_assume_tac) >>
  Cases_on `new_block ("fn_" ++ name) sd` >>
  rename1 `new_block _ sd = (prev,cut)` >>
  drule new_block_props >> strip_tac >>
  `cs_extends sf sd` by metis_tac[cs_appends_selector_dispatch_linear, cs_appends_def] >>
  `fn_has_code sf cut fn` by metis_tac[installed_dispatch_cut_code] >>
  `~MEM cut.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sf cut))` by
    (`!b. MEM b cut.cs_blocks ==> b.bb_label IN bound_labels sd` by
       (simp[bound_labels_def, MEM_MAP] >> gen_tac >> disch_then DISJ_CASES_TAC
        >- gvs[] >>
        disj2_tac >> qexists_tac `b` >> simp[]) >>
     `!b. MEM b (emitted_blocks sf cut) ==> MEM b cut.cs_blocks` by
       (simp_tac bool_ss [emitted_blocks_def] >> metis_tac[MEM_TAKE]) >>
     `~("fn_" ++ name IN bound_labels sd)` by
       (qpat_assum `!l. l IN bound_labels sd ==> _`
          (qspec_then `"fn_" ++ name` mp_tac) >>
        simp_tac bool_ss [rich_listTheory.IS_PREFIX_APPEND3]) >>
     simp_tac bool_ss [MEM_MAP] >> qx_gen_tac `b` >> rpt strip_tac >>
     `b.bb_label IN bound_labels sd` by metis_tac[] >>
     metis_tac[]) >>
  `!b. lookup_block cut.cs_current_bb fn.fn_blocks = SOME b ==>
        phi_prefix_length b.bb_instructions = 0` by
    (rpt strip_tac >> gvs[]) >>
  `EVERY reject_prefix_opcode (state_insts sf)` by
    simp[state_insts_def, all_blocks_def] >>
  `new_block (linear_dispatch_target s.vs_call_ctx.cc_calldata
       (MAP (\(sel,lbl,z). (sel,lbl)) sels) fl) sd = (prev,cut)` by asm_rewrite_tac[] >>
  `fresh_vars_wrt sf s /\ s.vs_current_bb = sf.cs_current_bb /\
    s.vs_inst_idx = LENGTH sf.cs_current_insts` by simp[] >>
  drule_at (Pat `compile_selector_dispatch_linear _ _ _ = _`) installed_legacy_selector_prefix >>
  disch_then (drule_at (Pat `new_block (linear_dispatch_target _ _ _) _ = _`)) >>
  disch_then (qspecl_then [`fn`,`u.cu_context`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`fl`,`sf`,`sd`,`t`] >> simp[]
QED

Theorem installed_legacy_fallback_reject_prefix[local]:
  run_lowering sels exts ints NONE rp bc mb db ei "__entry" = SOME u /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,ss,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME fn /\
  EVERY (\(sel,lbl). sel < 2 ** 32) (MAP (\(sel,lbl,z). (sel,lbl)) sels) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  (!st. fresh_vars_wrt st s) /\ ~s.vs_halted /\
  s.vs_current_bb = "__entry" /\ s.vs_inst_idx = 0 /\
  (!fl. linear_dispatch_target s.vs_call_ctx.cc_calldata
       (MAP (\(sel,lbl,z). (sel,lbl)) sels) fl = fl) ==>
  ?t. RTC (reject_prefix_step u.cu_context fn) s t /\
      reject_prefix_terminal u.cu_context fn t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all legacy_fallback_dispatch_code >>
  disch_then (qx_choosel_then [`fl`,`sf`,`sd`,`sn`,`se`] strip_assume_tac) >>
  drule_all installed_empty_revert_code >> strip_tac >>
  `lookup_block fl fn.fn_blocks = SOME bb /\
   get_instruction bb 0 = SOME (mk_inst sn.cs_next_id REVERT [Lit 0w; Lit 0w] [])` by
    (qpat_assum `lookup_block sn.cs_current_bb fn.fn_blocks = SOME bb` mp_tac >>
     qpat_assum `get_instruction bb (LENGTH sn.cs_current_insts) = _` mp_tac >>
     qpat_assum `sn.cs_current_bb = fl` (fn lbl =>
       qpat_assum `sn.cs_current_insts = []` (fn empty =>
         simp[NoAsms, lbl, empty]))) >>
  Cases_on `new_block fl sd` >>
  rename1 `new_block fl sd = (prev,cut)` >>
  drule new_block_props >> strip_tac >>
  `cs_extends sf sd` by
    metis_tac[cs_appends_selector_dispatch_linear, cs_appends_def] >>
  `fn_has_code sf cut fn` by
    metis_tac[installed_dispatch_cut_code] >>
  `EVERY reject_prefix_opcode (state_insts sf)` by
    simp[state_insts_def, all_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> REVERT) (state_insts sd)` by
    (`EVERY (\i. i.inst_opcode <> REVERT) (state_insts sf)` by
       simp[state_insts_def, all_blocks_def] >>
     metis_tac[selector_dispatch_no_revert, pairTheory.SND]) >>
  `state_insts cut = state_insts sd` by
    simp[state_insts_def, all_blocks_def, REVERSE_DEF] >>
  `EVERY (\i. i.inst_opcode <> REVERT) (state_insts cut)` by simp[] >>
  `~MEM cut.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sf cut))` by
    (irule (Q.INST [`P` |-> `\i. i.inst_opcode <> REVERT`]
              installed_cut_unshadowed) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`bb`,`fn`,`mk_inst sn.cs_next_id REVERT [Lit 0w; Lit 0w] []`] >>
     simp[mk_inst_def]) >>
  `!target. lookup_block cut.cs_current_bb fn.fn_blocks = SOME target ==>
            phi_prefix_length target.bb_instructions = 0` by
    (rpt strip_tac >> gvs[] >>
     Cases_on `bb.bb_instructions` >>
     gvs[get_instruction_def, phi_prefix_length_def, mk_inst_def]) >>
  `new_block (linear_dispatch_target s.vs_call_ctx.cc_calldata
       (MAP (\(sel,lbl,z). (sel,lbl)) sels) fl) sd = (prev,cut)` by asm_rewrite_tac[] >>
  `fresh_vars_wrt sf s` by simp[] >>
  `s.vs_current_bb = sf.cs_current_bb /\ s.vs_inst_idx = LENGTH sf.cs_current_insts` by simp[] >>
  drule_at (Pat `compile_selector_dispatch_linear _ _ _ = _`) installed_legacy_selector_prefix >>
  disch_then (drule_at (Pat `new_block (linear_dispatch_target _ _ _) _ = _`)) >>
  disch_then (qspecl_then [`fn`,`u.cu_context`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule installed_empty_revert_terminal >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`sn`,`se`] >>
  qpat_assum `sn.cs_current_bb = fl` (fn lbl =>
    qpat_assum `sn.cs_current_insts = []` (fn empty =>
      asm_rewrite_tac [lbl, empty])) >> simp[]
QED

Theorem safe_observer_reject_in_context[local]:
  prefix_code_agrees observer fn cut /\
  EVERY reject_prefix_opcode (fn_insts observer) /\
  (!t fuel v. (t.vs_current_bb,t.vs_inst_idx) = cut ==>
    run_from fuel observer_ctx observer t <> Abort Revert_abort v) /\
  ~s.vs_halted /\ run_from fuel observer_ctx observer s = Abort Revert_abort v ==>
  ?t. RTC (reject_prefix_step ctx fn) s t /\ reject_prefix_terminal ctx fn t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `observer_region_closed observer_ctx observer cut UNIV` by
    simp[observer_region_closed_def] >>
  `!t bb i. lookup_block t.vs_current_bb observer.fn_blocks = SOME bb /\
     get_instruction bb t.vs_inst_idx = SOME i ==> i.inst_opcode <> INVOKE` by
    metis_tac[safe_observer_instruction, reject_prefix_opcode_def] >>
  drule abi_decode_reject_endpoint >>
  disch_then (qspecl_then [`v`,`s`,`fuel`] mp_tac) >>
  simp[] >> impl_tac >- metis_tac[] >> strip_tac >>
  qexists_tac `u` >> conj_tac
  >- (irule safe_observer_path_in_context >> qexistsl_tac [`cut`,`observer`,`observer_ctx`] >>
      simp[]) >>
  qpat_x_assum `prefix_code_agrees observer fn cut`
    (strip_assume_tac o REWRITE_RULE [prefix_code_agrees_def]) >>
  `?bb'. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb' /\
          get_instruction bb' u.vs_inst_idx = SOME inst` by metis_tac[] >>
  simp[reject_prefix_terminal_def] >> qexists_tac `inst` >>
  simp[step_inst_non_invoke] >>
  metis_tac[lookup_instruction_active, safe_observer_instruction]
QED

Theorem distinct_list_weight[local]:
  !xs. ALL_DISTINCT xs ==> SUM_IMAGE f (set xs) = SUM (MAP f xs)
Proof
  Induct >> simp[SUM_IMAGE_THM, DELETE_NON_ELEMENT_RWT]
QED

Theorem observed_alloca_budget[local]:
  fn_inst_ids_distinct observer /\
  (!i. MEM i (fn_insts observer) /\ i.inst_opcode = ALLOCA ==>
    MEM i (fn_insts fn)) /\
  MEM fn ctx.ctx_functions ==>
  SUM (MAP alloca_size
    (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts observer))) <= unit_alloca_budget ctx
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_insts observer)` by
    metis_tac[fn_inst_ids_distinct_all_distinct, ALL_DISTINCT_MAP] >>
  `set (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts observer)) SUBSET
   set (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts fn))` by
    simp[SUBSET_DEF, MEM_FILTER] >>
  `SUM_IMAGE alloca_size (set (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts observer))) <=
   SUM_IMAGE alloca_size (set (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts fn)))` by
    (irule SUM_IMAGE_SUBSET_LE >> simp[]) >>
  `SUM_IMAGE alloca_size (set (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts fn))) <=
   SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts fn)))` by
    irule SUM_IMAGE_LIST_TO_SET_upper_bound >>
  drule static_alloca_function_le >> strip_tac >>
  `ALL_DISTINCT (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts observer))` by
    metis_tac[FILTER_ALL_DISTINCT] >>
  FULL_SIMP_TAC std_ss [distinct_list_weight] >>
  simp[unit_alloca_budget_def, RIGHT_ADD_DISTRIB] >> decide_tac
QED

(* Preserve the checked decoder's frontier premise when observing it in
   isolation. The second function is uncalled and contributes only to the
   conservative, unit-wide static budget. *)
Theorem reject_decoder_observer_context[local]:
  EVERY reject_prefix_opcode (fn_insts observer) /\
  SUM (MAP alloca_size
    (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts observer))) < 2 ** 255 /\
  s.vs_alloca_next + remaining_alloca_budget (fn_insts observer) s <= 2 ** 255 ==>
  ?observer_ctx. unit_alloca_budget observer_ctx < dimword (:256) /\
    ~ctx_has_dalloca observer_ctx /\
    alloca_frontier_inv observer_ctx observer site s
Proof
  strip_tac >>
  qabbrev_tac `pad = mk_raw_function (observer.fn_name ++ "x")
    [<|bb_label := "padding"; bb_instructions :=
      [mk_inst 0 ALLOCA [Lit (n2w (2 ** 255))] []]|>]` >>
  qabbrev_tac `local_ctx = ctx with ctx_functions := [observer;pad]` >>
  `fn_insts pad = [mk_inst 0 ALLOCA [Lit (n2w (2 ** 255))] []]` by
    simp[Abbr `pad`, fn_insts_def, fn_insts_blocks_def, mk_raw_function_def] >>
  `FILTER (\i. i.inst_opcode = INVOKE) (fn_insts observer) = []` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM, reject_prefix_opcode_def] >> metis_tac[]) >>
  `unit_alloca_budget local_ctx =
     SUM (MAP alloca_size
       (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts observer))) + 2 ** 255` by
    simp[Abbr `local_ctx`, unit_alloca_budget_def,
      FILTER_APPEND, SUM_APPEND, mk_inst_def, alloca_size_def, dimword_def] >>
  `!q. ~fn_directly_calls local_ctx observer.fn_name q` by
    (simp[Abbr `local_ctx`, fn_directly_calls_def, lookup_function_def, FIND_thm] >>
     fs[EVERY_MEM, reject_prefix_opcode_def] >> metis_tac[]) >>
  `!g. ~TC (fn_directly_calls local_ctx) observer.fn_name g` by
    metis_tac[TC_CASES1] >>
  `{g | TC (fn_directly_calls local_ctx) observer.fn_name g} = {}` by
    simp[EXTENSION] >>
  qexists_tac `local_ctx` >> rpt conj_tac
  >- (fs[dimword_def] >> decide_tac)
  >- (simp[Abbr `local_ctx`, ctx_has_dalloca_def, mk_inst_def] >>
      fs[EVERY_MEM, reject_prefix_opcode_def, EXISTS_MEM] >> metis_tac[]) >>
  simp[alloca_frontier_inv_def, lookup_function_def, FIND_thm] >>
  conj_tac >- simp[Abbr `local_ctx`, FIND_thm] >>
  irule LESS_EQ_TRANS >> qexists_tac `2 ** 255` >>
  simp[arithmeticTheory.LESS_EQ_ADD, Once ADD_COMM]
QED

Theorem coherent_registration_reject_path:
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) tv.
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs /\
  compile_register_positional_args ce (build_positional_args ce args) 4 sa = (cef,sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  (!bb lbl. lookup_block lbl fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  calldata_decode_args s.vs_call_ctx.cc_calldata tvs 0 = NONE /\
  unit_alloca_budget ctx < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  (!id e. FLOOKUP s.vs_allocas id = SOME e ==> id < sa.cs_next_id) /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
      (s,G,tn) [] (Abort Revert_abort z,H,u)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `R = \st v (K:(string,num # num) fmap) (w:taint).
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp v /\
      v.vs_alloca_next + pending_alloca_size fn v <= w2n v.vs_initial_fmp) /\
    (!id e. FLOOKUP v.vs_allocas id = SOME e ==> id < st.cs_next_id) /\
    fresh_vars_wrt st v /\ ~v.vs_halted /\ v.vs_current_bb = st.cs_current_bb /\
    v.vs_inst_idx = LENGTH st.cs_current_insts` >>
  `R sa s G tn` by simp[Abbr `R`] >>
  mp_tac (Q.INST [`ctx` |-> `ctx`, `fn` |-> `fn`, `env` |-> `env`,
                  `cd` |-> `s.vs_call_ctx.cc_calldata`, `R` |-> `R`]
    none_registration_suffix_reject) >>
  impl_tac
  >- (ntac 8 gen_tac >> map_every qx_gen_tac [`s0`,`G0`,`tn0`] >>
      qunabbrev_tac `R` >> BETA_TAC >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      suspend "singleton") >>
  disch_then (drule_at (Pat `R _ _ _ _`)) >>
  disch_then (drule_at (Pat `calldata_decode_args _ _ _ = NONE`)) >>
  disch_then (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`) o
    REWRITE_RULE [ADD_CLAUSES]) >>
  simp[] >> decide_tac
QED

Resume coherent_registration_reject_path[singleton]:
  drule fn_inst_ids_distinct_all_distinct >> strip_tac >>
  rename1 `abi_decoder_coherent c env _ ty tv` >>
  rename1 `compile_register_positional_args c [build_positional_arg c (name,ty)] _ st = (c1,last)` >>
  qpat_x_assum `?loc. FLOOKUP c.ce_vars _ = SOME loc /\ _`
    (qx_choose_then `loc` strip_assume_tac) >>
  mp_tac (Q.INST [`ce` |-> `c`, `ce1` |-> `c1`, `env` |-> `env`, `ty` |-> `ty`,
    `tv` |-> `tv`, `name` |-> `name`, `loc` |-> `loc`, `ofs` |-> `ofs`,
    `st` |-> `st`, `last` |-> `last`, `fn` |-> `fn`, `s` |-> `s0`,
    `cd` |-> `s.vs_call_ctx.cc_calldata`, `ctx` |-> `ctx`, `site` |-> `site`,
    `G` |-> `G0`, `tn` |-> `tn0`] none_registration_singleton_paths) >>
  impl_tac
  >- (simp[] >>
      map_every qx_gen_tac [`first`,`t`,`src`,`q`,`p`,`d`,`oid`,`H`,`u`] >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      qpat_assum `abi_decoder_coherent c env _ ty tv`
        (mp_tac o MATCH_MP (BETA_RULE none_coherent_decode_paths)) >>
      disch_then (qspecl_then
        [`first`,`last`,`last`,`ctx`,`fn`,`site`,`src`,`q`,`t`,`p`,`d`,`oid`,`d`,
         `type_memory_size tv`,`H`,`u`,`0`,`[]`] mp_tac) >>
      impl_tac
      >- (simp[allocas_from_def] >> conj_tac
          >- (disj2_tac >> qx_gen_tac `bb` >> strip_tac >>
              qpat_assum `!bb lbl. lookup_block lbl _ = SOME bb ==> _`
                (qspecl_then [`bb`,`last.cs_current_bb`] mp_tac) >> simp[]) >>
          rpt strip_tac >>
          qpat_assum `!key. first.cs_next_id <= key ==> _`
            (drule_then (fs o single))) >>
      disch_then DISJ_CASES_TAC
      >- (pop_assum (qx_choosel_then [`z`,`Gout`,`w`] strip_assume_tac) >>
          disj1_tac >> qexistsl_tac [`z`,`Gout`,`w`] >> asm_rewrite_tac[]) >>
      pop_assum (qx_choosel_then [`v`,`sc`,`Gout`,`w`] strip_assume_tac) >>
      disj2_tac >> qexistsl_tac [`v`,`Gout`,`w`] >> simp[]) >>
  simp[GSYM CONJ_ASSOC]
QED
Finalise coherent_registration_reject_path

Theorem installed_registration_reject_prefix[local]:
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) tv.
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs /\
  compile_register_positional_args ce (build_positional_args ce args) 4 sa = (cef,sb) /\
  cs_extends sa sb /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  sa.cs_current_bb NOTIN decode_label_range sa.cs_next_label sb.cs_next_label /\
  EVERY reject_prefix_opcode sa.cs_current_insts /\
  (!bb lbl. lookup_block lbl fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  MEM fn ctx.ctx_functions /\ unit_alloca_budget ctx < 2 ** 254 /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  calldata_decode_args s.vs_call_ctx.cc_calldata tvs 0 = NONE /\
  alloca_inv s /\ s.vs_alloca_next <= unit_alloca_budget ctx /\
  (!id e. FLOOKUP s.vs_allocas id = SOME e ==> id < sa.cs_next_id) /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. RTC (reject_prefix_step ctx fn) s z /\ reject_prefix_terminal ctx fn z
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule registration_reject_prefix_code >> strip_tac >>
  drule_all registration_fragment_layout >> strip_tac >>
  mp_tac (Q.INST [`fn` |-> `fn`] frag_observer_fresh_id) >> strip_tac >>
  drule_all frag_observer_ids_distinct_from_labels >> strip_tac >>
  `!bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  qabbrev_tac `observer = frag_observer sa sb fn id` >>
  `fn_has_code sa sb observer /\ EVERY reject_prefix_opcode (fn_insts observer) /\
   prefix_code_agrees observer fn (frag_observer_cut sb)` by
    (simp[Abbr `observer`] >> rpt conj_tac
     >- (irule reject_observer_has_code >> simp[])
     >- (irule reject_observer_code >> simp[]) >>
     irule reject_observer_prefix_code >> simp[]) >>
  `!bb lbl. lookup_block lbl observer.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `prefix_code_agrees observer fn _`
       (strip_assume_tac o REWRITE_RULE [prefix_code_agrees_def]) >>
     map_every qx_gen_tac [`bb`,`lbl`] >> strip_tac >>
     qpat_assum `lookup_block lbl observer.fn_blocks = SOME bb` (fn found =>
       qpat_assum `!lbl bb. lookup_block lbl observer.fn_blocks = SOME bb ==> _`
         (qx_choose_then `bb'` strip_assume_tac o C MATCH_MP found o Q.SPECL [`lbl`,`bb`])) >>
     qpat_assum `!bb lbl. lookup_block lbl fn.fn_blocks = SOME bb ==> _`
       (qspecl_then [`bb'`,`lbl`] mp_tac) >> simp[]) >>
  `SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts observer))) <=
   unit_alloca_budget ctx` by
    (irule observed_alloca_budget >> simp[] >> qexists_tac `fn` >> simp[] >>
     simp[Abbr `observer`] >> rpt strip_tac >>
     irule frag_observer_nonstop_inclusion >> simp[] >> qexistsl_tac [`id`,`sa`,`sb`] >>
     simp[]) >>
  `remaining_alloca_budget (fn_insts observer) s <= unit_alloca_budget ctx` by
    (irule LESS_EQ_TRANS >> goal_assum (drule_at Any) >>
     irule remaining_alloca_budget_le) >>
  `SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts observer))) < 2 ** 255 /\
   s.vs_alloca_next + remaining_alloca_budget (fn_insts observer) s <= 2 ** 255` by
    (fs[] >> decide_tac) >>
  drule_all reject_decoder_observer_context >>
  disch_then (qspec_then `ARB:instruction` strip_assume_tac) >>
  drule_at (Pat `alloca_frontier_inv _ _ _ _`) coherent_registration_reject_path >>
  disch_then (drule_at (Pat `calldata_decode_args _ _ _ = NONE`)) >>
  disch_then (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`entry_taint`,`env`,`FEMPTY`] mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> metis_tac[]) >>
  disch_then (qx_choosel_then [`z`,`H`,`u`] strip_assume_tac) >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ _ _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_exec o Q.SPECL [`ARB`,`ARB`]) >>
  simp[exit_result_def] >> strip_tac >>
  irule safe_observer_reject_in_context >> simp[] >>
  qexistsl_tac [`frag_observer_cut sb`,`fuel`,`observer`,`observer_ctx`,`z`] >>
  simp[Abbr `observer`, abi_decode_frag_observer_cut_no_revert]
QED

Theorem registered_kwarg_fields[local]:
  !vars ce.
    (compile_register_kwarg_vars ce vars).ce_struct_fields = ce.ce_struct_fields /\
    (compile_register_kwarg_vars ce vars).ce_flag_n_members = ce.ce_flag_n_members /\
    (!n. ~MEM n (MAP (\(name,_,_,_). name) vars) ==>
      FLOOKUP (compile_register_kwarg_vars ce vars).ce_vars n = FLOOKUP ce.ce_vars n)
Proof
  Induct >- simp[compile_register_kwarg_vars_def] >>
  PairCases >> simp[compile_register_kwarg_vars_def, FLOOKUP_UPDATE]
QED

Theorem registered_kwarg_positional_metadata[local]:
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) tv.
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs /\
  MAP (\(name,_,_,_). name) vars = MAP FST (DROP n args) ==>
  ALL_DISTINCT (MAP FST (TAKE n args)) /\
  LIST_REL (\(name,ty) tv.
    abi_decoder_coherent (compile_register_kwarg_vars ce vars) env
      (compile_register_kwarg_vars ce vars).ce_struct_fields ty tv /\
    (?loc. FLOOKUP (compile_register_kwarg_vars ce vars).ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) (TAKE n args) (TAKE n tvs) /\
  build_positional_args (compile_register_kwarg_vars ce vars) (TAKE n args) =
    build_positional_args ce (TAKE n args)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST (TAKE n args)) /\
   !name. MEM name (MAP FST (TAKE n args)) ==> ~MEM name (MAP FST (DROP n args))` by
    (`TAKE n (args:(string # type) list) ++ DROP n args = args` by simp[] >>
     qpat_assum `ALL_DISTINCT (MAP FST args)` mp_tac >>
     qpat_assum `TAKE n args ++ DROP n args = _` (fn eq => ONCE_REWRITE_TAC [SYM eq]) >>
     simp[MAP_APPEND, ALL_DISTINCT_APPEND]) >>
  simp[registered_kwarg_fields] >> conj_tac
  >- (qpat_assum `LIST_REL _ args tvs` (fn rel =>
        mp_tac (MATCH_MP (SPEC_ALL LIST_REL_TAKE) rel)) >>
      simp[LIST_REL_EL_EQN] >> strip_tac >> qx_gen_tac `i` >> strip_tac >>
      Cases_on `EL i (TAKE n args)` >> gvs[] >>
      qpat_x_assum `!n'. _` (qspec_then `i` mp_tac) >> simp[] >>
      simp[MATCH_MP abi_decoder_coherent_layout_cong
        (CONJ (cj 1 (SPEC_ALL registered_kwarg_fields))
              (cj 2 (SPEC_ALL registered_kwarg_fields)))] >>
      `FLOOKUP (compile_register_kwarg_vars ce vars).ce_vars q = FLOOKUP ce.ce_vars q` by
        (irule (cj 3 (SPEC_ALL registered_kwarg_fields)) >>
         simp[] >> qpat_assum `!name. _` irule >>
         simp[MEM_MAP] >> metis_tac[EL_MEM, pairTheory.FST]) >> metis_tac[]) >>
  irule build_positional_args_layout_cong >> simp[registered_kwarg_fields]
QED

Theorem installed_common_reject_suffix[local]:
  emit_inst JMP [Label entry.cs_current_bb] [] mid = ((),done) /\
  fn_has_code mid done fn /\ fn_has_code entry registered fn /\
  cs_extends entry registered /\ entry.cs_current_insts = [] /\
  compile_register_positional_args ce (build_positional_args ce args) 4 entry =
    (cef,registered) /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) tv.
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs /\
  fn_inst_ids_distinct fn /\
  entry.cs_current_bb NOTIN decode_label_range entry.cs_next_label registered.cs_next_label /\
  (!bb lbl. lookup_block lbl fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  MEM fn ctx.ctx_functions /\ unit_alloca_budget ctx < 2 ** 254 /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH t.vs_call_ctx.cc_calldata /\
  LENGTH t.vs_call_ctx.cc_calldata < dimword (:256) /\
  calldata_decode_args t.vs_call_ctx.cc_calldata tvs 0 = NONE /\
  alloca_inv t /\ t.vs_alloca_next <= unit_alloca_budget ctx /\
  (!id e. FLOOKUP t.vs_allocas id = SOME e ==> id < entry.cs_next_id) /\
  fresh_vars_wrt entry t /\ ~t.vs_halted /\ at_point mid t ==>
  ?z. RTC (reject_prefix_step ctx fn) t z /\ reject_prefix_terminal ctx fn z
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?bb. lookup_block mid.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH mid.cs_current_insts) =
      SOME (mk_inst mid.cs_next_id JMP [Label entry.cs_current_bb] [])` by
    (drule emit_inst_extends >> strip_tac >>
     mp_tac (Q.SPECL [`mid`,`done`,`fn`,
       `[mk_inst mid.cs_next_id JMP [Label entry.cs_current_bb] []]`]
       fn_has_code_same_block) >> simp[] >>
     disch_then (qx_choose_then `b` strip_assume_tac) >>
     qexists_tac `b` >> simp[] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all fn_has_code_start >> strip_tac >>
  `phi_prefix_length bb'.bb_instructions = 0` by metis_tac[] >>
  `reject_prefix_step ctx fn t (jump_to entry.cs_current_bb t)` by
    (irule reject_prefix_jump >> fs[at_point_def] >> metis_tac[]) >>
  `?z. RTC (reject_prefix_step ctx fn) (jump_to entry.cs_current_bb t) z /\
       reject_prefix_terminal ctx fn z` by
    (mp_tac (Q.INST [`sa` |-> `entry`, `sb` |-> `registered`,
       `s` |-> `jump_to entry.cs_current_bb t`] installed_registration_reject_prefix) >>
     simp[jump_to_def, alloca_inv_def, allocas_non_overlapping_def,
       alloca_next_valid_def, fresh_vars_wrt_def] >>
     impl_tac >- (fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
                  rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  qexists_tac `z` >> simp[] >> metis_tac[RTC_RULES]
QED

Theorem observer_instructions_before_common_entry[local]:
  cs_extends mid dispatch_end /\
  entry_alloca_ids sf dispatch_end /\ state_insts sf = [] /\
  shape_state dispatch_end /\
  dispatch_end.cs_next_id <= entry.cs_next_id /\
  dispatch_end.cs_next_var <= entry.cs_next_var /\
  MEM i (fn_insts (frag_observer init mid fn 0)) ==>
  (i.inst_opcode = ALLOCA ==> i.inst_id < entry.cs_next_id) /\
  EVERY (not_fresh_at entry) i.inst_outputs
Proof
  strip_tac >>
  `i = mk_inst 0 STOP [] [] \/ MEM i (state_insts mid)` by
    (qpat_x_assum `MEM _ (fn_insts _) ` mp_tac >>
     simp[frag_observer_def, fn_insts_def, fn_insts_blocks_def,
       MEM_APPEND, MEM_fn_insts_blocks_iff, MEM_FILTER, state_insts_def,
       all_blocks_def, MEM_FLAT, MEM_MAP, emitted_blocks_def] >>
     metis_tac[MEM_TAKE])
  >- gvs[mk_inst_def] >>
  `MEM i (state_insts dispatch_end)` by
    metis_tac[state_insts_cs_extends, MEM_APPEND] >>
  fs[entry_alloca_ids_def, shape_state_def, shape_base_state_def, EVERY_MEM] >>
  metis_tac[LESS_LESS_EQ_TRANS, not_fresh_at_mono]
QED

(* A positional failure can be established independently of the omitted
   defaults' result. If the initializer gets to the common entry, its
   allocation and register frame suffices to replay the positional decoder. *)
Theorem installed_positional_reject_after_kwargs[local]:
  compile_init_kwargs ce vars off k (Lit 0w) init = ((),mid) /\
  emit_inst JMP [Label entry.cs_current_bb] [] mid = ((),done) /\
  cs_extends init mid /\ cs_extends mid dispatch_end /\ cs_extends dispatch_end final /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks final)) /\
  fn_has_code init mid fn /\ fn_has_code mid done fn /\
  EVERY reject_prefix_opcode (state_insts dispatch_end) /\
  ALL_DISTINCT (fn_labels fn) /\ no_phi_fn fn /\
  (!i. MEM i (fn_insts (frag_observer init mid fn 0)) ==>
    (i.inst_opcode = ALLOCA ==> i.inst_id < entry.cs_next_id) /\
    EVERY (not_fresh_at entry) i.inst_outputs) /\
  fn_has_code entry registered fn /\ cs_extends entry registered /\
  entry.cs_current_insts = [] /\
  compile_register_positional_args cr (build_positional_args cr args) 4 entry =
    (cef,registered) /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) tv.
    abi_decoder_coherent cr env cr.ce_struct_fields ty tv /\
    (?loc. FLOOKUP cr.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs /\
  fn_inst_ids_distinct fn /\
  entry.cs_current_bb NOTIN decode_label_range entry.cs_next_label registered.cs_next_label /\
  MEM fn ctx.ctx_functions /\ unit_alloca_budget ctx < 2 ** 254 /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH start.vs_call_ctx.cc_calldata /\
  LENGTH start.vs_call_ctx.cc_calldata < dimword (:256) /\
  calldata_decode_args start.vs_call_ctx.cc_calldata tvs 0 = NONE /\
  alloca_inv start /\
  start.vs_alloca_next + remaining_alloca_budget (fn_insts fn) start <= unit_alloca_budget ctx /\
  (!id e. FLOOKUP start.vs_allocas id = SOME e ==> id < entry.cs_next_id) /\
  fresh_vars_wrt entry start /\ ~start.vs_halted /\ at_point init start ==>
  ?P. P start /\ (!s i. P s /\ active_inst fn i s ==> reject_prefix_opcode i) /\
    (!s t. P s /\ reject_prefix_step ctx fn s t ==> P t)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac (SPEC_ALL installed_kwarg_initializer_invariant) >>
  impl_tac >- suspend "cut" >>
  disch_then ACCEPT_TAC
QED

Resume installed_positional_reject_after_kwargs[cut]:
  asm_rewrite_tac[] >>
  rpt strip_tac >>
  mp_tac (Q.INST [`st` |-> `entry`,`obs` |-> `frag_observer init mid fn 0`]
    (Q.SPECL [`start`,`t`] reject_prefix_observed_counters)) >>
  asm_rewrite_tac[] >> strip_tac >>
  `RTC (reject_prefix_step ctx fn) start t` by
    (irule RTC_MONOTONE >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all reject_prefix_allocation_frame >> strip_tac >>
  `t.vs_alloca_next <= unit_alloca_budget ctx` by decide_tac >>
  mp_tac (Q.INST [`ce` |-> `cr`] installed_common_reject_suffix) >>
  impl_tac >- (asm_rewrite_tac[] >> fs[no_phi_fn_def, EVERY_MEM] >>
               metis_tac[lookup_block_MEM]) >>
  disch_then ACCEPT_TAC
QED
Finalise installed_positional_reject_after_kwargs

Theorem length_minus_extension[local]:
  n - (n + k) = 0
Proof
  simp[SUB_EQ_0, LESS_EQ_ADD]
QED

Theorem entry_checks_reject_prefix_code[local]:
  compile_entry_checks m pay sa = ((),sb) ==>
  sa.cs_blocks = sb.cs_blocks /\ cs_extends sa sb /\
  frag_gas_free sa sb /\ EVERY reject_prefix_opcode (frag_code sa sb)
Proof
  Cases_on `pay` >> Cases_on `4 < m` >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  (conj_tac
    >- (simp[cs_extends_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
        MATCH_ACCEPT_TAC IS_PREFIX_APPEND3)) >>
  simp[frag_gas_free_def, frag_code_def, emitted_insts_def, DROP_APPEND,
    length_minus_extension,
    emitted_blocks_def, reject_prefix_opcode_def, mk_inst_def]
QED

Theorem installed_entry_checks_reject_prefix[local]:
  compile_entry_checks m pay sa = ((),sb) /\ fn_has_code sa sb fn /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ((~pay /\ s.vs_call_ctx.cc_callvalue <> 0w) \/
   (4 < m /\ LENGTH s.vs_call_ctx.cc_calldata < m /\ m < dimword (:256))) ==>
  ?u. RTC (reject_prefix_step ctx fn) s u /\ reject_prefix_terminal ctx fn u
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule entry_checks_reject_prefix_code >> strip_tac >>
  drule_all compile_entry_checks_frag >>
  disch_then (mp_tac o REWRITE_RULE [frag_exec_def, BETA_THM] o Q.SPEC `ctx`) >>
  disch_then (qspecl_then [`frag_observer sa sb fn 0`, `s`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[frag_observer_has_code]) >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (qpat_x_assum `(~pay /\ _) \/ _` (DISJ_CASES_THEN strip_assume_tac) >>
      fs[] >>
      `LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)` by decide_tac >>
      gvs[]) >>
  irule reject_prefix_observer_revert >> metis_tac[]
QED

Theorem installed_entry_checks_continue[local]:
  compile_entry_checks m pay sa = ((),sb) /\ fn_has_code sa sb fn /\
  EVERY reject_prefix_opcode sa.cs_current_insts /\
  (!bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  m <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?t u. vars_pc_only s t /\ fresh_vars_wrt sb t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        RTC (reject_prefix_step ctx fn) s u /\ ~u.vs_halted /\
        u = t with vs_returndata := u.vs_returndata
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule entry_checks_reject_prefix_code >> strip_tac >>
  mp_tac (Q.INST [`P` |-> `\t. vars_pc_only s t /\ fresh_vars_wrt sb t /\
                                t.vs_current_bb = sb.cs_current_bb /\
                                t.vs_inst_idx = LENGTH sb.cs_current_insts`]
    reject_fragment_continues) >>
  simp[emitted_blocks_def] >>
  impl_tac >- (
    qx_gen_tac `observer` >> strip_tac >>
    drule_all compile_entry_checks_pass >>
    disch_then (mp_tac o REWRITE_RULE [frag_exec_def, BETA_THM] o Q.SPEC `ctx`) >>
    disch_then (qspecl_then [`observer`, `s`] mp_tac) >>
    simp[] >> metis_tac[runs_through_def]) >>
  simp[GSYM CONJ_ASSOC]
QED

Theorem runtime_reject_prefix_excludes_fmp[local]:
  lower_vyper_runtime_unit tops rp = SOME u /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME entry /\
  RTC (reject_prefix_step u.cu_context entry)
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>) z /\
  reject_prefix_terminal u.cu_context entry z /\
  raw_reachable vs u.cu_context fn inst s ==>
  ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >> gvs[] >>
  drule_all lower_vyper_runtime_unit_entry_label >> strip_tac >>
  drule lookup_function_MEM >> strip_tac >>
  qpat_x_assum `lowering_context_ok _` (strip_assume_tac o REWRITE_RULE [lowering_context_ok_def]) >>
  `ALL_DISTINCT (fn_labels entry)` by
    (qpat_assum `EVERY (\f. ALL_DISTINCT _ /\ fn_has_entry f) _`
       (qspec_then `entry` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
  `?bb. lookup_block "__entry" entry.fn_blocks = SOME bb` by
    (Cases_on `entry.fn_blocks` >> fs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
  drule_all lower_vyper_runtime_unit_block_phi >> strip_tac >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `enters_block entry start start` by
    (simp[enters_block_def, Abbr `start`] >>
     Cases_on `bb.bb_instructions` >> gvs[eval_phis_def, phi_prefix_length_def, AllCaseEqs()]) >>
  drule reject_prefix_covers_reachable >>
  disch_then (qspecl_then [`"__entry"`,`entry`,`"__entry"`,`start`,`z`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all runtime_reachable_raw_fmp_opcode >>
  fs[reject_prefix_opcode_def]
QED

Theorem runtime_legacy_fallback_excludes_fmp[local]:
  lower_vyper_runtime_unit tops rp = SOME u /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  ~EXISTS is_default_decl tops /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  (LENGTH vs.vs_call_ctx.cc_calldata < 4 \/
   FIND (\(name,tys). abi_method_id (type_env tops) name tys =
       cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) = NONE) /\
  raw_reachable vs u.cu_context fn inst s ==>
  ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  rename1 `lookup_function "__entry" _ = SOME entry` >>
  drule_all lower_runtime_default_free_packages >> strip_tac >>
  `FST (SND (SND (classify_functions tops))) = NONE` by
    (drule calldataNoneFallbackJointTheory.absent_default_fold >>
     simp[classify_functions_def] >> rpt (pairarg_tac >> gvs[])) >>
  `fb = NONE` by simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  qpat_x_assum `fb = NONE` SUBST_ALL_TAC >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `!st. fresh_vars_wrt st start` by
    (gen_tac >> drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`,`"__entry"`,`st`] mp_tac) >> simp[Abbr `start`]) >>
  `~start.vs_halted /\ LENGTH start.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`,`"__entry"`,`initial_compile_state "__entry"`] mp_tac) >>
     simp[Abbr `start`]) >>
  `EVERY (\(sel,lbl). sel < 2 ** 32) (MAP (\(sel,lbl,z). (sel,lbl)) sels)` by
    (qspecl_then [`type_env tops`,`FST (classify_functions tops)`] mp_tac linear_selectors_lt >>
     simp[]) >>
  `!fl. linear_dispatch_target start.vs_call_ctx.cc_calldata
       (MAP (\(sel,lbl,z). (sel,lbl)) sels) fl = fl` by
    (gen_tac >> simp[Abbr `start`] >> irule default_raw_fallback_target >> simp[]) >>
  `start.vs_current_bb = "__entry" /\ start.vs_inst_idx = 0` by simp[Abbr `start`] >>
  drule_all installed_legacy_fallback_reject_prefix >> strip_tac >>
  qpat_x_assum `Abbrev (start = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all runtime_reject_prefix_excludes_fmp >> simp[]
QED

Theorem legacy_checks_registration_reject_prefix[local]:
  compile_entry_checks m pay opened = ((),checked) /\
  compile_register_positional_args ce (build_positional_args ce args) 4 checked = (cef,last) /\
  cs_extends checked last /\ fn_has_code opened checked fn /\
  fn_has_code checked last fn /\ fn_inst_ids_distinct fn /\
  opened.cs_current_bb = "fn_" ++ name /\ opened.cs_current_insts = [] /\
  (!bb lbl. lookup_block lbl fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  MEM fn ctx.ctx_functions /\ unit_alloca_budget ctx < 2 ** 254 /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(n,ty) tv.
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars n = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs /\
  m = 4 + SUM (MAP tv_abi_size tvs) /\ m < dimword (:256) /\
  4 <= LENGTH t.vs_call_ctx.cc_calldata /\
  LENGTH t.vs_call_ctx.cc_calldata < dimword (:256) /\
  (LENGTH t.vs_call_ctx.cc_calldata < m \/
   calldata_decode_args t.vs_call_ctx.cc_calldata tvs 0 = NONE) /\
  alloca_inv t /\ t.vs_alloca_next <= unit_alloca_budget ctx /\
  (!id pair. FLOOKUP t.vs_allocas id = SOME pair ==> id < checked.cs_next_id) /\
  fresh_vars_wrt opened t /\ ~t.vs_halted /\
  t.vs_current_bb = opened.cs_current_bb /\ t.vs_inst_idx = 0 ==>
  ?z. RTC (reject_prefix_step ctx fn) t z /\ reject_prefix_terminal ctx fn z
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `(~pay /\ t.vs_call_ctx.cc_callvalue <> 0w) \/
            LENGTH t.vs_call_ctx.cc_calldata < m`
  >- (irule installed_entry_checks_reject_prefix >> simp[] >>
      qexistsl_tac [`m`,`pay`,`opened`,`checked`] >>
      qpat_x_assum `(~pay /\ _) \/ _` DISJ_CASES_TAC >> simp[] >> decide_tac) >>
  `~(~pay /\ t.vs_call_ctx.cc_callvalue <> 0w)` by metis_tac[] >>
  `m <= LENGTH t.vs_call_ctx.cc_calldata` by
    (fs[DE_MORGAN_THM] >> decide_tac) >>
  drule_at (Pat `compile_entry_checks _ _ _ = _`) installed_entry_checks_continue >>
  disch_then (qspecl_then [`t`,`fn`,`ctx`] mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> metis_tac[]) >>
  disch_then (qx_choosel_then [`p`,`q`] strip_assume_tac) >>
  qpat_assum `vars_pc_only t p` (strip_assume_tac o MATCH_MP vars_pc_only_fields) >>
  `p.vs_allocas = t.vs_allocas /\ p.vs_alloca_next = t.vs_alloca_next` by
    (qpat_assum `vars_pc_only t p` (mp_tac o REWRITE_RULE [vars_pc_only_def]) >>
     simp[venom_state_component_equality]) >>
  `q.vs_call_ctx = t.vs_call_ctx /\ q.vs_allocas = t.vs_allocas /\ q.vs_alloca_next = t.vs_alloca_next /\
   q.vs_current_bb = checked.cs_current_bb /\ q.vs_inst_idx = LENGTH checked.cs_current_insts` by
    (qpat_assum `q = p with vs_returndata := _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `fresh_vars_wrt checked q` by
    (qpat_assum `q = p with vs_returndata := _` (fn th => ONCE_REWRITE_TAC [th]) >>
     PURE_REWRITE_TAC [fresh_vars_wrt_def, venom_state_accfupds] >>
     qpat_assum `fresh_vars_wrt checked p` (ACCEPT_TAC o REWRITE_RULE [fresh_vars_wrt_def])) >>
  qpat_assum `compile_entry_checks _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [same_blocks_def] o
     MATCH_MP compile_entry_checks_same_blocks) >>
  qpat_assum `compile_entry_checks _ _ _ = _`
    (strip_assume_tac o MATCH_MP entry_checks_reject_prefix_code) >>
  `EVERY reject_prefix_opcode checked.cs_current_insts` by
    (fs[frag_code_def, emitted_blocks_def, emitted_insts_def] >> gvs[]) >>
  `checked.cs_current_bb NOTIN decode_label_range checked.cs_next_label last.cs_next_label` by
    simp[decode_label_range_def, fresh_label_output_def] >>
  `alloca_inv q` by
    (fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `?z. RTC (reject_prefix_step ctx fn) q z /\ reject_prefix_terminal ctx fn z` by
    (mp_tac (Q.INST [`sa` |-> `checked`, `sb` |-> `last`, `s` |-> `q`]
       installed_registration_reject_prefix) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                  simp[FLOOKUP_DEF] >> fs[] >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  qexists_tac `z` >> simp[] >>
  metis_tac[RTC_TRANSITIVE, transitive_def]
QED

Theorem legacy_selected_source_reject_no_fmp[local]:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  FIND (\(n,ts). abi_method_id (type_env tops) n ts =
    cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) =
    SOME (name,tys) /\
  (OPT_MMAP (evaluate_type (type_env tops)) tys = NONE \/
    ?tvs. OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs /\
      (LENGTH vs.vs_call_ctx.cc_calldata < 4 + SUM (MAP tv_abi_size tvs) \/
       calldata_decode_args vs.vs_call_ctx.cc_calldata tvs 0 = NONE)) /\
  unit_alloca_budget unit.cu_context < 2 ** 254 /\
  raw_reachable vs unit.cu_context fn inst s ==>
  ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule venomInstTheory.FIND_MEM >> strip_tac >>
  drule_all none_signature_evaluates >> strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  rename1 `lookup_function "__entry" _ = SOME entry` >>
  drule_all lower_runtime_default_free_packages >>
  disch_then (qx_choosel_then [`sels`,`extpkgs`,`intpkgs`,`fbpkg`,`ei`] strip_assume_tac) >>
  `ALL_DISTINCT (MAP FST (build_selectors (type_env tops) (FST (classify_functions tops))))` by
    (fs[source_typing_ok_def] >>
     drule (INST_TYPE [alpha |-> ``:160 word``] check_contract_selectors_distinct) >> simp[]) >>
  `MEM (set_external_package_target rp.rpol_target
      (package_external_fn tops T (K context$global_nonreentrant_slot)
        (mut,nr,rr,name,args,([] : vyperAST$expr list),ret,fbody))) extpkgs` by
    (qpat_assum `extpkgs = _` SUBST1_TAC >>
     simp[MEM_MAP] >> qexists_tac `(mut,nr,rr,name,args,([] : vyperAST$expr list),ret,fbody)` >>
     simp[combinTheory.o_DEF]) >>
  Cases_on `set_external_package_target rp.rpol_target
    (package_external_fn tops T (K context$global_nonreentrant_slot)
      (mut,nr,rr,name,args,([] : vyperAST$expr list),ret,fbody))` >>
  PairCases_on `r` >>
  rename1 `set_external_package_target _ _ = (lbl,ce,pos,m,pay,nr',key,ut,iv,pbody,rt)` >>
  `lbl = "fn_" ++ name` by
    (qpat_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[NoAsms, package_external_fn_def, set_external_package_target_def, LET_THM]) >>
  qpat_x_assum `lbl = _` SUBST_ALL_TAC >>
  qpat_x_assum `tys = _` SUBST_ALL_TAC >>
  drule_all none_selected_package_metadata >> strip_tac >>
  qpat_x_assum `pos = _` SUBST_ALL_TAC >>
  `extpkgs <> []` by (strip_tac >> fs[]) >>
  drule_all run_lowering_selected_entry_code >>
  disch_then (qx_choosel_then [`fl`,`sf`,`sd`,`opened`,`checked`,`cef`,`last`,`bodyend`]
    strip_assume_tac) >>
  `?bb. lookup_block ("fn_" ++ name) entry.fn_blocks = SOME bb` by
    (qpat_assum `cs_extends opened checked` (fn ext =>
       qpat_assum `fn_has_code opened checked entry`
         (qx_choose_then `b` strip_assume_tac o
          MATCH_MP (Q.SPECL [`opened`,`checked`,`entry`] fn_has_code_start) o CONJ ext)) >>
     qexists_tac `b` >> metis_tac[]) >>
  `!bb lbl. lookup_block lbl entry.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
      (rpt strip_tac >> irule lowering_context_ok_block_phi >> metis_tac[]) >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `!st. fresh_vars_wrt st start` by
    (gen_tac >> drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`,`"__entry"`,`st`] mp_tac) >> simp[Abbr `start`]) >>
  `~start.vs_halted /\ LENGTH start.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`,`"__entry"`,`sf`] mp_tac) >> simp[Abbr `start`]) >>
  `EVERY (\(sel,lbl). sel < 2 ** 32) (MAP (\(sel,lbl,z). (sel,lbl)) sels)` by
    (qspecl_then [`type_env tops`,`FST (classify_functions tops)`] mp_tac linear_selectors_lt >>
     simp[]) >>
  `!fallback. linear_dispatch_target start.vs_call_ctx.cc_calldata
    (MAP (\(sel,lbl,z). (sel,lbl)) sels) fallback = "fn_" ++ name` by
    (gen_tac >> simp[Abbr `start`] >> drule_all default_raw_selected_target >> simp[]) >>
  `start.vs_current_bb = "__entry" /\ start.vs_inst_idx = 0` by simp[Abbr `start`] >>
  `phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  drule_all installed_legacy_named_selector_prefix >>
  disch_then (qx_choosel_then [`fl'`,`sf'`,`sd'`,`t`] strip_assume_tac) >>
  `fl' = fl /\ sf' = sf /\ sd' = sd` by metis_tac[pairTheory.PAIR_EQ] >>
  `fresh_vars_wrt opened t` by
    (irule fresh_vars_wrt_mono >> qexists_tac `sd` >> fs[]) >>
  `t.vs_call_ctx = vs.vs_call_ctx /\ t.vs_allocas = FEMPTY /\ t.vs_alloca_next = 0` by
    fs[Abbr `start`, initial_venom_state_rel_def] >>
  `LIST_REL (\(n,ty) tv.
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars n = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs` by
    (drule OPT_MMAP_LENGTH >> strip_tac >>
     simp[LIST_REL_EL_EQN] >> qx_gen_tac `i` >> strip_tac >>
     qpat_x_assum `LIST_REL _ args _`
       (qspec_then `i` mp_tac o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     Cases_on `EL i args` >> simp[EL_ZIP, EL_MAP]) >>
  `MEM entry unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `LENGTH t.vs_call_ctx.cc_calldata < m \/
    calldata_decode_args t.vs_call_ctx.cc_calldata tvs 0 = NONE` by fs[] >>
  `alloca_inv t` by
    simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def, FLOOKUP_DEF] >>
  `?z. RTC (reject_prefix_step unit.cu_context entry) t z /\
       reject_prefix_terminal unit.cu_context entry z` by
    (mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `fn` |-> `entry`, `env` |-> `type_env tops`]
       legacy_checks_registration_reject_prefix) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[Abbr `start`, FLOOKUP_DEF]) >>
     disch_then ACCEPT_TAC) >>
  `RTC (reject_prefix_step unit.cu_context entry) start z` by
    metis_tac[RTC_TRANSITIVE, transitive_def] >>
  qpat_x_assum `Abbrev (start = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all runtime_reject_prefix_excludes_fmp >> simp[]
QED

Theorem runtime_legacy_reject_excludes_fmp[local]:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  unit_alloca_budget unit.cu_context < 2 ** 254 /\
  raw_reachable vs unit.cu_context fn inst s ==>
  ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule calldata_dispatch_none_cases >>
  disch_then (DISJ_CASES_THEN2 (REPEAT_TCL CONJUNCTS_THEN assume_tac)
    (qx_choosel_then [`name`,`tys`] (REPEAT_TCL CONJUNCTS_THEN assume_tac)))
  >- (drule_all runtime_legacy_fallback_excludes_fmp >> simp[]) >>
  Q.SUBGOAL_THEN
    `OPT_MMAP (evaluate_type (type_env tops)) tys = NONE \/
   ?tvs. OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs /\
     (LENGTH vs.vs_call_ctx.cc_calldata < 4 + SUM (MAP tv_abi_size tvs) \/
      calldata_decode_args vs.vs_call_ctx.cc_calldata tvs 0 = NONE)` assume_tac
  >- metis_tac[] >>
  drule_all legacy_selected_source_reject_no_fmp >> simp[]
QED

Theorem lower_runtime_grouped_packages[local]:
  lower_vyper_runtime_unit tops rp = SOME u /\
  EXISTS external_has_defaults (FST (classify_functions tops)) ==>
  ?groups ints fb.
    run_grouped_lowering groups ints fb rp "__entry" = SOME u /\
    groups = MAP (package_external_group tops rp.rpol_target T
      (K global_nonreentrant_slot)) (FST (classify_functions tops)) /\
    fb = set_fallback_package_target rp.rpol_target
      (package_fallback_fn tops T (K global_nonreentrant_slot)
        (FST (SND (SND (classify_functions tops))))) /\
    EVERY group_entry_labels_ok groups /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints)
Proof
  strip_tac >> Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,intf,fallback,ctor)` >>
  qpat_x_assum `EXISTS external_has_defaults _`
    (assume_tac o REWRITE_RULE [pairTheory.FST]) >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def, bool_case_eq] >> strip_tac >>
  qexists_tac `MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn tops T (K global_nonreentrant_slot) F 0)
    (order_internals (runtime_internal_order tops intf) intf)` >>
  simp[EVERY_MAP, package_external_group_labels] >>
  rewrite_tac[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
    internal_fn_descriptors_MAP_package_internal_fn] >>
  rw[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD] >>
  rewrite_tac[internal_label_ok_def, internal_fn_label_prefix]
QED

Theorem runtime_grouped_short_excludes_fmp[local]:
  lower_vyper_runtime_unit tops rp = SOME u /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  ~EXISTS is_default_decl tops /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  LENGTH vs.vs_call_ctx.cc_calldata < 4 /\
  raw_reachable vs u.cu_context fn inst s ==>
  ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  rename1 `lookup_function "__entry" _ = SOME entry` >>
  drule_all lower_runtime_grouped_packages >> strip_tac >>
  `FST (SND (SND (classify_functions tops))) = NONE` by
    (drule calldataNoneFallbackJointTheory.absent_default_fold >>
     simp[classify_functions_def] >> rpt (pairarg_tac >> gvs[])) >>
  `fb = NONE` by simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  qpat_x_assum `fb = NONE` SUBST_ALL_TAC >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `~start.vs_halted` by
    (drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`,`"__entry"`,`initial_compile_state "__entry"`] mp_tac) >>
     simp[Abbr `start`]) >>
  `start.vs_current_bb = "__entry" /\ start.vs_inst_idx = 0 /\
   LENGTH start.vs_call_ctx.cc_calldata < 4` by simp[Abbr `start`] >>
  drule_all installed_grouped_short_reject_prefix >> strip_tac >>
  qpat_x_assum `Abbrev (start = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all runtime_reject_prefix_excludes_fmp >> simp[]
QED

Theorem grouped_selector_ids_perm[local]:
  PERM (MAP FST (grouped_selectors
      (MAP (package_external_group tops target trans nkeys)
        (FST (classify_functions tops)))))
    (abi_external_method_ids (type_env tops) tops)
Proof
  mp_tac (Q.ISPEC `\(name,tys). abi_method_id (type_env tops) name tys`
    (MATCH_MP sortingTheory.PERM_MAP abi_signature_partition)) >>
  simp[grouped_selector_method_ids, vyperABIEntriesTheory.abi_external_method_ids_def,
    listTheory.MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem grouped_selector_word_match[local]:
  MEM sel (MAP FST (grouped_selectors
    (MAP (package_external_group tops target trans nkeys)
      (FST (classify_functions tops))))) /\ 4 <= LENGTH cd ==>
  ((n2w sel : bytes32) = calldata_method_id cd <=> sel = cd_selector cd)
Proof
  strip_tac >>
  `MEM sel (abi_external_method_ids (type_env tops) tops)` by
    metis_tac[grouped_selector_ids_perm, PERM_MEM_EQ] >>
  `sel < dimword (:256)` by
    (qpat_x_assum `MEM _ (abi_external_method_ids _ _)` mp_tac >>
     simp[vyperABIEntriesTheory.abi_external_method_ids_def, MEM_MAP,
          pairTheory.EXISTS_PROD, PULL_EXISTS] >>
     rpt strip_tac >> gvs[] >>
     rename1 `abi_method_id (type_env tops) fname ftys < _` >>
     mp_tac (Q.INST [`tenv` |-> `type_env tops`, `name` |-> `fname`, `tys` |-> `ftys`]
       compute_selector_method_id) >>
     simp[compute_selector_def] >>
     disch_then (fn th => PURE_ONCE_REWRITE_TAC [SYM (CONJUNCT1 th)]) >> simp[w2n_lt]) >>
  `sel MOD dimword (:256) = sel` by metis_tac[LESS_MOD] >>
  drule cd_selector_method_id >> disch_then SUBST_ALL_TAC >>
  eq_tac
  >- (disch_then (mp_tac o AP_TERM (Term `w2n:bytes32 -> num`)) >>
      asm_rewrite_tac[w2n_n2w]) >>
  simp[]
QED

Theorem grouped_source_missed_selector[local]:
  FIND (\(name,tys). abi_method_id (type_env tops) name tys = cd_selector cd)
        (abi_external_signatures tops) = NONE /\ 4 <= LENGTH cd /\
  MEM sel (MAP FST (grouped_selectors
    (MAP (package_external_group tops target trans nkeys)
      (FST (classify_functions tops))))) ==>
  (n2w sel : bytes32) <> calldata_method_id cd
Proof
  strip_tac >> drule_all grouped_selector_word_match >> simp[] >>
  `!xs. FIND (\(name,tys). abi_method_id (type_env tops) name tys = cd_selector cd) xs = NONE ==>
    !name tys. MEM (name,tys) xs ==> abi_method_id (type_env tops) name tys <> cd_selector cd` by
    (Induct >- simp[] >> qx_gen_tac `head` >> PairCases_on `head` >>
     simp[FIND_thm] >> metis_tac[]) >>
  `MEM sel (abi_external_method_ids (type_env tops) tops)` by
    metis_tac[grouped_selector_ids_perm, PERM_MEM_EQ] >>
  qpat_x_assum `MEM _ (abi_external_method_ids _ _)` mp_tac >>
  simp[vyperABIEntriesTheory.abi_external_method_ids_def, MEM_MAP, pairTheory.EXISTS_PROD] >>
  disch_then (qx_choosel_then [`fname`,`ftys`] strip_assume_tac) >>
  qpat_x_assum `!xs. FIND _ xs = NONE ==> _`
    (qspec_then `abi_external_signatures tops` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`fname`,`ftys`] mp_tac) >> simp[]
QED

Theorem grouped_source_signature_prefix[local]:
  MEM (name,tys) (abi_external_signatures tops) ==>
  ?mut nr rr args defaults ret stmts prefix k.
    MEM (mut,nr,rr,name,args,defaults,ret,stmts)
      (FST (classify_functions tops)) /\
    MEM (prefix,k) (abi_entries args defaults) /\
    tys = MAP SND prefix
Proof
  strip_tac >>
  `MEM (name,tys)
     (FLAT (MAP (\(mut,nr,rr,n,args,ds,ret,stmts).
        abi_function_signatures n args ds) (FST (classify_functions tops))))` by
    (rewrite_tac[classify_external_signatures] >>
     metis_tac[abi_signature_partition, PERM_MEM_EQ]) >>
  pop_assum mp_tac >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS, pairTheory.EXISTS_PROD] >>
  rpt strip_tac >> gvs[vyperABIEntriesTheory.abi_function_signatures_def,
    MEM_MAP, pairTheory.EXISTS_PROD] >>
  metis_tac[]
QED

Theorem grouped_source_selected_package[local]:
  FIND (\(name,tys). abi_method_id (type_env tops) name tys = cd_selector cd)
    (abi_external_signatures tops) = SOME (name,tys) /\
  4 <= LENGTH cd ==>
  ?mut nr rr args defaults ret stmts prefix k group sel.
    MEM (mut,nr,rr,name,args,defaults,ret,stmts)
      (FST (classify_functions tops)) /\
    MEM (prefix,k) (abi_entries args defaults) /\ tys = MAP SND prefix /\
    group = package_external_group tops target trans nkeys
      (mut,nr,rr,name,args,defaults,ret,stmts) /\
    MEM group (MAP (package_external_group tops target trans nkeys)
      (FST (classify_functions tops))) /\
    MEM sel (external_group_selectors group) /\
    n2w (FST sel) = calldata_method_id cd
Proof
  strip_tac >>
  `MEM (name,tys) (abi_external_signatures tops)` by metis_tac[venomInstTheory.FIND_MEM] >>
  `abi_method_id (type_env tops) name tys = cd_selector cd` by
    (drule venomInstTheory.FIND_P >> simp[]) >>
  drule grouped_source_signature_prefix >> strip_tac >>
  qabbrev_tac `group = package_external_group tops target trans nkeys
    (mut,nr,rr,name,args,defaults,ret,stmts)` >>
  `MAP FST (external_group_selectors group) =
    MAP (\(n,ts). abi_method_id (type_env tops) n ts)
      (vyperABIEntries$abi_function_signatures name args defaults)` by
    (unabbrev_all_tac >> MATCH_ACCEPT_TAC external_group_method_ids) >>
  `MEM (abi_method_id (type_env tops) name tys)
       (MAP FST (external_group_selectors group))` by
    (qpat_assum `MAP FST (external_group_selectors group) = _`
      (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     simp[vyperABIEntriesTheory.abi_function_signatures_def,
          MAP_MAP_o, combinTheory.o_DEF, MEM_MAP, pairTheory.EXISTS_PROD] >>
     qexistsl_tac [`name`,`tys`] >> simp[] >>
     qexistsl_tac [`prefix`,`k`] >> simp[]) >>
  pop_assum (qx_choose_then `sel` strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
  `MEM group (MAP (package_external_group tops target trans nkeys)
    (FST (classify_functions tops)))` by
    (simp[MEM_MAP, Abbr `group`] >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`mut`,`nr`,`rr`,`args`,`defaults`,`ret`,`stmts`,`prefix`,`k`,`group`,`sel`] >>
  simp[Abbr `group`] >> metis_tac[cd_selector_method_id, n2w_w2n]
QED

Theorem grouped_selected_package_predecessors[local]:
  groups = pre ++ group::post /\ ALL_DISTINCT (MAP FST (grouped_selectors groups)) /\
  MEM sel (external_group_selectors group) /\ n2w (FST sel) = calldata_method_id cd /\
  groups = MAP (package_external_group tops target trans nkeys)
    (FST (classify_functions tops)) /\ 4 <= LENGTH cd ==>
  EVERY (\entry. calldata_method_id cd <> n2w (FST entry)) (grouped_selectors pre)
Proof
  strip_tac >>
  `grouped_selectors groups = grouped_selectors pre ++ external_group_selectors group ++
     grouped_selectors post` by
    (qpat_assum `groups = pre ++ _` (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[grouped_selectors_def]) >>
  `!n. MEM n (MAP FST (grouped_selectors groups)) ==>
    ((n2w n : bytes32) = calldata_method_id cd <=> n = cd_selector cd)` by
    (rpt strip_tac >>
     qpat_assum `groups = MAP _ _` (fn th =>
       qpat_x_assum `MEM n _` (assume_tac o REWRITE_RULE [th])) >>
     drule_all grouped_selector_word_match >> simp[]) >>
  `MEM (FST sel) (MAP FST (grouped_selectors groups))` by
    (qpat_assum `grouped_selectors groups = _` (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[MEM_MAP] >> metis_tac[]) >>
  `FST sel = cd_selector cd` by metis_tac[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM (FST entry) (MAP FST (grouped_selectors pre))` by
    (simp[MEM_MAP] >> qexists_tac `entry` >> simp[]) >>
  `MEM (FST entry) (MAP FST (grouped_selectors groups))` by
    (qpat_assum `grouped_selectors groups = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `FST entry = cd_selector cd` by metis_tac[] >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  simp[ALL_DISTINCT_APPEND, MEM_MAP] >> metis_tac[]
QED

Theorem grouped_defaults_selected_entry[local]:
  defaults <> [] /\ MEM (prefix,k) (abi_entries args defaults) /\
  package_external_group tops target trans nkeys
    (mut,nr,rr,name,args,defaults,ret,stmts) = ExternalDefaults common entries specs off ==>
  MEM (abi_method_id (type_env tops) name (MAP SND prefix),
       external_prefix_label name k,min_calldata_size common.ec_env prefix 0,k) entries /\
  common.ec_common_label = external_common_label name /\
  common.ec_pos_args = build_positional_args common.ec_env (TAKE (LENGTH args - LENGTH defaults) args) /\
  off = min_calldata_size common.ec_env (TAKE (LENGTH args - LENGTH defaults) args) 0 /\
  specs = MAP (\((n,ty),e). (n,ty,e)) (ZIP (DROP (LENGTH args - LENGTH defaults) args,defaults))
Proof
  strip_tac >>
  qpat_x_assum `package_external_group _ _ _ _ _ = _` mp_tac >>
  simp[package_external_group_def, NULL_EQ, LET_THM, compute_selector_method_id] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[MEM_MAP] >>
  qexists_tac `(prefix,k)` >> simp[]
QED

Theorem prefix_head_size_le[local]:
  !n tvs. SUM (MAP tv_abi_size (TAKE n tvs)) <= SUM (MAP tv_abi_size tvs)
Proof
  Induct >> Cases_on `tvs` >> simp[TAKE_def]
QED

Theorem grouped_kwarg_names[local]:
  LENGTH (defaults:expr list) <= LENGTH (args:(string # type) list) /\
  specs = MAP (\((n,ty),e). (n,ty,e))
    (ZIP (DROP (LENGTH args - LENGTH defaults) args,defaults)) /\
  MAP (\(name,_,ty,e). (name,ty,e)) vars = specs ==>
  MAP (\(name,_,_,_). name) vars = MAP FST (DROP (LENGTH args - LENGTH defaults) args)
Proof
  strip_tac >>
  `LENGTH (DROP (LENGTH args - LENGTH defaults) args) = LENGTH defaults` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  `MAP (FST : string # type # expr -> string)
       (MAP (\(name,_,ty,e). (name,ty,e)) vars) =
     MAP FST (MAP (\((n,ty),e). (n,ty,e))
       (ZIP (DROP (LENGTH args - LENGTH defaults) args,defaults)))` by
    asm_rewrite_tac[] >>
  pop_assum mp_tac >>
  simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD] >>
  `(\((name,_),_). name) = ((FST o FST) : (string # type) # expr -> string)` by
    simp[FUN_EQ_THM, pairTheory.FORALL_PROD] >>
  asm_simp_tac bool_ss [MAP_ZIP] >>
  simp[pairTheory.LAMBDA_PROD]
QED

Theorem grouped_defaults_argument_metadata[local]:
  lower_vyper_runtime_unit tops rp = SOME u /\
  supported_program tops /\ source_typing_ok tops am tx /\
  MEM (mut,nr,rr,name,args,defaults,ret,stmts) (FST (classify_functions tops)) /\
  package_external_group tops rp.rpol_target tr nkeys
    (mut,nr,rr,name,args,defaults,ret,stmts) = ExternalDefaults common entries specs off ==>
  ALL_DISTINCT (MAP FST args) /\
  ?tvs. OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
    4 + SUM (MAP tv_abi_size tvs) < dimword (:256) /\
    LIST_REL (\(n,ty) tv.
      abi_decoder_coherent common.ec_env (type_env tops) common.ec_env.ce_struct_fields ty tv /\
      (?loc. FLOOKUP common.ec_env.ce_vars n = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      type_memory_size tv < dimword (:256)) args tvs
Proof
  strip_tac >>
  Cases_on `set_external_package_target rp.rpol_target
    (package_external_fn tops tr nkeys (mut,nr,rr,name,args,[],ret,stmts))` >>
  PairCases_on `r` >>
  drule_all registration_reject_classified_defaults_metadata >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `tvs` strip_assume_tac))) >>
  `common.ec_env = r0` by
    (qpat_x_assum `package_external_group _ _ _ _ _ = _` mp_tac >>
     simp[package_external_group_def, LET_THM] >>
     Cases_on `defaults = []` >> gvs[NULL_EQ] >>
     Cases_on `ret = NoneT` >>
     gvs[package_external_fn_def, set_external_package_target_def, LET_THM] >>
     strip_tac >> gvs[]) >>
  simp[] >> drule OPT_MMAP_LENGTH >> simp[] >> strip_tac >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[LIST_REL_EL_EQN] >> strip_tac >> qx_gen_tac `j` >> strip_tac >>
  qpat_x_assum `!n. n < LENGTH args ==> _` (qspec_then `j` mp_tac) >>
  simp[EL_ZIP, EL_MAP] >> Cases_on `EL j args` >> simp[]
QED

Theorem checked_external_defaults_parameters[local]:
  source_typing_ok tops am tx /\ defaults <> [] /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,nr,args,defaults,ret,body) ==>
  params_ok (type_env tops) args /\ LENGTH defaults <= LENGTH args /\
  EVERY (runtime_constant_expr [(NONE,tops)]) defaults
Proof
  strip_tac >> drule lookup_function_External_cases >> strip_tac
  >- (fs[source_typing_ok_def] >>
      `module_allocated am.layouts tx.target NONE tops` by
        (drule check_contract_main_module_allocated >> simp[]) >>
      `check_function_body am.layouts tx.target [(NONE,tops)] art NONE
        External mut nr args defaults ret body` by
        (irule check_contract_runtime_function_body_MEM >> simp[] >>
         qexistsl_tac [`name`,`raw`] >> simp[]) >>
      fs[check_function_body_def, vyperContextTheory.type_env_all_modules_def,
         vyperContextTheory.type_env_def, FUNION_FEMPTY_2] >>
      qpat_assum `MAP expr_type defaults = _`
        (mp_tac o AP_TERM (Term `LENGTH : type list -> num`)) >>
      simp[LENGTH_DROP] >> decide_tac) >>
  metis_tac[vyperReadOnlySyntaxTheory.external_getter_defaults]
QED

Definition allocation_entries_from_code_def[local]:
  allocation_entries_from_code code s t <=>
    !id pair. FLOOKUP t.vs_allocas id = SOME pair ==>
      FLOOKUP s.vs_allocas id = SOME pair \/
      ?i. MEM i (state_insts code) /\ i.inst_opcode = ALLOCA /\ i.inst_id = id
End

Theorem allocation_entries_before[local]:
  allocation_entries_from_code code s t /\ s.vs_allocas = FEMPTY /\
  entry_alloca_ids first code /\ state_insts first = [] /\ code.cs_next_id <= limit ==>
  !id e. FLOOKUP t.vs_allocas id = SOME e ==> id < limit
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> rpt gen_tac >> strip_tac >>
  qpat_assum `allocation_entries_from_code code s t`
    (qspecl_then [`id`,`e`] mp_tac o REWRITE_RULE [allocation_entries_from_code_def]) >>
  asm_rewrite_tac[FLOOKUP_EMPTY, optionTheory.NOT_NONE_SOME] >> strip_tac >>
  qpat_assum `entry_alloca_ids first code`
    (qspec_then `i` mp_tac o CONJUNCT2 o REWRITE_RULE [entry_alloca_ids_def]) >>
  asm_rewrite_tac[MEM] >> strip_tac >>
  irule LESS_LESS_EQ_TRANS >> qexists_tac `code.cs_next_id` >> simp[]
QED

Theorem allocation_entries_from_code_compose[local]:
  allocation_entries_from_code mid s u /\ allocation_entries_from_code last u t /\
  cs_extends mid last ==> allocation_entries_from_code last s t
Proof
  rw[allocation_entries_from_code_def] >>
  metis_tac[state_insts_cs_extends, MEM_APPEND]
QED

Theorem allocation_entries_from_code_extend[local]:
  allocation_entries_from_code mid s t /\ cs_extends mid last ==>
  allocation_entries_from_code last s t
Proof
  rw[allocation_entries_from_code_def] >>
  metis_tac[state_insts_cs_extends, MEM_APPEND]
QED

Theorem checked_classified_defaults_length[local]:
  source_typing_ok tops am tx /\
  MEM (mut,nr,rr,name,args,defaults,ret,body) (FST (classify_functions tops)) ==>
  LENGTH defaults <= LENGTH args
Proof
  strip_tac >> Cases_on `defaults = []` >> simp[] >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_external_names_distinct] >>
  drule_all classified_external_source_lookup >> strip_tac >>
  `rawdefaults <> []` by fs[constSubstCorrectTheory.subst_consts_exprs_map] >>
  drule_all checked_external_defaults_parameters >>
  simp[constSubstCorrectTheory.subst_consts_exprs_map]
QED

Theorem grouped_defaults_selected_find[local]:
  group = package_external_group tops target tr keys
    (mut,nr,rr,name,args,defaults,ret,stmts) /\
  group = ExternalDefaults common entries specs off /\
  groups = pre ++ group::post /\
  groups = MAP (package_external_group tops target tr keys)
    (FST (classify_functions tops)) /\
  ALL_DISTINCT (MAP FST (grouped_selectors groups)) /\
  MEM (prefix,k) (abi_entries args defaults) /\
  abi_method_id (type_env tops) name (MAP SND prefix) = cd_selector cd /\
  4 <= LENGTH cd ==>
  FIND (\(n,_,_,_). calldata_method_id cd = n2w n) entries =
    SOME (cd_selector cd,external_prefix_label name k,
          min_calldata_size common.ec_env prefix 0,k)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `package_external_group tops target tr keys
     (mut,nr,rr,name,args,defaults,ret,stmts) = ExternalDefaults common entries specs off` by
    metis_tac[] >>
  drule_all grouped_default_entry_member >> strip_tac >>
  `EVERY (\(sel,_,_). sel < dimword (:256)) (grouped_selectors groups)` by
    (qpat_assum `groups = MAP _ _` SUBST1_TAC >> simp[packaged_grouped_selector_width]) >>
  drule cd_selector_method_id >> strip_tac >>
  `MEM (w2n (calldata_method_id cd),external_prefix_label name k,
       min_calldata_size common.ec_env prefix 0,k) entries` by metis_tac[] >>
  qpat_x_assum `group = ExternalDefaults _ _ _ _` SUBST_ALL_TAC >>
  qpat_x_assum `groups = pre ++ _` SUBST_ALL_TAC >>
  drule_all grouped_default_selector_route >> simp[]
QED

Theorem installed_group_allocas[local]:
  !specs ce sa sb vars ctx fn mid m s.
    compile_create_kwarg_allocas ce specs sa = (vars,sb) /\
    fn_has_code sa sb fn /\
    fresh_vars_wrt sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand mid s = SOME m ==>
    ?t. RTC (reject_prefix_step ctx fn) s t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        fresh_vars_wrt sb t /\ eval_operand mid t = SOME m /\
        ~t.vs_halted /\ t.vs_call_ctx = s.vs_call_ctx /\
        allocation_entries_from_code sb s t
Proof
  Induct
  >- (simp[compile_create_kwarg_allocas_def, comp_return_def] >>
      rpt strip_tac >> qexists_tac `s` >> simp[RTC_REFL, allocation_entries_from_code_def]) >>
  qx_gen_tac `kw` >> PairCases_on `kw` >> rpt gen_tac >>
  simp[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce kw1) sa` >>
  rename1 `compile_alloc_buffer (type_memory_bytes ce kw1) sa = (buf,sc)` >>
  Cases_on `compile_create_kwarg_allocas ce specs sc` >>
  rename1 `compile_create_kwarg_allocas ce specs sc = (rest,last)` >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `last = sb` by
    (qpat_x_assum `_ = (vars,sb)` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `fn_has_code sa sc fn /\ fn_has_code sc sb fn` by
    (irule (Q.SPECL [`sa`,`sc`,`sb`,`fn`] fn_has_code_split) >>
     simp[] >> conj_tac
     >- (mp_tac (Q.SPECL [`type_memory_bytes ce kw1`,`sa`] ci_mono_compile_alloc_buffer) >>
         simp[ci_mono_def]) >>
     mp_tac (Q.SPECL [`specs`,`ce`,`sc`] compile_create_kwarg_allocas_mono) >>
     simp[ci_mono_def]) >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA
       [Lit (n2w (type_memory_bytes ce kw1))] [out]` >>
  `sc.cs_current_bb = sa.cs_current_bb /\
   sc.cs_current_insts = sa.cs_current_insts ++ [inst] /\
   sc.cs_next_var = SUC sa.cs_next_var` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[Abbr `inst`, Abbr `out`, contextTheory.compile_alloc_buffer_def, emit_op_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >> strip_tac >>
     qpat_x_assum `_ = sc` (SUBST_ALL_TAC o SYM) >> simp[ADD1]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     qpat_assum `!i. i < LENGTH [inst] ==> _`
       (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `0`) >>
     first_assum ACCEPT_TAC) >>
  `?a. step_inst 0 ctx inst s = OK a /\
       a.vs_halted = s.vs_halted /\ a.vs_call_ctx = s.vs_call_ctx /\
       a.vs_current_bb = s.vs_current_bb /\ a.vs_labels = s.vs_labels /\
       !key. key <> out ==> lookup_var key a = lookup_var key s` by
    (Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> TRY (PairCases_on `x`) >>
     simp[Abbr `inst`, mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_alloca_def, eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qabbrev_tac `u = a with vs_inst_idx := SUC s.vs_inst_idx` >>
  `reject_prefix_step ctx fn s u` by
    (qspecl_then [`ctx`,`fn`,`s`,`u`,`bb`,`inst`,`a`] mp_tac reject_prefix_scalar >>
     simp[Abbr `inst`, Abbr `u`, mk_inst_def, reject_prefix_opcode_def, is_terminator_def]) >>
  `~u.vs_halted /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts` by
    simp[Abbr `u`] >>
  `fresh_vars_wrt sc u` by
    (simp[fresh_vars_wrt_def, Abbr `u`] >>
     rpt strip_tac >>
     `STRING #"%" (toString n) <> out` by simp[Abbr `out`] >>
     qpat_assum `!key. key <> out ==> _`
       (drule_then (mp_tac o REWRITE_RULE [lookup_var_def])) >>
     qpat_assum `fresh_vars_wrt sa s` (mp_tac o REWRITE_RULE [fresh_vars_wrt_def]) >>
     simp[FLOOKUP_DEF] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_SUC_REFL]) >>
  `eval_operand mid u = SOME m` by
    (Cases_on `mid` >> fs[eval_operand_def, Abbr `u`] >>
     rename1 `lookup_var key s = SOME m` >>
     `key <> out` by
       (qspecl_then [`sa`,`s`,`Var key`,`m`,`key`,`sa.cs_next_var`]
          mp_tac fresh_vars_wrt_eval_operand >> simp[Abbr `out`, eval_operand_def]) >>
     qpat_assum `!key. key <> out ==> _` (drule_then mp_tac) >> fs[lookup_var_def]) >>
  `cs_extends sc sb` by
    metis_tac[compile_create_kwarg_allocas_mono, ci_mono_def, SND] >>
  `MEM inst (state_insts sc)` by
    simp[state_insts_def, all_blocks_def, MEM_FLAT, MEM_MAP] >>
  `allocation_entries_from_code sc s u` by
    (simp[allocation_entries_from_code_def, Abbr `u`] >> gen_tac >> PairCases >> strip_tac >>
     `inst.inst_opcode <> INVOKE` by simp[Abbr `inst`, mk_inst_def] >>
     drule_all step_inst_alloca_lookup_origin >> strip_tac >> simp[] >>
     disj2_tac >> qexists_tac `inst` >> simp[]) >>
  first_x_assum (qspecl_then [`ce`,`sc`,`sb`,`rest`,`ctx`,`fn`,`mid`,`m`,`u`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> metis_tac[RTC_RULES, allocation_entries_from_code_compose]
QED

Theorem installed_group_entries_start[local]:
  compile_group_entries mid entries common vars off sa = ((),sb) /\
  fn_has_code sa sb fn /\ EVERY (\(_,name,_,_). ~internal_label_ok name) entries ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb
Proof
  Cases_on `entries`
  >- (simp[compile_group_entries_def, comp_return_def, fn_has_code_def] >> metis_tac[]) >>
  PairCases_on `h` >> simp[] >> strip_tac >>
  drule_all compile_group_entries_cons_layout >> metis_tac[]
QED

Theorem installed_group_entries_miss[local]:
  !entries mid common vars off sa sb ctx fn m s.
    compile_group_entries mid entries common vars off sa = ((),sb) /\
    fn_has_code sa sb fn /\
    EVERY (\(_,name,_,_). ~internal_label_ok name) entries /\
    (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    FIND (\(n,_,_,_). m = n2w n) entries = NONE /\
    fresh_vars_wrt sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand mid s = SOME m ==>
    ?t. RTC (reject_prefix_step ctx fn) s t /\ vars_pc_only s t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        fresh_vars_wrt sb t /\ eval_operand mid t = SOME m
Proof
  Induct
  >- (simp[compile_group_entries_def, comp_return_def, FIND_thm] >>
      rpt strip_tac >> qexists_tac `s` >> simp[RTC_REFL, vars_pc_only_refl]) >>
  qx_gen_tac `ge` >> PairCases_on `ge` >>
  rpt gen_tac >> simp[FIND_thm] >> strip_tac >>
  `m <> (n2w ge0 : bytes32)` by (strip_tac >> fs[]) >>
  drule_all compile_group_entries_cons_layout >>
  disch_then (qx_choosel_then [`next`,`next_state`,`checks`,`init`,`done`,`bb`]
    strip_assume_tac) >>
  `?target. lookup_block next fn.fn_blocks = SOME target` by
    (drule_at (Pat `compile_group_entries _ entries _ _ _ next_state = _`) installed_group_entries_start >>
     simp[]) >>
  `phi_prefix_length target.bb_instructions = 0` by
    (first_x_assum drule >> simp[]) >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  mp_tac (Q.INST [`id` |-> `sa.cs_next_id`, `next_id` |-> `sa.cs_next_id + 1`,
    `sel` |-> `ge0`, `yes` |-> `ge1`, `no` |-> `next`, `lbl` |-> `next`]
    reject_prefix_comparison) >>
  impl_tac >- fs[Abbr `out`] >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `~u.vs_halted /\ u.vs_labels = s.vs_labels` by
    fs[vars_pc_only_def, venom_state_component_equality] >>
  `fresh_vars_wrt next_state u` by
    (fs[fresh_vars_wrt_def] >> qx_gen_tac `n` >> strip_tac >>
     `STRING #"%" (toString n) <> out` by simp[Abbr `out`] >>
     qpat_x_assum `!p. p <> out ==> _`
       (qspec_then `STRING #"%" (toString n)` mp_tac) >>
     simp[lookup_var_def, FLOOKUP_DEF]) >>
  `eval_operand mid u = SOME m` by
    (Cases_on `mid` >> fs[eval_operand_def] >>
     rename1 `lookup_var key s = SOME m` >>
     `key <> out` by
       (qspecl_then [`sa`,`s`,`Var key`,`m`,`key`,`sa.cs_next_var`]
          mp_tac fresh_vars_wrt_eval_operand >> simp[Abbr `out`, eval_operand_def]) >>
     qpat_assum `!p. p <> out ==> _` (qspec_then `key` mp_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`mid`,`common`,`vars`,`off`,`next_state`,`sb`,`ctx`,`fn`,`m`,`u`] mp_tac) >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  metis_tac[RTC_TRANSITIVE, transitive_def, vars_pc_only_trans]
QED

Theorem installed_single_selector_miss[local]:
  compile_selector_checks mid [(sel,lbl)] sa = ((),sb) /\ fn_has_code sa sb fn /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand mid s = SOME m /\ m <> n2w sel ==>
  ?t. RTC (reject_prefix_step ctx fn) s t /\ vars_pc_only s t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      fresh_vars_wrt sb t /\ eval_operand mid t = SOME m
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all entryDispatchPtrTheory.compile_selector_checks_cons_layout >>
  disch_then (qx_choosel_then [`tail`,`match`,`next`,`bb`,`mb`] strip_assume_tac) >>
  `tail = sb` by fs[compile_selector_checks_def, comp_return_def] >>
  pop_assum SUBST_ALL_TAC >>
  `?target. lookup_block next fn.fn_blocks = SOME target` by
    fs[fn_has_code_def] >>
  `phi_prefix_length target.bb_instructions = 0` by metis_tac[] >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  mp_tac (Q.INST [`id` |-> `sa.cs_next_id`, `next_id` |-> `sa.cs_next_id + 1`,
    `sel` |-> `sel`, `yes` |-> `match`, `no` |-> `next`, `lbl` |-> `next`]
    reject_prefix_comparison) >>
  impl_tac >- fs[Abbr `out`] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  conj_tac >-
    (fs[fresh_vars_wrt_def] >> qx_gen_tac `n` >> strip_tac >>
     `STRING #"%" (toString n) <> out` by simp[Abbr `out`] >>
     qpat_x_assum `!key. key <> out ==> _`
       (qspec_then `STRING #"%" (toString n)` mp_tac) >>
     simp[lookup_var_def, FLOOKUP_DEF]) >>
  `t.vs_labels = s.vs_labels` by metis_tac[vars_pc_only_fields] >>
  Cases_on `mid` >> fs[eval_operand_def] >>
  rename1 `lookup_var key s = SOME m` >>
  `key <> out` by
    (qspecl_then [`sa`,`s`,`Var key`,`m`,`key`,`sa.cs_next_var`]
      mp_tac fresh_vars_wrt_eval_operand >> simp[Abbr `out`, eval_operand_def]) >>
  metis_tac[]
QED

Theorem installed_single_selector_hit[local]:
  compile_selector_checks mid [(sel,target.cs_current_bb)] sa = ((),sb) /\
  fn_has_code sa sb fn /\
  target.cs_current_insts = [] /\ sa.cs_next_var < target.cs_next_var /\
  (?bb. lookup_block target.cs_current_bb fn.fn_blocks = SOME bb) /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt target s /\ ~s.vs_halted /\ at_point sa s /\
  eval_operand mid s = SOME (n2w sel) ==>
  ?t. RTC (reject_prefix_step ctx fn) s t /\ vars_pc_only s t /\
      fresh_vars_wrt target t /\ at_point target t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `?b. lookup_block target.cs_current_bb fn.fn_blocks = SOME b`
    (qx_choose_then `bb` assume_tac) >>
  qpat_x_assum `at_point sa s` (strip_assume_tac o REWRITE_RULE [at_point_def]) >>
  drule_all entryDispatchPtrTheory.compile_selector_checks_cons_layout >>
  disch_then (qx_choosel_then [`tail`,`hit`,`next`,`b`,`mb`] strip_assume_tac) >>
  `phi_prefix_length mb.bb_instructions = 0 /\
   phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  mp_tac (Q.INST [`id` |-> `sa.cs_next_id`, `next_id` |-> `sa.cs_next_id + 1`,
    `ctx` |-> `ctx`, `s` |-> `s`, `mid` |-> `mid`,
    `sel` |-> `sel`, `yes` |-> `hit`, `no` |-> `next`, `lbl` |-> `hit`,
    `target` |-> `mb`, `bb` |-> `b`, `m` |-> `n2w sel:bytes32`]
    reject_prefix_comparison) >>
  impl_tac >- (once_asm_rewrite_tac[] >> simp[]) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `~u.vs_halted` by fs[vars_pc_only_def, venom_state_component_equality] >>
  `reject_prefix_step ctx fn u (jump_to target.cs_current_bb u)` by
    (irule reject_prefix_jump >> simp[get_instruction_def] >>
     qexists_tac `sa.cs_next_id + 2` >> simp[]) >>
  `fresh_vars_wrt target u` by
    (fs[fresh_vars_wrt_def] >> qx_gen_tac `n` >> strip_tac >>
     `STRING #"%" (toString n) <> out` by simp[Abbr `out`] >>
     qpat_assum `!p. p <> out ==> _`
       (qspec_then `STRING #"%" (toString n)` (mp_tac o REWRITE_RULE [lookup_var_def])) >>
     simp[FLOOKUP_DEF]) >>
  qexists_tac `jump_to target.cs_current_bb u` >>
  conj_tac >-
    (irule (REWRITE_RULE [transitive_def] RTC_TRANSITIVE) >>
     qexists_tac `u` >> simp[RTC_SINGLE]) >>
  simp[jump_to_def, at_point_def, fresh_vars_wrt_def] >>
  fs[vars_pc_only_def, venom_state_component_equality]
QED

Theorem installed_group_entries_selected[local]:
  !entries mid common (vars:(string # operand # type # expr) list) off sa sb ctx fn m s sel lbl mincd k.
    compile_group_entries mid entries common vars off sa = ((),sb) /\
    fn_has_code sa sb fn /\
    EVERY (\(_,name,_,_). ~internal_label_ok name) entries /\
    (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    FIND (\(n,_,_,_). m = n2w n) entries = SOME (sel,lbl,mincd,k) /\
    fresh_vars_wrt sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand mid s = SOME m ==>
    ?checks init done t.
      checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
      compile_entry_checks mincd common.ec_payable checks = ((),init) /\
      fn_has_code checks init fn /\
      compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label init =
        ((),done) /\ fn_has_code init done fn /\ cs_extends done sb /\
      init.cs_next_var <= sb.cs_next_var /\
      RTC (reject_prefix_step ctx fn) s t /\ vars_pc_only s t /\
      t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\ fresh_vars_wrt checks t
Proof
  Induct >- simp[FIND_thm] >>
  qx_gen_tac `ge` >> PairCases_on `ge` >>
  rpt gen_tac >> simp[FIND_thm] >> strip_tac >>
  drule_all compile_group_entries_cons_layout >>
  disch_then (qx_choosel_then [`next`,`next_state`,`checks`,`init`,`done`,`bb`]
    strip_assume_tac) >>
  qabbrev_tac `target_label = if m = n2w ge0 then ge1 else next` >>
  `?target. lookup_block target_label fn.fn_blocks = SOME target` by
    (simp[Abbr `target_label`] >> IF_CASES_TAC
     >- (qpat_x_assum `checks.cs_current_bb = ge1` (fn th => REWRITE_TAC [SYM th]) >>
         `cs_extends checks init` by
           (mp_tac (Q.SPECL [`ge2`, `common.ec_payable`, `checks`] compile_entry_checks_labels) >> simp[]) >>
         drule_all fn_has_code_start >> metis_tac[]) >>
     drule_at (Pat `compile_group_entries _ entries _ _ _ next_state = _`)
       installed_group_entries_start >> simp[]) >>
  `phi_prefix_length target.bb_instructions = 0` by metis_tac[] >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  mp_tac (Q.INST [`id` |-> `sa.cs_next_id`, `next_id` |-> `sa.cs_next_id + 1`,
    `sel` |-> `ge0`, `yes` |-> `ge1`, `no` |-> `next`, `lbl` |-> `target_label`]
    reject_prefix_comparison) >>
  impl_tac >- fs[Abbr `out`, Abbr `target_label`] >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `!st. sa.cs_next_var < st.cs_next_var ==> fresh_vars_wrt st u` by
    (simp[fresh_vars_wrt_def, GSYM finite_mapTheory.flookup_thm] >> rpt strip_tac >>
     `STRING #"%" (toString n) <> out` by simp[Abbr `out`] >>
     `n >= sa.cs_next_var` by decide_tac >>
     `FLOOKUP s.vs_vars (STRING #"%" (toString n)) = NONE` by
       fs[fresh_vars_wrt_def, finite_mapTheory.flookup_thm] >>
     qpat_assum `!p. p <> out ==> _`
       (qspec_then `STRING #"%" (toString n)` (mp_tac o REWRITE_RULE [lookup_var_def])) >>
     asm_rewrite_tac[]) >>
  Cases_on `m = n2w ge0`
  >- (`next_state.cs_next_var <= sb.cs_next_var` by
        metis_tac[compile_group_entries_ci_mono, ci_mono_def, SND] >>
      gvs[Abbr `target_label`] >> qexistsl_tac [`checks`,`init`,`done`,`u`] >> simp[]) >>
  `~u.vs_halted /\ u.vs_labels = s.vs_labels` by
    fs[vars_pc_only_def, venom_state_component_equality] >>
  `eval_operand mid u = SOME m` by
    (Cases_on `mid` >> fs[eval_operand_def] >>
     rename1 `lookup_var key s = SOME m` >>
     `key <> out` by
       (qspecl_then [`sa`,`s`,`Var key`,`m`,`key`,`sa.cs_next_var`]
          mp_tac fresh_vars_wrt_eval_operand >> simp[Abbr `out`, eval_operand_def]) >>
     qpat_assum `!p. p <> out ==> _` (qspec_then `key` mp_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`mid`,`common`,`vars`,`off`,`next_state`,`sb`,`ctx`,`fn`,
    `m`,`u`,`sel`,`lbl`,`mincd`,`k`] mp_tac) >>
  impl_tac >- (fs[Abbr `target_label`] >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`checked`,`initialized`,`finished`,`t`] strip_assume_tac) >>
  qexistsl_tac [`checked`,`initialized`,`finished`,`t`] >> simp[] >>
  metis_tac[RTC_TRANSITIVE, transitive_def, vars_pc_only_trans]
QED

Theorem installed_external_groups_miss[local]:
  !groups mid sa sb jobs ctx fn m s.
    compile_external_groups mid groups sa = (jobs,sb) /\ fn_has_code sa sb fn /\
    EVERY group_entry_labels_ok groups /\
    EVERY (\sel. m <> n2w (FST sel)) (grouped_selectors groups) /\
    (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    fresh_vars_wrt sa s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand mid s = SOME m ==>
    ?t. RTC (reject_prefix_step ctx fn) s t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        fresh_vars_wrt sb t /\ eval_operand mid t = SOME m /\
        ~t.vs_halted /\ t.vs_call_ctx = s.vs_call_ctx /\
        allocation_entries_from_code sb s t
Proof
  Induct >-
    (simp[compile_external_groups_def, comp_return_def] >>
     rpt strip_tac >> qexists_tac `s` >> simp[RTC_REFL, allocation_entries_from_code_def]) >>
  qx_gen_tac `group` >> Cases_on `group`
  >- (PairCases_on `p` >>
      simp[grouped_selectors_def, external_group_selectors_def] >>
      rpt gen_tac >> strip_tac >>
      drule_all compile_external_single_cons_layout >>
      disch_then (qx_choosel_then [`sc`,`rest`] strip_assume_tac) >>
      drule_all installed_single_selector_miss >>
      disch_then (qspec_then `ctx` (qx_choose_then `u` strip_assume_tac)) >>
      `~u.vs_halted /\ u.vs_call_ctx = s.vs_call_ctx /\ u.vs_allocas = s.vs_allocas` by
        fs[vars_pc_only_def, venom_state_component_equality] >>
      qpat_x_assum `!mid sa sb jobs ctx fn m s. _`
        (qspecl_then [`mid`,`sc`,`sb`,`rest`,`ctx`,`fn`,`m`,`u`] mp_tac) >>
      impl_tac >- (simp[grouped_selectors_def] >> first_assum ACCEPT_TAC) >>
      disch_then (qx_choose_then `t` strip_assume_tac) >>
      qexists_tac `t` >> simp[] >>
      fs[allocation_entries_from_code_def] >> metis_tac[RTC_TRANSITIVE, transitive_def]) >>
  rename1 `ExternalDefaults common entries specs off` >>
  simp[grouped_selectors_def, external_group_selectors_def, EVERY_APPEND] >>
  rpt gen_tac >> strip_tac >>
  `EVERY group_entry_labels_ok (ExternalDefaults common entries specs off::groups)` by simp[] >>
  drule_all compile_external_defaults_cons_layout >>
  disch_then (qx_choosel_then [`kwvars`,`sc`,`sd`,`rest`] strip_assume_tac) >>
  `EVERY (\(_,name,_,_). ~internal_label_ok name) entries` by
    fs[group_entry_labels_ok_def] >>
  `FIND (\(n,_,_,_). m = n2w n) entries = NONE` by
    (qpat_x_assum `EVERY _ (MAP _ entries)` mp_tac >>
     simp[mem2varBlockSimHelpersTheory.FIND_NONE_EVERY, EVERY_MAP,
       EVERY_MEM, combinTheory.o_DEF, pairTheory.FORALL_PROD]) >>
  drule_all installed_group_allocas >>
  disch_then (qspec_then `ctx` (qx_choose_then `u` strip_assume_tac)) >>
  `?v. RTC (reject_prefix_step ctx fn) u v /\ vars_pc_only u v /\
       v.vs_current_bb = sd.cs_current_bb /\ v.vs_inst_idx = LENGTH sd.cs_current_insts /\
       fresh_vars_wrt sd v /\ eval_operand mid v = SOME m` by
    (qspecl_then [`entries`,`mid`,`common`,`kwvars`,`off`,`sc`,`sd`,`ctx`,`fn`,`m`,`u`]
       mp_tac installed_group_entries_miss >> asm_rewrite_tac[]) >>
  `~v.vs_halted /\ v.vs_call_ctx = s.vs_call_ctx /\ v.vs_allocas = u.vs_allocas` by
    fs[vars_pc_only_def, venom_state_component_equality] >>
  qpat_x_assum `!mid sa sb jobs ctx fn m s. _`
    (qspecl_then [`mid`,`sd`,`sb`,`rest`,`ctx`,`fn`,`m`,`v`] mp_tac) >>
  impl_tac >- (simp[grouped_selectors_def] >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `cs_extends sc sd /\ cs_extends sd sb` by
    (fs[] >> metis_tac[compile_group_entries_extends, compile_external_groups_extends]) >>
  `allocation_entries_from_code sd s v` by
    (qpat_assum `allocation_entries_from_code sc s u`
       (mp_tac o REWRITE_RULE [allocation_entries_from_code_def]) >>
     simp[allocation_entries_from_code_def] >> metis_tac[state_insts_cs_extends, MEM_APPEND]) >>
  qexists_tac `t` >> simp[] >>
  metis_tac[RTC_TRANSITIVE, transitive_def, allocation_entries_from_code_compose]
QED

Theorem installed_external_groups_prefix[local]:
  compile_external_groups mid (pre ++ groups) sa = (jobs,sb) /\ fn_has_code sa sb fn /\
  EVERY group_entry_labels_ok (pre ++ groups) /\
  EVERY (\sel. m <> n2w (FST sel)) (grouped_selectors pre) /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand mid s = SOME m ==>
  ?pre_jobs rest cut t.
    compile_external_groups mid pre sa = (pre_jobs,cut) /\
    compile_external_groups mid groups cut = (rest,sb) /\
    jobs = pre_jobs ++ rest /\ fn_has_code cut sb fn /\
    RTC (reject_prefix_step ctx fn) s t /\ t.vs_call_ctx = s.vs_call_ctx /\
    allocation_entries_from_code cut s t /\ cs_extends cut sb /\
    fresh_vars_wrt cut t /\ ~t.vs_halted /\ eval_operand mid t = SOME m /\
    t.vs_current_bb = cut.cs_current_bb /\ t.vs_inst_idx = LENGTH cut.cs_current_insts
Proof
  strip_tac >> drule compile_external_groups_append >>
  disch_then (qx_choosel_then [`pre_jobs`,`rest`,`cut`] strip_assume_tac) >>
  `cs_extends sa cut /\ cs_extends cut sb` by
    (fs[EVERY_APPEND] >> metis_tac[compile_external_groups_extends]) >>
  `fn_has_code sa cut fn /\ fn_has_code cut sb fn` by metis_tac[fn_has_code_split] >>
  fs[EVERY_APPEND] >>
  mp_tac (Q.SPECL [`pre`,`mid`,`sa`,`cut`,`pre_jobs`,`ctx`,`fn`,`m`,`s`]
    installed_external_groups_miss) >> asm_rewrite_tac[] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[]
QED

Theorem installed_defaults_group_selected[local]:
  compile_external_groups mid (ExternalDefaults common entries specs off::groups) sa = (jobs,sb) /\
  fn_has_code sa sb fn /\
  EVERY group_entry_labels_ok (ExternalDefaults common entries specs off::groups) /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  FIND (\(n,_,_,_). m = n2w n) entries = SOME (sel,lbl,mincd,k) /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand mid s = SOME m ==>
  ?vars rest checks init done t.
    jobs = ExternalCommonJob common vars::rest /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    compile_entry_checks mincd common.ec_payable checks = ((),init) /\
    fn_has_code checks init fn /\
    compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label init = ((),done) /\
    fn_has_code init done fn /\ cs_extends done sb /\ init.cs_next_var <= sb.cs_next_var /\
    RTC (reject_prefix_step ctx fn) s t /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\ fresh_vars_wrt checks t /\ ~t.vs_halted /\
    allocation_entries_from_code sb s t /\
    MAP (\(n,_,ty,e). (n,ty,e)) vars = specs
Proof
  strip_tac >> drule_all compile_external_defaults_cons_layout >>
  disch_then (qx_choosel_then [`vars`,`sc`,`sd`,`rest`] strip_assume_tac) >>
  drule_all installed_group_allocas >>
  disch_then (qspec_then `ctx` (qx_choose_then `u` strip_assume_tac)) >>
  `EVERY (\(_,name,_,_). ~internal_label_ok name) entries` by fs[group_entry_labels_ok_def] >>
  mp_tac (Q.SPECL [`entries`,`mid`,`common`,`vars`,`off`,`sc`,`sd`,`ctx`,`fn`,
    `m`,`u`,`sel`,`lbl`,`mincd`,`k`] installed_group_entries_selected) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`checks`,`init`,`done`,`t`] strip_assume_tac) >>
  `t.vs_call_ctx = u.vs_call_ctx /\ ~t.vs_halted /\ t.vs_allocas = u.vs_allocas` by
    fs[vars_pc_only_def, venom_state_component_equality] >>
  `cs_extends sd sb /\ sd.cs_next_var <= sb.cs_next_var` by
    metis_tac[compile_external_groups_ci_mono, ci_mono_def, SND] >>
  `init.cs_next_var <= sb.cs_next_var` by decide_tac >>
  `cs_extends sc sd` by (fs[group_entry_labels_ok_def] >> metis_tac[compile_group_entries_extends]) >>
  `allocation_entries_from_code sc s t` by fs[allocation_entries_from_code_def] >>
  `MAP (\(n,_,ty,e). (n,ty,e)) vars = specs` by
    metis_tac[groupedKeywordDecodeTheory.compile_create_kwarg_allocas_preserves_specs] >>
  qexistsl_tac [`vars`,`rest`,`checks`,`init`,`done`,`t`] >> simp[] >>
  metis_tac[RTC_TRANSITIVE, transitive_def, cs_extends_trans,
    allocation_entries_from_code_extend]
QED

Theorem selected_group_dispatch_prefix[local]:
  compile_group_dispatch_linear groups fl sf = (jobs,sd) /\
  fn_has_code sf sd fn /\ EVERY group_entry_labels_ok groups /\
  4 <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  fresh_vars_wrt sf s /\ ~s.vs_halted /\ at_point sf s /\
  groups = pre ++ group::post /\
  EVERY (\entry. calldata_method_id s.vs_call_ctx.cc_calldata <> n2w (FST entry))
      (grouped_selectors pre) /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?mid cut r pre_jobs rest t.
    jobs = pre_jobs ++ rest /\
    compile_external_groups mid (group::post) cut = (rest,r) /\
    fn_has_code cut r fn /\ cs_extends r sd /\ r.cs_next_var <= sd.cs_next_var /\
    RTC (reject_prefix_step u.cu_context fn) s t /\ t.vs_call_ctx = s.vs_call_ctx /\
    fresh_vars_wrt cut t /\ ~t.vs_halted /\ at_point cut t /\
    allocation_entries_from_code sd s t /\
    eval_operand mid t = SOME (calldata_method_id s.vs_call_ctx.cc_calldata)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `groups = pre ++ _` SUBST_ALL_TAC >>
  qpat_x_assum `at_point sf s` (strip_assume_tac o REWRITE_RULE [at_point_def]) >>
  mp_tac (Q.INST [`groups` |-> `pre ++ group::post`] installed_grouped_long_dispatch_prefix) >>
  simp[at_point_def] >>
  disch_then (qx_choosel_then [`q`,`r`,`v`] strip_assume_tac) >>
  `~v.vs_halted /\ v.vs_call_ctx = s.vs_call_ctx /\ v.vs_allocas = s.vs_allocas` by
    fs[vars_pc_only_def, venom_state_component_equality] >>
  mp_tac (Q.INST [`groups` |-> `group::post`, `sa` |-> `q`, `sb` |-> `r`,
    `s` |-> `v`, `ctx` |-> `u.cu_context`,
    `m` |-> `calldata_method_id s.vs_call_ctx.cc_calldata`,
    `mid` |-> `Var (STRING #"%" (toString (sf.cs_next_var + 4)))`]
    installed_external_groups_prefix) >>
  simp[] >> asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`pre_jobs`,`rest`,`cut`,`t`] strip_assume_tac) >>
  qexistsl_tac [`Var (STRING #"%" (toString (sf.cs_next_var + 4)))`,
    `cut`,`r`,`pre_jobs`,`rest`,`t`] >>
  simp[at_point_def] >>
  conj_tac
  >- (irule (REWRITE_RULE [transitive_def] RTC_TRANSITIVE) >>
      qexists_tac `v` >> simp[]) >>
  irule allocation_entries_from_code_extend >> qexists_tac `cut` >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  rewrite_tac[allocation_entries_from_code_def] >>
  qpat_assum `v.vs_allocas = s.vs_allocas` (fn eq =>
    qpat_assum `allocation_entries_from_code cut v t`
      (ACCEPT_TAC o PURE_REWRITE_RULE [allocation_entries_from_code_def, eq]))
QED

Theorem installed_group_default_checks_reject[local]:
  compile_group_dispatch_linear groups fl sf = (jobs,sd) /\
  fn_has_code sf sd fn /\ EVERY group_entry_labels_ok groups /\
  4 <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  fresh_vars_wrt sf s /\ ~s.vs_halted /\ at_point sf s /\
  groups = pre ++ ExternalDefaults common entries specs off::post /\
  EVERY (\entry. calldata_method_id s.vs_call_ctx.cc_calldata <> n2w (FST entry))
      (grouped_selectors pre) /\
  (!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  FIND (\(n,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w n) entries =
    SOME (sel,lbl,mincd,k) /\
  ((~common.ec_payable /\ s.vs_call_ctx.cc_callvalue <> 0w) \/
   (4 < mincd /\ LENGTH s.vs_call_ctx.cc_calldata < mincd /\ mincd < dimword (:256))) ==>
  ?z. RTC (reject_prefix_step u.cu_context fn) s z /\
      reject_prefix_terminal u.cu_context fn z
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac (Q.INST [`group` |-> `ExternalDefaults common entries specs off`]
    selected_group_dispatch_prefix) >>
  asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`mid`,`cut`,`r`,`pre_jobs`,`rest`,`t`] strip_assume_tac) >>
  `EVERY group_entry_labels_ok (ExternalDefaults common entries specs off::post)` by
    fs[EVERY_APPEND] >>
  qpat_x_assum `at_point cut t` (strip_assume_tac o REWRITE_RULE [at_point_def]) >>
  mp_tac (Q.INST [`groups` |-> `post`,`sa` |-> `cut`,`sb` |-> `r`,
    `jobs` |-> `rest`,`ctx` |-> `u.cu_context`,`s` |-> `t`,
    `m` |-> `calldata_method_id s.vs_call_ctx.cc_calldata`]
    installed_defaults_group_selected) >>
  asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`vars`,`tail`,`checks`,`init`,`done`,`v`] strip_assume_tac) >>
  mp_tac (Q.INST [`m` |-> `mincd`,`pay` |-> `common.ec_payable`,
    `sa` |-> `checks`,`sb` |-> `init`,`s` |-> `v`,`ctx` |-> `u.cu_context`]
    installed_entry_checks_reject_prefix) >>
  asm_rewrite_tac[LENGTH] >>
  disch_then (qx_choose_then `z` strip_assume_tac) >>
  qexists_tac `z` >> simp[] >> metis_tac[RTC_TRANSITIVE, transitive_def]
QED

Theorem runtime_reject_invariant_excludes_fmp[local]:
  lower_vyper_runtime_unit tops rp = SOME u /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME entry /\
  start = (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>) /\
  P start /\ (!t i. P t /\ active_inst entry i t ==> reject_prefix_opcode i) /\
  (!t v. P t /\ reject_prefix_step u.cu_context entry t v ==> P v) /\
  raw_reachable vs u.cu_context fn inst s ==>
  ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >> gvs[] >>
  drule_all lower_vyper_runtime_unit_entry_label >> strip_tac >>
  `?bb. lookup_block "__entry" entry.fn_blocks = SOME bb` by
    (Cases_on `entry.fn_blocks` >> fs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
  drule_all lower_vyper_runtime_unit_block_phi >> strip_tac >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `enters_block entry start start` by
    (simp[enters_block_def, Abbr `start`] >>
     Cases_on `bb.bb_instructions` >> gvs[eval_phis_def, phi_prefix_length_def, AllCaseEqs()]) >>
  drule reject_prefix_invariant_reachable >>
  disch_then (qspecl_then [`"__entry"`,`entry`,`"__entry"`,`start`,`P`] mp_tac) >>
  simp[] >> impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> drule_all runtime_reachable_raw_fmp_opcode >>
  fs[reject_prefix_opcode_def]
QED

Theorem grouped_runtime_reject_dispatch_inputs[local]:
  lower_vyper_runtime_unit tops rp = SOME u /\
  source_typing_ok tops am tx /\ initial_venom_state_rel tops am tx vs /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  s = (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>) ==>
  ?groups fn fl sf jobs sd sx final art.
    groups = MAP (package_external_group tops rp.rpol_target T
      (K global_nonreentrant_slot)) (FST (classify_functions tops)) /\
    check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
    lookup_function "__entry" u.cu_context.ctx_functions = SOME fn /\
    compile_group_dispatch_linear groups fl sf = (jobs,sd) /\
    compile_external_jobs jobs sd = ((),sx) /\
    EVERY group_job_label_ok jobs /\
    fn_has_code sf sd fn /\ fn_has_code sd sx fn /\ EVERY group_entry_labels_ok groups /\
    fresh_vars_wrt sf s /\ ~s.vs_halted /\ at_point sf s /\ s.vs_call_ctx = vs.vs_call_ctx /\
    s.vs_allocas = FEMPTY /\ sf.cs_current_insts = [] /\ state_insts sf = [] /\
    4 <= LENGTH s.vs_call_ctx.cc_calldata /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    ALL_DISTINCT (fn_labels fn) /\ no_phi_fn fn /\ fn_inst_ids_distinct fn /\
    cs_extends sf sd /\ cs_extends sd final /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks final)) /\
    shape_state sd /\ EVERY reject_prefix_opcode (state_insts sd) /\
    MEM fn u.cu_context.ctx_functions /\ unit_alloca_budget u.cu_context < 2 ** 254 /\
    alloca_inv s /\
    s.vs_alloca_next + remaining_alloca_budget (fn_insts fn) s <= unit_alloca_budget u.cu_context
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `s = start` by simp[Abbr `start`] >>
  qpat_x_assum `s = start` SUBST_ALL_TAC >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  rename1 `lookup_function "__entry" _ = SOME fn` >>
  drule_all lower_runtime_grouped_packages >>
  disch_then (qx_choosel_then [`groups`,`ints`,`fallback`] strip_assume_tac) >>
  drule_all run_grouped_lowering_dispatch_code >>
  disch_then (qx_choosel_then [`sf`,`fl`,`jobs`,`sd`,`sx`,`sn`,`final`] strip_assume_tac) >>
  `?art. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
    fs[source_typing_ok_def] >>
  `MEM fn u.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `ALL_DISTINCT (fn_labels fn)` by
    (qpat_assum `lowering_context_ok _`
      (strip_assume_tac o REWRITE_RULE [lowering_context_ok_def]) >>
     qpat_assum `EVERY (\f. ALL_DISTINCT _ /\ fn_has_entry f) _`
       (qspec_then `fn` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
  `no_phi_fn fn` by
    (simp[no_phi_fn_def, EVERY_MEM] >> rpt strip_tac >>
     irule lowering_context_ok_block_phi >>
     metis_tac[MEM_lookup_block, fn_labels_def]) >>
  `fn_inst_ids_distinct fn` by
    (drule lowering_context_ok_static_integrity >> strip_tac >>
     drule_all ctx_inst_ids_distinct_fn >>
     simp[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id]) >>
  `unit_alloca_budget u.cu_context < 2 ** 254` by
    (drule lowering_context_ok_static_headroom >> decide_tac) >>
  `fresh_label_output "fallback" 0 = fl` by
    (qpat_assum `fresh_label "fallback" _ = _`
      (mp_tac o AP_TERM ``FST : string # compile_state -> string``) >>
     simp[NoAsms, fresh_label_def, initial_compile_state_def]) >>
  `sf.cs_blocks = [] /\ sf.cs_next_var = 0 /\ state_insts sf = []` by
    (drule fresh_label_props >>
     simp[initial_compile_state_def, state_insts_def, all_blocks_def] >>
     strip_tac >> simp[]) >>
  `shape_state sf` by
    (irule shape_state_same_code >> qexists_tac `initial_compile_state "__entry"` >>
     simp[shape_state_initial_compile_state, initial_compile_state_def]) >>
  `jump_label_ok fl /\ ~label_sfx "dispatch" fl` by
    (qpat_assum `fresh_label_output "fallback" 0 = fl` (SUBST1_TAC o SYM) >>
     simp[jump_label_ok_def, compiler_label_def, fresh_label_output_in_future,
          label_sfx_def] >>
     metis_tac[fresh_label_output_inj, EVAL ``"fallback" <> "dispatch"`` |> EQT_ELIM]) >>
  `shape_state sd` by metis_tac[checked_group_dispatch_shape] >>
  `EVERY reject_prefix_opcode (state_insts sd)` by
    (drule_all checked_group_dispatch_safe_opcodes >>
     simp[EVERY_MEM, reject_prefix_opcode_def] >> metis_tac[]) >>
  `fresh_vars_wrt sf start /\ ~start.vs_halted /\ LENGTH start.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`,`"__entry"`,`sf`] mp_tac) >> simp[Abbr `start`]) >>
  `start.vs_allocas = FEMPTY /\ start.vs_alloca_next = 0` by
    fs[Abbr `start`, initial_venom_state_rel_def] >>
  qexistsl_tac [`groups`,`fn`,`fl`,`sf`,`jobs`,`sd`,`sx`,`final`,`art`] >>
  simp[Abbr `start`, at_point_def, alloca_inv_def, allocas_non_overlapping_def,
       alloca_next_valid_def, FLOOKUP_DEF, remaining_alloca_budget_unit]
QED

Theorem grouped_legacy_reject_terminal[local]:
  compile_group_dispatch_linear groups fl sf = (jobs,sd) /\
  compile_external_jobs jobs sd = ((),sx) /\
  EVERY group_job_label_ok jobs /\
  fn_has_code sf sd fn /\ fn_has_code sd sx fn /\ EVERY group_entry_labels_ok groups /\
  groups = pre ++ ExternalSingle (sel,"fn_" ++ name,tz)
    ("fn_" ++ name,ce,build_positional_args ce args,m,pay,nr,key,tr,view,stmts,rt)::post /\
  EVERY (\e. calldata_method_id s.vs_call_ctx.cc_calldata <> n2w (FST e))
    (grouped_selectors pre) /\
  calldata_method_id s.vs_call_ctx.cc_calldata = n2w sel /\
  fresh_vars_wrt sf s /\ ~s.vs_halted /\ at_point sf s /\
  s.vs_allocas = FEMPTY /\ state_insts sf = [] /\
  4 <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(n,ty) tv.
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars n = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs /\
  m = 4 + SUM (MAP tv_abi_size tvs) /\ m < dimword (:256) /\
  (LENGTH s.vs_call_ctx.cc_calldata < m \/
   calldata_decode_args s.vs_call_ctx.cc_calldata tvs 0 = NONE) /\
  no_phi_fn fn /\ fn_inst_ids_distinct fn /\
  MEM fn u.cu_context.ctx_functions /\ unit_alloca_budget u.cu_context < 2 ** 254 /\
  alloca_inv s /\
  s.vs_alloca_next + remaining_alloca_budget (fn_insts fn) s <= unit_alloca_budget u.cu_context ==>
  ?z. RTC (reject_prefix_step u.cu_context fn) s z /\ reject_prefix_terminal u.cu_context fn z
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (fs[no_phi_fn_def, EVERY_MEM] >> rpt strip_tac >>
     drule lookup_block_MEM >> simp[]) >>
  qabbrev_tac `pk = ("fn_" ++ name,ce,build_positional_args ce args,m,pay,nr,key,tr,view,stmts,rt)` >>
  mp_tac (Q.INST [`group` |-> `ExternalSingle (sel,"fn_" ++ name,tz) pk`]
    selected_group_dispatch_prefix) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`mid`,`cut`,`r`,`pre_jobs`,`rest`,`t`] strip_assume_tac) >>
  `EVERY group_entry_labels_ok post` by fs[EVERY_APPEND] >>
  drule_all compile_external_single_cons_layout >>
  disch_then (qx_choosel_then [`cmpend`,`tail`] strip_assume_tac) >>
  `MEM (ExternalLegacyJob pk) jobs` by
    (qpat_assum `jobs = _` SUBST1_TAC >> simp[MEM_APPEND, Abbr `pk`]) >>
  drule_all compile_external_legacy_job_interval >>
  disch_then (qx_choosel_then [`legacy_begin`,`legacy_end`,`jobs_pre`,`jobs_post`] strip_assume_tac) >>
  `sd.cs_next_id <= legacy_begin.cs_next_id /\ sd.cs_next_var <= legacy_begin.cs_next_var` by
    metis_tac[compile_external_jobs_ci_mono, ci_mono_def, SND] >>
  `MEM ("fn_" ++ name,ce,build_positional_args ce args,m,pay,nr,key,tr,view,stmts,rt) [pk]` by
    simp[Abbr `pk`] >>
  drule_all external_fn_selected_check_intervals >>
  disch_then (qx_choosel_then [`opened`,`checked`,`cef`,`last`,`bodyend`] strip_assume_tac) >>
  `cs_extends checked last` by metis_tac[registration_compile_ci_mono, ci_mono_def, SND] >>
  `fn_has_code opened checked fn /\ fn_has_code checked last fn` by
    metis_tac[fn_has_code_mid, cs_extends_trans] >>
  `?bb. lookup_block opened.cs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[fn_has_code_start] >>
  `cmpend.cs_next_var <= r.cs_next_var` by
    metis_tac[compile_external_groups_ci_mono, ci_mono_def, SND] >>
  `cut.cs_next_var < cmpend.cs_next_var` by
    (drule entryDispatchCountersTheory.compile_selector_checks_next_var_exact >>
     simp[]) >>
  `cut.cs_next_var < opened.cs_next_var /\ fresh_vars_wrt opened t` by
    (conj_tac >- decide_tac >>
     irule fresh_vars_wrt_mono >> qexists_tac `cut` >> simp[] >> decide_tac) >>
  `opened.cs_next_id <= checked.cs_next_id /\ legacy_begin.cs_next_id <= opened.cs_next_id` by
    (conj_tac
     >- metis_tac[compile_entry_checks_ci_mono, ci_mono_def, SND] >>
     `pre' = []` by
       (qpat_assum `[pk] = _` mp_tac >> Cases_on `pre'` >> simp[]) >>
     qpat_x_assum `pre' = []` SUBST_ALL_TAC >>
     qpat_x_assum `compile_external_fn_bodies [] legacy_begin = _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_external_fn_bodies_def, comp_return_def]) >>
     drule new_block_props >> simp[]) >>
  `compile_selector_checks mid [(sel,opened.cs_current_bb)] cut = ((),cmpend) /\
   eval_operand mid t = SOME (n2w sel)` by
    (conj_tac
     >- (qpat_assum `opened.cs_current_bb = _` (pure_once_rewrite_tac o single) >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `calldata_method_id s.vs_call_ctx.cc_calldata = n2w sel`
       (pure_once_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  pop_assum strip_assume_tac >>
  mp_tac (Q.INST [`target` |-> `opened`,`sa` |-> `cut`,`sb` |-> `cmpend`,
    `s` |-> `t`,`ctx` |-> `u.cu_context`] installed_single_selector_hit) >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  `RTC (reject_prefix_step u.cu_context fn) s v` by metis_tac[RTC_TRANSITIVE, transitive_def] >>
  `v.vs_allocas = t.vs_allocas` by
    (qpat_assum `vars_pc_only t v`
      (mp_tac o AP_TERM ``\w:venom_state. w.vs_allocas`` o REWRITE_RULE [vars_pc_only_def]) >>
     simp[venom_state_accfupds]) >>
  `entry_alloca_ids sf sd` by metis_tac[entry_ids_group_dispatch] >>
  `!id e. FLOOKUP v.vs_allocas id = SOME e ==> id < checked.cs_next_id` by
    (qpat_assum `v.vs_allocas = t.vs_allocas` (pure_once_rewrite_tac o single) >>
     mp_tac (Q.INST [`code` |-> `sd`,`first` |-> `sf`,`limit` |-> `checked.cs_next_id`]
       allocation_entries_before) >>
     impl_tac >- (asm_rewrite_tac[] >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  drule_at (Pat `RTC _ s v`) reject_prefix_allocation_frame >> simp[] >> strip_tac >>
  `v.vs_alloca_next <= unit_alloca_budget u.cu_context` by decide_tac >>
  qpat_assum `at_point opened v` (strip_assume_tac o REWRITE_RULE [at_point_def]) >>
  `?z. RTC (reject_prefix_step u.cu_context fn) v z /\
       reject_prefix_terminal u.cu_context fn z` by
    (mp_tac (Q.INST [`ce` |-> `ce`,`cef` |-> `cef`,`checked` |-> `checked`,
       `env` |-> `env`,`last` |-> `last`,`m` |-> `m`,`name` |-> `name`,
       `opened` |-> `opened`,`pay` |-> `pay`,`args` |-> `args`,`tvs` |-> `tvs`,
       `fn` |-> `fn`,`ctx` |-> `u.cu_context`,`t` |-> `v`]
       (SPEC_ALL legacy_checks_registration_reject_prefix)) >>
     impl_tac >- (asm_simp_tac bool_ss [LENGTH] >> metis_tac[]) >>
     disch_then ACCEPT_TAC) >>
  qexists_tac `z` >> simp[] >> metis_tac[RTC_TRANSITIVE, transitive_def]
QED

Theorem grouped_positional_reject_invariant[local]:
  compile_group_dispatch_linear groups fl sf = (jobs,sd) /\
  compile_external_jobs jobs sd = ((),sx) /\
  EVERY group_job_label_ok jobs /\
  fn_has_code sf sd fn /\ fn_has_code sd sx fn /\ EVERY group_entry_labels_ok groups /\
  groups = pre ++ ExternalDefaults common entries specs off::post /\
  EVERY (\e. calldata_method_id s.vs_call_ctx.cc_calldata <> n2w (FST e))
    (grouped_selectors pre) /\
  FIND (\(n,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w n) entries =
    SOME (sel,lbl,mincd,k) /\
  fresh_vars_wrt sf s /\ ~s.vs_halted /\ at_point sf s /\
  s.vs_allocas = FEMPTY /\ state_insts sf = [] /\
  4 <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  (common.ec_payable \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  mincd <= LENGTH s.vs_call_ctx.cc_calldata /\
  common.ec_common_label = external_common_label name /\
  common.ec_pos_args = build_positional_args common.ec_env (TAKE n args) /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) tv.
    abi_decoder_coherent common.ec_env env common.ec_env.ce_struct_fields ty tv /\
    (?loc. FLOOKUP common.ec_env.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs /\
  LENGTH defaults <= LENGTH args /\ n = LENGTH args - LENGTH defaults /\
  specs = MAP (\((n,ty),e). (n,ty,e)) (ZIP (DROP n args,defaults)) /\
  4 + SUM (MAP tv_abi_size (TAKE n tvs)) <= LENGTH s.vs_call_ctx.cc_calldata /\
  calldata_decode_args s.vs_call_ctx.cc_calldata (TAKE n tvs) 0 = NONE /\
  ALL_DISTINCT (fn_labels fn) /\ no_phi_fn fn /\ fn_inst_ids_distinct fn /\
  cs_extends sd final /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks final)) /\
  shape_state sd /\ EVERY reject_prefix_opcode (state_insts sd) /\
  MEM fn u.cu_context.ctx_functions /\ unit_alloca_budget u.cu_context < 2 ** 254 /\
  alloca_inv s /\
  s.vs_alloca_next + remaining_alloca_budget (fn_insts fn) s <= unit_alloca_budget u.cu_context ==>
  ?P. P s /\ (!t i. P t /\ active_inst fn i t ==> reject_prefix_opcode i) /\
    (!t v. P t /\ reject_prefix_step u.cu_context fn t v ==> P v)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!name bb. lookup_block name fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (fs[no_phi_fn_def, EVERY_MEM] >> rpt strip_tac >>
     drule lookup_block_MEM >> simp[]) >>
  mp_tac (Q.INST [`group` |-> `ExternalDefaults common entries specs off`]
    selected_group_dispatch_prefix) >>
  asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`mid`,`cut`,`r`,`pre_jobs`,`rest`,`t`] strip_assume_tac) >>
  `EVERY group_entry_labels_ok (ExternalDefaults common entries specs off::post)` by
    fs[EVERY_APPEND] >>
  qpat_x_assum `at_point cut t` (strip_assume_tac o REWRITE_RULE [at_point_def]) >>
  mp_tac (Q.INST [`groups` |-> `post`,`sa` |-> `cut`,`sb` |-> `r`,
    `jobs` |-> `rest`,`ctx` |-> `u.cu_context`,`s` |-> `t`,
    `m` |-> `calldata_method_id s.vs_call_ctx.cc_calldata`]
    installed_defaults_group_selected) >>
  asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`vars`,`tail`,`checks`,`init`,`done`,`v`] strip_assume_tac) >>
  `RTC (reject_prefix_step u.cu_context fn) s v` by
    metis_tac[RTC_TRANSITIVE, transitive_def] >>
  `init.cs_next_var <= sd.cs_next_var` by decide_tac >>
  `cs_extends done sd` by metis_tac[cs_extends_trans] >>
  `allocation_entries_from_code sd v v` by simp[allocation_entries_from_code_def] >>
  `allocation_entries_from_code sd t v` by
    (irule allocation_entries_from_code_compose >> qexistsl_tac [`r`,`v`] >> simp[]) >>
  `allocation_entries_from_code sd s v` by
    (irule allocation_entries_from_code_compose >> qexistsl_tac [`sd`,`t`] >>
     simp[cs_extends_refl]) >>
  qpat_x_assum `jobs = pre_jobs ++ rest` SUBST_ALL_TAC >>
  qpat_x_assum `rest = ExternalCommonJob common vars::tail` SUBST_ALL_TAC >>
  drule_all compile_external_common_job_interval >> strip_tac >>
  rename1 `new_block common.ec_common_label common_begin = (_,entry)` >>
  rename1 `compile_register_positional_args _ _ 4 entry = (cef,registered)` >>
  rename1 `compile_guarded_body cef _ _ _ _ _ _ registered = ((),bodyend)` >>
  `fn_has_code entry registered fn` by
    metis_tac[fn_has_code_mid, cs_extends_trans] >>
  `entry.cs_current_insts = [] /\
   entry.cs_current_bb = common.ec_common_label /\
   common_begin.cs_next_id = entry.cs_next_id /\ common_begin.cs_next_var = entry.cs_next_var` by
    (drule new_block_props >> simp[]) >>
  `ci_mono sd common_begin` by
    (qpat_assum `compile_external_jobs pre_jobs sd = ((),common_begin)` (fn eq =>
       ACCEPT_TAC (REWRITE_RULE [eq,SND]
         (Q.SPECL [`pre_jobs`,`sd`] compile_external_jobs_ci_mono)))) >>
  `sd.cs_next_id <= entry.cs_next_id /\ sd.cs_next_var <= entry.cs_next_var` by
    (qpat_assum `ci_mono sd common_begin` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp[]) >>
  `entry.cs_current_bb NOTIN decode_label_range entry.cs_next_label registered.cs_next_label` by
    simp[external_common_label_def, decode_label_range_def, fresh_label_output_def] >>
  drule_all compile_entry_point_kwargs_layout >>
  disch_then (qx_choose_then `kwend` strip_assume_tac) >>
  `cs_extends init kwend /\ cs_extends kwend sd` by
    (conj_tac >- metis_tac[compile_init_kwargs_ci_mono, ci_mono_def, SND] >>
     metis_tac[ci_mono_emit_inst, ci_mono_def, SND, cs_extends_trans]) >>
  `entry_alloca_ids sf sd` by metis_tac[entry_ids_group_dispatch] >>
  `!i. MEM i (fn_insts (frag_observer init kwend fn 0)) ==>
   (i.inst_opcode = ALLOCA ==> i.inst_id < entry.cs_next_id) /\
   EVERY (not_fresh_at entry) i.inst_outputs` by
    (gen_tac >> strip_tac >> irule observer_instructions_before_common_entry >>
     qexistsl_tac [`sd`,`fn`,`init`,`kwend`,`sf`] >> asm_rewrite_tac[]) >>
  `MAP (\(name,_,_,_). name) vars = MAP FST (DROP n args)` by
    (qpat_assum `n = LENGTH args - LENGTH defaults` SUBST1_TAC >>
     irule grouped_kwarg_names >> simp[] >> qexists_tac `specs` >> simp[]) >>
  drule_all registered_kwarg_positional_metadata >> strip_tac >>
  mp_tac (Q.INST [`sa` |-> `checks`,`sb` |-> `init`,`m` |-> `mincd`,
    `pay` |-> `common.ec_payable`,`ctx` |-> `u.cu_context`,`s` |-> `v`]
     installed_entry_checks_continue) >>
  impl_tac >- (asm_simp_tac bool_ss [EVERY_DEF, LENGTH] >> metis_tac[]) >>
  disch_then (qx_choosel_then [`v'`,`w`] strip_assume_tac) >>
  `RTC (reject_prefix_step u.cu_context fn) s w` by
    metis_tac[RTC_TRANSITIVE, transitive_def] >>
  `w.vs_allocas = v.vs_allocas /\ fresh_vars_wrt init w /\ at_point init w` by
    fs[vars_pc_only_def, venom_state_component_equality, fresh_vars_wrt_def, at_point_def] >>
  `fresh_vars_wrt entry w` by
    (irule fresh_vars_wrt_mono >> qexists_tac `init` >> simp[] >> decide_tac) >>
  `!id e. FLOOKUP w.vs_allocas id = SOME e ==> id < entry.cs_next_id` by
    (qpat_assum `w.vs_allocas = v.vs_allocas` (pure_once_rewrite_tac o single) >>
     mp_tac (Q.INST [`code` |-> `sd`,`first` |-> `sf`,`t` |-> `v`,
       `limit` |-> `entry.cs_next_id`]
       allocation_entries_before) >> asm_rewrite_tac[]) >>
  drule_at (Pat `RTC _ s w`) reject_prefix_allocation_frame >> simp[] >> strip_tac >>
  qabbrev_tac `reg_env = compile_register_kwarg_vars common.ec_env vars` >>
  qabbrev_tac `pos_args = TAKE n args` >>
  qabbrev_tac `pos_tvs = TAKE n tvs` >>
  mp_tac (Q.INST [`ce` |-> `common.ec_env`,`mid` |-> `kwend`,
    `dispatch_end` |-> `sd`,`cr` |-> `reg_env`,`args` |-> `pos_args`,
    `tvs` |-> `pos_tvs`,`start` |-> `w`,`ctx` |-> `u.cu_context`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:string``] installed_positional_reject_after_kwargs))) >>
  impl_tac >- (asm_rewrite_tac[] >>
    qpat_assum `common.ec_pos_args = _` (fn eq =>
      qpat_assum `compile_register_positional_args reg_env common.ec_pos_args 4 entry = _`
        (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  disch_then (qx_choose_then `P` strip_assume_tac) >>
  mp_tac (Q.INST [`ctx` |-> `u.cu_context`,`start` |-> `s`,`first` |-> `w`]
    (SPEC_ALL reject_prefix_invariant_prepend)) >> asm_rewrite_tac[]
QED

Theorem grouped_legacy_selected_source_reject[local]:
  lower_vyper_runtime_unit tops rp = SOME u /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  MEM (mut,nr,rr,name,args,[],ret,fbody) (FST (classify_functions tops)) /\
  abi_method_id (type_env tops) name (MAP SND args) = cd_selector vs.vs_call_ctx.cc_calldata /\
  (OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = NONE \/
    ?tvs. OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
      (LENGTH vs.vs_call_ctx.cc_calldata < 4 + SUM (MAP tv_abi_size tvs) \/
       calldata_decode_args vs.vs_call_ctx.cc_calldata tvs 0 = NONE)) /\
  raw_reachable vs u.cu_context fn inst s ==>
  ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  mp_tac (Q.INST [`s` |-> `start`] grouped_runtime_reject_dispatch_inputs) >>
  impl_tac >- simp[Abbr `start`] >>
  disch_then (qx_choosel_then [`groups`,`entry`,`fl`,`sf`,`jobs`,`sd`,`sx`,`final`,`art`] strip_assume_tac) >>
  qabbrev_tac `ext = (mut,nr,rr,name,args,[]:expr list,ret,fbody)` >>
  Cases_on `set_external_package_target rp.rpol_target (package_external_fn tops T
    (K global_nonreentrant_slot) ext)` >> PairCases_on `r` >>
  rename1 `set_external_package_target _ _ = (lbl,ce,pos,m,pay,nr',key,ut,iv,pbody,rt)` >>
  `lbl = "fn_" ++ name` by
    (qpat_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[NoAsms, Abbr `ext`, package_external_fn_def, set_external_package_target_def, LET_THM]) >>
  qpat_x_assum `lbl = _` SUBST_ALL_TAC >>
  qunabbrev_tac `ext` >>
  `ALL_DISTINCT (MAP FST args) /\ pos = build_positional_args ce args /\
    ?tvs. OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
      m = 4 + SUM (MAP tv_abi_size tvs) /\ m < dimword (:256) /\
      LIST_REL (\(argname,ty) (ty',tv). ty = ty' /\
        abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
        (?loc. FLOOKUP ce.ce_vars argname = SOME loc /\
          var_location_memory_size loc = SOME (type_memory_size tv)) /\
        type_memory_size tv < dimword (:256)) args (ZIP (MAP SND args,tvs))` by
    (drule_all registration_reject_classified_package_inputs >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `pos = _` SUBST_ALL_TAC >>
  `LIST_REL (\(n,ty) tv.
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars n = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tvs` by
    (drule OPT_MMAP_LENGTH >> strip_tac >>
     simp[LIST_REL_EL_EQN] >> qx_gen_tac `i` >> strip_tac >>
     qpat_x_assum `LIST_REL _ args _`
       (qspec_then `i` mp_tac o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     Cases_on `EL i args` >> simp[EL_ZIP, EL_MAP]) >>
  qabbrev_tac `chosen_id = cd_selector vs.vs_call_ctx.cc_calldata` >>
  qabbrev_tac `hit = ExternalSingle (chosen_id,"fn_" ++ name,selector_has_trailing_zeroes chosen_id)
    ("fn_" ++ name,ce,build_positional_args ce args,m,pay,nr',key,ut,iv,pbody,rt)` >>
  `package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
     (mut,nr,rr,name,args,[],ret,fbody) = hit` by
    simp[Abbr `hit`, package_external_group_no_defaults,
         compute_selector_method_id, GSYM markerTheory.Abbrev_def] >>
  `MEM hit groups` by
    (qpat_assum `groups = MAP _ _` SUBST1_TAC >> simp[MEM_MAP] >>
     qexists_tac `(mut,nr,rr,name,args,[]:expr list,ret,fbody)` >> simp[]) >>
  pop_assum (qx_choosel_then [`pre`,`post`] assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  `ALL_DISTINCT (MAP FST (grouped_selectors groups))` by
    (qpat_assum `groups = MAP _ _` SUBST1_TAC >>
     drule check_contract_grouped_selectors_distinct >> simp[]) >>
  `calldata_method_id vs.vs_call_ctx.cc_calldata = n2w chosen_id` by
    simp[Abbr `chosen_id`, cd_selector_method_id] >>
  `EVERY (\e. calldata_method_id vs.vs_call_ctx.cc_calldata <> n2w (FST e))
       (grouped_selectors pre)` by
    (match_mp_tac (Q.INST [`groups` |-> `groups`,`group` |-> `hit`,
       `post` |-> `post`,`sel` |-> `(chosen_id,"fn_" ++ name,selector_has_trailing_zeroes chosen_id)`,
       `tops` |-> `tops`,`target` |-> `rp.rpol_target`,`trans` |-> `T`,
       `nkeys` |-> `K global_nonreentrant_slot`] grouped_selected_package_predecessors) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[Abbr `hit`, external_group_selectors_def]) >>
  `LENGTH vs.vs_call_ctx.cc_calldata < m \/
    calldata_decode_args vs.vs_call_ctx.cc_calldata tvs 0 = NONE` by metis_tac[optionTheory.SOME_11, optionTheory.NOT_NONE_SOME] >>
  (mp_tac (Q.INST [`s` |-> `start`,`fn` |-> `entry`, `env` |-> `type_env tops`,
     `nr` |-> `nr'`,`tr` |-> `ut`,`view` |-> `iv`,`stmts` |-> `pbody`,
     `sel` |-> `chosen_id`,`tz` |-> `selector_has_trailing_zeroes chosen_id`]
     grouped_legacy_reject_terminal) >>
   qunabbrev_tac `hit` >>
   impl_tac
   >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_assum `start.vs_call_ctx = _` SUBST1_TAC >> asm_rewrite_tac[]) >>
   strip_tac >> qunabbrev_tac `start` >>
   drule_all runtime_reject_prefix_excludes_fmp >> simp[])
QED

Theorem runtime_grouped_missed_selector_excludes_fmp[local]:
  lower_vyper_runtime_unit tops rp = SOME u /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  ~EXISTS is_default_decl tops /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  FIND (\(name,tys). abi_method_id (type_env tops) name tys =
    cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) = NONE /\
  raw_reachable vs u.cu_context fn inst s ==>
  ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `LENGTH vs.vs_call_ctx.cc_calldata < 4`
  >- (drule_all runtime_grouped_short_excludes_fmp >> simp[]) >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  rename1 `lookup_function "__entry" _ = SOME entry` >>
  drule_all lower_runtime_grouped_packages >> strip_tac >>
  `FST (SND (SND (classify_functions tops))) = NONE` by
    (drule calldataNoneFallbackJointTheory.absent_default_fold >>
     simp[classify_functions_def] >> rpt (pairarg_tac >> gvs[])) >>
  `fb = NONE` by simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  qpat_x_assum `fb = NONE` SUBST_ALL_TAC >>
  drule_all grouped_fallback_dispatch_code >>
  disch_then (qx_choosel_then [`fl`,`sf`,`jobs`,`sd`,`sn`,`se`] strip_assume_tac) >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `fresh_vars_wrt sf start /\ ~start.vs_halted /\
   4 <= LENGTH start.vs_call_ctx.cc_calldata /\
   LENGTH start.vs_call_ctx.cc_calldata < dimword (:256) /\
   start.vs_current_bb = sf.cs_current_bb /\ start.vs_inst_idx = LENGTH sf.cs_current_insts` by
    (drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`,`"__entry"`,`sf`] mp_tac) >> fs[Abbr `start`]) >>
  drule_all installed_grouped_long_dispatch_prefix >>
  disch_then (qspec_then `u` (qx_choosel_then [`q`,`r`,`v`] strip_assume_tac)) >>
  `EVERY (\sel. calldata_method_id start.vs_call_ctx.cc_calldata <> n2w (FST sel))
    (grouped_selectors groups)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM (FST sel) (MAP FST (grouped_selectors groups))` by
       (simp[MEM_MAP] >> qexists_tac `sel` >> simp[]) >>
     `MEM (FST sel) (MAP FST (grouped_selectors
       (MAP (package_external_group tops rp.rpol_target T (K global_nonreentrant_slot))
         (FST (classify_functions tops)))))` by
       (qpat_assum `groups = MAP _ _` (fn groups_eq =>
          qpat_assum `MEM (FST sel) (MAP FST (grouped_selectors groups))`
            (ACCEPT_TAC o REWRITE_RULE [groups_eq]))) >>
     `4 <= LENGTH vs.vs_call_ctx.cc_calldata` by decide_tac >>
     drule_all grouped_source_missed_selector >> fs[Abbr `start`]) >>
  `!lbl bb. lookup_block lbl entry.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule lowering_context_ok_block_phi >> metis_tac[]) >>
  `~v.vs_halted` by fs[vars_pc_only_def, venom_state_component_equality] >>
  drule_all installed_external_groups_miss >>
  disch_then (qspec_then `u.cu_context` (qx_choose_then `w` strip_assume_tac)) >>
  drule_all installed_empty_revert_code >>
  disch_then (qx_choose_then `fb` strip_assume_tac) >>
  `phi_prefix_length fb.bb_instructions = 0` by metis_tac[] >>
  `reject_prefix_step u.cu_context entry w (jump_to fl w)` by
    (irule reject_prefix_jump >> fs[] >> metis_tac[]) >>
  `reject_prefix_terminal u.cu_context entry (jump_to fl w)` by
    (irule installed_empty_revert_terminal >> simp[jump_to_def] >>
     qexistsl_tac [`sn`,`se`] >> gvs[]) >>
  `RTC (reject_prefix_step u.cu_context entry) start (jump_to fl w)` by
    metis_tac[RTC_TRANSITIVE, transitive_def, RTC_SINGLE] >>
  qpat_x_assum `Abbrev (start = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all runtime_reject_prefix_excludes_fmp >> simp[]
QED

(* Observe the complete dispatcher through a synthetic stop placed before
   the function bodies. A revert in this observer is a real raw prefix. *)
Theorem observe_grouped_dispatch_reject[local]:
  cs_extends sf sd /\ cs_extends sd final /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks final)) /\
  sf.cs_current_insts = [] /\ fn_has_code sf sd fn /\
  EVERY reject_prefix_opcode (state_insts sd) /\
  fn_inst_ids_distinct fn /\ no_phi_fn fn /\ MEM fn ctx.ctx_functions /\
  unit_alloca_budget ctx < 2 ** 254 /\ alloca_inv s /\ s.vs_allocas = FEMPTY /\
  s.vs_alloca_next <= unit_alloca_budget ctx /\
  fresh_vars_wrt sf s /\ ~s.vs_halted /\ at_point sf s /\
  (!obs local_ctx.
    fn_has_code sf sd obs /\ fn_inst_ids_distinct obs /\
    (!label bb. lookup_block label obs.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    selected_registration_resources local_ctx obs site 0 sf s /\
    unit_alloca_budget local_ctx < dimword (:256) /\ ~ctx_has_dalloca local_ctx ==>
    ?z H u. gas_origin_ptr_path (D,0,explicit,local_ctx,obs,PG)
      (s,G,tn) [] (Abort Revert_abort z,H,u)) ==>
  ?z. RTC (reject_prefix_step ctx fn) s z /\ reject_prefix_terminal ctx fn z
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `~MEM sd.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sf sd))` by
    (irule distinct_final_blocks_avoid_cut >> metis_tac[]) >>
  `EVERY reject_prefix_opcode (frag_code sf sd)` by
    (PURE_REWRITE_TAC [EVERY_MEM] >> rpt strip_tac >>
     drule frag_code_in_state_insts >> strip_tac >>
     qpat_assum `EVERY _ (state_insts sd)`
       (drule_then ACCEPT_TAC o REWRITE_RULE [EVERY_MEM])) >>
  mp_tac (Q.INST [`fn` |-> `fn`] frag_observer_fresh_id) >> strip_tac >>
  drule_all frag_observer_ids_distinct_from_labels >> strip_tac >>
  qabbrev_tac `obs = frag_observer sf sd fn id` >>
  `fn_has_code sf sd obs /\ EVERY reject_prefix_opcode (fn_insts obs) /\
   prefix_code_agrees obs fn (frag_observer_cut sd) /\ no_phi_fn obs` by
    (simp[Abbr `obs`] >> rpt conj_tac
     >- metis_tac[reject_observer_has_code]
     >- metis_tac[reject_observer_code, EVERY_DEF]
     >- (irule reject_observer_prefix_code >> simp[] >>
         fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
     metis_tac[fragObserverCodePropsTheory.abi_dyn_observer_no_phi]) >>
  `SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs))) <=
   unit_alloca_budget ctx` by
    (irule observed_alloca_budget >> simp[] >> qexists_tac `fn` >> simp[] >>
     simp[Abbr `obs`] >> rpt strip_tac >>
     irule frag_observer_nonstop_inclusion >> simp[] >>
     qexistsl_tac [`id`,`sf`,`sd`] >> simp[]) >>
  `remaining_alloca_budget (fn_insts obs) s <= unit_alloca_budget ctx` by
    (irule LESS_EQ_TRANS >>
     qexists_tac `SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs)))` >>
     simp[remaining_alloca_budget_le]) >>
  `SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs))) < 2 ** 255 /\
   s.vs_alloca_next + remaining_alloca_budget (fn_insts obs) s <= 2 ** 255` by (fs[] >> decide_tac) >>
  drule_all reject_decoder_observer_context >>
  disch_then (qspec_then `site` strip_assume_tac) >>
  rename1 `alloca_frontier_inv obs_ctx obs site s` >>
  `!label bb. lookup_block label obs.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  `selected_registration_resources obs_ctx obs site 0 sf s` by
    (qpat_x_assum `at_point sf s` (strip_assume_tac o REWRITE_RULE [at_point_def]) >>
     simp[selected_registration_resources_def, allocas_from_def]) >>
  qpat_x_assum `!obs local_ctx. _` (qspecl_then [`obs`,`obs_ctx`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  drule gas_origin_ptr_path_exec >> simp[exit_result_def] >> strip_tac >>
  irule safe_observer_reject_in_context >> simp[] >>
  qexistsl_tac [`frag_observer_cut sd`,`fuel`,`obs`,`obs_ctx`,`z`] >>
  simp[] >> simp[Abbr `obs`, abi_decode_frag_observer_cut_no_revert]
QED

Theorem calldata_decode_args_append_success[local]:
  !pos kw cd off pv kv.
    calldata_decode_args cd pos off = SOME pv /\
    calldata_decode_args cd kw (off + SUM (MAP tv_abi_size pos)) = SOME kv ==>
    calldata_decode_args cd (pos ++ kw) off = SOME (pv ++ kv)
Proof
  Induct >- simp[calldata_decode_args_def] >>
  rpt gen_tac >>
  simp[calldata_decode_args_def, LET_THM, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `off + (SUM (MAP tv_abi_size pos) + tv_abi_size h) =
   off + tv_abi_size h + SUM (MAP tv_abi_size pos)` by decide_tac >>
  gvs[] >> first_x_assum drule_all >> simp[]
QED

Theorem grouped_defaults_selected_source_reject[local]:
  lower_vyper_runtime_unit tops rp = SOME u /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
  MEM (mut,nr,rr,name,args,defaults,ret,stmts) (FST (classify_functions tops)) /\
  defaults <> [] /\ MEM (prefix,k) (abi_entries args defaults) /\
  abi_method_id (type_env tops) name (MAP SND prefix) = cd_selector vs.vs_call_ctx.cc_calldata /\
  (OPT_MMAP (evaluate_type (type_env tops)) (MAP SND prefix) = NONE \/
    ?tvs. OPT_MMAP (evaluate_type (type_env tops)) (MAP SND prefix) = SOME tvs /\
      (LENGTH vs.vs_call_ctx.cc_calldata < 4 + SUM (MAP tv_abi_size tvs) \/
       calldata_decode_args vs.vs_call_ctx.cc_calldata tvs 0 = NONE)) /\
  raw_reachable vs u.cu_context fn inst s ==>
  ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  mp_tac (Q.INST [`s` |-> `start`] grouped_runtime_reject_dispatch_inputs) >>
  impl_tac >- simp[Abbr `start`] >>
  disch_then (qx_choosel_then [`groups`,`entry`,`fl`,`sf`,`jobs`,`sd`,`sx`,`final`,`art`] strip_assume_tac) >>
  qabbrev_tac `ext = (mut,nr,rr,name,args,defaults,ret,stmts)` >>
  qabbrev_tac `group = package_external_group tops rp.rpol_target T (K global_nonreentrant_slot) ext` >>
  `?common entries specs off. group = ExternalDefaults common entries specs off` by
    (simp[Abbr `group`, Abbr `ext`, package_external_group_def, LET_THM, NULL_EQ] >>
     pairarg_tac >> gvs[]) >>
  `MEM group groups` by
    (qpat_assum `groups = MAP _ _` SUBST1_TAC >> simp[MEM_MAP, Abbr `group`] >>
     qexists_tac `ext` >> simp[Abbr `ext`]) >>
  qpat_x_assum `MEM group groups`
    (qx_choosel_then [`pre`,`post`] assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  `ALL_DISTINCT (MAP FST (grouped_selectors groups))` by
    (qpat_assum `groups = MAP _ _` SUBST1_TAC >>
     drule check_contract_grouped_selectors_distinct >> simp[]) >>
  qunabbrev_tac `ext` >>
  `group = package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
    (mut,nr,rr,name,args,defaults,ret,stmts)` by simp[Abbr `group`] >>
  `package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)
    (mut,nr,rr,name,args,defaults,ret,stmts) = ExternalDefaults common entries specs off` by
    metis_tac[] >>
  drule_all grouped_defaults_argument_metadata >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `all_tvs` strip_assume_tac)) >>
  `LENGTH defaults <= LENGTH args` by metis_tac[checked_classified_defaults_length] >>
  drule_all grouped_defaults_selected_entry >> strip_tac >>
  `FIND (\(n,_,_,_). calldata_method_id vs.vs_call_ctx.cc_calldata = n2w n) entries =
    SOME (cd_selector vs.vs_call_ctx.cc_calldata,external_prefix_label name k,
          min_calldata_size common.ec_env prefix 0,k)` by
    (drule_all grouped_defaults_selected_find >> disch_then ACCEPT_TAC) >>
  `EVERY (\e. calldata_method_id vs.vs_call_ctx.cc_calldata <> n2w (FST e))
       (grouped_selectors pre)` by
    (match_mp_tac (Q.INST [`groups` |-> `groups`,`group` |-> `group`,`post` |-> `post`,
       `sel` |-> `(cd_selector vs.vs_call_ctx.cc_calldata,external_prefix_label name k,
         cd_selector vs.vs_call_ctx.cc_calldata MOD 256 = 0)`,
       `tops` |-> `tops`,`target` |-> `rp.rpol_target`,`trans` |-> `T`,
       `nkeys` |-> `K global_nonreentrant_slot`] grouped_selected_package_predecessors) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_assum `group = ExternalDefaults _ _ _ _` SUBST1_TAC >>
         simp[external_group_selectors_def, MEM_MAP] >>
         qexists_tac `(cd_selector vs.vs_call_ctx.cc_calldata,external_prefix_label name k,
           min_calldata_size common.ec_env prefix 0,k)` >>
         simp[] >> metis_tac[venomInstTheory.FIND_MEM]) >>
     simp[cd_selector_method_id]) >>
  qabbrev_tac `n = LENGTH args - LENGTH defaults` >>
  qabbrev_tac `pos_tvs = TAKE n all_tvs` >>
  `prefix = TAKE (n+k) args` by
    (qpat_assum `MEM (prefix,k) (abi_entries args defaults)`
       (mp_tac o REWRITE_RULE [abi_entries_member]) >>
     simp[Abbr `n`]) >>
  `OPT_MMAP (evaluate_type (type_env tops)) (MAP SND prefix) = SOME (TAKE (n+k) all_tvs) /\
   OPT_MMAP (evaluate_type (type_env tops)) (MAP SND (TAKE n args)) = SOME pos_tvs` by
    (qpat_assum `prefix = TAKE _ args` SUBST1_TAC >>
     simp[Abbr `pos_tvs`] >> conj_tac >> pure_rewrite_tac[MAP_TAKE] >>
     irule opt_mmap_take_some >> first_assum ACCEPT_TAC) >>
  `LIST_REL (\arg tv. abi_decoder_coherent common.ec_env
     (type_env tops) common.ec_env.ce_struct_fields (SND arg) tv) args all_tvs` by
    (qpat_assum `LIST_REL (\(name,ty) tv. _ /\ _ /\ _) args all_tvs` mp_tac >>
     ho_match_mp_tac LIST_REL_mono >> Cases >> simp[]) >>
  qabbrev_tac `mincd = min_calldata_size common.ec_env prefix 0` >>
  `mincd = 4 + SUM (MAP tv_abi_size (TAKE (n+k) all_tvs))` by
    (simp[Abbr `mincd`] >>
     qpat_assum `LIST_REL (\arg tv. abi_decoder_coherent _ _ _ (SND arg) tv) args all_tvs`
       (mp_tac o Q.INST [`n` |-> `n+k`] o MATCH_MP grouped_argument_min_calldata_size) >>
     simp[]) >>
  `mincd < dimword (:256)` by
    (mp_tac (Q.SPECL [`n+k`,`all_tvs`] prefix_head_size_le) >> decide_tac) >>
  SUBGOAL_THEN ``LENGTH start.vs_call_ctx.cc_calldata < mincd \/
    calldata_decode_args start.vs_call_ctx.cc_calldata (TAKE (n+k) all_tvs) 0 = NONE`` ASSUME_TAC
  >- metis_tac[optionTheory.SOME_11, optionTheory.NOT_NONE_SOME] >>
  `!label bb. lookup_block label entry.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `no_phi_fn entry` (mp_tac o REWRITE_RULE [no_phi_fn_def, EVERY_MEM]) >>
     metis_tac[lookup_block_MEM]) >>
  `FIND (\(i,_,_,_). calldata_method_id start.vs_call_ctx.cc_calldata = n2w i) entries =
     SOME (cd_selector vs.vs_call_ctx.cc_calldata,external_prefix_label name k,mincd,k)` by
    simp[Abbr `mincd`] >>
  qpat_x_assum `group = ExternalDefaults _ _ _ _` SUBST_ALL_TAC >>
  Cases_on `LENGTH start.vs_call_ctx.cc_calldata < mincd \/
             (~common.ec_payable /\ start.vs_call_ctx.cc_callvalue <> 0w)`
  >- (SUBGOAL_THEN ``(~common.ec_payable /\ start.vs_call_ctx.cc_callvalue <> 0w) \/
        (4 < mincd /\ LENGTH start.vs_call_ctx.cc_calldata < mincd /\
         mincd < dimword (:256))`` ASSUME_TAC
      >- (qpat_assum `LENGTH start.vs_call_ctx.cc_calldata < mincd \/
                        (~common.ec_payable /\ start.vs_call_ctx.cc_callvalue <> 0w)`
            (DISJ_CASES_THEN assume_tac)
          >- (DISJ2_TAC >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
          DISJ1_TAC >> first_assum ACCEPT_TAC) >>
      mp_tac (Q.INST [`s` |-> `start`,`fn` |-> `entry`,
        `sel` |-> `cd_selector vs.vs_call_ctx.cc_calldata`,
        `lbl` |-> `external_prefix_label name k`] installed_group_default_checks_reject) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qpat_assum `start.vs_call_ctx = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      strip_tac >> qunabbrev_tac `start` >>
      drule_all runtime_reject_prefix_excludes_fmp >> simp[]) >>
  qpat_assum `~(LENGTH start.vs_call_ctx.cc_calldata < mincd \/ _)`
    (CONJUNCTS_THEN assume_tac o
       REWRITE_RULE [DE_MORGAN_THM, arithmeticTheory.NOT_LESS, NOT_CLAUSES]) >>
  `4 + SUM (MAP tv_abi_size pos_tvs) <= LENGTH start.vs_call_ctx.cc_calldata` by
    (qpat_assum `Abbrev (pos_tvs = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     mp_tac (Q.SPECL [`n`,`TAKE (n+k) all_tvs`] prefix_head_size_le) >>
     simp_tac bool_ss [TAKE_TAKE_T, LESS_EQ_ADD] >> decide_tac) >>
  `calldata_decode_args start.vs_call_ctx.cc_calldata (TAKE (n+k) all_tvs) 0 = NONE` by
    metis_tac[] >>
  Cases_on `calldata_decode_args start.vs_call_ctx.cc_calldata pos_tvs 0`
  >- (qunabbrev_tac `pos_tvs` >> qunabbrev_tac `n` >>
      mp_tac (Q.INST [`s` |-> `start`,`fn` |-> `entry`,`env` |-> `type_env tops`,
        `tvs` |-> `all_tvs`,`sel` |-> `cd_selector vs.vs_call_ctx.cc_calldata`,
        `lbl` |-> `external_prefix_label name k`,`n` |-> `LENGTH args - LENGTH defaults`]
        grouped_positional_reject_invariant) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
      strip_tac >>
      `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` by
        simp[Abbr `start`] >>
      match_mp_tac (Q.INST [`tops` |-> `tops`,`rp` |-> `rp`,`u` |-> `u`,
        `vs` |-> `vs`,`entry` |-> `entry`,`start` |-> `start`,`P` |-> `P`]
        runtime_reject_invariant_excludes_fmp) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `kw_tvs = TAKE k (DROP n all_tvs)` >>
  qabbrev_tac `pos_size = SUM (MAP tv_abi_size pos_tvs)` >>
  `TAKE (n+k) all_tvs = pos_tvs ++ kw_tvs` by simp[TAKE_SUM, Abbr `pos_tvs`, Abbr `kw_tvs`] >>
  `calldata_decode_args start.vs_call_ctx.cc_calldata kw_tvs pos_size = NONE` by
    (Cases_on `calldata_decode_args start.vs_call_ctx.cc_calldata kw_tvs pos_size` >> simp[] >>
     qpat_x_assum `calldata_decode_args start.vs_call_ctx.cc_calldata (TAKE (n+k) all_tvs) 0 = NONE` mp_tac >>
     qpat_assum `TAKE (n+k) all_tvs = _` SUBST1_TAC >>
     mp_tac (Q.SPECL [`pos_tvs`,`kw_tvs`,`start.vs_call_ctx.cc_calldata`,`0`,`x`,`x'`]
       calldata_decode_args_append_success) >>
     impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
       simp_tac bool_ss [arithmeticTheory.ADD_CLAUSES] >>
       qpat_assum `Abbrev (pos_size = _)`
         (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
       first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [optionTheory.NOT_SOME_NONE]) >>
  `off = 4 + pos_size` by
    (qpat_assum `off = _` SUBST1_TAC >>
     qpat_assum `LIST_REL (\arg tv. abi_decoder_coherent _ _ _ (SND arg) tv) args all_tvs`
       (mp_tac o Q.INST [`n` |-> `n`] o MATCH_MP grouped_argument_min_calldata_size) >>
     simp[Abbr `n`, Abbr `pos_size`, Abbr `pos_tvs`]) >>
  `4 + pos_size + SUM (MAP tv_abi_size kw_tvs) < dimword (:256)` by
    (qpat_assum `TAKE (n+k) all_tvs = _` (fn parts =>
       qpat_assum `mincd = 4 + SUM _`
         (assume_tac o PURE_REWRITE_RULE [parts, MAP_APPEND, SUM_APPEND])) >>
     qpat_assum `Abbrev (pos_size = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     decide_tac) >>
  `k <= LENGTH defaults` by
    (qpat_assum `MEM (prefix,k) (abi_entries args defaults)`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [abi_entries_member])) >>
  `LIST_REL (\(n,ty) tv. abi_decoder_coherent common.ec_env (type_env tops)
      common.ec_env.ce_struct_fields ty tv) args all_tvs` by
    (qpat_assum `LIST_REL (\(name,ty) tv. _ /\ _ /\ _) args all_tvs` mp_tac >>
     ho_match_mp_tac LIST_REL_mono >>
     Cases >> simp[]) >>
  `EVERY (\g. case g of ExternalSingle _ _ => T
      | ExternalDefaults comp es sp _ => EVERY
          (\(_,ty,_). type_memory_bytes comp.ec_env ty < dimword (:256)) sp) groups` by
    (qpat_assum `groups = MAP _ _` SUBST1_TAC >>
     Cases_on `classify_functions tops` >> PairCases_on `r` >>
     drule_all checked_grouped_package_keyword_widths >> simp[]) >>
  `EVERY (\g. case g of ExternalSingle _ _ => T
      | ExternalDefaults comp es sp _ => EVERY
          (\(_,ty,_). type_memory_bytes comp.ec_env ty < dimword (:256)) sp) pre /\
    EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs` by
    (qpat_assum `groups = pre ++ _` (fn split =>
       qpat_assum `EVERY (\g. case g of ExternalSingle _ _ => T | _ => _) groups`
         (mp_tac o PURE_ONCE_REWRITE_RULE [split])) >>
     simp[EVERY_APPEND]) >>
  `!g e. MEM g pre /\ MEM e (external_group_selectors g) ==>
    calldata_method_id start.vs_call_ctx.cc_calldata <> n2w (FST e)` by
    (qx_genl_tac [`g`,`e`] >> disch_then (CONJUNCTS_THEN assume_tac) >>
     `MEM e (grouped_selectors pre)` by
       (simp[grouped_selectors_def, MEM_FLAT, MEM_MAP] >>
        qexists_tac `external_group_selectors g` >> simp[] >>
        qexists_tac `g` >> simp[]) >>
     qpat_assum `EVERY _ (grouped_selectors pre)`
       (qspec_then `e` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp_tac bool_ss [ASSUME ``MEM e (grouped_selectors pre)``] >>
     qpat_assum `start.vs_call_ctx = _` SUBST1_TAC >>
     simp[]) >>
  `EVERY (\g. case g of ExternalSingle (sel,_,_) _ =>
        calldata_method_id start.vs_call_ctx.cc_calldata <> n2w sel
      | ExternalDefaults comp es sp _ =>
        FIND (\(sel,_,_,_). calldata_method_id start.vs_call_ctx.cc_calldata = n2w sel) es = NONE /\
        EVERY (\(_,ty,_). type_memory_bytes comp.ec_env ty < dimword (:256)) sp) pre` by
    (simp_tac bool_ss [EVERY_MEM] >> Cases
     >- (rename1 `ExternalSingle selector pkg` >> PairCases_on `selector` >> strip_tac >>
         qpat_assum `!g e. MEM g pre /\ _ ==> _`
           (qspecl_then [`ExternalSingle (selector0,selector1,selector2) pkg`,
             `(selector0,selector1,selector2)`] mp_tac) >>
         simp[external_group_selectors_def]) >>
     rename1 `MEM (ExternalDefaults comp es sp offset) pre ==> _` >>
     strip_tac >> simp_tac (srw_ss()) [] >> conj_tac
     >- (simp[mem2varBlockSimHelpersTheory.FIND_NONE_EVERY, combinTheory.o_DEF,
              EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
         rename1 `MEM (sel,lbl,sz,k') es` >>
         qpat_assum `!g e. MEM g pre /\ _ ==> _`
           (qspecl_then [`ExternalDefaults comp es sp offset`,`(sel,lbl,sel MOD 256 = 0)`] mp_tac) >>
         simp[external_group_selectors_def, MEM_MAP] >>
         qexists_tac `(sel,lbl,sz,k')` >> simp[]) >>
     qpat_assum `EVERY (\g. case g of ExternalSingle _ _ => T | _ => _) pre`
       (qspec_then `ExternalDefaults comp es sp offset` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[]) >>
  `LENGTH kw_tvs = k` by
    (qpat_assum `OPT_MMAP _ (MAP SND args) = SOME all_tvs`
       (mp_tac o MATCH_MP OPT_MMAP_LENGTH) >>
     simp[Abbr `kw_tvs`, Abbr `n`, LENGTH_TAKE_EQ, LENGTH_DROP] >> decide_tac) >>
  `groups = pre ++ ExternalDefaults common entries specs (4+pos_size)::post` by
    (qpat_assum `off = 4 + pos_size` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `common.ec_payable \/ start.vs_call_ctx.cc_callvalue = 0w` by
    (Cases_on `common.ec_payable` >> simp[]) >>
  `?z. RTC (reject_prefix_step u.cu_context entry) start z /\
      reject_prefix_terminal u.cu_context entry z` by
    (mp_tac (Q.INST [`ctx` |-> `u.cu_context`,`s` |-> `start`,`fn` |-> `entry`,
       `site` |-> `ARB`,`D` |-> `ARB`,`PG` |-> `[]`,`G` |-> `FEMPTY`,`tn` |-> `entry_taint`,
       `explicit` |-> `EMPTY`] (SPEC_ALL observe_grouped_dispatch_reject)) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
       >- decide_tac >>
       qx_genl_tac [`obs`,`local_ctx`] >>
       disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
       mp_tac (Q.INST [`sa` |-> `sf`,`sb` |-> `sd`,`s` |-> `start`,
          `ctx` |-> `local_ctx`,`fn` |-> `obs`,`site` |-> `ARB`,`lo` |-> `0`,
          `fallback` |-> `fl`,
          `sel` |-> `cd_selector vs.vs_call_ctx.cc_calldata`,
          `lbl` |-> `external_prefix_label name k`,
          `kw` |-> `kw_tvs`,`off` |-> `pos_size`,`env` |-> `type_env tops`,
          `PG` |-> `[]`,`G` |-> `FEMPTY`,`tn` |-> `entry_taint`]
          (SPEC_ALL grouped_bad_supplied_origin)) >>
       impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
         >- simp[] >>
         qx_genl_tac [`vars`,`st`,`t`,`H`,`ut`] >>
         disch_then (CONJUNCTS_THEN assume_tac) >>
         qunabbrev_tac `kw_tvs` >>
         irule (DISCH_ALL (CONJUNCT2 (UNDISCH (SPEC_ALL grouped_supplied_owners)))) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`args`,`defaults`] >>
         asm_simp_tac bool_ss [Abbr `n`] >>
         qpat_assum `specs = MAP _ _` (SUBST1_TAC o SYM) >>
         first_assum ACCEPT_TAC) >>
       disch_then (qx_choosel_then [`z`,`Hz`,`tz`] (CONJUNCTS_THEN2 assume_tac
         (qspecl_then [`ARB`,`EMPTY`] assume_tac))) >>
       qexistsl_tac [`z`,`Hz`,`tz`] >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  qunabbrev_tac `start` >>
  drule_all runtime_reject_prefix_excludes_fmp >> simp[]
QED

Theorem lower_vyper_runtime_unit_reject_reaches_no_fmp_ops:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    ctx_has_dalloca unit.cu_context /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254 ==>
    !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
      ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `EXISTS external_has_defaults (FST (classify_functions tops))`
  >- (drule calldata_dispatch_none_cases >>
      disch_then (DISJ_CASES_THEN2 (CONJUNCTS_THEN assume_tac)
        (qx_choosel_then [`name`,`tys`] (REPEAT_TCL CONJUNCTS_THEN assume_tac)))
      >- (qpat_x_assum `LENGTH _ < 4 \/ FIND _ _ = NONE`
            (DISJ_CASES_THEN assume_tac)
          >- (drule_all runtime_grouped_short_excludes_fmp >> simp[]) >>
          drule_all runtime_grouped_missed_selector_excludes_fmp >> simp[]) >>
      mp_tac (Q.INST [`cd` |-> `vs.vs_call_ctx.cc_calldata`,
        `target` |-> `rpolicy.rpol_target`,`trans` |-> `T`,
        `nkeys` |-> `K global_nonreentrant_slot`]
        grouped_source_selected_package) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (qx_choosel_then [`mut`,`nr`,`rr`,`args`,`defaults`,`ret`,`stmts`,
        `prefix`,`k`,`group`,`sel`] strip_assume_tac) >>
      `abi_method_id (type_env tops) name (MAP SND prefix) =
        cd_selector vs.vs_call_ctx.cc_calldata` by
        (qpat_assum `FIND _ _ = SOME (name,tys)` (mp_tac o MATCH_MP venomInstTheory.FIND_P) >>
         simp[]) >>
      SUBGOAL_THEN ``OPT_MMAP (evaluate_type (type_env tops))
        (MAP SND (prefix:(string # type) list)) = NONE \/
        ?tvs. OPT_MMAP (evaluate_type (type_env tops)) (MAP SND prefix) = SOME tvs /\
          (LENGTH vs.vs_call_ctx.cc_calldata < 4 + SUM (MAP tv_abi_size tvs) \/
           calldata_decode_args vs.vs_call_ctx.cc_calldata tvs 0 = NONE)`` ASSUME_TAC
      >- metis_tac[] >>
      Cases_on `defaults = []`
      >- (qpat_x_assum `defaults = []` SUBST_ALL_TAC >>
          qpat_x_assum `MEM (prefix,k) (abi_entries args [])`
            (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_entries_no_defaults]) >>
          qpat_x_assum `prefix = args` SUBST_ALL_TAC >>
          drule_all grouped_legacy_selected_source_reject >> simp[]) >>
      drule_all grouped_defaults_selected_source_reject >> simp[]) >>
  `unit_alloca_budget unit.cu_context < 2 ** 254` by (fs[] >> decide_tac) >>
  drule_all runtime_legacy_reject_excludes_fmp >> simp[]
QED

Theorem call_reject_raw_variant_no_wrap:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\ initial_venom_state_rel tops am tx vs /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
  ctx_has_dalloca unit.cu_context /\
  unit_alloca_budget unit.cu_context <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  raw_variant fmp vi vs ==>
  !fn inst s. raw_reachable vi unit.cu_context fn inst s ==>
    dalloca_no_wrap inst s /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp
Proof
  strip_tac >>
  `initial_venom_state_rel tops am tx vi` by
    metis_tac[raw_variant_initial_venom_state_rel] >>
  `vi.vs_call_ctx = vs.vs_call_ctx` by metis_tac[raw_variant_call_ctx] >>
  `vi.vs_fmp = fmp /\ vi.vs_initial_fmp = fmp` by
    (fs[raw_variant_def, gas_variant_def, venom_state_component_equality] >> metis_tac[]) >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vi`] mp_tac
    lower_vyper_runtime_unit_reject_reaches_no_fmp_ops >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `s.vs_fmp = vi.vs_fmp /\ s.vs_initial_fmp = vi.vs_initial_fmp` by
    metis_tac[raw_reachable_fmp_unchanged, raw_reachable_initial_fmp] >>
  first_x_assum drule >> strip_tac >>
  `inst.inst_opcode <> DALLOCA` by metis_tac[is_raw_fmp_opcode_def] >>
  simp[dalloca_no_wrap_def]
QED
