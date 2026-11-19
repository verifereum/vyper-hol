Theory gasFocusJointProgress
Ancestors passSharedFrame[qualified,ignore_grammar] blast[qualified,ignore_grammar] sat[qualified,ignore_grammar] normalizer[qualified,ignore_grammar] bool[qualified,ignore_grammar] Canon_Port_Context[qualified,ignore_grammar]
  gasFocusSourceProvider[qualified,ignore_grammar]
  dftFinitePacket dftGasFromListTraceDefs dftPacketNativeSlice
  dftFinitePacketReachability dftGasInvForwardActive dftRunRel dftDefs stepWriteFootprintBase
  dftPacketClosedRowNative dftPacketNativeContinuation
  o1ContractCfgNormJointCursors frameJointTrace frameJointTransition
  o1ContractCfgNorm
  makeSsaCurrentLockstep makeSsaCurrentPhiBatchRuntime o1LowerDloadEntryFetch fnFrameRequestPrefix
  o1ContractSimplifyCfgSrcFrame fnFrameBoundaryInvoke
  frameRawProjection frameHistoryCfg frameOriginHistory frameOriginReachable venomExecProps
  venomFnInstsProofs fnLineageStatic stackPlanGen livenessDefs venomExecProofs
  fnFramePrefixDriver fnFrameSymbolicPrefix codegenEntryRel
  o1PipelineCorrect o1SafeUpto o1PassContract o1PassLift unitMemInv
  venomPipelineRunner venomPassSchedule irSupply fcgDefs
  dftGasOracleDefs gasEvents contextRawReachable memSafeRun
  venomExecSemantics venomWf venomInst venomState unitShapeDefs
  codegenSymRel asmDataEnv asmFrameRel asmOptimizer asmSem asmSymSem symbolResolve
  contextCodegenRel lowerDloadDefs staticAbortDefs frameOutcome callTrace
  callLayoutDefs fmpWfDefs venomWfProps
  o1RequestContract unitTransformDefs ptrDiscipline passSimulationDefs
  vfmExecution codegen asmIR
  gasFocusPlainFrameProgress blockSimHelpers venomCompilerTypes
  o1ContractCfgNormCursors cfgNormSupplySim stateFrame
  gasFocusPlainGasPreEdge gasFocusGasPreEdge codegenAsmProgOk
  gasFocusFalseCodegenContext gasFocusOptLabelFlow gasFocusOptStaticAssembly
  finite_map list rich_list words arithmetic

Theorem focus_return_output_length[local]:
  fmp_lowered_context_wf C /\ MEM caller C.ctx_functions /\
  MEM call (fn_insts caller) /\ call.inst_opcode = INVOKE /\
  decode_invoke call = SOME (nm,args) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  MEM inst (fn_insts callee) /\ step_inst fuel C inst s = IntRet ret send ==>
  LENGTH call.inst_outputs = LENGTH ret.iret_values
Proof
  strip_tac >>
  `invoke_layout_wf C call` by metis_tac[fmp_lowered_context_wf_def] >>
  qpat_x_assum `invoke_layout_wf C call`
    (strip_assume_tac o REWRITE_RULE [invoke_layout_wf_def]) >>
  gvs[decode_invoke_def] >>
  `MEM inst (fn_return_insts callee)` by
    (simp[fn_return_insts_def, MEM_FILTER] >>
     conj_tac
     >- metis_tac[step_inst_intret_opcodes, is_raw_return_opcode_def, MEM] >>
     fs[fn_insts_def, fn_insts_blocks_flat]) >>
  `fmp_lowered_return_layout_wf sig callee` by
    fs[fmp_seal_layout_matches_fn_def, fmp_signature_syntax_wf_def] >>
  `?n. fmp_expected_user_return_arity sig callee = SOME n /\
       lowered_return_inst_layout_wf sig.fms_publishes n inst` by
    (qpat_assum `fmp_lowered_return_layout_wf sig callee` mp_tac >>
     qpat_assum `MEM inst (fn_return_insts callee)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `fn_return_insts callee` >>
     simp[fmp_lowered_return_layout_wf_def] >>
     Cases_on `fmp_expected_user_return_arity sig callee` >>
     simp[] >> metis_tac[EVERY_MEM]) >>
  pop_assum strip_assume_tac >>
  drule lowered_return_inst_layout_wf_length >> strip_tac >>
  `inst.inst_opcode = RET` by fs[lowered_return_inst_layout_wf_def] >>
  `?v vals. eval_operands inst.inst_operands s = SOME (v::vals) /\
             ret.iret_values = FRONT (v::vals)` by
    (Cases_on `eval_operands inst.inst_operands s`
     >- fs[step_inst_non_invoke, step_inst_base_def] >>
     Cases_on `x` >> gvs[step_inst_non_invoke, step_inst_base_def]) >>
  pop_assum strip_assume_tac >>
  `LENGTH (v::vals) = LENGTH inst.inst_operands` by
    metis_tac[eval_operands_some_length] >>
  Cases_on `sig.fms_publishes` >>
  fs[fmp_invoke_output_arity_ok_def,LENGTH_FRONT] >> decide_tac
QED

Theorem focus_c9_return_exists[local]:
  EVERY wf_function C.ctx_functions /\ fmp_lowered_context_wf C /\
  joint_config_reachable vs0 C
    (JointConfig stk PG G tn fn inst s oms om hs hist) /\
  stk <> [] /\ active_inst fn inst s /\
  step_inst fuel C inst s = IntRet ret send ==>
  ?ev q'. joint_transition C
    (JointConfig stk PG G tn fn inst s oms om hs hist) ev q'
Proof
  Cases_on `stk` >- simp[] >>
  rename1 `JointConfig (caller::stk) PG G tn fn inst s oms om hs hist` >>
  strip_tac >>
  qpat_x_assum `joint_config_reachable _ _ _`
    (assume_tac o REWRITE_RULE [joint_config_reachable_def]) >>
  drule_then assume_tac joint_origin_history_projection >>
  drule_all_then strip_assume_tac frame_history_cfg_invariant >>
  `frame_reachable vs0 C (caller::stk) PG G tn fn inst s` by
    (drule_then (ACCEPT_TAC o MATCH_MP (SPEC_ALL origin_frame_erasure))
       joint_origin_history_erasure) >>
  drule_all_then strip_assume_tac frame_reachable_prefix_stack >>
  qpat_x_assum `matched_prefix_stack _ _ (caller::stk) _ _`
    (strip_assume_tac o REWRITE_RULE [matched_prefix_stack_def]) >>
  `MEM caller.cf_fn C.ctx_functions /\ oms <> [] /\ hs <> []` by
    (drule_then strip_assume_tac joint_origin_history_endpoints >>
     Cases_on `hs` >> Cases_on `oms` >> gvs[]) >>
  `MEM inst (fn_insts fn) /\ MEM caller.cf_inst (fn_insts caller.cf_fn)` by
    metis_tac[active_inst_def,MEM_fn_insts,EL_MEM] >>
  drule_all_then assume_tac focus_return_output_length >>
  `?post. bind_outputs caller.cf_inst.inst_outputs ret.iret_values
     (adopt_return_fmp ret (merge_callee_state caller.cf_state send)) = SOME post` by
    simp[bind_outputs_def] >>
  pop_assum strip_assume_tac >>
  drule_then assume_tac return_binding_current_bb >>
  `?next. active_inst caller.cf_fn next
           (post with vs_inst_idx := SUC caller.cf_state.vs_inst_idx)` by
    (qpat_assum `active_inst caller.cf_fn caller.cf_inst caller.cf_state`
      (strip_assume_tac o REWRITE_RULE [active_inst_def]) >>
     `bb_well_formed bb` by fs[wf_function_def] >>
     `SUC caller.cf_state.vs_inst_idx < LENGTH bb.bb_instructions` by
       (irule non_terminator_not_last >> fs[is_terminator_def]) >>
     simp[active_inst_def] >> qexists `bb` >> simp[]) >>
  pop_assum strip_assume_tac >>
  Cases_on `oms` >> Cases_on `hs` >> gvs[] >>
  metis_tac[joint_transition_rules]
QED

Theorem focus_callee_first_instruction[local]:
  codegen_ready_fn callee /\ setup_callee callee args caller = SOME entry ==>
  ?first. enters_block callee entry entry /\ active_inst callee first entry
Proof
  strip_tac >>
  drule setup_callee_props >> strip_tac >>
  `wf_function callee` by fs[codegen_ready_fn_def] >>
  `?bb. lookup_block entry.vs_current_bb callee.fn_blocks = SOME bb` by
    (qpat_x_assum `fn_entry_label callee = SOME _` mp_tac >>
     simp[fn_entry_label_def, entry_block_def, AllCaseEqs()] >>
     strip_tac >>
     Cases_on `callee.fn_blocks` >> gvs[lookup_block_def, FIND_thm]) >>
  pop_assum strip_assume_tac >>
  `MEM bb callee.fn_blocks /\ bb.bb_label = entry.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `collect_phis bb.bb_instructions = []` by metis_tac[ready_entry_no_phis] >>
  `bb.bb_instructions <> []` by fs[wf_function_def, bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> gvs[collect_phis_def] >>
  `h.inst_opcode <> PHI` by (strip_tac >> fs[]) >>
  `entry with vs_inst_idx := 0 = entry` by simp[venom_state_component_equality] >>
  qexists `h` >> conj_tac
  >- (simp[enters_block_def] >> qexists `entry` >>
      simp[eval_phis_def, phi_prefix_length_def]) >>
  simp[active_inst_def] >> qexists `bb` >> simp[]
QED

Theorem focus_c9_call_exists[local]:
  codegen_ready C /\ active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME entry ==>
  ?q'. joint_transition C (JointConfig stk PG G tn fn inst s oms om hs hist) NONE q'
Proof
  strip_tac >>
  `codegen_ready_fn callee` by metis_tac[codegen_ready_def, lookup_function_MEM, EVERY_MEM] >>
  drule_all_then strip_assume_tac focus_callee_first_instruction >>
  metis_tac[joint_transition_rules]
QED

Theorem focus_cfg_terminator_enters[local]:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  supply_prefix_defined fn s /\ active_inst fn inst s /\
  is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK post /\
  ~post.vs_halted ==>
  ?s1 next. enters_block fn post s1 /\ active_inst fn next s1
Proof
  strip_tac >>
  drule_all_then strip_assume_tac lockstep_active_terminator_edge >>
  drule_all_then assume_tac supply_prefix_terminator_entry >>
  drule_all_then (qx_choose_then `bb` assume_tac) supply_entry_defined_lookup >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = post.vs_current_bb` by
    metis_tac[lookup_block_MEM,lookup_block_label] >>
  `?pred. MEM pred fn.fn_blocks /\ pred.bb_label = s.vs_current_bb /\
     EVERY inst_wf pred.bb_instructions /\ exec_block fuel C pred s = OK post` by
    (qpat_assum `active_inst fn inst s`
       (qx_choose_then `pred` strip_assume_tac o REWRITE_RULE [active_inst_def]) >>
     qexists_tac `pred` >> simp[] >> conj_tac
     >- (fs[fn_inst_wf_def,EVERY_MEM] >> metis_tac[]) >>
     irule supply_active_terminator_exec_block >> metis_tac[]) >>
  `?sp. eval_phis post bb.bb_instructions = OK sp` by
    (irule current_phi_batch_success_all >> rpt strip_tac >>
     rename1 `MEM i bb.bb_instructions` >>
     `inst_wf i` by (fs[fn_inst_wf_def,EVERY_MEM] >> metis_tac[]) >>
     `phi_well_formed i.inst_operands /\ LENGTH i.inst_outputs = 1` by
       (qpat_x_assum `inst_wf i` mp_tac >> simp[inst_wf_def]) >>
     `phi_edge_uses_wf fn bb i` by
       (fs[wf_ssa_def,def_dominates_uses_def] >> metis_tac[]) >>
     `fn_cfg_edge fn s.vs_current_bb bb.bb_label` by metis_tac[] >>
     `?v. MEM (s.vs_current_bb,v) (phi_pairs i.inst_operands)` by
       (qpat_assum `phi_edge_uses_wf fn bb i`
          (mp_tac o Q.SPEC `s.vs_current_bb` o cj 3 o
            REWRITE_RULE [phi_edge_uses_wf_def]) >>
        simp[pairTheory.EXISTS_PROD] >> strip_tac >> gvs[] >> metis_tac[]) >>
     `?x. resolve_phi s.vs_current_bb i.inst_operands = SOME (Var x)` by
       metis_tac[phi_pairs_resolve_phi_some,resolve_phi_well_formed] >>
     `MEM (s.vs_current_bb,x) (phi_pairs i.inst_operands)` by
       metis_tac[resolve_phi_pair] >>
     `def_available_at fn pred NONE x` by
       (qpat_assum `phi_edge_uses_wf fn bb i`
          (mp_tac o Q.SPECL [`s.vs_current_bb`,`x`] o cj 4 o
            REWRITE_RULE [phi_edge_uses_wf_def]) >>
        simp[] >> strip_tac >>
        `pred_bb = pred` by metis_tac[same_label_same_block] >> gvs[]) >>
     `x IN FDOM post.vs_vars` by
       (irule def_available_at_exec_block_endpoint >>
        qexistsl [`pred`,`C`,`fn`,`fuel`,`s`] >>
        fs[supply_prefix_defined_def,supply_entry_defined_def] >>
        rpt strip_tac >> first_x_assum irule >>
        qexistsl [`pred`,`j`] >> simp[]) >>
     Cases_on `i.inst_outputs` >>
     gvs[eval_one_phi_def,eval_operand_def,lookup_var_def,FLOOKUP_DEF]) >>
  `enters_block fn post (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[enters_block_def] >> qexists_tac `sp` >> simp[]) >>
  drule_all_then strip_assume_tac ld_wf_enters_block_fetch >>
  metis_tac[]
QED

Theorem focus_c9_continuing_exists[local]:
  codegen_ready C9 /\ EVERY wf_function C9.ctx_functions /\
  fmp_lowered_context_wf C9 /\ active_inst fn9 inst9 s9 /\
  joint_config_reachable vs0 C9
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  (inst9.inst_opcode = INVOKE ==>
    ?nm ops callee args ent. decode_invoke inst9 = SOME (nm,ops) /\
      lookup_function nm C9.ctx_functions = SOME callee /\
      eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent) /\
  (inst9.inst_opcode <> INVOKE ==>
    (?u. step_inst 0 C9 inst9 s9 = OK u /\ ~u.vs_halted) \/
    (stk9 <> [] /\ ?ir u. step_inst 0 C9 inst9 s9 = IntRet ir u)) ==>
  ?ev q'. joint_transition C9
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ev q'
Proof
  strip_tac >> Cases_on `inst9.inst_opcode = INVOKE` >> fs[]
  >- (drule_all_then strip_assume_tac focus_c9_call_exists >> metis_tac[])
  >- (`wf_function fn9 /\ fn_inst_wf fn9 /\ wf_ssa fn9 /\ supply_prefix_defined fn9 s9` by
        (qpat_assum `cfg_norm_joint_cursors _ _ _ _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> PairCases_on `current` >>
         simp[cfg_norm_joint_cursors_def] >> strip_tac >>
         qpat_x_assum `EVERY _ schedules`
           (drule_then strip_assume_tac o REWRITE_RULE [EVERY_MEM]) >>
         drule_then strip_assume_tac cfg_norm_cursors_last >>
         gvs[supply_norm_inv_def]) >>
      Cases_on `is_terminator inst9.inst_opcode`
      >- (drule_all_then strip_assume_tac focus_cfg_terminator_enters >>
          metis_tac[joint_transition_block]) >>
      drule_all_then strip_assume_tac active_inst_next_nonterminator >>
      metis_tac[joint_transition_next]) >>
  drule_all_then ACCEPT_TAC focus_c9_return_exists
QED

(* A same-frame visit cannot occur in the nested trace of an INVOKE. *)
Theorem focus_native_visit_row_prefix[local]:
  !s. MEM ((a,e,i.inst_id),tf,i,t)
    (trace_block a e fuel C tf bb s) ==>
  ?k. t.vs_inst_idx = s.vs_inst_idx + k /\
      get_instruction bb t.vs_inst_idx = SOME i /\
      EVERY (\x. ~is_terminator x.inst_opcode)
        (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) /\
      FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK
        (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s = OK t
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once dftGasFromListTraceDefsTheory.trace_defs] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME head` >>
  `~MEM ((a,e,i.inst_id),tf,i,t) (trace_step a e fuel C tf head s)` by
    metis_tac[dftGasFromListTraceNamesTheory.trace_step_not_root, MEM_MAP, pairTheory.FST] >>
  simp[Once dftGasFromListTraceDefsTheory.trace_defs, MEM_APPEND] >>
  strip_tac
  >- (gvs[] >> qexists_tac `0` >> simp[]) >>
  Cases_on `step_inst fuel C head s` >> gvs[] >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by fs[get_instruction_def] >>
  rename1 `step_inst fuel C head s = OK out` >>
  qpat_x_assum `!y. _` (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspec_then `out with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `SUC k` >>
  `DROP s.vs_inst_idx bb.bb_instructions = head :: DROP (SUC s.vs_inst_idx) bb.bb_instructions` by
    fs[get_instruction_def, DROP_CONS_EL] >>
  gvs[dftIndexedExecTheory.dft_exec_cons_def, ADD_CLAUSES]
QED

(* A live row ends at the indexed current instruction (or pending call). *)
Theorem focus_live_body_slice[local]:
  bt.bb_instructions = ps ++ ys /\ be.vs_inst_idx = LENGTH ps /\
  m <= LENGTH ys /\ EVERY (\x. ~is_terminator x.inst_opcode) (TAKE m ys) /\
  FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK (TAKE m ys) be = OK b0 /\
  ALL_DISTINCT (MAP FST R) /\ hbe <= LENGTH R /\
  R = TAKE hbe R ++ trace_block a e fuel C tf bt be ++ rest /\
  get_instruction bt b0.vs_inst_idx = SOME endinst /\
  j < LENGTH R /\ EL j R = ((a,e,endinst.inst_id),tf,endinst,b0) ==>
  TAKE j R = TAKE hbe R ++
    trace_block a e fuel C tf
      (bt with bb_instructions := TAKE (LENGTH ps + m) bt.bb_instructions) be
Proof
  strip_tac >>
  `DROP be.vs_inst_idx bt.bb_instructions = ys` by simp[DROP_APPEND] >>
  qsuff_tac `TAKE j R = TAKE hbe R ++ trace_block a e fuel C tf
    (bt with bb_instructions := TAKE (be.vs_inst_idx + m) bt.bb_instructions) be`
  >- simp[] >>
  irule native_trace_embedded_prefix_cut >>
  rpt (first_assum (irule_at Any)) >> simp[]
QED

(* A finished row exposes exactly its native trace and the next block or return. *)
Theorem focus_closed_native_row[local]:
  lookup_block hin.vs_current_bb tf.fn_blocks = SOME bt /\
  eval_phis hin bt.bb_instructions = OK sp /\
  start = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions /\
  bt.bb_instructions = ps ++ ys /\ be.vs_inst_idx = LENGTH ps /\
  phi_prefix_length bt.bb_instructions <= LENGTH ps /\
  EVERY (\x. ~is_terminator x.inst_opcode)
    (DROP (phi_prefix_length bt.bb_instructions) ps) /\
  FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK
    (DROP (phi_prefix_length bt.bb_instructions) ps) start = OK be /\
  ys <> [] /\ is_terminator (LAST ys).inst_opcode /\
  FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK ys be = front ==>
  trace_blocks a inc (SUC fuel) C tf hin =
    trace_block a (SUC inc) fuel C tf bt start ++
    (case front of OK post =>
       if post.vs_halted then [] else trace_blocks a (SUC inc) fuel C tf post
     | _ => [])
Proof
  strip_tac >>
  `DROP be.vs_inst_idx bt.bb_instructions = ys` by simp[DROP_APPEND] >>
  `exec_block fuel C bt be = front` by metis_tac[native_exec_block_terminated_fold] >>
  `DROP (phi_prefix_length bt.bb_instructions) ps =
     TAKE (LENGTH ps - phi_prefix_length bt.bb_instructions)
       (DROP (phi_prefix_length bt.bb_instructions) bt.bb_instructions)` by
    simp[GSYM DROP_TAKE, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  `exec_block fuel C bt start = front` by
    (qsuff_tac `exec_block fuel C bt start = exec_block fuel C bt be` >- simp[] >>
     irule native_exec_block_prefix_skip >>
     qexists_tac `LENGTH ps - phi_prefix_length bt.bb_instructions` >>
     qpat_x_assum `DROP _ ps = TAKE _ _` (assume_tac o SYM) >> gvs[]) >>
  drule_all trace_blocks_enter >>
  disch_then (qspecl_then [`a`, `fuel`, `inc`, `C`] SUBST1_TAC) >> gvs[]
QED

(* Expose the actual native suffix at a retained row or call anchor. *)
Theorem focus_native_anchor[local]:
  R = trace_blocks [] 0 N C tf0 entry /\ h < LENGTH R /\
  EL h R = ((a,e,i.inst_id),tf,i,t) /\
  lookup_block t.vs_current_bb tf.fn_blocks = SOME bt ==>
  get_instruction bt t.vs_inst_idx = SOME i /\
  ?rest. DROP h R = trace_block a e (N-e) C tf bt t ++ rest /\
         R = TAKE h R ++ trace_block a e (N-e) C tf bt t ++ rest
Proof
  strip_tac >> gvs[] >> drule_all native_trace_blocks_continuation >>
  strip_tac >> gvs[] >>
  rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  qpat_x_assum `DROP h _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
  rewrite_tac[listTheory.TAKE_DROP]
QED

(* A live body slice can be recovered from the two native indices. *)
Theorem focus_live_indexed_slice[local]:
  R = trace_blocks [] 0 N C tf0 entry /\
  bt.bb_instructions = ps ++ ys /\ be.vs_inst_idx = LENGTH ps /\
  m <= LENGTH ys /\ EVERY (\x. ~is_terminator x.inst_opcode) (TAKE m ys) /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C) OK (TAKE m ys) be = OK b0 /\
  ALL_DISTINCT (MAP FST R) /\ hbe <= j /\ j < LENGTH R /\
  EL hbe R = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
  lookup_block be.vs_current_bb tf.fn_blocks = SOME bt /\
  lookup_block b0.vs_current_bb tf.fn_blocks = SOME bt /\
  EL j R = ((a,e,endinst.inst_id),tf,endinst,b0) ==>
  TAKE j R = TAKE hbe R ++
    trace_block a e (N-e) C tf
      (bt with bb_instructions := TAKE (LENGTH ps + m) bt.bb_instructions) be
Proof
  strip_tac >>
  `hbe < LENGTH R` by decide_tac >>
  drule_all focus_native_anchor >> strip_tac >>
  `get_instruction bt b0.vs_inst_idx = SOME endinst` by
    (qpat_x_assum `EL hbe R = _` kall_tac >>
     drule_all focus_native_anchor >> simp[]) >>
  `hbe <= LENGTH R` by decide_tac >>
  irule focus_live_body_slice >>
  rpt (first_assum (irule_at Any))
QED

(* A successful row replay and its scheduled prefix share an oracle. *)
Theorem focus_historical_row_observation[local]:
  LIST_REL dftRunRel$dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  dftRunRel$dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dftRunRel$dft_remaining_inv sf bb xs be /\ be.vs_inst_idx = LENGTH ps /\
  q < LENGTH xs /\ k < LENGTH ys /\ EL q xs = inst /\ EL k ys = inst /\
  inv_memory_observation inst.inst_opcode /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k ys) /\
  FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
    (be with vs_gas_readings := FLAT kgss ++ tail) = OK u /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE k ys) be = OK visit /\
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (FLAT ks) /\
  LIST_REL (\key slot. slot = ALOOKUP obs key) (FLAT (TAKE q ks)) (FLAT (TAKE q ms)) /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
  trace_gas (trace_block a e (fuel-e) C7 sf
    (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
    (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE q ks),FLAT kgss) /\
  EVERY (\kw. MEM kw obs) (trace_gas (trace_block a e (N-e) C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps + k) bt.bb_instructions) be)) ==>
  (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op visit) /\
  u.vs_initial_fmp = visit.vs_initial_fmp
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (TAKE q ks))` by
    (qsuff_tac `ALL_DISTINCT (FLAT (TAKE q ks) ++ FLAT (DROP q ks))`
     >- simp[ALL_DISTINCT_APPEND] >>
     pure_rewrite_tac[GSYM FLAT_APPEND, TAKE_DROP] >> first_assum ACCEPT_TAC) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q ms)) (FLAT kgss)` by
    (qpat_x_assum `LIST_REL (LIST_REL _) _ _` mp_tac >>
     qspec_tac (`TAKE q ms`, `mss`) >> qid_spec_tac `kgss` >>
     Induct >> Cases_on `mss` >> simp[EVERY2_APPEND_suff]) >>
  `?orc. trace_agrees orc (trace_block a e (fuel-e) C7 sf
           (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
           (be with vs_gas_readings := FLAT kgss ++ tail)) /\
         trace_agrees orc (trace_block a e (N-e) C8 tf
           (bt with bb_instructions := TAKE (LENGTH ps + k) bt.bb_instructions) be)` by
    (drule_all dftPacketCommonOracleTheory.dft_packet_common_oracle >>
     strip_tac >> goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  `xs = TAKE q xs ++ inst :: DROP (SUC q) xs` by
    gvs[TAKE_DROP_SUC] >>
  `ys = TAKE k ys ++ inst :: DROP (SUC k) ys` by
    (qpat_assum `k < LENGTH ys` (mp_then Any mp_tac TAKE_DROP_SUC) >>
     simp[] >> metis_tac[]) >>
  `LENGTH (TAKE q xs) = q /\ LENGTH (TAKE k ys) = k` by simp[] >>
  `MEM bb sf.fn_blocks` by metis_tac[lookup_block_MEM] >>
  irule dftPacketObservationSuccessTheory.dft_packet_native_observation_success >>
  metis_tac[]
QED

(* The common-oracle argument does not distinguish live and returned rows. *)
Theorem focus_packet_body_observation[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,row_order,hin,h0,SOME (be,hbe),nseen,front,closed,brest) /\
  q < LENGTH xs /\ k < LENGTH ys /\ EL q xs = inst /\ EL k ys = inst /\
  inv_memory_observation inst.inst_opcode /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k ys) /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE k ys) be = OK visit /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
    (TAKE q (THE (FLOOKUP ms_tab (a,e)))) kgss /\
  FOLDR (dftIndexedExec$dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
    (be with vs_gas_readings := FLAT kgss ++ tail) = OK u /\
  trace_gas (trace_block a e (fuel-e) C7 (FST (THE (FLOOKUP acts a)))
    (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
    (be with vs_gas_readings := FLAT kgss ++ tail)) =
      ZIP (FLAT (TAKE q (THE (FLOOKUP ks_tab (a,e)))),FLAT kgss) /\
  EVERY (\kw. MEM kw obs) (trace_gas (trace_block a e (N-e) C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps + k) bt.bb_instructions) be)) ==>
  (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op visit) /\
  u.vs_initial_fmp = visit.vs_initial_fmp
Proof
  strip_tac >>
  `?ms ks. FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
     ALL_DISTINCT (FLAT ks) /\ ALL_DISTINCT (MAP FST obs) /\
     LIST_REL (\key slot. slot = ALOOKUP obs key) (FLAT (TAKE q ks)) (FLAT (TAKE q ms)) /\
     LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\ dft_fn_rel sf tf /\
     lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
     lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
     bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
     EVERY (\i. is_pseudo i.inst_opcode) ps /\ EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
     EVERY inst_shape_ok bb.bb_instructions /\ dft_remaining_inv sf bb xs be /\
     be.vs_inst_idx = LENGTH ps` by
    (qhdtm_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     `?ms ess ks. FLOOKUP ms_tab (a,e) = SOME ms /\
       FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM es_tab`,
           `FDOM blocks = FDOM ks_tab`,`FLOOKUP blocks (a,e) = _`] >>
        POP_ASSUM_LIST (K all_tac) >> rw[FLOOKUP_DEF] >> gvs[]) >>
     drule_all dft_packet_retained_prefix_lookup >>
     disch_then (qspec_then `q` assume_tac) >>
     qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
       FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
       FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
       (drule_all_then strip_assume_tac o cj 6) >>
     qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (fn inv => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
         (mp_then Any assume_tac (cj 3 inv))) >>
     qpat_assum `!a e bb bt ps xs ys rho hin h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`
       (fn inv => qpat_assum `FLOOKUP blocks (a,e) = _`
         (mp_then Any (strip_assume_tac o SRULE []) inv)) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`,
        `FLOOKUP acts a = SOME (_,_,_,_,_,_,_)`,
        `FLOOKUP ms_tab (a,e) = _`, `FLOOKUP ks_tab (a,e) = _`,
        `(j,obs) = _`, `ALL_DISTINCT (MAP FST _)`, `ALL_DISTINCT (FLAT ks)`,
        `LIST_REL (\key slot. slot = ALOOKUP _ key) _ _`,
        `LIST_REL dft_fn_rel _ _`, `dft_fn_rel sf tf`,
        `lookup_block bb.bb_label _ = SOME bb`, `lookup_block bb.bb_label _ = SOME bt`,
        `bb.bb_instructions = ps ++ xs`, `bt.bb_instructions = ps ++ ys`,
        `EVERY (\i. is_pseudo i.inst_opcode) ps`, `EVERY (\i. ~is_pseudo i.inst_opcode) xs`,
        `EVERY inst_shape_ok bb.bb_instructions`, `dft_remaining_inv _ _ _ _`,
        `be.vs_inst_idx = LENGTH ps`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >> gvs[]) >>
  qhdtm_x_assum `dft_focus_packet_rel` kall_tac >>
  gvs[] >> irule focus_historical_row_observation >>
  simp[arithmeticTheory.ADD_COMM] >> rpt (first_assum (irule_at Any)) >>
  qexists_tac `a` >> simp[]
QED

(* Gas seen before an indexed body visit is included even when the
   activation has returned by the packet cursor j. *)
Theorem focus_indexed_body_observations[local]:
  R = trace_blocks [] 0 N C tf0 entry /\ obs = trace_gas (TAKE j R) /\
  bt.bb_instructions = ps ++ ys /\ be.vs_inst_idx = LENGTH ps /\
  k <= LENGTH ys /\ EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k ys) /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C) OK (TAKE k ys) be = OK visit /\
  ALL_DISTINCT (MAP FST R) /\ hbe <= h /\ h < LENGTH R /\ h <= j /\
  EL hbe R = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
  lookup_block be.vs_current_bb tf.fn_blocks = SOME bt /\
  lookup_block visit.vs_current_bb tf.fn_blocks = SOME bt /\
  EL h R = ((a,e,inst.inst_id),tf,inst,visit) ==>
  EVERY (\kw. MEM kw obs) (trace_gas (trace_block a e (N-e) C tf
    (bt with bb_instructions := TAKE (LENGTH ps + k) bt.bb_instructions) be))
Proof
  strip_tac >>
  `TAKE h R = TAKE hbe R ++ trace_block a e (N-e) C tf
    (bt with bb_instructions := TAKE (LENGTH ps + k) bt.bb_instructions) be` by
    (drule_all focus_live_indexed_slice >> simp[]) >>
  `TAKE h (TAKE j R) = TAKE h R` by simp[rich_listTheory.TAKE_TAKE_T] >>
  `TAKE j R = TAKE h R ++ DROP h (TAKE j R)` by metis_tac[TAKE_DROP] >>
  qpat_x_assum `obs = trace_gas _` SUBST1_TAC >>
  qpat_x_assum `TAKE j R = _` SUBST1_TAC >>
  qpat_x_assum `TAKE h R = _` SUBST1_TAC >>
  simp[dftGasFromListReadingsTheory.trace_gas_append, EVERY_MEM]
QED

(* Use the cut in the selected packet, not a transported cut from an
   earlier packet.  In the row trace bridge the working table is ms_tab. *)
Theorem focus_packet_rooted_body_observation[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,row_order,hin,h0,SOME (be,hbe),nseen,front,closed,brest) /\
  q < LENGTH xs /\ k < LENGTH ys /\ EL q xs = inst /\ EL k ys = inst /\
  inv_memory_observation inst.inst_opcode /\
  z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE nseen row_order)) /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts = LENGTH levels /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then
        ai = a /\ ei = e /\ qi = q /\ zi = z
      else
        ?cid call_h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) =
            SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
            MEM r done_at_call)) /\
      EL i levels =
        (sfi,
         MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
           DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
             (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
         [(bbi,ei,zi)],
         if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
  N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
    (events,OK u) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k ys) /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE k ys) be = OK visit /\
  R = trace_blocks [] 0 N C8 root_tf root_entry /\
  hbe <= h /\ h < j /\ EL h R = ((a,e,inst.inst_id),tf,inst,visit) /\
  lookup_block visit.vs_current_bb tf.fn_blocks = SOME bt ==>
  (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op visit) /\
  u.vs_initial_fmp = visit.vs_initial_fmp
Proof
  strip_tac >>
  `bt.bb_instructions = ps ++ ys /\ be.vs_inst_idx = LENGTH ps /\
   lookup_block be.vs_current_bb tf.fn_blocks = SOME bt /\
   EL hbe R = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
   obs = trace_gas (TAKE j R) /\ j < LENGTH R /\ ALL_DISTINCT (MAP FST R)` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_assum `!a e bb bt ps xs ys rho hin h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`
       (fn inv => qpat_assum `FLOOKUP blocks (a,e) = _`
         (mp_then Any (strip_assume_tac o SRULE []) inv)) >>
     `ALL_DISTINCT (MAP FST (trace_blocks [] 0 N C8 root_tf root_entry))` by
       (qpat_assum `LIST_REL dft_fn_rel _ C8.ctx_functions`
          (mp_then Any mp_tac dftContractGasTheory.dft_ctx_block_ids_distinct) >>
        qpat_assum `lookup_function _ C8.ctx_functions = SOME root_tf`
          (mp_then Any mp_tac lookup_function_MEM) >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        irule (cj 3 dftGasFromListTraceNamesTheory.trace_names_distinct) >>
        simp[] >> qpat_assum `EVERY _ C8.ctx_functions`
          (qspec_then `root_tf` mp_tac o ONCE_REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`R = trace_blocks _ _ _ _ _ _`, `(j,obs) = _`, `_ < LENGTH (trace_blocks _ _ _ _ _ _)`,
        `_ = trace_gas (TAKE _ (trace_blocks _ _ _ _ _ _))`,
        `ALL_DISTINCT (MAP FST (trace_blocks _ _ _ _ _ _))`,
        `bt.bb_instructions = _`, `be.vs_inst_idx = _`, `be.vs_current_bb = _`,
        `EL hbe (trace_blocks _ _ _ _ _ _) = _`,
        `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`,
        `FLOOKUP acts a = SOME (_,_,_,_,_,_,_)`,
        `lookup_block bb.bb_label _ = SOME bt`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >> gvs[]) >>
  `h < LENGTH R /\ h <= j /\ k <= LENGTH ys` by decide_tac >>
  drule_all_then assume_tac focus_indexed_body_observations >>
  `FDOM ms_tab = FDOM ms_tab` by simp[] >>
  `!key old new. FLOOKUP ms_tab key = SOME old /\ FLOOKUP ms_tab key = SOME new ==>
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) old new` by
    (rw[] >> gvs[] >> irule EVERY2_refl >> rw[] >>
     irule EVERY2_refl >> simp[]) >>
  drule_all dft_packet_cut_row_trace >> strip_tac >>
  drule_all focus_packet_body_observation >> simp[]
QED

(* Scratch statement for elaboration and independent review.
   The literal continuing cases are decoded INVOKE setup, a nonhalting
   ordinary or block evaluator result, or a return with a saved caller.
   C8 stutters keep all six tables. Moving C8 edges keep the same
   root and may extend the native trace fuel. Stuttering keeps N. *)
(* Projection facts for comparing the native traversal with the joint chain. *)
Theorem focus_active_get[local]:
  wf_function f /\ lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  active_inst f i s ==> get_instruction bb s.vs_inst_idx = SOME i
Proof
  rw[active_inst_def, wf_function_def, get_instruction_def] >>
  `bb' = bb` by metis_tac[simplifyCfgPhiShapeTheory.member_lookup_block_eq] >>
  gvs[]
QED

Theorem focus_joint_next_native[local]:
  joint_transition C (JointConfig stk PG G tn f i s oms om hs hist) ev q /\
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = OK out ==>
  ?PG' G' tn' i' s' oms' om' hs' hist'.
    q = JointConfig stk PG' G' tn' f i' s' oms' om' hs' hist' /\
    active_inst f i' s' /\
    (if is_terminator i.inst_opcode then ~out.vs_halted /\ enters_block f out s'
     else s' = out with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >>
  gvs[step_inst_non_invoke] >> metis_tac[]
QED

Theorem focus_joint_ret_native[local]:
  joint_transition C (JointConfig (fr::stk) PG G tn f i s oms om hs hist) ev q /\
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = IntRet r out ==>
  ?PG' G' tn' i' post oms' om' hs' hist'.
    q = JointConfig stk PG' G' tn' fr.cf_fn i'
      (post with vs_inst_idx := SUC fr.cf_state.vs_inst_idx) oms' om' hs' hist' /\
    active_inst fr.cf_fn i' (post with vs_inst_idx := SUC fr.cf_state.vs_inst_idx) /\
    bind_outputs fr.cf_inst.inst_outputs r.iret_values
      (adopt_return_fmp r (merge_callee_state fr.cf_state out)) = SOME post
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >>
  gvs[step_inst_non_invoke] >> metis_tac[]
QED

Theorem focus_joint_call_native[local]:
  joint_transition C (JointConfig stk PG G tn f i s oms om hs hist) ev q /\
  i.inst_opcode = INVOKE ==>
  ?nm ops callee args cs s' i'.
    decode_invoke i = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s' /\ active_inst callee i' s' /\
    q = JointConfig
      (<|cf_fn := f; cf_inst := i; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee i' s'
      (om::oms) FEMPTY (hist::hs)
      [OriginCallee cs; OriginObserve
        (OriginSnapshot callee (MAP (op_prov G) ops) FEMPTY FEMPTY i' s')]
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >>
  gvs[is_terminator_def] >>
  drule step_inst_intret_opcodes >> simp[]
QED

Theorem focus_chain_drop[local]:
  joint_chain C q es qs Q /\ k <= LENGTH es ==>
  joint_chain C (EL k (q::qs)) (DROP k es) (DROP k qs) Q
Proof
  strip_tac >> drule_all joint_chain_split >> strip_tac >>
  `EL (LENGTH (TAKE k es)) (q::TAKE k qs) = u` by
    metis_tac[joint_chain_endpoint] >>
  `EL (LENGTH (TAKE k es)) (q::TAKE k qs) = EL k (q::qs)` by
    (Cases_on `k` >> gvs[LENGTH_TAKE, EL_TAKE] >>
     imp_res_tac joint_chain_length >> simp[EL_TAKE]) >>
  gvs[]
QED

Theorem focus_chain_native_append[local]:
  joint_chain C q es qs Q /\
  (!h. h <= LENGTH es /\ h < LENGTH X ==> P (EL h X) (EL h (q::qs))) /\
  (LENGTH X <= LENGTH es ==> A (EL (LENGTH X) (q::qs))) /\
  (!u fs us. joint_chain C u fs us Q /\ A u ==>
    (!h. h <= LENGTH fs /\ h < LENGTH Y ==> P (EL h Y) (EL h (u::us))) /\
    (LENGTH Y <= LENGTH fs ==> B (EL (LENGTH Y) (u::us)))) ==>
  (!h. h <= LENGTH es /\ h < LENGTH (X ++ Y) ==>
    P (EL h (X ++ Y)) (EL h (q::qs))) /\
  (!u. LENGTH (X ++ Y) <= LENGTH es /\ EL (LENGTH (X ++ Y)) (q::qs) = u ==> B u)
Proof
  strip_tac >> Cases_on `LENGTH X <= LENGTH es`
  >- (`LENGTH es = LENGTH qs` by metis_tac[joint_chain_length] >>
      drule_all_then assume_tac focus_chain_drop >>
      `EL (LENGTH X) (q::qs) :: DROP (LENGTH X) qs = DROP (LENGTH X) (q::qs)` by
        simp[DROP_CONS_EL, LENGTH, LESS_EQ] >>
      qpat_x_assum `!u fs us. _` drule >> (impl_tac >- simp[]) >>
      simp[EL_DROP, LENGTH_APPEND] >> strip_tac >>
      rpt strip_tac >> simp[EL_APPEND_EQN] >>
      Cases_on `h < LENGTH X` >> simp[] >>
      qpat_x_assum `!h. _ ==> P (EL h Y) _` (qspec_then `h - LENGTH X` mp_tac) >>
      simp[]) >>
  simp[LENGTH_APPEND, EL_APPEND_EQN]
QED

Theorem focus_enters_get[local]:
  wf_function f /\ enters_block f entry s /\ active_inst f i s ==>
  ?bb sp. lookup_block entry.vs_current_bb f.fn_blocks = SOME bb /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    eval_phis entry bb.bb_instructions = OK sp /\
    s = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
    get_instruction bb s.vs_inst_idx = SOME i
Proof
  rw[enters_block_def] >>
  drule_then assume_tac eval_phis_preserves_current_bb >>
  `lookup_block (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_current_bb
     f.fn_blocks = SOME bb` by simp[] >>
  drule_all_then assume_tac focus_active_get >>
  qexistsl [`bb`, `s_phi`] >> simp[] >> fs[]
QED

Theorem focus_chain_native_cons[local]:
  joint_chain C q es qs Q /\ P v q /\
  (!ev u fs us. joint_transition C q ev u /\ joint_chain C u fs us Q ==>
    (!h. h <= LENGTH fs /\ h < LENGTH X ==> P (EL h X) (EL h (u::us))) /\
    (!w. LENGTH X <= LENGTH fs /\ EL (LENGTH X) (u::us) = w ==> A w)) ==>
  (!h. h <= LENGTH es /\ h < LENGTH (v::X) ==> P (EL h (v::X)) (EL h (q::qs))) /\
  (!u. LENGTH (v::X) <= LENGTH es /\ EL (LENGTH (v::X)) (q::qs) = u ==> A u)
Proof
  Cases_on `es` >> Cases_on `qs` >> simp[joint_chain_def] >>
  strip_tac >> first_x_assum drule_all >> simp[] >> strip_tac >>
  Cases >> simp[]
QED

(* Match a native trace up to the length covered by the actual joint chain.
   At the first index after a completed segment, retain the resumed caller
   (INVOKE/IntRet) or the entered block (a nonhalting terminator). *)
Theorem focus_native_joint_segments[local]:
  (!a e f i s stk PG G tn oms om hs hist.
     P ((a,e,i.inst_id),f,i,s) (JointConfig stk PG G tn f i s oms om hs hist)) ==>
  ((!p d fuel C f i s. !stk PG G tn oms om hs hist ev q es qs Q.
      EVERY wf_function C.ctx_functions /\ i.inst_opcode = INVOKE /\
      joint_transition C (JointConfig stk PG G tn f i s oms om hs hist) ev q /\
      joint_chain C q es qs Q ==>
      (!k. k <= LENGTH es /\ k < LENGTH (trace_step p d fuel C f i s) ==>
         P (EL k (trace_step p d fuel C f i s)) (EL k (q::qs))) /\
      (!post. LENGTH (trace_step p d fuel C f i s) <= LENGTH es /\
         step_inst fuel C i s = OK post ==>
         ?PG' G' tn' i' oms' om' hs' hist'.
           EL (LENGTH (trace_step p d fuel C f i s)) (q::qs) =
             JointConfig stk PG' G' tn' f i' (post with vs_inst_idx := SUC s.vs_inst_idx)
               oms' om' hs' hist' /\
           active_inst f i' (post with vs_inst_idx := SUC s.vs_inst_idx))) /\
   (!p d fuel C f bb s. !stk PG G tn i oms om hs hist es qs Q.
      EVERY wf_function C.ctx_functions /\ wf_function f /\
      lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\ active_inst f i s /\
      joint_chain C (JointConfig stk PG G tn f i s oms om hs hist) es qs Q ==>
      (!k. k <= LENGTH es /\ k < LENGTH (trace_block p d fuel C f bb s) ==>
         P (EL k (trace_block p d fuel C f bb s))
           (EL k (JointConfig stk PG G tn f i s oms om hs hist::qs))) /\
      (!u. LENGTH (trace_block p d fuel C f bb s) <= LENGTH es /\
         EL (LENGTH (trace_block p d fuel C f bb s))
           (JointConfig stk PG G tn f i s oms om hs hist::qs) = u ==>
         case exec_block fuel C bb s of
           OK out =>
             ?PG' G' tn' i' s' oms' om' hs' hist'.
               u = JointConfig stk PG' G' tn' f i' s' oms' om' hs' hist' /\
               enters_block f out s' /\ active_inst f i' s'
         | IntRet r out =>
             !fr rest. stk = fr::rest ==>
             ?PG' G' tn' i' post oms' om' hs' hist'.
               u = JointConfig rest PG' G' tn' fr.cf_fn i'
                   (post with vs_inst_idx := SUC fr.cf_state.vs_inst_idx) oms' om' hs' hist' /\
               active_inst fr.cf_fn i' (post with vs_inst_idx := SUC fr.cf_state.vs_inst_idx) /\
               bind_outputs fr.cf_inst.inst_outputs r.iret_values
                 (adopt_return_fmp r (merge_callee_state fr.cf_state out)) = SOME post
         | _ => T)) /\
   (!p d fuel C f entry. !stk PG G tn i s oms om hs hist es qs Q.
      EVERY wf_function C.ctx_functions /\ wf_function f /\
      enters_block f entry s /\ active_inst f i s /\
      joint_chain C (JointConfig stk PG G tn f i s oms om hs hist) es qs Q ==>
      (!k. k <= LENGTH es /\ k < LENGTH (trace_blocks p d fuel C f entry) ==>
         P (EL k (trace_blocks p d fuel C f entry))
           (EL k (JointConfig stk PG G tn f i s oms om hs hist::qs))) /\
      (!r out fr rest. LENGTH (trace_blocks p d fuel C f entry) <= LENGTH es /\
         run_blocks fuel C f entry = IntRet r out /\ stk = fr::rest ==>
         ?PG' G' tn' i' post oms' om' hs' hist'.
           EL (LENGTH (trace_blocks p d fuel C f entry))
             (JointConfig stk PG G tn f i s oms om hs hist::qs) =
             JointConfig rest PG' G' tn' fr.cf_fn i'
               (post with vs_inst_idx := SUC fr.cf_state.vs_inst_idx) oms' om' hs' hist' /\
           active_inst fr.cf_fn i' (post with vs_inst_idx := SUC fr.cf_state.vs_inst_idx) /\
           bind_outputs fr.cf_inst.inst_outputs r.iret_values
             (adopt_return_fmp r (merge_callee_state fr.cf_state out)) = SOME post)))
Proof
  strip_tac >> ho_match_mp_tac dftGasFromListTraceDefsTheory.trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume focus_native_joint_segments[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac focus_joint_call_native >>
  `wf_function callee` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  gvs[cj 1 dftGasFromListTraceDefsTheory.trace_defs] >>
  first_x_assum drule_all >> strip_tac >>
  conj_tac >- simp[] >>
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _`
    (mp_tac o ONCE_REWRITE_RULE [venomExecSemanticsTheory.step_inst_def]) >>
  simp[AllCaseEqs()] >> strip_tac >>
  first_x_assum (drule_at (Pat `run_blocks _ _ _ _ = IntRet _ _`)) >>
  simp[] >> strip_tac >> gvs[]
QED

Resume focus_native_joint_segments[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all_then assume_tac focus_active_get >>
  once_rewrite_tac [cj 2 dftGasFromListTraceDefsTheory.trace_defs] >>
  pure_asm_rewrite_tac [optionTheory.option_case_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  ho_match_mp_tac focus_chain_native_cons >>
  simp[Excl "LENGTH_APPEND", ExclSF "UNWIND"] >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (gvs[Excl "LENGTH_APPEND", Excl "EL", ExclSF "UNWIND"] >>
      qpat_x_assum `!i'. i = i' ==> _` (qspec_then `i` mp_tac) >>
      simp[Excl "LENGTH_APPEND", ExclSF "UNWIND"] >>
      disch_then drule_all >> strip_tac >>
      `~is_terminator INVOKE` by EVAL_TAC >>
      Cases_on `step_inst fuel C i s` >>
      ntac 3 (asm_rewrite_tac[venomExecSemanticsTheory.exec_result_case_def,
                             APPEND_NIL] >> BETA_TAC) >>
      TRY (FIRST [conj_tac >- first_assum ACCEPT_TAC >> simp[],
                  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
                  simp[fnBlockBodyStepsTheory.step_inst_invoke_not_intret]]) >>
      rename1 `step_inst fuel C i s = OK post` >>
      drule_all_then strip_assume_tac intCallStepTheory.step_inst_invoke_OK_control >>
      ho_match_mp_tac (Q.INST [`A` |-> `\q. ?PG' G' tn' i' oms' om' hs' hist'.
        q = JointConfig stk PG' G' tn' f i' (post with vs_inst_idx := SUC s.vs_inst_idx)
              oms' om' hs' hist' /\ active_inst f i' (post with vs_inst_idx := SUC s.vs_inst_idx)`]
        focus_chain_native_append) >>
      simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
      first_x_assum drule_all >> simp[]) >>
  gvs[dftGasFromListTraceDefsTheory.trace_step_noninvoke, Excl "EL"] >>
  Cases_on `step_inst fuel C i s` >> simp[]
  >- (rename1 `step_inst fuel C i s = OK out` >>
      drule_all_then strip_assume_tac focus_joint_next_native >>
      Cases_on `is_terminator i.inst_opcode` >> gvs[] >>
      `step_inst_base i s = OK out` by gvs[step_inst_non_invoke] >>
      drule_all_then strip_assume_tac venomInstProofs1Theory.step_inst_base_preserves_all >>
      `lookup_block out.vs_current_bb f.fn_blocks = SOME bb` by simp[] >>
      first_x_assum drule_all >> simp[]) >>
  rpt strip_tac >> gvs[] >> drule_all focus_joint_ret_native >> simp[]
QED

Resume focus_native_joint_segments[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac focus_enters_get >>
  Cases_on `fuel` >>
  once_rewrite_tac [cj 3 dftGasFromListTraceDefsTheory.trace_defs] >>
  ntac 4 (asm_rewrite_tac [optionTheory.option_case_def,
    venomExecSemanticsTheory.exec_result_case_def, arithmeticTheory.num_case_def] >> BETA_TAC)
  >- simp[Once venomExecSemanticsTheory.run_blocks_def] >>
  once_rewrite_tac [venomExecSemanticsTheory.run_blocks_def] >>
  ntac 3 (asm_rewrite_tac [optionTheory.option_case_def,
    venomExecSemanticsTheory.exec_result_case_def, arithmeticTheory.num_case_def] >> BETA_TAC) >>
  qpat_x_assum `!fuel' bb sp. _` (qspecl_then [`n`, `bb`, `sp`] mp_tac) >>
  impl_tac >- simp[] >>
  qpat_x_assum `s = sp with vs_inst_idx := _` SUBST_ALL_TAC >>
  disch_then drule_all >> strip_tac >>
  Cases_on `run_block_non_phis n C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  TRY (simp[AllCaseEqs()] >> NO_TAC)
  >- (rename1 `run_block_non_phis _ _ _ _ = OK next` >>
      Cases_on `next.vs_halted` >- simp[] >>
      ntac 2 (asm_rewrite_tac[venomExecSemanticsTheory.exec_result_case_def] >> BETA_TAC) >>
      qabbrev_tac `X = dftGasFromListTraceDefs$trace_block p (SUC d) n C f bb
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      qabbrev_tac `Y = dftGasFromListTraceDefs$trace_blocks p (SUC d) n C f next` >>
      qabbrev_tac `q = JointConfig stk PG G tn f i
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) oms om hs hist` >>
      qabbrev_tac `B = \u. !r out fr rest.
        run_blocks n C f next = IntRet r out /\ stk = fr::rest ==>
        ?PG' G' tn' i' post oms' om' hs' hist'.
          u = JointConfig rest PG' G' tn' fr.cf_fn i'
               (post with vs_inst_idx := SUC fr.cf_state.vs_inst_idx) oms' om' hs' hist' /\
          active_inst fr.cf_fn i' (post with vs_inst_idx := SUC fr.cf_state.vs_inst_idx) /\
          bind_outputs fr.cf_inst.inst_outputs r.iret_values
            (adopt_return_fmp r (merge_callee_state fr.cf_state out)) = SOME post` >>
      `(!k. k <= LENGTH es /\ k < LENGTH (X ++ Y) ==>
         P (EL k (X ++ Y)) (EL k (q::qs))) /\
       (!u. LENGTH (X ++ Y) <= LENGTH es /\ EL (LENGTH (X ++ Y)) (q::qs) = u ==> B u)`
        suffices_by (simp[Abbr `B`] >> metis_tac[]) >>
      ho_match_mp_tac (Q.INST [`A` |-> `\u. ?PG' G' tn' i' s' oms' om' hs' hist'.
        u = JointConfig stk PG' G' tn' f i' s' oms' om' hs' hist' /\
        enters_block f next s' /\ active_inst f i' s'`] focus_chain_native_append) >>
      qpat_x_assum `!fuel' bb sp entry'. _` (qspecl_then [`n`, `bb`, `sp`, `next`] mp_tac) >>
      impl_tac >- simp[] >>
      strip_tac >>
      conj_tac >- simp[] >>
      conj_tac >- simp[] >>
      conj_tac >- (strip_tac >>
        qpat_assum `!u. LENGTH X <= LENGTH es /\ _ ==> _`
          (qspec_then `EL (LENGTH X) (q::qs)` mp_tac) >> simp[] >> gvs[]) >>
      rpt gen_tac >> strip_tac >> gvs[Abbr `B`, Abbr `Y`] >>
      first_x_assum drule_all >> simp[]) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!u. LENGTH _ <= LENGTH es /\ _ ==> _` mp_tac >>
  gvs[]
QED

Finalise focus_native_joint_segments

Theorem focus_native_joint_visit[local]:
  C.ctx_entry = SOME nm /\
  lookup_function nm C.ctx_functions = SOME root_tf /\
  fn_entry_label root_tf = SOME lbl /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  EVERY wf_function C.ctx_functions /\
  joint_initial vs0 C q0 /\ joint_trace vs0 C q0 evs qs Q /\
  h <= LENGTH evs /\
  h < LENGTH (dftGasFromListTraceDefs$trace_blocks [] 0 fuel C root_tf root_entry) /\
  EL h (dftGasFromListTraceDefs$trace_blocks [] 0 fuel C root_tf root_entry) =
    ((a,e,inst.inst_id),tf,inst,v) ==>
  ?stk PG G tn oms om hs hist.
    EL h (q0::qs) = JointConfig stk PG G tn tf inst v oms om hs hist
Proof
  strip_tac >>
  `wf_function root_tf` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qpat_x_assum `joint_trace _ _ _ _ _ _` mp_tac >>
  simp[joint_trace_def] >> strip_tac >>
  qpat_x_assum `joint_initial _ _ _` mp_tac >>
  simp[Once joint_initial_cases] >> strip_tac >> gvs[] >>
  mp_tac (Q.INST [`P` |-> `\(_,f,i,s) q.
    ?stk PG G tn oms om hs hist. q = JointConfig stk PG G tn f i s oms om hs hist`]
    focus_native_joint_segments) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (drule_all o cj 3) >> simp[] >>
  disch_then (qspecl_then [`[]`, `0`, `fuel`, `h`] mp_tac) >> simp[]
QED

Theorem focus_guard_not_pseudo[local]:
  (inv_memory_observation i.inst_opcode \/ is_fallible i \/ i.inst_opcode = INVOKE) ==>
  ~is_pseudo i.inst_opcode
Proof
  Cases_on `i.inst_opcode` >>
  simp[dftGasInvCrossingProbeTheory.inv_memory_observation_def,dftDefsTheory.is_fallible_def,
       venomEffectsTheory.opcode_fail_class_def,is_pseudo_def]
QED

(* A retained target cursor yields the same guarded instruction in the source
   schedule.  At a strict-prefix cursor the earlier calls are still recorded. *)
Theorem focus_guarded_schedule_prefix[local]:
  !sched seen. dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM sched (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) sched ys /\
  k < LENGTH ys /\ k <= seen /\ q = EL k sched /\ i = EL k ys /\
  (inv_memory_observation i.inst_opcode \/ is_fallible i \/ i.inst_opcode = INVOKE) ==>
  q < LENGTH xs /\ EL q xs = i /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE seen sched))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `q < LENGTH xs /\ from_block [EL q xs] i` by
    (qpat_assum `LIST_REL _ sched ys` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     disch_then (fn th => mp_tac (CONJUNCT1 th) >> qspec_then `k` mp_tac (CONJUNCT2 th)) >>
     simp[]) >>
  `EL q xs = i` by (irule gasFocusSourceProviderTheory.focus_history_guard_source_inst >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
   (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE k sched))` by
    (Cases_on `inv_memory_observation i.inst_opcode`
     >- (irule dft_packet_memory_schedule_predecessors >>
         rpt (first_assum (irule_at Any)) >> metis_tac[]) >>
     irule dft_packet_schedule_predecessors >>
     rpt (first_assum (irule_at Any)) >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  `MEM r (TAKE k sched)` by metis_tac[] >>
  `TAKE k (TAKE seen sched) = TAKE k sched` by simp[rich_listTheory.TAKE_TAKE_T] >>
  metis_tac[rich_listTheory.MEM_TAKE]
QED

Theorem focus_trace_block_fragment_every[local]:
  !s.
    (!i t. MEM ((a,e,i.inst_id),tf,i,t) (trace_block a e fuel C tf bt s) /\
      s.vs_inst_idx <= t.vs_inst_idx /\ t.vs_inst_idx < B /\
      t.vs_current_bb = s.vs_current_bb /\
      get_instruction bt t.vs_inst_idx = SOME i ==>
      P ((a,e,i.inst_id),tf,i,t) /\ EVERY P (trace_step a e fuel C tf i t)) ==>
    EVERY P (trace_block a e fuel C tf
      (bt with bb_instructions := TAKE B bt.bb_instructions) s)
Proof
  measureInduct_on `LENGTH bt.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> strip_tac >> gvs[] >> disch_tac >>
  Cases_on `get_instruction (bt with bb_instructions := TAKE B bt.bb_instructions)
    s.vs_inst_idx`
  >- (once_rewrite_tac[dftGasFromListTraceDefsTheory.trace_defs] >> simp[]) >>
  rename1 `get_instruction _ s.vs_inst_idx = SOME head` >>
  `get_instruction bt s.vs_inst_idx = SOME head /\
    s.vs_inst_idx < LENGTH bt.bb_instructions /\ s.vs_inst_idx < B` by
    gvs[get_instruction_def, LENGTH_TAKE_EQ, EL_TAKE] >>
  qpat_assum `get_instruction bt s.vs_inst_idx = SOME head`
    (mp_then Any assume_tac trace_block_visit) >>
  `P ((a,e,head.inst_id),tf,head,s) /\ EVERY P (trace_step a e fuel C tf head s)` by
    (qpat_assum `!i t. _` (qspecl_then [`head`,`s`] mp_tac) >> simp[]) >>
  once_rewrite_tac[dftGasFromListTraceDefsTheory.trace_defs] >>
  simp[EVERY_APPEND] >>
  Cases_on `step_inst fuel C head s` >> simp[] >>
  Cases_on `is_terminator head.inst_opcode` >> simp[] >>
  rename1 `step_inst fuel C head s = OK post` >>
  drule_all_then strip_assume_tac venomInstPropsTheory.step_preserves_control_flow >>
  qpat_x_assum `!y. _` (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspec_then `post with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then irule >>
  rpt strip_tac >> qpat_assum `!i t. _` drule >>
  simp[trace_block_visit, MEM_APPEND]
QED

Theorem focus_packet_native_keys_distinct[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused ==>
  ALL_DISTINCT (MAP FST (trace_blocks [] 0 N C8 root_tf root_entry))
Proof
  rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
  qpat_assum `LIST_REL dft_fn_rel _ C8.ctx_functions`
    (mp_then Any mp_tac dftContractGasTheory.dft_ctx_block_ids_distinct) >>
  qpat_assum `lookup_function _ C8.ctx_functions = SOME root_tf`
    (mp_then Any mp_tac lookup_function_MEM) >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  irule (cj 3 dftGasFromListTraceNamesTheory.trace_names_distinct) >>
  simp[] >> qpat_assum `EVERY _ C8.ctx_functions`
    (qspec_then `root_tf` mp_tac o ONCE_REWRITE_RULE [EVERY_MEM]) >> simp[]
QED

Theorem focus_packet_returned_trace_step[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),nseen,front,closed,brest) /\
  MEM ((a,e,i.inst_id),tf,i,t) (trace_block a e (N-e) C8 tf bt be) /\
  t.vs_inst_idx = LENGTH ps + k /\ get_instruction bt t.vs_inst_idx = SOME i /\
  k < nseen /\ i.inst_opcode = INVOKE ==>
  ?q h done child_entry ir child_out caller_post csf ctf child_order child_rest.
    FLOOKUP calls (a,e,i.inst_id) =
      SOME (q,h,t,done,child_entry,SOME (ir,child_out,caller_post)) /\
    FLOOKUP acts ((e,i.inst_id)::a) =
      SOME (csf,ctf,e,child_entry,child_order,SOME (IntRet ir child_out),SOME child_rest) /\
    trace_step a e (N-e) C8 tf i t = trace_blocks ((e,i.inst_id)::a) e (N-e) C8 ctf child_entry
Proof
  strip_tac >>
  drule_then assume_tac focus_packet_native_keys_distinct >>
  qabbrev_tac `R = trace_blocks [] 0 N C8 root_tf root_entry` >>
  `bt.bb_instructions = ps ++ ys /\ LENGTH sched = LENGTH ys /\
   LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
     from_block [EL q xs] y) sched ys /\
   hbe <= j /\ j < LENGTH R /\ EL hbe R = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
   lookup_block be.vs_current_bb tf.fn_blocks = SOME bt` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_assum `!a e bb bt ps xs ys sched hin h0 body cnt front closed brest.
       FLOOKUP blocks (a,e) = _ ==> ?sf. _`
       (fn inv => qpat_assum `FLOOKUP blocks (a,e) = _`
         (mp_then Any (strip_assume_tac o SRULE []) inv)) >>
     unabbrev_all_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`(j,obs) = _`, `_ < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)`,
        `hbe <= _`, `EL hbe (trace_blocks [] 0 N C8 root_tf root_entry) = _`,
        `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`,
        `FLOOKUP acts a = SOME (_,_,_,_,_,_,_)`,
        `be.vs_current_bb = _`, `lookup_block bb.bb_label _ = SOME bt`,
        `bt.bb_instructions = _`, `LIST_REL _ sched ys`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >>
     gvs[LIST_REL_EL_EQN]) >>
  `k < LENGTH ys /\ i = EL k ys` by
    (qpat_x_assum `get_instruction bt t.vs_inst_idx = SOME i` mp_tac >>
     simp[get_instruction_def, EL_APPEND_EQN]) >>
  `hbe < LENGTH R` by decide_tac >>
  `R = trace_blocks [] 0 N C8 root_tf root_entry` by simp[Abbr `R`] >>
  drule_all focus_native_anchor >> strip_tac >> pop_assum kall_tac >>
  `MEM ((a,e,i.inst_id),tf,i,t) R` by
    (irule rich_listTheory.MEM_DROP_IMP >> qexists_tac `hbe` >>
     simp[MEM_APPEND] >> metis_tac[]) >>
  `EL k sched < LENGTH xs /\ EL (EL k sched) xs = i` by
    (qpat_assum `LIST_REL _ sched ys`
       (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     disch_then (qspec_then `k` mp_tac o CONJUNCT2) >>
     simp[] >> metis_tac[gasFocusSourceProviderTheory.focus_history_guard_source_inst]) >>
  `MEM (EL k sched) (TAKE nseen sched)` by
    (simp[MEM_EL] >> qexists_tac `k` >> simp[LENGTH_TAKE_EQ, EL_TAKE]) >>
  `?h b0 done child_entry ir child_out caller_post.
     FLOOKUP calls (a,e,i.inst_id) =
       SOME (EL k sched,h,b0,done,child_entry,SOME (ir,child_out,caller_post))` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_assum `!a e bb bt ps xs ys sched hin h0 be hbe cnt front closed brest.
       FLOOKUP blocks (a,e) = _ ==> !q. _`
       (fn inv => qpat_assum `FLOOKUP blocks (a,e) = _`
         (mp_then Any (qspec_then `EL k sched` mp_tac) inv)) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`MEM (EL k sched) (TAKE nseen sched)`, `EL k sched < LENGTH xs`,
        `EL (EL k sched) xs = i`, `i.inst_opcode = INVOKE`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
  `?c csf ctf child_order child_rest nm ops args.
     h < j /\ c.inst_id = i.inst_id /\ EL h R = ((a,e,i.inst_id),tf,c,b0) /\
     FLOOKUP acts ((e,i.inst_id)::a) =
       SOME (csf,ctf,e,child_entry,child_order,SOME (IntRet ir child_out),SOME child_rest) /\
     decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
     eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry` by
    (qpat_assum `FLOOKUP acts a = _` (mk_asm "parent") >>
     qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls (a,e,cid) = _ ==> ?sf. _`
       (fn inv => qpat_assum `FLOOKUP calls (a,e,i.inst_id) = _`
         (mp_then Any (strip_assume_tac o SRULE []) inv)) >>
     qpat_assum `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`
       (fn inv => qpat_assum `FLOOKUP acts (_::_) = _` (mp_then Any mp_tac inv)) >>
     asm_x "parent" mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP acts a = SOME (_,_,_,_,_,_,_)`,
        `FLOOKUP acts (_::_) = _`, `(j,obs) = _`,
        `h < j'`, `R = trace_blocks [] 0 N C8 root_tf root_entry`,
        `EL h (trace_blocks [] 0 N C8 root_tf root_entry) = _`,
        `_.inst_id = i.inst_id`, `decode_invoke _ = SOME _`,
        `lookup_function _ C8.ctx_functions = SOME _`,
        `eval_operands _ b0 = SOME _`, `setup_callee _ _ b0 = SOME child_entry`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     gvs[] >> Cases_on `child_rest` >> gvs[] >> metis_tac[]) >>
  `MEM ((a,e,i.inst_id),tf,c,b0) R` by metis_tac[EL_MEM, arithmeticTheory.LESS_TRANS] >>
  `((a,e,i.inst_id),tf,c,b0) = ((a,e,i.inst_id),tf,i,t)` by
    (drule dftCorrectnessTheory.all_distinct_map_mem_inj >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  pop_assum (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  qpat_x_assum `c = i` SUBST_ALL_TAC >>
  qpat_x_assum `b0 = t` SUBST_ALL_TAC >>
  drule_all trace_step_invoke >> strip_tac >>
  rpt (first_assum (irule_at Any))
QED

Theorem focus_packet_row_projection[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 body nseen front closed brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,nseen,front,closed,brest) ==>
  ?sp. MEM e order /\ e <= N /\
    lookup_block hin.vs_current_bb tf.fn_blocks = SOME bt /\
    bt.bb_instructions = ps ++ ys /\ EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    eval_phis hin bt.bb_instructions = OK sp /\
    (e = SUC inc ==> hin = entry) /\
    (e <> SUC inc ==>
      ?pb pt pps pxs pys prho pin ph pbe pc pu.
        FLOOKUP blocks (a,e-1) =
          SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu) /\
        ~hin.vs_halted) /\
    (e <> LAST order ==> closed /\ ?post. front = OK post /\ ~post.vs_halted) /\
    (e = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest) /\
    (closed <=> IS_SOME brest) /\ (body = NONE ==> ~closed) /\ nseen <= LENGTH ys /\
    (!be hbe. body = SOME (be,hbe) ==>
      be.vs_inst_idx = LENGTH ps /\ lookup_block be.vs_current_bb tf.fn_blocks = SOME bt /\
      FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
        (DROP (phi_prefix_length bt.bb_instructions) ps)
        (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
      FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE nseen ys) be = front /\
      (closed ==> nseen = LENGTH ys))
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h0 body nseen front closed brest.
    FLOOKUP blocks (a,e) = _ ==> ?sf. _`
    (fn inv => qpat_assum `FLOOKUP blocks (a,e) = _` (mp_then Any mp_tac inv)) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`,
     `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,_,_,OK _,F,NONE)`,
     `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,_,hin,h0,_,nseen,front,closed,brest)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >>
  rename1 `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,_,hin,h0,bentry,nseen,front,closed,brest)` >>
  `hin.vs_current_bb = bb.bb_label` by
    (qpat_assum `lookup_block hin.vs_current_bb _ = SOME bb`
       (mp_then Any mp_tac venomExecProofsTheory.lookup_block_label) >> simp[]) >>
  Cases_on `bentry`
  >- (Cases_on `e = SUC inc` >> gvs[]) >>
  PairCases_on `x` >> Cases_on `e = SUC inc` >> gvs[] >>
  qpat_assum `!F. N <= F ==> FOLDR _ _ _ _ = _`
    (qspec_then `N` mp_tac) >> simp[]
QED

Theorem focus_packet_activation_order[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
  wf_function tf /\ order <> [] /\
  (!r. r < LENGTH order ==> EL r order = inc + SUC r) /\
  (!e. MEM e order <=> (a,e) IN FDOM blocks)
Proof
  strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    (fn inv => qpat_assum `FLOOKUP acts a = _` (mp_then Any mp_tac inv)) >>
  qpat_assum `o1_ctx_shape C8` mp_tac >>
  qpat_assum `LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >>
  conj_tac
  >- (drule_all LIST_REL_MEM_IMP >> simp[] >> strip_tac >>
      drule dftContractGasTheory.o1_ctx_shape_wf_functions >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `order = GENLIST _ _` (fn th => once_rewrite_tac[th]) >> simp[EL_GENLIST]
QED

Theorem focus_target_body_shape[local]:
  bb_well_formed bt /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\ EVERY (\i. ~is_pseudo i.inst_opcode) ys ==>
  ys <> [] /\ is_terminator (LAST ys).inst_opcode /\
  phi_prefix_length bt.bb_instructions <= LENGTH ps /\
  EVERY (\i. ~is_terminator i.inst_opcode)
    (DROP (phi_prefix_length bt.bb_instructions) ps)
Proof
  strip_tac >>
  `!op. is_pseudo op ==> ~is_terminator op` by
    (Cases >> simp[is_pseudo_def,is_terminator_def]) >>
  `ys <> []` by
    (spose_not_then assume_tac >> gvs[bb_well_formed_def] >>
     drule LAST_MEM >> gvs[EVERY_MEM] >> metis_tac[]) >>
  simp[] >> rpt conj_tac
  >- fs[bb_well_formed_def,LAST_APPEND_NOT_NIL]
  >- (irule blockPrefixEquivTheory.phi_prefix_length_non_phi >>
      `0 < LENGTH ys` by (Cases_on `ys` >> gvs[]) >>
      simp[EL_APPEND_EQN] >>
      qpat_assum `EVERY (\i. ~is_pseudo i.inst_opcode) ys`
        (mp_tac o REWRITE_RULE [EVERY_EL]) >>
      disch_then (qspec_then `0` mp_tac) >> simp[] >>
      metis_tac[CONJUNCT1 is_pseudo_def]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule rich_listTheory.MEM_DROP_IMP >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem focus_packet_completed_row_segment[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    r bb bt ps xs ys rho hin h0 body nseen front brest P.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  r < LENGTH order /\ e = EL r order /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,nseen,front,T,brest) /\
  (!sp be hbe. eval_phis hin bt.bb_instructions = OK sp /\ body = SOME (be,hbe) ==>
    EVERY P (trace_block a e (N-e) C8 tf
      (bt with bb_instructions := TAKE (LENGTH ps) bt.bb_instructions)
      (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions)) /\
    EVERY P (trace_block a e (N-e) C8 tf
      (bt with bb_instructions := TAKE (LENGTH ps + nseen) bt.bb_instructions) be)) ==>
  ?seg. EVERY P seg /\ e = inc + SUC r /\ e <= N /\
    (r = 0 ==> hin = entry) /\
    trace_blocks a (inc+r) (N-(inc+r)) C8 tf hin = seg ++
      (case front of OK post => if post.vs_halted then [] else trace_blocks a e (N-e) C8 tf post
       | _ => []) /\
    (SUC r < LENGTH order ==>
      ?post nb nt nps nxs nys nrho nh0 nbody nc nf nclosed nr.
        front = OK post /\ ~post.vs_halted /\
        FLOOKUP blocks (a,EL (SUC r) order) =
          SOME (nb,nt,nps,nxs,nys,nrho,post,nh0,nbody,nc,nf,nclosed,nr)) /\
    (SUC r = LENGTH order ==> res = SOME front /\ ?ir out. front = IntRet ir out)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all focus_packet_activation_order >> strip_tac >>
  drule_all focus_packet_row_projection >> strip_tac >>
  `e = inc + SUC r` by simp[] >>
  `bb_well_formed bt` by (gvs[wf_function_def] >> metis_tac[venomExecProofsTheory.lookup_block_MEM]) >>
  drule_all focus_target_body_shape >> strip_tac >>
  rename1 `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,_,hin,h0,bentry,nseen,front,T,brest)` >>
  Cases_on `bentry` >- gvs[] >> PairCases_on `x` >> rename1 `SOME (be,hbe) = SOME _` >>
  qpat_x_assum `!be' hbe'. SOME (be,hbe) = _ ==> _`
    (qspecl_then [`be`,`hbe`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!sp be' hbe'. _ ==> EVERY _ _ /\ _`
    (qspecl_then [`sp`,`be`,`hbe`] mp_tac) >> simp[] >> strip_tac >>
  qabbrev_tac `start = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions` >>
  `trace_block a e (N-e) C8 tf bt start =
    trace_block a e (N-e) C8 tf
      (bt with bb_instructions := TAKE (LENGTH ps) bt.bb_instructions) start ++
    trace_block a e (N-e) C8 tf bt be` by
    (`start.vs_inst_idx + (LENGTH ps - phi_prefix_length bt.bb_instructions) = LENGTH ps` by
       gvs[Abbr `start`] >>
     pop_assum (fn th => once_rewrite_tac[GSYM th]) >>
     irule (cj 2 native_trace_block_prefix_split) >>
     simp[Abbr `start`,GSYM DROP_TAKE,TAKE_APPEND,TAKE_LENGTH_TOO_LONG] >> gvs[]) >>
  `EVERY P (trace_block a e (N-e) C8 tf bt start)` by
    (qpat_assum `trace_block _ _ _ _ _ _ start = _`
       (fn th => once_rewrite_tac [th]) >>
     qpat_x_assum `EVERY P (trace_block _ _ _ _ _ _ be)` mp_tac >>
     qpat_x_assum `EVERY P (trace_block _ _ _ _ _ _ (sp with vs_inst_idx := _))` mp_tac >>
     `TAKE (LENGTH ps + LENGTH ys) (ps ++ ys) = ps ++ ys` by
       (once_rewrite_tac[GSYM LENGTH_APPEND] >> simp[]) >>
     `bt with bb_instructions := ps ++ ys = bt` by
       (qpat_assum `bt.bb_instructions = _` (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
     simp[Abbr `start`,EVERY_APPEND]) >>
  `N - (inc+r) = SUC (N-e) /\ SUC (inc+r) = e` by decide_tac >>
  `trace_blocks a (inc+r) (N-(inc+r)) C8 tf hin =
     trace_block a e (N-e) C8 tf bt start ++
     (case front of OK post => if post.vs_halted then [] else trace_blocks a e (N-e) C8 tf post
      | _ => [])` by
    (qpat_x_assum `N - (inc+r) = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `SUC (inc+r) = e` (fn th => once_rewrite_tac[GSYM th]) >>
     irule focus_closed_native_row >>
     conj_tac >- simp[] >>
     conj_tac >- (qexists_tac `sp` >> simp[Abbr `start`]) >>
     map_every qexists_tac [`be`,`ps`,`ys`] >>
     `SUC (inc + r) = inc + SUC r` by decide_tac >>
     pop_assum (fn th => once_rewrite_tac[th]) >>
     simp[Abbr `start`,TAKE_LENGTH_ID_rwt] >>
     qpat_x_assum `FOLDR _ OK (TAKE nseen ys) be = front` mp_tac >>
     simp[TAKE_LENGTH_ID_rwt]) >>
  qexists_tac `trace_block a e (N-e) C8 tf bt start` >>
  qpat_x_assum `trace_block _ _ _ _ _ _ start = _` kall_tac >>
  simp[] >>
  `LAST order = inc + LENGTH order` by
    (simp[LAST_EL] >> `PRE (LENGTH order) < LENGTH order` by decide_tac >>
     simp[] >> decide_tac) >>
  conj_tac
  >- (strip_tac >>
      `EL (SUC r) order = inc + SUC (SUC r)` by simp[] >>
      `(a,EL (SUC r) order) IN FDOM blocks` by
        (qpat_assum `!k. MEM k order <=> _` (qspec_then `EL (SUC r) order` (fn th => once_rewrite_tac[GSYM th])) >>
         irule EL_MEM >> simp[]) >>
      Cases_on `FLOOKUP blocks (a,EL (SUC r) order)` >- gvs[FLOOKUP_DEF] >>
      PairCases_on `x` >>
      qpat_assum `FLOOKUP blocks (a,EL (SUC r) order) = SOME _`
        (mp_then (Pat `FLOOKUP blocks _ = _`) mp_tac focus_packet_row_projection) >>
      disch_then (drule_all_then strip_assume_tac) >>
      `EL (SUC r) order <> SUC inc /\ EL (SUC r) order - 1 = e` by decide_tac >>
      qpat_x_assum `EL (SUC r) order <> SUC inc ==> _`
        (fn th => first_assum (mp_then Any strip_assume_tac th)) >>
      qpat_x_assum `EL (SUC r) order - 1 = e` SUBST_ALL_TAC >>
      gvs[]) >>
  strip_tac >> `e = LAST order` by decide_tac >>
  `res = SOME front /\ nrest = brest` by simp[] >>
  Cases_on `brest` >> gvs[] >>
  drule_all dft_packet_closed_activation_return >> simp[]
QED

Theorem focus_packet_live_boundary[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst st oms om hs hist raw_slots sites unused
    a e sf tf inc entry order bb bt ps xs ys sched hin h0 body nseen front sp.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst st oms om hs hist) raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
  e = LAST order /\ eval_phis hin bt.bb_instructions = OK sp /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,body,nseen,front,F,NONE) ==>
  (a = p /\ e = d /\ tf = fn /\ front = OK st /\
    get_instruction bt st.vs_inst_idx = SOME inst /\
    (case body of
       NONE => phi_prefix_length bt.bb_instructions <= st.vs_inst_idx /\
         st.vs_inst_idx < LENGTH ps /\
         FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
           (DROP (phi_prefix_length bt.bb_instructions) (TAKE st.vs_inst_idx ps))
           (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK st
     | SOME _ => st.vs_inst_idx = LENGTH ps + nseen /\ nseen < LENGTH ys)) \/
  (?be hbe b0 c csf ctf child_entry child_order.
    body = SOME (be,hbe) /\ front = OK b0 /\
    b0.vs_inst_idx = LENGTH ps + nseen /\ get_instruction bt b0.vs_inst_idx = SOME c /\
    c.inst_opcode = INVOKE /\
    FLOOKUP acts ((e,c.inst_id)::a) =
      SOME (csf,ctf,e,child_entry,child_order,NONE,NONE) /\
    trace_step a e (N-e) C8 tf c b0 =
      trace_blocks ((e,c.inst_id)::a) e (N-e) C8 ctf child_entry)
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  Cases_on `a = p`
  >- (disj1_tac >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`JointConfig _ _ _ _ fn inst st _ _ _ _ = _`,
         `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE)`,
         `FLOOKUP acts p = SOME (_,_,_,_,_,NONE,NONE)`,
         `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,_,nseen,front,F,NONE)`,
         `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,_,_,OK _,F,NONE)`,
         `e = LAST order`, `LAST _ = d`, `a = p`,
         `eval_phis hin bt.bb_instructions = OK sp`,
         `get_instruction _ _ = SOME _`,
         `(case _ of NONE => _ | SOME _ => _)`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      gvs[] >> rename1 `(case bdy of NONE => _ | SOME _ => _)` >>
      Cases_on `bdy` >> gvs[]) >>
  disj2_tac >>
  `?k. k < LENGTH p /\ a = DROP (SUC k) p` by
    (qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (fn inv => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE)`
          (mp_then Any mp_tac inv)) >>
     qpat_assum `a <> p` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[MEM_GENLIST] >> BETA_TAC >> rpt strip_tac >>
     rename1 `a = DROP ix p` >> namedCases_on `ix` ["", "k0"] >> gvs[] >>
     qexists_tac `k0` >> simp[]) >>
  qpat_assum `!k. _ ==> ?sf tf inc entry order bb bt. _`
    (qspec_then `k` (fn th =>
      qpat_assum `k < LENGTH p` (mp_then Any strip_assume_tac th))) >>
  `?q h cb done child cid.
     FLOOKUP calls (a,e,cid) = SOME (q,h,cb,done,child,NONE) /\
     (?be hbe. body' = SOME (be,hbe)) /\
     cb.vs_inst_idx = LENGTH ps + nseen /\ front = OK cb` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE)`,
        `FLOOKUP acts _ = SOME (_,_,_,_,_,NONE,NONE)`,
        `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,_,nseen,front,F,NONE)`,
        `FLOOKUP blocks (_,_) = SOME (_,_,_,_,_,_,_,_,SOME _,_,OK _,F,NONE)`,
        `e = LAST order`, `LAST _ = _`, `a = DROP (SUC k) p`,
        `_ = DROP (SUC k) p`,
        `FLOOKUP calls (_,_,_) = SOME (_,_,_,_,_,NONE)`,
        `_.vs_inst_idx = LENGTH _ + _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >> metis_tac[]) >>
  qpat_assum `FLOOKUP calls (a,e,_) = SOME (_,_,cb,_,_,NONE)`
    (fn th => qpat_assum `!a e cid q h b0 done child ret. FLOOKUP calls (a,e,cid) = _ ==> ?sf. _`
       (fn inv => mp_then Any (strip_assume_tac o SRULE []) inv th)) >>
  qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    (fn inv => qpat_assum `FLOOKUP acts ((e,_)::a) = SOME _`
      (mp_then Any (strip_assume_tac o SRULE []) inv)) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE)`,
     `FLOOKUP acts a = SOME (_,_,_,_,_,_,_)`,
     `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,_,nseen,front,F,NONE)`,
     `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_)`,
     `front = OK cb`, `cb.vs_inst_idx = LENGTH ps + nseen`,
     `get_instruction _ cb.vs_inst_idx = SOME _`, `_.inst_id = _`, `_.inst_opcode = INVOKE`,
     `FLOOKUP acts ((e,_)::a) = SOME (_,_,_,_,_,NONE,_)`, `child_rest = NONE`,
     `decode_invoke _ = SOME _`, `lookup_function _ C8.ctx_functions = SOME _`,
     `eval_operands _ cb = SOME _`, `setup_callee _ _ cb = SOME _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >>
  metis_tac[trace_step_invoke]
QED

Theorem focus_native_live_split[local]:
  bb_well_formed bt /\ s.vs_inst_idx <= t.vs_inst_idx /\
  t.vs_inst_idx < LENGTH bt.bb_instructions /\
  FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK
    (DROP s.vs_inst_idx (TAKE t.vs_inst_idx bt.bb_instructions)) s = OK t ==>
  trace_block a e fuel C tf bt s =
    trace_block a e fuel C tf
      (bt with bb_instructions := TAKE t.vs_inst_idx bt.bb_instructions) s ++
    trace_block a e fuel C tf bt t /\
  t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  qabbrev_tac `k = t.vs_inst_idx - s.vs_inst_idx` >>
  `s.vs_inst_idx + k = t.vs_inst_idx` by gvs[Abbr `k`] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE k (DROP s.vs_inst_idx bt.bb_instructions))` by
    (simp[EVERY_EL,LENGTH_TAKE,LENGTH_DROP,EL_TAKE,EL_DROP] >>
     rpt strip_tac >>
     qpat_assum `bb_well_formed bt`
       (qspec_then `n + s.vs_inst_idx` mp_tac o
        CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE [bb_well_formed_def]) >>
     simp[] >> decide_tac) >>
  qpat_x_assum `FOLDR _ OK (DROP _ _) s = OK t` (assume_tac o REWRITE_RULE [DROP_TAKE]) >>
  `FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK
    (TAKE k (DROP s.vs_inst_idx bt.bb_instructions)) s = OK t` by simp[Abbr `k`] >>
  conj_tac
  >- (`s.vs_inst_idx + k <= LENGTH bt.bb_instructions` by simp[] >>
      drule_all (cj 2 native_trace_block_prefix_split) >> simp[]) >>
  drule_all dftAvailabilityTheory.dft_prefix_frame >> simp[]
QED

Theorem focus_native_live_body_split[local]:
  bb_well_formed bt /\ bt.bb_instructions = ps ++ ys /\
  s.vs_inst_idx <= LENGTH ps /\ be.vs_inst_idx = LENGTH ps /\
  t.vs_inst_idx = LENGTH ps + m /\ get_instruction bt t.vs_inst_idx = SOME c /\
  FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK (DROP s.vs_inst_idx ps) s = OK be /\
  FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK (TAKE m ys) be = OK t ==>
  trace_block a e fuel C tf bt s =
    trace_block a e fuel C tf (bt with bb_instructions := TAKE (LENGTH ps) bt.bb_instructions) s ++
    trace_block a e fuel C tf (bt with bb_instructions := TAKE (LENGTH ps + m) bt.bb_instructions) be ++
    trace_block a e fuel C tf bt t /\
  MEM ((a,e,c.inst_id),tf,c,t) (trace_block a e fuel C tf bt be) /\
  t.vs_current_bb = be.vs_current_bb
Proof
  strip_tac >>
  `t.vs_inst_idx < LENGTH bt.bb_instructions` by fs[get_instruction_def] >>
  `TAKE (LENGTH ps) bt.bb_instructions = ps /\
   TAKE (LENGTH ps + m) bt.bb_instructions = ps ++ TAKE m ys` by
    simp[TAKE_APPEND,TAKE_LENGTH_TOO_LONG] >>
  `FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK
     (DROP be.vs_inst_idx (TAKE t.vs_inst_idx bt.bb_instructions)) be = OK t` by
    simp[TAKE_APPEND,TAKE_LENGTH_TOO_LONG,DROP_APPEND] >>
  `FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK
     (DROP s.vs_inst_idx (TAKE be.vs_inst_idx bt.bb_instructions)) s = OK be` by
    simp[TAKE_APPEND,TAKE_LENGTH_TOO_LONG] >>
  `be.vs_inst_idx < LENGTH bt.bb_instructions /\ s.vs_inst_idx <= be.vs_inst_idx /\
   be.vs_inst_idx <= t.vs_inst_idx` by decide_tac >>
  map_every (fn pat => qpat_assum pat
    (mp_then (Pat `FOLDR _ _ _ _ = _`) (drule_all_then strip_assume_tac)
      focus_native_live_split))
    [`FOLDR _ OK (DROP _ _) s = OK be`, `FOLDR _ OK (DROP _ _) be = OK t`] >>
  gvs[TAKE_APPEND,TAKE_LENGTH_TOO_LONG] >>
  once_rewrite_tac[trace_defs] >> simp[]
QED

Theorem focus_packet_live_row_split[local]:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d stk PG G tn fn inst st oms om hs hist raw_slots sites unused
    a e sf tf inc entry order bb bt ps xs ys sched hin h0 bentry nseen front P.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst st oms om hs hist) raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
  0 < e /\ e = LAST order /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,bentry,nseen,front,F,NONE) /\
  (!sp B. eval_phis hin bt.bb_instructions = OK sp /\ B <= LENGTH ps ==>
    EVERY P (trace_block a e (N-e) C8 tf
      (bt with bb_instructions := TAKE B bt.bb_instructions)
      (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions))) /\
  (!be hbe m. bentry = SOME (be,hbe) /\ m <= nseen ==>
    EVERY P (trace_block a e (N-e) C8 tf
      (bt with bb_instructions := TAKE (LENGTH ps + m) bt.bb_instructions) be)) /\
  (!be hbe b0 c. bentry = SOME (be,hbe) /\ b0.vs_inst_idx = LENGTH ps + nseen /\
    lookup_block b0.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt b0.vs_inst_idx = SOME c /\
    MEM ((a,e,c.inst_id),tf,c,b0) (trace_block a e (N-e) C8 tf bt be) ==>
    P ((a,e,c.inst_id),tf,c,b0)) /\
  (!cid csf ctf child_entry child_order.
    FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,child_entry,child_order,NONE,NONE) ==>
    ?l r. trace_blocks ((e,cid)::a) e (N-e) C8 ctf child_entry =
      l ++ [((p,d,inst.inst_id),fn,inst,st)] ++ r /\ EVERY P l) ==>
  ?l r. trace_blocks a (e-1) (N-(e-1)) C8 tf hin =
    l ++ [((p,d,inst.inst_id),fn,inst,st)] ++ r /\ EVERY P l
Proof
  rpt gen_tac >> strip_tac >>
  drule_all focus_packet_activation_order >> strip_tac >>
  drule_all focus_packet_row_projection >> strip_tac >>
  `bb_well_formed bt` by (gvs[wf_function_def] >> metis_tac[lookup_block_MEM]) >>
  drule_all focus_target_body_shape >> strip_tac >>
  `SUC (e-1) = e /\ N-(e-1) = SUC (N-e)` by decide_tac >>
  qabbrev_tac `start = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions` >>
  `?tail. trace_blocks a (e-1) (N-(e-1)) C8 tf hin =
      trace_block a e (N-e) C8 tf bt start ++ tail` by
    (qpat_assum `N - (e-1) = _` (fn th => once_rewrite_tac[th]) >>
     drule_all trace_blocks_enter >>
     disch_then (qspecl_then [`a`,`N-e`,`e-1`,`C8`] mp_tac) >> simp[Abbr `start`]) >>
  drule_all_then assume_tac focus_packet_live_boundary >>
  qpat_x_assum `e = LAST order` kall_tac >>
  Cases_on `bentry`
  >- (gvs[] >>
      `start.vs_inst_idx <= st.vs_inst_idx /\ st.vs_inst_idx < LENGTH bt.bb_instructions` by
        gvs[Abbr `start`] >>
      `st.vs_inst_idx - LENGTH ps = 0` by decide_tac >>
      `FOLDR (dftIndexedExec$dft_exec_cons (N - LAST order) C8) OK
        (DROP start.vs_inst_idx (TAKE st.vs_inst_idx bt.bb_instructions)) start = OK st` by
        simp[Abbr `start`,TAKE_APPEND] >>
      drule_all focus_native_live_split >> strip_tac >>
      `?rest. trace_block a (LAST order) (N - LAST order) C8 fn bt st =
          [((a,LAST order,inst.inst_id),fn,inst,st)] ++ rest` by
        (once_rewrite_tac[trace_defs] >> simp[]) >>
      qexists_tac `trace_block a (LAST order) (N - LAST order) C8 fn
        (bt with bb_instructions := TAKE st.vs_inst_idx bt.bb_instructions) start` >>
      qexists_tac `rest ++ tail` >> simp[APPEND_ASSOC,Abbr `start`]) >>
  PairCases_on `x` >>
  qpat_x_assum `!be hbe. _ ==> be.vs_inst_idx = _ /\ _`
    (qspecl_then [`x0`,`x1`] (strip_assume_tac o SRULE [])) >>
  `FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
      (DROP start.vs_inst_idx ps) start = OK x0 /\ start.vs_inst_idx <= LENGTH ps` by
    (simp[Abbr `start`] >> metis_tac[]) >>
  `EVERY P (trace_block a e (N-e) C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps) bt.bb_instructions) start)` by
    (qpat_assum `!sp B. _ ==> EVERY P _`
       (qspecl_then [`sp`,`LENGTH ps`] mp_tac) >> simp[Abbr `start`]) >>
  `EVERY P (trace_block a e (N-e) C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps + nseen) bt.bb_instructions) x0)` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `_ \/ _` (strip_assume_tac o SRULE [])
  >- (map_every (fn pat => qpat_x_assum pat (SUBST_ALL_TAC o SYM))
        [`a = p`, `e = d`, `tf = fn`] >>
      qpat_x_assum `front = OK st` SUBST_ALL_TAC >>
      drule_all focus_native_live_body_split >> strip_tac >>
      `?rest. trace_block a e (N-e) C8 tf bt st = [((a,e,inst.inst_id),tf,inst,st)] ++ rest` by
        (once_rewrite_tac[trace_defs] >> simp[]) >>
      qexists_tac `trace_block a e (N-e) C8 tf
        (bt with bb_instructions := TAKE (LENGTH ps) bt.bb_instructions) start ++
        trace_block a e (N-e) C8 tf
        (bt with bb_instructions := TAKE (LENGTH ps + nseen) bt.bb_instructions) x0` >>
      qexists_tac `rest ++ tail` >> simp[APPEND_ASSOC]) >>
  qpat_x_assum `front = OK b0` SUBST_ALL_TAC >>
  drule_all focus_native_live_body_split >>
  disch_then (qspecl_then [`tf`,`e`,`a`] strip_assume_tac) >>
  `P ((a,e,c.inst_id),tf,c,b0)` by
    (qpat_assum `!be hbe b0 c. _ ==> P _` irule >> simp[]) >>
  qpat_assum `!cid csf ctf child_entry child_order. _ ==> _`
    (drule_then strip_assume_tac) >>
  `?rest. trace_block a e (N-e) C8 tf bt b0 =
    [((a,e,c.inst_id),tf,c,b0)] ++
    trace_blocks ((e,c.inst_id)::a) e (N-e) C8 ctf child_entry ++ rest` by
    (once_rewrite_tac[cj 2 trace_defs] >> simp[]) >>
  qexists_tac `trace_block a e (N-e) C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps) bt.bb_instructions) start ++
    trace_block a e (N-e) C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps + nseen) bt.bb_instructions) x0 ++
    [((a,e,c.inst_id),tf,c,b0)] ++ l` >>
  qexists_tac `r ++ rest ++ tail` >> simp[APPEND_ASSOC]
QED

(* The schedule and native entry anchor belong to this very same row. *)
Theorem focus_packet_direct_row_data[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,beopt,nseen,front,closed,brest) ==>
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM sched (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) sched ys /\
  (!be hbe. beopt = SOME (be,hbe) ==>
    hbe <= j /\ be.vs_inst_idx = LENGTH ps /\
    lookup_block be.vs_current_bb tf.fn_blocks = SOME bt /\
    EL hbe (trace_blocks [] 0 N C8 root_tf root_entry) =
      ((a,e,(HD ys).inst_id),tf,HD ys,be))
Proof
  strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h0 body seen front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn inv => qpat_assum `FLOOKUP blocks (a,e) = _` (mp_then Any mp_tac inv)) >>
  qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    (fn inv => qpat_assum `FLOOKUP acts a = _` (mp_then Any mp_tac inv)) >>
  qpat_assum `_ < LENGTH (trace_blocks _ _ _ _ _ _)` mp_tac >>
  qpat_assum `(j,obs) = _` mp_tac >>
  qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >>
  gvs[] >> rpt strip_tac >> gvs[]
QED

Theorem focus_native_anchor_le[local]:
  ALL_DISTINCT (MAP FST R) /\ h < LENGTH R /\ EL h R = v /\
  MEM v (DROP hbe R) ==> hbe <= h
Proof
  simp[MEM_DROP] >> rpt strip_tac >>
  `EL h (MAP FST R) = EL (m + hbe) (MAP FST R)` by simp[EL_MAP] >>
  `h < LENGTH (MAP FST R) /\ m + hbe < LENGTH (MAP FST R)` by simp[] >>
  `h = m + hbe` by metis_tac[ALL_DISTINCT_EL_IMP] >> decide_tac
QED

Theorem focus_packet_direct_visit_row[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  R = trace_blocks [] 0 N C8 root_tf root_entry /\
  h < j /\ EL h R = ((a,e,i.inst_id),tf,i,t) /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,beopt,nseen,front,closed,brest) /\
  get_instruction bt t.vs_inst_idx = SOME i /\
  (t.vs_inst_idx < LENGTH ps \/
   ?be hbe k. beopt = SOME (be,hbe) /\
     t.vs_inst_idx = LENGTH ps + k /\ k <= nseen /\
     lookup_block t.vs_current_bb tf.fn_blocks = SOME bt /\
     MEM ((a,e,i.inst_id),tf,i,t) (trace_block a e (N-e) C8 tf bt be)) ==>
  (inv_memory_observation i.inst_opcode \/ is_fallible i \/ i.inst_opcode = INVOKE) ==>
  ?be hbe k q.
    beopt = SOME (be,hbe) /\ hbe <= h /\
    lookup_block t.vs_current_bb tf.fn_blocks = SOME bt /\
    LENGTH ps <= t.vs_inst_idx /\ k = t.vs_inst_idx - LENGTH ps /\
    k < LENGTH ys /\ k <= nseen /\ EL k ys = i /\
    EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k ys) /\
    FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE k ys) be = OK t /\
    k < LENGTH sched /\ q = EL k sched /\ q < LENGTH xs /\ EL q xs = i /\
    EVERY (\x. ~is_terminator x.inst_opcode) (TAKE q xs) /\
    (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE nseen sched))
Proof
  strip_tac >> disch_tac >>
  drule_all focus_packet_direct_row_data >> strip_tac
  >- (drule focus_guard_not_pseudo >>
      gvs[get_instruction_def,EL_APPEND_EQN,EVERY_EL]) >>
  qpat_x_assum `!be hbe. _ ==> hbe <= j /\ _`
    (qspecl_then [`be`,`hbe`] mp_tac) >> simp[] >> strip_tac >>
  `EL hbe R = ((a,e,(HD ys).inst_id),tf,HD ys,be)` by simp[] >>
  `hbe < LENGTH R /\ h < LENGTH R` by gvs[] >>
  `k < LENGTH ys /\ EL k ys = i` by gvs[get_instruction_def,EL_APPEND_EQN] >>
  `EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k ys) /\
   FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE k ys) be = OK t` by
    (drule focus_native_visit_row_prefix >> gvs[DROP_APPEND]) >>
  `hbe <= h` by
    (`MEM ((a,e,i.inst_id),tf,i,t) (DROP hbe R)` by
       (qpat_x_assum `EL h R = _` kall_tac >>
        drule_all focus_native_anchor >> strip_tac >> fs[MEM_APPEND]) >>
     drule_then assume_tac focus_packet_native_keys_distinct >>
     qpat_assum `MEM _ (DROP hbe R)`
       (mp_then (Pat `MEM _ (DROP _ _)`) mp_tac focus_native_anchor_le) >>
     disch_then irule >> simp[]) >>
  `k < LENGTH sched` by fs[LIST_REL_EL_EQN] >>
  `EL k sched < LENGTH xs /\ EL (EL k sched) xs = i /\
   EVERY (\x. ~is_terminator x.inst_opcode) (TAKE (EL k sched) xs) /\
   (!r. r < EL k sched /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE nseen sched))` by
    (irule focus_guarded_schedule_prefix >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  simp[]
QED

Theorem focus_packet_pseudo_fragment_every[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,beopt,nseen,front,closed,brest) /\
  eval_phis hin bt.bb_instructions = OK sp /\ B <= LENGTH ps /\
  (!i t. get_instruction bt t.vs_inst_idx = SOME i /\ t.vs_inst_idx < LENGTH ps ==>
    P ((a,e,i.inst_id),tf,i,t)) ==>
  EVERY P (trace_block a e (N-e) C8 tf
    (bt with bb_instructions := TAKE B bt.bb_instructions)
    (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions))
Proof
  strip_tac >> drule_all focus_packet_row_projection >> strip_tac >>
  irule focus_trace_block_fragment_every >> rpt gen_tac >> strip_tac >>
  rename1 `get_instruction bt t.vs_inst_idx = SOME i` >>
  `t.vs_inst_idx < LENGTH ps` by decide_tac >>
  conj_tac >- (first_x_assum irule >> simp[]) >>
  `EL t.vs_inst_idx ps = i` by gvs[get_instruction_def,EL_APPEND_EQN] >>
  `is_pseudo i.inst_opcode` by
    (qpat_assum `EVERY _ ps` (qspec_then `t.vs_inst_idx` mp_tac o REWRITE_RULE [EVERY_EL]) >> simp[]) >>
  `i.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_pseudo_def]) >>
  simp[trace_step_noninvoke]
QED

Theorem focus_packet_body_fragment_every[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),nseen,front,closed,brest) /\
  m <= nseen /\
  (!i t k. MEM ((a,e,i.inst_id),tf,i,t) (trace_block a e (N-e) C8 tf bt be) /\
    t.vs_inst_idx = LENGTH ps + k /\ k <= nseen /\
    lookup_block t.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt t.vs_inst_idx = SOME i ==> P ((a,e,i.inst_id),tf,i,t)) /\
  (!cid csf ctf child_entry child_order ir child_out child_rest.
    FLOOKUP acts ((e,cid)::a) =
      SOME (csf,ctf,e,child_entry,child_order,SOME (IntRet ir child_out),SOME child_rest) ==>
    EVERY P (trace_blocks ((e,cid)::a) e (N-e) C8 ctf child_entry)) ==>
  EVERY P (trace_block a e (N-e) C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps + m) bt.bb_instructions) be)
Proof
  strip_tac >> drule_all focus_packet_row_projection >> strip_tac >>
  `be.vs_inst_idx = LENGTH ps /\ lookup_block be.vs_current_bb tf.fn_blocks = SOME bt` by
    (qpat_assum `!b h. _ ==> b.vs_inst_idx = _ /\ _`
       (qspecl_then [`be`,`hbe`] mp_tac) >> simp[]) >>
  irule focus_trace_block_fragment_every >> rpt gen_tac >> strip_tac >>
  rename1 `get_instruction bt t.vs_inst_idx = SOME i` >>
  qabbrev_tac `k = t.vs_inst_idx - LENGTH ps` >>
  `t.vs_inst_idx = LENGTH ps + k /\ k < nseen` by gvs[Abbr `k`] >>
  `lookup_block t.vs_current_bb tf.fn_blocks = SOME bt` by simp[] >>
  conj_tac
  >- (qpat_assum `!i t k. _ ==> P _` irule >> simp[]) >>
  Cases_on `i.inst_opcode = INVOKE` >- (
    PairCases_on `packet` >> drule_all focus_packet_returned_trace_step >> strip_tac >>
    simp[] >> qpat_assum `!cid csf ctf ce co ir cu cr. _ ==> EVERY P _` irule >>
    goal_assum (drule_at Any)) >>
  simp[trace_step_noninvoke]
QED

Theorem focus_packet_first_row[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
  0 < LENGTH order /\
  ?bb bt ps xs ys sched h0 beopt nseen front closed brest.
    FLOOKUP blocks (a,EL 0 order) =
      SOME (bb,bt,ps,xs,ys,sched,entry,h0,beopt,nseen,front,closed,brest)
Proof
  strip_tac >> drule_all focus_packet_activation_order >> strip_tac >>
  `0 < LENGTH order` by simp[LENGTH_NON_NIL] >> simp[] >>
  `(a,EL 0 order) IN FDOM blocks` by metis_tac[EL_MEM] >>
  Cases_on `FLOOKUP blocks (a,EL 0 order)` >- gvs[FLOOKUP_DEF] >>
  PairCases_on `x` >> drule_all focus_packet_row_projection >> strip_tac >>
  gvs[]
QED

Theorem focus_packet_suffix_every[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst st oms om hs hist) raw_slots sites unused /\
  (!a sf tf inc entry order res nrest e bb bt ps xs ys sched hin h0 beopt nseen front closed brest i t.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,beopt,nseen,front,closed,brest) /\
    get_instruction bt t.vs_inst_idx = SOME i /\ t.vs_inst_idx < LENGTH ps ==>
    P ((a,e,i.inst_id),tf,i,t)) /\
  (!a sf tf inc entry order res nrest e bb bt ps xs ys sched hin h0 be hbe nseen front closed brest i t k.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),nseen,front,closed,brest) /\
    MEM ((a,e,i.inst_id),tf,i,t) (trace_block a e (N-e) C8 tf bt be) /\
    t.vs_inst_idx = LENGTH ps + k /\ k <= nseen /\
    lookup_block t.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt t.vs_inst_idx = SOME i ==> P ((a,e,i.inst_id),tf,i,t)) ==>
  !n a sf tf inc entry order res nrest r hin bb bt ps xs ys sched h0 beopt nseen front closed brest.
  n = N-(inc+r) /\ FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  r < LENGTH order /\
  FLOOKUP blocks (a,EL r order) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,beopt,nseen,front,closed,brest) ==>
  (IS_SOME res ==> EVERY P (trace_blocks a (inc+r) n C8 tf hin)) /\
  (res = NONE ==> ?l u. trace_blocks a (inc+r) n C8 tf hin =
      l ++ [((p,d,inst.inst_id),fn,inst,st)] ++ u /\ EVERY P l)
Proof
  strip_tac >> completeInduct_on `n` >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `e = EL r order` >>
  drule_all focus_packet_activation_order >> strip_tac >>
  drule_all focus_packet_row_projection >> strip_tac >>
  `e = inc + SUC r` by simp[Abbr `e`] >>
  `N-e < n` by decide_tac >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `N-e` (fn ih => qpat_assum `N-e < n` (assume_tac o MATCH_MP ih))) >>
  `!cid csf ctf ce co cr cns.
     FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,ce,co,cr,cns) ==>
     (IS_SOME cr ==> EVERY P (trace_blocks ((e,cid)::a) e (N-e) C8 ctf ce)) /\
     (cr = NONE ==> ?l u. trace_blocks ((e,cid)::a) e (N-e) C8 ctf ce =
       l ++ [((p,d,inst.inst_id),fn,inst,st)] ++ u /\ EVERY P l)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `FLOOKUP acts ((e,_)::a) = SOME _`
       (mp_then Any mp_tac focus_packet_first_row) >>
     disch_then (drule_all_then strip_assume_tac) >>
     qpat_assum `!a sf tf inc entry order res nrest r hin bb bt ps xs ys sched h0 beopt nseen front closed brest.
       _ ==> (IS_SOME res ==> _) /\ _`
       (drule_at_then (Pat `FLOOKUP acts _ = _`) mp_tac) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then drule >> simp[]) >>
  `!i t. get_instruction bt t.vs_inst_idx = SOME i /\ t.vs_inst_idx < LENGTH ps ==>
      P ((a,e,i.inst_id),tf,i,t)` by
    (rpt strip_tac >> qpat_assum `!a sf tf inc entry order res nrest e bb bt ps xs ys sched hin h0 b c f cl br i t.
       _ ==> P _` irule >> rpt (first_assum (irule_at Any))) >>
  `!be hbe i t k. beopt = SOME (be,hbe) /\
      MEM ((a,e,i.inst_id),tf,i,t) (trace_block a e (N-e) C8 tf bt be) /\
      t.vs_inst_idx = LENGTH ps + k /\ k <= nseen /\
      lookup_block t.vs_current_bb tf.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i ==> P ((a,e,i.inst_id),tf,i,t)` by
    (rpt strip_tac >> qpat_x_assum `beopt = SOME _` SUBST_ALL_TAC >>
     qpat_assum `!a sf tf inc entry order res nrest e bb bt ps xs ys sched hin h0 b h c f cl br i t k.
       _ ==> P _` irule >> rpt (first_assum (irule_at Any))) >>
  `!sp B. eval_phis hin bt.bb_instructions = OK sp /\ B <= LENGTH ps ==>
      EVERY P (trace_block a e (N-e) C8 tf
        (bt with bb_instructions := TAKE B bt.bb_instructions)
        (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions))` by
    (rpt strip_tac >> irule focus_packet_pseudo_fragment_every >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  `!be hbe m. beopt = SOME (be,hbe) /\ m <= nseen ==>
      EVERY P (trace_block a e (N-e) C8 tf
        (bt with bb_instructions := TAKE (LENGTH ps + m) bt.bb_instructions) be)` by
    (rpt strip_tac >> qpat_x_assum `beopt = SOME _` SUBST_ALL_TAC >>
     irule focus_packet_body_fragment_every >>
     rpt (first_assum (irule_at Any)) >> rpt strip_tac
     >- (qpat_assum `!be hbe i t k. _ ==> P _` irule >>
         rpt (first_assum (irule_at Any)) >> simp[]) >>
     qpat_assum `!cid csf ctf ce co cr cns. _ ==> _` (drule_then (mp_tac o CONJUNCT1)) >> simp[]) >>
  Cases_on `closed`
  >- (`e = EL r order` by simp[Abbr `e`,IgnAsm `e = inc + SUC r`] >>
      `!sp be hbe. eval_phis hin bt.bb_instructions = OK sp /\ beopt = SOME (be,hbe) ==>
        EVERY P (trace_block a e (N-e) C8 tf
          (bt with bb_instructions := TAKE (LENGTH ps) bt.bb_instructions)
          (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions)) /\
        EVERY P (trace_block a e (N-e) C8 tf
          (bt with bb_instructions := TAKE (LENGTH ps + nseen) bt.bb_instructions) be)` by
        (rpt strip_tac >> first_assum irule >> simp[] >> goal_assum (drule_at Any)) >>
      drule_all_then strip_assume_tac focus_packet_completed_row_segment >>
      Cases_on `SUC r < LENGTH order`
      >- (qpat_x_assum `SUC r < LENGTH order ==> _` (drule_then strip_assume_tac) >>
          qpat_assum `!a sf tf inc ent order res rest r hin bb bt ps xs ys sched h0 b c f cl br.
            _ ==> (IS_SOME res ==> _) /\ _`
            (fn ih => qpat_assum `FLOOKUP blocks (a,EL (SUC r) order) = SOME _`
              (mp_then (Pat `FLOOKUP blocks _ = _`) mp_tac ih)) >>
          disch_then (drule_at (Pat `FLOOKUP acts _ = _`)) >>
          (impl_tac >- (conj_tac >- decide_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
          map_every (fn pat => qpat_assum pat mp_tac)
            [`trace_blocks a (inc+r) (N-(inc+r)) C8 tf hin = _`,
             `front = OK post`, `~post.vs_halted`, `n = N-(inc+r)`, `e = inc + SUC r`,
             `EVERY P seg`, `IS_SOME res ==> _`, `res = NONE ==> _`] >>
          POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
          conj_tac >- gvs[EVERY_APPEND] >> disch_tac >>
          qpat_x_assum `res = NONE ==> _` (drule_then strip_assume_tac) >>
          qexistsl [`seg ++ l`,`u`] >> gvs[APPEND_ASSOC,EVERY_APPEND]) >>
      `SUC r = LENGTH order` by decide_tac >>
      qpat_x_assum `SUC r = LENGTH order ==> _` (drule_then strip_assume_tac) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`trace_blocks a (inc+r) (N-(inc+r)) C8 tf hin = _`,
         `front = IntRet _ _`, `res = SOME front`, `n = N-(inc+r)`, `EVERY P seg`] >>
      POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `e = LAST order /\ ~IS_SOME brest` by
    (qpat_assum `e <> LAST order ==> _` mp_tac >>
     qpat_assum `F <=> IS_SOME brest` mp_tac >> simp[NoAsms]) >>
  `res = NONE /\ nrest = NONE /\ brest = NONE` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`e = LAST order ==> _`,`e = LAST order`,`~IS_SOME brest`] >>
     simp[NoAsms,optionTheory.NOT_IS_SOME_EQ_NONE]) >>
  `0 < e /\ e-1 = inc+r` by decide_tac >>
  qpat_x_assum `res = NONE` SUBST_ALL_TAC >>
  qpat_x_assum `nrest = NONE` SUBST_ALL_TAC >>
  qpat_x_assum `brest = NONE` SUBST_ALL_TAC >>
  simp[NoAsms] >>
  qpat_x_assum `n = N-(inc+r)` SUBST_ALL_TAC >>
  qpat_assum `e-1 = inc+r` (fn th => once_rewrite_tac[GSYM th]) >>
  irule focus_packet_live_row_split >>
  rpt (first_assum (irule_at Any)) >> rpt strip_tac
  >- (qpat_assum `!be hbe m. _ ==> EVERY P _` irule >>
      rpt (first_assum (irule_at Any)) >> simp[])
  >- (qpat_assum `!be hbe i t k. _ ==> P _` irule >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  simp[]
QED

Theorem focus_packet_native_prefix_every[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst st oms om hs hist) raw_slots sites unused /\
  (!a sf tf inc entry order res nrest e bb bt ps xs ys sched hin h0 beopt nseen front closed brest i t.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,beopt,nseen,front,closed,brest) /\
    get_instruction bt t.vs_inst_idx = SOME i /\ t.vs_inst_idx < LENGTH ps ==>
    P ((a,e,i.inst_id),tf,i,t)) /\
  (!a sf tf inc entry order res nrest e bb bt ps xs ys sched hin h0 be hbe nseen front closed brest i t k.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),nseen,front,closed,brest) /\
    MEM ((a,e,i.inst_id),tf,i,t) (trace_block a e (N-e) C8 tf bt be) /\
    t.vs_inst_idx = LENGTH ps + k /\ k <= nseen /\
    lookup_block t.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt t.vs_inst_idx = SOME i ==> P ((a,e,i.inst_id),tf,i,t)) ==>
  EVERY P (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry))
Proof
  strip_tac >> drule_then assume_tac focus_packet_native_keys_distinct >>
  qabbrev_tac `R = trace_blocks [] 0 N C8 root_tf root_entry` >>
  `j < LENGTH R /\ EL j R = ((p,d,inst.inst_id),fn,inst,st) /\
   ?order. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_assum `FLOOKUP acts [] = _` (fn th => irule_at Any th) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (R = _)`, `(j,obs) = _`, `JointConfig stk PG G tn fn inst st oms om hs hist = _`,
        `_ < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)`,
        `EL _ (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,_),_,_,_)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def] >> metis_tac[]) >>
  drule_all_then strip_assume_tac focus_packet_first_row >>
  `?l u. R = l ++ [((p,d,inst.inst_id),fn,inst,st)] ++ u /\ EVERY P l` by
    (qhdtm_assum `dft_focus_packet_rel`
       (mp_then Any mp_tac focus_packet_suffix_every) >>
     disch_then (qspecl_then [`P`,`N`] (drule_at (Pat `FLOOKUP acts _ = _`))) >>
     disch_then (qspecl_then [`P`,`0`] (drule_at (Pat `FLOOKUP blocks _ = _`))) >>
     disch_then (qspec_then `P` mp_tac) >>
     gvs[Abbr `R`] >> disch_then match_mp_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH l < LENGTH R /\ EL (LENGTH l) R = EL j R` by
    simp[EL_APPEND_EQN] >>
  `LENGTH l = j` by
    (qpat_assum `ALL_DISTINCT (MAP FST _)`
       (mp_then Any (qspecl_then [`LENGTH l`,`j`] mp_tac) ALL_DISTINCT_EL_IMP) >>
     simp[EL_MAP] >> fs[]) >>
  qpat_x_assum `LENGTH l = j` (SUBST1_TAC o SYM) >>
  `LENGTH l - (LENGTH l + 1) = 0` by decide_tac >>
  simp[TAKE_APPEND]
QED

Theorem focus_packet_visit_row:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst st oms om hs hist) raw_slots sites unused /\
  R = trace_blocks [] 0 N C8 root_tf root_entry /\
  h < j /\ EL h R = ((a,e,i.inst_id),tf,i,t) ==>
  ?sf inc entry order res nrest bb bt ps xs ys sched hin h0 beopt nseen front closed brest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,beopt,nseen,front,closed,brest) /\
    get_instruction bt t.vs_inst_idx = SOME i /\
    ((inv_memory_observation i.inst_opcode \/ is_fallible i \/ i.inst_opcode = INVOKE) ==>
     ?be hbe k q.
       beopt = SOME (be,hbe) /\ hbe <= h /\
       lookup_block t.vs_current_bb tf.fn_blocks = SOME bt /\
       LENGTH ps <= t.vs_inst_idx /\ k = t.vs_inst_idx - LENGTH ps /\
       k < LENGTH ys /\ k <= nseen /\ EL k ys = i /\
       EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k ys) /\
       FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE k ys) be = OK t /\
       k < LENGTH sched /\ q = EL k sched /\ q < LENGTH xs /\ EL q xs = i /\
       EVERY (\x. ~is_terminator x.inst_opcode) (TAKE q xs) /\
       (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE nseen sched)))
Proof
  strip_tac >> qmatch_abbrev_tac `wanted` >>
  `j < LENGTH R` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`R = trace_blocks [] 0 N C8 root_tf root_entry`, `(j,obs) = _`,
        `_ < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `MEM ((a,e,i.inst_id),tf,i,t) (TAKE j R)` by
    (simp[MEM_EL] >> qexists `h` >> gvs[LENGTH_TAKE_EQ,EL_TAKE]) >>
  `EVERY (\v. v = ((a,e,i.inst_id),tf,i,t) ==> wanted) (TAKE j R)` by
    (qhdtm_assum `dft_focus_packet_rel`
       (mp_then Any mp_tac focus_packet_native_prefix_every) >>
     disch_then (qspec_then `\v. v = ((a,e,i.inst_id),tf,i,t) ==> wanted` mp_tac) >>
     impl_tac
     >- (BETA_TAC >> conj_tac >> rpt gen_tac >> strip_tac >>
         simp[] >> strip_tac >> gvs[] >> unabbrev_all_tac >>
         rpt (first_assum (irule_at Any))
         >- (drule_all focus_packet_direct_row_data >> strip_tac >>
             `is_pseudo i.inst_opcode` by gvs[get_instruction_def,EL_APPEND_EQN,EVERY_EL] >>
             qpat_assum `is_pseudo i.inst_opcode` mp_tac >>
             POP_ASSUM_LIST (K all_tac) >> metis_tac[focus_guard_not_pseudo]) >>
         disch_tac >>
         qhdtm_assum `dft_focus_packet_rel`
           (mp_then Any mp_tac focus_packet_direct_visit_row) >>
         disch_then (drule_at (Pat `EL _ _ = _`)) >>
         disch_then (drule_at (Pat `FLOOKUP acts _ = _`)) >>
         disch_then (drule_at (Pat `FLOOKUP blocks _ = _`)) >> simp[]) >>
     simp[]) >>
  fs[EVERY_MEM]
QED

Theorem focus_historical_cut_source_safety[local]:
  C7.ctx_entry = SOME nm /\ lookup_function nm C7.ctx_functions = SOME root /\
  fn_entry_label root = SOME lbl /\ root_entry.vs_prev_bb = NONE /\
  root_entry.vs_current_bb = lbl /\ root_entry.vs_inst_idx = 0 /\
  MEM (key,sf,inst,u) (trace_blocks [] 0 fuel C7 root
    (root_entry with vs_gas_readings := gs ++ tail)) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  LENGTH Mcut < n /\ u.vs_gas_readings = tail /\
  mem_inv (\C fn i s. gas_cut n (root_entry with vs_gas_readings := gs ++ tail) s ==>
    static_mem_ok cpl.cp_max_static_eom C fn i s)
    C7 (root_entry with vs_gas_readings := gs ++ tail) /\
  o1_ctx_shape C7 /\ MEM sf C7.ctx_functions /\ dft_fn_rel sf tf /\ tf = dftDefs$dft_fn sf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  MEM inst bb.bb_instructions /\ visit.vs_current_bb = bb.bb_label /\
  lookup_block visit.vs_current_bb tf.fn_blocks = SOME bt /\
  get_instruction bt visit.vs_inst_idx = SOME inst /\ ~in_revert_forward tf visit ==>
  static_mem_ok cpl.cp_max_static_eom C7 sf inst u /\ ~in_revert_forward sf u
Proof
  strip_tac >>
  `raw_reachable (root_entry with vs_gas_readings := gs ++ tail) C7 sf inst u` by
    (match_mp_tac (Q.SPECL [`C7`, `nm`, `root`, `lbl`,
       `root_entry with vs_gas_readings := gs ++ tail`, `key`, `sf`, `inst`, `u`, `fuel`]
       dftFinitePacketReachabilityTheory.dft_packet_trace_raw_reachable) >> simp[]) >>
  conj_tac
  >- (`LENGTH gs = LENGTH Mcut` by metis_tac[LIST_REL_LENGTH] >>
      `gas_cut n (root_entry with vs_gas_readings := gs ++ tail) u` by
        simp[gas_cut_def] >>
      qpat_x_assum `mem_inv _ _ _` (strip_assume_tac o REWRITE_RULE [mem_inv_raw_reachable]) >>
      qpat_x_assum `!fn i s. raw_reachable _ _ _ _ _ ==> _` drule >> simp[]) >>
  `active_inst sf inst u` by
    (drule stepWriteFootprintBaseTheory.raw_reachable_active >> simp[]) >>
  `wf_function sf` by fs[dftRunRelTheory.dft_fn_rel_def] >>
  drule_all_then assume_tac dft_packet_active_block >>
  `active_inst tf inst visit` by
    (simp[active_inst_def] >> qexists_tac `bt` >>
     drule_then strip_assume_tac venomExecProofsTheory.lookup_block_label >>
     fs[get_instruction_def] >> metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
  metis_tac[dftGasInvForwardActiveTheory.inv_forward_active]
QED

Theorem focus_packet_visit_cut[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn endpoint_inst st oms om hs hist) raw_slots sites unused /\
  R = trace_blocks [] 0 N C8 root_tf root_entry /\
  hbe <= h /\ h < j /\ EL h R = ((a,e,inst.inst_id),tf,inst,visit) /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),nseen,front,closed,brest) /\
  get_instruction bt visit.vs_inst_idx = SOME inst /\
  lookup_block visit.vs_current_bb tf.fn_blocks = SOME bt /\
  LENGTH ps <= visit.vs_inst_idx /\ k = visit.vs_inst_idx - LENGTH ps /\
  k < LENGTH ys /\ EL k ys = inst /\ k < LENGTH sched /\ q = EL k sched /\
  q < LENGTH xs /\ EL q xs = inst /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k ys) /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE k ys) be = OK visit /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE nseen sched)) ==>
  ((inv_memory_observation inst.inst_opcode \/ is_fallible inst \/ inst.inst_opcode = INVOKE) /\
   ~in_revert_forward tf visit) ==>
  ?q' z src_inst cuts levels Mcut Ecut Kcut mr er kr.
    src_inst = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    ((IS_SOME (SOME (be,hbe)) /\ LENGTH ps <= visit.vs_inst_idx /\
      visit.vs_inst_idx - LENGTH ps < LENGTH sched /\
      q' = EL (visit.vs_inst_idx - LENGTH ps) sched /\ q' < LENGTH xs /\
      (a <> p \/ e <> d \/ visit <> st \/
        (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q' xs) /\
         (!r. r < q' /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE nseen sched)))) /\
      (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
         inst.inst_opcode = INVOKE ==> EL q' xs = inst) /\
      z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q' xs) \/
     (a = p /\ e = d /\ visit = st /\ SOME (be,hbe) = NONE /\
      visit.vs_inst_idx < LENGTH ps /\ q' = 0 /\
      z = DROP (phi_prefix_length bb.bb_instructions) (TAKE visit.vs_inst_idx ps))) /\
    MAP (\(ai,ds,ei,qi,zi). ai) cuts =
      REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
    LENGTH cuts = LENGTH levels /\
    (!i ai ds ei qi zi.
      i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
        ini hi bei counti fronti closedi resti later.
        FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
        FLOOKUP blocks (ai,ei) =
          SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
        orderi = ds ++ ei::later /\
        (if SUC i = LENGTH cuts then
          ai = a /\ ei = e /\ qi = q' /\ zi = z
        else
          ?cid h b0 done_at_call child_entry ret.
            EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
            FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
            qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
            zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
            EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
            (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
        EL i levels =
          (sfi,
           MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
             DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
               (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
           [(bbi,ei,zi)],
           if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
    Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
    Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
    Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
    raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) = Kcut ++ kr /\
    LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
    (!F gs tail.
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
      (?extra. Ecut = FST (rooted_eval F C7 levels
        (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
      (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
        OK u =>
          FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
          u.vs_gas_readings = tail /\
          (?before after.
            trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
              before ++ [((a,e,src_inst.inst_id),sf,src_inst,u)] ++ after /\
            trace_gas before = ZIP (Kcut,gs)) /\
          (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
            (Ecut,OK (u with vs_gas_readings := tail'))) /\
          (SOME (be,hbe) = NONE ==> u with vs_gas_readings := visit.vs_gas_readings = visit) /\
          (a = p /\ e = d /\ IS_SOME (SOME (be,hbe)) /\
           inv_memory_observation inst.inst_opcode /\ EL q' xs = inst ==>
            (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op visit) /\
            u.vs_initial_fmp = visit.vs_initial_fmp)
      | stopped =>
          run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
          gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)))) /\
    (!F gs tail n u.
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
      LENGTH Mcut < n /\
      mem_inv (\ctx src_fn src_i src_state.
        gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
        static_mem_ok cpl.cp_max_static_eom ctx src_fn src_i src_state)
        C7 (root_entry with vs_gas_readings := gs ++ tail) /\
      rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail) = (Ecut,OK u) ==>
      static_mem_ok cpl.cp_max_static_eom C7 sf src_inst u /\
      ~in_revert_forward sf u /\
      (inv_memory_observation src_inst.inst_opcode ==>
        (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op visit) /\
        u.vs_initial_fmp = visit.vs_initial_fmp))
Proof
  strip_tac >> disch_then (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) >>
  qabbrev_tac `z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs` >>
  `o1_ctx_shape C7 /\ MEM sf C7.ctx_functions /\ dft_fn_rel sf tf /\ tf = dftDefs$dft_fn sf /\
   lookup_block bb.bb_label sf.fn_blocks = SOME bb /\ bt.bb_label = bb.bb_label /\
   bb.bb_instructions = ps ++ xs /\ EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
   (?nm lbl. C7.ctx_entry = SOME nm /\ lookup_function nm C7.ctx_functions = SOME root_sf /\
     fn_entry_label root_sf = SOME lbl /\ root_entry.vs_prev_bb = NONE /\
     root_entry.vs_current_bb = lbl /\ root_entry.vs_inst_idx = 0)` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (fn inv => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
         (mp_then Any mp_tac inv)) >>
     qpat_assum `!a e bb bt ps xs ys rho hin h0 body count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> ?sf. _`
       (fn inv => qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,_,nseen,front,closed,brest)`
         (mp_then Any mp_tac inv)) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`, `o1_ctx_shape C7`,
        `C7.ctx_entry = SOME _`, `lookup_function _ C7.ctx_functions = SOME root_sf`,
        `fn_entry_label root_sf = SOME _`, `root_entry.vs_prev_bb = NONE`,
        `root_entry.vs_current_bb = _`, `root_entry.vs_inst_idx = 0`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >> gvs[] >> metis_tac[]) >>
  `inst = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
    (`EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = EL q xs` by
       (irule dft_packet_cut_instruction >> simp[Abbr `z`]) >> metis_tac[]) >>
  (* Select this visit's inventory before choosing replay fuel or readings. *)
  ASSUM_LIST (fn before_cut =>
    qhdtm_assum `dft_focus_packet_rel`
      (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
    qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho hin h0
        body count front closed brest q z. _ ==> ?cuts levels Mcut Ecut Kcut mr er kr. _`
      mp_tac >>
    disch_then (fn inv => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
      (mp_then (Pat `FLOOKUP acts _ = _`) mp_tac inv)) >>
    disch_then (fn inv => qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),nseen,front,closed,brest)`
      (mp_then (Pat `FLOOKUP blocks _ = _`) mp_tac inv)) >>
    disch_then (qspecl_then [`q`,`z`] mp_tac) >>
    (impl_tac >- simp[Abbr `z`]) >>
    map_every (fn pat => qpat_assum pat mp_tac)
      [`raw_slots = AM []`, `sites = AE []`, `AM = _`, `AE = _`, `AK = _`] >>
    POP_ASSUM_LIST (K (map_every assume_tac (rev before_cut))) >>
    ntac 5 (disch_then assume_tac)) >>
  disch_then strip_assume_tac >>
  qpat_x_assum `!i ai ds ei qi zi. _ ==> ?sfi. _`
    (assume_tac o BETA_RULE o PURE_REWRITE_RULE [pairTheory.pair_CASE_def]) >>
  qpat_x_assum `AK = _` (fn def =>
    qpat_x_assum `AK [] = _` (assume_tac o BETA_RULE o REWRITE_RULE [def])) >>
  qpat_assum `inst = EL _ _` (fn src_eq =>
    qpat_x_assum `!F gs tail. _ ==> levels_ok _ _ _ _ _ _ _ _ _ /\ _`
      (mk_asm "replay" o REWRITE_RULE [GSYM src_eq])) >>
  `z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs` by simp[Abbr `z`] >>
  qexistsl [`q`, `z`, `inst`, `cuts`, `levels`, `Mcut`, `Ecut`, `Kcut`, `mr`, `er`, `kr`] >>
  rpt (conj_tac >- FIRST_PROVE [first_assum ACCEPT_TAC, simp[Abbr `z`]]) >>
  conj_tac
  >- (map_every qx_gen_tac [`fuel`, `gs`, `tail`] >> strip_tac >>
      asm "replay" (qspecl_then [`fuel`, `gs`, `tail`] mp_tac) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (CONJUNCTS_THEN2 (K all_tac)
        (CONJUNCTS_THEN2 assume_tac (mk_asm "case_replay"))) >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      Cases_on `rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail)` >>
      rename1 `rooted_eval fuel C7 levels _ = (events,result)` >>
      asm_x "case_replay" mp_tac >>
      Cases_on `result` >>
      rewrite_tac[pairTheory.FST,pairTheory.SND,venomExecSemanticsTheory.exec_result_case_def,
                  optionTheory.option_CLAUSES,optionTheory.NOT_SOME_NONE] >>
      BETA_TAC >>
      TRY (disch_tac >> first_assum ACCEPT_TAC) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      strip_tac >> match_mp_tac (GEN_ALL focus_packet_rooted_body_observation) >>
      qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
      qpat_assum `FLOOKUP blocks (a,e) = _` (irule_at (Pat `FLOOKUP blocks _ = _`)) >>
      qpat_assum `FLOOKUP acts a = _` (irule_at (Pat `FLOOKUP acts _ = _`)) >>
      qpat_assum `rooted_eval fuel C7 levels _ = _` (irule_at (Pat `rooted_eval _ _ _ _ = _`)) >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  map_every qx_gen_tac [`fuel`, `gs`, `tail`, `n`, `u`] >> strip_tac >>
  asm_x "replay" (qspecl_then [`fuel`, `gs`, `tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `rooted_eval fuel C7 levels _ = (Ecut,OK u)` (fn eval_eq =>
    disch_then (fn th => CONJUNCT2 (CONJUNCT2 th) |> mp_tac) >>
    rewrite_tac[eval_eq,pairTheory.FST,pairTheory.SND,venomExecSemanticsTheory.exec_result_case_def]) >>
  BETA_TAC >> strip_tac >>
  `MEM (inst:instruction) bb.bb_instructions` by
    (qpat_assum `bb.bb_instructions = _` SUBST1_TAC >> rewrite_tac[MEM_APPEND] >>
     disj2_tac >> rewrite_tac[MEM_EL] >> qexists `q` >>
     conj_tac >- first_assum ACCEPT_TAC >> sym_tac >> first_assum ACCEPT_TAC) >>
  `visit.vs_current_bb = bb.bb_label` by
    (qpat_assum `lookup_block visit.vs_current_bb tf.fn_blocks = _`
      (mp_then Any mp_tac venomExecProofsTheory.lookup_block_label) >>
     qpat_assum `bt.bb_label = bb.bb_label` (fn th => rewrite_tac[th]) >>
     disch_then (ACCEPT_TAC o SYM)) >>
  `MEM ((a,e,inst.inst_id),sf,inst,u)
    (trace_blocks [] 0 fuel C7 root_sf (root_entry with vs_gas_readings := gs ++ tail))` by
    (qpat_assum `trace_blocks [] 0 fuel C7 root_sf _ = _` SUBST1_TAC >>
     rewrite_tac[MEM_APPEND,MEM]) >>
  `static_mem_ok cpl.cp_max_static_eom C7 sf inst u /\ ~in_revert_forward sf u` by
    (match_mp_tac (GEN_ALL focus_historical_cut_source_safety) >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> match_mp_tac (GEN_ALL focus_packet_rooted_body_observation) >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (a,e) = _` (irule_at (Pat `FLOOKUP blocks _ = _`)) >>
  qpat_assum `FLOOKUP acts a = _` (irule_at (Pat `FLOOKUP acts _ = _`)) >>
  qpat_assum `rooted_eval fuel C7 levels _ = _` (irule_at (Pat `rooted_eval _ _ _ _ = _`)) >>
  rpt (first_assum (irule_at Any)) >> simp[]
QED

Theorem focus_finalizers_distinct[local]:
  asm_opt_finalizer <> K SOME
Proof
  disch_then (mp_tac o C AP_THM
    ``rpolicy with rpol_final_assembly := FAP_Optimize``) >>
  disch_then (mp_tac o C AP_THM ``[AsmOp "STOP"; AsmOp "POP"]``) >>
  simp[asm_opt_finalizer_def, combinTheory.K_THM] >>
  EVAL_TAC
QED

Theorem focus_selected_frame_edge[local]:
  fin IN accepted_finalizers /\
  joint_config_reachable vs0 u.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  joint_transition u.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) ev
    (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') /\
  ~in_revert_forward fn s /\
  (inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode ==>
    source_memory_reads_disjoint cpl inst s /\
    context_source_memory_writes_disjoint cpl inst s) /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog k (entry_asm_state vs0 es0) = AsmOK ast /\
  (fin = K SOME ==>
    normal_frame_plan rpolicy u cpl prog
      (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                  vs_return_pc_token := 0w; vs_inst_idx := 0|>) es0
      (JointConfig stk PG G tn fn inst s oms om hs h) ast) /\
  (fin = asm_opt_finalizer ==>
    focus_s7_symbolic_context u prog /\ focus_s7_symbolic_guard prog cpl fn inst s /\
    sym_steps prog (asm_data_env prog vs0.vs_code) k
      (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy u cpl prog vs0 es0
      (JointConfig stk PG G tn fn inst s oms om hs h) ast ss) ==>
  ?n ast' ss'.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast' /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog (k + n) (entry_asm_state vs0 es0) = AsmOK ast' /\
    (fin = K SOME ==>
      normal_frame_plan rpolicy u cpl prog
        (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                    vs_return_pc_token := 0w; vs_inst_idx := 0|>) es0
        (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ast') /\
    (fin = asm_opt_finalizer ==>
      sym_steps prog (asm_data_env prog vs0.vs_code) n ss = SymOK ss' /\
      sym_steps prog (asm_data_env prog vs0.vs_code) (k + n)
        (sym_init (entry_asm_state vs0 es0)) = SymOK ss' /\
      normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy u cpl prog vs0 es0
        (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ast' ss') /\
    (0 < n \/
     (n = 0 /\ inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
      stk' = stk /\ fn' = fn /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = SUC s.vs_inst_idx /\
      ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        LENGTH bb.bb_instructions - t.vs_inst_idx < LENGTH bb.bb_instructions - s.vs_inst_idx))
Proof
  strip_tac >>
  `fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  pop_assum strip_assume_tac >> gvs[focus_finalizers_distinct]
  >- (drule_all_then (qx_choosel_then [`n`, `ast'`]
         (map_every assume_tac o CONJUNCTS))
         (SIMP_RULE (srw_ss()) [] focus_plain_frame_progress) >>
      qexistsl [`n`, `ast'`] >> asm_rewrite_tac[] >>
      irule asm_steps_compose_ok >> qexists_tac `ast` >> asm_rewrite_tac[]) >>
  drule_all_then (qx_choosel_then [`n`, `ast'`, `ss'`]
    (map_every assume_tac o CONJUNCTS))
    (SIMP_RULE (srw_ss()) []
      (Q.INST [`env` |-> `asm_data_env prog vs0.vs_code`]
        normal_frame_symbolic_joint_progress)) >>
  qexistsl [`n`, `ast'`, `ss'`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (irule asm_steps_compose_ok >> qexists_tac `ast` >> asm_rewrite_tac[]) >>
  irule sym_steps_compose >> qexists_tac `ss` >> asm_rewrite_tac[]
QED

Theorem focus_cfg_gas_cursor[local]:
  !C rounds cells. cfg_norm_cursors C rounds cells /\
    (FST (FST (HD cells))).inst_opcode = GAS ==>
    (FST (FST (LAST cells))).inst_opcode = GAS /\
    (SND (FST (LAST cells))).vs_gas_readings =
      (SND (FST (HD cells))).vs_gas_readings
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac cfg_norm_cursors_ind >>
  simp_tac bool_ss [HD,LAST_CONS,pairTheory.FST,pairTheory.SND,NOT_CONS_NIL] >>
  conj_tac >> rpt gen_tac >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >> disch_tac
  >- (`(EL v.vs_inst_idx
        (supply_block_image pred target split repls bb).bb_instructions).inst_opcode = GAS`
      by metis_tac[supply_block_image_index] >>
      `v.vs_gas_readings = a.vs_gas_readings` by
        (qpat_assum `supply_state_agree fn a v`
           (mp_tac o cj 1 o REWRITE_RULE [supply_state_agree_def]) >>
         disch_then (mp_tac o AP_TERM ``\s:venom_state. s.vs_gas_readings``) >>
         simp[execution_frame_def]) >>
      first_x_assum (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  gvs[is_terminator_def]
QED

Theorem focus_joint_gas_cursor[local]:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  inst8.inst_opcode = GAS ==>
  inst9.inst_opcode = GAS /\ s8.vs_gas_readings = s9.vs_gas_readings
Proof
  PairCases_on `current` >>
  simp[cfg_norm_joint_cursors_def] >> strip_tac >>
  drule focus_cfg_gas_cursor >> gvs[]
QED

Theorem focus_selected_gas_ready[local]:
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  generate_context_plan u.cu_context = SOME cpl /\
  codegen_assembly rpolicy u = SOME prog /\ unit_shape_ok u /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
  run_call es0 = SOME (result,final) /\ ~frame_resource_starved es0 result final /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es0) = AsmOK ast /\
  (fin = K SOME ==>
    normal_frame_plan rpolicy u cpl prog
      (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                  vs_return_pc_token := 0w; vs_inst_idx := 0|>) es0
      (JointConfig stk PG G tn fn inst s oms om hs h) ast) /\
  (fin = asm_opt_finalizer ==>
    codegen_ready u.cu_context /\ focus_s7_symbolic_context u prog /\
    sym_steps prog (asm_data_env prog vs0.vs_code) n
      (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy u cpl prog vs0 es0
      (JointConfig stk PG G tn fn inst s oms om hs h) ast ss) /\
  active_inst fn inst s /\ inst.inst_opcode = GAS ==>
  s.vs_gas_readings <> [] /\
  ?k ready.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog k ast = AsmOK ready /\
    ready.as_pc < LENGTH prog /\ EL ready.as_pc prog = AsmOp "GAS" /\
    ready.as_gas_readings = s.vs_gas_readings /\
    (fin = asm_opt_finalizer ==> ?sr.
      sym_steps prog (asm_data_env prog vs0.vs_code) k ss = SymOK sr)
Proof
  strip_tac >>
  `fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  pop_assum strip_assume_tac >> gvs[focus_finalizers_distinct, combinTheory.K_THM]
  >- (`(entry_asm_state vs0 es0 with as_code := assemble prog ++ vs0.vs_data_section) =
        entry_asm_state vs0 es0` by simp[entry_asm_state_def] >>
      `asm_frame_prog_ok prog` by metis_tac[codegen_assembly_frame_prog_ok] >>
      gvs[] >>
      drule_all_then ACCEPT_TAC
        (SIMP_RULE (srw_ss()) [] focus_plain_frame_gas_available)) >>
  drule_all_then strip_assume_tac focus_normal_frame_gas_available >>
  qpat_assum `vs0.vs_code = _` (fn code_eq =>
    qpat_assum `!n ast ss stk PG G tn fn inst s oms om hs h. _`
      (drule_all_then strip_assume_tac o REWRITE_RULE [code_eq])) >>
  asm_rewrite_tac[] >> qexistsl [`k`, `ast1`] >> asm_rewrite_tac[] >>
  qexists_tac `ss1` >> asm_rewrite_tac[]
QED

Theorem focus_packet_native_index[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs hist) raw_slots sites unused ==>
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((p,d,inst.inst_id),fn,inst,s) /\
  obs = trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry)) /\
  LENGTH (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry)) = j
Proof
  disch_then (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`(j,obs) = _`, `JointConfig stk PG G tn fn inst s oms om hs hist = _`,
     `_ < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)`,
     `EL _ (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,_),_,_,_)`,
     `_ = trace_gas (TAKE _ (trace_blocks [] 0 N C8 root_tf root_entry))`] >>
  POP_ASSUM_LIST (K all_tac) >> simp[LENGTH_TAKE_EQ]
QED

Theorem focus_packet_motion[local]:
  0 < N /\
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs hist) raw_slots sites unused /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (callTrace$gas_readings es0) /\
  (inst.inst_opcode = GAS ==> s.vs_gas_readings <> []) /\
  joint_transition C8 (JointConfig stk PG G tn fn inst s oms om hs hist) ev
    (JointConfig stk' PG' G' tn' fn' inst' s' oms' om' hs' hist') ==>
  ?N' obs' acts' blocks' calls' ms_tab' es_tab' ks_tab' p' d' raw_slots' sites' unused'.
    0 < N' /\ N <= N' /\
    dft_focus_packet_rel N' C7 C8 root_sf root_tf root_entry (SUC j,obs')
      acts' blocks' calls' ms_tab' es_tab' ks_tab' rooted_eval p' d'
      (JointConfig stk' PG' G' tn' fn' inst' s' oms' om' hs' hist') raw_slots' sites' unused' /\
    SUC j < LENGTH (trace_blocks [] 0 N' C8 root_tf root_entry) /\
    EL (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) =
      ((p',d',inst'.inst_id),fn',inst',s') /\
    obs' = trace_gas (TAKE (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry)) /\
    LENGTH (TAKE (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry)) = SUC j /\
    LENGTH raw_slots' = LENGTH sites' /\
    PERM (MAP THE (FILTER IS_SOME raw_slots') ++ unused') (callTrace$gas_readings es0) /\
    (!a e cid ix h b0 done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (ix,h,b0,done_at_call,child_entry,ret) ==>
      ?ret'. FLOOKUP calls' (a,e,cid) = SOME (ix,h,b0,done_at_call,child_entry,ret') /\
             (IS_SOME ret ==> ret' = ret))
Proof
  strip_tac >>
  let
    val retained = dft_focus_packet_step_retained
    val v = List.find (fn tm => fst (dest_var tm) = "gas_readings")
      (free_vars (concl retained)) |> valOf
    val gas = ``callTrace$gas_readings``
    val ty = match_type (type_of v) (type_of gas)
    val step = INST [inst ty v |-> gas] (INST_TYPE ty retained)
  in
    drule_all_then strip_assume_tac (SIMP_RULE (srw_ss()) [] (cj 1 step))
  end >>
  fs[pairTheory.FST] >>
  qpat_assum `dft_focus_packet_rel N' _ _ _ _ _ (SUC j,obs') _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any strip_assume_tac focus_packet_native_index) >>
  `0 < N'` by decide_tac >>
  qexistsl [`N'`, `acts'`, `blocks'`, `calls'`, `ms_tab'`, `es_tab'`, `ks_tab'`,
            `p'`, `d'`, `raw_slots'`, `sites'`, `unused'`] >>
  gvs[]
QED

Theorem focus_joint_progress:
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
    code_layout_valid vs0 /\
    unit_shape_ok out.po_unit /\
    generate_context_plan out.po_unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==>
       label_flow_ok unit.cu_context /\
       (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                  ~MEM (Label "code_end") inst.inst_operands) /\
       EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                         ds.ds_items) unit.cu_data_segment /\
       ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                   MEM inst (fn_insts fn) /\
                   MEM (Label "runtime_begin") inst.inst_operands) ==>
        EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
       LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
    (vs0.vs_call_ctx.cc_static ==>
       !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                 ~MEM (Label "runtime_begin") inst.inst_operands) /\
    vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
    codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
    unit.cu_context.ctx_entry = SOME nm /\
    lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
    fn_entry_label entryfn = SOME lbl /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final /\
    run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
      (init_ir_supply unit) = SOME (pre,t) /\
    pre.cu_context.ctx_entry = SOME nm /\
    run_callee_first rpolicy o1_fn_passes
      (fcg_postorder (fcg_analyze pre.cu_context) nm)
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
      SOME (out.po_unit,t') /\
    stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
    stage 9 = out.po_unit.cu_context /\
    (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (stage k) (stage (SUC k))) /\
    (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
      EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  0 < N /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  (stage 7).ctx_entry = SOME nm /\ (stage 8).ctx_entry = SOME nm /\
  lookup_function nm (stage 7).ctx_functions = SOME root_sf /\
  lookup_function nm (stage 8).ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl7 /\ fn_entry_label root_tf = SOME lbl7 /\
  joint_initial vs0 (stage 8) q80 /\ joint_initial vs0 (stage 9) q90 /\
  joint_trace vs0 (stage 8) q80 evs8 qs8 (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) /\
  joint_trace vs0 (stage 9) q90 evs9 qs9 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  cfg_norm_joint_cursors (stage 8) (stage 9) (schedules,current,saved) (JointConfig stk8 PG8 G8 tn8 fn8
    inst8 s8 oms8 om8 hs8 hist8) (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog asm_fuel (entry_asm_state vs0 es0) = AsmOK ast /\
  (fin = K SOME ==> normal_frame_plan rpolicy out.po_unit cpl prog (vs0 with
    <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp; vs_return_pc_token := 0w;
    vs_inst_idx := 0|>) es0 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) asm_fuel (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss) /\
  dft_focus_packet_rel N (stage 7) (stage 8) root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8
      om8 hs8 hist8) raw_slots sites unused /\
  j = LENGTH evs8 /\ LENGTH evs8 <= LENGTH evs9 /\ LENGTH (TAKE j (dftGasFromListTraceDefs$trace_blocks []
    0 N (stage 8) root_tf root_entry)) = j /\
  j < LENGTH (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) /\ obs =
    dftGasFromListTraceDefs$trace_gas (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8)
    root_tf root_entry)) /\
  EL j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) =
    ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
  ~in_revert_forward fn9 s9 /\
  (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode ==>
    source_memory_reads_disjoint cpl inst9 s9 /\
    context_source_memory_writes_disjoint cpl inst9 s9) /\
  (fin = asm_opt_finalizer ==>
    !dst x sz src off.
      inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
      code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
      FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
      w2n (src - n2w off) < dimword (:256) DIV 2) /\
  active_inst fn9 inst9 s9 /\
  (inst9.inst_opcode = INVOKE ==>
    ?nm' ops callee args ent.
      decode_invoke inst9 = SOME (nm',ops) /\
      lookup_function nm' (stage 9).ctx_functions = SOME callee /\
      eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent) /\
  (inst9.inst_opcode <> INVOKE ==>
    (?u. step_inst 0 (stage 9) inst9 s9 = OK u /\ ~u.vs_halted) \/
    (stk9 <> [] /\ ?ir u. step_inst 0 (stage 9) inst9 s9 = IntRet ir u)) ==>
  ?ev9 q9' n ast' ss' N'
    raw_slots' sites' unused' evs8' qs8' evs9' qs9' current' saved'
    asm_fuel' j' obs' acts' blocks' calls' ms_tab' es_tab' ks_tab' p' d'
    stk8' PG8' G8' tn8' fn8' inst8' s8' oms8' om8' hs8' hist8'
    stk9' PG9' G9' tn9' fn9' inst9' s9' oms9' om9' hs9' hist9'.
  0 < N' /\ N <= N' /\
  q9' = (JointConfig stk9' PG9' G9' tn9' fn9' inst9' s9' oms9' om9' hs9' hist9') /\
    joint_transition (stage 9) (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ev9 q9' /\
  evs9' = evs9 ++ [ev9] /\ qs9' = qs9 ++ [q9'] /\
  asm_fuel' = asm_fuel + n /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n ast = AsmOK ast' /\
  (fin = asm_opt_finalizer ==> sym_steps prog (asm_data_env prog vs0.vs_code) n ss = SymOK ss') /\
  (0 < n \/
    (n = 0 /\ inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode /\
     stk9' = stk9 /\ fn9' = fn9 /\ s9'.vs_current_bb = s9.vs_current_bb /\
     s9'.vs_inst_idx = SUC s9.vs_inst_idx /\
     ?bb. lookup_block s9.vs_current_bb fn9.fn_blocks = SOME bb /\
       LENGTH bb.bb_instructions - s9'.vs_inst_idx < LENGTH bb.bb_instructions - s9.vs_inst_idx)) /\
  ((N' = N /\ (JointConfig stk8' PG8' G8' tn8' fn8' inst8' s8' oms8' om8' hs8' hist8') =
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) /\ MEM inst9.inst_opcode [ASSIGN; JMP;
    JNZ] /\
    inst_mem_ranges inst9 s9 = [] /\ j' = j /\
    evs8' = evs8 /\ qs8' = qs8 /\
    acts' = acts /\ blocks' = blocks /\ calls' = calls /\
    ms_tab' = ms_tab /\ es_tab' = es_tab /\ ks_tab' = ks_tab /\
    p' = p /\ d' = d /\ obs' = obs /\
    raw_slots' = raw_slots /\ sites' = sites /\ unused' = unused) \/
   (?ev8. joint_transition (stage 8) (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) ev8
     (JointConfig stk8' PG8' G8' tn8' fn8' inst8' s8' oms8' om8' hs8' hist8') /\
     j' = SUC j /\ evs8' = evs8 ++ [ev8] /\ qs8' = qs8 ++ [(JointConfig stk8' PG8' G8' tn8' fn8' inst8'
       s8' oms8' om8' hs8' hist8')] /\
     (inst8.inst_opcode = GAS ==>
       s8.vs_gas_readings <> [] /\
       ?k ready.
         asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
           prog k ast = AsmOK ready /\
         ready.as_pc < LENGTH prog /\ EL ready.as_pc prog = AsmOp "GAS" /\
         ready.as_gas_readings = s9.vs_gas_readings /\
         (fin = asm_opt_finalizer ==> ?sr. sym_steps prog (asm_data_env prog vs0.vs_code) k ss =
           SymOK sr)))) /\
  (!a e cid ix h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (ix,h,b0,done_at_call,child_entry,ret) ==>
    ?ret'. FLOOKUP calls' (a,e,cid) = SOME (ix,h,b0,done_at_call,child_entry,ret') /\
           (IS_SOME ret ==> ret' = ret)) /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  (stage 7).ctx_entry = SOME nm /\ (stage 8).ctx_entry = SOME nm /\
  lookup_function nm (stage 7).ctx_functions = SOME root_sf /\
  lookup_function nm (stage 8).ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl7 /\ fn_entry_label root_tf = SOME lbl7 /\
  joint_initial vs0 (stage 8) q80 /\ joint_initial vs0 (stage 9) q90 /\
  joint_trace vs0 (stage 8) q80 evs8' qs8' (JointConfig stk8' PG8' G8' tn8' fn8' inst8' s8' oms8' om8'
    hs8' hist8') /\
  joint_trace vs0 (stage 9) q90 evs9' qs9' (JointConfig stk9' PG9' G9' tn9' fn9' inst9' s9' oms9' om9'
    hs9' hist9') /\
  cfg_norm_joint_cursors (stage 8) (stage 9) (schedules,current',saved') (JointConfig stk8' PG8' G8' tn8'
    fn8' inst8' s8' oms8' om8' hs8' hist8') (JointConfig stk9' PG9' G9' tn9' fn9' inst9' s9' oms9' om9'
    hs9' hist9') /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog asm_fuel' (entry_asm_state vs0 es0) = AsmOK ast' /\
  (fin = K SOME ==> normal_frame_plan rpolicy out.po_unit cpl prog (vs0 with
    <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp; vs_return_pc_token := 0w;
    vs_inst_idx := 0|>) es0 (JointConfig stk9' PG9' G9' tn9' fn9' inst9' s9' oms9' om9' hs9' hist9') ast') /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) asm_fuel' (sym_init (entry_asm_state vs0 es0)) =
      SymOK ss' /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0
      (JointConfig stk9' PG9' G9' tn9' fn9' inst9' s9' oms9' om9' hs9' hist9') ast' ss') /\
  dft_focus_packet_rel N' (stage 7) (stage 8) root_sf root_tf root_entry (j',obs')
    acts' blocks' calls' ms_tab' es_tab' ks_tab' rooted_eval p' d' (JointConfig stk8' PG8' G8' tn8' fn8'
      inst8' s8' oms8' om8' hs8' hist8') raw_slots' sites' unused' /\
  j' = LENGTH evs8' /\ LENGTH evs8' <= LENGTH evs9' /\ LENGTH (TAKE j'
    (dftGasFromListTraceDefs$trace_blocks [] 0 N' (stage 8) root_tf root_entry)) = j' /\
  j' < LENGTH (dftGasFromListTraceDefs$trace_blocks [] 0 N' (stage 8) root_tf root_entry) /\ obs' =
    dftGasFromListTraceDefs$trace_gas (TAKE j' (dftGasFromListTraceDefs$trace_blocks [] 0 N' (stage 8)
    root_tf root_entry)) /\
  EL j' (dftGasFromListTraceDefs$trace_blocks [] 0 N' (stage 8) root_tf root_entry) =
    ((p',d',inst8'.inst_id),fn8',inst8',s8') /\
  LENGTH raw_slots' = LENGTH sites' /\
  PERM (MAP THE (FILTER IS_SOME raw_slots') ++ unused') (gas_readings es0) /\
  (!h. h < j' ==>
    ?a e tf inst visit_state stk PG G tn oms om hs hist.
      EL h (TAKE j' (dftGasFromListTraceDefs$trace_blocks [] 0 N' (stage 8) root_tf root_entry)) =
        ((a,e,inst.inst_id),tf,inst,visit_state) /\
      EL h (q80::qs8') = JointConfig stk PG G tn tf inst visit_state oms om hs hist /\
      ?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest.
        FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        FLOOKUP blocks' (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
        get_instruction bt visit_state.vs_inst_idx = SOME inst /\
        ((inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
          inst.inst_opcode = INVOKE) /\ ~in_revert_forward tf visit_state ==>
          ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
            src_inst = EL (LENGTH z)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
            ((IS_SOME body_entry /\ LENGTH ps <= visit_state.vs_inst_idx /\
              visit_state.vs_inst_idx - LENGTH ps < LENGTH rho /\
              q = EL (visit_state.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
              (a <> p' \/ e <> d' \/ visit_state <> s8' \/
                (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
                 (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
              (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
                 inst.inst_opcode = INVOKE ==> EL q xs = inst) /\
              z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
             (a = p' /\ e = d' /\ visit_state = s8' /\ body_entry = NONE /\
              visit_state.vs_inst_idx < LENGTH ps /\ q = 0 /\
              z = DROP (phi_prefix_length bb.bb_instructions) (TAKE visit_state.vs_inst_idx ps))) /\
            MAP (\(ai,ds,ei,qi,zi). ai) cuts =
              REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
            LENGTH cuts = LENGTH levels /\
            (!i ai ds ei qi zi.
              i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
              ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
                ini hi bei counti fronti closedi resti later.
                FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
                FLOOKUP blocks' (ai,ei) =
                  SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
                orderi = ds ++ ei::later /\
                (if SUC i = LENGTH cuts then
                  ai = a /\ ei = e /\ qi = q /\ zi = z
                else
                  ?cid h b0 done_at_call child_entry ret.
                    EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                    FLOOKUP calls' (ai,ei,cid) =
                      SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                    qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                    zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                    EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                    (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                      MEM r done_at_call)) /\
                EL i levels =
                  (sfi,
                   MAP (\f.
                     (FST (THE (FLOOKUP blocks' (ai,f))),f,
                      DROP (phi_prefix_length
                        (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)
                        (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)) ds ++
                     [(bbi,ei,zi)],
                   if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
            Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei))))) cuts) /\
            Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei))))) cuts) /\
            Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei))))) cuts) /\
            raw_slots' = Mcut ++ mr /\ sites' = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab'
              ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts' []))))))))) = Kcut ++ kr /\
            LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
            (!F gs tail.
              N' <= F /\
              LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
              (?extra. Ecut = FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
              (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
                OK u =>
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
                  u.vs_gas_readings = tail /\
                  (?before after.
                    dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                      (root_entry with vs_gas_readings := gs ++ tail) =
                      before ++ [((a,e,(EL (LENGTH z)
                        (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions)).inst_id),sf,
                        EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions),u)] ++ after /\
                    dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
                  (!tail'. rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail') =
                      (Ecut,OK (u with vs_gas_readings := tail'))) /\
                  (body_entry = NONE ==>
                    u with vs_gas_readings := visit_state.vs_gas_readings = visit_state) /\
                  (a = p' /\ e = d' /\ IS_SOME body_entry /\
                   inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
                    (!op. MEM op inst.inst_operands ==>
                      eval_operand op u = eval_operand op visit_state) /\
                    u.vs_initial_fmp = visit_state.vs_initial_fmp)
              | stopped =>
                  run_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
                  gas_events_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) =
                      FST (rooted_eval F (stage 7) levels
                        (root_entry with vs_gas_readings := gs ++ tail)))) /\
            (!F gs tail n u.
              N' <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
              LENGTH Mcut < n /\
              mem_inv (\ctx src_fn src_inst src_state.
                gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
                  static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
                (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
              rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
                (Ecut,OK u) ==>
              static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
              ~in_revert_forward sf u /\
              (inv_memory_observation src_inst.inst_opcode ==>
                (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op visit_state) /\
                u.vs_initial_fmp = visit_state.vs_initial_fmp))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY wf_function (stage 8).ctx_functions /\ EVERY wf_function (stage 9).ctx_functions` by
    (qpat_assum `!k. k <= 9 ==> _` (qspec_then `8` mp_tac) >>
     qpat_assum `!k. k <= 9 ==> _` (qspec_then `9` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  qpat_x_assum `stage 9 = out.po_unit.cu_context` SUBST_ALL_TAC >>
  drule_all_then (strip_assume_tac o REWRITE_RULE [codegen_context_obligations_def])
    focus_false_codegen_context >>
  every_drule_then assume_tac joint_trace_reachable >>
  drule_all_then (qx_choosel_then [`ev9`,`q9'`] assume_tac) focus_c9_continuing_exists >>
  Cases_on `q9'` >>
  rename1 `joint_transition _ _ ev9
    (JointConfig stk9' PG9' G9' tn9' fn9' inst9' s9' oms9' om9' hs9' hist9')` >>
  `fin = asm_opt_finalizer ==> focus_s7_symbolic_context out.po_unit prog` by
    (disch_tac >> qpat_assum `fin = asm_opt_finalizer ==> label_flow_ok _ /\ _`
       (fn th => drule_then (map_every assume_tac o CONJUNCTS) th) >>
     drule_all_then assume_tac focus_opt_label_flow >>
     drule_all_then strip_assume_tac focus_opt_static_assembly >>
     asm_rewrite_tac[focus_s7_symbolic_context_def]) >>
  `fin = asm_opt_finalizer ==> focus_s7_symbolic_guard prog cpl fn9 inst9 s9` by
    (simp[focus_s7_symbolic_guard_def]) >>
  `fin = asm_opt_finalizer ==>
       focus_s7_symbolic_context out.po_unit prog /\ focus_s7_symbolic_guard prog cpl fn9 inst9 s9 /\
       sym_steps prog (asm_data_env prog vs0.vs_code) asm_fuel
         (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
       normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0
         (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss` by simp[] >>
  drule_all_then (qx_choosel_then [`n`,`ast'`,`ss'`] (map_every assume_tac o CONJUNCTS))
    focus_selected_frame_edge >>
  `inst8.inst_opcode = GAS ==>
     s8.vs_gas_readings <> [] /\
     ?k ready. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog k ast = AsmOK ready /\
       ready.as_pc < LENGTH prog /\ EL ready.as_pc prog = AsmOp "GAS" /\
       ready.as_gas_readings = s9.vs_gas_readings /\
       (fin = asm_opt_finalizer ==> ?sr. sym_steps prog (asm_data_env prog vs0.vs_code) k ss = SymOK sr)` by
    (disch_tac >> drule_all_then strip_assume_tac focus_joint_gas_cursor >>
     `fin = asm_opt_finalizer ==> codegen_ready out.po_unit.cu_context /\
       focus_s7_symbolic_context out.po_unit prog /\
       sym_steps prog (asm_data_env prog vs0.vs_code) asm_fuel
         (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
       normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0
         (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss` by simp[] >>
     drule_all_then (CONJUNCTS_THEN2 assume_tac mp_tac) focus_selected_gas_ready >> simp[]) >>
  drule_all_then assume_tac joint_trace_snoc >>
  drule_all_then (strip_assume_tac o cj 4) cfg_norm_joint_cursors_step >>
  IF (qpat_assum `q8' = _` (K all_tac))
    (qpat_x_assum `q8' = _` SUBST_ALL_TAC >>
     qexistsl [`ev9`, `JointConfig stk9' PG9' G9' tn9' fn9' inst9' s9' oms9' om9' hs9' hist9'`,
       `n`, `ast'`, `ss'`, `N`, `raw_slots`, `sites`, `unused`, `evs8`, `qs8`,
       `evs9 ++ [ev9]`, `qs9 ++ [JointConfig stk9' PG9' G9' tn9' fn9' inst9' s9' oms9' om9' hs9' hist9']`,
       `current'`, `saved'`, `asm_fuel + n`, `j`, `obs`, `acts`, `blocks`, `calls`,
       `ms_tab`, `es_tab`, `ks_tab`, `p`, `d`,
       `stk8`,`PG8`,`G8`,`tn8`,`fn8`,`inst8`,`s8`,`oms8`,`om8`,`hs8`,`hist8`,
       `stk9'`,`PG9'`,`G9'`,`tn9'`,`fn9'`,`inst9'`,`s9'`,`oms9'`,`om9'`,`hs9'`,`hist9'`] >>
     rpt (conj_tac >- FIRST_PROVE [first_assum ACCEPT_TAC,
       simp[LENGTH_APPEND], decide_tac]))
    (Cases_on `q8'` >>
     rename1 `joint_transition (stage 8) _ ev8
       (JointConfig stk8' PG8' G8' tn8' fn8' inst8' s8' oms8' om8' hs8' hist8')` >>
     `inst8.inst_opcode = GAS ==> s8.vs_gas_readings <> []` by simp[] >>
     drule_all_then strip_assume_tac focus_packet_motion >>
     qpat_assum `joint_transition (stage 8) _ _ _`
       (mp_then Any (drule_then assume_tac) (REWRITE_RULE [GSYM AND_IMP_INTRO] joint_trace_snoc)) >>
     qexistsl [`ev9`, `JointConfig stk9' PG9' G9' tn9' fn9' inst9' s9' oms9' om9' hs9' hist9'`,
       `n`, `ast'`, `ss'`, `N'`, `raw_slots'`, `sites'`, `unused'`, `evs8 ++ [ev8]`,
       `qs8 ++ [JointConfig stk8' PG8' G8' tn8' fn8' inst8' s8' oms8' om8' hs8' hist8']`,
       `evs9 ++ [ev9]`, `qs9 ++ [JointConfig stk9' PG9' G9' tn9' fn9' inst9' s9' oms9' om9' hs9' hist9']`,
       `current'`, `saved'`, `asm_fuel + n`, `SUC j`, `obs'`, `acts'`, `blocks'`, `calls'`,
       `ms_tab'`, `es_tab'`, `ks_tab'`, `p'`, `d'`,
       `stk8'`,`PG8'`,`G8'`,`tn8'`,`fn8'`,`inst8'`,`s8'`,`oms8'`,`om8'`,`hs8'`,`hist8'`,
       `stk9'`,`PG9'`,`G9'`,`tn9'`,`fn9'`,`inst9'`,`s9'`,`oms9'`,`om9'`,`hs9'`,`hist9'`] >>
     rpt (conj_tac >- FIRST_PROVE [first_assum ACCEPT_TAC,
       simp[LENGTH_APPEND], decide_tac,
       disj2_tac >> qexists `ev8` >> simp[]]) >>
     `SUC j = LENGTH (evs8 ++ [ev8])` by simp[LENGTH_APPEND] >>
     qabbrev_tac `event_chain = evs8 ++ [ev8]` >>
     qabbrev_tac `packet_idx = SUC j`) >>
  (* Both branches use the native prefix of the selected final packet. *)
  qmatch_goalsub_rename_tac `TAKE idx8 (trace_blocks [] 0 fuel8 (stage 8) root_tf root_entry)` >>
  rename1 `idx8 = LENGTH trace_evs` >>
  rpt strip_tac >>
  `EVERY (\v. ?a e tf i t. v = ((a,e,i.inst_id),tf,i,t))
    (TAKE idx8 (trace_blocks [] 0 fuel8 (stage 8) root_tf root_entry))` by
    (qpat_assum `dft_focus_packet_rel fuel8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac focus_packet_native_prefix_every) >>
     disch_then (qspec_then `\v. ?a e tf i t. v = ((a,e,i.inst_id),tf,i,t)` mp_tac) >>
     simp[]) >>
  `?a e tf i v. EL h (TAKE idx8 (trace_blocks [] 0 fuel8 (stage 8) root_tf root_entry)) =
     ((a,e,i.inst_id),tf,i,v)` by
    (qpat_x_assum `EVERY (\v. ?a e tf i t. _) _`
       (qspec_then `h` mp_tac o REWRITE_RULE [EVERY_EL]) >>
     impl_tac >- (once_rewrite_tac[] >>
       qpat_assum `LENGTH (TAKE _ _) = idx8` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     BETA_TAC >> disch_then ACCEPT_TAC) >>
  `EL h (trace_blocks [] 0 fuel8 (stage 8) root_tf root_entry) = ((a,e,i.inst_id),tf,i,v)` by
    (qpat_assum `h < idx8` (fn th =>
       qpat_assum `EL h (TAKE _ _) = _`
         (ACCEPT_TAC o REWRITE_RULE [MATCH_MP listTheory.EL_TAKE th]))) >>
  `h <= LENGTH trace_evs /\ h < LENGTH (trace_blocks [] 0 fuel8 (stage 8) root_tf root_entry)` by
    decide_tac >>
  drule_all_then strip_assume_tac focus_native_joint_visit >>
  qexistsl [`a`,`e`,`tf`,`i`,`v`,`stk`,`PG`,`G`,`tn`,`oms`,`om`,`hs`,`hist`] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  `trace_blocks [] 0 fuel8 (stage 8) root_tf root_entry =
    trace_blocks [] 0 fuel8 (stage 8) root_tf root_entry` by REFL_TAC >>
  drule_all_then strip_assume_tac focus_packet_visit_row >>
  qexistsl [`sf`,`inc`,`entry`,`order`,`res`,`nrest`,`bb`,`bt`,`ps`,`xs`,`ys`,`sched`,`hin`,`h0`,
            `beopt`,`nseen`,`front`,`closed`,`brest`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `beopt = SOME _` SUBST_ALL_TAC >>
  qpat_assum `dft_focus_packet_rel fuel8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o GEN_ALL o MATCH_MP
      (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] focus_packet_visit_cut)) >>
  disch_then (fn cut => qpat_assum `EL h (trace_blocks [] 0 _ _ _ _) = _`
    (mp_then (Pat `EL _ _ = _`) mp_tac cut)) >>
  disch_then (fn cut => qpat_assum `FLOOKUP _ a = _`
    (mp_then (Pat `FLOOKUP _ a = _`) mp_tac cut)) >>
  disch_then (fn cut => qpat_assum `FLOOKUP _ (a,e) = _`
    (mp_then (Pat `FLOOKUP _ (_,_) = _`) mp_tac cut)) >>
  disch_then (fn cut => qpat_assum `k = v.vs_inst_idx - LENGTH ps`
    (mp_then (Pat `_ = _ - LENGTH _`) mp_tac cut)) >>
  disch_then (fn cut => qpat_assum `q = EL k sched`
    (mp_then (Pat `_ = EL _ _`) mp_tac cut)) >>
  disch_then (qspec_then `cpl` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  SIMP_TAC bool_ss [UNWIND_THM2] >>
  disch_then (MATCH_ACCEPT_TAC o GEN_ALL o SIMP_RULE bool_ss [UNWIND_THM2])
QED
