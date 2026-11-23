(* Correlated source and actual target-frame indices at a bounded cut. *)
Theory gasFocusLowerDloadFrameSafety
Ancestors lowerDloadSafetyImmutableWriteCoverage[qualified] lowerDloadPtrJointAlloc[qualified] rich_list[qualified,ignore_grammar] pair[qualified,ignore_grammar]
  gasFocusLowerDloadActualEntry gasFocusLowerDloadActualInterior
  gasFocusLowerDloadFrameCallEntry gasFocusLowerDloadIndexedTerminalSafety
  gasFocusLowerDloadFrameRequestRow gasFocusLowerDloadFrameHaltRow
  gasFocusLowerDloadControlEntryExact gasFocusLowerDloadBranchReset
  gasFocusLowerDloadSuffixCons gasFocusLowerDloadSuffixPop
  gasFocusLowerDloadPopGeometry gasFocusLowerDloadPopSavedRows
  gasFocusLowerDloadLocalPopSync gasFocusLowerDloadPrivateFrameSuccessor
  gasFocusLowerDloadBytesWrite gasFocusLowerDloadBytesNext
  gasFocusLowerDloadEnvironmentPoint gasFocusLowerDloadArithmeticBindingPoint
  gasFocusLowerDloadLogStorePoint lowerDloadPtrLog[qualified]
  lowerDloadSafetyKeyedEnvironmentReadEffects[qualified]
  lowerDloadSafetyAccountReadEffects[qualified]
  lowerDloadSafetyStorageReadEffects[qualified]
  lowerDloadPtrJointStorage[qualified] lowerDloadPtrStorage[qualified]
  lowerDloadPtrScalar[qualified] lowerDloadPtrGas lowerDloadPtrJointScalar
  lowerDloadPtrJointNext lowerDloadPtrIdentity[qualified]
  lowerDloadPtrMemoryRead[qualified] lowerDloadPtrOrdinary[qualified]
  lowerDloadMemoryWritePointEffect[qualified]
  lowerDloadPtrByteStore[qualified] lowerDloadPtrMCopy[qualified]
  lowerDloadPtrMemoryStore[qualified] lowerDloadPtrJointMemoryStore[qualified]
  lowerDloadPublicCopyPointEffect[qualified] lowerDloadPtrCopy[qualified]
  lowerDloadPtrCopiedSafety lowerDloadPtrDalloca[qualified]
  lowerDloadOrdinaryEndpoint[qualified] lowerDloadPtrSourceInv[qualified]
  lowerDloadPtrAlloc lowerDloadPtrAllocTransport lowerDloadPtrJointBudget[qualified]
  lowerDloadSafetyAllocation[qualified]
  lowerDloadPublicTrace lowerDloadSafetyAmbient lowerDloadReturnAlignment
  lowerDloadClassifiedReadPointEffect[qualified] lowerDloadSafetyAllocBounds[qualified]
  ctxLookupAgree codegenRel[qualified] venomEffects
  lowerDloadSafetyDelegate lowerDloadSafetyCreate lowerDloadFrontier
  lowerDloadSafetyUpdates lowerDloadSafetyAssemblyPremises
  lowerDloadSafetyTaintWidth lowerDloadSafetyHashLog lowerDloadSafetyImmutableWriteEffects
  lowerDloadSafetyWriteAssembly lowerDloadSafetyValues
  lowerDloadPtrHash[qualified]
  irSupply venomWf unitShapeDefs unitTransformDefs fmpStepStructural[qualified]
  gasFocusLowerDloadCutGuards lowerDloadPtrControlInversion lowerDloadPtrBlockEntry
  lowerDloadSafetyKernel lowerDloadPtrRawReachable lowerDloadReturnOrdinary
  lowerDloadSafetyAdvance lowerDloadSafetyLocations
  lowerDloadSafetyBoundary lowerDloadPtrStatic lowerDloadPtrSupport
  lowerDloadPtrReachableStatic lowerDloadOracleCallAssembly lowerDloadPtrNormalReturn
  lowerDloadPtrRel lowerDloadPtrPhase lowerDloadSafetyRelation
  o1SafeUpto o1PassContract ptrDiscipline lowerDloadDefs o1ContractLowerDload
  unitMemInv[qualified] fmpAnalysisProps[qualified] gasCount[qualified]
  lowerDloadPtrTerminal lowerDloadPtrAggregate lowerDloadPtrCall contextCodegenRelProps
  lowerDloadPtrJointSafety lowerDloadPtrTerminalClosure ptrDisciplineEmptyTaint ctxLookupAgreeHelpers
  lowerDloadPtrPhaseNext lowerDloadPtrExpansionSafety lowerDloadPtrExpansionTransport
  lowerDloadPtrDloadOrigins lowerDloadPtrBackward lowerDloadPtrSupplyOrigins
  lowerDloadPtrBytesTransport[qualified]
  o1ContractLowerDloadStage instIdxIndep venomExecProps venomMemProps
  gasFocusLowerDloadRoot lowerDloadCurrentSafety lowerDloadScratchSafety
  lowerDloadRevertSuffix[qualified]
  genBlockSim[qualified] fmpStageBlockSimCode[qualified]
  contextCodegenRel venomExecSemantics venomInst venomState list finite_map pred_set
Libs
  lowerDloadReturnPackageLib

(* Proof motives only; the assembled safety theorem exports no new relation. *)
val frame_suffix = ``\A frames.
  !k a. k < LENGTH frames /\
    (a IN FRANGE (EL k frames).lf_H \/ MEM (SOME a) (EL k frames).lf_Q) ==>
    a IN ld_slots A (DROP k frames)``;

val frame_saved_control = ``\frames stk ds.
  !k. k < LENGTH stk ==>
    dload_control_match (EL (SUC k) frames).lf_supply
      (EL k stk).cf_fn (EL k ds).cf_fn (EL k stk).cf_state (EL k ds).cf_state
      (EL k stk).cf_inst [(EL k stk).cf_inst] 0``;

val frame_occurrence = ``\B lo P C C' vs Sigma names ds PH H un gn ti t.
  ?stk PG G tn fn inst s t0 A frames N X p h rs H0 un0 pfuel fs0 f0 A0.
    ld_sync lo P C vs stk PG G tn fn inst s t0 A frames N /\
    ^ld_probe_stable lo P Sigma names fs0 f0 A0 A frames /\
    gn = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    t0.vs_inst_idx = p /\ ld_prefix C' gn X p h t0 t /\
    h < LENGTH X /\ B (SUC h) (LENGTH X) /\ ti = EL h X /\
    dload_boundary_core (dyn_floor C vs) lo rs
      (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) stk)
      PG PH G H0 tn un0 s t0 stk ds /\
    dload_control_match (HD frames).lf_supply fn gn s t0 inst X 0 /\
    dload_prefix_match pfuel C' PH X h t0 H0 un0 t H un /\
    dload_control_match (HD frames).lf_supply fn gn s t inst X h /\
    (!v. v IN set (fn_ir_vars fn) ==>
      (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
    LENGTH rs = LENGTH frames /\ LENGTH rs = SUC (LENGTH stk) /\
    LENGTH stk = LENGTH ds /\
    (!k. k < LENGTH ds ==>
      (EL k ds).cf_fn = ld_image (EL (SUC k) frames) /\
      (EL k ds).cf_state = (EL (SUC k) frames).lf_tgt) /\
    (!k. k < LENGTH rs ==>
      (EL k rs).dr_scratch =
        FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
        {id | ?i. MEM i (fn_insts (EL k (fn::MAP (\c. c.cf_fn) stk))) /\
                  i.inst_id = id}) /\
    (!k. k < LENGTH stk ==>
      dload_live_layout lo (EL k stk).cf_state.vs_alloca_next
        (EL k ds).cf_state.vs_alloca_next (DROP (SUC k) rs) /\
      dload_equal_environment (EL k stk).cf_state (EL k ds).cf_state /\
      (EL k stk).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
      (EL k stk).cf_inst = (EL k ds).cf_inst /\
      (!a. a IN set (fn_ir_vars (EL k stk).cf_fn) ==>
        (lookup_var a (EL k stk).cf_state = NONE <=>
         lookup_var a (EL k ds).cf_state = NONE)) /\
      (?q. ir_supply_covers_fn q (EL k stk).cf_fn /\
        (?q'. lower_dload_function_supply q (EL k stk).cf_fn = ((EL k ds).cf_fn,q')) /\
        dload_control_match q (EL k stk).cf_fn (EL k ds).cf_fn
          (EL k stk).cf_state (EL k ds).cf_state (EL k stk).cf_inst
          [(EL k stk).cf_inst] 0)) /\
    s.vs_gas_readings = t0.vs_gas_readings /\ t0.vs_gas_readings = t.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) frames /\
    ^frame_suffix A frames /\ ^frame_saved_control frames stk ds``;

val frame_normal = ``^frame_occurrence (\_ _. T)``;

Theorem ld_frame_normal_entry[local]:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  gn = FST (lower_dload_function_supply (Sigma fn.fn_name) fn) /\
  enters_block gn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  active_inst gn ti t /\ gas_cut n vs t ==>
  ^frame_normal lo P C C' vs Sigma names [] [] FEMPTY entry_taint gn ti t
Proof
  BETA_TAC >> strip_tac >>
  drule_all_then (qspec_then `C'` strip_assume_tac) ld_focus_actual_frame_entry >>
  qexistsl [`[]`,`[]`,`FEMPTY`,`entry_taint`,`fn`,`inst`,`t`,`t`,`FEMPTY`,`[f]`,
    `1`,`X`,`0`,`0`,
    `[<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>]`,
    `FEMPTY`,`entry_taint`,`0`,`[]`,`f`,`FEMPTY`] >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> gvs[listTheory.EL] >>
  Cases >> simp[rich_listTheory.DROP] >>
  metis_tac[ld_global_selected, ld_sync_slots, MEM]
QED

Theorem ld_frame_normal_interior[local]:
  ^frame_normal lo P C C' vs Sigma names ds PH H un gn ti t /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) gn.fn_blocks) /\
  step_inst fuel C' ti t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^frame_occurrence (=) lo P C C' vs Sigma names ds PH H un gn ti t \/
  ^frame_normal lo P C C' vs Sigma names ds PH
    (step_prov PH H ti u) (step_taint ti t u un) gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  Cases_on `SUC h < LENGTH X`
  >- (disj2_tac >> drule ld_sync_source >> strip_tac >>
      drule_all ld_focus_actual_interior_next >> strip_tac >>
      qexistsl [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`t0`,`A`,`frames`,`N`,`X`,`p`,
        `SUC h`,`rs`,`H0`,`un0`,`pfuel`,`fs0`,`f0`,`A0`] >> simp[] >> metis_tac[]) >>
  disj1_tac >>
  qexistsl [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`t0`,`A`,`frames`,`N`,`X`,`p`,
    `h`,`rs`,`H0`,`un0`,`pfuel`,`fs0`,`f0`,`A0`] >> simp[] >> metis_tac[]
QED

Theorem ld_frame_normal_block[local]:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  callee_first names C.ctx_functions /\
  (!f. MEM f C.ctx_functions ==>
    lookup_function f.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma f.fn_name) f))) /\
  (!f. MEM f C.ctx_functions ==> ir_supply_covers_fn (Sigma f.fn_name) f) /\
  ^frame_normal lo P C C' vs Sigma names ds PH H un gn ti t /\
  is_terminator ti.inst_opcode /\ step_inst fuel C' ti t = OK q /\ ~q.vs_halted /\
  enters_block gn q t1 /\ active_inst gn j t1 /\ gas_cut n vs t1 ==>
  ^frame_normal lo P C C' vs Sigma names ds PH
    (entry_prov gn q H) (entry_taint_vars gn q un) gn j t1
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  `gas_cut n vs t` by (drule_all ld_block_entry_cut_back >> simp[]) >>
  namedCases_on `frames` ["", "f fs1"] >- fs[] >>
  RULE_ASSUM_TAC (REWRITE_RULE[HD,TL]) >>
  qpat_x_assum `fs1 = fs0` (SUBST_ALL_TAC o SYM) >>
  drule_all dload_control_block_inversion >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac))) >>
  qpat_x_assum `ld_prefix _ _ _ _ 0 _ _`
    (strip_assume_tac o SRULE[ld_prefix_zero]) >>
  qpat_x_assum `dload_prefix_match _ _ _ _ 0 _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[dload_prefix_zero]) >>
  qpat_x_assum `t = t0` SUBST_ALL_TAC >>
  qpat_x_assum `H = H0` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `un = un0` (SUBST_ALL_TAC o SYM) >>
  `gas_cut n vs s` by
    (qpat_assum `gas_cut n vs t0` (mp_tac o REWRITE_RULE[gas_cut_def]) >>
     simp[gas_cut_def]) >>
  drule ld_sync_source >> strip_tac >>
  `raw_reachable vs C fn inst s` by
    (irule lowerDloadPtrRawReachableTheory.frame_reachable_raw >> metis_tac[]) >>
  qpat_assum `o1_safe_upto D lo n C vs`
    (strip_assume_tac o REWRITE_RULE[o1_safe_upto_def,o1_ptr_safe_upto_def]) >>
  qpat_assum `!fn inst s. raw_reachable vs C fn inst s /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `ptr_discipline_upto lo n C vs`
    (drule_all_then strip_assume_tac o cj 3 o REWRITE_RULE[ptr_discipline_upto_def]) >>
  `gn = FST (lower_dload_function_supply (Sigma fn.fn_name) fn)` by
    (qpat_assum `EVERY (\a. a.lf_supply = _) (f::fs1)`
       (assume_tac o CONJUNCT1 o SRULE[EVERY_DEF]) >>
     drule ld_sync_active >> simp[ld_image_def]) >>
  `^ld_probe_stable lo P Sigma names fs1 f A A (f::fs1)` by
    (BETA_TAC >> asm_rewrite_tac[HD,TL,NOT_CONS_NIL]) >>
  `(o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs)`
    by simp[] >>
  drule_all ld_focus_control_entry_exact >> strip_tac >>
  `active_inst fn ni s1` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ fn ni s1 _ _ _ _`
       (mp_tac o MATCH_MP ld_sync_source) >> simp[]) >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ fn inst s _ _ _ _`
       (assume_tac o cj 8 o REWRITE_RULE[ld_sync_def]) >> simp[]) >>
  `!a. MEM a C.ctx_functions ==> fn_ptr_ok P a` by fs[EVERY_MEM] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    (qpat_assum `frame_reachable vs C stk PG G tn fn inst s`
       (mp_tac o MATCH_MP frame_reachable_prov_supported) >>
     disch_then (qspec_then `P` mp_tac) >> simp[]) >>
  `fn_ptr_ok P fn` by simp[] >>
  `o1_fn_shape C fn` by
    (qpat_assum `o1_ctx_shape C`
       (mp_tac o cj 3 o REWRITE_RULE[o1_ctx_shape_def]) >> simp[EVERY_MEM]) >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `opaque_use_ok fn /\ ALL_DISTINCT (fn_labels fn)` by
    (qpat_x_assum `o1_fn_shape C fn` mp_tac >>
     simp[o1_fn_shape_def,unitShapeDefsTheory.fn_shape_ok_def,venomWfTheory.wf_function_def]) >>
  `!v. MEM (Var v) inst.inst_operands ==>
       v IN set (fn_ir_vars fn) DIFF {a | retpc_var fn a}` by
    (`~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET]` by
       (qpat_x_assum `MEM inst.inst_opcode [JMP;JNZ;DJMP]`
          (strip_assume_tac o REWRITE_RULE[MEM]) >> simp[]) >>
     rpt strip_tac >>
     drule_all lowerDloadPtrJointScalarTheory.dload_original_nonopaque_operands >>
     simp[]) >>
  `!a v bb op w. MEM a (fn_insts fn) /\ a.inst_opcode = PHI /\
       a.inst_outputs = [v] /\ v IN set (fn_ir_vars fn) DIFF {x | retpc_var fn x} /\
       resolve_phi bb a.inst_operands = SOME op /\ op = Var w ==>
       w IN set (fn_ir_vars fn) DIFF {x | retpc_var fn x}` by
    (rpt strip_tac >> irule dload_original_phi_input_tracked >>
     qexistsl [`a`,`bb`,`v`] >> simp[]) >>
  `f.lf_fn = fn /\ f.lf_supply = Sigma fn.fn_name` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ fn inst s _ _ _ _`
       (strip_assume_tac o SRULE[HD] o MATCH_MP ld_sync_active) >>
     qpat_assum `EVERY (\a. a.lf_supply = _) (f::fs1)`
       (assume_tac o CONJUNCT1 o SRULE[EVERY_DEF]) >> simp[]) >>
  `g.lf_supply = f.lf_supply /\ g.lf_serial = f.lf_serial /\ g.lf_fn = fn` by
    (qpat_assum `g = f with <|lf_src := _; lf_tgt := _; lf_H := _; lf_tv := _|>`
       SUBST1_TAC >> simp[]) >>
  `?qout. lower_dload_function_supply f.lf_supply fn = (gn,qout)` by
    ((qexists `SND (lower_dload_function_supply f.lf_supply fn)` >>
     simp[pairTheory.PAIR] >> (metis_tac[pairTheory.PAIR]))) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
   ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)` by
    (drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     simp[GSYM fn_labels_def]) >>
  qpat_assum `g.lf_supply = f.lf_supply` (fn eq =>
    qpat_assum `ld_envelope g.lf_supply fn s1 _ X _`
      (assume_tac o REWRITE_RULE[eq])) >>
  drule_at (Pat `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ld_focus_actual_branch_reset >>
  disch_then (drule_at (Pat `dload_control_match _ _ _ _ _ _ _ _`)) >>
  disch_then drule_all >> disch_then (qspec_then `pfuel` strip_assume_tac) >>
  `0 < LENGTH X` by metis_tac[dload_control_match_expansion] >>
  `t1.vs_allocas = t0.vs_allocas` by
    (qpat_assum `enters_block gn q t1`
       (mp_tac o MATCH_MP lowerDloadPtrEntryTheory.dload_enters_block_allocations) >>
     simp[jump_to_def]) >>
  `s1.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `enters_block fn (jump_to lbl s) s1`
       (mp_tac o MATCH_MP o1LowerDloadRunnerBoundaryTheory.ld_enters_block_call_ctx) >>
     simp[jump_to_def]) >>
  qpat_x_assum `^ld_probe_stable lo P Sigma names fs1 f A A (g::fs1)`
    (strip_assume_tac o SRULE[HD,TL]) >>
  `^frame_suffix A (g::fs1)` by
    (CONV_TAC (REDEPTH_CONV BETA_CONV) >>
     `FDOM A = ld_slots A (g::fs1)` by
       (qpat_assum `ld_sync _ _ _ _ _ _ _ _ fn ni s1 _ _ _ _`
          (mp_tac o MATCH_MP ld_sync_slots) >> simp[]) >>
     MATCH_MP_TAC (Q.INST [`m` |-> `1`, `old` |-> `f::fs1`,
                           `A` |-> `A`, `lo` |-> `lo`] ld_focus_suffix_cons) >>
     qpat_assum `!k a. _ ==> _ IN ld_slots A (DROP k (f::fs1))` mp_tac >>
     simp[rich_listTheory.DROP]) >>
  qexistsl [`stk`,`PG`,`entry_prov fn (jump_to lbl s) G`,
    `entry_taint_vars fn (jump_to lbl s) tn`,`fn`,`ni`,`s1`,`t1`,`A`,`g::fs1`,
    `N`,`X`,`t1.vs_inst_idx`,`0`,`rs`,`entry_prov gn q H`,
    `entry_taint_vars gn q un`,`pfuel`,`fs1`,`f`,`A`] >>
  conj_tac
  >- (CONV_TAC (REDEPTH_CONV BETA_CONV) >> simp[HD,TL]) >>
  `LENGTH ds = LENGTH fs1` by fs[] >>
  qpat_x_assum `g = f with <|lf_src := _; lf_tgt := _; lf_H := _; lf_tv := _|>` kall_tac >>
  qpat_x_assum `gn = ld_image f` kall_tac >>
  qpat_x_assum `gn = FST _` kall_tac >>
  simp[HD,TL,NOT_CONS_NIL,listTheory.EL] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- gvs[] >>
  conj_tac >- gvs[] >>
  conj_tac >- gvs[] >>
  conj_tac >- (Cases >> simp[listTheory.EL]) >>
  gvs[] >> first_assum ACCEPT_TAC
QED

Theorem ld_frame_normal_call[local]:
  o1_ctx_shape C /\ callee_first names C.ctx_functions /\
  (!g. MEM g C.ctx_functions ==>
    ir_supply_covers_fn (Sigma g.fn_name) g /\ fn_ptr_ok P g /\
    lookup_function g.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma g.fn_name) g))) /\
  ptr_discipline_upto lo n C vs /\
  ^frame_normal lo P C C' vs Sigma names ds PH H un gn call t /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME gcallee /\
  eval_operands ops t = SOME argsT /\ setup_callee gcallee argsT t = SOME ct /\
  enters_block gcallee ct tp /\ active_inst gcallee ti tp /\ gas_cut n vs tp ==>
  ^frame_normal lo P C C' vs Sigma names
    (<|cf_fn := gn; cf_inst := call; cf_state := t;
       cf_params := PH; cf_prov := H; cf_tvar := un.t_var |> :: ds)
    (MAP (op_prov H) ops) FEMPTY (un with t_var := FEMPTY) gcallee ti tp
Proof
  qabbrev_tac `Stable = ^ld_probe_stable` >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  namedCases_on `frames` ["", "f fs"] >- fs[Abbr `Stable`] >>
  RULE_ASSUM_TAC (REWRITE_RULE[HD,TL]) >>
  `dload_control_match f.lf_supply fn gn s t call [call] 0` by
    (qpat_assum `dload_control_match _ _ _ _ t _ _ h`
       (strip_assume_tac o MATCH_MP dload_control_match_expansion) >>
     `MEM call X` by metis_tac[EL_MEM] >>
     `call = inst` by
       (irule lower_dload_inst_supply_control >>
        conj_tac >- (goal_assum (drule_at Any) >> metis_tac[]) >> simp[]) >>
     qpat_x_assum `call = inst` SUBST_ALL_TAC >>
     `lower_dload_inst_supply is inst = ([inst],is)` by
       (irule lower_dload_inst_supply_special >> simp[]) >>
     `X = [inst]` by
       (qpat_assum `lower_dload_inst_supply _ inst = (X,_)` mp_tac >> simp[]) >>
     `h = 0` by fs[] >>
     qpat_x_assum `X = [inst]` SUBST_ALL_TAC >>
     qpat_x_assum `h = 0` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (Stable = _)`
    (fn th => drule_all (REWRITE_RULE[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]
      (CONV_RULE (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_THM2)) ld_focus_frame_call_entry))) >>
  strip_tac >>
  qabbrev_tac `saved = <|cf_fn := fn; cf_inst := call; cf_state := s;
                        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>` >>
  `0 < LENGTH emitted` by
    (qpat_assum `dload_control_match _ callee gcallee cs _ i emitted 0`
       (mp_tac o MATCH_MP dload_control_match_expansion) >> simp[] >> strip_tac >> simp[]) >>
  `LENGTH ds = LENGTH fs` by fs[] >>
  `^frame_suffix A (fc::f::fs)` by
    (CONV_TAC (REDEPTH_CONV BETA_CONV) >>
     `FDOM A = ld_slots A (fc::f::fs)` by
       (qpat_assum `ld_sync _ _ _ _ _ _ _ _ callee i cs _ _ _ _`
          (mp_tac o MATCH_MP ld_sync_slots) >> simp[]) >>
     `ld_global lo A (fc::f::fs)` by fs[Abbr `Stable`] >>
     MATCH_MP_TAC (Q.INST [`m` |-> `0`, `old` |-> `f::fs`,
                           `A` |-> `A`, `lo` |-> `lo`] ld_focus_suffix_cons) >>
     qpat_assum `!k a. _ ==> _ IN ld_slots A (DROP k (f::fs))` mp_tac >>
     simp[rich_listTheory.DROP]) >>
  qexistsl [`saved::stk`,`MAP (op_prov G) ops`,`FEMPTY`,`tn with t_var := FEMPTY`,
    `callee`,`i`,`cs`,`tp`,`A`,`fc::f::fs`,`SUC N`,`emitted`,`tp.vs_inst_idx`,`0`,
    `<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: rs`,
    `FEMPTY`,`un with t_var := FEMPTY`,`pfuel`,`f::fs`,`fc`,`A`] >>
  qpat_x_assum `Abbrev (saved = _)`
    (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  let val rows = [HD,EL,rich_listTheory.DROP] in
    RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) rows) >> SIMP_TAC (srw_ss()) rows
  end >>
  gvs[] >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     first_x_assum (drule_then strip_assume_tac) >>
     metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `t = f.lf_tgt` by
    (qpat_assum `!k. _ ==> _ /\ (EL k (_::ds)).cf_state = (EL k (f::fs)).lf_tgt`
       (qspec_then `0` (strip_assume_tac o SIMP_RULE (srw_ss()) [EL])) >>
     first_assum ACCEPT_TAC) >>
  Cases >> simp[EL] >>
  qpat_x_assum `t = f.lf_tgt` SUBST_ALL_TAC >> first_assum ACCEPT_TAC
QED

(* An actual return cannot be in the interior of a generated DLOAD. *)
Theorem ld_frame_intret_boundary[local]:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t0 A frames N /\
  ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix Ct gn X p h t0 t /\ h < LENGTH X /\ ti = EL h X /\
  step_inst fuel Ct ti t = IntRet rt te ==>
  X = [inst] /\ h = 0 /\ ti = inst /\ t = t0 /\
  inst.inst_opcode = RET /\ te = t
Proof
  strip_tac >>
  drule ld_sync_source >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all lowerDloadSafetyAmbientTheory.ld_sync_fn_shape >>
     strip_tac >> drule lowerDloadSafetyAmbientTheory.o1_fn_shape_components >> simp[]) >>
  `is_terminator ti.inst_opcode` by
    (drule o1ContractSimplifyCfgSrcFrameTheory.step_inst_intret_opcodes >>
     simp[] >> strip_tac >> simp[is_terminator_def]) >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (Cases_on `inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES`
     >- (`~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
           (qpat_x_assum `_ = DLOAD \/ _ = DLOADBYTES` strip_assume_tac >>
            simp[is_terminator_def]) >>
         drule_all_then assume_tac lowerDloadEnvelopeControlTheory.ld_envelope_nonterminal >>
         qpat_assum `EVERY _ X` (mp_tac o REWRITE_RULE[EVERY_EL]) >>
         disch_then (qspec_then `h` mp_tac) >> simp[] >> metis_tac[]) >>
     fs[]) >>
  `X = [inst]` by (drule_all lowerDloadSafetyLocationsTheory.ld_envelope_ordinary >> simp[]) >>
  `h = 0` by fs[] >>
  `ti = inst /\ t = t0` by fs[ld_prefix_zero] >>
  `MEM fn C.ctx_functions` by
    (drule lowerDloadSafetyAmbientTheory.ld_frame_reachable_certificate >> simp[]) >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `pre_fmp_opcode inst.inst_opcode` by
    (fs[o1_safe_upto_def,o1_ptr_safe_upto_def,fmp_free_ctx_def,
        pre_fmp_ops_def,EVERY_MEM] >> metis_tac[]) >>
  `inst.inst_opcode = RET` by
    (drule o1ContractSimplifyCfgSrcFrameTheory.step_inst_intret_opcodes >>
     fs[pre_fmp_opcode_def]) >>
  simp[] >> metis_tac[o1LowerDloadRunnerBoundaryTheory.ld_ret_endpoint]
QED

Theorem ld_frame_return_bind_readings[local]:
  bind_outputs outs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state saved te)) = SOME u ==>
  u.vs_gas_readings = te.vs_gas_readings
Proof
  strip_tac >> drule o1LowerDloadJointRestoreTheory.ld_bind_outputs_vars_only >>
  disch_then (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >>
  Cases_on `rt.iret_adopt_fmp` >>
  simp[venomExecSemanticsTheory.adopt_return_fmp_def,
       venomExecSemanticsTheory.merge_callee_state_def]
QED

Theorem ld_frame_normal_return[local]:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ^frame_normal lo P C C' vs Sigma names (d::ds) PH H un gn ri t /\
  step_inst fuel C' ri t = IntRet rt te /\
  bind_outputs d.cf_inst.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state d.cf_state te)) = SOME u /\
  active_inst d.cf_fn j (u with vs_inst_idx := SUC d.cf_state.vs_inst_idx) /\
  gas_cut n vs (u with vs_inst_idx := SUC d.cf_state.vs_inst_idx) ==>
  ^frame_normal lo P C C' vs Sigma names ds d.cf_params
    (DRESTRICT d.cf_prov (COMPL (set d.cf_inst.inst_outputs)))
    (un with t_var := DRESTRICT d.cf_tvar (COMPL (set d.cf_inst.inst_outputs)))
    d.cf_fn j (u with vs_inst_idx := SUC d.cf_state.vs_inst_idx)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  drule_all_then strip_assume_tac ld_frame_intret_boundary >>
  qpat_x_assum `h = 0` SUBST_ALL_TAC >>
  qpat_x_assum `ri = inst` SUBST_ALL_TAC >>
  qpat_x_assum `t = t0` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `te = t` SUBST_ALL_TAC >>
  qpat_x_assum `X = [inst]` SUBST_ALL_TAC >>
  qpat_x_assum `dload_prefix_match _ _ _ _ 0 _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[dload_prefix_zero]) >>
  qpat_x_assum `H = H0` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `un = un0` (SUBST_ALL_TAC o SYM) >>
  drule ld_frame_return_bind_readings >> strip_tac >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  namedCases_on `stk` ["", "c cs"] >- fs[] >>
  namedCases_on `rs` ["", "e rs1"] >- fs[] >>
  namedCases_on `rs1` ["", "r rs2"] >- fs[] >>
  drule ld_sync_source >> strip_tac >>
  `taint_ok fn tn inst s` by
    (qpat_assum `o1_safe_upto D lo n C vs`
      (strip_assume_tac o REWRITE_RULE[o1_safe_upto_def,o1_ptr_safe_upto_def]) >>
     qpat_assum `ptr_discipline_upto lo n C vs`
      (drule_all_then strip_assume_tac o cj 3 o REWRITE_RULE[ptr_discipline_upto_def]) >>
     simp[]) >>
  `!a. MEM a C.ctx_functions ==> fn_ptr_ok P a` by
    (qhdtm_assum `ld_sync`
      (mp_tac o cj 8 o REWRITE_RULE[ld_sync_def]) >> simp[EVERY_MEM]) >>
  drule frame_reachable_prov_supported >> disch_then (qspec_then `P` mp_tac) >>
  simp[] >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (`fn_ptr_ok P fn` by simp[] >> fs[fn_ptr_ok_def]) >>
  `opaque_use_ok fn` by
    (drule_all lowerDloadSafetyAmbientTheory.ld_sync_fn_shape >>
     simp[o1_fn_shape_def,unitShapeDefsTheory.fn_shape_ok_def]) >>
  `!a. MEM (Var a) (FRONT inst.inst_operands) ==>
       a IN (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})` by
    (rpt strip_tac >>
     `MEM (Var a) inst.inst_operands` by
       (Cases_on `inst.inst_operands` >- fs[] >>
        drule rich_listTheory.MEM_FRONT >> simp[]) >>
     `MEM a (fn_ir_vars fn)` by metis_tac[fn_ir_vars_operand] >>
     simp[] >> irule lowerDloadOpaqueExecutionTheory.ld_retpc_return_front >>
     simp[] >> qexists `inst` >> simp[]) >>
  `!a. MEM (Var a) inst.inst_operands ==>
       (lookup_var a s = NONE <=> lookup_var a t = NONE)` by
    (rpt strip_tac >> `MEM a (fn_ir_vars fn)` by metis_tac[fn_ir_vars_operand] >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) d.cf_fn.fn_blocks)` by
    (qpat_assum `!k. k < LENGTH (c::cs) ==> dload_live_layout _ _ _ _ /\ _`
       (qspec_then `0` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
     `MEM c.cf_fn C.ctx_functions` by metis_tac[MEM] >>
     `o1_fn_shape C c.cf_fn` by fs[o1_ctx_shape_def,EVERY_MEM] >>
     drule lowerDloadSafetyAmbientTheory.o1_fn_shape_components >> strip_tac >>
     drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     simp[fn_labels_def]) >>
  drule_all dload_normal_return >> strip_tac >>
  namedCases_on `frames` ["", "fc tail"] >- fs[] >>
  namedCases_on `tail` ["", "fc0 fs0'"] >- fs[] >>
  `fc0.lf_fn = c.cf_fn /\ fc0.lf_src = c.cf_state /\
   fc0.lf_tgt = d.cf_state /\ ld_image fc0 = d.cf_fn` by
    (qpat_assum `!k. _ ==> _.cf_fn = ld_image _ /\ _`
       (qspec_then `0` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
     qhdtm_assum `ld_sync` (mp_tac o Q.SPEC `0` o cj 17 o REWRITE_RULE[ld_sync_def]) >>
     simp[] >> metis_tac[]) >>
  qabbrev_tac `B = DRESTRICT A (ld_slots A (fc0::fs0'))` >>
  `FDOM B = ld_slots B (fc0::fs0')` by
    simp[Abbr `B`, lowerDloadReturnInvokePopTheory.ld_slots_restrict_domain] >>
  `!a. a IN ld_slots A (fc0::fs0') ==> FLOOKUP B a = FLOOKUP A a` by
    simp[Abbr `B`, FLOOKUP_DRESTRICT] >>
  `!g a. MEM g (fc0::fs0') /\ (a IN FRANGE g.lf_H \/ MEM (SOME a) g.lf_Q) ==>
     FLOOKUP B a = FLOOKUP A a` by
    (qpat_x_assum `TL (fc::fc0::fs0') = fs0` (SUBST_ALL_TAC o SYM) >>
     fs[] >> metis_tac[SUBSET_DEF]) >>
  `c.cf_inst = d.cf_inst /\ c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address` by
    (qpat_assum `!k. k < LENGTH (c::cs) ==> dload_live_layout _ _ _ _ /\ _`
       (qspec_then `0` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >> simp[]) >>
  `bind_outputs c.cf_inst.inst_outputs rt.iret_values (merge_callee_state fc0.lf_src s) = SOME s'` by
    gvs[venomExecSemanticsTheory.adopt_return_fmp_def] >>
  `bind_outputs c.cf_inst.inst_outputs rt.iret_values (merge_callee_state fc0.lf_tgt t) = SOME u` by
    gvs[venomExecSemanticsTheory.adopt_return_fmp_def] >>
  qabbrev_tac `keep = COMPL (set c.cf_inst.inst_outputs)` >>
  `?g. g = fc0 with <|lf_src := s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx;
                       lf_tgt := u with vs_inst_idx := SUC d.cf_state.vs_inst_idx;
                       lf_H := DRESTRICT fc0.lf_H keep; lf_tv := DRESTRICT fc0.lf_tv keep|>` by simp[] >>
  `g.lf_src.vs_allocas = fc0.lf_src.vs_allocas /\ g.lf_tgt.vs_allocas = fc0.lf_tgt.vs_allocas /\
   g.lf_serial = fc0.lf_serial /\ FRANGE g.lf_H SUBSET FRANGE fc0.lf_H /\ g.lf_Q = fc0.lf_Q` by
    (drule_all lowerDloadReturnInvokePopTheory.ld_return_frame_geometry >> simp[]) >>
  `^frame_suffix B (g::fs0') /\ FDOM B = ld_slots B (g::fs0')` by
    (CONV_TAC (REDEPTH_CONV BETA_CONV) >>
     `B = DRESTRICT A (ld_slots A (fc0::fs0'))` by simp[Abbr `B`] >>
     drule_all ld_focus_suffix_pop >> simp[]) >>
  `dload_control_match fc0.lf_supply c.cf_fn d.cf_fn c.cf_state d.cf_state
     c.cf_inst [c.cf_inst] 0` by
    (qpat_assum `!k. k < LENGTH (c::cs) ==> dload_control_match _ _ _ _ _ _ _ 0`
       (qspec_then `0` (mp_tac o SIMP_RULE (srw_ss()) [])) >> simp[]) >>
  `bind_outputs c.cf_inst.inst_outputs rs.iret_values (merge_callee_state c.cf_state s) = SOME s' /\
   bind_outputs d.cf_inst.inst_outputs rt.iret_values (merge_callee_state d.cf_state t) = SOME u` by
    gvs[venomExecSemanticsTheory.adopt_return_fmp_def] >>
  drule_all_then strip_assume_tac lowerDloadPtrReturnTheory.dload_return_control_reachable >>
  drule_all_then strip_assume_tac ld_focus_pop_saved_rows >>
  qpat_assum `dload_boundary_core _ _ (r::rs2) _ _ _ _ _ _ _ _ _ _ cs ds`
    (strip_assume_tac o REWRITE_RULE [lowerDloadPtrAggregateTheory.dload_boundary_core_def]) >>
  `LENGTH (r::rs2) = LENGTH (g::fs0')` by fs[] >>
  `dload_live_layout lo g.lf_src.vs_alloca_next g.lf_tgt.vs_alloca_next (r::rs2)` by
    gvs[] >>
  `!k. k < LENGTH (g::fs0') ==>
    (EL k (r::rs2)).dr_source = (EL k (g::fs0')).lf_src.vs_allocas /\
    (EL k (r::rs2)).dr_target = (EL k (g::fs0')).lf_tgt.vs_allocas` by
    (Cases >> simp[EL]
     >- (drule lowerDloadPtrRelTheory.dload_table_stack_current >> simp[]) >>
     rename1 `k < LENGTH fs0' ==> _` >> strip_tac >>
     `k < LENGTH cs /\ k < LENGTH ds` by fs[] >>
     `(EL k cs).cf_state = (EL k fs0').lf_src` by
       ((qpat_assum `!j. j < LENGTH (c::cs) ==>
         (EL j (c::cs)).cf_fn = (EL j (fc0::fs0')).lf_fn /\ _`
          (qspec_then `SUC k` mp_tac) >>
        (impl_tac >- simp[]) >>
        disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [EL]) >> simp[] >> (gvs[]))) >>
     `(EL k ds).cf_state = (EL k fs0').lf_tgt` by
       (qpat_assum `!j. j < LENGTH (d::ds) ==> _.cf_fn = ld_image _ /\ _`
          (qspec_then `SUC k` mp_tac) >>
        (impl_tac >- simp[]) >>
        disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [EL]) >> simp[]) >>
     `SUC k < LENGTH (r::rs2)` by fs[] >>
     drule_all (Q.SPEC `SUC k` (Q.GEN `k` lowerDloadPtrRelTheory.dload_table_stack_saved)) >>
     simp[EL, EL_MAP]) >>
  RULE_ASSUM_TAC BETA_RULE >>
  `ld_global lo B (g::fs0')` by (drule_all ld_focus_pop_layout_global >> simp[]) >>
  drule_all_then strip_assume_tac ld_focus_pop_charge_geometry >>
  `set c.cf_inst.inst_outputs SUBSET set (fn_ir_vars fc0.lf_fn)` by
    (`active_inst c.cf_fn c.cf_inst c.cf_state` by
       metis_tac[dload_control_match_boundary] >>
     `MEM c.cf_inst (fn_insts c.cf_fn)` by metis_tac[ld_active_inst_member] >>
     simp[SUBSET_DEF] >> metis_tac[lowerDloadSafetyUpdatesTheory.ld_inst_output_ir]) >>
  `ld_envelope fc0.lf_supply c.cf_fn
     (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx) (SUC c.cf_state.vs_inst_idx)
     emitted' (SUC d.cf_state.vs_inst_idx) /\ 0 < LENGTH emitted' /\
   active_inst c.cf_fn i' (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx)` by
    (qpat_assum `dload_control_match fc0.lf_supply _ _ _ _ i' emitted' 0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[dload_control_match_def] >> strip_tac >>
     fs[ld_envelope_def, PULL_EXISTS] >>
     rename1 `b < LENGTH c.cf_fn.fn_blocks` >> qexists `b` >> gvs[]) >>
  `ld_sync lo P C vs cs c.cf_params (DRESTRICT c.cf_prov keep)
     (tn with t_var := DRESTRICT c.cf_tvar keep) c.cf_fn i'
     (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx)
     (u with vs_inst_idx := SUC d.cf_state.vs_inst_idx) B (g::fs0') N` by
    (qpat_assum `g = _` SUBST_ALL_TAC >>
     qpat_x_assum `Abbrev (keep = _)`
       (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     `B = DRESTRICT A (ld_slots A (fc0::fs0'))` by simp[Abbr `B`] >>
     irule (CONV_RULE (TOP_DEPTH_CONV Unwind.UNWIND_FORALL_CONV) ld_focus_local_pop_sync) >>
     qpat_assum `!j. j < LENGTH (c::cs) ==>
         (EL j (c::cs)).cf_fn = (EL j (fc0::fs0')).lf_fn /\ _`
       assume_tac >>
     qpat_assum `fc0.lf_fn = c.cf_fn` (assume_tac o SYM) >>
     qpat_assum `fc0.lf_src = c.cf_state` (assume_tac o SYM) >>
     qpat_assum `fc0.lf_tgt = d.cf_state` (assume_tac o SYM) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (qexists `emitted'` >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`A`,`G`,`PG`,`fc`,`fn`,`inst`,`s`,`t`,`rt.iret_values`] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qpat_assum `rs.iret_values = rt.iret_values` (rewrite_tac o single o SYM) >>
        first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qpat_assum `c.cf_inst = d.cf_inst` (rewrite_tac o single) >>
        first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `s'.vs_gas_readings = s.vs_gas_readings` by
    (irule ld_frame_return_bind_readings >> goal_assum (drule_at Any)) >>
  `!h a. MEM h fs0' /\ (a IN FRANGE h.lf_H \/ MEM (SOME a) h.lf_Q) ==>
      a IN ld_slots B fs0'` by
    (drule ld_focus_suffix_saved >> disch_then ACCEPT_TAC) >>
  qexistsl [`cs`, `c.cf_params`, `DRESTRICT c.cf_prov keep`,
    `tn with t_var := DRESTRICT c.cf_tvar keep`, `c.cf_fn`, `i'`,
    `s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx`,
    `u with vs_inst_idx := SUC d.cf_state.vs_inst_idx`,
    `B`, `g::fs0'`, `N`, `emitted'`, `0`, `r::rs2`,
    `DRESTRICT d.cf_prov (COMPL (set d.cf_inst.inst_outputs))`,
    `un with t_var := DRESTRICT d.cf_tvar (COMPL (set d.cf_inst.inst_outputs))`,
    `pfuel`, `g`, `B`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `g.lf_fn = fc0.lf_fn /\ g.lf_supply = fc0.lf_supply` by
    (qpat_assum `g = _` (simp o single)) >>
  `ld_image g = d.cf_fn` by
    (qpat_assum `g.lf_fn = fc0.lf_fn` (fn fth =>
       qpat_assum `g.lf_supply = fc0.lf_supply` (fn sth =>
         rewrite_tac[ld_image_def,fth,sth])) >>
     qpat_assum `ld_image fc0 = d.cf_fn`
       (ACCEPT_TAC o REWRITE_RULE[ld_image_def])) >>
  `!k. (EL k (g::fs0')).lf_fn = (EL (SUC k) (fc::fc0::fs0')).lf_fn` by
    (Cases >> simp[EL]) >>
  `LENGTH fs0' = LENGTH cs` by fs[] >>
  simp[NoAsms,HD,TL,dload_prefix_zero,ld_prefix_zero] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `EVERY (\f. f.lf_supply = _) (fc::fc0::fs0')`
       (strip_assume_tac o BETA_RULE o REWRITE_RULE[EVERY_DEF]) >>
     qpat_assum `g.lf_supply = fc0.lf_supply` (rewrite_tac o single) >>
     qpat_assum `g.lf_fn = fc0.lf_fn` (rewrite_tac o single) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `EVERY (\f. !j a. _ ==> j IN P f.lf_fn.fn_name) (fc::fc0::fs0')`
       (strip_assume_tac o BETA_RULE o REWRITE_RULE[EVERY_DEF]) >>
     qpat_assum `g.lf_Q = fc0.lf_Q` (rewrite_tac o single) >>
     qpat_assum `g.lf_fn = fc0.lf_fn` (rewrite_tac o single) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (map_every qx_gen_tac [`aidx`,`bidx`] >> strip_tac >>
     qpat_assum `!j k. _ ==> list_precedes _ _ names`
       (qspecl_then [`SUC aidx`,`SUC bidx`] mp_tac) >>
     qpat_assum `!k. (EL k (g::fs0')).lf_fn = _` (rewrite_tac o single) >>
     simp[NoAsms,LENGTH] >> decide_tac) >>
  conj_tac >-
    (rewrite_tac[SUBSET_DEF] >> qx_gen_tac `row` >> disch_tac >>
     qpat_assum `!h a. MEM h fs0' /\ _ ==> a IN ld_slots B fs0'`
       (qspec_then `row` mp_tac) >> simp[] >> metis_tac[]) >>
  conj_tac >- (sym_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[] >>
  conj_tac >- (conj_tac >- first_assum ACCEPT_TAC >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `dload_boundary_core _ _ (r::rs2) _ _ _ _ _ _ _ _ _ _ cs ds` mp_tac >>
     simp[Abbr `keep`] >> metis_tac[Abbr `keep`]) >>
  conj_tac >-
    (qpat_assum `g.lf_supply = fc0.lf_supply` (rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `g.lf_supply = fc0.lf_supply` (rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  `LENGTH rs2 = LENGTH cs` by
    (qpat_assum `LENGTH (r::rs2) = SUC (LENGTH cs)` mp_tac >> simp[NoAsms,LENGTH]) >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qx_gen_tac `idx` >> disch_tac >>
     qpat_assum `!k. k < LENGTH (d::ds) ==> _ /\ _`
       (qspec_then `SUC idx` mp_tac) >>
     simp[NoAsms,LENGTH,EL] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  conj_tac >-
    (qpat_assum `!k. k < LENGTH (r::rs2) ==> (EL k (r::rs2)).dr_scratch = _` mp_tac >>
     simp[NoAsms,LENGTH]) >>
  conj_tac >-
    (qpat_assum `!k. k < LENGTH cs ==> _ /\ _ /\ _ /\ _ /\ _ /\ ?q. _` mp_tac >>
     simp[NoAsms,DROP_def]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- gvs[] >>
  conj_tac >-
    (qpat_assum `!k a. k < LENGTH (g::fs0') /\ _ ==> _` mp_tac >>
     simp[NoAsms,LENGTH]) >>
  qx_gen_tac `idx` >> disch_tac >>
  qpat_assum `!k. k < LENGTH (c::cs) ==> dload_control_match _ _ _ _ _ _ _ _`
    (qspec_then `SUC idx` mp_tac) >>
  simp[NoAsms,LENGTH,EL] >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_tac >>
  qpat_assum `!k. k < LENGTH cs ==> dload_live_layout _ _ _ _ /\ _`
    (qspec_then `idx` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  metis_tac[]
QED

val frame_taint_rows = ``\D C ti t un.
  (!fuel u. active_inst gn ti t /\ ti.inst_opcode <> INVOKE /\
    step_inst fuel C ti t = OK u /\ LENGTH t.vs_requests < LENGTH u.vs_requests ==>
    un.t_stor SUBSET D.d_stor t.vs_call_ctx.cc_address
      (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
    un.t_trans SUBSET D.d_trans t.vs_call_ctx.cc_address
      (t.vs_transient t.vs_call_ctx.cc_address)) /\
  (!fuel u. active_inst gn ti t /\ ti.inst_opcode <> INVOKE /\
    step_inst fuel C ti t = Halt u ==>
    (step_taint ti t u un).t_stor SUBSET D.d_stor u.vs_call_ctx.cc_address
      (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
    (step_taint ti t u un).t_trans SUBSET D.d_trans u.vs_call_ctx.cc_address
      (u.vs_transient u.vs_call_ctx.cc_address) /\
    (step_taint ti t u un).t_imm SUBSET D.d_imm u.vs_immutables /\
    ret_taint un ti t SUBSET D.d_ret u.vs_returndata)``;

Theorem ld_frame_normal_taint_rows[local]:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\ dead_wf D /\
  gas_cut n vs t /\ ^frame_normal lo P C C' vs Sigma names ds PH H un gn ti t ==>
  ^frame_taint_rows D C' ti t un
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all ld_focus_frame_request_row >> simp[]) >>
  rpt gen_tac >> strip_tac >> drule_all ld_focus_frame_halt_row >> simp[]
QED

(* A forwarding slice is indexed at the current instruction on both sides.
   Its source reading equality is carried independently of the ghost tables. *)
val frame_terminal = ``\lo P vs C ds H un g j t.
  ?cs PG G tn f s fs bb tb bs bt mid a b k.
    frame_reachable vs C cs PG G tn f (EL k mid) s /\ j = EL k mid /\
    MEM bb f.fn_blocks /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb g.fn_blocks = SOME tb /\
    s.vs_inst_idx = a+k /\ t.vs_inst_idx = b+k /\
    TAKE (LENGTH mid) (DROP a bb.bb_instructions) = mid /\
    TAKE (LENGTH mid) (DROP b tb.bb_instructions) = mid /\
    a+LENGTH mid <= LENGTH bb.bb_instructions /\
    b+LENGTH mid <= LENGTH tb.bb_instructions /\
    mid <> [] /\ EVERY (\i. i.inst_opcode = ASSIGN) (FRONT mid) /\
    (LAST mid).inst_opcode = REVERT /\ k < LENGTH mid /\
    lower_dload_block_supply bs bb = (tb,bt) /\
    set (fn_ir_vars f) SUBSET set bs.irs_used_vars /\
    (!i v. MEM i bb.bb_instructions /\ MEM (Var v) i.inst_operands ==>
       v IN set (fn_ir_vars f)) /\
    (!h. h <= LENGTH mid ==> ?pre u.
       lower_dload_insts_supply bs (TAKE (a+h) bb.bb_instructions) = (pre,u) /\
       LENGTH pre = b+h) /\
    FDOM G SUBSET fn_pv P f /\ s.vs_labels = t.vs_labels /\
    (!v. v IN set (fn_ir_vars f) ==>
       (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
    dload_vars_match (dyn_floor C vs) fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
       G H tn un s t /\
    dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
    dload_table_stack fs (s::MAP (\c. c.cf_state) cs)
                        (t::MAP (\c. c.cf_state) ds) /\
    (ctx_has_dalloca C ==> allocas_below_fmp t) /\
    s.vs_gas_readings = t.vs_gas_readings``;

Theorem ld_frame_terminal_ptr_rows[local]:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ gas_cut n vs t /\
  ^frame_terminal lo P vs C ds H un gn ti t ==>
  access_ok lo H gn ti t /\ taint_ok gn un ti t /\ allocas_from lo t
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `access_ok lo G f (EL k mid) s /\ taint_ok f tn (EL k mid) s` by
    (qpat_assum `o1_safe_upto D lo n C vs`
       (strip_assume_tac o REWRITE_RULE[o1_safe_upto_def,o1_ptr_safe_upto_def]) >>
     qpat_assum `ptr_discipline_upto lo n C vs`
       (drule_all_then strip_assume_tac o cj 3 o REWRITE_RULE[ptr_discipline_upto_def]) >>
     simp[]) >>
  drule_all ld_focus_indexed_terminal_safety >> strip_tac >> simp[] >>
  irule dload_live_layout_allocas_from >>
  qexistsl [`fs`,`0`,`s.vs_alloca_next`,`t.vs_alloca_next`] >> simp[] >>
  qpat_assum `dload_table_stack fs _ _` mp_tac >>
  simp[NoAsms,dload_table_stack_def,listTheory.EL] >> strip_tac >>
  `0 < LENGTH fs` by simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[listTheory.EL]
QED

Theorem ld_frame_terminal_taint_rows[local]:
  ^frame_terminal lo P vs C ds H un gn ti t ==>
  ^frame_taint_rows D C' ti t un
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  SUBGOAL_THEN ``ti.inst_opcode = ASSIGN \/ ti.inst_opcode = REVERT`` assume_tac
  >- (drule_all dload_terminal_slice_opcode >> strip_tac >>
      `k + 1 < LENGTH mid \/ k + 1 = LENGTH mid` by decide_tac >> simp[]) >>
  conj_tac >> rpt gen_tac >> strip_tac
  >- (drule (lowerDloadRevertSuffixTheory.ld_revert_suffix_step) >>
      disch_then (qspecl_then [`ARB`,`u`,`t`,`fuel`,`C'`] strip_assume_tac) >>
      `u.vs_requests = t.vs_requests` by metis_tac[] >> fs[]) >>
  drule (lowerDloadRevertSuffixTheory.ld_revert_suffix_step) >>
  disch_then (qspecl_then [`ARB`,`u`,`t`,`fuel`,`C'`] strip_assume_tac) >>
  metis_tac[]
QED

Theorem ld_frame_return_cut_back[local]:
  step_inst fuel C ri t = IntRet rt te /\
  bind_outputs outs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state saved te)) = SOME u /\
  gas_cut n vs (u with vs_inst_idx := k) ==> gas_cut n vs t
Proof
  strip_tac >> drule ld_frame_return_bind_readings >> strip_tac >>
  qspecl_then [`fuel`,`C`,`ri`,`t`] mp_tac (CONJUNCT1 gasCountTheory.gas_count_suffix) >>
  simp[gasCountTheory.gas_count_suffix_def] >>
  disch_then (SUBST_ALL_TAC) >> gvs[gas_cut_def, listTheory.LENGTH_DROP] >> decide_tac
QED

Theorem ld_frame_singleton_sync_next[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs f0 A0 A (f::fs) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] t.vs_inst_idx /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK ss /\ step_inst fuel C' inst t = OK u /\
  active_inst (ld_image f) j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := H';
                       lf_tv := (step_taint inst s ss tn).t_var|>) /\
  ld_memory lo A (step_taint inst s ss tn) ss u /\
  ld_nonghost (step_taint inst s ss tn) ss u /\
  ld_ghost_ok (dyn_floor C vs) A H' (step_prov PG G inst ss) /\
  ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem ss.vs_memory u.vs_memory /\
  (!a. a IN FRANGE H' ==> a IN FDOM A) /\
  ss.vs_allocas = s.vs_allocas /\ u.vs_allocas = t.vs_allocas /\
  ss.vs_alloca_next = s.vs_alloca_next /\ u.vs_alloca_next = t.vs_alloca_next /\
  ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = t.vs_current_bb /\
  ss.vs_prev_bb = s.vs_prev_bb /\ u.vs_prev_bb = t.vs_prev_bb /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) ==>
  ?g i.
    g = (f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                  lf_tgt := u with vs_inst_idx := SUC t.vs_inst_idx;
                  lf_H := H'; lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn) fn i
      (ss with vs_inst_idx := SUC s.vs_inst_idx) (u with vs_inst_idx := SUC t.vs_inst_idx)
      A (g::fs) N /\
    ^ld_probe_stable lo P Sigma names fs f0 A0 A (g::fs) /\
    ss.vs_gas_readings = u.vs_gas_readings /\
    EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
               LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_abbrev_tac `goal` >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  `ld_global lo A (f::fs)` by fs[] >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  qabbrev_tac `sn = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `unext = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `?i Y. active_inst fn i sn /\
         ld_envelope f.lf_supply fn sn (SUC s.vs_inst_idx) Y (SUC t.vs_inst_idx)` by
    (drule_at (Pat `ld_envelope`) ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`unext`,`ld_image f`] mp_tac) >>
     simp[arithmeticTheory.ADD1, Abbr `sn`, Abbr `unext`] >> metis_tac[]) >>
  qabbrev_tac `g = f with <|lf_src := sn; lf_tgt := unext; lf_H := H';
                            lf_tv := (step_taint inst s ss tn).t_var|>` >>
  `ld_vars P A g` by
    (mp_tac (Q.INST
       [`f` |-> `f with <|lf_src := ss; lf_tgt := u; lf_H := H';
                          lf_tv := (step_taint inst s ss tn).t_var|>`,
        `i` |-> `SUC s.vs_inst_idx`, `j` |-> `SUC t.vs_inst_idx`]
       ld_vars_inst_indices) >>
     simp[Abbr `g`, Abbr `sn`, Abbr `unext`]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn) fn i sn unext
     A (g::fs) N /\ ld_global lo A (g::fs)` by
    (drule ld_sync_ordinary_advance >>
     simp[GSYM markerTheory.Abbrev_def] >> metis_tac[]) >>
  `^ld_probe_stable lo P Sigma names fs f0 A0 A (g::fs)` by
    (BETA_TAC >> irule (BETA_RULE ld_stable_head_replace) >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- (qexists_tac `f` >> rpt conj_tac >>
       TRY (first_assum ACCEPT_TAC) >> simp[Abbr `g`])) >> first_assum ACCEPT_TAC) >>
  `ss.vs_gas_readings = u.vs_gas_readings` by fs[ld_nonghost_def] >>
  `LENGTH ss.vs_gas_readings <= LENGTH s.vs_gas_readings` by
    (qspecl_then [`fuel`,`C`,`inst`,`s`] mp_tac (CONJUNCT1 gasCountTheory.gas_count_suffix) >>
     simp[gasCountTheory.gas_count_suffix_def, LENGTH_DROP] >> decide_tac) >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH sn.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)` by
    (simp[Abbr `g`, Abbr `sn`, Abbr `unext`] >>
     qpat_assum `EVERY _ (f::fs)`
       (mp_tac o cj 2 o REWRITE_RULE[EVERY_DEF]) >>
     rewrite_tac[EVERY_MEM] >> BETA_TAC >> strip_tac >>
     qx_gen_tac `a:ld_frame` >> disch_tac >>
     first_x_assum (qspec_then `a` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `ss.vs_gas_readings = u.vs_gas_readings` (rewrite_tac o single o SYM) >>
     decide_tac) >>
  qunabbrev_tac `goal` >> qexistsl [`g`,`i`] >>
  `ss with vs_inst_idx := SUC s.vs_inst_idx = sn` by simp[Abbr `sn`] >>
  `u with vs_inst_idx := SUC t.vs_inst_idx = unext` by simp[Abbr `unext`] >>
  qpat_assum `ss with vs_inst_idx := SUC s.vs_inst_idx = sn` SUBST1_TAC >>
  qpat_assum `u with vs_inst_idx := SUC t.vs_inst_idx = unext` SUBST1_TAC >>
  (conj_tac >- simp[Abbr `g`]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `^ld_probe_stable lo P Sigma names fs f0 A0 A (g::fs)`
    (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  `ss.vs_gas_readings = sn.vs_gas_readings` by simp[Abbr `sn`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `ss.vs_gas_readings = sn.vs_gas_readings` SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Theorem ld_frame_classified_read_sync[local]:
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs f0 A0 A (f::fs) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] t.vs_inst_idx /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ] /\
  step_inst fuel C' inst t = OK u /\
  active_inst (ld_image f) j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) ==>
  ?ss g i Hr.
    step_inst fuel C inst s = OK ss /\
    g = (f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                  lf_tgt := u with vs_inst_idx := SUC t.vs_inst_idx;
                  lf_H := Hr; lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn) fn i
      (ss with vs_inst_idx := SUC s.vs_inst_idx) (u with vs_inst_idx := SUC t.vs_inst_idx)
      A (g::fs) N /\
    ^ld_probe_stable lo P Sigma names fs f0 A0 A (g::fs) /\
    ss.vs_gas_readings = u.vs_gas_readings /\
    EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
               LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_active >> simp[NoAsms] >> strip_tac >>
  drule_all ld_sync_source_mem_inv >> strip_tac >>
  `s.vs_initial_fmp = vs.vs_initial_fmp` by
    (drule_all lowerDloadSafetyAmbientTheory.ld_frame_raw_reachable >>
     metis_tac[ctxLookupAgreeTheory.raw_reachable_initial_fmp]) >>
  drule ld_sync_frontier >> strip_tac >>
  `t.vs_alloca_next <= dyn_floor C vs` by
    (simp[dyn_floor_def] >> IF_CASES_TAC >>
     gvs[dload_headroom_ok_def,ctx_has_dalloca_def] >> decide_tac) >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_target_headroom] >>
  drule ld_sync_slots >> strip_tac >>
  drule ld_sync_maps >> strip_tac >>
  `ld_global lo A (f::fs)` by fs[] >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==>
     b+sz <= dyn_floor C vs /\ c+sz < dimword(:256)` by
    (rpt gen_tac >> strip_tac >>
     drule_all lowerDloadSafetyAllocBoundsTheory.ld_alloc_frontiers >> simp[] >>
     decide_tac) >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> b+sz <= dyn_floor C vs` by metis_tac[] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  `MEM inst.inst_opcode [MLOAD;ILOAD] ==> ~in_revert_forward fn s` by
    (strip_tac >> irule concretizeLayoutLocalReturnTheory.active_inst_not_revert_forward >>
     conj_tac >- simp[fn_labels_def] >> qexists_tac `inst` >> simp[] >>
     qpat_assum `MEM inst.inst_opcode [MLOAD;ILOAD]` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
   ~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst s = []` by
    (qpat_assum `MEM inst.inst_opcode _` mp_tac >> pure_rewrite_tac[listTheory.MEM] >>
     strip_tac >> simp[is_terminator_def,is_alloca_op_def,write_effects_def,
                       empty_effects_def,codegenRelTheory.source_memory_write_ranges_def]) >>
  drule_all lowerDloadClassifiedReadPointEffectTheory.ld_sync_classified_read_effect_at >>
  disch_then (qx_choose_then `ss` (qx_choose_then `H'` strip_assume_tac)) >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  drule_all ld_sync_dyn_agree_unwritten >> strip_tac >>
  drule_all (BETA_RULE ld_frame_singleton_sync_next) >>
  disch_then (qx_choose_then `g` (qx_choose_then `i` (fn th =>
    assume_tac (CONJUNCT2 th) >> SUBST_ALL_TAC (CONJUNCT1 th)))) >>
  qexistsl_tac [`ss`,`i`,`H'`] >> fs[] >> conj_tac
  >- (qpat_assum `!j a. j < LENGTH (f:ld_frame).lf_Q /\ _ ==>
         j IN P f.lf_fn.fn_name` mp_tac >>
      qpat_assum `(f:ld_frame).lf_fn = fn` (fn eq => simp[NoAsms,eq])) >>
  qpat_assum `!g. MEM g fs ==> FRANGE g.lf_H SUBSET ld_slots A fs /\ _`
    (fn th => metis_tac[th])
QED

Theorem ld_frame_identity_boundary[local]:
  MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE] /\
  MEM inst (fn_insts fn) /\ fn_inst_wf fn /\ opaque_use_ok fn /\
  fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ s.vs_labels = t.vs_labels /\
  (!v. MEM v (fn_ir_vars fn) ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core floor lo rs (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
    Ws PG PH G H tn un s t stk ds /\ step_inst fuel C' inst t = OK u ==>
  step_inst fuel C inst s = OK s /\ u = t /\
  step_prov PG G inst s = G /\ step_taint inst s s tn = tn /\
  (!v. MEM v (fn_ir_vars fn) ==>
    (lookup_var v (s with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
     lookup_var v (u with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
  dload_boundary_core floor lo rs (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
    Ws PG PH (step_prov PG G inst s) (step_prov PH H inst u)
    (step_taint inst s s tn) (step_taint inst t u un)
    (s with vs_inst_idx := SUC s.vs_inst_idx) (u with vs_inst_idx := SUC t.vs_inst_idx)
    stk ds
Proof
  strip_tac >>
  `inst.inst_outputs = []` by metis_tac[lowerDloadPtrIdentityTheory.identity_arity] >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by
    (qpat_assum `MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE]` mp_tac >>
     pure_rewrite_tac[MEM] >> strip_tac >> simp[]) >>
  `!v. MEM (Var v) inst.inst_operands ==>
    v IN (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})` by
    metis_tac[dload_original_nonopaque_operands] >>
  `written_taint tn inst s = {}` by
    (irule lowerDloadPtrScalarTheory.written_taint_opcode_exclusion >>
     qpat_assum `MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE]` mp_tac >>
     pure_rewrite_tac[MEM] >> strip_tac >> simp[]) >>
  `step_prov PG G inst s = G /\ step_taint inst s s tn = tn` by
    (qpat_assum `MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE]` mp_tac >>
     pure_rewrite_tac[MEM] >> strip_tac >>
     simp[step_prov_def, set_prov_def, step_taint_def, DRESTRICT_UNIV,
          set_var_taint_def, mem_taint_def, adopt_reset_def, store_taint_def,
          imm_taint_def, new_site_bytes_def, step_writes_def, range_bytes_def,
          codegenRelTheory.source_memory_write_ranges_def, FLOOKUP_DEF,
          taint_component_equality, EXTENSION, SF CONJ_ss]) >>
  drule_at (Pat `dload_boundary_core`)
    lowerDloadPtrIdentityTheory.dload_boundary_core_identity_index >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars fn)`,`C`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[fn_ir_vars_operand])) >>
  strip_tac >> gvs[]

QED

Theorem ld_frame_external_effect[local]:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ gas_cut n vs t /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  step_inst fuel C' inst t = OK u ==>
  ?ss H'. step_inst 0 C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_ghost_ok (dyn_floor C vs) A H' (step_prov PG G inst ss) /\
    ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem
      ss.vs_memory u.vs_memory /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ u.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ u.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ u.vs_prev_bb = t.vs_prev_bb
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `s.vs_gas_readings = t.vs_gas_readings` by fs[ld_nonghost_def] >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ lo <= vs.vs_alloca_next /\
   mem_inv dload_headroom_ok C vs` by
    (fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> RETURNDATACOPY /\
   inst.inst_opcode <> REVERT` by fs[MEM] >>
  `~in_revert_forward fn s` by
    (`ALL_DISTINCT (fn_labels fn)` by simp[fn_labels_def] >>
     drule_all active_inst_block_lookup >> strip_tac >>
     gvs[in_revert_forward_def, revert_forward_at_def, revert_forward_pair_def] >>
     metis_tac[]) >>
  suspend "point"
QED

Resume ld_frame_external_effect[point]:
  drule_all ld_frame_raw_reachable >> strip_tac >>
  drule ld_raw_reachable_frontier >> strip_tac >>
  drule raw_reachable_initial_fmp >> strip_tac >>
  drule ld_sync_frontier >> strip_tac >>
  `dload_headroom_ok C fn inst s` by metis_tac[ld_sync_source_mem_inv] >>
  `lo <= dyn_floor C vs /\ t.vs_alloca_next <= dyn_floor C vs /\
   t.vs_alloca_next < dimword(:256)` by
    (simp[dyn_floor_def] >> IF_CASES_TAC >>
     gvs[dload_headroom_ok_def, ctx_has_dalloca_def] >> decide_tac) >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    metis_tac[ld_sync_slots, ld_sync_maps] >>
  `!a u v sz. FLOOKUP A a = SOME (u,v,sz) ==> lo <= u /\ lo <= v` by
    metis_tac[lowerDloadSafetyAllocBoundsTheory.ld_alloc_bounds] >>
  `!a k u v z b c sz. FLOOKUP A a = SOME (u,v,z) /\
    FLOOKUP A k = SOME (b,c,sz) /\ a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)` by
    metis_tac[lowerDloadSafetyAllocBoundsTheory.ld_alloc_separate] >>
  drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
  `!a u v sz. FLOOKUP A a = SOME (u,v,sz) ==>
    u+sz <= dyn_floor C vs /\ v+sz <= dyn_floor C vs /\ v+sz < dimword(:256)` by
    (rpt strip_tac >> drule_all lowerDloadSafetyAllocBoundsTheory.ld_alloc_frontiers >> simp[] >> decide_tac) >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs` by metis_tac[] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by metis_tac[ld_global_selected, MEM] >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  drule ld_sync_ghosts >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_dyn_agree >> strip_tac >>
  suspend "effect"
QED

Resume ld_frame_external_effect[effect]:
  `tn.t_var = f.lf_tv` by simp[] >>
  `step_inst_base inst t = OK u` by fs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  qpat_assum `f.lf_fn = fn` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
  `?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss u /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss u /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H) inst ss =
      ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE /\
    ld_dyn_agree (dyn_floor C vs) (step_taint inst f.lf_src ss tn).t_mem ss.vs_memory u.vs_memory /\
    ss.vs_allocas = f.lf_src.vs_allocas /\ u.vs_allocas = f.lf_tgt.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\ u.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\ u.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\ u.vs_prev_bb = f.lf_tgt.vs_prev_bb` by
    (Cases_on `MEM inst.inst_opcode [CALL;STATICCALL]`
     >- (`inst_wf inst` by
           (fs[fn_inst_wf_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
            metis_tac[]) >>
         (Q.SUBGOAL_THEN
           `?g a v ao az ro rz st.
             (inst.inst_opcode = CALL /\ inst.inst_operands = [g;a;v;ao;az;ro;rz] /\
               st = f.lf_tgt.vs_call_ctx.cc_static) \/
             (inst.inst_opcode = STATICCALL /\ inst.inst_operands = [g;a;ao;az;ro;rz] /\ st = T)`
           (REPEAT_TCL CHOOSE_THEN assume_tac)
          >- (qpat_x_assum `inst_wf inst` mp_tac >>
              qpat_assum `MEM inst.inst_opcode [CALL;STATICCALL]` mp_tac >>
              pure_rewrite_tac[MEM] >> strip_tac >>
              qpat_assum `inst.inst_opcode = _` (fn th =>
                simp[NoAsms, th, inst_wf_def, LENGTH_EQ_NUM_compute]) >>
              disch_tac >> metis_tac[])) >>
         drule_all ld_oracle_call_step >> strip_tac >>
         qexists_tac `ss` >> simp[ld_oracle_call_provenance]) >>
     Cases_on `inst.inst_opcode = DELEGATECALL`
     >- (drule_all ld_delegate_step >> strip_tac >>
         qexists_tac `ss` >> simp[step_prov_def, out_prov_def, ld_erase_set_prov]) >>
     `MEM inst.inst_opcode [CREATE;CREATE2]` by fs[MEM] >>
     drule_all ld_create_step >>
     disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
     qexists_tac `ss` >> simp[]) >>
  qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  (conj_tac >- (irule ld_sync_ghost_step >> metis_tac[])) >>
  qpat_assum `FDOM A = _` (once_rewrite_tac o single o GSYM) >>
  rpt strip_tac >>
  metis_tac[ld_set_prov_selected, optionTheory.NOT_NONE_SOME]
QED

Finalise ld_frame_external_effect

Theorem ld_frame_external_boundary[local]:
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  MEM inst (fn_insts fn) /\ opaque_use_ok fn /\
  fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ ~in_revert_forward fn s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM v (fn_ir_vars fn) ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core floor lo rs (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
    Ws PG PH G H tn un s t stk ds /\ step_inst fuel C' inst t = OK u ==>
  ?ss. step_inst fuel C inst s = OK ss /\
    (!v. MEM v (fn_ir_vars fn) ==>
      (lookup_var v (ss with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (u with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    dload_boundary_core floor lo rs (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
      Ws PG PH (step_prov PG G inst ss) (step_prov PH H inst u)
      (step_taint inst s ss tn) (step_taint inst t u un)
      (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (u with vs_inst_idx := SUC t.vs_inst_idx) stk ds /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\ ss.vs_call_ctx = s.vs_call_ctx /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb /\
    u.vs_inst_idx = t.vs_inst_idx /\ u.vs_allocas = t.vs_allocas
Proof
  strip_tac >>
  `inst.inst_opcode <> RETURNDATACOPY /\ inst.inst_opcode <> REVERT /\
   ~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET]` by
    (qpat_assum `MEM inst.inst_opcode _` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
  `~about_to_revert fn inst s` by simp[about_to_revert_def] >>
  `ptr_use_ok P (fn_pv P fn) inst` by fs[fn_ptr_ok_def] >>
  `!v. MEM (Var v) inst.inst_operands ==>
       v IN (set (fn_ir_vars fn) DIFF {v | retpc_var fn v}) /\ MEM v (fn_ir_vars fn)` by
    metis_tac[dload_original_nonopaque_operands,fn_ir_vars_operand] >>
  `!v. MEM (Var v) (TL inst.inst_operands) ==>
       v IN (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})` by
    metis_tac[listTheory.MEM_TL] >>
  `?ss. step_inst fuel C inst s = OK ss /\
    (!v. MEM v (fn_ir_vars fn) ==> (lookup_var v ss = NONE <=> lookup_var v u = NONE)) /\
    dload_boundary_core floor lo rs (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
      Ws PG PH (step_prov PG G inst ss) (step_prov PH H inst u)
      (step_taint inst s ss tn) (step_taint inst t u un) ss u stk ds /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\ ss.vs_call_ctx = s.vs_call_ctx /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb /\
    u.vs_inst_idx = t.vs_inst_idx /\ u.vs_allocas = t.vs_allocas` by
    (let
       fun transport boundary =
         mp_tac (Q.INST [`i` |-> `inst`, `f` |-> `fn`, `P` |-> `P`,
           `pv` |-> `fn_pv P fn`, `U` |-> `set (fn_ir_vars fn)`,
           `V` |-> `set (fn_ir_vars fn) DIFF {v | retpc_var fn v}`,
           `fl` |-> `floor`, `fs` |-> `rs`, `cs` |-> `stk`,
           `Ct` |-> `C'`, `Cs` |-> `C`, `t1` |-> `u`] boundary) >>
         simp[] >> metis_tac[]
     in
       Cases_on `inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL`
       >- transport lowerDloadPtrExternalCallTheory.dload_boundary_core_external_call >>
       Cases_on `inst.inst_opcode = DELEGATECALL`
       >- transport lowerDloadPtrDelegateTheory.dload_boundary_core_delegate >>
       `inst.inst_opcode = CREATE \/ inst.inst_opcode = CREATE2` by fs[listTheory.MEM] >>
       transport lowerDloadPtrCreateTheory.dload_boundary_core_create
     end) >>
  qexists_tac `ss` >> simp[] >>
  conj_tac >- fs[lookup_var_def] >>
  drule dload_boundary_core_index_update >> simp[]
QED

Theorem ld_frame_slots[local]:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) ==>
  lo <= dyn_floor C vs /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
    b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs) /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256))
Proof
  strip_tac >>
  `mem_inv dload_headroom_ok C vs /\ lo <= vs.vs_alloca_next` by
    fs[o1_safe_upto_def,o1_ptr_safe_upto_def,ptr_discipline_upto_def] >>
  drule ld_sync_source >> strip_tac >>
  drule_all ld_frame_raw_reachable >> strip_tac >>
  drule ld_raw_reachable_frontier >> strip_tac >>
  drule ctxLookupAgreeTheory.raw_reachable_initial_fmp >> strip_tac >>
  drule ld_sync_frontier >> strip_tac >>
  `dload_headroom_ok C fn inst s` by metis_tac[ld_sync_source_mem_inv] >>
  `lo <= dyn_floor C vs /\ t.vs_alloca_next <= dyn_floor C vs /\
   t.vs_alloca_next < dimword(:256)` by
    (simp[dyn_floor_def] >> IF_CASES_TAC >>
     gvs[dload_headroom_ok_def,ctx_has_dalloca_def] >> decide_tac) >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    metis_tac[ld_sync_slots,ld_sync_maps] >>
  drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
    b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs /\ c+sz < dimword(:256)` by
    (rpt strip_tac >> drule_all lowerDloadSafetyAllocBoundsTheory.ld_alloc_frontiers >>
     qpat_assum `f.lf_src = s` (fn hs => qpat_assum `f.lf_tgt = t` (fn ht =>
       simp[NoAsms,hs,ht,listTheory.HD])) >> decide_tac) >> metis_tac[]
QED

Theorem ld_frame_public_copy_boundary[local]:
  MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] /\
  inst.inst_outputs = [] /\ MEM inst (fn_insts fn) /\ opaque_use_ok fn /\
  fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ ~in_revert_forward fn s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM v (fn_ir_vars fn) ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core floor lo rs (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
    Ws PG PH G H tn un s t stk ds /\ step_inst fuel C' inst t = OK u ==>
  ?ss. step_inst fuel C inst s = OK ss /\
    (!v. MEM v (fn_ir_vars fn) ==>
      (lookup_var v (ss with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (u with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    dload_boundary_core floor lo rs (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
      Ws PG PH (step_prov PG G inst ss) (step_prov PH H inst u)
      (step_taint inst s ss tn) (step_taint inst t u un)
      (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (u with vs_inst_idx := SUC t.vs_inst_idx) stk ds /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\ ss.vs_call_ctx = s.vs_call_ctx /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb /\
    u.vs_inst_idx = t.vs_inst_idx /\ u.vs_allocas = t.vs_allocas
Proof
  strip_tac >>
  `~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET]` by
    (qpat_assum `MEM inst.inst_opcode _` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
  `!v. MEM (Var v) inst.inst_operands ==>
       v IN (set (fn_ir_vars fn) DIFF {v | retpc_var fn v}) /\ MEM v (fn_ir_vars fn)` by
    metis_tac[dload_original_nonopaque_operands,fn_ir_vars_operand] >>
  `?ss. step_inst fuel C inst s = OK ss /\
    (!v. MEM v (fn_ir_vars fn) ==> (lookup_var v ss = NONE <=> lookup_var v u = NONE)) /\
    dload_boundary_core floor lo rs (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
      Ws PG PH (step_prov PG G inst ss) (step_prov PH H inst u)
      (step_taint inst s ss tn) (step_taint inst t u un) ss u stk ds /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\ u.vs_current_bb = t.vs_current_bb /\
    u.vs_prev_bb = t.vs_prev_bb /\ u.vs_inst_idx = t.vs_inst_idx` by
    (mp_tac (Q.INST
      [`i` |-> `inst`, `f` |-> `fn`, `U` |-> `set (fn_ir_vars fn)`,
       `V` |-> `set (fn_ir_vars fn) DIFF {v | retpc_var fn v}`, `fl` |-> `floor`,
       `fs` |-> `rs`, `cs` |-> `stk`, `Ct` |-> `C'`, `Cs` |-> `C`,
       `t'` |-> `u`, `fuel` |-> `fuel`]
      lowerDloadPtrCopyTheory.dload_boundary_core_external_copy) >> simp[] >> metis_tac[]) >>
  `ss.vs_call_ctx = s.vs_call_ctx /\ u.vs_allocas = t.vs_allocas` by
    metis_tac[lowerDloadPtrCopyTheory.dload_external_copy_step_fields] >>
  qexists_tac `ss` >> simp[] >>
  conj_tac >- fs[lookup_var_def] >>
  drule dload_boundary_core_index_update >> simp[]
QED

Theorem ld_frame_boundary_below_fmp[local]:
  dload_boundary_core (dyn_floor C vs) lo fs V Ws PG PH G H tn un s t cs ds /\
  frame_reachable vs C cs PG G tn f i s /\ ptr_discipline_upto lo n C vs /\ gas_cut n vs s /\
  o1_ctx_shape C /\ ctx_has_dalloca C ==>
  allocas_below_fmp t
Proof
  strip_tac >>
  `allocas_below_fmp s` by
    (qpat_assum `ptr_discipline_upto lo n C vs`
       (drule_all_then strip_assume_tac o cj 3 o REWRITE_RULE[ptr_discipline_upto_def]) >>
     simp[]) >>
  `s.vs_initial_fmp = vs.vs_initial_fmp` by
    (`raw_reachable vs C f i s` by
       (irule lowerDloadPtrRawReachableTheory.frame_reachable_raw >>
        metis_tac[]) >>
     drule raw_reachable_initial_fmp >> simp[]) >>
  `t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_fmp = s.vs_fmp` by
    (drule dload_boundary_environment >>
     simp[lowerDloadPtrCallTheory.dload_equal_environment_def, venom_state_component_equality]) >>
  `t.vs_alloca_next <= w2n t.vs_initial_fmp` by
    (`t.vs_alloca_next <= dyn_floor C vs` by
       (drule dload_boundary_memory >> simp[dload_memory_match_def]) >>
     gvs[dyn_floor_def]) >>
  `dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs` by
    (drule dload_boundary_layout >> simp[]) >>
  `dload_table_stack fs (s::MAP (\c. c.cf_state) cs)
     (t::MAP (\d. d.cf_state) ds)` by
    (drule dload_boundary_tables >> simp[]) >>
  `(EL 0 fs).dr_target = t.vs_allocas` by
    (fs[dload_table_stack_def] >>
     qpat_x_assum `!k. k < LENGTH fs ==> _` (qspec_then `0` mp_tac) >>
     simp[]) >>
  simp[allocas_below_fmp_def] >> conj_tac >- fs[allocas_below_fmp_def] >>
  rpt strip_tac >>
  qpat_x_assum `dload_live_layout _ _ _ _` mp_tac >>
  simp[dload_live_layout_def] >> strip_tac >>
  qpat_x_assum `!k id b n. k < LENGTH fs /\
      FLOOKUP (EL k fs).dr_target id = SOME (b,n) ==> _`
    (qspecl_then [`0`,`aid`,`b`,`sz`] mp_tac) >>
  `0 < LENGTH fs` by gvs[dload_table_stack_def] >>
  simp[] >> strip_tac >> gvs[] >> decide_tac
QED

Theorem ld_frame_copy_terminal_fields[local]:
  o1_ctx_shape C /\ ptr_discipline_upto lo n C vs /\ gas_cut n vs s /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  i.inst_opcode = RETURNDATACOPY /\ i.inst_operands = [dst;off;sz] /\
  FDOM G SUBSET fn_pv P f /\
  dload_boundary_core fl lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v}) Ws
    PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel C i s = OK s' /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    t'.vs_allocas = t.vs_allocas /\ t'.vs_alloca_next = t.vs_alloca_next /\
    s'.vs_labels = t'.vs_labels /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    (!v. op_taint (step_taint i s s' tn) (Var v) = op_taint tn (Var v)) /\
    (!v. op_taint (step_taint i t t' un) (Var v) = op_taint un (Var v)) /\
    dload_vars_match fl fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `MEM f C.ctx_functions` by
    (drule frame_reachable_raw_certificate >> simp[] >> strip_tac >> simp[]) >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `fn_ptr_ok P f` by metis_tac[EVERY_MEM] >>
  `fn_inst_wf f /\ opaque_use_ok f` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> strip_tac >>
     first_x_assum drule >> simp[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def]) >>
  `inst_wf i` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `i.inst_outputs = []` by gvs[inst_wf_def] >>
  `taint_ok f tn i s` by
    (qpat_assum `ptr_discipline_upto lo n C vs`
       (drule_all_then strip_assume_tac o cj 3 o REWRITE_RULE[ptr_discipline_upto_def]) >>
     simp[]) >>
  irule dload_copy_boundary_terminal_fields >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ld_frame_copy_terminal_next[local]:
  o1_ctx_shape C /\ ptr_discipline_upto lo n C vs /\ gas_cut n vs s /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  i.inst_opcode = RETURNDATACOPY /\ i.inst_operands = [dst;off;sz] /\
  FDOM G SUBSET fn_pv P f /\
  dload_boundary_core fl lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v}) Ws
    PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel Ct i t = OK t' /\
  active_inst g j (t' with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?s' i' emitted'.
    step_inst fuel C i s = OK s' /\
    frame_reachable vs C cs PG (step_prov PG G i s') (step_taint i s s' tn)
      f i' (s' with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
      (t' with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
    j = HD emitted' /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    t'.vs_allocas = t.vs_allocas /\ t'.vs_alloca_next = t.vs_alloca_next /\
    s'.vs_labels = t'.vs_labels /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v (s' with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (t' with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    dload_vars_match fl fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un)
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
      (t' with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  drule_all ld_frame_copy_terminal_fields >> strip_tac >>
  `s'.vs_current_bb = s.vs_current_bb /\ s'.vs_prev_bb = s.vs_prev_bb /\
   s'.vs_inst_idx = s.vs_inst_idx` by
    (irule external_copy_control_fields >> simp[] >> metis_tac[]) >>
  `t'.vs_current_bb = t.vs_current_bb /\ t'.vs_prev_bb = t.vs_prev_bb /\
   t'.vs_inst_idx = t.vs_inst_idx` by
    (irule external_copy_control_fields >> simp[] >> metis_tac[]) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  drule_all dload_singleton_reachable_next_fields >> strip_tac >>
  qexistsl [`s'`,`i'`,`emitted'`] >>
  simp[lookup_var_def, dload_vars_match_def] >>
  gvs[dload_vars_match_def, lookup_var_def]
QED

Theorem ld_frame_terminal_copy_readings[local]:
  inst.inst_opcode = RETURNDATACOPY /\ step_inst fuel C inst s = OK t ==>
  t.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >> gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  mp_tac gasCountTheory.gas_count_base >>
  simp[gasCountTheory.gas_count_suffix_def]
QED

Theorem ld_frame_terminal_copy_below[local]:
  inst.inst_opcode = RETURNDATACOPY /\ step_inst fuel C inst t = OK t' /\
  allocas_below_fmp t ==>
  allocas_below_fmp (t' with vs_inst_idx := n)
Proof
  strip_tac >>
  gvs[venomExecSemanticsTheory.step_inst_non_invoke,
      venomExecSemanticsTheory.step_inst_base_def,AllCaseEqs(),
      allocas_below_fmp_def,write_memory_with_expansion_def] >>
  metis_tac[]
QED

Theorem ld_frame_copy_terminal_entry[local]:
  o1_ctx_shape C /\ ptr_discipline_upto lo n C vs /\ gas_cut n vs s /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\ ir_supply_covers_fn q f /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  i.inst_opcode = RETURNDATACOPY /\ i.inst_operands = [dst;off;sz] /\
  FDOM G SUBSET fn_pv P f /\
  dload_boundary_core fl lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v}) Ws
    PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  (in_revert_forward g t \/ about_to_revert g i t) /\
  step_inst fuel Ct i t = OK t' ==>
  ?s' ss tt bb tb bs bt mid.
    step_inst fuel C i s = OK s' /\
    ss = s' with vs_inst_idx := SUC s.vs_inst_idx /\
    tt = t' with vs_inst_idx := SUC t.vs_inst_idx /\
    frame_reachable vs C cs PG (step_prov PG G i s') (step_taint i s s' tn)
      f (HD mid) ss /\
    active_inst f (HD mid) ss /\ active_inst g (HD mid) tt /\
    FDOM (step_prov PG G i s') SUBSET fn_pv P f /\
    ss.vs_labels = tt.vs_labels /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v ss = NONE <=> lookup_var v tt = NONE)) /\
    dload_vars_match fl fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) ss tt /\
    dload_live_layout lo ss.vs_alloca_next tt.vs_alloca_next fs /\
    dload_table_stack fs (ss::MAP (\c. c.cf_state) cs)
                        (tt::MAP (\c. c.cf_state) ds) /\
    MEM bb f.fn_blocks /\
    lookup_block ss.vs_current_bb f.fn_blocks = SOME bb /\
    lookup_block tt.vs_current_bb g.fn_blocks = SOME tb /\
    lower_dload_block_supply bs bb = (tb,bt) /\
    set (fn_ir_vars f) SUBSET set bs.irs_used_vars /\
    (!j v. MEM j bb.bb_instructions /\ MEM (Var v) j.inst_operands ==>
       v IN set (fn_ir_vars f)) /\
    mid <> [] /\
    TAKE (LENGTH mid) (DROP ss.vs_inst_idx bb.bb_instructions) = mid /\
    TAKE (LENGTH mid) (DROP tt.vs_inst_idx tb.bb_instructions) = mid /\
    ss.vs_inst_idx + LENGTH mid <= LENGTH bb.bb_instructions /\
    tt.vs_inst_idx + LENGTH mid <= LENGTH tb.bb_instructions /\
    EVERY (\j. j.inst_opcode = ASSIGN) (FRONT mid) /\
    (LAST mid).inst_opcode = REVERT /\
    (!k. k <= LENGTH mid ==>
      ?pre u. lower_dload_insts_supply bs
        (TAKE (ss.vs_inst_idx+k) bb.bb_instructions) = (pre,u) /\
        LENGTH pre = tt.vs_inst_idx+k) /\
    (revert_forward_pair tb (tt.vs_inst_idx-1)
       (tt.vs_inst_idx+LENGTH mid-1) \/ LENGTH mid = 1)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `active_inst g i t` by
    (gvs[dload_control_match_def] >> metis_tac[]) >>
  drule_all dload_copy_exempt_terminal_slice >>
  disch_then (qx_choose_then `tb` (qx_choose_then `mid`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  `t'.vs_current_bb = t.vs_current_bb /\ t'.vs_prev_bb = t.vs_prev_bb /\
   t'.vs_inst_idx = t.vs_inst_idx` by
    (irule external_copy_control_fields >> simp[] >> metis_tac[]) >>
  `active_inst g (HD mid) (t' with vs_inst_idx := SUC t.vs_inst_idx)` by
    (`0 < LENGTH mid` by (Cases_on `mid` >> gvs[]) >>
     `EL 0 mid = EL 0 (DROP (SUC t.vs_inst_idx) tb.bb_instructions)` by
       metis_tac[EL_TAKE] >>
     irule lookup_instruction_active >> qexists `tb` >>
     gvs[get_instruction_def, EL_DROP]) >>
  drule_all ld_frame_copy_terminal_next >> strip_tac >>
  `EVERY (\j. j.inst_opcode = ASSIGN \/ j.inst_opcode = REVERT) mid` by
    (`EVERY (\j. j.inst_opcode = ASSIGN \/ j.inst_opcode = REVERT)
       (FRONT mid ++ [LAST mid])` by
       (simp[EVERY_APPEND, EVERY_MEM] >>
        qpat_x_assum `EVERY _ (FRONT mid)` mp_tac >>
        simp[EVERY_MEM] >> metis_tac[]) >>
     metis_tac[APPEND_FRONT_LAST]) >>
  drule dload_control_terminal_singleton >>
  disch_then (qspec_then `HD mid` mp_tac) >>
  (impl_tac
   >- (simp[] >>
       `MEM (HD mid) mid` by (Cases_on `mid` >> gvs[]) >>
       qpat_x_assum `EVERY _ mid` mp_tac >> simp[EVERY_MEM] >> metis_tac[])) >>
  strip_tac >>
  qabbrev_tac `ss = s' with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `tt = t' with vs_inst_idx := SUC t.vs_inst_idx` >>
  `lookup_block tt.vs_current_bb g.fn_blocks = SOME tb /\
   LENGTH mid <= LENGTH (DROP tt.vs_inst_idx tb.bb_instructions) /\
   mid = TAKE (LENGTH mid) (DROP tt.vs_inst_idx tb.bb_instructions)` by
    simp[Abbr `tt`, LENGTH_DROP] >>
  drule_all dload_control_cover_terminal_slice >> strip_tac >>
  qexistsl [`s'`,`ss`,`tt`,`bb`,`tb`,`bs`,`bt`,`mid`] >>
  qpat_x_assum `mid = TAKE _ _` kall_tac >>
  qpat_x_assum `HD mid = HD emitted'` kall_tac >>
  gnvs[Abbr `ss`, Abbr `tt`] >>
  conj_tac
  >- (qpat_x_assum `dload_control_match _ _ _ _ _ (HD emitted') _ _` mp_tac >>
      simp[dload_control_match_def] >> metis_tac[]) >>
  conj_tac
  >- (drule frame_reachable_prov_supported >>
      disch_then (qspec_then `P` mp_tac) >>
      qpat_x_assum `EVERY (fn_ptr_ok P) _` mp_tac >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (irule dload_boundary_layout >> goal_assum (drule_at Any)) >>
  conj_tac >- suspend "tables" >> metis_tac[]
QED

Resume ld_frame_copy_terminal_entry[tables]:
  drule dload_boundary_tables >>
  simp[dload_table_stack_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> simp[] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!k. _ ==> _` (qspec_then `k` mp_tac) >>
  Cases_on `k` >> simp[]
QED
Finalise ld_frame_copy_terminal_entry

Theorem ld_frame_classified_read_boundary[local]:
  MEM inst.inst_opcode [MLOAD; ILOAD; LT; GT; EQ] /\
  MEM inst (fn_insts fn) /\ opaque_use_ok fn /\
  fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ s.vs_labels = t.vs_labels /\
  (MEM inst.inst_opcode [MLOAD; ILOAD] ==> ~in_revert_forward fn s) /\
  (!v. MEM v (fn_ir_vars fn) ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core floor lo rs (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
    Ws PG PH G H tn un s t stk ds /\ step_inst fuel C' inst t = OK u ==>
  ?ss. step_inst fuel C inst s = OK ss /\
    (!v. MEM v (fn_ir_vars fn) ==> (lookup_var v ss = NONE <=> lookup_var v u = NONE)) /\
    dload_boundary_core floor lo rs (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
      Ws PG PH (step_prov PG G inst ss) (step_prov PH H inst u)
      (step_taint inst s ss tn) (step_taint inst t u un) ss u stk ds /\
    ss = s with vs_vars := ss.vs_vars /\ u = t with vs_vars := u.vs_vars
Proof
  strip_tac >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by
    (qpat_assum `MEM inst.inst_opcode [MLOAD; ILOAD; LT; GT; EQ]` mp_tac >>
     pure_rewrite_tac[MEM] >> strip_tac >> simp[]) >>
  `!v. MEM (Var v) inst.inst_operands ==>
    v IN (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})` by
    metis_tac[dload_original_nonopaque_operands] >>
  let
    fun transport th =
      drule_at (Pat `dload_boundary_core`) th >>
      disch_then (drule_at (Pat `step_inst`)) >>
      disch_then (drule_at (Pat `fn_ptr_ok`)) >>
      disch_then (qspecl_then [`set (fn_ir_vars fn)`,`C`] mp_tac) >>
      (impl_tac >- (simp[] >> metis_tac[fn_ir_vars_operand])) >>
      disch_then ACCEPT_TAC
  in
    Cases_on `MEM inst.inst_opcode [MLOAD; ILOAD]`
    >- transport lowerDloadPtrMemoryReadTheory.dload_boundary_core_mload >>
    `inst.inst_opcode = LT \/ inst.inst_opcode = GT \/ inst.inst_opcode = EQ` by
      (qpat_assum `~MEM inst.inst_opcode [MLOAD; ILOAD]` mp_tac >>
       qpat_assum `MEM inst.inst_opcode [MLOAD; ILOAD; LT; GT; EQ]` mp_tac >>
       pure_rewrite_tac[MEM] >> metis_tac[NoAsms]) >>
    transport lowerDloadPtrOrdinaryTheory.dload_boundary_core_compare
  end
QED

Theorem ld_frame_copied_ptr_rows[local]:
  o1_ctx_shape C /\ EVERY fn_shape_ok C'.ctx_functions /\ ptr_discipline_upto lo ngas C vs /\ gas_cut ngas vs s /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  frame_reachable vs C' ds PH H un g i t /\
  dload_boundary_core fl lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G H tn un s t cs ds /\
  dload_control_match q f g s t i [i] 0 /\ ir_supply_covers_fn q f /\
  (?q'. lower_dload_function_supply q f = (g,q')) /\
  i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES ==>
  access_ok lo H g i t /\ taint_ok g un i t
Proof
  strip_tac >>
  `access_ok lo G f i s /\ taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline_upto _ _ _ _` mp_tac >>
     simp[ptr_discipline_upto_def] >> metis_tac[]) >>
  `MEM f C.ctx_functions /\ FDOM G SUBSET fn_pv P f` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
       (mp_tac o MATCH_MP frame_reachable_prov_supported) >>
     disch_then (qspec_then `P` mp_tac) >>
     impl_tac >- metis_tac[EVERY_MEM] >> simp[]) >>
  `fn_ptr_ok P f` by metis_tac[EVERY_MEM] >>
  `o1_fn_shape C f` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
       fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  drule dload_boundary_vars >> strip_tac >>
  drule dload_boundary_layout >> strip_tac >>
  drule dload_boundary_environment >> strip_tac >>
  `s.vs_labels = t.vs_labels` by
    (qpat_x_assum `dload_equal_environment s t` mp_tac >>
     rewrite_tac[lowerDloadPtrCallTheory.dload_equal_environment_def] >>
     disch_then (mp_tac o AP_TERM ``\x:venom_state. x.vs_labels``) >> simp[]) >>
  conj_tac >- suspend "access" >> suspend "taint"
QED

Resume ld_frame_copied_ptr_rows[access]:
  `i.inst_opcode <> DRET` by
    (fs[o1_fn_shape_def, dretDesugarDefsTheory.no_dret_def, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `MEM i.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]`
  >- (gvs[MEM] >> simp[access_ok_def, source_memory_read_ranges_def,
        codegenRelTheory.source_memory_write_ranges_def, memLocDefsTheory.mem_read_ops_def, memLocDefsTheory.mem_write_ops_def]) >>
  `!v. MEM (Var v) i.inst_operands ==>
     v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
    (`opaque_use_ok f` by fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
     rpt strip_tac >> drule_all dload_original_nonopaque_operands >> simp[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks)` by
    fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks)` by
    (drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     fs[fn_labels_def]) >>
  `!v. v IN FDOM H ==> lookup_var v t <> NONE` by
    (qpat_assum `frame_reachable vs C' ds PH H un g i t`
       (mp_tac o MATCH_MP lowerDloadPtrDynamicSupportTheory.dload_frame_prov_defined) >> simp[]) >>
  simp[access_ok_def] >> conj_tac
  >- (strip_tac >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >> `~in_revert_forward f s` by
            metis_tac[dload_copied_forward_guard, MEM] >>
          drule_all dload_copied_write_range >> strip_tac >>
          fs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >> `~in_revert_forward f s` by
        metis_tac[dload_copied_forward_guard, MEM] >>
      drule_all dload_copied_read_range >> strip_tac >>
      fs[arithmeticTheory.ADD_COMM]) >>
  `t.vs_alloca_next <= fl` by
    (drule dload_boundary_memory >> simp[dload_memory_match_def]) >>
  rpt gen_tac >> strip_tac >> irule dload_copied_compare_access >>
  simp[] >> metis_tac[]
QED

Resume ld_frame_copied_ptr_rows[taint]:
  `EVERY fn_shape_ok C.ctx_functions` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  `!v. retpc_var f v ==> op_taint tn (Var v) = {}` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
       (mp_tac o MATCH_MP lowerDloadPtrRetpcCleanTheory.dload_frame_retpc_clean) >> simp[]) >>
  `!v. retpc_var g v ==> op_taint un (Var v) = {}` by
    (qpat_assum `frame_reachable vs C' ds PH H un g i t`
       (mp_tac o MATCH_MP lowerDloadPtrRetpcCleanTheory.dload_frame_retpc_clean) >> simp[]) >>
  `retpc_var g = retpc_var f` by
    metis_tac[o1ContractLowerDloadTheory.lower_dload_function_supply_retpc_var] >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = op_taint un op` by
    (rpt strip_tac >> Cases_on `op` >> simp[op_taint_def] >>
     rename1 `MEM (Var v) i.inst_operands` >>
     Cases_on `retpc_var f v`
     >- (fs[op_taint_def] >> metis_tac[]) >>
     `v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
       (simp[] >> metis_tac[lowerDloadPtrStaticTheory.fn_ir_vars_operand]) >>
     fs[dload_vars_match_def] >> metis_tac[]) >>
  `!b. i.inst_opcode = MUL /\ MEM b i.inst_operands /\
       op_taint tn b = {} ==> eval_operand b s = eval_operand b t` by
    (rpt strip_tac >>
     `opaque_use_ok f` by fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
     `!v. MEM (Var v) i.inst_operands ==>
        v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
       (rpt strip_tac >> irule dload_original_nonopaque_operands >>
        simp[] >> qexists `i` >> simp[MEM]) >>
     `op_prov G b = NONE` by
       (irule lowerDloadPtrScalarTheory.scalar_operand_no_prov >>
        simp[MEM] >> metis_tac[]) >>
     `eval_operand b s = NONE <=> eval_operand b t = NONE` by
       (irule dload_matched_operand_defined >> metis_tac[]) >>
     `!v. b = Var v ==>
        v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by metis_tac[] >>
     drule_all scalar_operand_equal >> simp[]) >>
  simp[taint_ok_def] >> conj_tac
  >- (rpt strip_tac >>
      `op_taint tn op <> {}` by metis_tac[] >>
      qpat_x_assum `taint_ok f tn i s` mp_tac >>
      simp[taint_ok_def] >> strip_tac >>
      first_x_assum (qspec_then `op` mp_tac) >> simp[] >>
      strip_tac >> gvs[] >> fs[MEM] >> metis_tac[]) >>
  suspend "memory"
QED

Resume ld_frame_copied_ptr_rows[memory]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks)` by
    fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks)` by
    (drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     fs[fn_labels_def]) >>
  `~about_to_revert f i s` by metis_tac[dload_copied_about_to_revert] >>
  `~in_revert_forward f s` by
    (strip_tac >>
     `i.inst_opcode = RETURNDATACOPY \/ i.inst_opcode = REVERT` by
       (qpat_x_assum `in_revert_forward f s` mp_tac >>
        qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
        simp[dload_control_match_def, active_inst_def, in_revert_forward_def,
             revert_forward_at_def] >> rpt strip_tac >>
        `lookup_block s.vs_current_bb f.fn_blocks = SOME bb` by
          (irule venomExecProofsTheory.MEM_lookup_block >> simp[]) >>
        gvs[revert_forward_pair_def, get_instruction_def]) >>
     gvs[about_to_revert_def, source_memory_read_ranges_def]) >>
  `i.inst_opcode <> DRET` by
    (fs[o1_fn_shape_def, dretDesugarDefsTheory.no_dret_def, EVERY_MEM] >> metis_tac[]) >>
  `~MEM i.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by
    (strip_tac >> gvs[MEM, source_memory_read_ranges_def]) >>
  `!v. MEM (Var v) i.inst_operands ==>
     v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
    (`opaque_use_ok f` by fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
     rpt strip_tac >> drule_all dload_original_nonopaque_operands >> simp[]) >>
  `len <> 0` by decide_tac >>
  drule_all dload_copied_read_range >> strip_tac >>
  drule dload_boundary_memory >> strip_tac >>
  `?j. a <= j /\ j < a+len /\ j IN tn.t_mem` by
    (Cases_on `a = off /\ a+len <= lo`
     >- (`i' < lo` by decide_tac >>
         `i' IN tn.t_mem` by metis_tac[dload_memory_match_def] >>
         qexists `i'` >> simp[] >> decide_tac) >>
     Cases_on `a = off /\ fl <= a /\ a + len < dimword (:256)`
     >- (`fl <= i' /\ i' < dimword (:256)` by decide_tac >>
         `i' IN tn.t_mem` by metis_tac[dload_memory_match_def] >>
         qexists `i'` >> simp[] >> decide_tac) >>
     `?owner id b c n d. dload_live_site fs owner id b c n /\
        a=b+d /\ off=c+d /\ d+len<=n` by metis_tac[] >>
     `d + (i'-off) < n` by decide_tac >>
     `i' = c + (d + (i'-off))` by decide_tac >>
     `b + (d + (i'-off)) IN tn.t_mem` by
       metis_tac[dload_memory_match_def] >>
     qexists `b + (d + (i'-off))` >> simp[] >> decide_tac) >>
  fs[taint_ok_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise ld_frame_copied_ptr_rows

Theorem ld_frame_alloca_successor_headroom[local]:
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = ALLOCA /\ step_inst fuel C inst s = OK s' /\
  active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  s'.vs_alloca_next + 32 * ctx_dload_count C < dimword (:256)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG (step_prov PG G inst s')
    (step_taint inst s s' tn) fn inst'
    (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule frame_reachable_next >>
     simp[venomInstTheory.is_terminator_def] >> metis_tac[]) >>
  `dload_headroom_ok C fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[lowerDloadPtrSourceInvTheory.mem_inv_frame_reachable] >>
  fs[dload_headroom_ok_def]
QED

Theorem ld_frame_alloca_fresh_post_bound[local]:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  FLOOKUP t.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s amount = OK s' /\ exec_alloca inst t amount = OK t' /\
  dload_table_stack (f::fs) (s::ss) (t::ts) /\
  SUM (MAP (\f. CARD f.dr_scratch) (f::fs)) <= ctx_dload_count C /\
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = ALLOCA /\ step_inst fuel C inst s = OK s' /\
  active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  t'.vs_alloca_next < dimword (:256) /\
  t.vs_alloca_next + w2n amount < dimword (:256) /\
  t'.vs_alloca_next <= dyn_floor C vs
Proof
  strip_tac >> drule_all ld_frame_alloca_successor_headroom >> strip_tac >>
  `frame_reachable vs C stk PG (step_prov PG G inst s')
    (step_taint inst s s' tn) fn inst'
    (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule frame_reachable_next >>
     simp[venomInstTheory.is_terminator_def] >> metis_tac[]) >>
  `dload_headroom_ok C fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[lowerDloadPtrSourceInvTheory.mem_inv_frame_reachable] >>
  `raw_reachable vs C fn inst s` by
    (irule lowerDloadPtrRawReachableTheory.frame_reachable_raw >>
     metis_tac[]) >>
  drule raw_reachable_initial_fmp >> strip_tac >>
  drule dload_table_stack_current >> strip_tac >>
  qpat_x_assum `exec_alloca inst s amount = OK s'` mp_tac >>
  qpat_x_assum `exec_alloca inst t amount = OK t'` mp_tac >>
  simp[exec_alloca_def, update_var_def] >> rpt strip_tac >> gvs[] >>
  gvs[dload_headroom_ok_def, dyn_floor_def, ctx_has_dalloca_def] >>
  rw[] >> gvs[] >> decide_tac
QED

Theorem ld_frame_alloca_next[local]:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  i.inst_opcode = ALLOCA /\ step_inst fuel C' i t = OK t1 /\
  active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
  dload_table_stack (r::rs) (s::ss) (t::ts) /\ dload_frame_sites r /\
  dload_live_layout lo s.vs_alloca_next t.vs_alloca_next (r::rs) /\
  dload_memory_match (dyn_floor C vs) lo (r::rs) tn un s t /\
  r.dr_scratch = FDOM t.vs_allocas DIFF {ci.inst_id | MEM ci (fn_insts f)} /\
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs /\
  SUM (MAP (\r. CARD r.dr_scratch) (r::rs)) <= ctx_dload_count C ==>
  ?s1 r1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
    j = HD emitted' /\
    dload_table_stack (r1::rs) (s1::ss) (t1::ts) /\ dload_frame_sites r1 /\
    r1.dr_scratch = r.dr_scratch /\
    r1.dr_scratch = FDOM t1.vs_allocas DIFF {ci.inst_id | MEM ci (fn_insts f)} /\
    dload_memory_match (dyn_floor C vs) lo (r1::rs)
      (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 /\
    t1.vs_alloca_next < dimword (:256)
Proof
  strip_tac >>
  `MEM i (fn_insts f) /\ active_inst f i s` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `i.inst_id NOTIN r.dr_scratch` by (simp[] >> metis_tac[]) >>
  drule_all lowerDloadPtrJointAllocTheory.dload_alloca_step_shape >> strip_tac >>
  `?s1. step_inst fuel C i s = OK s1 /\ exec_alloca i s amount = OK s1 /\
    s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
    s1.vs_inst_idx = s.vs_inst_idx` by
    (irule lowerDloadPtrJointAllocTheory.dload_alloca_step_fields >> simp[]) >>
  `t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
    t1.vs_inst_idx = t.vs_inst_idx` by
    (gvs[exec_alloca_def, update_var_def, AllCaseEqs()]) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  drule_all dload_singleton_reachable_next_fields >> strip_tac >>
  `active_inst f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ i' _ _` mp_tac >>
     simp[dload_control_match_def] >> metis_tac[]) >>
  drule_all ld_frame_alloca_successor_headroom >> strip_tac >>
  `r.dr_source = s.vs_allocas /\ r.dr_target = t.vs_allocas` by
    fs[dload_table_stack_cons] >>
  Cases_on `FLOOKUP s.vs_allocas i.inst_id`
  >- ( `FLOOKUP t.vs_allocas i.inst_id = NONE` by
         (qpat_assum `dload_frame_sites r`
            (strip_assume_tac o REWRITE_RULE [dload_frame_sites_def]) >>
          qpat_x_assum `FDOM r.dr_target = _`
            (mp_tac o Q.AP_TERM `\ids. i.inst_id IN ids`) >>
          qpat_assum `r.dr_source = s.vs_allocas` mp_tac >>
          qpat_assum `r.dr_target = t.vs_allocas` mp_tac >>
          qpat_assum `FLOOKUP s.vs_allocas i.inst_id = NONE` mp_tac >>
          qpat_assum `i.inst_id NOTIN r.dr_scratch` mp_tac >>
          POP_ASSUM_LIST (K ALL_TAC) >>
          simp[flookup_thm, IN_UNION]) >>
       `t1.vs_alloca_next <= dyn_floor C vs` by
         (drule_all ld_frame_alloca_fresh_post_bound >> simp[]) >>
       qexistsl [`s1`,`r with <|dr_source := r.dr_source |+
         (i.inst_id,(s.vs_alloca_next,w2n amount));
         dr_target := r.dr_target |+ (i.inst_id,(t.vs_alloca_next,w2n amount))|>`,
         `i'`,`emitted'`] >> simp[] >>
       conj_tac
       >- (drule_all (SRULE [] (Q.INST [`j` |-> `i`] dload_table_original_fresh)) >> simp[]) >>
       conj_tac
       >- (drule_all dload_frame_original_insert >> simp[]) >>
       conj_tac
       >- (`t1.vs_allocas = t.vs_allocas |+
              (i.inst_id,(t.vs_alloca_next,w2n amount))` by
             (gvs[exec_alloca_def, update_var_def]) >>
           simp[EXTENSION] >> metis_tac[]) >>
       conj_tac
       >- (drule_all dload_alloca_fresh_memory >> simp[]) >>
       drule_all ld_frame_alloca_fresh_post_bound >> simp[]) >>
  PairCases_on `x` >>
  `?c. FLOOKUP t.vs_allocas i.inst_id = SOME (c,x1)` by
    (fs[dload_frame_sites_def] >> metis_tac[]) >>
  qexistsl [`s1`,`r`,`i'`,`emitted'`] >> simp[] >>
  conj_tac
  >- (drule_all (Q.INST [`j` |-> `i`] dload_table_original_repeated) >> simp[]) >>
  conj_tac
  >- (gvs[exec_alloca_def, update_var_def]) >>
  conj_tac
  >- (drule_all dload_alloca_repeated_memory >> simp[]) >>
  gvs[exec_alloca_def, update_var_def, dload_live_layout_def]
QED

Theorem ld_frame_alloca_boundary_next[local]:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  i.inst_opcode = ALLOCA /\ step_inst fuel C' i t = OK t1 /\
  active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
  dload_boundary_core (dyn_floor C vs) lo (r::rs) V Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF {ci.inst_id | MEM ci (fn_insts f)} /\
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs /\
  SUM (MAP (\r. CARD r.dr_scratch) (r::rs)) <= ctx_dload_count C ==>
  ?s1 r1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
    j = HD emitted' /\
    dload_boundary_core (dyn_floor C vs) lo (r1::rs) V Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un)
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    r1.dr_scratch = r.dr_scratch /\
    r1.dr_scratch = FDOM t1.vs_allocas DIFF {ci.inst_id | MEM ci (fn_insts f)} /\
    t1.vs_alloca_next < dimword (:256)
Proof
  strip_tac >>
  drule dload_boundary_tables >> strip_tac >>
  drule dload_boundary_layout >> strip_tac >>
  drule dload_boundary_memory >> strip_tac >>
  `dload_frame_sites r` by fs[dload_live_layout_def] >>
  drule_all ld_frame_alloca_next >> strip_tac >>
  `t1.vs_alloca_next <= dyn_floor C vs` by
    (qpat_x_assum `dload_memory_match _ _ (r1::rs) _ _ s1 t1`
       (strip_assume_tac o REWRITE_RULE [dload_memory_match_def]) >>
     simp[]) >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ s t _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `i.inst_id NOTIN r.dr_scratch` by (simp[] >> metis_tac[]) >>
  drule_all lowerDloadPtrJointAllocTheory.dload_alloca_step_shape >> strip_tac >>
  `exec_alloca i s amount = OK s1` by
    (qpat_x_assum `step_inst fuel C i s = OK s1` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  `exec_alloca i t amount = OK t1` by
    (qpat_x_assum `step_inst fuel C' i t = OK t1` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  drule_all dload_boundary_core_alloca >>
  disch_then (qx_choose_then `r2` strip_assume_tac) >>
  `r2.dr_scratch = r.dr_scratch` by
    (qpat_x_assum `r2 = _` SUBST1_TAC >>
     Cases_on `FLOOKUP s.vs_allocas i.inst_id = NONE` >> simp[]) >>
  qexistsl [`s1`,`r2`,`i'`,`emitted'`] >> simp[] >>
  conj_tac
  >- (irule dload_boundary_core_index_update >> metis_tac[]) >>
  metis_tac[]
QED

val ld_frame_dload_later_header = ``
  o1_ctx_shape C /\ o1_run_state_ok vs /\ mem_inv dload_headroom_ok C vs /\
  gas_cut ngas vs s /\ callee_first names C.ctx_functions /\ ptr_discipline_upto lo ngas C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  frame_reachable vs C' ds PH H un g j t /\
  dload_boundary_core fl lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G H0 tn un0 s t0 cs ds /\
  dload_control_match q f g s t0 i emitted 0 /\
  dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un /\
  FDOM G SUBSET fn_pv P f /\
  LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
  (!k. k < LENGTH fs ==>
    (EL k fs).dr_scratch =
      FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                 ci.inst_id = id}) /\
  ir_supply_covers_fn q f /\
  (?q'. lower_dload_function_supply q f = (g,q')) /\
  (!k. k < LENGTH cs ==>
    ?qc qc'. lower_dload_function_supply qc (EL k cs).cf_fn =
      ((EL k ds).cf_fn,qc')) /\
  i.inst_opcode = DLOAD /\ 2 <= n /\ n < 4 ==>
  access_ok lo H g (EL n emitted) t /\ taint_ok g un (EL n emitted) t``;

val static_run = ``\s. o1_initial_state_ok s /\
  s.vs_fmp = s.vs_initial_fmp /\ code_layout_valid s``;

Theorem ld_frame_dload_later_rows[local]:
  ^(rhs (concl (DEPTH_CONV BETA_CONV
    (subst [``o1_run_state_ok`` |-> static_run] ld_frame_dload_later_header))))
Proof
  strip_tac >>
  Cases_on `fs` >- gvs[] >> rename1 `LENGTH (r::rs) = _` >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match q f g s t0 i emitted 0` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
       fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `MEM f C.ctx_functions` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
       (mp_then Any mp_tac frame_reachable_raw_certificate) >>
     simp[] >> strip_tac >> simp[]) >>
  `o1_fn_shape C f /\ fn_ptr_ok P f` by
    fs[o1_ctx_shape_def, EVERY_MEM] >>
  `?off out. i.inst_operands = [off] /\ i.inst_outputs = [out]` by
    suspend "shape" >>
  `!v. off = Var v ==> v IN set (fn_ir_vars f) /\ ~retpc_var f v` by
    suspend "operand" >>
  drule_all dload_control_supply_origins >> strip_tac >>
  `off <> Var av` by metis_tac[] >>
  `op_taint un0 off = {}` by suspend "clean" >>
  `?x. eval_operand off t0 = SOME x` by suspend "defined" >>
  `(FLOOKUP t0.vs_allocas (EL 0 emitted).inst_id = NONE ==>
    t0.vs_alloca_next + 32 < dimword (:256))` by suspend "reserve" >>
  `!bb sz. FLOOKUP t0.vs_allocas (EL 0 emitted).inst_id = SOME (bb,sz) ==>
    sz = 32 /\ bb + 32 < dimword (:256)` by suspend "cached" >>
  irule dload_supply_prefix_safety >> simp[] >>
  goal_assum (drule_at (Pat `dload_prefix_match`)) >>
  goal_assum (drule_at (Pat `lower_dload_inst_supply`)) >>
  qexistsl_tac [`off`,`out`,`x`] >>
  rpt conj_tac >> first_assum (MATCH_ACCEPT_TAC o SIMP_RULE (srw_ss()) [])
QED

Resume ld_frame_dload_later_rows[shape]:
  rpt strip_tac >>
  `fn_inst_wf f` by fs[o1_fn_shape_def] >>
  `inst_wf i` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  gvs[inst_wf_def] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  Cases_on `i.inst_outputs` >> gvs[]
QED

Resume ld_frame_dload_later_rows[operand]:
  rpt strip_tac
  >- (irule fn_ir_vars_operand >> qexists `i` >> simp[]) >>
  `MEM (Var v) i.inst_operands` by simp[] >>
  `opaque_use_ok f` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  drule_all opaque_use_ok_retpc_use >>
  gvs[retpc_use_ok_def, MEM]
QED

Resume ld_frame_dload_later_rows[cached]:
  rpt strip_tac >>
  `(EL 0 emitted).inst_id IN r.dr_scratch` by
    (qpat_x_assum `!k. k < LENGTH (r::rs) ==> _` (qspec_then `0` mp_tac) >>
     simp[] >> strip_tac >> simp[] >>
     fs[FLOOKUP_DEF]) >>
  drule_all lowerDloadPtrJointSafetyTheory.dload_boundary_cached_scratch_bounds >> simp[]
QED

Resume ld_frame_dload_later_rows[clean]:
  rpt strip_tac >>
  `taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline_upto lo ngas C vs` mp_tac >>
     simp[ptr_discipline_upto_def] >> strip_tac >>
     first_x_assum (drule_at (Pat `frame_reachable`)) >> simp[]) >>
  drule_all dload_offset_clean >> strip_tac >>
  drule dload_boundary_vars >> strip_tac >>
  Cases_on `off` >> gvs[op_taint_def] >>
  fs[dload_vars_match_def] >> metis_tac[]
QED

Resume ld_frame_dload_later_rows[reserve]:
  rpt strip_tac >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `dload_headroom_ok C f i s` by suspend "headroom" >>
  `dload_table_stack (r::rs) (s::MAP (\c. c.cf_state) cs)
    (t0::MAP (\d. d.cf_state) ds)` by
    (drule dload_boundary_tables >> simp[]) >>
  irule (cj 1 dload_positive_prefix_fresh_reserve) >>
  qpat_assum `frame_reachable vs C cs PG G tn f i s`
    (irule_at (Pat `frame_reachable`)) >>
  qpat_assum `frame_reachable vs C' ds PH H un g j t`
    (irule_at (Pat `frame_reachable`)) >>
  qpat_assum `dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un`
    (irule_at (Pat `dload_prefix_match`)) >>
  qpat_assum `lower_dload_inst_supply supply i = (emitted,after)`
    (irule_at (Pat `lower_dload_inst_supply`)) >>
  qpat_assum `dload_table_stack (r::rs) _ _`
    (irule_at (Pat `dload_table_stack`)) >>
  qpat_assum `callee_first names C.ctx_functions`
    (irule_at (Pat `callee_first`)) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[EXTENSION] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `k`
  >- (simp[] >> metis_tac[]) >>
  fs[EL_MAP] >> metis_tac[]
QED

Resume ld_frame_dload_later_rows[headroom]:
  rpt strip_tac >>
  metis_tac[lowerDloadPtrSourceInvTheory.mem_inv_frame_reachable]
QED

Resume ld_frame_dload_later_rows[defined]:
  rpt strip_tac >>
  drule_all dload_supply_expansion >> strip_tac >> gvs[] >>
  `n = SUC (SUC 0) \/ n = SUC (SUC (SUC 0))` by decide_tac >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_asm_rewrite_tac [dload_prefix_match_def, EL, HD, TL, LENGTH] >>
  rpt strip_tac >> gvs[] >>
  irule dload_replay_offset_defined >>
  goal_assum (drule_at (Pat `step_inst`)) >>
  goal_assum (drule_at (Pat `step_inst`)) >> simp[] >> metis_tac[]
QED

Finalise ld_frame_dload_later_rows


Theorem ld_frame_dloadbytes_rows[local]:
  o1_ctx_shape C /\ access_ok lo G f i s /\ taint_ok f tn i s /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_boundary_core fl lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G H0 tn un0 s t0 cs ds /\
  dload_control_match q f g s t0 i emitted 0 /\
  dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un /\
  FDOM G SUBSET fn_pv P f /\ ir_supply_covers_fn q f /\
  i.inst_opcode = DLOADBYTES /\ n < LENGTH emitted ==>
  access_ok lo H g (EL n emitted) t /\ taint_ok g un (EL n emitted) t
Proof
  strip_tac >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `MEM f C.ctx_functions` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
      (mp_then Any mp_tac frame_reachable_raw_certificate) >>
     simp[] >> strip_tac >> simp[]) >>
  `o1_fn_shape C f /\ fn_ptr_ok P f` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `?dst off sz. i.inst_operands = [dst;off;sz] /\ i.inst_outputs = []` by
    suspend "shape" >>
  `!v. MEM (Var v) i.inst_operands ==>
    v IN set (fn_ir_vars f) DIFF {v | retpc_var f v}` by suspend "operands" >>
  `?supply after cv supply1.
    lower_dload_inst_supply supply i = (emitted,after) /\
    fresh_ir_var supply = (cv,supply1) /\ cv NOTIN set (fn_ir_vars f)` by
    suspend "supply" >>
  `~in_revert_forward f s` by suspend "forward" >>
  suspend "phases"
QED

Resume ld_frame_dloadbytes_rows[shape]:
  rpt strip_tac >>
  `fn_inst_wf f` by fs[o1_fn_shape_def] >>
  `inst_wf i` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  gvs[inst_wf_def] >>
  Cases_on `i.inst_operands` >> gvs[] >> rename1 `SUC (LENGTH rest) = 3` >>
  Cases_on `rest` >> gvs[] >> rename1 `SUC (SUC (LENGTH tail)) = 3` >>
  Cases_on `tail` >> gvs[] >>
  rename1 `SUC (SUC (SUC (LENGTH last))) = 3` >>
  Cases_on `last` >> gvs[]
QED

Resume ld_frame_dloadbytes_rows[operands]:
  rpt strip_tac >> simp[] >> conj_tac
  >- (irule fn_ir_vars_operand >> qexists `i` >> simp[]) >>
  `opaque_use_ok f` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  strip_tac >> drule_all opaque_use_ok_retpc_use >>
  gvs[retpc_use_ok_def, MEM]
QED

Resume ld_frame_dloadbytes_rows[supply]:
  rpt strip_tac >>
  qpat_x_assum `dload_control_match q f g s t0 i emitted 0` mp_tac >>
  pure_rewrite_tac[dload_control_match_def] >> strip_tac >>
  Cases_on `fresh_ir_var is` >> rename1 `fresh_ir_var is = (cv1,supply2)` >>
  qexistsl [`is`,`after`,`cv1`,`supply2`] >> simp[] >>
  Cases_on `lower_dload_blocks_supply q (TAKE bi f.fn_blocks)` >>
  drule lower_dload_blocks_supply_reserved_operand >> strip_tac >>
  drule lower_dload_insts_supply_reserved_operand >> strip_tac >>
  drule fresh_ir_var_contract >> strip_tac >>
  fs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
     venomFnScheduleRunnerTheory.list_subset_def, EVERY_MEM] >> metis_tac[]
QED

Resume ld_frame_dloadbytes_rows[forward]:
  rpt strip_tac >>
  `active_inst f i s` by fs[dload_control_match_def] >>
  `ALL_DISTINCT (fn_labels f)` by
    fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def] >>
  qpat_assum `active_inst f i s`
    (mp_then (Pat `active_inst`) mp_tac
      concretizeLayoutLocalReturnTheory.active_inst_not_revert_forward) >>
  simp[]
QED

Resume ld_frame_dloadbytes_rows[phases]:
  `dload_vars_match fl fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    G H0 tn un0 s t0` by metis_tac[dload_boundary_vars] >>
  `s.vs_labels = t0.vs_labels` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `op_taint un0 off = {}` by
    (drule_all lowerDloadPtrBytesTransportTheory.dloadbytes_scalar_clean >> strip_tac >>
     Cases_on `off` >> gvs[op_taint_def] >>
     fs[dload_vars_match_def] >> metis_tac[]) >>
  Cases_on `n = 0`
  >- (gvs[] >> irule (SIMP_RULE (srw_ss()) [] dloadbytes_supply_zero_safety) >>
      goal_assum (drule_at (Pat `dload_prefix_match`)) >>
      goal_assum (drule_at (Pat `lower_dload_inst_supply`)) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
  simp[lower_dload_inst_supply_def] >>
  Cases_on `fresh_inst_id supply1` >> simp[] >>
  rename1 `fresh_inst_id supply1 = (aid,supply2)` >>
  Cases_on `fresh_inst_id supply2` >> simp[] >>
  strip_tac >> gvs[] >>
  `n = SUC 0` by decide_tac >> gvs[] >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  `1 = SUC 0` by simp[] >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp[dload_prefix_match_def] >> disch_then strip_assume_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `step_inst pfuel C' a t0` >>
  qmatch_goalsub_abbrev_tac `access_ok lo _ g c _` >>
  `step_inst_base a t0 = OK v` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke, Abbr `a`]) >>
  `dload_boundary_core fl lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G (step_prov PH H0 a v) tn (step_taint a t0 v un0) s v cs ds` by
    (irule dload_boundary_core_add_temporary >> simp[Abbr `a`] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `access_ok lo H1 g c t1` >>
  qmatch_goalsub_abbrev_tac `taint_ok g un1 c t1` >>
  `dload_boundary_core fl lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G H1 tn un1 s t1 cs ds` by
    (qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ s v _ _`
      (mp_then Any mp_tac dload_boundary_core_index_update) >>
     disch_then (qspecl_then [`SUC t0.vs_inst_idx`,`s.vs_inst_idx`] mp_tac) >>
     simp[Abbr `H1`, Abbr `un1`, Abbr `t1`]) >>
  `op_taint un1 (Var cv) = {}` by suspend "temporary_clean" >>
  `eval_operand off s <> NONE` by suspend "offset_defined" >>
  drule dload_boundary_vars >> strip_tac >>
  drule dload_boundary_layout >> strip_tac >>
  `s.vs_labels = t1.vs_labels` by
    (qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ s t1 _ _`
      (mp_then Any mp_tac dload_boundary_environment) >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  irule lowerDloadPtrBytesTransportTheory.dloadbytes_codecopy_safety >>
  simp[Abbr `c`] >>
  goal_assum (drule_at (Pat `dload_vars_match`)) >>
  goal_assum (drule_at (Pat `dload_live_layout`)) >>
  qexistsl [`P`,`f`,`i`,`off`] >>
  simp[] >> metis_tac[]
QED

Resume ld_frame_dloadbytes_rows[temporary_clean]:
  simp[Abbr `un1`, Abbr `a`, op_taint_def, step_taint_def,
       out_taint_def, mem_taint_def, imm_taint_def, adopt_reset_def,
       set_var_taint_def, FLOOKUP_UPDATE] >>
  Cases_on `eval_operand off t0` >> simp[]
QED

Resume ld_frame_dloadbytes_rows[offset_defined]:
  `eval_operand off t0 <> NONE` by
    (qpat_x_assum `step_inst_base a t0 = OK v` mp_tac >>
     simp[Abbr `a`, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
     metis_tac[optionTheory.NOT_SOME_NONE]) >>
  `!v. off = Var v ==> v IN set (fn_ir_vars f) DIFF {v | retpc_var f v}` by
    (gvs[] >> metis_tac[]) >>
  drule_at (Pat `dload_vars_match`) dload_matched_operand_defined >>
  simp[] >> metis_tac[]
QED

Finalise ld_frame_dloadbytes_rows

val frame_projection_witness = ``\ds PH H un g j t.
  ?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core (dyn_floor C vs) lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG PH G H0 tn un0 s t0 cs ds /\
    dload_control_match q f g s t0 i emitted 0 /\
    dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un /\
    dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
    s.vs_gas_readings = t.vs_gas_readings /\
    FDOM G SUBSET fn_pv P f /\
    (!k b sz. k < LENGTH PG /\ EL k PG = SOME (b,sz) ==> k IN P f.fn_name) /\
    (!c. MEM c cs ==> FDOM c.cf_prov SUBSET fn_pv P c.cf_fn) /\
    (!c k b sz. MEM c cs /\ k < LENGTH c.cf_params /\
      EL k c.cf_params = SOME (b,sz) ==> k IN P c.cf_fn.fn_name) /\
    LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
    (!k. k < LENGTH fs ==>
      (EL k fs).dr_scratch =
        FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
        {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                   ci.inst_id = id}) /\
    ir_supply_covers_fn q f /\
    (?q'. lower_dload_function_supply q f = (g,q')) /\
    (!k. k < LENGTH cs ==>
      let c = EL k cs; d = EL k ds in
      dload_live_layout lo c.cf_state.vs_alloca_next d.cf_state.vs_alloca_next
        (DROP (SUC k) fs) /\
      dload_equal_environment c.cf_state d.cf_state /\
      c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
      c.cf_inst = d.cf_inst /\
      (!a. a IN set (fn_ir_vars c.cf_fn) ==>
        (lookup_var a c.cf_state = NONE <=> lookup_var a d.cf_state = NONE)) /\
      (?qc. ir_supply_covers_fn qc c.cf_fn /\
        (?qc'. lower_dload_function_supply qc c.cf_fn = (d.cf_fn,qc')) /\
        dload_control_match qc c.cf_fn d.cf_fn c.cf_state d.cf_state
          c.cf_inst [c.cf_inst] 0))``;

val ld_frame_normal_rows_header = ``
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  o1_ctx_shape C /\ EVERY fn_shape_ok C'.ctx_functions /\ o1_run_state_ok vs /\
  mem_inv dload_headroom_ok C vs /\ callee_first names C.ctx_functions /\
  ptr_discipline_upto lo ngas C vs /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C' ds PH H un g j t /\
  gas_cut ngas vs t /\ (^frame_projection_witness) ds PH H un g j t ==>
  access_ok lo H g j t /\ taint_ok g un j t /\ allocas_from lo t /\
  (ctx_has_dalloca C' ==> allocas_below_fmp t)``;

Theorem ld_frame_normal_ptr_rows[local]:
  ^(rhs (concl (DEPTH_CONV (REWR_CONV LET_THM THENC BETA_CONV)
    (subst [``o1_run_state_ok`` |-> static_run] ld_frame_normal_rows_header))))
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >> gvs[] >>
  `gas_cut ngas vs s` by fs[gas_cut_def] >>
  qpat_assum `dload_control_match q f g s t i emitted n`
    (mp_then Any strip_assume_tac dload_control_match_expansion) >>
  `(ctx_has_dalloca C' ==> allocas_below_fmp t)` by suspend "below_fmp" >>
  `allocas_from lo t` by suspend "allocations" >>
  `access_ok lo H g (EL n emitted) t /\ taint_ok g un (EL n emitted) t`
    suffices_by metis_tac[] >>
  Cases_on `i.inst_opcode = DLOAD` >- suspend "dload" >>
  Cases_on `i.inst_opcode = DLOADBYTES` >- suspend "bytes" >>
  suspend "copied"
QED

Resume ld_frame_normal_ptr_rows[below_fmp]:
  strip_tac >>
  `ctx_has_dalloca C` by metis_tac[lower_dload_stage_no_dalloca] >>
  `allocas_below_fmp s` by
    (qpat_x_assum `ptr_discipline_upto lo ngas C vs` mp_tac >>
     simp[ptr_discipline_upto_def] >> strip_tac >>
     first_x_assum (drule_at (Pat `frame_reachable`)) >> simp[]) >>
  `s.vs_initial_fmp = vs.vs_initial_fmp` by
    (`raw_reachable vs C f i s` by
       (irule lowerDloadPtrRawReachableTheory.frame_reachable_raw >>
        metis_tac[]) >>
     drule raw_reachable_initial_fmp >> simp[]) >>
  `t0.vs_initial_fmp = s.vs_initial_fmp /\ t0.vs_fmp = s.vs_fmp` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `t0.vs_alloca_next <= w2n t0.vs_initial_fmp` by
    (`t0.vs_alloca_next <= dyn_floor C vs` by
       (drule dload_boundary_memory >> simp[dload_memory_match_def]) >>
     gvs[dyn_floor_def]) >>
  `allocas_below_fmp t0` by
    (`dload_live_layout lo s.vs_alloca_next t0.vs_alloca_next fs` by
    (drule dload_boundary_layout >> simp[]) >>
  `dload_table_stack fs (s::MAP (\c. c.cf_state) cs)
     (t0::MAP (\d. d.cf_state) ds)` by
    (drule dload_boundary_tables >> simp[]) >>
  `(EL 0 fs).dr_target = t0.vs_allocas` by
    (fs[dload_table_stack_def] >>
     qpat_x_assum `!k. k < LENGTH fs ==> _` (qspec_then `0` mp_tac) >>
     simp[]) >>
  simp[allocas_below_fmp_def] >> conj_tac >- fs[allocas_below_fmp_def] >>
  rpt strip_tac >>
  qpat_x_assum `dload_live_layout _ _ _ _` mp_tac >>
  simp[dload_live_layout_def] >> strip_tac >>
  qpat_x_assum `!k id b n. k < SUC (LENGTH ds) /\
      FLOOKUP (EL k fs).dr_target id = SOME (b,n) ==> _`
    (qspecl_then [`0`,`aid`,`b`,`sz`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >> decide_tac) >>
  Cases_on `n = 0` >- gvs[dload_prefix_match_def] >>
  `FLOOKUP t0.vs_allocas (EL 0 emitted).inst_id = NONE /\
   i.inst_opcode = DLOAD ==>
   t0.vs_alloca_next + 32 <= w2n t0.vs_initial_fmp` by
    suspend "scratch_reserve" >>
  `i.inst_opcode = DLOAD \/ i.inst_opcode = DLOADBYTES` by
    (qpat_assum `dload_control_match q f g s t i emitted n`
       (mp_then Any mp_tac dload_control_match_phase) >>
     simp[] >> metis_tac[]) >>
  `allocas_below_fmp t0 /\
   (!k. k < n ==> MEM (EL k emitted).inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD]) /\
   (!k. k < n /\ (EL k emitted).inst_opcode = ALLOCA ==>
      k = 0 /\ (EL 0 emitted).inst_operands = [Lit 32w] /\
      (FLOOKUP t0.vs_allocas (EL 0 emitted).inst_id = NONE ==>
         t0.vs_alloca_next + 32 <= w2n t0.vs_initial_fmp))` by
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (rpt strip_tac >> `SUC k < LENGTH emitted` by decide_tac >>
         drule_all dload_supply_interior_shape >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
     simp[lower_dload_inst_supply_def] >>
     Cases_on `i.inst_opcode = DLOAD` >> simp[]
     >- (simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
         `k = 0 \/ k = 1 \/ k = 2 \/ k = 3` by decide_tac >> gvs[]) >>
     Cases_on `i.inst_opcode = DLOADBYTES` >> simp[]
     >- (simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
         `k = 0 \/ k = 1` by decide_tac >> gvs[]) >>
     strip_tac >> gvs[]) >>
  qpat_assum `dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un`
    (mp_then (Pat `dload_prefix_match`) mp_tac lowerDloadPtrJointSafetyTheory.dload_prefix_allocas_below_fmp) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!k. k < n /\ _ ==> k = 0 /\ _` drule_all >>
  strip_tac >> gvs[listTheory.EL]
QED

Resume ld_frame_normal_ptr_rows[scratch_reserve]:
  strip_tac >>
  `t0.vs_alloca_next + 32 <= w2n s.vs_initial_fmp` suffices_by simp[] >>
  Cases_on `fs` >- gvs[] >> rename1 `LENGTH (r::rs) = _` >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match q f g s t0 i emitted 0` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
       fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `MEM f C.ctx_functions` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
       (mp_then Any mp_tac frame_reachable_raw_certificate) >>
     simp[] >> strip_tac >> simp[]) >>
  `o1_fn_shape C f` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `?off out. i.inst_operands = [off] /\ i.inst_outputs = [out]` by
    (`fn_inst_wf f` by fs[o1_fn_shape_def] >>
     `inst_wf i` by
       (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >>
        metis_tac[]) >>
     gvs[inst_wf_def] >>
     Cases_on `i.inst_operands` >> gvs[] >>
     Cases_on `i.inst_outputs` >> gvs[]) >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `dload_headroom_ok C f i s` by
    metis_tac[lowerDloadPtrSourceInvTheory.mem_inv_frame_reachable] >>
  `dload_table_stack (r::rs) (s::MAP (\c. c.cf_state) cs)
    (t0::MAP (\d. d.cf_state) ds)` by
    (drule dload_boundary_tables >> simp[]) >>
  `0 < n /\ n <= 4` by
    (qpat_assum `dload_control_match q f g s t i emitted n`
       (mp_then Any mp_tac dload_control_match_phase) >>
     simp[]) >>
  `(EL 0 emitted).inst_id NOTIN {ci.inst_id | MEM ci (fn_insts f)}` by
    (drule_all dload_control_supply_origins >>
     disch_then (qx_choosel_then [`sp`,`af`,`av`,`cv`] strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  irule (cj 2 dload_positive_prefix_fresh_reserve) >>
  qpat_assum `frame_reachable vs C cs PG G tn f i s`
    (irule_at (Pat `frame_reachable`)) >>
  qpat_assum `frame_reachable vs C' ds PH H un g _ t`
    (irule_at (Pat `frame_reachable`)) >>
  qpat_assum `dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un`
    (irule_at (Pat `dload_prefix_match`)) >>
  qpat_assum `lower_dload_inst_supply _ i = (emitted,_)`
    (irule_at (Pat `lower_dload_inst_supply`)) >>
  qpat_assum `dload_table_stack (r::rs) _ _`
    (irule_at (Pat `dload_table_stack`)) >>
  qpat_assum `callee_first names C.ctx_functions`
    (irule_at (Pat `callee_first`)) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[EXTENSION] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `k`
  >- (simp[] >> metis_tac[]) >>
  fs[] >>
  qpat_x_assum `!k. k < LENGTH ds ==> dload_live_layout _ _ _ _ /\ _` (qspec_then `n'` mp_tac) >>
  `n' < LENGTH cs` by decide_tac >>
  pop_assum (fn th => simp[EL_MAP, th]) >> metis_tac[]
QED

Resume ld_frame_normal_ptr_rows[allocations]:
  irule dload_supply_prefix_allocas_from >>
  goal_assum (drule_at (Pat `dload_boundary_core`)) >>
  goal_assum (drule_at (Pat `dload_prefix_match`)) >> metis_tac[]
QED

Resume ld_frame_normal_ptr_rows[bytes]:
  `access_ok lo G f i s /\ taint_ok f tn i s` by
    (qpat_assum `ptr_discipline_upto lo ngas C vs`
       (mp_tac o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE [ptr_discipline_upto_def]) >>
     disch_then (qspecl_then [`cs`,`PG`,`G`,`tn`,`f`,`i`,`s`] mp_tac) >>
     simp[]) >>
  irule ld_frame_dloadbytes_rows >> simp[] >>
  goal_assum (drule_at (Pat `dload_boundary_core`)) >>
  goal_assum (drule_at (Pat `dload_prefix_match`)) >> metis_tac[]
QED

Resume ld_frame_normal_ptr_rows[copied]:
  `n = 0` by metis_tac[dload_control_match_phase] >>
  `emitted = [i]` by
    (qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
     simp[lower_dload_inst_supply_def]) >>
  gvs[dload_prefix_zero] >>
  irule ld_frame_copied_ptr_rows >> simp[] >>
  goal_assum (drule_at (Pat `dload_boundary_core`)) >> metis_tac[]
QED

Resume ld_frame_normal_ptr_rows[dload]:
  Cases_on `2 <= n`
  >- (`n < 4` by
        (`n <> 0` by decide_tac >>
         qpat_assum `dload_control_match q f g s t i emitted n`
           (mp_then Any mp_tac dload_control_match_phase) >> simp[]) >>
      irule ld_frame_dload_later_rows >> simp[] >>
      goal_assum (drule_at (Pat `dload_boundary_core`)) >>
      goal_assum (drule_at (Pat `dload_prefix_match`)) >>
      simp[] >> metis_tac[]) >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match q f g s t0 i emitted 0` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
       fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `MEM f C.ctx_functions` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
       (mp_then Any mp_tac frame_reachable_raw_certificate) >>
     simp[] >> strip_tac >> simp[]) >>
  `o1_fn_shape C f` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `?off out. i.inst_operands = [off] /\ i.inst_outputs = [out]` by
    suspend "early_shape" >>
  `!v. off = Var v ==> v IN set (fn_ir_vars f) /\ ~retpc_var f v` by
    suspend "early_operand" >>
  drule_all dload_control_supply_origins >> strip_tac >>
  `off <> Var av` by metis_tac[] >>
  `op_taint un0 off = {}` by suspend "early_clean" >>
  irule dload_supply_early_safety >>
  conj_tac >- decide_tac >>
  goal_assum (drule_at (Pat `dload_prefix_match`)) >>
  goal_assum (drule_at (Pat `lower_dload_inst_supply`)) >>
  qexistsl [`av`,`off`,`out`] >> simp[]
QED

Resume ld_frame_normal_ptr_rows[early_shape]:
  `fn_inst_wf f` by fs[o1_fn_shape_def] >>
  `inst_wf i` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  gvs[inst_wf_def] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  Cases_on `i.inst_outputs` >> gvs[]
QED

Resume ld_frame_normal_ptr_rows[early_operand]:
  rpt strip_tac
  >- (irule fn_ir_vars_operand >> qexists `i` >> simp[]) >>
  `MEM (Var v) i.inst_operands` by simp[] >>
  `opaque_use_ok f` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  drule_all opaque_use_ok_retpc_use >> gvs[retpc_use_ok_def, MEM]
QED

Resume ld_frame_normal_ptr_rows[early_clean]:
  `fn_ptr_ok P f` by fs[EVERY_MEM] >>
  `taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline_upto lo ngas C vs` mp_tac >>
     simp[ptr_discipline_upto_def] >> strip_tac >>
     first_x_assum (drule_at (Pat `frame_reachable`)) >> simp[]) >>
  drule_all dload_offset_clean >> strip_tac >>
  drule dload_boundary_vars >> strip_tac >>
  Cases_on `off` >> gvs[op_taint_def] >>
  fs[dload_vars_match_def] >> metis_tac[]
QED

Finalise ld_frame_normal_ptr_rows

(* These tactics share the packing proof across distinct instruction arms.
   Separate enclosing resumes keep each arm at its own retained state. *)
val ld_frame_singleton_next_tac =
  `dload_control_match f.lf_supply f.lf_fn (ld_image f) f.lf_src f.lf_tgt inst [inst] 0` by
    (first_assum ACCEPT_TAC ORELSE
     (qpat_assum `f.lf_supply = Sigma f.lf_fn.fn_name` SUBST1_TAC >>
      first_assum ACCEPT_TAC)) >>
  `active_inst (ld_image f) ti' (s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx)` by
    (first_assum ACCEPT_TAC ORELSE fs[Abbr `tq`]) >>
  qpat_assum `frame_reachable vs C stk PG G tn f.lf_fn inst f.lf_src`
    (mp_then (Pat `frame_reachable`) mp_tac dload_singleton_reachable_next_fields) >>
  disch_then (qspecl_then [`s'`,`f.lf_tgt`,`ss`,`f.lf_supply`,`ti'`,`ld_image f`,`fuel`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
  disch_then (qx_choose_then `j` (qx_choose_then `E` strip_assume_tac)) >>
  qabbrev_tac `sn = ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx` >>
  qabbrev_tac `tnext = s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx` >>
  TRY (qpat_x_assum `Abbrev (g = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]));

val ld_frame_singleton_control_tac =
  `i = j` by
    (irule fmpStageBlockSimCodeTheory.active_inst_unique >>
     qexistsl [`f.lf_fn`,`sn`] >> simp[fn_labels_def] >>
     qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ i sn _ _ _ _`
       (strip_assume_tac o MATCH_MP ld_sync_source) >>
     qpat_assum `dload_control_match _ _ _ sn tnext j E 0`
       (strip_assume_tac o MATCH_MP dload_control_match_boundary) >> simp[]) >>
  qpat_x_assum `i = j` SUBST_ALL_TAC >>
  `g.lf_supply = f.lf_supply /\ g.lf_serial = f.lf_serial /\
   g.lf_fn = f.lf_fn /\ g.lf_Q = f.lf_Q /\ g.lf_src = sn /\ g.lf_tgt = tnext /\
   ld_image g = ld_image f` by
    (qpat_assum `g = f with <|lf_src := _; lf_tgt := _; lf_H := _; lf_tv := _|>`
       SUBST1_TAC >> simp[NoAsms,ld_image_def]) >>
  `dload_control_match g.lf_supply f.lf_fn (ld_image f) sn tnext j E 0` by
    (qpat_assum `g.lf_supply = f.lf_supply` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `0 < LENGTH E /\ ld_envelope g.lf_supply f.lf_fn sn sn.vs_inst_idx E tnext.vs_inst_idx /\
   ld_prefix C' (ld_image f) E tnext.vs_inst_idx 0 tnext tnext` by
    (qpat_assum `dload_control_match g.lf_supply _ _ sn tnext j E 0`
       (fn th => POP_ASSUM_LIST (K (mp_tac th))) >>
     simp[dload_control_match_def,ld_prefix_zero] >> strip_tac >>
     simp[lowerDloadSafetyRelationTheory.ld_envelope_def] >>
     metis_tac[pairTheory.FST,pairTheory.SND]);

val ld_frame_singleton_head_tac =
  `ti' = EL 0 E` by
    (qpat_assum `0 < LENGTH E` mp_tac >>
     qpat_assum `ti' = HD E` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `E` >> simp[listTheory.EL]);

val ld_frame_singleton_slots_tac =
  `!k a. k < LENGTH (g::fs) /\
     (a IN FRANGE (EL k (g::fs)).lf_H \/ MEM (SOME a) (EL k (g::fs)).lf_Q) ==>
     a IN ld_slots A (DROP k (g::fs))` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ A (g::fs) _`
       (fn sync =>
         qpat_assum `ld_global lo A (g::fs)` (fn global =>
           MATCH_MP_TAC (Q.INST [`m` |-> `1`, `old` |-> `f::fs`,
                                  `A` |-> `A`, `lo` |-> `lo`] ld_focus_suffix_cons) >>
           simp[NoAsms,rich_listTheory.DROP,global,
             MATCH_MP lowerDloadOracleCallAssemblyTheory.ld_sync_slots sync] >>
           first_assum ACCEPT_TAC))) >>
  `tnext.vs_allocas = f.lf_tgt.vs_allocas` by
    (qpat_assum `s'.vs_allocas = f.lf_tgt.vs_allocas` mp_tac >>
     simp[NoAsms,Abbr `tnext`]);

val ld_frame_singleton_history_tac =
  `sn.vs_call_ctx = f.lf_src.vs_call_ctx` by
    (qpat_assum `step_inst fuel C inst f.lf_src = OK ss`
       (mp_tac o CONJUNCT1 o MATCH_MP fnRunFieldsTheory.step_inst_ok_fields) >>
     simp[NoAsms,Abbr `sn`]) >>
  `sn.vs_gas_readings = tnext.vs_gas_readings` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ sn _ _ (g::fs) _`
       (mp_tac o CONJUNCT2 o MATCH_MP ld_sync_memory) >>
     simp[NoAsms,lowerDloadSafetyKernelTheory.ld_nonghost_def]);

val ld_frame_singleton_gas_count_tac =
  `LENGTH s'.vs_gas_readings <= LENGTH f.lf_tgt.vs_gas_readings` by
    (qspecl_then [`fuel`,`C'`,`inst`,`f.lf_tgt`] mp_tac
       (CONJUNCT1 gasCountTheory.gas_count_suffix) >>
     qpat_assum `step_inst fuel C' inst f.lf_tgt = OK s'` (fn h =>
       simp[NoAsms,h,gasCountTheory.gas_count_suffix_def,listTheory.LENGTH_DROP]));

val ld_frame_singleton_gas_tail_tac =
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
              LENGTH s'.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) fs` by
    ((`ss.vs_gas_readings = s'.vs_gas_readings` by
        (qpat_assum `sn.vs_gas_readings = tnext.vs_gas_readings` mp_tac >>
         simp[NoAsms,Abbr `sn`,Abbr `tnext`]) >>
      qpat_assum `EVERY (\a. _ /\ LENGTH ss.vs_gas_readings <= _) (g::fs)`
        (mp_tac o CONJUNCT2 o REWRITE_RULE[listTheory.EVERY_DEF]) >>
      qpat_assum `ss.vs_gas_readings = s'.vs_gas_readings` (fn hg =>
        simp[NoAsms,hg])) ORELSE
     (simp[NoAsms,listTheory.EVERY_MEM] >> qx_gen_tac `a` >> strip_tac >>
     qpat_assum `EVERY (\a. _ /\ LENGTH f.lf_tgt.vs_gas_readings <= _) fs`
       (qspec_then `a` mp_tac o REWRITE_RULE[listTheory.EVERY_MEM]) >>
     qpat_assum `MEM a fs` (fn h => simp[NoAsms,h]) >>
     strip_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists `LENGTH f.lf_tgt.vs_gas_readings` >> conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings`
       (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC));

val ld_frame_singleton_witness_tac =
  disj1_tac >>
  qexistsl [`stk`,`PG`,`step_prov PG G inst ss`,`step_taint inst f.lf_src ss tn`,
    `f.lf_fn`,`j`,`sn`,`tnext`,`A`,`g::fs`,`N`,`E`,`0`,`r::rs`,
    `step_prov PH H0 inst s'`,`step_taint inst f.lf_tgt s' un0`,`0`,`f`,`A`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[NoAsms,HD,TL,listTheory.EL,rich_listTheory.DROP,dload_prefix_zero,EVERY_DEF] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[IgnAsm `ld_image f = _`];

val ld_frame_singleton_rows_tac =
  qpat_assum `g.lf_supply = f.lf_supply` (fn hs =>
    qpat_assum `sn.vs_call_ctx = f.lf_src.vs_call_ctx` (fn hc =>
      simp[NoAsms,hs,hc])) >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (qmatch_goalsub_rename_tac `list_precedes _ _ _` >>
    qx_gen_tac `i0` >> qx_gen_tac `k0` >> strip_tac >>
    qpat_assum `!i k. _ ==> list_precedes (EL i (f::fs)).lf_fn.fn_name _ _`
      (qspecl_then [`i0`,`k0`] mp_tac) >>
    (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
    qpat_assum `g.lf_fn = f.lf_fn` (fn he =>
      Cases_on `i0` >> Cases_on `k0` >> simp[NoAsms,listTheory.EL,he])) >>
  TRY (qmatch_goalsub_rename_tac `FDOM (EL _ (_::MAP _ _)).vs_allocas` >>
    qx_gen_tac `k` >> strip_tac >> Cases_on `k` >>
    qpat_assum `tnext.vs_allocas = f.lf_tgt.vs_allocas`
      (fn ha => simp[NoAsms,listTheory.EL,ha]));

val ld_frame_singleton_saved_source_tac =
  `k < LENGTH stk` by
    (qpat_assum `LENGTH stk = LENGTH fs` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `((EL k stk).cf_fn = (EL k fs).lf_fn) /\
   ((EL k stk).cf_state = (EL k fs).lf_src)` by
    (qpat_assum `ld_sync lo P C vs stk PG G tn f.lf_fn inst f.lf_src f.lf_tgt A (f::fs) N`
       (mp_tac o SPEC (``k:num``) o cj 3 o MATCH_MP ld_sync_ghosts) >>
     qpat_assum `k < LENGTH stk` (fn h => simp[NoAsms,listTheory.EL,h]));

val ld_frame_singleton_saved_tac =
  TRY (FIRST_PROVE [qmatch_goalsub_rename_tac `ir_supply_covers_fn _ _` >>
    qx_gen_tac `k` >> strip_tac >>
    qpat_assum `!k. _ ==> dload_live_layout _ _ _ _ /\ _` (qspec_then `k` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
    qpat_assum `(EL k stk).cf_inst = (EL k ds).cf_inst` (SUBST1_TAC o SYM) >>
    (FIRST_PROVE [rpt conj_tac >> first_assum ACCEPT_TAC,
     ld_frame_singleton_saved_source_tac >>
      qpat_assum `(EL k stk).cf_fn = (EL k fs).lf_fn` (SUBST1_TAC o SYM) >>
      qpat_assum `(EL k stk).cf_state = (EL k fs).lf_src` (SUBST1_TAC o SYM) >>
      rpt conj_tac >> first_assum ACCEPT_TAC])]);

val ld_frame_singleton_saved_control_tac =
  TRY (FIRST_PROVE [qmatch_goalsub_rename_tac `dload_control_match _ _ _ _ _ _ _ _` >>
    qx_gen_tac `k` >> strip_tac >>
    qpat_assum `!k. _ ==> dload_control_match (EL k fs).lf_supply _ _ _ _ _ _ _`
      (qspec_then `k` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    ld_frame_singleton_saved_source_tac >>
    qpat_assum `(EL k stk).cf_fn = (EL k fs).lf_fn` (fn hf =>
      qpat_assum `(EL k stk).cf_state = (EL k fs).lf_src` (fn hs =>
        simp[NoAsms,hf,hs]))]);

val ld_frame_singleton_finish_tac =
  simp[Abbr `tnext`] >>
  TRY (qmatch_goalsub_rename_tac `HD lhs = HD rhs` >>
    (qpat_assum `ti' = HD lhs` mp_tac ORELSE qpat_assum `ti' = EL 0 lhs` mp_tac) >>
    (qpat_assum `ti' = HD rhs` mp_tac ORELSE qpat_assum `ti' = EL 0 rhs` mp_tac) >>
    simp[NoAsms,listTheory.EL] >> metis_tac[NoAsms]);

val ld_frame_singleton_reset_tac =
  `sg = ss` by
    (qpat_assum `step_inst fuel C inst f.lf_src = OK sg` mp_tac >>
     qpat_assum `step_inst 0 C inst f.lf_src = OK ss` mp_tac >>
     simp[IgnAsm `step_inst _ _ _ _ = _`,
          venomExecSemanticsTheory.step_inst_non_invoke]) >>
  qpat_x_assum `sg = ss` SUBST_ALL_TAC;

val ld_frame_singleton_scalar_fields_tac =
  rename1 `step_inst fuel C inst f.lf_src = OK sg` >>
  rename1 `step_inst 0 C inst f.lf_src = OK ss` >>
  `sg.vs_current_bb = f.lf_src.vs_current_bb /\
   sg.vs_prev_bb = f.lf_src.vs_prev_bb /\ sg.vs_inst_idx = f.lf_src.vs_inst_idx /\
   sg.vs_call_ctx = f.lf_src.vs_call_ctx /\
   s'.vs_current_bb = f.lf_tgt.vs_current_bb /\
   s'.vs_prev_bb = f.lf_tgt.vs_prev_bb /\ s'.vs_inst_idx = f.lf_tgt.vs_inst_idx /\
   s'.vs_allocas = f.lf_tgt.vs_allocas` by
    (qpat_assum `sg = _ with vs_vars := _` SUBST1_TAC >>
     qpat_assum `s' = _ with vs_vars := _` SUBST1_TAC >> simp[NoAsms]);

val ld_frame_singleton_index_fields_tac =
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars f.lf_fn)`,`C`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[fn_ir_vars_operand])) >>
  strip_tac;

val ld_frame_singleton_index_reset_tac =
  rename1 `step_inst fuel C inst f.lf_src = OK sg` >>
  `!v. MEM v (fn_ir_vars f.lf_fn) ==>
     (lookup_var v (sg with vs_inst_idx := SUC f.lf_src.vs_inst_idx) = NONE <=>
      lookup_var v (s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx) = NONE)` by
    (qpat_assum `!v. MEM v (fn_ir_vars f.lf_fn) ==> (lookup_var v sg = NONE <=> _)` mp_tac >>
     simp[NoAsms,lookup_var_def]) >>
  qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ sg s' _ _`
    (fn hb => assume_tac
      (Q.INST [`si` |-> `SUC f.lf_src.vs_inst_idx`,
               `ti` |-> `SUC f.lf_tgt.vs_inst_idx`]
        (SPEC_ALL (MATCH_MP dload_boundary_core_index_update hb))));

val ld_frame_singleton_sync_premises_tac =
  simp[NoAsms,HD,TL,EVERY_DEF] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[Excl "MEM",Excl "EVERY_MEM"];

val ld_frame_singleton_external_sync_tac =
  `ALL_DISTINCT (MAP (\b. b.bb_label) f.lf_fn.fn_blocks)` by simp[fn_labels_def] >>
  mp_tac (Q.INST [`C'` |-> `C'`, `fuel` |-> `fuel`,`j` |-> `ti'`,
                  `fn` |-> `f.lf_fn`, `s` |-> `f.lf_src`, `t` |-> `f.lf_tgt`,
                  `u` |-> `s'`, `H'` |-> `Hr`, `f0` |-> `f`, `A0` |-> `A`]
    (SPEC_ALL (BETA_RULE ld_frame_singleton_sync_next))) >>
  (impl_tac >- ld_frame_singleton_sync_premises_tac) >>
  disch_then (qx_choose_then `g` (qx_choose_then `i` strip_assume_tac));

val ld_frame_singleton_write_premises_tac =
  simp[] >> rpt strip_tac >>
  irule fn_ir_vars_operand >> qexists `inst` >> simp[];

val ld_frame_singleton_memory_write_finish_tac =
  rename1 `dload_boundary_core _ _ (r::rs) _ _ _ _ _ _ _ _ sg s' stk ds` >>
  `sg = ss` by
    (qpat_assum `step_inst fuel C inst f.lf_src = OK sg` mp_tac >>
     qpat_assum `step_inst fuel C inst f.lf_src = OK ss` mp_tac >> simp[NoAsms]) >>
  qpat_x_assum `sg = ss` SUBST_ALL_TAC >>
  `ld_ghost_ok (dyn_floor C vs) A Hr (step_prov PG G inst ss)` by
    (qpat_assum `Hr = f.lf_H` SUBST1_TAC >>
     qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ (f::fs) _`
       (mp_tac o CONJUNCT1 o MATCH_MP ld_sync_ghosts) >>
     qpat_assum `inst.inst_outputs = []` (fn ho =>
       simp[NoAsms,HD,ho,step_prov_def,set_prov_def,DRESTRICT_UNIV])) >>
  `ld_vars P A (f with <|lf_src := ss; lf_tgt := s'; lf_H := Hr;
                           lf_tv := (step_taint inst f.lf_src ss tn).t_var|>)` by
    (`(f with <|lf_src := ss; lf_tgt := s'; lf_H := Hr;
                lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) =
      (f with <|lf_src := ss; lf_tgt := s';
                lf_tv := (step_taint inst f.lf_src ss tn).t_var|>)` by
       (qpat_assum `Hr = f.lf_H` (fn hh =>
          simp[NoAsms,hh,ld_frame_component_equality])) >>
     qpat_assum `(f with <|lf_src := ss; lf_tgt := s'; lf_H := Hr; lf_tv := _|>) = _`
       SUBST1_TAC >> first_assum ACCEPT_TAC);

val ld_frame_singleton_index_boundary_tac =
  `!v. MEM v (fn_ir_vars f.lf_fn) ==>
      (lookup_var v (ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx) = NONE <=>
       lookup_var v (s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx) = NONE)` by
    (qpat_assum `!v. MEM v (fn_ir_vars f.lf_fn) ==> (lookup_var v ss = NONE <=> _)` mp_tac >>
     simp[NoAsms,lookup_var_def]) >>
  qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ ss s' _ _`
    (fn hb => assume_tac
      (Q.INST [`si` |-> `SUC f.lf_src.vs_inst_idx`,
               `ti` |-> `SUC f.lf_tgt.vs_inst_idx`]
        (SPEC_ALL (MATCH_MP dload_boundary_core_index_update hb))));

val ld_frame_singleton_alloca_reset_tac =
  TRY (qpat_x_assum `Abbrev (g = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])) >>
  `g.lf_supply = f.lf_supply /\ g.lf_serial = f.lf_serial /\
   g.lf_fn = f.lf_fn /\ g.lf_Q = f.lf_Q /\ g.lf_src = sn /\ g.lf_tgt = tnext /\
   ld_image g = ld_image f` by
    (qpat_assum `g = f with <|lf_src := _; lf_tgt := _; lf_H := _; lf_tv := _|>`
       SUBST1_TAC >> simp[NoAsms,ld_image_def,Abbr `sn`,Abbr `tnext`,arithmeticTheory.ADD1]) >>
  `dload_control_match g.lf_supply f.lf_fn (ld_image f) sn tnext i E 0` by
    (qpat_assum `g.lf_supply = f.lf_supply` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst f.lf_src ss tn)
      f.lf_fn i sn tnext Ar (g::fs) N` by
    (first_assum ACCEPT_TAC ORELSE (qpat_assum `Abbrev (Ar = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >> first_assum ACCEPT_TAC));

val ld_frame_singleton_alloca_slots_tac =
  `!a. a IN ld_slots A fs ==> FLOOKUP Ar a = FLOOKUP A a` by
    (simp[NoAsms,ld_slots_def] >> rpt strip_tac >>
     qpat_assum `!k. k IN FDOM A ==> FLOOKUP Ar k = FLOOKUP A k` irule >>
     qpat_assum `FLOOKUP A _ = SOME _` mp_tac >> simp[NoAsms,FLOOKUP_DEF]) >>
  `ld_slots A fs SUBSET ld_slots Ar fs` by
    (irule lowerDloadReturnInvokeStackTheory.ld_slots_agree_subset >>
     first_assum ACCEPT_TAC) >>
  `!a. MEM a fs ==> FRANGE a.lf_H SUBSET ld_slots Ar fs /\
                        (!k. MEM (SOME k) a.lf_Q ==> k IN ld_slots Ar fs)` by
    (qx_gen_tac `a:ld_frame` >> disch_tac >>
     qpat_assum `!g. MEM g fs ==> FRANGE g.lf_H SUBSET ld_slots A fs /\ _`
       (qspec_then `a` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `ld_slots A fs SUBSET ld_slots Ar fs`
       (mp_tac o REWRITE_RULE[SUBSET_DEF]) >>
     qpat_assum `FRANGE a.lf_H SUBSET ld_slots A fs`
       (mp_tac o REWRITE_RULE[SUBSET_DEF]) >>
     qpat_assum `!k. MEM (SOME k) a.lf_Q ==> _` mp_tac >>
     simp[NoAsms,SUBSET_DEF] >> metis_tac[NoAsms]);

val ld_frame_singleton_alloca_suffix_tac =
  `!k a. k < LENGTH (g::fs) /\
     (a IN FRANGE (EL k (g::fs)).lf_H \/ MEM (SOME a) (EL k (g::fs)).lf_Q) ==>
     a IN ld_slots Ar (DROP k (g::fs))` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ Ar (g::fs) _` (fn sync =>
       qpat_assum `ld_global lo Ar (g::fs)` (fn global =>
         MATCH_MP_TAC (Q.INST [`m` |-> `1`, `old` |-> `f::fs`,
                                `A` |-> `A`, `lo` |-> `lo`] ld_focus_suffix_cons) >>
         simp[NoAsms,rich_listTheory.DROP,global,
           MATCH_MP lowerDloadOracleCallAssemblyTheory.ld_sync_slots sync] >>
         conj_tac >> first_assum ACCEPT_TAC))) >>
  `ld_envelope (Sigma f.lf_fn.fn_name) f.lf_fn sn sn.vs_inst_idx E tnext.vs_inst_idx` by
    (qpat_assum `f.lf_supply = Sigma f.lf_fn.fn_name` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC);

val ld_frame_singleton_alloca_witness_tac =
  disj1_tac >>
  qexistsl [`stk`,`PG`,`step_prov PG G inst ss`,`step_taint inst f.lf_src ss tn`,
    `f.lf_fn`,`i`,`sn`,`tnext`,`Ar`,`g::fs`,`N`,`E`,`0`,`r1::rs`,
    `step_prov PH H0 inst s'`,`step_taint inst f.lf_tgt s' un0`,`0`,`f`,`A`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[NoAsms,HD,TL,listTheory.EL,rich_listTheory.DROP,dload_prefix_zero,EVERY_DEF] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC);

val ld_frame_singleton_alloca_history_tac =
  `tnext.vs_gas_readings = s'.vs_gas_readings` by
    simp[NoAsms,Abbr `tnext`] >>
  `sn.vs_gas_readings = s'.vs_gas_readings` by
    (qpat_assum `sn.vs_gas_readings = tnext.vs_gas_readings` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `LENGTH rs = LENGTH stk` by
    (qpat_assum `LENGTH stk = LENGTH fs` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `!a. a IN FDOM A /\ a IN ld_slots A fs ==> FLOOKUP Ar a = FLOOKUP A a` by
    (rpt strip_tac >>
     qpat_assum `!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a` irule >>
     first_assum ACCEPT_TAC);

val ld_frame_singleton_alloca_fields_tac =
  map_every (fn field => qpat_assum field (fn eq => simp[NoAsms,eq]))
    [`g.lf_supply = f.lf_supply`, `g.lf_serial = f.lf_serial`,
     `g.lf_fn = f.lf_fn`, `g.lf_Q = f.lf_Q`,
     `g.lf_src = sn`, `g.lf_tgt = tnext`, `ld_image g = ld_image f`,
     `sn.vs_call_ctx = f.lf_src.vs_call_ctx`,
     `sn.vs_gas_readings = s'.vs_gas_readings`,
     `tnext.vs_gas_readings = s'.vs_gas_readings`] >>
  TRY (first_assum ACCEPT_TAC);

val ld_frame_singleton_alloca_geometry_tac =
  TRY (FIRST_PROVE [qmatch_goalsub_rename_tac `list_precedes _ _ _` >>
    qx_gen_tac `i0` >> qx_gen_tac `k0` >> strip_tac >>
    qpat_assum `!i k. _ ==> list_precedes (EL i (f::fs)).lf_fn.fn_name _ _`
      (qspecl_then [`i0`,`k0`] mp_tac) >>
    (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
    qpat_assum `g.lf_fn = f.lf_fn` (fn he =>
      Cases_on `i0` >> Cases_on `k0` >> simp[NoAsms,listTheory.EL,he])]) >>
  TRY (FIRST_PROVE [qmatch_goalsub_rename_tac `(EL _ (r1::rs)).dr_scratch` >>
    qpat_assum `LENGTH rs = LENGTH fs` SUBST1_TAC >>
    qx_gen_tac `k` >> Cases_on `k`
    >- (qpat_assum `r1.dr_scratch = FDOM s'.vs_allocas DIFF _` (fn h =>
          simp[NoAsms,h,Abbr `tnext`,listTheory.EL,EXTENSION]) >>
        metis_tac[NoAsms]) >>
    strip_tac >>
    qpat_assum `!k. _ ==> (EL k (r::rs)).dr_scratch = _`
      (qspec_then `SUC n'` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms,listTheory.EL]]);

val ld_frame_singleton_alloca_saved_tac =
  TRY (FIRST_PROVE [qmatch_goalsub_rename_tac `dload_live_layout _ _ _ _` >>
    qpat_assum `LENGTH stk = LENGTH fs` SUBST1_TAC >>
    qx_gen_tac `k` >> strip_tac >>
    qpat_assum `!k. _ ==> (EL k ds).cf_fn = _ /\ (EL k ds).cf_state = _`
      (qspec_then `k` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    qpat_assum `(EL k ds).cf_fn = ld_image (EL k fs)` SUBST1_TAC >>
    qpat_assum `(EL k ds).cf_state = (EL k fs).lf_tgt` SUBST1_TAC >>
    qpat_assum `!k. _ ==> dload_live_layout _ _ _ _ /\ _` (qspec_then `k` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms]]);

val ld_frame_singleton_alloca_control_tac =
  TRY (FIRST_PROVE [qmatch_goalsub_rename_tac `dload_control_match _ _ _ _ _ _ _ _` >>
    qpat_assum `LENGTH stk = LENGTH fs` SUBST1_TAC >>
    qx_gen_tac `k` >> strip_tac >>
    qpat_assum `!k. _ ==> (EL k ds).cf_fn = _ /\ (EL k ds).cf_state = _`
      (qspec_then `k` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    qpat_assum `(EL k ds).cf_fn = ld_image (EL k fs)` SUBST1_TAC >>
    qpat_assum `(EL k ds).cf_state = (EL k fs).lf_tgt` SUBST1_TAC >>
    qpat_assum `!k. _ ==> dload_live_layout _ _ _ _ /\ _` (qspec_then `k` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    qpat_assum `(EL k stk).cf_inst = (EL k ds).cf_inst` SUBST1_TAC >>
    qpat_assum `!k. _ ==> dload_control_match (EL k fs).lf_supply _ _ _ _ _ _ _`
      (qspec_then `k` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms]]);

Theorem ld_frame_actual_occurrence[local]:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  callee_first names C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\
  (!f. MEM f C.ctx_functions ==>
    ir_supply_covers_fn (Sigma f.fn_name) f /\
    lookup_function f.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma f.fn_name) f))) /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions ==>
  !ds PH H un gn ti t. frame_reachable vs C' ds PH H un gn ti t ==>
    gas_cut n vs t ==>
    ^frame_normal lo P C C' vs Sigma names ds PH H un gn ti t \/
    ^frame_terminal lo P vs C ds H un gn ti t
Proof
  strip_tac >>
  `!v Ct ds PH H un gn ti t. frame_reachable v Ct ds PH H un gn ti t ==>
     v = vs /\ Ct = C' /\ gas_cut n vs t ==>
     ^frame_normal lo P C C' vs Sigma names ds PH H un gn ti t \/
     ^frame_terminal lo P vs C ds H un gn ti t`
  suffices_by (disch_then (qspecl_then [`vs`,`C'`] mp_tac) >> simp[]) >>
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `v = vs` SUBST_ALL_TAC >> qpat_x_assum `Ct = C'` SUBST_ALL_TAC
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_frame_actual_occurrence[entry]:
  disj1_tac >> irule ld_frame_normal_entry >>
  `?nm f l. C.ctx_entry = SOME nm /\
    lookup_function nm C.ctx_functions = SOME f /\ fn_entry_label f = SOME l` by
    (fs[o1_safe_upto_def, unitMemInvTheory.mem_inv_raw_reachable] >> metis_tac[]) >>
  `MEM f C.ctx_functions /\ f.fn_name = nm` by
    metis_tac[lookup_function_MEM, fmpAnalysisPropsTheory.lookup_function_name] >>
  `fn_entry_label (FST (lower_dload_function_supply (Sigma f.fn_name) f)) =
   fn_entry_label f` by
    (Cases_on `lower_dload_function_supply (Sigma f.fn_name) f` >>
     drule lower_dload_function_supply_labels >> simp[]) >>
  simp[] >> conj_tac
  >- (gvs[] >> metis_tac[])
  >> qexistsl [`D`,`n`] >> simp[]
QED

Resume ld_frame_actual_occurrence[block]:
  `gas_cut n vs t` by (drule_all ld_block_entry_cut_back >> simp[]) >>
  qpat_x_assum `vs = vs /\ C' = C' /\ gas_cut n vs t ==> _` mp_tac >>
  (impl_tac >- simp[]) >> disch_then (DISJ_CASES_THEN assume_tac)
  >- (disj1_tac >>
      `!f. MEM f C.ctx_functions ==> ir_supply_covers_fn (Sigma f.fn_name) f` by metis_tac[] >>
      `!f. MEM f C.ctx_functions ==> lookup_function f.fn_name C'.ctx_functions =
        SOME (FST (lower_dload_function_supply (Sigma f.fn_name) f))` by metis_tac[] >>
      drule_all ld_frame_normal_block >> disch_then ACCEPT_TAC) >>
  pop_assum (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `_ = EL k mid` SUBST_ALL_TAC >>
  `k+1 = LENGTH mid` by
    (Cases_on `k+1 < LENGTH mid`
     >- (`~is_terminator (EL k mid).inst_opcode` by
           (irule (cj 3 dload_indexed_terminal_constructor_exclusions) >> simp[]) >> fs[]) >>
     decide_tac) >>
  `step_inst fuel C' (EL k mid) t <> OK s'` by
    (irule (cj 4 dload_indexed_terminal_constructor_exclusions) >> simp[]) >> fs[]
QED

Resume ld_frame_actual_occurrence[call]:
  `gas_cut n vs t` by (drule_all ld_callee_entry_cut_back >> simp[]) >>
  qpat_x_assum `vs = vs /\ C' = C' /\ gas_cut n vs t ==> _` mp_tac >>
  (impl_tac >- simp[]) >> disch_then (DISJ_CASES_THEN assume_tac)
  >- (disj1_tac >>
      `!f. MEM f C.ctx_functions ==> ir_supply_covers_fn (Sigma f.fn_name) f /\
         fn_ptr_ok P f /\ lookup_function f.fn_name C'.ctx_functions =
           SOME (FST (lower_dload_function_supply (Sigma f.fn_name) f))` by
        metis_tac[EVERY_MEM] >>
      `ptr_discipline_upto lo n C vs` by fs[o1_safe_upto_def,o1_ptr_safe_upto_def] >>
      drule_all ld_frame_normal_call >> disch_then ACCEPT_TAC) >>
  pop_assum (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `_ = EL k mid` SUBST_ALL_TAC >>
  `(EL k mid).inst_opcode <> INVOKE` by
    (irule (cj 1 dload_indexed_terminal_constructor_exclusions) >> simp[]) >> fs[]
QED

Resume ld_frame_actual_occurrence[ret]:
  `gas_cut n vs t` by (drule_all ld_frame_return_cut_back >> simp[]) >>
  qpat_x_assum `vs = vs /\ C' = C' /\ gas_cut n vs t ==> _` mp_tac >>
  (impl_tac >- simp[]) >> disch_then (DISJ_CASES_THEN assume_tac)
  >- (disj1_tac >> drule_all ld_frame_normal_return >> disch_then ACCEPT_TAC) >>
  pop_assum (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `_ = EL k mid` SUBST_ALL_TAC >>
  drule_all dload_indexed_terminal_constructor_exclusions >> metis_tac[]
QED

Resume ld_frame_actual_occurrence[next]:
  `gas_cut n vs t` by
    (irule ld_step_ok_cut_back >> qexistsl [`C'`,`fuel`,`ti`,`s'`] >>
     fs[gas_cut_def]) >>
  `ALL_DISTINCT (fn_labels gn)` by
    (`MEM gn C'.ctx_functions` by
       metis_tac[frameAllocationOwnershipTheory.frame_reachable_functions_member] >>
     qpat_assum `EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions`
       (mp_tac o REWRITE_RULE[EVERY_MEM]) >>
     disch_then (drule_at (Pat `MEM gn _`)) >> simp[]) >>
  qpat_x_assum `vs = vs /\ C' = C' /\ gas_cut n vs t ==> _` mp_tac >>
  (impl_tac >- simp[]) >> reverse (disch_then (DISJ_CASES_THEN assume_tac))
  >- (disj2_tac >>
      pop_assum (strip_assume_tac o BETA_RULE) >>
      qpat_x_assum `ti = EL k mid` SUBST_ALL_TAC >>
      `k+1 < LENGTH mid` by
        (Cases_on `k+1 < LENGTH mid` >- simp[] >>
         `k+1 = LENGTH mid` by decide_tac >>
         drule_all dload_indexed_terminal_constructor_exclusions >> metis_tac[]) >>
      `(EL k mid).inst_opcode = ASSIGN` by
        (irule (cj 1 dload_terminal_slice_opcode) >> simp[]) >>
      `s'.vs_gas_readings = t.vs_gas_readings /\
       (ctx_has_dalloca C ==> allocas_below_fmp (s' with vs_inst_idx := SUC t.vs_inst_idx))` by
        (drule_all_then strip_assume_tac genBlockSimTheory.step_inst_assign_ok >>
         gvs[update_var_def, allocas_below_fmp_def] >>
         strip_tac >> qpat_assum `ctx_has_dalloca C ==> _` mp_tac >> simp[]) >>
      drule_all dload_terminal_assign_next >>
      disch_then (qspec_then `PH` strip_assume_tac) >>
      `ti' = EL (k+1) mid` by
        (irule fmpStageBlockSimCodeTheory.active_inst_unique >>
         qexistsl [`gn`,`s' with vs_inst_idx := SUC t.vs_inst_idx`] >>
         gvs[]) >>
      `ss.vs_gas_readings = s.vs_gas_readings` by
        (qpat_x_assum `step_inst fuel C' _ t = OK s'` kall_tac >>
         drule_all_then strip_assume_tac genBlockSimTheory.step_inst_assign_ok >>
         gvs[update_var_def]) >>
      CONV_TAC (REDEPTH_CONV BETA_CONV) >>
      qrefinel [`cs`,`PG`,`_`,`_`,`f`,`ss`,`fs`,`bb`,`tb`,`bs`,`bt`,`mid`,`a`,`b`,`k+1`] >>
      gvs[] >> rpt (goal_assum (drule_at Any)) >> simp[])
  >> qpat_x_assum `ALL_DISTINCT (fn_labels gn)`
        (assume_tac o REWRITE_RULE[fn_labels_def]) >>
      drule_all ld_frame_normal_interior >>
      reverse (disch_then (DISJ_CASES_THEN assume_tac))
      >- (disj1_tac >> first_assum ACCEPT_TAC)
      >> qpat_x_assum `(\B lo P C C' vs Sigma names ds PH H un gn ti t. _) (\x y. T) _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac
      >> pop_assum (strip_assume_tac o BETA_RULE)
      >> `gas_cut n vs s` by fs[gas_cut_def]
      >> Cases_on `frames` >- gvs[]
      >> rename1 `ld_sync _ _ _ _ _ _ _ _ fn inst s t0 A (f::fs) N`
      >> Cases_on `rs` >- fs[]
      >> rename1 `dload_boundary_core _ _ (r::rs) _ _ _ _ _ _ _ _ _ _ _ _`
      >> fs[HD,TL,NOT_CONS_NIL]
      >> drule_then strip_assume_tac ld_sync_source
      >> drule_then (strip_assume_tac o REWRITE_RULE[HD]) ld_sync_active
      >> drule_all_then strip_assume_tac ld_sync_fn_shape
      >> drule_then strip_assume_tac o1_fn_shape_components
      >> `MEM fn C.ctx_functions` by
           (drule_then strip_assume_tac frame_reachable_raw_certificate >> simp[])
      >> `ir_supply_covers_fn f.lf_supply fn` by simp[]
      >> `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member]
      >> `inst_wf inst` by
           (qpat_assum `fn_inst_wf fn` (mp_tac o REWRITE_RULE[fmpStepStructuralTheory.fn_inst_wf_fn_insts,EVERY_MEM]) >>
            disch_then drule >> simp[])
      >> Cases_on `inst.inst_opcode = DLOAD`
      >- suspend "dload"
      >> suspend "other_final"
QED

Resume ld_frame_actual_occurrence[dload]:
  `?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
    fs[inst_wf_def,LENGTH_EQ_NUM_compute] >>
  drule_all_then strip_assume_tac ld_dload_envelope_temporary >>
  `h = 3` by fs[] >>
  qpat_x_assum `h = 3` SUBST_ALL_TAC >>
  qpat_x_assum `gn = ld_image f` SUBST_ALL_TAC >>
  `set (fn_ir_inst_ids fn) = {id | ?i. MEM i (fn_insts fn) /\ i.inst_id = id}` by
    (`fn_ir_inst_ids fn = MAP (\i. i.inst_id) (fn_insts fn)` by
       (pure_rewrite_tac[fn_ir_inst_ids_def,fn_insts_def] >>
        qspec_tac (`fn.fn_blocks`,`bs`) >> Induct >>
        simp[fn_insts_blocks_def,block_ir_inst_ids_def]) >>
     simp[EXTENSION,MEM_MAP] >> metis_tac[]) >>
  `r.dr_scratch = FDOM t0.vs_allocas DIFF set (fn_ir_inst_ids fn)` by
    (qpat_x_assum `!k. _ ==> (EL k (r::rs)).dr_scratch = _` (qspec_then `0` mp_tac) >>
     simp[listTheory.EL]) >>
  qpat_x_assum `fs = fs0` (SUBST_ALL_TAC o SYM) >>
  mp_tac (Q.INST [`u` |-> `s'`, `j` |-> `ti'`, `pf` |-> `pfuel`,
                  `Ws` |-> `MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) stk`]
    (CONV_RULE (TOP_DEPTH_CONV
       (HO_REWR_CONV UNWIND_THM2 ORELSEC Unwind.UNWIND_FORALL_CONV))
       ld_focus_private_frame_successor)) >>
  (impl_tac >- simp[EVERY_DEF]) >>
  strip_tac >> disj1_tac >>
  qabbrev_tac `s1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `t1 = s' with vs_inst_idx := SUC t.vs_inst_idx` >>
  `s1.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `step_inst 0 C inst s = OK ss`
       (mp_tac o MATCH_MP o1LowerDloadRunnerBoundaryTheory.ld_step_ok_call_ctx) >>
     simp[Abbr `s1`]) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\
   g.lf_supply = f.lf_supply /\ g.lf_Q = f.lf_Q` by
    (qpat_assum `g = f with <|lf_src := _; lf_tgt := _; lf_H := _;
                             lf_tv := _; lf_E := _|>` SUBST1_TAC >> simp[]) >>
  `^frame_suffix A (g::fs)` by
    (BETA_TAC >>
     `FDOM A = ld_slots A (g::fs)` by
       (qpat_assum `ld_sync _ _ _ _ _ _ _ _ fn i s1 t1 A (g::fs) _`
          (mp_tac o MATCH_MP ld_sync_slots) >> simp[]) >>
     MATCH_MP_TAC (Q.INST [`m` |-> `1`, `old` |-> `f::fs`,
                           `A` |-> `A`, `lo` |-> `lo`] ld_focus_suffix_cons) >>
     qpat_assum `!k a. _ ==> _ IN ld_slots A (DROP k (f::fs))` mp_tac >>
     simp[rich_listTheory.DROP]) >>
  qpat_x_assum `g = f with <|lf_src := _; lf_tgt := _; lf_H := _;
                            lf_tv := _; lf_E := _|>` kall_tac >>
  qpat_x_assum `r1.dr_scratch = (EL 0 X).inst_id INSERT r.dr_scratch` kall_tac >>
  qexistsl [`stk`,`PG`,`step_prov PG G inst ss`,`step_taint inst s ss tn`,
    `fn`,`i`,`s1`,`t1`,`A`,`g::fs`,`N`,`Y`,`0`,`r1::rs`,
    `step_prov PH H (EL 3 X) s'`,`step_taint (EL 3 X) t s' un`,
    `pfuel`,`g`,`A`] >>
  fs[HD,TL,listTheory.EL,EVERY_DEF] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!j k. _ ==> list_precedes (EL j (f::fs)).lf_fn.fn_name _ names`
        (qspecl_then [`j`,`k`] mp_tac) >>
      Cases_on `j` >> Cases_on `k` >> simp[listTheory.EL]) >>
  conj_tac
  >- (rpt strip_tac >> qpat_assum `!g. MEM g fs ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  qpat_assum `ld_image g = ld_image f` (fn eq =>
    qpat_assum `ld_prefix C' (ld_image g) Y _ 0 t1 t1`
      (assume_tac o REWRITE_RULE[eq]) >>
    qpat_assum `dload_control_match f.lf_supply _ (ld_image g) s1 t1 _ Y 0`
      (assume_tac o REWRITE_RULE[eq])) >>
  qpat_assum `f.lf_supply = Sigma fn.fn_name` (fn eq =>
    qpat_assum `ld_envelope f.lf_supply fn s1 _ Y _`
      (assume_tac o REWRITE_RULE[eq]) >>
    qpat_assum `dload_control_match f.lf_supply _ (ld_image f) s1 t1 _ Y 0`
      (assume_tac o REWRITE_RULE[eq])) >>
  simp[] >>
  conj_tac
  >- (Cases >> simp[listTheory.EL] >> rename1 `(EL k rs).dr_scratch = _` >> strip_tac >>
      qpat_assum `!k. k < SUC (LENGTH rs) ==> (EL k (r::rs)).dr_scratch = _`
        (qspec_then `SUC k` (mp_tac o REWRITE_RULE[listTheory.EL,arithmeticTheory.LESS_MONO_EQ])) >>
      impl_tac >- decide_tac >> simp[TL]) >>
  simp[Abbr `t1`] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!k. k < LENGTH stk ==> dload_live_layout _ _ _ _ /\ _`
        (qspec_then `k` mp_tac) >>
      (impl_tac >- decide_tac) >>
      strip_tac >> qpat_assum `!k. k < LENGTH ds ==> _ /\ _` (qspec_then `k` mp_tac) >>
      (impl_tac >- decide_tac) >> gvs[]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  rpt strip_tac >>
  rename1 `dload_control_match _ (EL j stk).cf_fn _ _ _ _ _ _` >>
  qpat_assum `!k. k < LENGTH stk ==> dload_control_match _ _ _ _ _ _ _ _`
    (qspec_then `j` mp_tac) >> (impl_tac >- decide_tac) >>
  qpat_assum `!k. k < LENGTH ds ==> _ /\ _` (qspec_then `j` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  qpat_assum `!k. k < LENGTH stk ==> dload_live_layout _ _ _ _ /\ _`
    (qspec_then `j` mp_tac) >> (impl_tac >- decide_tac) >> gvs[]
QED

Resume ld_frame_actual_occurrence[other_final]:
  qpat_x_assum `fs = fs0` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `gn = ld_image f` SUBST_ALL_TAC >>
  Cases_on `inst.inst_opcode = DLOADBYTES`
  >- suspend "bytes_frame"
  >> suspend "singleton_frame"
QED

Resume ld_frame_actual_occurrence[bytes_frame]:
  `?dest off len. inst.inst_operands = [dest;off;len] /\ inst.inst_outputs = []` by
    fs[inst_wf_def,LENGTH_EQ_NUM_compute] >>
  drule_all_then strip_assume_tac ld_dloadbytes_envelope_temporary >>
  `h = 1` by fs[] >>
  qpat_x_assum `h = 1` SUBST_ALL_TAC >>
  `step_inst pfuel C' (EL 1 X) t = OK s'` by
    fs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `dload_prefix_match pfuel C' PH X (SUC 1) t0 H0 un0
       (s' with vs_inst_idx := SUC t.vs_inst_idx)
       (step_prov PH H (EL 1 X) s') (step_taint (EL 1 X) t s' un)` by
    (pure_once_rewrite_tac[dload_prefix_match_def] >>
     conj_tac
     >- (qpat_assum `SUC 1 = LENGTH X` (SUBST1_TAC o SYM) >> decide_tac) >>
     qexistsl [`t`,`H`,`un`,`s'`] >>
     qpat_assum `dload_prefix_match pfuel _ _ _ 1 _ _ _ _ _ _`
       (fn pr => qpat_assum `step_inst pfuel _ _ _ = OK _`
          (fn st => rewrite_tac[pr,st]))) >>
  `~in_revert_forward fn s` by
    (irule concretizeLayoutLocalReturnTheory.active_inst_not_revert_forward >>
     conj_tac >- simp[fn_labels_def] >> qexists_tac `inst` >> simp[]) >>
  `lo <= vs.vs_alloca_next /\ mem_inv dload_headroom_ok C vs /\
   ptr_discipline_upto lo n C vs` by
    (fs[o1_safe_upto_def,o1_ptr_safe_upto_def,ptr_discipline_upto_def] >> (metis_tac[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def])) >>
  drule_all_then strip_assume_tac concretizeLayoutCutSafeTheory.ptr_discipline_upto_at >>
  `dload_offset_ok C fn inst s` by
    (`raw_reachable vs C fn inst s` by metis_tac[ld_frame_raw_reachable] >>
     qpat_assum `o1_safe_upto _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[o1_safe_upto_def]) >>
     qpat_assum `!fn inst s. raw_reachable _ _ fn inst s /\ _ ==> _`
       (qspecl_then [`fn`,`inst`,`s`] mp_tac) >> simp[]) >>
  `code_layout_valid s` by (irule ld_sync_source_code_layout_static >> metis_tac[]) >>
  `fn_ptr_ok P fn` by fs[EVERY_MEM] >>
  `FDOM G SUBSET fn_pv P fn` by
    (qpat_assum `frame_reachable vs C stk PG G tn fn inst s`
       (mp_tac o MATCH_MP frame_reachable_prov_supported) >>
     disch_then (qspec_then `P` mp_tac) >>
     (impl_tac >- fs[EVERY_MEM]) >> simp[]) >>
  `!v. MEM (Var v) inst.inst_operands ==>
       v IN set (fn_ir_vars fn) DIFF {v | retpc_var fn v}` by
    (`opaque_use_ok fn` by
       fs[unitShapeDefsTheory.fn_shape_ok_def,venomWfTheory.wf_function_def] >>
     `~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET]` by simp[] >>
     rpt strip_tac >>
     drule_all lowerDloadPtrJointScalarTheory.dload_original_nonopaque_operands >> simp[]) >>
  `LENGTH X = 2` by
    (qpat_assum `SUC 1 = LENGTH X` (SUBST1_TAC o SYM) >> decide_tac) >>
  mp_tac (Q.INST [`u` |-> `s'`, `t1` |-> `t`, `gn` |-> `ld_image f`] ld_focus_bytes_classified_write) >>
  (impl_tac >- simp[]) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  mp_tac (Q.INST [`u` |-> `s'`, `t1` |-> `t`, `z` |-> `z'`]
    (INST_TYPE [alpha |-> ``:256``]
      (CONV_RULE (TOP_DEPTH_CONV Unwind.UNWIND_FORALL_CONV) ld_focus_bytes_classified_next))) >>
  (impl_tac >- (rpt conj_tac >> FIRST_PROVE [first_assum ACCEPT_TAC, simp[]])) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `s1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `t1 = s' with vs_inst_idx := SUC t.vs_inst_idx` >>
  `dload_boundary_core (dyn_floor C vs) lo (r::rs)
     (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
     (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) stk)
     PG PH (step_prov PG G inst ss) (step_prov PH H (EL 1 X) s')
     (step_taint inst s ss tn) (step_taint (EL 1 X) t s' un) s1 t1 stk ds` by
    (`dload_prefix_match pfuel C' PH [EL 0 X;EL 1 X] 2 t0 H0 un0 t1
       (step_prov PH H (EL 1 X) s') (step_taint (EL 1 X) t s' un)` by
       (qpat_assum `X = [a;c]` (fn xe =>
          qpat_assum `dload_prefix_match pfuel C' PH X (SUC 1) _ _ _ _ _ _`
            (mp_tac o REWRITE_RULE[xe])) >>
        simp[NoAsms,Abbr `t1`,listTheory.EL] >>
        qpat_assum `X = [a;c]` (fn xe => simp[NoAsms,xe,listTheory.EL])) >>
     qpat_assum `dload_prefix_match _ _ _ [EL 0 X; EL 1 X] 2 _ _ _ _ _ _`
       (mp_then Any mp_tac lowerDloadPtrBytesTransportTheory.dloadbytes_two_step_boundary) >>
     disch_then (drule_at (Pat `dload_boundary_core`)) >>
     disch_then (drule_at (Pat `fn_ptr_ok`)) >>
     disch_then (drule_at (Pat `dload_offset_ok`)) >>
     disch_then (qspecl_then [`len`,`off`,`dest`,`z`] mp_tac) >>
     (impl_tac >- simp[listTheory.EL]) >>
     disch_then (qx_choose_then `ss0` (CONJUNCTS_THEN assume_tac)) >>
     `step_inst pfuel C inst s = step_inst 0 C inst s` by
       (irule ptrSafeRunTheory.step_inst_non_invoke_fuel >> simp[]) >>
     `ss0 = ss` by
       (qpat_assum `step_inst pfuel C inst s = OK ss0` mp_tac >>
        qpat_assum `step_inst pfuel C inst s = step_inst 0 C inst s`
          (fn eq => rewrite_tac[eq]) >>
        simp[]) >>
     qpat_x_assum `ss0 = ss` SUBST_ALL_TAC >>
     qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ t1 _ _` mp_tac >>
     qpat_assum `X = [a;c]` (fn xe => simp[NoAsms,Abbr `s1`,xe,listTheory.EL]) >>
     simp[]) >>
  `ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
   ss.vs_inst_idx = s.vs_inst_idx /\ s1.vs_call_ctx = s.vs_call_ctx /\
   t1.vs_current_bb = t0.vs_current_bb /\ t1.vs_prev_bb = t0.vs_prev_bb /\
   t1.vs_inst_idx = t0.vs_inst_idx + LENGTH X /\ t1.vs_allocas = t0.vs_allocas` by
    simp[Abbr `s1`,Abbr `t1`,venomStateTheory.write_memory_with_expansion_def,
         venomStateTheory.update_var_def] >>
  qpat_assum `dload_control_match f.lf_supply fn (ld_image f) s t0 inst X 0`
    (mp_then Any mp_tac lowerDloadPtrJointNextTheory.dload_control_emission_next_fields) >>
  disch_then (drule_at (Pat `active_inst (ld_image f) ti' t1`)) >>
  disch_then (qspec_then `ss` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `i` (qx_choose_then `Y` strip_assume_tac)) >>
  `dload_control_match f.lf_supply fn (ld_image f) s1 t1 i Y 0` by
    (simp[NoAsms,Abbr `s1`] >> first_assum ACCEPT_TAC) >>
  `active_inst fn i s1` by
    (qpat_assum `dload_control_match _ fn _ s1 t1 i Y 0`
       (strip_assume_tac o MATCH_MP dload_control_match_boundary) >> simp[]) >>
  qabbrev_tac `g = f with <|lf_src := s1; lf_tgt := t1|>` >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
           fn i s1 t1 A (g::fs) N` by
    (qpat_assum `!next. active_inst _ next _ ==> ld_sync _ _ _ _ _ _ _ _ _ next _ _ _ _ _`
       (qspec_then `i` mp_tac) >>
     simp[NoAsms,Abbr `g`,Abbr `s1`,Abbr `t1`] >>
     asm_rewrite_tac[]) >>
  `ld_global lo A (g::fs) /\ FDOM A = ld_slots A (g::fs)` by
    (simp[NoAsms,Abbr `g`,Abbr `s1`,Abbr `t1`] >> asm_rewrite_tac[]) >>
  `g.lf_supply = f.lf_supply /\ g.lf_fn = fn /\ g.lf_serial = f.lf_serial /\
   g.lf_Q = f.lf_Q /\ g.lf_src = s1 /\ g.lf_tgt = t1 /\ ld_image g = ld_image f` by
    simp[Abbr `g`,ld_image_def] >>
  `ld_envelope f.lf_supply fn s1 s1.vs_inst_idx Y t1.vs_inst_idx /\
   ld_prefix C' (ld_image f) Y t1.vs_inst_idx 0 t1 t1` by
    (qpat_assum `dload_control_match _ fn _ s1 t1 i Y 0` mp_tac >>
     simp[NoAsms,dload_control_match_def,ld_envelope_def,ld_prefix_zero] >>
     rpt strip_tac >> metis_tac[pairTheory.FST,pairTheory.SND]) >>
  `!a. MEM a (fn_ir_vars fn) ==> (lookup_var a s1 = NONE <=> lookup_var a t1 = NONE)` by
    (qx_gen_tac `x` >> disch_tac >> `x <> z'` by metis_tac[] >>
     `lookup_var x s1 = lookup_var x s /\ lookup_var x t1 = lookup_var x t0` by
       simp[Abbr `s1`,Abbr `t1`,venomStateTheory.write_memory_with_expansion_def,
            venomStateTheory.update_var_def,venomStateTheory.lookup_var_def,
            finite_mapTheory.FLOOKUP_UPDATE] >>
     qpat_assum `lookup_var x s1 = _` SUBST1_TAC >>
     qpat_assum `lookup_var x t1 = _` SUBST1_TAC >>
     qpat_assum `!v. MEM v (fn_ir_vars fn) ==>
       (lookup_var v s = NONE <=> lookup_var v t0 = NONE)`
       (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
  `!k a. k < LENGTH (g::fs) /\
     (a IN FRANGE (EL k (g::fs)).lf_H \/ MEM (SOME a) (EL k (g::fs)).lf_Q) ==>
     a IN ld_slots A (DROP k (g::fs))` by
    (MATCH_MP_TAC (Q.INST [`m` |-> `1`, `old` |-> `f::fs`,
                          `A` |-> `A`, `lo` |-> `lo`] ld_focus_suffix_cons) >>
     qpat_assum `!k a. _ ==> _ IN ld_slots A (DROP k (f::fs))` mp_tac >>
     simp[rich_listTheory.DROP]) >>
  `ti' = EL 0 Y /\ 0 < LENGTH Y` by
    (qpat_assum `ld_prefix _ _ Y _ 0 _ _` mp_tac >>
     simp[NoAsms,ld_prefix_zero] >> strip_tac >> simp[listTheory.EL]) >>
  disj1_tac >>
  qexistsl [`stk`,`PG`,`step_prov PG G inst ss`,`step_taint inst s ss tn`,
    `fn`,`i`,`s1`,`t1`,`A`,`g::fs`,`N`,`Y`,`0`,`r::rs`,
    `step_prov PH H (EL 1 X) s'`,`step_taint (EL 1 X) t s' un`,
    `pfuel`,`g`,`A`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[NoAsms,HD,TL,listTheory.EL,EVERY_DEF,dload_prefix_zero] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `f.lf_supply = Sigma _` mp_tac >>
      qpat_assum `f.lf_fn = fn` (fn e1 =>
        qpat_assum `g.lf_fn = fn` (fn e2 =>
          qpat_assum `g.lf_supply = f.lf_supply` (fn e3 => simp[NoAsms,e1,e2,e3]))))
  >- (qpat_assum `!j a. _ ==> j IN P f.lf_fn.fn_name` mp_tac >>
      qpat_assum `f.lf_fn = fn` (fn e1 =>
        qpat_assum `g.lf_fn = fn` (fn e2 =>
          qpat_assum `g.lf_Q = f.lf_Q` (fn e3 => simp[NoAsms,e1,e2,e3]))))
  >- (rpt strip_tac >> rename1 `j < k` >>
      qpat_assum `!j k. _ ==> list_precedes (EL j (f::fs)).lf_fn.fn_name _ _`
        (qspecl_then [`j`,`k`] mp_tac) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
      qpat_assum `f.lf_fn = fn` (fn e1 =>
        qpat_assum `g.lf_fn = fn` (fn e2 =>
          Cases_on `j` >> Cases_on `k` >> simp[NoAsms,listTheory.EL,e1,e2])))
  >- (sym_tac >> first_assum ACCEPT_TAC)
  >- (qpat_assum `g.lf_supply = f.lf_supply` SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- (qpat_assum `g.lf_supply = f.lf_supply` SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- (qpat_assum `g.lf_supply = f.lf_supply` SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- simp[]
  >- simp[]
  >- simp[]
  >- (gen_tac >> rename1 `k < _ ==> _` >> strip_tac >>
      qpat_assum `!k. k < SUC (LENGTH rs) ==> (EL k (r::rs)).dr_scratch = _`
        (qspec_then `k` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `t1.vs_allocas = t0.vs_allocas` (fn th =>
        Cases_on `k` >> simp[NoAsms,listTheory.EL,th]))
  >- (qpat_assum `s1.vs_call_ctx = s.vs_call_ctx` SUBST1_TAC >> first_assum ACCEPT_TAC)
  >> qpat_assum `g.lf_src = s1` SUBST1_TAC >>
  qpat_assum `g.lf_tgt = t1` SUBST1_TAC >>
  simp[NoAsms,Abbr `s1`,Abbr `t1`] >>
  qpat_assum `ss.vs_gas_readings = s.vs_gas_readings` SUBST1_TAC >>
  qpat_assum `s'.vs_gas_readings = t0.vs_gas_readings` SUBST1_TAC >>
  qpat_assum `s.vs_gas_readings = t.vs_gas_readings` SUBST1_TAC >>
  qpat_assum `t0.vs_gas_readings = t.vs_gas_readings` SUBST1_TAC >>
  simp[NoAsms] >>
  qpat_assum `EVERY (\g. _ /\ LENGTH s.vs_gas_readings <= _) fs` mp_tac >>
  qpat_assum `s.vs_gas_readings = t.vs_gas_readings` (fn th => simp[NoAsms,th])
QED

Resume ld_frame_actual_occurrence[singleton_frame]:
  `X = [inst]` by (drule_all lowerDloadSafetyLocationsTheory.ld_envelope_ordinary >> simp[]) >>
  qpat_x_assum `X = [inst]` SUBST_ALL_TAC >>
  `h = 0` by fs[] >> qpat_x_assum `h = 0` SUBST_ALL_TAC >>
  qpat_x_assum `ld_prefix _ _ _ _ 0 _ _` (strip_assume_tac o SRULE[ld_prefix_zero]) >>
  qpat_x_assum `t = t0` SUBST_ALL_TAC >>
  qpat_x_assum `dload_prefix_match _ _ _ _ 0 _ _ _ _ _ _`
    (strip_assume_tac o SRULE[dload_prefix_match_def]) >>
  qpat_x_assum `H = H0` SUBST_ALL_TAC >> qpat_x_assum `un = un0` SUBST_ALL_TAC >>
  gvs[NoAsms] >>
  `?bb. lookup_block f.lf_tgt.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
        get_instruction bb f.lf_tgt.vs_inst_idx = SOME inst` by
    (irule active_inst_block_lookup >> simp[fn_labels_def]) >>
  `^ld_probe_stable lo P Sigma names fs f A A (f::fs)` by (simp[] >> metis_tac[]) >>
  `EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
             LENGTH f.lf_src.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings)
     (f::fs)` by simp[] >>
  `ld_envelope f.lf_supply f.lf_fn f.lf_src f.lf_src.vs_inst_idx [inst]
     f.lf_tgt.vs_inst_idx` by simp[] >>
  `gas_cut n vs f.lf_src` by
    (qpat_assum `gas_cut n vs f.lf_tgt` mp_tac >> simp[gas_cut_def]) >>
  drule ld_sync_source >> strip_tac >>
  `MEM inst (fn_insts f.lf_fn)` by metis_tac[ld_active_inst_member] >>
  drule_then assume_tac ld_sync_ptr_ok >>
  drule_then assume_tac ld_sync_labels >>
  qpat_assum `o1_safe_upto D lo n C vs`
    (strip_assume_tac o REWRITE_RULE[o1_safe_upto_def,o1_ptr_safe_upto_def]) >>
  qpat_assum `ptr_discipline_upto lo n C vs`
    (drule_all_then strip_assume_tac o cj 3 o REWRITE_RULE[ptr_discipline_upto_def]) >>
  drule lowerDloadPtrSupportTheory.frame_reachable_prov_supported >>
  disch_then (qspec_then `P` mp_tac) >>
  (impl_tac >- fs[EVERY_MEM]) >> strip_tac >>
  Cases_on `MEM inst.inst_opcode
      [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;COINBASE;
       TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
       CALLDATASIZE;RETURNDATASIZE;CODESIZE]`
  >- suspend "singleton_environment" >>
  Cases_on `MEM inst.inst_opcode [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET; SHL; SHR; SAR;
    ADD; SUB; ASSIGN; PARAM; RETPC_PARAM]`
  >- suspend "singleton_scalar" >>
  suspend "singleton_other_remaining"
QED

Resume ld_frame_actual_occurrence[singleton_environment]:
  `f.lf_tgt.vs_inst_idx = f.lf_tgt.vs_inst_idx` by simp[] >>
  drule_all_then (strip_assume_tac o BETA_RULE) ld_focus_environment_point_next >>
  `opaque_use_ok f.lf_fn` by fs[unitShapeDefsTheory.fn_shape_ok_def] >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by
    (qpat_assum `MEM inst.inst_opcode _` mp_tac >> pure_rewrite_tac[listTheory.MEM] >>
     strip_tac >> simp[]) >>
  `!v. MEM (Var v) inst.inst_operands ==>
     v IN (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v})` by
    metis_tac[dload_original_nonopaque_operands] >>
  rename1 `step_inst 0 C inst f.lf_src = OK ss` >>
  `?sg. step_inst fuel C inst f.lf_src = OK sg /\
    (!v. MEM v (fn_ir_vars f.lf_fn) ==>
      (lookup_var v (sg with vs_inst_idx := SUC f.lf_src.vs_inst_idx) = NONE <=>
       lookup_var v (s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx) = NONE)) /\
    dload_boundary_core (dyn_floor C vs) lo (r::rs)
      (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) stk)
      PG PH (step_prov PG G inst sg) (step_prov PH H0 inst s')
      (step_taint inst f.lf_src sg tn) (step_taint inst f.lf_tgt s' un0)
      (sg with vs_inst_idx := SUC f.lf_src.vs_inst_idx)
      (s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx) stk ds /\
    sg.vs_current_bb = f.lf_src.vs_current_bb /\
    sg.vs_prev_bb = f.lf_src.vs_prev_bb /\ sg.vs_inst_idx = f.lf_src.vs_inst_idx /\
    sg.vs_call_ctx = f.lf_src.vs_call_ctx /\
    s'.vs_current_bb = f.lf_tgt.vs_current_bb /\
    s'.vs_prev_bb = f.lf_tgt.vs_prev_bb /\ s'.vs_inst_idx = f.lf_tgt.vs_inst_idx /\
    s'.vs_allocas = f.lf_tgt.vs_allocas` by
    (let
       fun ghost_step th =
         drule_at (Pat `dload_boundary_core`) th >>
         disch_then (drule_at (Pat `step_inst`)) >>
         disch_then (drule_at (Pat `fn_ptr_ok`)) >>
         disch_then (qspecl_then [`set (fn_ir_vars f.lf_fn)`,`C`] mp_tac) >>
         simp[] >> (impl_tac >- metis_tac[fn_ir_vars_operand]) >>
         strip_tac >> rename1 `step_inst fuel C inst f.lf_src = OK u` >>
         qexists `u` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     in
       Cases_on `inst.inst_opcode = GAS`
       >- (ghost_step dload_boundary_core_gas_index >>
           qpat_assum `u = _ with <|vs_vars := _; vs_gas_readings := _|>` SUBST1_TAC >>
           qpat_assum `s' = _ with <|vs_vars := _; vs_gas_readings := _|>` SUBST1_TAC >>
           simp[NoAsms]) >>
       `MEM inst.inst_opcode
         [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
          COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
          CALLDATASIZE; RETURNDATASIZE; BLOCKHASH; BLOBHASH; CALLDATALOAD;
          BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH; CODESIZE; INITIAL_FMP]` by
         (qpat_assum `MEM inst.inst_opcode _` mp_tac >>
          pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
       ghost_step lowerDloadPtrEnvironmentReadTheory.dload_boundary_core_environment_read_index >>
       qpat_assum `u = _ with vs_vars := _` SUBST1_TAC >>
       qpat_assum `s' = _ with vs_vars := _` SUBST1_TAC >>
       simp[NoAsms]
     end) >>
  ld_frame_singleton_reset_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_scalar]:
  `f.lf_tgt.vs_inst_idx = f.lf_tgt.vs_inst_idx` by simp[] >>
  SUBGOAL_THEN
    ``MEM inst.inst_opcode
       [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
        ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET; ADD; SUB; SHL; SHR; SAR] \/
     MEM inst.inst_opcode [ASSIGN; RETPC_PARAM; PARAM]`` assume_tac
  >- (qpat_assum `MEM inst.inst_opcode (MUL::_)` mp_tac >>
      pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
  drule_all_then strip_assume_tac
    (CONV_RULE (TOP_DEPTH_CONV
       (HO_REWR_CONV UNWIND_THM2 ORELSEC Unwind.UNWIND_FORALL_CONV))
       ld_focus_arithmetic_binding_point_next) >>
  Cases_on `inst.inst_opcode = ASSIGN`
  >- suspend "singleton_assign" >>
  Cases_on `inst.inst_opcode = PARAM \/ inst.inst_opcode = RETPC_PARAM`
  >- suspend "singleton_param" >>
  `opaque_use_ok f.lf_fn` by fs[unitShapeDefsTheory.fn_shape_ok_def] >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by
    (qpat_assum `MEM inst.inst_opcode (MUL::_)` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
  `!v. MEM (Var v) inst.inst_operands ==>
     v IN (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v})` by
    metis_tac[dload_original_nonopaque_operands] >>
  Cases_on `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB`
  >- suspend "singleton_affine" >>
  Cases_on `MEM inst.inst_opcode [SHL; SHR; SAR]`
  >- suspend "singleton_shift_index" >>
  `MEM inst.inst_opcode [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET]` by
    (qpat_assum `MEM inst.inst_opcode (MUL::_)` mp_tac >>
     qpat_assum `~MEM inst.inst_opcode [SHL; SHR; SAR]` mp_tac >>
     qpat_assum `~(inst.inst_opcode = ADD \/ inst.inst_opcode = SUB)` mp_tac >>
     qpat_assum `~(inst.inst_opcode = PARAM \/ inst.inst_opcode = RETPC_PARAM)` mp_tac >>
     qpat_assum `inst.inst_opcode <> ASSIGN` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> pure_rewrite_tac[listTheory.MEM] >> metis_tac[]) >>
  drule_at (Pat `dload_boundary_core`) lowerDloadPtrScalarTheory.dload_boundary_core_scalar_index >>
  ld_frame_singleton_index_fields_tac >>
  ld_frame_singleton_scalar_fields_tac >>
  ld_frame_singleton_reset_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_assign]:
  `?op. inst.inst_operands = [op]` by
    (drule_all lowerDloadPtrOrdinaryTheory.assign_step_success >> metis_tac[]) >>
  `!v. MEM (Var v) inst.inst_operands ==> MEM v (fn_ir_vars f.lf_fn)` by
    (rpt strip_tac >> irule fn_ir_vars_operand >> qexists `inst` >> simp[]) >>
  `!out w. MEM out inst.inst_outputs /\
     out IN (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v}) /\
     MEM (Var w) inst.inst_operands ==>
     w IN (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v})` by
    metis_tac[lowerDloadPtrOrdinaryTheory.dload_assign_original_input_closed] >>
  drule_at (Pat `dload_boundary_core`) lowerDloadPtrOrdinaryTheory.dload_boundary_core_assign_tracked_index >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars f.lf_fn)`,`C`] mp_tac) >>
  (impl_tac >- (simp[IgnAsm `inst.inst_operands = [op]`] >>
     qpat_x_assum `!out w. _ ==> _ IN (_ DIFF _)` mp_tac >>
     simp[NoAsms, IgnAsm `inst.inst_operands = [op]`] >> metis_tac[])) >>
  strip_tac >> ld_frame_singleton_scalar_fields_tac >>
  ld_frame_singleton_reset_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_param]:
  `inst.inst_opcode = RETPC_PARAM ==>
     !out. MEM out inst.inst_outputs ==>
       out NOTIN (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v})` by
    (simp[] >> metis_tac[lowerDloadPtrParametersTheory.dload_parameter_retpc_output]) >>
  drule_at (Pat `dload_boundary_core`) lowerDloadPtrParametersTheory.dload_boundary_core_parameter_tracked_index >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars f.lf_fn)`,`C`] mp_tac) >>
  simp[] >> strip_tac >> ld_frame_singleton_scalar_fields_tac >>
  ld_frame_singleton_reset_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_affine]:
  drule_at (Pat `dload_boundary_core`) lowerDloadPtrAffineTheory.dload_boundary_core_affine >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars f.lf_fn)`,`C`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[fn_ir_vars_operand])) >>
  strip_tac >> rename1 `step_inst fuel C inst f.lf_src = OK sg` >>
  `!v. MEM v (fn_ir_vars f.lf_fn) ==>
     (lookup_var v (sg with vs_inst_idx := SUC f.lf_src.vs_inst_idx) = NONE <=>
      lookup_var v (s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx) = NONE)` by
    (qpat_assum `!v. MEM v (fn_ir_vars f.lf_fn) ==> (lookup_var v sg = NONE <=> _)` mp_tac >>
     simp[NoAsms,lookup_var_def]) >>
  qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ sg s' _ _`
    (fn hb => assume_tac
      (Q.INST [`si` |-> `SUC f.lf_src.vs_inst_idx`,
               `ti` |-> `SUC f.lf_tgt.vs_inst_idx`]
        (SPEC_ALL (MATCH_MP dload_boundary_core_index_update hb)))) >>
  ld_frame_singleton_scalar_fields_tac >>
  ld_frame_singleton_reset_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_shift_index]:
  drule_at (Pat `dload_boundary_core`) lowerDloadPtrShiftTheory.dload_boundary_core_shift_index >>
  ld_frame_singleton_index_fields_tac >>
  ld_frame_singleton_scalar_fields_tac >>
  ld_frame_singleton_reset_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_other_remaining]:
  Cases_on `MEM inst.inst_opcode [LOG;SSTORE;TSTORE]`
  >- suspend "singleton_log_store" >>
  suspend "singleton_remaining"
QED

Resume ld_frame_actual_occurrence[singleton_log_store]:
  `f.lf_tgt.vs_inst_idx = f.lf_tgt.vs_inst_idx` by simp[] >>
  drule_all_then (strip_assume_tac o BETA_RULE) ld_focus_log_store_point_next >>
  `inst.inst_outputs = [] /\ ~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET] /\
   ~about_to_revert f.lf_fn inst f.lf_src` by
    (qpat_assum `MEM inst.inst_opcode [LOG;SSTORE;TSTORE]` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >>
     fs[inst_wf_def,about_to_revert_def]) >>
  `opaque_use_ok f.lf_fn` by fs[unitShapeDefsTheory.fn_shape_ok_def] >>
  `!v. MEM (Var v) inst.inst_operands ==>
     v IN (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v})` by
    metis_tac[dload_original_nonopaque_operands] >>
  `~in_revert_forward f.lf_fn f.lf_src` by
    (`?b. lookup_block f.lf_src.vs_current_bb f.lf_fn.fn_blocks = SOME b /\
          get_instruction b f.lf_src.vs_inst_idx = SOME inst` by
       (irule active_inst_block_lookup >> simp[fn_labels_def]) >>
     simp[in_revert_forward_def] >> strip_tac >>
     drule_all_then strip_assume_tac memSafeRunTheory.revert_forward_at_opcode >>
     fs[]) >>
  `!v. op_taint tn (Var v) SUBSET {k | k < 32}` by
    (gen_tac >> drule lowerDloadPtrTaintBoundsTheory.dload_reachable_op_taint_bound >> simp[]) >>
  Cases_on `inst.inst_opcode = LOG`
  >- (drule_at (Pat `dload_boundary_core`) lowerDloadPtrLogTheory.dload_boundary_core_log >>
      suspend "singleton_log_ghost") >>
  `MEM inst.inst_opcode [SSTORE;TSTORE]` by fs[] >>
  drule_at (Pat `dload_boundary_core`) lowerDloadPtrStorageTheory.dload_boundary_core_storage_write >>
  suspend "singleton_store_ghost"
QED

Resume ld_frame_actual_occurrence[singleton_log_ghost]:
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars f.lf_fn)`,`C`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[fn_ir_vars_operand])) >>
  strip_tac >> rename1 `step_inst fuel C inst f.lf_src = OK sg` >>
  `sg.vs_current_bb = f.lf_src.vs_current_bb /\
   sg.vs_prev_bb = f.lf_src.vs_prev_bb /\ sg.vs_inst_idx = f.lf_src.vs_inst_idx /\
   sg.vs_call_ctx = f.lf_src.vs_call_ctx /\
   s'.vs_current_bb = f.lf_tgt.vs_current_bb /\
   s'.vs_prev_bb = f.lf_tgt.vs_prev_bb /\ s'.vs_inst_idx = f.lf_tgt.vs_inst_idx /\
   s'.vs_allocas = f.lf_tgt.vs_allocas` by
    (qpat_assum `sg = _ with vs_logs := _` SUBST1_TAC >>
     qpat_assum `s' = _ with vs_logs := _` SUBST1_TAC >> simp[NoAsms]) >>
  ld_frame_singleton_index_reset_tac >>
  ld_frame_singleton_reset_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_store_ghost]:
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars f.lf_fn)`,`C`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[fn_ir_vars_operand])) >>
  strip_tac >> rename1 `step_inst fuel C inst f.lf_src = OK sg` >>
  map_every (fn step => qpat_assum step
    (mp_then (Pat `step_inst`) mp_tac
      lowerDloadPtrJointStorageTheory.dload_storage_write_step_fields) >>
    simp[] >> strip_tac)
    [`step_inst fuel C inst f.lf_src = OK sg`, `step_inst fuel C' inst f.lf_tgt = OK s'`] >>
  ld_frame_singleton_index_reset_tac >>
  ld_frame_singleton_reset_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_remaining]:
  Cases_on `MEM inst.inst_opcode
    [BLOCKHASH;BLOBHASH;CALLDATALOAD;BALANCE;SELFBALANCE;EXTCODESIZE;EXTCODEHASH;SLOAD;TLOAD]`
  >- suspend "singleton_observational_read" >>
  suspend "singleton_after_reads"
QED

Resume ld_frame_actual_occurrence[singleton_observational_read]:
  `tn.t_var = f.lf_tv` by (sym_tac >> first_assum ACCEPT_TAC) >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  `step_inst_base inst f.lf_tgt = OK s'` by
    metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := s';
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss s' /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss s' /\
    ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE =
      step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H) inst ss /\
    ss.vs_allocas = f.lf_src.vs_allocas /\ ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\ ss.vs_prev_bb = f.lf_src.vs_prev_bb /\
    s'.vs_allocas = f.lf_tgt.vs_allocas /\ s'.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    s'.vs_current_bb = f.lf_tgt.vs_current_bb /\ s'.vs_prev_bb = f.lf_tgt.vs_prev_bb` by
    (let
       fun finish effect =
         drule_all effect >>
         disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q`
           (qx_choose_then `ss` strip_assume_tac)) >>
         qexists `ss` >> rpt conj_tac >> first_assum ACCEPT_TAC
     in
       Cases_on `MEM inst.inst_opcode [BLOCKHASH;BLOBHASH;CALLDATALOAD]`
       >- finish lowerDloadSafetyKeyedEnvironmentReadEffectsTheory.ld_keyed_environment_read_effect >>
       Cases_on `MEM inst.inst_opcode [BALANCE;SELFBALANCE;EXTCODESIZE;EXTCODEHASH]`
       >- finish lowerDloadSafetyAccountReadEffectsTheory.ld_account_read_effect >>
       `MEM inst.inst_opcode [SLOAD;TLOAD]` by
         (qpat_assum `MEM inst.inst_opcode (BLOCKHASH::_)` mp_tac >>
          qpat_assum `~MEM inst.inst_opcode (BLOCKHASH::_)` mp_tac >>
          qpat_assum `~MEM inst.inst_opcode (BALANCE::_)` mp_tac >>
          pure_rewrite_tac[listTheory.MEM] >> metis_tac[NoAsms]) >>
       finish lowerDloadSafetyStorageReadEffectsTheory.ld_storage_read_effect
     end) >>
  suspend "singleton_read_advance"
QED

Resume ld_frame_actual_occurrence[singleton_read_advance]:
  `step_inst 0 C inst f.lf_src = OK ss /\ step_inst fuel C inst f.lf_src = OK ss` by
    simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  qabbrev_tac `Hr = set_prov f.lf_H inst.inst_outputs NONE` >>
  qabbrev_tac `sn = ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx` >>
  qabbrev_tac `tq = s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx` >>
  qabbrev_tac `g = f with <|lf_src := sn; lf_tgt := tq; lf_H := Hr;
                           lf_tv := (step_taint inst f.lf_src ss tn).t_var|>` >>
  `~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst f.lf_src = []` by
    (qpat_assum `MEM inst.inst_opcode (BLOCKHASH::_)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> pure_rewrite_tac[listTheory.MEM] >> strip_tac >>
     simp[is_alloca_op_def,venomEffectsTheory.write_effects_def,
          venomEffectsTheory.empty_effects_def,codegenRelTheory.source_memory_write_ranges_def]) >>
  `ld_ghost_ok (dyn_floor C vs) A Hr (step_prov PG G inst ss)` by
    (irule lowerDloadSafetyAmbientTheory.ld_sync_ghost_step >>
     goal_assum (drule_at Any) >> simp[Abbr `Hr`] >> metis_tac[]) >>
  `!a. a IN FRANGE Hr ==> a IN FDOM A` by
    (simp[Abbr `Hr`] >> rpt strip_tac >>
     drule (SRULE [pred_setTheory.SUBSET_DEF]
       (Q.INST [`q` |-> `NONE`] lowerDloadSafetyUpdatesTheory.ld_set_prov_range)) >>
     simp[] >> metis_tac[ld_global_selected, MEM]) >>
  `ld_dyn_agree (dyn_floor C vs) (step_taint inst f.lf_src ss tn).t_mem
     ss.vs_memory s'.vs_memory` by
    (irule lowerDloadSafetyAmbientTheory.ld_sync_dyn_agree_unwritten >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  suspend "singleton_read_fetch"
QED

Resume ld_frame_actual_occurrence[singleton_read_fetch]:
  `ld_image f = FST (lower_dload_function_supply f.lf_supply f.lf_fn)` by
    simp[ld_image_def] >>
  `tq.vs_current_bb = f.lf_src.vs_current_bb /\
   tq.vs_inst_idx = SUC f.lf_tgt.vs_inst_idx` by
    (drule ld_sync_control >> simp[Abbr `tq`]) >>
  `?i Y. active_inst f.lf_fn i sn /\
         ld_envelope f.lf_supply f.lf_fn sn (SUC f.lf_src.vs_inst_idx) Y
           (SUC f.lf_tgt.vs_inst_idx) /\ 0 < LENGTH Y /\ ti' = EL 0 Y` by
    (qpat_assum `ld_envelope f.lf_supply _ _ _ [inst] _`
       (mp_then Any mp_tac lowerDloadSafetyLocationsTheory.ld_envelope_successor_head) >>
     disch_then (qspecl_then [`ti'`,`ss`,`tq`,`ld_image f`] mp_tac) >>
     simp[arithmeticTheory.ADD1,Abbr `sn`]) >>
  `ld_vars P A g` by
    (mp_tac (lowerDloadSafetyAdvanceTheory.ld_vars_inst_indices |> Q.INST
       [`f` |-> `f with <|lf_src := ss; lf_tgt := s'; lf_H := Hr;
                         lf_tv := (step_taint inst f.lf_src ss tn).t_var|>`,
        `i` |-> `SUC f.lf_src.vs_inst_idx`, `j` |-> `SUC f.lf_tgt.vs_inst_idx`]) >>
     simp[Abbr `g`,Abbr `sn`,Abbr `tq`,Abbr `Hr`]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst f.lf_src ss tn)
     f.lf_fn i sn tq A (g::fs) N /\ ld_global lo A (g::fs)` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ inst _ _ A (f::fs) _`
       (mp_then Any mp_tac lowerDloadSafetyAdvanceTheory.ld_sync_ordinary_advance) >>
     simp[Abbr `sn`,Abbr `tq`,Abbr `g`] >> metis_tac[]) >>
  suspend "singleton_read_ghost"
QED

Resume ld_frame_actual_occurrence[singleton_read_ghost]:
  `opaque_use_ok f.lf_fn` by fs[unitShapeDefsTheory.fn_shape_ok_def] >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by
    (qpat_assum `MEM inst.inst_opcode (BLOCKHASH::_)` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
  `!v. MEM (Var v) inst.inst_operands ==>
     v IN (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v})` by
    metis_tac[dload_original_nonopaque_operands] >>
  `?sg. step_inst fuel C inst f.lf_src = OK sg /\
    (!v. MEM v (fn_ir_vars f.lf_fn) ==>
          (lookup_var v sg = NONE <=> lookup_var v s' = NONE)) /\
    dload_boundary_core (dyn_floor C vs) lo (r::rs)
      (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) stk)
      PG PH (step_prov PG G inst sg) (step_prov PH H0 inst s')
      (step_taint inst f.lf_src sg tn) (step_taint inst f.lf_tgt s' un0) sg s' stk ds /\
    sg = f.lf_src with vs_vars := sg.vs_vars /\
    s' = f.lf_tgt with vs_vars := s'.vs_vars` by
  (let
     fun ghost_step th =
       drule_at (Pat `dload_boundary_core`) th >>
       disch_then (fn h => qpat_assum `step_inst fuel C' inst f.lf_tgt = OK s'`
         (mp_then (Pat `step_inst`) mp_tac h)) >>
       disch_then (drule_at (Pat `fn_ptr_ok`)) >>
       disch_then (qspecl_then [`set (fn_ir_vars f.lf_fn)`,`C`] mp_tac) >>
       simp[] >> (impl_tac >- metis_tac[fn_ir_vars_operand]) >>
       simp[]
   in
     Cases_on `MEM inst.inst_opcode [SLOAD;TLOAD]`
     >- ghost_step lowerDloadPtrStorageTheory.dload_boundary_core_storage_read >>
     `MEM inst.inst_opcode
       [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
        COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
        CALLDATASIZE; RETURNDATASIZE; BLOCKHASH; BLOBHASH; CALLDATALOAD;
        BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH; CODESIZE; INITIAL_FMP]` by
       (qpat_assum `~MEM inst.inst_opcode [SLOAD;TLOAD]` mp_tac >>
        qpat_assum `MEM inst.inst_opcode (BLOCKHASH::_)` mp_tac >>
        pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
     ghost_step lowerDloadPtrEnvironmentReadTheory.dload_boundary_core_environment_read
   end) >>
  suspend "singleton_read_fields"
QED

Resume ld_frame_actual_occurrence[singleton_read_fields]:
  rename1 `step_inst fuel C inst f.lf_src = OK sg` >>
  `sg.vs_current_bb = f.lf_src.vs_current_bb /\
   sg.vs_prev_bb = f.lf_src.vs_prev_bb /\ sg.vs_inst_idx = f.lf_src.vs_inst_idx /\
   sg.vs_call_ctx = f.lf_src.vs_call_ctx /\
   s'.vs_current_bb = f.lf_tgt.vs_current_bb /\
   s'.vs_prev_bb = f.lf_tgt.vs_prev_bb /\ s'.vs_inst_idx = f.lf_tgt.vs_inst_idx /\
   s'.vs_allocas = f.lf_tgt.vs_allocas` by
    (qpat_assum `sg = _ with vs_vars := _` SUBST1_TAC >>
     qpat_assum `s' = _ with vs_vars := _` SUBST1_TAC >> simp[NoAsms]) >>
  map_every (fn q => qpat_x_assum q (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]))
    [`Abbrev (sn = _)`, `Abbrev (tq = _)`] >>
  ld_frame_singleton_index_reset_tac >>
  ld_frame_singleton_reset_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_after_reads]:
  Cases_on `MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ]`
  >- suspend "singleton_classified_read" >>
  Cases_on `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`
  >- suspend "singleton_identity" >>
  suspend "singleton_after_identity"
QED

Resume ld_frame_actual_occurrence[singleton_classified_read]:
  `opaque_use_ok f.lf_fn` by fs[fn_shape_ok_def] >>
  `MEM inst.inst_opcode [MLOAD;ILOAD] ==> ~in_revert_forward f.lf_fn f.lf_src` by
    (strip_tac >> irule concretizeLayoutLocalReturnTheory.active_inst_not_revert_forward >>
     conj_tac >- simp[fn_labels_def] >> qexists `inst` >> simp[] >>
     qpat_assum `MEM inst.inst_opcode [MLOAD;ILOAD]` mp_tac >>
     pure_rewrite_tac[MEM] >> strip_tac >> simp[]) >>
  drule_all ld_frame_classified_read_boundary >>
  disch_then (qspec_then `C` (qx_choose_then `ss` strip_assume_tac)) >>
  drule_at (Pat `ld_sync`)
    (Q.INST [`f0` |-> `f`, `A0` |-> `A`] ld_frame_classified_read_sync) >>
  disch_then (drule_at (Pat `step_inst fuel C' inst f.lf_tgt = OK s'`)) >>
  disch_then (drule_at (Pat `active_inst (ld_image f) ti' _`)) >>
  disch_then (qspecl_then [`names`,`Sigma`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `sg` (qx_choose_then `g`
    (qx_choose_then `i` (qx_choose_then `Hr` (strip_assume_tac o BETA_RULE))))) >>
  `sg = ss` by
    (qpat_assum `step_inst fuel C inst f.lf_src = OK sg` mp_tac >>
     qpat_assum `step_inst fuel C inst f.lf_src = OK ss` mp_tac >> simp[NoAsms]) >>
  qpat_x_assum `sg = ss` SUBST_ALL_TAC >>
  `ss.vs_current_bb = f.lf_src.vs_current_bb /\
   ss.vs_prev_bb = f.lf_src.vs_prev_bb /\ ss.vs_inst_idx = f.lf_src.vs_inst_idx /\
   s'.vs_current_bb = f.lf_tgt.vs_current_bb /\
   s'.vs_prev_bb = f.lf_tgt.vs_prev_bb /\ s'.vs_inst_idx = f.lf_tgt.vs_inst_idx /\
   s'.vs_allocas = f.lf_tgt.vs_allocas` by
    (qpat_assum `ss = _ with vs_vars := _` SUBST1_TAC >>
     qpat_assum `s' = _ with vs_vars := _` SUBST1_TAC >> simp[NoAsms]) >>
  ld_frame_singleton_index_boundary_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_identity]:
  `opaque_use_ok f.lf_fn` by fs[unitShapeDefsTheory.fn_shape_ok_def] >>
  drule_all ld_frame_identity_boundary >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  SUBGOAL_THEN ``?ss. ss = f.lf_src`` (qx_choose_then `ss` assume_tac)
  >- (qexists_tac `f.lf_src` >> simp[]) >>
  `step_inst fuel C inst f.lf_src = OK ss /\
   ss.vs_current_bb = f.lf_src.vs_current_bb /\
   ss.vs_prev_bb = f.lf_src.vs_prev_bb /\ ss.vs_inst_idx = f.lf_src.vs_inst_idx /\
   ss.vs_call_ctx = f.lf_src.vs_call_ctx /\
   s'.vs_current_bb = f.lf_tgt.vs_current_bb /\
   s'.vs_prev_bb = f.lf_tgt.vs_prev_bb /\ s'.vs_inst_idx = f.lf_tgt.vs_inst_idx /\
   s'.vs_allocas = f.lf_tgt.vs_allocas` by simp[] >>
  `!v. MEM v (fn_ir_vars f.lf_fn) ==>
     (lookup_var v (ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx) = NONE <=>
      lookup_var v (s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx) = NONE)` by
    (qpat_assum `!v. MEM v (fn_ir_vars f.lf_fn) ==> (lookup_var v (f.lf_src with vs_inst_idx := _) = NONE <=> _)` mp_tac >>
     qpat_assum `ss = f.lf_src` (fn eq => simp[NoAsms,eq])) >>
  `dload_boundary_core (dyn_floor C vs) lo (r::rs)
     (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v})
     (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) stk)
     PG PH (step_prov PG G inst ss) (step_prov PH H0 inst s')
     (step_taint inst f.lf_src ss tn) (step_taint inst f.lf_tgt s' un0)
     (ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx)
     (s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx) stk ds` by
    (qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _
        (f.lf_src with vs_inst_idx := _) (s' with vs_inst_idx := _) _ _` mp_tac >>
     qpat_assum `ss = f.lf_src` (fn eq => simp[NoAsms,eq])) >>
  suspend "singleton_identity_sync"
QED

Resume ld_frame_actual_occurrence[singleton_identity_sync]:
  `ALL_DISTINCT (MAP (\b. b.bb_label) f.lf_fn.fn_blocks)` by simp[fn_labels_def] >>
  `ld_vars P A (f with <|lf_src := f.lf_src; lf_tgt := s'; lf_H := f.lf_H;
                      lf_tv := (step_taint inst f.lf_src f.lf_src tn).t_var|>)` by
    (drule ld_sync_active >> simp[NoAsms] >> strip_tac >>
     `f with <|lf_src := f.lf_src; lf_tgt := s'; lf_H := f.lf_H;
          lf_tv := (step_taint inst f.lf_src f.lf_src tn).t_var|> = f` by
       simp[ld_frame_component_equality] >> simp[]) >>
  `f.lf_tv = tn.t_var /\ ld_vars P A f` by
    (drule ld_sync_active >> simp[NoAsms] >> strip_tac >> simp[]) >>
  `f with <|lf_src := f.lf_src; lf_tgt := f.lf_tgt; lf_H := f.lf_H;
       lf_tv := tn.t_var|> = f` by simp[ld_frame_component_equality] >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_ghosts >> simp[NoAsms] >> strip_tac >>
  drule ld_sync_dyn_agree >> strip_tac >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  mp_tac (Q.INST [`C'` |-> `C'`, `fuel` |-> `fuel`,`j` |-> `ti'`,
                  `fn` |-> `f.lf_fn`, `s` |-> `f.lf_src`, `t` |-> `f.lf_tgt`,
                  `u` |-> `s'`, `H'` |-> `f.lf_H`, `f0` |-> `f`, `A0` |-> `A`]
    (SPEC_ALL (BETA_RULE ld_frame_singleton_sync_next))) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[])) >>
  disch_then (qx_choose_then `g` (qx_choose_then `i` strip_assume_tac)) >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_after_identity]:
  Cases_on `MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]`
  >- suspend "singleton_external" >>
  suspend "singleton_after_external"
QED

Resume ld_frame_actual_occurrence[singleton_external]:
  `~in_revert_forward f.lf_fn f.lf_src` by
    (irule concretizeLayoutLocalReturnTheory.active_inst_not_revert_forward >>
     conj_tac >- simp[fn_labels_def] >> qexists_tac `inst` >>
     qpat_assum `MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
  `opaque_use_ok f.lf_fn` by fs[unitShapeDefsTheory.fn_shape_ok_def] >>
  drule_all ld_frame_external_boundary >>
  disch_then (qspec_then `C` (qx_choose_then `sg` strip_assume_tac)) >>
  drule_all (BETA_RULE ld_frame_external_effect) >>
  disch_then (qx_choose_then `ss` (qx_choose_then `Hr` strip_assume_tac)) >>
  `sg = ss` by
    (qpat_assum `step_inst fuel C inst f.lf_src = OK sg` mp_tac >>
     qpat_assum `step_inst 0 C inst f.lf_src = OK ss` mp_tac >>
     qpat_assum `inst.inst_opcode <> INVOKE` mp_tac >>
     simp[NoAsms,venomExecSemanticsTheory.step_inst_non_invoke]) >>
  qpat_x_assum `sg = ss` SUBST_ALL_TAC >>
  ld_frame_singleton_external_sync_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_after_external]:
  Cases_on `MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY]`
  >- suspend "singleton_copy" >>
  suspend "singleton_after_copy"
QED

Resume ld_frame_actual_occurrence[singleton_copy]:
  Cases_on `in_revert_forward f.lf_fn f.lf_src`
  >- suspend "singleton_terminal_copy" >>
  `inst.inst_outputs = []` by
    (qpat_assum `MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY]` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> fs[inst_wf_def]) >>
  `opaque_use_ok f.lf_fn` by fs[unitShapeDefsTheory.fn_shape_ok_def] >>
  drule_all ld_frame_public_copy_boundary >>
  disch_then (qspec_then `C` (qx_choose_then `sg` strip_assume_tac)) >>
  drule_all_then strip_assume_tac ld_frame_slots >>
  drule_all_then (qx_choose_then `ss` (qx_choose_then `Hr` strip_assume_tac))
    lowerDloadPublicCopyPointEffectTheory.ld_sync_public_copy_effect_at >>
  `sg = ss` by
    (qpat_assum `step_inst fuel C inst f.lf_src = OK sg` mp_tac >>
     qpat_assum `step_inst fuel C inst f.lf_src = OK ss` mp_tac >> simp[NoAsms]) >>
  qpat_x_assum `sg = ss` SUBST_ALL_TAC >>
  `ld_ghost_ok (dyn_floor C vs) A Hr (step_prov PG G inst ss)` by
    (irule ld_sync_ghost_step >> goal_assum (drule_at Any) >> metis_tac[]) >>
  ld_frame_singleton_external_sync_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_terminal_copy]:
  `inst.inst_opcode = RETURNDATACOPY` by
    (`?bb. lookup_block f.lf_src.vs_current_bb f.lf_fn.fn_blocks = SOME bb /\
           get_instruction bb f.lf_src.vs_inst_idx = SOME inst` by
       (irule active_inst_block_lookup >> simp[fn_labels_def]) >>
     qpat_x_assum `in_revert_forward f.lf_fn f.lf_src` mp_tac >>
     simp[in_revert_forward_def] >> strip_tac >>
     drule_all_then strip_assume_tac memSafeRunTheory.revert_forward_at_opcode >>
     qpat_x_assum `MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY]` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> fs[]) >>
  `?dst off sz. inst.inst_operands = [dst;off;sz]` by
    (qpat_assum `step_inst fuel C' inst f.lf_tgt = OK s'` mp_tac >>
     qpat_assum `inst.inst_opcode = RETURNDATACOPY` (fn eq =>
       simp[NoAsms,eq,venomExecSemanticsTheory.step_inst_non_invoke,
         venomExecSemanticsTheory.step_inst_base_opcode_eqs,AllCaseEqs()]) >>
     metis_tac[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) f.lf_fn.fn_blocks) /\
   ir_supply_covers_fn (Sigma f.lf_fn.fn_name) f.lf_fn` by
    (simp[fn_labels_def] >> metis_tac[]) >>
  `in_revert_forward (ld_image f) f.lf_tgt` by
    (irule dload_control_source_forward_copy >>
     simp[] >> qexistsl_tac [`C`,`f.lf_fn`,`inst`,`Sigma f.lf_fn.fn_name`,`f.lf_src`] >> simp[]) >>
  `gas_cut n vs f.lf_src /\ ptr_discipline_upto lo n C vs` by
    fs[gas_cut_def,o1_safe_upto_def,o1_ptr_safe_upto_def] >>
  `!v. v IN set (fn_ir_vars f.lf_fn) ==>
     (lookup_var v f.lf_src = NONE <=> lookup_var v f.lf_tgt = NONE)` by simp[] >>
  `in_revert_forward (ld_image f) f.lf_tgt \/ about_to_revert (ld_image f) inst f.lf_tgt` by simp[] >>
  drule_at (Pat `dload_boundary_core`) ld_frame_copy_terminal_entry >>
  disch_then (drule_at (Pat `dload_control_match`)) >>
  disch_then (drule_at (Pat `step_inst`)) >>
  simp[fn_labels_def] >>
  disch_then (qspecl_then [`vs`,`n`,`P`,`C`] mp_tac) >> simp[] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  suspend "singleton_terminal_copy_finish"
QED

Resume ld_frame_actual_occurrence[singleton_terminal_copy_finish]:
  markerLib.RESUME_TAC >>
  `ti' = HD mid` by
    (qpat_assum `active_inst (ld_image f) ti' _`
       (mp_then Any mp_tac fmpStageBlockSimCodeTheory.active_inst_unique) >>
     disch_then (qspec_then `HD mid` mp_tac) >> simp[fn_labels_def]) >>
  `s''.vs_gas_readings = f.lf_src.vs_gas_readings /\ s'.vs_gas_readings = f.lf_tgt.vs_gas_readings` by
    (qpat_assum `inst.inst_opcode = RETURNDATACOPY` (fn opcode =>
       let fun readings step = MATCH_ACCEPT_TAC
         (MATCH_MP ld_frame_terminal_copy_readings (CONJ opcode step))
       in
         conj_tac
         >- qpat_assum `step_inst fuel C inst f.lf_src = OK s''` readings
         >- qpat_assum `step_inst fuel C' inst f.lf_tgt = OK s'` readings
       end)) >>
  `ctx_has_dalloca C ==> allocas_below_fmp (s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx)` by
    (strip_tac >>
     irule ld_frame_terminal_copy_below >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[ld_frame_boundary_below_fmp]) >>
  disj2_tac >>
  qrefinel [`stk`,`PG`,`step_prov PG G inst s''`,`step_taint inst f.lf_src s'' tn`,
    `f.lf_fn`,`s'' with vs_inst_idx := SUC f.lf_src.vs_inst_idx`,`r::rs`,`bb'`,`tb`,`bs`,`bt`,`mid`,`SUC f.lf_src.vs_inst_idx`,
    `SUC f.lf_tgt.vs_inst_idx`,`0`] >>
  simp[listTheory.EL] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  Cases_on `mid` >> gvs[]
QED

Resume ld_frame_actual_occurrence[singleton_after_copy]:
  Cases_on `inst.inst_opcode = DALLOCA`
  >- suspend "singleton_dalloca" >>
  suspend "singleton_after_dalloca"
QED

Resume ld_frame_actual_occurrence[singleton_dalloca]:
  `ctx_has_dalloca C` by
    (simp[ctx_has_dalloca_def,EXISTS_MEM] >> metis_tac[]) >>
  `w2n vs.vs_initial_fmp <= w2n f.lf_src.vs_fmp` by
    (drule ptrDisciplineEmptyTaintTheory.frame_reachable_initial_fmp >>
     simp[allocas_below_fmp_def] >> metis_tac[allocas_below_fmp_def]) >>
  `dyn_floor C vs <= w2n f.lf_src.vs_fmp` by simp[dyn_floor_def] >>
  `opaque_use_ok f.lf_fn` by fs[unitShapeDefsTheory.fn_shape_ok_def] >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by simp[] >>
  `!v. MEM (Var v) inst.inst_operands ==>
     v IN (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v}) /\
     v IN set (fn_ir_vars f.lf_fn)` by
    (qpat_assum `opaque_use_ok f.lf_fn` (fn opaque =>
       qpat_assum `MEM inst (fn_insts f.lf_fn)` (fn member =>
         qpat_assum `~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]`
           (fn ordinary =>
             mp_tac (MATCH_MP dload_original_nonopaque_operands
               (CONJ opaque (CONJ member ordinary)))))) >>
     simp[]) >>
  drule_at (Pat `dload_boundary_core`) lowerDloadPtrDallocaTheory.dload_boundary_core_dalloca >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars f.lf_fn)`,`C`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `sg` strip_assume_tac) >>
  drule_all_then (qx_choose_then `ss` (qx_choose_then `Hr` strip_assume_tac))
    lowerDloadOrdinaryEndpointTheory.ld_sync_dalloca_effect_at >>
  `sg = ss` by
    (qpat_assum `step_inst fuel C inst f.lf_src = OK sg` mp_tac >>
     qpat_assum `step_inst fuel C inst f.lf_src = OK ss` mp_tac >> simp[NoAsms]) >>
  qpat_x_assum `sg = ss` SUBST_ALL_TAC >>
  `ss.vs_inst_idx = f.lf_src.vs_inst_idx /\ s'.vs_inst_idx = f.lf_tgt.vs_inst_idx` by
    (qpat_assum `ss = f.lf_src with <|vs_vars := _; vs_fmp := _|>` SUBST1_TAC >>
     qpat_assum `s' = f.lf_tgt with <|vs_vars := _; vs_fmp := _|>` SUBST1_TAC >> simp[NoAsms]) >>
  ld_frame_singleton_index_boundary_tac >>
  ld_frame_singleton_external_sync_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_after_dalloca]:
  Cases_on `MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY]`
  >- suspend "singleton_memory_write" >>
  suspend "singleton_after_memory_write"
QED

Resume ld_frame_actual_occurrence[singleton_memory_write]:
  drule_all_then strip_assume_tac ld_frame_slots >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
     b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs /\ c+sz < dimword(:256)` by
    metis_tac[] >>
  `~in_revert_forward f.lf_fn f.lf_src` by
    (irule concretizeLayoutLocalReturnTheory.active_inst_not_revert_forward >>
     conj_tac >- simp[fn_labels_def] >> qexists `inst` >>
     qpat_assum `MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY]` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
  drule lowerDloadMemoryWritePointEffectTheory.ld_sync_memory_write_effect_at >>
  disch_then (fn h => qpat_assum `step_inst fuel C' inst f.lf_tgt = OK s'`
    (mp_then (Pat `step_inst`) mp_tac h)) >>
  (impl_tac >- (simp[] >> gvs[])) >>
  disch_then (qx_choose_then `ss` strip_assume_tac) >>
  qabbrev_tac `Hr = f.lf_H` >>
  `Hr = f.lf_H` by simp[Abbr `Hr`] >>
  `inst.inst_outputs = []` by
    (qpat_assum `inst_wf inst` mp_tac >>
     qpat_assum `MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY]` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[inst_wf_def]) >>
  `opaque_use_ok f.lf_fn` by
    (qpat_assum `fn_shape_ok f.lf_fn` mp_tac >>
     simp[NoAsms,unitShapeDefsTheory.fn_shape_ok_def]) >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by
    (qpat_assum `MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY]` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
  `!v. MEM (Var v) inst.inst_operands ==>
     v IN (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v})` by
    (rpt strip_tac >> drule_all dload_original_nonopaque_operands >> simp[]) >>
  Cases_on `inst.inst_opcode = MSTORE`
  >- suspend "singleton_mstore" >>
  Cases_on `inst.inst_opcode = MSTORE8`
  >- suspend "singleton_mstore8" >>
  suspend "singleton_mcopy"
QED

val ld_frame_write_boundary = fn th =>
  drule_at (Pat `dload_boundary_core`) th >>
  disch_then (fn h => qpat_assum `step_inst fuel C' inst f.lf_tgt = OK s'`
    (mp_then (Pat `step_inst`) mp_tac h)) >>
  disch_then (drule_at (Pat `fn_ptr_ok`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars f.lf_fn)`,`C`] mp_tac);

Resume ld_frame_actual_occurrence[singleton_mstore]:
  `!op. MEM op inst.inst_operands ==> op_taint tn op SUBSET {k | k < 32}` by
    (gen_tac >> strip_tac >>
     qpat_assum `frame_reachable vs C stk PG G tn _ _ _`
       (mp_then Any irule lowerDloadPtrTaintBoundsTheory.dload_reachable_op_taint_bound)) >>
  ld_frame_write_boundary lowerDloadPtrMemoryStoreTheory.dload_boundary_core_mstore >>
  (impl_tac >- ld_frame_singleton_write_premises_tac) >>
  strip_tac >> ld_frame_singleton_memory_write_finish_tac >>
  ld_frame_singleton_index_boundary_tac >>
  ld_frame_singleton_external_sync_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_mstore8]:
  ld_frame_write_boundary lowerDloadPtrByteStoreTheory.dload_boundary_core_mstore8 >>
  (impl_tac >- ld_frame_singleton_write_premises_tac) >>
  strip_tac >> ld_frame_singleton_memory_write_finish_tac >>
  ld_frame_singleton_index_boundary_tac >>
  ld_frame_singleton_external_sync_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_mcopy]:
  `inst.inst_opcode = MCOPY` by
    (qpat_assum `MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY]` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
  ld_frame_write_boundary lowerDloadPtrMCopyTheory.dload_boundary_core_mcopy >>
  (impl_tac >- ld_frame_singleton_write_premises_tac) >>
  strip_tac >> ld_frame_singleton_memory_write_finish_tac >>
  ld_frame_singleton_index_boundary_tac >>
  ld_frame_singleton_external_sync_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_after_memory_write]:
  Cases_on `MEM inst.inst_opcode [ISTORE;SHA3]`
  >- suspend "singleton_residual_data" >>
  suspend "singleton_after_residual_data"
QED

Resume ld_frame_actual_occurrence[singleton_residual_data]:
  drule_all_then strip_assume_tac ld_frame_slots >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_dyn_agree >> strip_tac >>
  drule ld_sync_ghosts >> simp[Excl "MEM"] >> strip_tac >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected,listTheory.MEM] >>
  `~in_revert_forward f.lf_fn f.lf_src` by
    (irule concretizeLayoutLocalReturnTheory.active_inst_not_revert_forward >>
     conj_tac >- simp[fn_labels_def] >> qexists `inst` >>
     qpat_assum `MEM inst.inst_opcode [ISTORE;SHA3]` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
  `opaque_use_ok f.lf_fn` by
    (qpat_assum `fn_shape_ok f.lf_fn` mp_tac >>
     simp[NoAsms,unitShapeDefsTheory.fn_shape_ok_def]) >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by
    (qpat_assum `MEM inst.inst_opcode [ISTORE;SHA3]` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> strip_tac >> simp[]) >>
  `!v. MEM (Var v) inst.inst_operands ==>
     v IN (set (fn_ir_vars f.lf_fn) DIFF {v | retpc_var f.lf_fn v})` by
    (rpt strip_tac >> drule_all dload_original_nonopaque_operands >> simp[]) >>
  `!v. MEM (Var v) inst.inst_operands ==> MEM v (fn_ir_vars f.lf_fn)` by
    (qpat_assum `!v. MEM (Var v) inst.inst_operands ==> v IN _ DIFF _` mp_tac >>
     simp[NoAsms,pred_setTheory.IN_DIFF] >> metis_tac[NoAsms]) >>
  Cases_on `inst.inst_opcode = ISTORE`
  >- suspend "singleton_istore" >>
  `inst.inst_opcode = SHA3` by fs[] >>
  suspend "singleton_sha3"
QED

Resume ld_frame_actual_occurrence[singleton_istore]:
  drule ld_sync_maps >> strip_tac >>
  drule ld_sync_slots >> strip_tac >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
                b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs` by metis_tac[] >>
  `step_inst_base inst f.lf_tgt = OK s'` by metis_tac[step_inst_non_invoke] >>
  `tn.t_var = f.lf_tv` by (sym_tac >> first_assum ACCEPT_TAC) >>
  `MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE]` by simp[] >>
  drule_all lowerDloadMemoryWritePointEffectTheory.ld_write2_operands >> strip_tac >>
  rename1 `inst.inst_operands = [addr; value]` >>
  `op_prov f.lf_H addr = NONE /\ op_prov f.lf_H value = NONE` by
    (conj_tac >>
     (irule lowerDloadSafetyImmutableWriteCoverageTheory.ld_istore_operand_unselected >> conj_tac
      >- (qexists_tac `inst` >> simp[])
      >> qexistsl [`A`,`P`] >> simp[])) >>
  `word_agree_except (op_taint tn value) x y` by
    (irule lowerDloadMemoryWritePointEffectTheory.ld_write_scalar_observation >>
     qexistsl [`A`,`P`,`f`,`inst`] >>
     qpat_assum `inst.inst_opcode = ISTORE` (rewrite_tac o single) >>
     qpat_assum `inst.inst_operands = [addr;value]` (rewrite_tac o single) >>
     simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `op_taint tn addr = {}` by metis_tac[lowerDloadMemoryWritePointEffectTheory.ld_write2_taint] >>
  `dst = dst'` by
    (irule (cj 1 lowerDloadMemoryWritePointEffectTheory.ld_write_address_observation) >>
     qexistsl [`A`,`P`,`f`,`inst`,`addr`,`tn`] >>
     qpat_assum `inst.inst_opcode = ISTORE` (rewrite_tac o single) >>
     qpat_assum `inst.inst_operands = [addr;value]` (rewrite_tac o single) >>
     simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `dst = dst'` (SUBST_ALL_TAC o SYM) >>
  `?ops. mem_write_ops inst = SOME ops /\ ops.iao_ofst = addr` by
    simp[memLocDefsTheory.mem_write_ops_def] >>
  `MEM (w2n dst,32) (source_memory_write_ranges inst f.lf_src)` by
    (qpat_assum `inst.inst_opcode = ISTORE` (fn opcode =>
       qpat_assum `inst.inst_operands = [addr;value]` (fn operands =>
         simp[NoAsms, codegenRelTheory.source_memory_write_ranges_def, opcode, operands]) >>
       simp[codegenRelTheory.fixed_source_write_range_def])) >>
  `0 < (32:num)` by simp[] >>
  `(op_prov f.lf_H ops.iao_ofst = NONE ==> dst = dst) /\
   (!k. op_prov f.lf_H ops.iao_ofst = SOME k ==> ld_wordrel A (SOME k) dst dst)` by
    simp[] >>
  (Q.SUBGOAL_THEN
    `w2n dst+32 <= lo \/
     (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
       w2n dst=b+delta /\ w2n dst=c+delta /\ delta+32 <= sz) \/
     dyn_floor C vs <= w2n dst` assume_tac
   >- (drule_all (Q.INST [`n` |-> `32`] (cj 2 ld_access_dyn_cases)) >> metis_tac[])) >>
  `op_taint tn value SUBSET {j | j < 32}` by metis_tac[ld_reachable_op_taint_width] >>
  (Q.SUBGOAL_THEN `EVERY (ld_maps A) (f::fs)` assume_tac >- simp[]) >>
  drule_all ld_istore_effect >> strip_tac >>
  drule_all lowerDloadSafetyAmbientTheory.ld_sync_ghost_step >> strip_tac >>
  `step_inst fuel C inst f.lf_src = OK ss` by metis_tac[step_inst_non_invoke] >>
  qabbrev_tac `Hr = f.lf_H` >>
  `(f with <|lf_src := ss; lf_tgt := s'; lf_H := Hr;
             lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) =
   (f with <|lf_src := ss; lf_tgt := s';
             lf_tv := (step_taint inst f.lf_src ss tn).t_var|>)` by
    simp[NoAsms,Abbr `Hr`,ld_frame_component_equality] >>
  `ld_vars P A (f with <|lf_src := ss; lf_tgt := s'; lf_H := Hr;
    lf_tv := (step_taint inst f.lf_src ss tn).t_var|>)` by
    (qpat_assum `(f with <|lf_src := ss; lf_tgt := s'; lf_H := Hr; lf_tv := _|>) = _`
       SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  suspend "singleton_istore_boundary"
QED

Resume ld_frame_actual_occurrence[singleton_istore_boundary]:
  `MEM inst.inst_opcode [MSTORE;ISTORE]` by simp[] >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op SUBSET {k | k < 32}` by
    (gen_tac >> strip_tac >>
     qpat_assum `frame_reachable vs C stk PG G tn _ _ _`
       (mp_then Any irule lowerDloadPtrTaintBoundsTheory.dload_reachable_op_taint_bound)) >>
  drule_at (Pat `dload_boundary_core`)
    lowerDloadPtrMemoryStoreTheory.dload_boundary_core_mstore >>
  disch_then (fn h => qpat_assum `step_inst fuel C' inst f.lf_tgt = OK s'`
    (mp_then (Pat `step_inst`) mp_tac h)) >>
  disch_then (drule_at (Pat `fn_ptr_ok`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars f.lf_fn)`,`C`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `sg` strip_assume_tac) >>
  `sg = ss` by
    (qpat_assum `step_inst fuel C inst f.lf_src = OK sg` mp_tac >>
     qpat_assum `step_inst fuel C inst f.lf_src = OK ss` mp_tac >> simp[NoAsms]) >>
  qpat_x_assum `sg = ss` SUBST_ALL_TAC >>
  ld_frame_singleton_index_boundary_tac >>
  ld_frame_singleton_external_sync_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_sha3]:
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  `step_inst_base inst f.lf_tgt = OK s'` by metis_tac[step_inst_non_invoke] >>
  `tn.t_var = f.lf_tv` by (sym_tac >> first_assum ACCEPT_TAC) >>
  drule_all ld_sha3_operands >> strip_tac >>
  drule_all ld_sha3_effect >>
  disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
  drule_all lowerDloadSafetyAmbientTheory.ld_sync_ghost_step >> strip_tac >>
  `~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
     source_memory_write_ranges inst f.lf_src = []` by
    (qpat_assum `inst.inst_opcode = SHA3` (fn opcode =>
      simp[NoAsms, opcode, is_alloca_op_def, write_effects_def, empty_effects_def,
           codegenRelTheory.source_memory_write_ranges_def])) >>
  `step_inst fuel C inst f.lf_src = OK ss /\ step_inst fuel C' inst f.lf_tgt = OK s'` by
    metis_tac[step_inst_non_invoke] >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode` by simp[] >>
  drule_all lowerDloadSafetyAmbientTheory.ld_sync_dyn_agree_unwritten >> strip_tac >>
  qabbrev_tac `Hr = set_prov f.lf_H inst.inst_outputs NONE` >>
  `!a. a IN FRANGE Hr ==> a IN FDOM A` by
    (simp[Abbr `Hr`] >> rpt strip_tac >>
     drule (SRULE [SUBSET_DEF]
       (Q.INST [`q` |-> `NONE`] ld_set_prov_range)) >>
     simp[] >> metis_tac[ld_global_selected,listTheory.MEM]) >>
  `~about_to_revert f.lf_fn inst f.lf_src` by
    simp[ptrDisciplineTheory.about_to_revert_def] >>
  drule_at (Pat `dload_boundary_core`) lowerDloadPtrHashTheory.dload_boundary_core_sha3 >>
  disch_then (fn h => qpat_assum `step_inst fuel C' inst f.lf_tgt = OK s'`
    (mp_then (Pat `step_inst`) mp_tac h)) >>
  disch_then (drule_at (Pat `fn_ptr_ok`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars f.lf_fn)`,`C`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `sg` strip_assume_tac) >>
  `sg = ss` by
    (qpat_assum `step_inst fuel C inst f.lf_src = OK sg` mp_tac >>
     qpat_assum `step_inst fuel C inst f.lf_src = OK ss` mp_tac >> simp[NoAsms]) >>
  qpat_x_assum `sg = ss` SUBST_ALL_TAC >>
  ld_frame_singleton_index_boundary_tac >>
  ld_frame_singleton_external_sync_tac >>
  ld_frame_singleton_next_tac >>
  ld_frame_singleton_control_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_slots_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_witness_tac >>
  ld_frame_singleton_rows_tac >>
  ld_frame_singleton_saved_tac >>
  ld_frame_singleton_saved_control_tac >>
  ld_frame_singleton_finish_tac
QED

Resume ld_frame_actual_occurrence[singleton_after_residual_data]:
  Cases_on `inst.inst_opcode = ALLOCA`
  >- suspend "singleton_alloca" >>
  suspend "singleton_exhaustive"
QED

Resume ld_frame_actual_occurrence[singleton_alloca]:
  `ALL_DISTINCT (MAP (\b. b.bb_label) (ld_image f).fn_blocks)` by
    simp[fn_labels_def] >>
  `dload_control_match f.lf_supply f.lf_fn (ld_image f)
     f.lf_src f.lf_tgt inst [inst] 0` by simp[] >>
  `r.dr_scratch = FDOM f.lf_tgt.vs_allocas DIFF {i.inst_id | MEM i (fn_insts f.lf_fn)}` by
    (qpat_assum `!k. _ ==> (EL k (r::rs)).dr_scratch = _` (qspec_then `0` mp_tac) >>
     simp[NoAsms,listTheory.EL] >> disch_then (K ALL_TAC) >>
     simp[NoAsms,EXTENSION] >> metis_tac[NoAsms]) >>
  `vs.vs_allocas = FEMPTY` by
    (qpat_assum `o1_initial_state_ok vs` mp_tac >> simp[NoAsms,o1_initial_state_ok_def]) >>
  `SUM (MAP (\r. CARD r.dr_scratch) (r::rs)) <= ctx_dload_count C` by
    (irule lowerDloadPtrJointBudgetTheory.dload_joint_runtime_scratch_budget >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qexists_tac `names` >> first_assum ACCEPT_TAC) >>
     qpat_assum `frame_reachable vs C stk PG G tn f.lf_fn inst f.lf_src`
       (irule_at (Pat `frame_reachable`)) >>
     qpat_assum `frame_reachable vs C' ds PH H0 un0 (ld_image f) inst f.lf_tgt`
       (irule_at (Pat `frame_reachable`)) >>
     simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_assum `!k. _ ==> (EL k (r::rs)).dr_scratch = _` mp_tac >>
         qpat_assum `LENGTH rs = LENGTH fs` (fn len => simp[NoAsms,len]) >>
         strip_tac >> rpt strip_tac >> simp[NoAsms,EXTENSION] >> metis_tac[NoAsms])
     >> qx_gen_tac `k` >> Cases_on `k` >> simp[listTheory.EL]
     >- (qexistsl [`f.lf_supply`,`SND (lower_dload_function_supply f.lf_supply f.lf_fn)`] >>
         simp[ld_image_def]) >>
     qpat_assum `!k. _ ==> dload_live_layout _ _ _ _ /\ _`
       (qspec_then `n'` mp_tac) >>
     simp[EL_MAP] >> metis_tac[]) >>
  drule_at (Pat `dload_boundary_core`) ld_frame_alloca_boundary_next >>
  disch_then (drule_at (Pat `frame_reachable vs C stk PG G tn _ _ _`)) >>
  disch_then (drule_at (Pat `dload_control_match _ _ _ _ _ _ [inst] 0`)) >>
  disch_then (drule_at (Pat `step_inst fuel C' inst f.lf_tgt = OK s'`)) >>
  disch_then (drule_at (Pat `active_inst (ld_image f) ti' _`)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `ss` (qx_choose_then `r1`
    (qx_choose_then `i` (qx_choose_then `E` strip_assume_tac)))) >>
  qpat_assum `step_inst fuel C' inst f.lf_tgt = OK s'`
    (mp_then (Pat `step_inst`) mp_tac lowerDloadPtrJointAllocTheory.dload_alloca_step_shape) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `sz` (qx_choose_then `out` strip_assume_tac)) >>
  `exec_alloca inst f.lf_src sz = OK ss` by
    (qpat_assum `step_inst fuel C inst f.lf_src = OK ss` mp_tac >>
     simp[lowerDloadSafetyAllocationTheory.ld_alloca_step]) >>
  `MEM out (fn_ir_vars f.lf_fn)` by
    (irule ld_inst_output_ir >> qexists `inst` >> simp[]) >>
  `out IN fn_pv P f.lf_fn` by
    (irule (REWRITE_RULE [SUBSET_DEF] o1LowerDloadClosureTheory.ptr_roots_subset_fn_pv) >>
     simp[NoAsms,ptr_roots_def,pointerConfinedDefsTheory.alloca_roots_def] >>
     disj1_tac >> disj1_tac >> qexists_tac `inst` >>
     qpat_assum `inst.inst_outputs = [out]`
       (fn outs => simp[NoAsms,inst_output_def,outs]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `sn = ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx` >>
  qabbrev_tac `tnext = s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx` >>
  qabbrev_tac `Hr = f.lf_H |+ (out,(f.lf_serial,inst.inst_id))` >>
  `0 < LENGTH E /\ ld_envelope f.lf_supply f.lf_fn sn sn.vs_inst_idx E tnext.vs_inst_idx /\
   ld_prefix C' (ld_image f) E tnext.vs_inst_idx 0 tnext tnext` by
    (qpat_assum `dload_control_match f.lf_supply _ _ _ _ i E 0`
       (fn th => POP_ASSUM_LIST (K (mp_tac th))) >>
     simp[dload_control_match_def,ld_prefix_zero] >> strip_tac >>
     simp[ld_envelope_def] >> metis_tac[pairTheory.FST,pairTheory.SND]) >>
  `!v. MEM v (fn_ir_vars f.lf_fn) ==> (lookup_var v sn = NONE <=> lookup_var v tnext = NONE)` by
    (qpat_assum `inst.inst_opcode = ALLOCA` (fn opc =>
       qpat_assum `step_inst fuel C inst f.lf_src = OK ss` (fn src =>
         qpat_assum `step_inst fuel C' inst f.lf_tgt = OK s'` (fn tgt =>
           mp_tac (CONJUNCT1 (MATCH_MP
             lowerDloadPtrJointAllocClosureTheory.dload_alloca_success_lookup (CONJ opc src))) >>
           mp_tac (CONJUNCT1 (MATCH_MP
             lowerDloadPtrJointAllocClosureTheory.dload_alloca_success_lookup (CONJ opc tgt)))))) >>
     qpat_assum `!v. MEM v (fn_ir_vars f.lf_fn) ==> (lookup_var v f.lf_src = NONE <=> _)`
       mp_tac >>
     simp[NoAsms,Abbr `sn`,Abbr `tnext`,lookup_var_def] >> metis_tac[NoAsms]) >>
  `ld_envelope f.lf_supply f.lf_fn f.lf_src f.lf_src.vs_inst_idx [inst] f.lf_tgt.vs_inst_idx` by
    (first_assum ACCEPT_TAC ORELSE
     (qpat_assum `f.lf_supply = Sigma f.lf_fn.fn_name` SUBST1_TAC >>
      first_assum ACCEPT_TAC)) >>
  Cases_on `FLOOKUP f.lf_src.vs_allocas inst.inst_id`
  >- suspend "singleton_alloca_fresh" >>
  rename1 `FLOOKUP f.lf_src.vs_allocas inst.inst_id = SOME alloc` >>
  PairCases_on `alloc` >>
  suspend "singleton_alloca_cached"
QED

Resume ld_frame_actual_occurrence[singleton_alloca_cached]:
  (Q.SUBGOAL_THEN `f.lf_tgt.vs_inst_idx = f.lf_tgt.vs_inst_idx` assume_tac
    >- REFL_TAC) >>
  drule_all lowerDloadSafetyAllocationTheory.ld_cached_alloca_endpoint >>
  disch_then (qx_choose_then `src` (qx_choose_then `g` strip_assume_tac)) >>
  `src = ss` by
    (qpat_assum `step_inst fuel C inst f.lf_src = OK ss` mp_tac >>
     qpat_assum `step_inst 0 C inst f.lf_src = OK src` mp_tac >>
     qpat_assum `inst.inst_opcode <> INVOKE` (fn opc =>
       simp[NoAsms,opc,step_inst_non_invoke])) >>
  qpat_x_assum `src = ss` SUBST_ALL_TAC >>
  `g.lf_src = sn /\ g.lf_tgt = tnext` by
    (qpat_assum `g = f with <|lf_src := _; lf_tgt := _; lf_H := _; lf_tv := _|>`
       SUBST1_TAC >> simp[Abbr `sn`,Abbr `tnext`,arithmeticTheory.ADD1]) >>
  `active_inst f.lf_fn i sn` by
    (qpat_assum `dload_control_match _ f.lf_fn (ld_image f) sn tnext i E 0`
       (ACCEPT_TAC o CONJUNCT1 o MATCH_MP dload_control_match_boundary)) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst f.lf_src ss tn)
      f.lf_fn i sn tnext A (g::fs) N` by
    (qpat_assum `!next. active_inst f.lf_fn next g.lf_src ==> _` (qspec_then `i` mp_tac) >>
     qpat_assum `g.lf_src = sn` (fn hs =>
       qpat_assum `g.lf_tgt = tnext` (fn ht =>
         qpat_assum `active_inst f.lf_fn i sn` (fn ha =>
           simp[NoAsms,hs,ht,ha])))) >>
  (Q.SUBGOAL_THEN `?Ar. Abbrev (Ar = A) /\ ld_global lo Ar (g::fs)`
      (qx_choose_then `Ar` strip_assume_tac)
   >- (qexists_tac `A` >> simp[markerTheory.Abbrev_def])) >>
  `!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a` by simp[Abbr `Ar`] >>
  ld_frame_singleton_alloca_reset_tac >>
  ld_frame_singleton_alloca_slots_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_alloca_suffix_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_alloca_history_tac >>
  ld_frame_singleton_alloca_witness_tac >>
  ld_frame_singleton_alloca_fields_tac >>
  ld_frame_singleton_alloca_geometry_tac >>
  ld_frame_singleton_alloca_saved_tac >>
  ld_frame_singleton_alloca_control_tac
QED

Resume ld_frame_actual_occurrence[singleton_alloca_fresh]:
  `MEM f.lf_fn C.ctx_functions` by
    (qpat_assum `frame_reachable vs C stk PG G tn f.lf_fn inst f.lf_src`
      (ACCEPT_TAC o CONJUNCT1 o MATCH_MP frameAllocationOwnershipTheory.frame_reachable_functions_member)) >>
  `ir_supply_covers_fn f.lf_supply f.lf_fn` by
    (qpat_assum `f.lf_supply = Sigma f.lf_fn.fn_name` SUBST1_TAC >>
     qpat_assum `!fn. MEM fn C.ctx_functions ==> _` (qspec_then `f.lf_fn` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> first_assum ACCEPT_TAC) >>
  drule_all lowerDloadSafetyAllocationTheory.ld_sync_original_site_fresh >> strip_tac >>
  qabbrev_tac `Ar = A |+ ((f.lf_serial,inst.inst_id),(f.lf_src.vs_alloca_next,
                     f.lf_tgt.vs_alloca_next,w2n sz))` >>
  qabbrev_tac `g = f with <|lf_src := sn; lf_tgt := tnext; lf_H := Hr;
                          lf_tv := (step_taint inst f.lf_src ss tn).t_var|>` >>
  `!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a` by
    (simp[Abbr `Ar`,FLOOKUP_UPDATE] >> metis_tac[]) >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_ghosts >> simp[NoAsms] >> strip_tac >>
  `FRANGE f.lf_H SUBSET FDOM A` by
    (simp[SUBSET_DEF] >> metis_tac[ld_global_selected,listTheory.MEM]) >>
  `step_prov PG (ld_erase A o_f f.lf_H) inst ss = ld_erase Ar o_f Hr /\
   ld_vars P Ar (f with <|lf_src := ss; lf_tgt := s'; lf_H := Hr;
                          lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
   ld_memory lo Ar (step_taint inst f.lf_src ss tn) ss s' /\
   ld_nonghost (step_taint inst f.lf_src ss tn) ss s' /\ FRANGE Hr SUBSET FDOM Ar` by
    (`Ar = A |+ ((f.lf_serial,inst.inst_id),(f.lf_src.vs_alloca_next,
                  f.lf_tgt.vs_alloca_next,w2n sz))` by simp[Abbr `Ar`] >>
     drule_all lowerDloadSafetyAllocationTheory.ld_fresh_alloca_effect >>
     disch_then (qspecl_then [`fuel`,`PG`,`C'`,`C`] strip_assume_tac) >>
     qpat_assum `Abbrev (Hr = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ld_vars P Ar g` by
    (qpat_assum `ld_vars P Ar _` mp_tac >>
     simp[NoAsms,Abbr `g`,Abbr `sn`,Abbr `tnext`,ld_vars_def]) >>
  `ld_memory lo Ar (step_taint inst f.lf_src ss tn) sn tnext /\
   ld_nonghost (step_taint inst f.lf_src ss tn) sn tnext` by
    (conj_tac
     >- (qpat_assum `ld_memory lo Ar _ ss s'` mp_tac >>
         simp[NoAsms,Abbr `sn`,Abbr `tnext`,ld_memory_def] >>
         strip_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `ld_nonghost _ ss s'` mp_tac >>
     simp[NoAsms,Abbr `sn`,Abbr `tnext`,ld_nonghost_def] >>
     strip_tac >> rpt conj_tac >> metis_tac[]) >>
  `ld_ghost_ok (dyn_floor C vs) Ar Hr (step_prov PG G inst ss)` by
    (`~MEM inst.inst_opcode [PARAM; ADD; SUB; ASSIGN]` by simp[] >>
     drule_then irule ld_ghost_ok_step_fixed >> metis_tac[]) >>
  suspend "singleton_alloca_fresh_pack"
QED

Resume ld_frame_actual_occurrence[singleton_alloca_fresh_pack]:
  `source_memory_write_ranges inst f.lf_src = []` by (qpat_assum `inst.inst_opcode = ALLOCA` (fn opc =>
      simp[NoAsms,opc,codegenRelTheory.source_memory_write_ranges_def])) >>
  `ss.vs_memory = f.lf_src.vs_memory /\ s'.vs_memory = f.lf_tgt.vs_memory` by
    (qpat_assum `exec_alloca inst f.lf_src sz = OK ss` mp_tac >>
     qpat_assum `exec_alloca inst f.lf_tgt sz = OK s'` mp_tac >>
     simp[NoAsms,exec_alloca_def,update_var_def,AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  `ld_dyn_agree (dyn_floor C vs) (step_taint inst f.lf_src ss tn).t_mem
     sn.vs_memory tnext.vs_memory` by
    (simp[NoAsms,Abbr `sn`,Abbr `tnext`] >> drule ld_sync_dyn_agree >> strip_tac >>
     drule_all ld_dyn_agree_unwritten >> disch_then ACCEPT_TAC) >>
  `lo <= f.lf_src.vs_alloca_next /\ lo <= f.lf_tgt.vs_alloca_next` by
    (`lo <= vs.vs_alloca_next` by
       (qpat_assum `ptr_discipline_upto lo n C vs` mp_tac >>
        simp[NoAsms,ptr_discipline_upto_def]) >>
     qpat_assum `o1_ctx_shape C` (fn sh =>
       qpat_assum `frame_reachable vs C stk PG G tn f.lf_fn inst f.lf_src`
         (assume_tac o MATCH_MP ld_raw_reachable_frontier o
          MATCH_MP lowerDloadPtrRawReachableTheory.frame_reachable_raw o CONJ sh)) >>
     qpat_assum `ld_sync lo P C vs stk PG G tn f.lf_fn inst f.lf_src f.lf_tgt A (f::fs) N`
       (strip_assume_tac o MATCH_MP ld_sync_frontier) >>
     decide_tac) >>
  `active_inst f.lf_fn i sn` by
    (qpat_assum `dload_control_match _ f.lf_fn (ld_image f) sn tnext i E 0`
       (ACCEPT_TAC o CONJUNCT1 o MATCH_MP dload_control_match_boundary)) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst f.lf_src ss tn)
      f.lf_fn i sn tnext Ar (g::fs) N /\ ld_global lo Ar (g::fs)` by
    (`Ar = A |+ ((f.lf_serial,inst.inst_id),(f.lf_src.vs_alloca_next,
          f.lf_tgt.vs_alloca_next,w2n sz)) /\
      sn = ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx /\
      tnext = s' with vs_inst_idx := SUC f.lf_tgt.vs_inst_idx /\
      g = f with <|lf_src := sn; lf_tgt := tnext; lf_H := Hr;
                   lf_tv := (step_taint inst f.lf_src ss tn).t_var|>` by
       simp[Abbr `Ar`,Abbr `sn`,Abbr `tnext`,Abbr `g`] >>
     drule_all (SRULE [PULL_EXISTS] lowerDloadSafetyAllocationTheory.ld_sync_fresh_alloca_update) >>
     qpat_assum `g = f with <|lf_src := _; lf_tgt := _; lf_H := _; lf_tv := _|>`
       SUBST1_TAC >>
     qpat_assum `sn = ss with vs_inst_idx := _` SUBST1_TAC >>
     qpat_assum `tnext = s' with vs_inst_idx := _` SUBST1_TAC >>
     qpat_assum `Ar = A |+ _` SUBST1_TAC >>
     disch_then ACCEPT_TAC) >>
  ld_frame_singleton_alloca_reset_tac >>
  ld_frame_singleton_alloca_slots_tac >>
  ld_frame_singleton_head_tac >>
  ld_frame_singleton_alloca_suffix_tac >>
  ld_frame_singleton_history_tac >>
  ld_frame_singleton_gas_count_tac >>
  ld_frame_singleton_gas_tail_tac >>
  ld_frame_singleton_alloca_history_tac >>
  ld_frame_singleton_alloca_witness_tac >>
  ld_frame_singleton_alloca_fields_tac >>
  ld_frame_singleton_alloca_geometry_tac >>
  ld_frame_singleton_alloca_saved_tac >>
  ld_frame_singleton_alloca_control_tac
QED
Resume ld_frame_actual_occurrence[singleton_exhaustive]:
  `pre_fmp_opcode inst.inst_opcode` by
    (qpat_assum `fmp_free_ctx C`
       (qspec_then `f.lf_fn` (mp_tac o BETA_RULE) o
        REWRITE_RULE[fmp_free_ctx_def,EVERY_MEM]) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `pre_fmp_ops f.lf_fn`
       (qspec_then `inst` (mp_tac o BETA_RULE) o
        REWRITE_RULE[pre_fmp_ops_def,EVERY_MEM]) >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  `inst.inst_opcode <> MEMTOP` by
    (qpat_assum `fn_ptr_ok P f.lf_fn`
       (mp_tac o cj 2 o REWRITE_RULE[fn_ptr_ok_def]) >>
     disch_then (qspec_then `inst` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  `step_inst_base inst f.lf_tgt = OK s'` by metis_tac[step_inst_non_invoke] >>
  `inst.inst_opcode <> PHI` by
    (strip_tac >> qpat_assum `step_inst_base inst f.lf_tgt = OK s'` mp_tac >>
     simp[NoAsms, step_inst_base_def] >>
     qpat_assum `inst.inst_opcode = PHI` (rewrite_tac o single) >>
     simp[NoAsms, opcode_case_def]) >>
  qpat_x_assum `pre_fmp_opcode inst.inst_opcode` mp_tac >>
  qpat_x_assum `~is_terminator inst.inst_opcode` mp_tac >>
  rpt (qpat_x_assum `inst.inst_opcode <> _` mp_tac) >>
  rpt (qpat_x_assum `~MEM inst.inst_opcode _` mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `inst.inst_opcode` >> simp[pre_fmp_opcode_def,is_terminator_def]
QED

Finalise ld_frame_actual_occurrence

Theorem ld_frame_normal_frontier[local]:
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  mem_inv dload_headroom_ok C vs /\
  (!f. MEM f C.ctx_functions ==> ir_supply_covers_fn (Sigma f.fn_name) f) /\
  ^frame_normal lo P C C' vs Sigma names ds PH H un gn ti t ==>
  t.vs_alloca_next < dimword (:256)
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  Cases_on `frames` >- gvs[] >>
  RULE_ASSUM_TAC (REWRITE_RULE[HD,TL]) >>
  rename1 `ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N` >>
  `t0.vs_alloca_next < dimword(:256)` by
    (drule dload_boundary_layout >> simp[dload_live_layout_def]) >>
  drule ld_sync_source >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule_then strip_assume_tac o1_fn_shape_components >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def,contextCodegenRelTheory.active_inst_def] >>
     metis_tac[MEM_EL]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by simp[fn_labels_def] >>
  `MEM fn C.ctx_functions` by
    metis_tac[frameAllocationOwnershipTheory.frame_reachable_functions_member] >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  `ir_supply_covers_fn f.lf_supply fn` by
    (qpat_assum `f.lf_fn = fn` (fn hf =>
       qpat_assum `EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs)`
         (mp_tac o CONJUNCT1 o REWRITE_RULE[EVERY_DEF]) >>
       qpat_assum `!f. MEM f C.ctx_functions ==> _` (qspec_then `fn` mp_tac) >>
       qpat_assum `MEM fn C.ctx_functions` (fn hm => simp[NoAsms,hf,hm]))) >>
  `ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs))` by
    (irule ld_frames_distinct >> qexists_tac `names` >> fs[]) >>
  Cases_on `inst.inst_opcode = DLOAD`
  >- (`?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
        fs[inst_wf_def,LENGTH_EQ_NUM_compute] >>
      drule_all ld_dload_envelope_temporary >> strip_tac >>
      drule_all ld_sync_dload_scratch_bounds_static >> strip_tac >>
      drule_all lower_dload_prefix_scratch >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = DLOADBYTES`
  >- (`?dest off len. inst.inst_operands = [dest;off;len]` by
        fs[inst_wf_def,LENGTH_EQ_NUM_compute] >>
      drule_all ld_dloadbytes_envelope_temporary >> strip_tac >>
      `h < 2` by
        (qpat_assum `h < LENGTH X` mp_tac >>
         qpat_assum `X = [_;_]` (fn hs => simp[NoAsms,hs])) >>
      Cases_on `h = 0`
      >- (qpat_assum `ld_prefix C' gn X p h t0 t` mp_tac >>
          qpat_assum `h = 0` (fn hz => simp[NoAsms,hz,ld_prefix_zero]) >>
          strip_tac >> qpat_assum `t = t0` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      `h = 1` by decide_tac >>
      qpat_x_assum `h = 1` SUBST_ALL_TAC >>
      drule_all ld_dloadbytes_prefix_observations >> strip_tac >>
      qpat_assum `t.vs_alloca_next = t0.vs_alloca_next` SUBST1_TAC >>
      first_assum ACCEPT_TAC) >>
  `X = [inst]` by (drule_all ld_envelope_ordinary >> disch_then ACCEPT_TAC) >>
  `h = 0` by
    (qpat_assum `h < LENGTH X` mp_tac >>
     qpat_assum `X = [inst]` (fn hx => simp[NoAsms,hx])) >>
  qpat_assum `ld_prefix C' gn X p h t0 t` mp_tac >>
  qpat_assum `h = 0` (fn hz => simp[NoAsms,hz,ld_prefix_zero]) >>
  strip_tac >> qpat_assum `t = t0` SUBST1_TAC >> first_assum ACCEPT_TAC
QED

Theorem ld_frame_bounded_observations[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  callee_first names C.ctx_functions /\ o1_safe_upto D lo n C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  (!fn. MEM fn C.ctx_functions ==>
    ir_supply_covers_fn (Sigma fn.fn_name) fn /\
    lookup_function fn.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma fn.fn_name) fn))) /\
  C'.ctx_entry = C.ctx_entry /\
  EVERY (\gn. ALL_DISTINCT (fn_labels gn)) C'.ctx_functions /\
  EVERY fn_shape_ok C'.ctx_functions /\
  frame_reachable vs C' ds PH H un gn ti t /\ gas_cut n vs t ==>
  access_ok lo H gn ti t /\ taint_ok gn un ti t /\ allocas_from lo t /\
  (ctx_has_dalloca C' ==> allocas_below_fmp t) /\
  t.vs_alloca_next < dimword (:256) /\ ^frame_taint_rows D C' ti t un
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
  drule_all ld_frame_actual_occurrence >>
  disch_then (DISJ_CASES_THEN assume_tac)
  >- suspend "normal" >>
  suspend "terminal"
QED

Resume ld_frame_bounded_observations[terminal]:
  drule_all_then strip_assume_tac ld_frame_terminal_ptr_rows >>
  `^frame_taint_rows D C' ti t un` by
    (MATCH_MP_TAC ld_frame_terminal_taint_rows >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `^frame_taint_rows D C' ti t un` (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `^frame_terminal lo P vs C ds H un gn ti t`
    (strip_assume_tac o BETA_RULE) >>
  simp[] >> metis_tac[lower_dload_stage_no_dalloca,dload_live_layout_def]
QED

Resume ld_frame_bounded_observations[normal]:
  drule_all_then (strip_assume_tac o BETA_RULE) ld_frame_normal_taint_rows >>
  `mem_inv dload_headroom_ok C vs /\ ptr_discipline_upto lo n C vs` by
    fs[o1_safe_upto_def,o1_ptr_safe_upto_def] >>
  `!f. MEM f C.ctx_functions ==> ir_supply_covers_fn (Sigma f.fn_name) f` by
    (rpt strip_tac >>
     qpat_assum `!f. MEM f C.ctx_functions ==> _ /\ _` (qspec_then `f` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  drule_all_then assume_tac ld_frame_normal_frontier >>
  `^frame_projection_witness ds PH H un gn ti t` by suspend "projection" >>
  qpat_x_assum `^frame_projection_witness ds PH H un gn ti t`
    (assume_tac o BETA_RULE o CONV_RULE (DEPTH_CONV (REWR_CONV LET_THM THENC BETA_CONV))) >>
  `access_ok lo H gn ti t /\ taint_ok gn un ti t /\ allocas_from lo t /\
   (ctx_has_dalloca C' ==> allocas_below_fmp t)` by
    (MATCH_MP_TAC (Q.INST [`rpolicy` |-> `rpolicy`, `view` |-> `view`,
       `C` |-> `C`, `vs` |-> `vs`, `names` |-> `names`, `P` |-> `P`,
       `ngas` |-> `n`, `ds` |-> `ds`, `PH` |-> `PH`]
       (BETA_RULE ld_frame_normal_ptr_rows)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ld_frame_bounded_observations[projection]:
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  qpat_x_assum `^frame_normal lo P C C' vs Sigma names ds PH H un gn ti t`
    (strip_assume_tac o BETA_RULE) >>
  Cases_on `frames` >- fs[] >>
  rename1 `ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N` >>
  fs[HD,TL] >> drule_then strip_assume_tac ld_sync_source >>
  drule_then (strip_assume_tac o REWRITE_RULE[HD]) ld_sync_active >>
  `ir_supply_covers_fn f.lf_supply fn` by
    (qpat_assum `!fn. MEM fn C.ctx_functions ==> _` (qspec_then `fn` mp_tac) >>
     `MEM fn C.ctx_functions` by
       metis_tac[frameAllocationOwnershipTheory.frame_reachable_functions_member] >>
     simp[] >> metis_tac[]) >>
  drule lowerDloadPtrSupportTheory.frame_reachable_prov_supported >>
  disch_then (qspec_then `P` mp_tac) >>
  (impl_tac >- fs[EVERY_MEM]) >> strip_tac >>
  `?q'. lower_dload_function_supply f.lf_supply fn = (gn,q')` by
    (qexists_tac `SND (lower_dload_function_supply f.lf_supply fn)` >>
     qpat_assum `gn = ld_image f` (fn hg =>
       qpat_assum `f.lf_fn = fn` (fn hf =>
         simp[NoAsms,hg,hf,ld_image_def,pairTheory.PAIR]))) >>
  qexistsl [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`f.lf_supply`,
    `X`,`h`,`pfuel`,`t0`,`H0`,`un0`,`rs`] >>
  simp[] >> metis_tac[]
QED

Finalise ld_frame_bounded_observations

Theorem ld_focus_actual_frame_safety:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  callee_first names C.ctx_functions /\ o1_safe_upto D lo n C vs ==>
  ptr_discipline_upto lo n C' vs /\ taint_within_upto D n C' vs /\
  alloca_frontier_upto n C' vs
Proof
  strip_tac >> drule_all ld_focus_stage_suppliers >> strip_tac >>
  `EVERY (\gn. ALL_DISTINCT (fn_labels gn)) C'.ctx_functions /\
   EVERY fn_shape_ok C'.ctx_functions` by
    metis_tac[lower_dload_stage_labels_distinct,lower_dload_stage_fn_shape] >>
  `!ds PH H un gn ti t.
     frame_reachable vs C' ds PH H un gn ti t /\ gas_cut n vs t ==>
     access_ok lo H gn ti t /\ taint_ok gn un ti t /\ allocas_from lo t /\
     (ctx_has_dalloca C' ==> allocas_below_fmp t) /\
     t.vs_alloca_next < dimword (:256) /\ ^frame_taint_rows D C' ti t un` by
    (CONV_TAC (REDEPTH_CONV BETA_CONV) >> rpt gen_tac >> strip_tac >>
     drule_all (BETA_RULE ld_frame_bounded_observations) >> simp[]) >>
  `lo <= vs.vs_alloca_next /\
   ?Q. EVERY (\fn. fn_ptr_ok Q fn /\ fn_ptr_ok Q (reachable_fn fn)) C'.ctx_functions` by
    (qpat_assum `o1_safe_upto D lo n C vs`
       (strip_assume_tac o REWRITE_RULE
          [o1_safe_upto_def,o1_ptr_safe_upto_def,ptr_discipline_upto_def]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     drule_all lower_dload_stage_static_ptr_ok >> metis_tac[]) >>
  simp[ptr_discipline_upto_def,taint_within_upto_def,alloca_frontier_upto_def] >>
  rpt conj_tac
  >- (qexists_tac `Q` >> first_assum ACCEPT_TAC)
  >> rpt gen_tac >> strip_tac >>
  first_x_assum (drule_at (Pat `frame_reachable vs C' _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED
