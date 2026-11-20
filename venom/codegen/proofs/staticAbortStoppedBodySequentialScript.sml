Theory staticAbortStoppedBodySequential
Ancestors
  staticAbortProtectedOrdinary staticAbortProtectedGas staticAbortProtectedTerminal
  fnStaticAbortBodyFacts fnBlockBodyClasses fnBlockBody fnBlockBodySteps
  fnStaticAbortBoundary symBlockBody contextStaticAbortRel staticAbortDefs
  venomExecSemantics venomExecProps venomInst venomInstProps unitShapeDefs
  stepWriteFootprintForward contextCodegenRel list rich_list
  codegenSymRel asmSymBridge

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

Theorem stopped_body_sequential_case_mode:
  !allow_own own A. A = (\rpolicy unit cpl prog ctx lo o2pc Inv env ast ss vs'.
    (?n out. (asm_steps lo o2pc prog n ast = AsmRevert out \/
              asm_steps lo o2pc prog n ast = AsmFault out) /\
       sym_terminal (sym_steps_mode allow_own prog env own n ss) /\ out.as_requests <<= vs'.vs_requests) \/
    (?nc cut sc iC fnC rC livC dfgC cfgC chC growthC spillC ctrC fnopsC endC
      bbC pslC hC promisedC dfsC blockC dfsafterC afterC prefixC restopsC kC
      psC pcC cvsC raC pcretC restC memC retC srestC labsC.
       asm_steps lo o2pc prog nc ast = AsmOK cut /\
       sym_steps_mode allow_own prog env own nc ss = SymOK sc /\
       (if allow_own then body_inv_abort_reloc else body_inv_abort)
      rpolicy unit cpl prog ctx lo o2pc iC fnC rC livC dfgC cfgC
         chC growthC spillC ctrC fnopsC endC bbC pslC hC promisedC dfsC blockC
         dfsafterC afterC prefixC restopsC kC psC pcC cvsC cut Inv
         raC pcretC restC memC /\
       (if allow_own then sym_frame_inv_own lo prog env own
      else sym_frame_inv prog env) ctx cpl fnC retC srestC labsC psC cut sc /\
       (in_static_abort_prefix fnC cvsC \/ in_revert_forward fnC cvsC) /\
       cut.as_requests = vs'.vs_requests)) ==>
  !R. R = (\rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss res.
    (!vs'. res = Halt vs' ==>
       ?n out. asm_steps lo o2pc prog n ast = AsmHalt out /\
         venom_asm_terminal_rel vs' out /\ sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!a vs'. res = Abort a vs' ==> A rpolicy unit cpl prog ctx lo o2pc Inv env ast ss vs') /\
    (!rv vs'. res = IntRet rv vs' ==>
       ?n out ss'. asm_steps lo o2pc prog n ast = AsmOK out /\
         out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
         context_memory_rel cpl vs'.vs_memory out.as_memory /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           read_byte b out.as_memory = read_byte b mem0) /\
         shared_state_rel vs' out /\ sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
         (if allow_own then asm_sym_rel_own lo prog env own
          else asm_sym_rel prog env) out ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))) ==>
  (!n ast0 ast1 ss0 ss1 vs'.
    asm_steps lo o2pc prog n ast0 = AsmOK ast1 /\
    sym_steps_mode allow_own prog env own n ss0 = SymOK ss1 /\
    A rpolicy unit cpl prog ctx lo o2pc Inv env ast1 ss1 vs' ==>
    A rpolicy unit cpl prog ctx lo o2pc Inv env ast0 ss0 vs') /\
  (!n ast0 ast1 ss0 ss1 res.
    asm_steps lo o2pc prog n ast0 = AsmOK ast1 /\
    sym_steps_mode allow_own prog env own n ss0 = SymOK ss1 /\
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast1 ss1 res ==>
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast0 ss0 res) /\
  (!k1 prefix1 rest1 ps1 vs1 ast1 ss1.
    LENGTH bb.bb_instructions - k1 < LENGTH bb.bb_instructions - k /\
    (if allow_own then body_inv_abort_reloc else body_inv_abort)
      rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix1 rest1 k1 ps1 pc0 vs1 ast1 Inv
      ra pc_ret rest mem0 /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      ctx /\ sym_unit_static_ok unit /\
    asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    (if allow_own then sym_frame_inv_own lo prog env own
      else sym_frame_inv prog env) ctx cpl fn ret srest labs0 ps1 ast1 ss1 ==>
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast1 ss1
      (block_rest fuel ctx fn bb vs1)) /\
  (if allow_own then body_inv_abort_reloc else body_inv_abort)
      rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
    ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  (if allow_own then sym_frame_inv_own lo prog env own
      else sym_frame_inv prog env) ctx cpl fn ret srest labs0 ps ast ss /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode ==>
  R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss
    (block_rest fuel ctx fn bb vs)
Proof
  ntac 2 gen_tac >>
  gen_tac >> disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  gen_tac >> disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  strip_tac >>
  `body_inv_abort_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0` by
    (Cases_on `allow_own` >> fs[body_inv_abort_reloc_canonical]) >>
  drule body_inv_abort_plan_reloc >> strip_tac >>
  drule body_plan_inv_facts_reloc >> strip_tac >>
  drule_all body_plan_inv_inst_reloc >> strip_tac >>
  `vs.vs_inst_idx = k` by
    (qhdtm_assum `body_plan_inv_reloc` mp_tac >>
     pure_rewrite_tac[body_plan_inv_reloc_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!j. ~revert_forward_pair bb k j` by
    (qpat_x_assum `~in_revert_forward fn vs` mp_tac >>
     simp[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  `LENGTH (compute_operands inst) <= 16` by metis_tac[body_operands_le_16] >>
  `(inst.inst_opcode = LOG ==>
    ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4)` by
    (strip_tac >> irule log_case_topics >> metis_tac[body_log_topics]) >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by metis_tac[] >>
  Cases_on `?vs1. step_inst fuel ctx inst vs = OK vs1`
  >- suspend "ok"
  >> suspend "nonok"
QED

Resume stopped_body_sequential_case_mode[ok]:
  pop_assum strip_assume_tac >>
  `?ops ps' rest' n ast1 ss1.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    asm_steps lo o2pc prog n ast = AsmOK ast1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 ast1 /\
    ast1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    (if allow_own then sym_frame_inv_own lo prog env own
     else sym_frame_inv prog env) ctx cpl fn ret srest labs0 ps' ast1 ss1` by
    (Cases_on `inst.inst_opcode = GAS` >> Cases_on `allow_own` >> (RULE_ASSUM_TAC (PURE_REWRITE_RULE [COND_CLAUSES]) >>
      PURE_REWRITE_TAC [COND_CLAUSES]) >>
     FIRST [
       drule_all (PURE_REWRITE_RULE [COND_CLAUSES] (Q.INST [`allow_own` |-> `T`]
         sym_body_abort_protected_gas_ok_reloc)),
       drule_all sym_body_abort_protected_gas_ok,
       drule_all (PURE_REWRITE_RULE [COND_CLAUSES] (Q.SPECL [`T`, `own`]
         sym_body_abort_protected_ordinary_ok_reloc)),
       drule_all sym_body_abort_protected_ordinary_ok] >>
     simp[sym_steps_mode_def] >> metis_tac[]) >>
  `(if allow_own then body_inv_abort_reloc else body_inv_abort)
    rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after (prefix_ops ++ ops) rest' (SUC k) ps'
    pc0 (vs1 with vs_inst_idx := SUC k) ast1 Inv ra pc_ret rest mem0` by
    (Cases_on `allow_own` >> (RULE_ASSUM_TAC (PURE_REWRITE_RULE [COND_CLAUSES]) >>
      PURE_REWRITE_TAC [COND_CLAUSES]) >>
     FIRST [drule_all body_inv_abort_advance, drule_all body_inv_abort_advance_reloc] >>
     simp[]) >>
  `block_rest fuel ctx fn bb vs =
   block_rest fuel ctx fn bb (vs1 with vs_inst_idx := SUC k)` by
    metis_tac[block_rest_advance] >>
  `R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast1 ss1
    (block_rest fuel ctx fn bb (vs1 with vs_inst_idx := SUC k))` by
    (qpat_x_assum `!k1 prefix1 rest1 ps1 vs1 ast1 ss1. _` irule >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  metis_tac[]
QED

Resume stopped_body_sequential_case_mode[nonok]:
  qpat_x_assum `!k1 prefix1 rest1 ps1 vs1 ast1 ss1. _` kall_tac >>
  ntac 2 (qpat_x_assum `!n ast0 ast1 ss0 ss1 x. _` kall_tac) >>
  `!v. step_inst fuel ctx inst vs <> OK v` by metis_tac[] >>
  `block_rest fuel ctx fn bb vs = step_inst fuel ctx inst vs` by
    metis_tac[block_rest_other] >>
  (* gvs removes EL k = inst; restore its reflexive instance for
     the public per-instruction interfaces. *)
  Cases_on `step_inst fuel ctx inst vs` >> gvs[] >>
  `EL vs.vs_inst_idx bb.bb_instructions = EL vs.vs_inst_idx bb.bb_instructions` by simp[]
  >- (Cases_on `allow_own` >> (RULE_ASSUM_TAC (PURE_REWRITE_RULE [COND_CLAUSES]) >>
      PURE_REWRITE_TAC [COND_CLAUSES]) >>
      FIRST [drule_all sym_abort_protected_halt_step,
        drule_all (PURE_REWRITE_RULE [COND_CLAUSES] (Q.INST [`allow_own` |-> `T`]
          sym_abort_protected_halt_step_reloc))] >>
      simp[sym_body_result_def, sym_body_result_own_def, sym_steps_mode_def, Abbr `R`])
  >- (Cases_on `allow_own` >> (RULE_ASSUM_TAC (PURE_REWRITE_RULE [COND_CLAUSES]) >>
      PURE_REWRITE_TAC [COND_CLAUSES]) >>
      FIRST [drule_all sym_abort_protected_abort_step,
        drule_all (PURE_REWRITE_RULE [COND_CLAUSES] (Q.INST [`allow_own` |-> `T`]
          sym_abort_protected_abort_step_reloc))] >>
      simp[sym_body_result_def, sym_body_result_own_def, sym_steps_mode_def,
           Abbr `R`, Abbr `A`] >>
      strip_tac >> disj1_tac >>
      fs[codegenRelTheory.venom_asm_terminal_rel_def] >>
      qexistsl [`n`, `as'`] >> simp[IS_PREFIX_REFL])
  >- (drule_all codegen_ready_intret_opcode >> strip_tac >>
      gvs[is_terminator_def]) >>
  simp[Abbr `R`]
QED

Finalise stopped_body_sequential_case_mode

Theorem stopped_body_sequential_case:
  !A. A = (\rpolicy unit cpl prog ctx lo o2pc Inv env ast ss vs'.
    (?n out. (asm_steps lo o2pc prog n ast = AsmRevert out \/
              asm_steps lo o2pc prog n ast = AsmFault out) /\
       sym_terminal (sym_steps prog env n ss) /\ out.as_requests <<= vs'.vs_requests) \/
    (?nc cut sc iC fnC rC livC dfgC cfgC chC growthC spillC ctrC fnopsC endC
      bbC pslC hC promisedC dfsC blockC dfsafterC afterC prefixC restopsC kC
      psC pcC cvsC raC pcretC restC memC retC srestC labsC.
       asm_steps lo o2pc prog nc ast = AsmOK cut /\
       sym_steps prog env nc ss = SymOK sc /\
       body_inv_abort rpolicy unit cpl prog ctx lo o2pc iC fnC rC livC dfgC cfgC
         chC growthC spillC ctrC fnopsC endC bbC pslC hC promisedC dfsC blockC
         dfsafterC afterC prefixC restopsC kC psC pcC cvsC cut Inv
         raC pcretC restC memC /\
       sym_frame_inv prog env ctx cpl fnC retC srestC labsC psC cut sc /\
       (in_static_abort_prefix fnC cvsC \/ in_revert_forward fnC cvsC) /\
       cut.as_requests = vs'.vs_requests)) ==>
  !R. R = (\rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss res.
    (!vs'. res = Halt vs' ==>
       ?n out. asm_steps lo o2pc prog n ast = AsmHalt out /\
         venom_asm_terminal_rel vs' out /\ sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. res = Abort a vs' ==> A rpolicy unit cpl prog ctx lo o2pc Inv env ast ss vs') /\
    (!rv vs'. res = IntRet rv vs' ==>
       ?n out ss'. asm_steps lo o2pc prog n ast = AsmOK out /\
         out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
         context_memory_rel cpl vs'.vs_memory out.as_memory /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           read_byte b out.as_memory = read_byte b mem0) /\
         shared_state_rel vs' out /\ sym_steps prog env n ss = SymOK ss' /\
         asm_sym_rel prog env out ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))) ==>
  (!n ast0 ast1 ss0 ss1 vs'.
    asm_steps lo o2pc prog n ast0 = AsmOK ast1 /\
    sym_steps prog env n ss0 = SymOK ss1 /\
    A rpolicy unit cpl prog ctx lo o2pc Inv env ast1 ss1 vs' ==>
    A rpolicy unit cpl prog ctx lo o2pc Inv env ast0 ss0 vs') /\
  (!n ast0 ast1 ss0 ss1 res.
    asm_steps lo o2pc prog n ast0 = AsmOK ast1 /\
    sym_steps prog env n ss0 = SymOK ss1 /\
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast1 ss1 res ==>
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast0 ss0 res) /\
  (!k1 prefix1 rest1 ps1 vs1 ast1 ss1.
    LENGTH bb.bb_instructions - k1 < LENGTH bb.bb_instructions - k /\
    body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix1 rest1 k1 ps1 pc0 vs1 ast1 Inv
      ra pc_ret rest mem0 /\
    label_flow_ok ctx /\
    code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      ctx /\ sym_unit_static_ok unit /\
    asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps1 ast1 ss1 ==>
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast1 ss1
      (block_rest fuel ctx fn bb vs1)) /\
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0 /\
  label_flow_ok ctx /\
  code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
    ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps ast ss /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode ==>
  R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss
    (block_rest fuel ctx fn bb vs)
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES]
    (Q.SPECL [`F`, `[]`] stopped_body_sequential_case_mode))
QED
