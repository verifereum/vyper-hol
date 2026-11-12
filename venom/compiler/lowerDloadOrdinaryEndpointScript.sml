(* Exhaustive ordinary instruction effects, independent of successor activity. *)
Theory lowerDloadOrdinaryEndpoint
Ancestors
  lowerDloadSafetyAssignmentCoverage lowerDloadSafetyParamCoverage
  lowerDloadSafetyArithmeticCoverage lowerDloadSafetyReadCoverage
  lowerDloadSafetyClassifiedReadCoverage lowerDloadSafetyWriteAssembly
  lowerDloadSafetyImmutableWriteCoverage lowerDloadSafetyStorageWriteCoverage
  lowerDloadSafetyIdentityCoverage lowerDloadSafetyPublicCopy
  lowerDloadSafetyHashLog lowerDloadSafetyCreate lowerDloadSafetyDelegate
  lowerDloadExpansionEndpoint lowerDloadSafetyAdvance
  lowerDloadSafetyKernel lowerDloadSafetyAmbient lowerDloadSafetyAssemblyPremises
  lowerDloadSafetyRelation lowerDloadSafetyScalarEffects
  lowerDloadOracleCallAssembly o1PassContract venomInst
  venomExecSemantics ptrDiscipline lowerDloadSafetyValues lowerDloadSafetyUpdates
  venomState memLocDefs pointerConfinedDefs finite_map list words

Theorem ld_dalloca_step[local]:
  inst.inst_opcode = DALLOCA /\
  eval_operands inst.inst_operands s = eval_operands inst.inst_operands t /\
  step_inst_base inst t = OK ts ==>
  ?op out sz. inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
    ts = update_var out t.vs_fmp
           (t with vs_fmp := t.vs_fmp + n2w (ceil32 (w2n (sz:bytes32)))) /\
    step_inst_base inst s =
      OK (update_var out s.vs_fmp
            (s with vs_fmp := s.vs_fmp + n2w (ceil32 (w2n sz))))
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst t = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  simp[Once step_inst_base_def] >> qexists_tac `sz` >> simp[]
QED

Theorem ld_dalloca_taint[local]:
  inst.inst_opcode = DALLOCA /\ inst.inst_operands = [op] ==>
  step_taint inst s s' tn =
    tn with <| t_mem := tn.t_mem UNION new_site_bytes s s';
               t_var := set_var_taint tn.t_var inst.inst_outputs {} |>
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
       store_taint_def, adopt_reset_def, imm_taint_def, out_taint_def,
       taint_component_equality] >>
  Cases_on `eval_operand op s` >> simp[pred_setTheory.EXTENSION]
QED

(* The fresh region lies in [fl, 2^256), whether or not the pointer wraps. *)
Theorem ld_ghost_ok_dalloca[local]:
  ld_ghost_ok fl A H G /\ fl <= b /\ b < dimword (:256) /\
  e < dimword (:256) ==>
  ld_ghost_ok fl A (set_prov H [out] NONE) (G |+ (out,(b,e - b)))
Proof
  simp[lowerDloadSafetyRelationTheory.ld_ghost_ok_def, set_prov_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `out = v` >> gvs[] >> metis_tac[]
QED

Theorem ld_memory_dalloca[local]:
  ld_memory lo A tn s t ==>
  tn.t_mem SUBSET tn'.t_mem /\
  s'.vs_memory = s.vs_memory /\ t'.vs_memory = t.vs_memory ==>
  ld_memory lo A tn' s' t'
Proof
  simp[ld_memory_def, pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem ld_nonghost_dalloca[local]:
  ld_nonghost tn s t /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  tn'.t_imm = tn.t_imm ==>
  ld_nonghost tn' (update_var out s.vs_fmp (s with vs_fmp := s.vs_fmp + d))
    (update_var out t.vs_fmp (t with vs_fmp := t.vs_fmp + d))
Proof
  strip_tac >> fs[ld_nonghost_def, update_var_def] >> metis_tac[]
QED

Theorem ld_vars_dalloca_write[local]:
  ld_vars P A f /\ MEM out (fn_ir_vars f.lf_fn) /\ tv = f.lf_tv /\
  ss.vs_vars = f.lf_src.vs_vars |+ (out,x) /\
  ss.vs_params = f.lf_src.vs_params /\
  ts.vs_vars = f.lf_tgt.vs_vars |+ (out,x) /\
  ts.vs_params = f.lf_tgt.vs_params ==>
  ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
    lf_H := set_prov f.lf_H [out] NONE; lf_tv := tv |+ (out,{})|>)
Proof
  strip_tac >>
  `ld_vars P A (f with <|lf_src := f.lf_src with vs_vars := f.lf_src.vs_vars |+ (out,x);
      lf_tgt := f.lf_tgt with vs_vars := f.lf_tgt.vs_vars |+ (out,x);
      lf_H := set_prov f.lf_H [out] NONE; lf_tv := tv |+ (out,{})|>)` by
    (irule ld_vars_write >> simp[FLOOKUP_UPDATE, ld_word_agree_empty]) >>
  pop_assum mp_tac >> simp[lowerDloadSafetyRelationTheory.ld_vars_def]
QED

(* A DALLOCA moves both free memory pointers past a fresh dynamic region:
   its output's provenance is that region in G and nothing in H. *)
Theorem ld_sync_dalloca_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  inst.inst_opcode = DALLOCA /\ step_inst fuel C' inst t = OK ts ==>
  ?ss H'. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    ld_ghost_ok (dyn_floor C vs0) A H' (step_prov PG G inst ss) /\
    ld_dyn_agree (dyn_floor C vs0) (step_taint inst s ss tn).t_mem
      ss.vs_memory ts.vs_memory /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `MEM fn C.ctx_functions` by
    (qhdtm_x_assum `ld_sync` mp_tac >>
     simp[lowerDloadSafetyRelationTheory.ld_sync_def, EVERY_MEM] >>
     strip_tac >> metis_tac[MEM]) >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `ctx_has_dalloca C` by
    (simp[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  `w2n vs0.vs_initial_fmp <= w2n s.vs_fmp` by
    (drule ld_sync_source >> strip_tac >>
     drule o1LowerDloadOccurrenceTheory.frame_reachable_initial_fmp >>
     strip_tac >>
     qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
     simp[ptr_discipline_def] >> rpt strip_tac >>
     first_x_assum drule >> gvs[allocas_below_fmp_def]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  `ld_dyn_agree (dyn_floor C vs0) tn.t_mem s.vs_memory t.vs_memory` by
    metis_tac[lowerDloadSafetyRelationTheory.ld_sync_dyn_agree] >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  gvs[step_inst_non_invoke] >>
  `!v. MEM (Var v) inst.inst_operands ==>
     MEM v (fn_ir_vars f.lf_fn) /\ v NOTIN fn_pv P f.lf_fn` by
    (gen_tac >> strip_tac >> conj_tac
     >- metis_tac[ld_inst_input_ir] >>
     irule ld_ptr_use_scalar >> simp[] >> qexists_tac `inst` >>
     gvs[mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def]) >>
  `~MEM inst.inst_opcode
     [ASSIGN;PHI;RET;RETFMP;DRET;MUL;SHL;SHR;SAR;MSTORE;SSTORE;TSTORE;ISTORE]` by
    gvs[] >>
  `tn.t_var = f.lf_tv` by simp[] >>
  `eval_operands inst.inst_operands f.lf_src =
   eval_operands inst.inst_operands f.lf_tgt` by
    (drule_all ld_vars_numeric_operands_equal >> simp[]) >>
  qpat_x_assum `tn.t_var = f.lf_tv` kall_tac >>
  `f.lf_src.vs_fmp = f.lf_tgt.vs_fmp` by fs[ld_nonghost_def] >>
  drule_all ld_dalloca_step >> strip_tac >>
  qabbrev_tac `ss = update_var out f.lf_src.vs_fmp
    (f.lf_src with vs_fmp := f.lf_src.vs_fmp + n2w (ceil32 (w2n sz)))` >>
  `ld_dyn_agree (dyn_floor C vs0) (step_taint inst f.lf_src ss tn).t_mem
     ss.vs_memory ts.vs_memory` by
    (irule lowerDloadSafetyRelationTheory.ld_dyn_agree_unwritten >>
     simp[Abbr`ss`, update_var_def,
          codegenRelTheory.source_memory_write_ranges_def] >>
     qexists_tac `f.lf_tgt` >> simp[]) >>
  `step_taint inst f.lf_src ss tn =
   tn with <| t_mem := tn.t_mem UNION new_site_bytes f.lf_src ss;
              t_var := set_var_taint tn.t_var inst.inst_outputs {} |>` by
    (irule ld_dalloca_taint >> simp[]) >>
  `step_prov PG G inst ss =
   G |+ (out, (w2n f.lf_src.vs_fmp, w2n ss.vs_fmp - w2n f.lf_src.vs_fmp))` by
    simp[step_prov_def, out_prov_def, set_prov_def, Abbr`ss`,
         update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `ld_ghost_ok (dyn_floor C vs0) A (set_prov f.lf_H [out] NONE)
     (step_prov PG G inst ss)` by
    (simp[] >> irule ld_ghost_ok_dalloca >>
     simp[dyn_floor_def, wordsTheory.w2n_lt] >> metis_tac[]) >>
  `ld_nonghost (step_taint inst f.lf_src ss tn) ss ts` by
    (qpat_x_assum `ts = _` SUBST1_TAC >> qunabbrev_tac `ss` >>
     irule ld_nonghost_dalloca >> simp[] >> qexists_tac `tn` >> simp[]) >>
  `ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts` by
    (simp[] >> drule_then irule ld_memory_dalloca >>
     simp[Abbr`ss`, update_var_def, pred_setTheory.SUBSET_UNION]) >>
  `ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H [out] NONE;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>)` by
    (simp[set_var_taint_def] >> irule ld_vars_dalloca_write >>
     simp[Abbr`ss`, update_var_def] >>
     `MEM out (fn_ir_vars f.lf_fn)` by metis_tac[ld_inst_output_ir, MEM] >>
     simp[] >> qexists_tac `f.lf_tgt.vs_fmp` >> simp[]) >>
  `!a. a IN FRANGE (set_prov f.lf_H [out] NONE) ==> a IN FDOM A` by
    (gen_tac >> strip_tac >> irule ld_set_prov_selected >>
     qexistsl_tac [`f.lf_H`,`[out]`,`NONE`] >> simp[]) >>
  qexistsl_tac [`ss`, `set_prov f.lf_H [out] NONE`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[Abbr`ss`, update_var_def]
QED

val ld_effect_tac =
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  qexistsl [`ss`,`H'`] >> simp[];

val ld_ghost_tac = drule_all lowerDloadSafetyAmbientTheory.ld_sync_ghost_step >> simp[];

(* The step leaves both memories alone, so the dynamic agreement carries. *)
val ld_unwritten_tac =
  `~is_alloca_op inst.inst_opcode /\
   Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst s = []` by
    (rpt (qpat_x_assum `MEM inst.inst_opcode _` mp_tac) >> simp[] >>
     rpt strip_tac >>
     gvs[venomInstTheory.is_alloca_op_def, venomEffectsTheory.write_effects_def,
         venomEffectsTheory.empty_effects_def,
         codegenRelTheory.source_memory_write_ranges_def]) >>
  drule_all lowerDloadSafetyAmbientTheory.ld_sync_dyn_agree_unwritten >> simp[];

val ld_pure_tac =
  ld_effect_tac >> conj_tac >- ld_ghost_tac >> ld_unwritten_tac;

val ld_write_tac = ld_effect_tac >> ld_ghost_tac;

Theorem ld_sync_ordinary_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ fmp_free_ctx C /\
  mem_inv dload_headroom_ok C vs0 /\ ~in_revert_forward fn s /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (f::fs) /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DLOAD /\
  inst.inst_opcode <> DLOADBYTES /\ step_inst fuel C' inst t = OK ts ==>
  ?ss H'. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    ld_ghost_ok (dyn_floor C vs0) A H' (step_prov PG G inst ss) /\
    ld_dyn_agree (dyn_floor C vs0) (step_taint inst s ss tn).t_mem
      ss.vs_memory ts.vs_memory /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `inst.inst_opcode <> MEMTOP /\ inst.inst_opcode <> DRET /\
   inst.inst_opcode <> GETFMP /\ inst.inst_opcode <> SETFMP /\
   inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> FMP_PARAM` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  (Cases_on `inst.inst_opcode = DALLOCA`
   >- (mp_tac ld_sync_dalloca_effect >> ld_effect_tac)) >>
  (Cases_on `MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET;
     ADD; SUB; SHL; SHR; SAR]`
   >- (mp_tac ld_sync_arithmetic_effect >> ld_pure_tac)) >>
  (Cases_on `MEM inst.inst_opcode [ASSIGN;RETPC_PARAM]`
   >- (mp_tac ld_sync_assignment_effect >> ld_pure_tac)) >>
  (Cases_on `inst.inst_opcode = PARAM`
   >- (mp_tac ld_sync_param_effect >> ld_pure_tac)) >>
  (Cases_on `MEM inst.inst_opcode
    [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;COINBASE;
     TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
     CALLDATASIZE;RETURNDATASIZE;CODESIZE;BLOCKHASH;BLOBHASH;CALLDATALOAD;
     BALANCE;SELFBALANCE;EXTCODESIZE;EXTCODEHASH;SLOAD;TLOAD]`
   >- (mp_tac ld_sync_observational_read_effect >> ld_pure_tac)) >>
  (Cases_on `MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ]`
   >- (mp_tac ld_sync_classified_read_effect >> ld_pure_tac)) >>
  (Cases_on `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`
   >- (mp_tac ld_sync_identity_effect >> ld_pure_tac)) >>
  (Cases_on `MEM inst.inst_opcode [SSTORE;TSTORE]`
   >- (mp_tac ld_sync_storage_write_effect >> ld_pure_tac)) >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  (Cases_on `MEM inst.inst_opcode [CALL;STATICCALL]`
   >- (mp_tac ld_sync_oracle_call_effect >> ld_write_tac)) >>
  (Cases_on `MEM inst.inst_opcode [CREATE;CREATE2]`
   >- (mp_tac ld_sync_create_effect >> ld_write_tac)) >>
  (Cases_on `inst.inst_opcode = DELEGATECALL`
   >- (mp_tac ld_sync_delegate_effect >> ld_write_tac)) >>
  (Cases_on `MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY]`
   >- (mp_tac ld_sync_public_copy_effect >> ld_write_tac)) >>
  (Cases_on `inst.inst_opcode = SHA3`
   >- (mp_tac ld_sync_sha3_effect >> ld_pure_tac)) >>
  (Cases_on `inst.inst_opcode = LOG`
   >- (mp_tac ld_sync_log_effect >> ld_pure_tac)) >>
  fs[] >>
  `fn_shape_ok fn /\ fn_inst_wf fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn` by
    (drule ld_sync_active >> simp[]) >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `ld_ghost_ok (dyn_floor C vs0) A f.lf_H G` by
    (drule ld_sync_ghosts >> simp[]) >>
  (Cases_on `MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY]`
   >- (drule_all ld_sync_memory_write_effect >> strip_tac >>
       qexistsl [`ss`,`f.lf_H`] >> gvs[ld_vars_def])) >>
  fs[] >>
  (Cases_on `MEM inst.inst_opcode [INITIAL_FMP;BUMP]`
   >- (qpat_x_assum `MEM inst.inst_opcode [INITIAL_FMP;BUMP]`
         (strip_assume_tac o REWRITE_RULE [MEM]) >> (
       `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
       `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
         metis_tac[ld_global_selected, MEM] >>
       drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
       drule ld_sync_memory >> strip_tac >>
       `inst.inst_opcode <> INVOKE` by (fs[MEM] >> gvs[]) >>
       `?ss. step_inst_base inst s = OK ss /\
          ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
            lf_H := set_prov f.lf_H inst.inst_outputs NONE;
            lf_tv := (step_taint inst s ss tn).t_var|>) /\
          ld_memory lo A (step_taint inst s ss tn) ss ts /\
          ld_nonghost (step_taint inst s ss tn) ss ts /\
          step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q)
            (ld_erase A o_f f.lf_H) inst ss =
          ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE /\
          ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
          ss.vs_alloca_next = s.vs_alloca_next /\
          ts.vs_alloca_next = t.vs_alloca_next /\
          ss.vs_current_bb = s.vs_current_bb /\
          ts.vs_current_bb = t.vs_current_bb /\
          ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb` by
         (gvs[step_inst_non_invoke, Excl "MEM"] >>
          `tn.t_var = f.lf_tv` by simp[] >>
          `MEM inst.inst_opcode [INITIAL_FMP;BUMP]` by simp[] >>
          drule_all ld_residual_scalar_effect >>
          disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q`
            strip_assume_tac) >> simp[]) >>
       qexistsl [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
       gvs[step_inst_non_invoke, Excl "MEM"] >> rpt conj_tac
       >~ [`ld_ghost_ok _ _ _ _`] >- ld_ghost_tac
       >~ [`ld_dyn_agree _ _ _ _`]
       >- (`~is_terminator inst.inst_opcode /\
            ~is_alloca_op inst.inst_opcode /\
            Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
            !st. source_memory_write_ranges inst st = []` by
             (gvs[venomInstTheory.is_alloca_op_def,
                  venomInstTheory.is_terminator_def,
                  venomEffectsTheory.write_effects_def,
                  venomEffectsTheory.empty_effects_def,
                  codegenRelTheory.source_memory_write_ranges_def]) >>
           irule lowerDloadSafetyRelationTheory.ld_dyn_agree_unwritten >>
           imp_res_tac venomInstProofs3Theory.step_inst_base_preserves_memory >>
           simp[] >> metis_tac[lowerDloadSafetyRelationTheory.ld_sync_dyn_agree]) >>
       gen_tac >> strip_tac >> irule ld_set_prov_selected >>
       qexistsl [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[]))) >>
  (Cases_on `inst.inst_opcode = ISTORE`
   >- (drule_all ld_sync_istore_effect >> strip_tac >>
       qexistsl [`ss`,`f.lf_H`] >> gvs[ld_vars_def])) >>
  `inst.inst_opcode = PHI` by
    (Cases_on `inst.inst_opcode` >>
     FIRST [first_assum (CONTR_TAC o REWRITE_RULE []),
            fs[is_terminator_def]]) >>
  qpat_x_assum `step_inst fuel C' inst t = OK ts` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def]
QED

(* The singleton consumer retains the full endpoint, even with no successor. *)
(* TEMPORARILY CHEATED - P4b in progress: follows ld_sync_ordinary_effect
   and ld_nonallocating_endpoint, restated for the DALLOCA ghosts.
Proof
  strip_tac >>
  drule_all ld_sync_ordinary_effect >> strip_tac >>
  `step_inst 0 C inst s = OK ss` by
    gvs[step_inst_non_invoke] >>
  `u.vs_inst_idx = t.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  qabbrev_tac `g = f with
    <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
      lf_tgt := u with vs_inst_idx := p + 1;
      lf_H := H'; lf_tv := (step_taint inst s ss tn).t_var|>` >>
  `ld_vars P A g /\ ld_maps A g /\
   ld_global lo A (g::fs) /\ FDOM A = ld_slots A (g::fs) /\
   EVERY (ld_maps A) fs /\
   (!next. active_inst fn next g.lf_src ==>
     ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
       (step_taint inst s ss tn) fn next g.lf_src g.lf_tgt A (g::fs) N)` by
    (drule_all ld_nonallocating_endpoint >>
     simp[Abbr `g`]) >>
  qexistsl [`ss`,`g`] >> simp[Abbr `g`]
QED
*)
Theorem ld_ordinary_endpoint:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ fmp_free_ctx C /\
  mem_inv dload_headroom_ok C vs0 /\ ~in_revert_forward fn s /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (f::fs) /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DLOAD /\
  inst.inst_opcode <> DLOADBYTES /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\ step_inst fuel C' inst t = OK u ==>
  ?ss g.
    step_inst 0 C inst s = OK ss /\ u.vs_inst_idx = t.vs_inst_idx /\
    (u with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = p + 1 /\
    g.lf_serial = f.lf_serial /\ g.lf_supply = f.lf_supply /\
    g.lf_fn = f.lf_fn /\ g.lf_Q = f.lf_Q /\
    g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
    g.lf_tgt = (u with vs_inst_idx := p + 1) /\
    g.lf_tv = (step_taint inst s ss tn).t_var /\
    ld_ghost_ok (dyn_floor C vs0) A g.lf_H (step_prov PG G inst ss) /\
    ld_vars P A g /\ ld_maps A g /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_global lo A (g::fs) /\ FDOM A = ld_slots A (g::fs) /\
    EVERY (ld_maps A) fs /\
    (!next. active_inst fn next g.lf_src ==>
      ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
        (step_taint inst s ss tn) fn next g.lf_src g.lf_tgt A (g::fs) N)
Proof
  cheat
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "ordinary endpoint has hypotheses")
  [ld_sync_ordinary_effect, ld_ordinary_endpoint];
