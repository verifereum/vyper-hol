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
  venomExecSemantics ptrDiscipline finite_map list words

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
    step_prov PG G inst ss = ld_erase A o_f H' /\
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
  `inst.inst_opcode <> DALLOCA` by
    (`MEM fn C.ctx_functions` by
       (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[NoAsms, ld_sync_def] >> metis_tac[]) >>
     fs[fmp_free_ctx_def, EVERY_MEM, no_raw_fmp_ops_def] >>
     metis_tac[is_raw_fmp_opcode_def]) >>
  (Cases_on `MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET;
     ADD; SUB; SHL; SHR; SAR]`
   >- (irule ld_sync_arithmetic_effect >> simp[] >> metis_tac[])) >>
  (Cases_on `MEM inst.inst_opcode [ASSIGN;RETPC_PARAM]`
   >- (irule ld_sync_assignment_effect >> simp[] >> metis_tac[])) >>
  (Cases_on `inst.inst_opcode = PARAM`
   >- (drule_all ld_sync_param_effect >> simp[])) >>
  (Cases_on `MEM inst.inst_opcode
    [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;COINBASE;
     TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
     CALLDATASIZE;RETURNDATASIZE;CODESIZE;BLOCKHASH;BLOBHASH;CALLDATALOAD;
     BALANCE;SELFBALANCE;EXTCODESIZE;EXTCODEHASH;SLOAD;TLOAD]`
   >- (irule ld_sync_observational_read_effect >> simp[] >> metis_tac[])) >>
  (Cases_on `MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ]`
   >- (irule ld_sync_classified_read_effect >> simp[] >> metis_tac[])) >>
  (Cases_on `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`
   >- (irule ld_sync_identity_effect >> simp[] >> metis_tac[])) >>
  (Cases_on `MEM inst.inst_opcode [SSTORE;TSTORE]`
   >- (irule ld_sync_storage_write_effect >> simp[] >> metis_tac[])) >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  (Cases_on `MEM inst.inst_opcode [CALL;STATICCALL]`
   >- (drule_all ld_sync_oracle_call_effect >> strip_tac >>
       qexistsl [`ss`,`H'`] >> simp[])) >>
  (Cases_on `MEM inst.inst_opcode [CREATE;CREATE2]`
   >- (drule_all ld_sync_create_effect >> strip_tac >>
       qexistsl [`ss`,`H'`] >> simp[])) >>
  (Cases_on `inst.inst_opcode = DELEGATECALL`
   >- (drule_all ld_sync_delegate_effect >> strip_tac >>
       qexistsl [`ss`,`H'`] >> simp[])) >>
  (Cases_on `MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY]`
   >- (drule_all ld_sync_public_copy_effect >> strip_tac >>
       qexistsl [`ss`,`H'`] >> simp[])) >>
  (Cases_on `inst.inst_opcode = SHA3`
   >- (drule_all ld_sync_sha3_effect >> strip_tac >>
       qexistsl [`ss`,`H'`] >> simp[])) >>
  (Cases_on `inst.inst_opcode = LOG`
   >- (drule_all ld_sync_log_effect >> strip_tac >>
       qexistsl [`ss`,`H'`] >> simp[])) >>
  fs[] >>
  `fn_shape_ok fn /\ fn_inst_wf fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn` by
    (drule ld_sync_active >> simp[]) >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  (Cases_on `MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY]`
   >- (drule_all ld_sync_memory_write_effect >> strip_tac >>
       `G = ld_erase A o_f f.lf_H` by (drule ld_sync_ghosts >> simp[]) >>
       qexistsl [`ss`,`f.lf_H`] >> gvs[ld_vars_def])) >>
  fs[] >>
  (Cases_on `MEM inst.inst_opcode [INITIAL_FMP;BUMP]`
   >- (`taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
       `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
         metis_tac[ld_global_selected, MEM] >>
       drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
       drule ld_sync_ghosts >> simp[Excl "MEM"] >> strip_tac >>
       drule ld_sync_memory >> strip_tac >>
       `inst.inst_opcode <> INVOKE` by (fs[MEM] >> gvs[]) >>
       gvs[step_inst_non_invoke, Excl "MEM"] >>
       `tn.t_var = f.lf_tv` by simp[] >>
       `MEM inst.inst_opcode [INITIAL_FMP;BUMP]` by simp[] >>
       drule_all ld_residual_scalar_effect >>
       disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
       qexistsl [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >> simp[] >>
       gen_tac >> strip_tac >> irule ld_set_prov_selected >>
       qexistsl [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[])) >>
  (Cases_on `inst.inst_opcode = ISTORE`
   >- (drule_all ld_sync_istore_effect >> strip_tac >>
       `G = ld_erase A o_f f.lf_H` by (drule ld_sync_ghosts >> simp[]) >>
       qexistsl [`ss`,`f.lf_H`] >> gvs[ld_vars_def])) >>
  `inst.inst_opcode = PHI` by
    (Cases_on `inst.inst_opcode` >>
     FIRST [first_assum (CONTR_TAC o REWRITE_RULE []),
            fs[is_terminator_def]]) >>
  qpat_x_assum `step_inst fuel C' inst t = OK ts` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def]
QED

(* The singleton consumer retains the full endpoint, even with no successor. *)
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
    step_prov PG G inst ss = ld_erase A o_f g.lf_H /\
    ld_vars P A g /\ ld_maps A g /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_global lo A (g::fs) /\ FDOM A = ld_slots A (g::fs) /\
    EVERY (ld_maps A) fs /\
    (!next. active_inst fn next g.lf_src ==>
      ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
        (step_taint inst s ss tn) fn next g.lf_src g.lf_tgt A (g::fs) N)
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

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "ordinary endpoint has hypotheses")
  [ld_sync_ordinary_effect, ld_ordinary_endpoint];
