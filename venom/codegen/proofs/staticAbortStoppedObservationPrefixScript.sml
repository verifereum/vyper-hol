Theory staticAbortStoppedObservationPrefix
Ancestors
  fnStaticAbortBodyFacts symBlockBody contextStaticAbortRel staticAbortDefs
  contextCodegenRel asmSem asmSymSem asmSymBridge codegenSymRel stackOpSim

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

(* These predicates name the stopped body observations, not new constants. *)
Theorem stopped_abort_observation_prefix_mode:
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
  !rpolicy unit cpl prog ctx lo o2pc Inv env n ast0 ast1 ss0 ss1 vs'.
    asm_steps lo o2pc prog n ast0 = AsmOK ast1 /\
    sym_steps_mode allow_own prog env own n ss0 = SymOK ss1 /\
    A rpolicy unit cpl prog ctx lo o2pc Inv env ast1 ss1 vs' ==>
    A rpolicy unit cpl prog ctx lo o2pc Inv env ast0 ss0 vs'
Proof
  ntac 3 gen_tac >> disch_then SUBST1_TAC >> BETA_TAC >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then DISJ_CASES_TAC
  >- (qpat_x_assum `?n out. _` strip_assume_tac >>
      disj1_tac >> qexistsl_tac [`n + n'`, `out`] >>
      simp[asm_steps_add, sym_steps_mode_add])
  >> qpat_x_assum `?nc cut sc. _` strip_assume_tac >>
  disj2_tac >> qexistsl_tac [`n + nc`, `cut`, `sc`] >>
  simp[asm_steps_add, sym_steps_mode_add] >> metis_tac[]
QED

Theorem stopped_abort_observation_prefix:
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
  !rpolicy unit cpl prog ctx lo o2pc Inv env n ast0 ast1 ss0 ss1 vs'.
    asm_steps lo o2pc prog n ast0 = AsmOK ast1 /\
    sym_steps prog env n ss0 = SymOK ss1 /\
    A rpolicy unit cpl prog ctx lo o2pc Inv env ast1 ss1 vs' ==>
    A rpolicy unit cpl prog ctx lo o2pc Inv env ast0 ss0 vs'
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES]
    (Q.SPECL [`F`, `[]`] stopped_abort_observation_prefix_mode))
QED

Theorem stopped_result_observation_prefix_mode:
  !allow_own own R. R = (\rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss res.
    (!vs'. res = Halt vs' ==>
       ?n out. asm_steps lo o2pc prog n ast = AsmHalt out /\
         venom_asm_terminal_rel vs' out /\ sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!a vs'. res = Abort a vs' ==>
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
          cut.as_requests = vs'.vs_requests)) /\
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
  !rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0
    n ast0 ast1 ss0 ss1 res.
    asm_steps lo o2pc prog n ast0 = AsmOK ast1 /\
    sym_steps_mode allow_own prog env own n ss0 = SymOK ss1 /\
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast1 ss1 res ==>
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast0 ss0 res
Proof
  ntac 3 gen_tac >> disch_then SUBST1_TAC >> BETA_TAC >>
  rpt gen_tac >> strip_tac >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (first_x_assum drule >> strip_tac >>
      qexistsl_tac [`n + n'`, `out`] >> simp[asm_steps_add, sym_steps_mode_add])
  >- (first_x_assum drule >> disch_tac >>
      irule (BETA_RULE (Unwind.UNWIND_FORALL_RULE
        (Q.SPECL [`allow_own`, `own`] stopped_abort_observation_prefix_mode))) >>
      qexistsl_tac [`ast1`, `n`, `ss1`] >> simp[] >>
      pop_assum mp_tac >> simp[])
  >> first_x_assum drule >> strip_tac >>
  qexistsl_tac [`n + n'`, `out`, `ss'`] >> simp[asm_steps_add, sym_steps_mode_add]
QED

Theorem stopped_result_observation_prefix:
  !R. R = (\rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss res.
    (!vs'. res = Halt vs' ==>
       ?n out. asm_steps lo o2pc prog n ast = AsmHalt out /\
         venom_asm_terminal_rel vs' out /\ sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. res = Abort a vs' ==>
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
          cut.as_requests = vs'.vs_requests)) /\
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
  !rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0
    n ast0 ast1 ss0 ss1 res.
    asm_steps lo o2pc prog n ast0 = AsmOK ast1 /\
    sym_steps prog env n ss0 = SymOK ss1 /\
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast1 ss1 res ==>
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast0 ss0 res
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES]
    (Q.SPECL [`F`, `[]`] stopped_result_observation_prefix_mode))
QED
