Theory staticAbortStoppedObservationPrefix
Ancestors
  fnStaticAbortBodyFacts symBlockBody contextStaticAbortRel staticAbortDefs
  contextCodegenRel asmSem asmSymSem codegenSymRel stackOpSim

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

(* These lexical predicates are the stopped body observations, not constants. *)
Theorem stopped_abort_observation_prefix:
  let A = \rpolicy unit cpl prog ctx lo o2pc Inv env ast ss vs'.
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
       cut.as_requests = vs'.vs_requests)
  in
  !rpolicy unit cpl prog ctx lo o2pc Inv env n ast0 ast1 ss0 ss1 vs'.
    asm_steps lo o2pc prog n ast0 = AsmOK ast1 /\
    sym_steps prog env n ss0 = SymOK ss1 /\
    A rpolicy unit cpl prog ctx lo o2pc Inv env ast1 ss1 vs' ==>
    A rpolicy unit cpl prog ctx lo o2pc Inv env ast0 ss0 vs'
Proof
  simp_tac (srw_ss()) [LET_THM] >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then DISJ_CASES_TAC
  >- (qpat_x_assum `?n out. _` strip_assume_tac >>
      disj1_tac >> qexistsl_tac [`n + n'`, `out`] >>
      simp[asm_steps_add, sym_steps_add])
  >> qpat_x_assum `?nc cut sc. _` strip_assume_tac >>
  disj2_tac >> qexistsl_tac [`n + nc`, `cut`, `sc`] >>
  simp[asm_steps_add, sym_steps_add] >> metis_tac[]
QED

Theorem stopped_result_observation_prefix:
  let A = \rpolicy unit cpl prog ctx lo o2pc Inv env ast ss vs'.
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
       cut.as_requests = vs'.vs_requests)
  in
  let R = \rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast ss res.
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
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))
  in
  !rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0
    n ast0 ast1 ss0 ss1 res.
    asm_steps lo o2pc prog n ast0 = AsmOK ast1 /\
    sym_steps prog env n ss0 = SymOK ss1 /\
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast1 ss1 res ==>
    R rpolicy unit cpl prog ctx lo o2pc Inv env fn mem0 pc_ret rest srest labs0 ast0 ss0 res
Proof
  qmatch_goalsub_abbrev_tac `LET _ A` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  simp_tac (srw_ss()) [LET_THM] >> rpt gen_tac >> strip_tac >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (first_x_assum drule >> strip_tac >>
      qexistsl_tac [`n + n'`, `out`] >> simp[asm_steps_add, sym_steps_add])
  >- (first_x_assum drule >> disch_tac >>
      simp[Abbr `A`] >>
      irule (SRULE [LET_THM] stopped_abort_observation_prefix) >>
      qexistsl_tac [`ast1`, `n`, `ss1`] >> simp[] >>
      pop_assum mp_tac >> simp[])
  >> first_x_assum drule >> strip_tac >>
  qexistsl_tac [`n + n'`, `out`, `ss'`] >> simp[asm_steps_add, sym_steps_add]
QED
