Theory dftGasToListReachBoundary
Ancestors
  dftGasOracleDefs contextCodegenRel venomExecProofs venomInst list

Theorem active_inst_lookup_distinct:
  !fn inst s.
    ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s ==>
    ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
         get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rw[active_inst_def, fn_labels_def] >> qexists_tac `bb` >>
  simp[get_instruction_def] >> irule MEM_lookup_block >> simp[]
QED

Theorem ev_reachable_function_member:
  !orc vs0 ctx p d fn inst s.
    ev_reachable orc vs0 ctx p d fn inst s ==>
    MEM fn ctx.ctx_functions
Proof
  ho_match_mp_tac ev_reachable_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> metis_tac[lookup_function_MEM]
QED

Theorem ev_reachable_wf_function:
  EVERY wf_function ctx.ctx_functions /\
  ev_reachable orc vs0 ctx p d fn inst s ==> wf_function fn
Proof
  metis_tac[ev_reachable_function_member, EVERY_MEM]
QED
