(* TOP-LEVEL: successful fragment paths extend the allocation map and
   preserve every previously backed window, including across internal calls.
   Helpers lift native record preservation through blocks and prefixes. *)
Theory abiPathAllocRecords
Ancestors
  abiStepAllocRecords abiBlockInvariant abiAllocatedWindows abiPathAllocInv fragBlockPath exprLoweringProps
  venomExecSemantics venomState venomInst relation finite_map list pair words arithmetic

Theorem run_inst_seq_lookup_old:
  !insts ss out id offset recorded_size.
    run_inst_seq insts ss = OK out /\ FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size) ==>
    FLOOKUP out.vs_allocas id = SOME (offset,recorded_size)
Proof
  Induct_on `insts` >- simp[run_inst_seq_def] >> qx_gen_tac `inst` >>
  rpt gen_tac >> simp_tac bool_ss [Once run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base inst ss` >> gvs[] >>
  drule_all step_inst_base_lookup_old >> DISCH_TAC >> first_x_assum drule_all >> simp[]
QED

Theorem exec_block_lookup_old:
  !fuel ctx bb ss out id offset recorded_size.
    exec_block fuel ctx bb ss = OK out /\ FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size) ==>
    FLOOKUP out.vs_allocas id = SOME (offset,recorded_size)
Proof
  rpt gen_tac >> strip_tac >>
  `!state inst next.
    get_instruction bb state.vs_inst_idx = SOME inst /\ step_inst fuel ctx inst state = OK next /\
    FLOOKUP state.vs_allocas id = SOME (offset,recorded_size) ==>
    FLOOKUP next.vs_allocas id = SOME (offset,recorded_size) /\
    FLOOKUP (next with vs_inst_idx := SUC state.vs_inst_idx).vs_allocas id = SOME (offset,recorded_size)` by
    (rpt gen_tac >> strip_tac >> drule_all step_inst_lookup_old >> simp[]) >>
  mp_tac (Q.SPECL [`\state. FLOOKUP state.vs_allocas id = SOME (offset,recorded_size)`,
    `fuel`, `ctx`, `bb`, `ss`, `out`] exec_block_invariant) >>
  impl_tac >- (simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem fragment_prefix_lookup_old:
  !func ss out id offset recorded_size.
    fragment_prefix func ss out /\ FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size) ==>
    FLOOKUP out.vs_allocas id = SOME (offset,recorded_size)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fragment_prefix _ _ _` (mp_tac o REWRITE_RULE [fragment_prefix_def]) >>
  disch_then (qx_choose_then `bb` (qx_choose_then `insts` (qx_choose_then `result` strip_assume_tac))) >>
  drule_all run_inst_seq_lookup_old >> DISCH_TAC >> simp[]
QED

Theorem fragment_jump_lookup_old:
  !ctx func ss out id offset recorded_size.
    fragment_jump ctx func ss out /\ FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size) ==>
    FLOOKUP out.vs_allocas id = SOME (offset,recorded_size)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fragment_jump _ _ _ _` (strip_assume_tac o REWRITE_RULE [fragment_jump_def]) >>
  drule_all exec_block_lookup_old >> simp[]
QED

Theorem fragment_step_lookup_old:
  !ctx func ss out id offset recorded_size.
    fragment_step ctx func ss out /\ FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size) ==>
    FLOOKUP out.vs_allocas id = SOME (offset,recorded_size)
Proof
  rpt gen_tac >> simp_tac bool_ss [fragment_step_def] >> strip_tac >>
  FIRST [drule_all fragment_jump_lookup_old >> simp[], drule_all fragment_prefix_lookup_old >> simp[]]
QED

Theorem fragment_step_allocas_extend:
  !ctx func ss out.
    fragment_step ctx func ss out ==> ss.vs_allocas SUBMAP out.vs_allocas
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [SUBMAP_FLOOKUP_EQN] >>
  MAP_EVERY qx_gen_tac [`id`, `recorded_region`] >> DISCH_TAC >>
  PairCases_on `recorded_region` >> drule_all fragment_step_lookup_old >> simp[]
QED

Theorem fragment_path_allocas_extend:
  !ctx func ss out.
    fragment_path ctx func ss out ==> ss.vs_allocas SUBMAP out.vs_allocas
Proof
  gen_tac >> gen_tac >> REWRITE_TAC [fragment_path_def] >>
  ho_match_mp_tac RTC_INDUCT >> conj_tac >- simp[] >>
  MAP_EVERY qx_gen_tac [`ss_start`, `ss_mid`, `ss_final`] >> strip_tac >>
  drule fragment_step_allocas_extend >> DISCH_TAC >>
  irule SUBMAP_TRANS >> qexists_tac `ss_mid.vs_allocas` >> simp[]
QED

Theorem fragment_path_lookup_old:
  !ctx func ss out id offset recorded_size.
    fragment_path ctx func ss out /\ FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size) ==>
    FLOOKUP out.vs_allocas id = SOME (offset,recorded_size)
Proof
  rpt gen_tac >> strip_tac >> drule fragment_path_allocas_extend >> DISCH_TAC >>
  drule_all FLOOKUP_SUBMAP >> simp[]
QED

Theorem fragment_path_allocated_window:
  !ctx func ss out id offset byte_count.
    fragment_path ctx func ss out /\ abi_allocated_window ss id offset byte_count ==>
    abi_allocated_window out id offset byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_allocated_window _ _ _ _` (strip_assume_tac o REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP ss.vs_allocas id = SOME (window_base,window_size)` >>
  drule_all fragment_path_lookup_old >> DISCH_TAC >>
  simp_tac bool_ss [abi_allocated_window_def] >> qexistsl_tac [`window_base`, `window_size`] >> simp[]
QED

Theorem fragment_path_allocation_post:
  !ctx func ss out.
    fragment_path ctx func ss out /\ alloca_inv ss ==>
    alloca_inv out /\ ss.vs_allocas SUBMAP out.vs_allocas /\
    (!id offset byte_count. abi_allocated_window ss id offset byte_count ==>
      abi_allocated_window out id offset byte_count)
Proof
  rpt gen_tac >> strip_tac >> drule_all fragment_path_alloca_inv >> DISCH_TAC >>
  drule fragment_path_allocas_extend >> DISCH_TAC >>
  rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >>
  rpt gen_tac >> DISCH_TAC >> drule_all fragment_path_allocated_window >> simp[]
QED
