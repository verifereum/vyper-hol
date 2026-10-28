(* TOP-LEVEL: real successful native paths preserve old allocation records,
   put new records above the initial frontier, and retain live-local backing.
   Internal calls are included. Helpers lift the native step to blocks. *)
Theory allocationPathGrowth
Ancestors
  allocationGrowth abiStepAllocRecords abiPathAllocRecords abiPathAllocInv abiBlockInvariant
  abiAllocationFrame memoryValueSnapshot typedCopyStateFrame
  exprLoweringProps compileEnv fragBlockPath venomMemProps venomExecProps
  venomExecSemantics venomMemDefs venomState venomInst finite_map relation list pair words arithmetic

Theorem allocation_growth_map_eq:
  !before after.
    after.vs_allocas = before.vs_allocas /\ before.vs_alloca_next <= after.vs_alloca_next ==>
    allocation_growth before after
Proof
  simp[allocation_growth_def] >> rpt strip_tac >> gvs[]
QED

Theorem allocation_growth_index[simp]:
  !before after index.
    allocation_growth before (after with vs_inst_idx := index) = allocation_growth before after
Proof
  simp[allocation_growth_def]
QED

Theorem exec_alloca_allocation_growth:
  !inst ss alloc_size out.
    exec_alloca inst ss alloc_size = OK out ==> allocation_growth ss out
Proof
  rpt gen_tac >> simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >>
  gvs[allocation_growth_def, update_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[FLOOKUP_UPDATE] >> rw[] >> gvs[]
QED

Theorem step_inst_base_allocation_growth:
  !inst ss out.
    step_inst_base inst ss = OK out ==> allocation_growth ss out
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `step_inst_base _ _ = _` (mp_tac o ONCE_REWRITE_RULE [step_inst_base_def]) >>
      asm_simp_tac bool_ss [] >> strip_tac >> gvs[AllCaseEqs()] >>
      drule exec_alloca_allocation_growth >> simp[]) >>
  drule step_inst_base_OK_not_INVOKE >> DISCH_TAC >>
  mp_tac (Q.SPECL [`inst`, `ss`, `out`] step_inst_base_preserves_allocas) >> impl_tac >- simp[] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`inst`, `ss`, `out`] step_inst_base_preserves_alloca_next) >> impl_tac >- simp[] >> DISCH_TAC >>
  irule allocation_growth_map_eq >> simp[]
QED

Theorem step_inst_allocation_growth:
  !fuel ctx inst ss out.
    alloca_inv ss /\ step_inst fuel ctx inst ss = OK out ==> allocation_growth ss out
Proof
  rpt gen_tac >> strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_allocas >> DISCH_TAC >>
      drule_all step_inst_alloca_frontier >> DISCH_TAC >> irule allocation_growth_map_eq >> simp[]) >>
  `step_inst_base inst ss = OK out` by fs[step_inst_non_invoke] >>
  drule step_inst_base_allocation_growth >> simp[]
QED

Theorem run_inst_seq_allocation_growth:
  !insts ss out.
    run_inst_seq insts ss = OK out ==> allocation_growth ss out
Proof
  Induct_on `insts` >- simp[run_inst_seq_def] >> qx_gen_tac `inst` >>
  rpt gen_tac >> simp_tac bool_ss [Once run_inst_seq_def] >> DISCH_TAC >>
  Cases_on `step_inst_base inst ss` >> gvs[] >>
  drule step_inst_base_allocation_growth >> DISCH_TAC >> first_x_assum drule >> DISCH_TAC >>
  irule allocation_growth_trans >> goal_assum drule >> simp[]
QED

Theorem exec_block_allocation_growth:
  !fuel ctx bb ss out.
    alloca_inv ss /\ exec_block fuel ctx bb ss = OK out ==> allocation_growth ss out
Proof
  rpt gen_tac >> strip_tac >>
  `!state inst next. get_instruction bb state.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst state = OK next /\ alloca_inv state /\ allocation_growth ss state ==>
    (alloca_inv next /\ allocation_growth ss next) /\
    (alloca_inv (next with vs_inst_idx := SUC state.vs_inst_idx) /\
      allocation_growth ss (next with vs_inst_idx := SUC state.vs_inst_idx))` by
    (rpt gen_tac >> strip_tac >> drule_all alloca_inv_step_inst >> DISCH_TAC >>
     drule_all step_inst_allocation_growth >> DISCH_TAC >>
     `allocation_growth ss next` by (irule allocation_growth_trans >> qexists_tac `state` >> simp[]) >>
     fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`\state. alloca_inv state /\ allocation_growth ss state`, `fuel`, `ctx`, `bb`, `ss`, `out`]
    exec_block_invariant) >>
  impl_tac >- (simp_tac bool_ss [] >> rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> simp[]
QED

Theorem fragment_prefix_allocation_growth:
  !func ss out. fragment_prefix func ss out ==> allocation_growth ss out
Proof
  rpt gen_tac >> DISCH_TAC >>
  qpat_x_assum `fragment_prefix _ _ _` (mp_tac o REWRITE_RULE [fragment_prefix_def]) >>
  disch_then (qx_choose_then `bb` (qx_choose_then `insts` (qx_choose_then `result` strip_assume_tac))) >>
  drule_all run_inst_seq_allocation_growth >> simp[]
QED

Theorem fragment_jump_allocation_growth:
  !ctx func ss out.
    alloca_inv ss /\ fragment_jump ctx func ss out ==> allocation_growth ss out
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fragment_jump _ _ _ _` (strip_assume_tac o REWRITE_RULE [fragment_jump_def]) >>
  drule_all exec_block_allocation_growth >> simp[allocation_growth_def]
QED

Theorem fragment_step_allocation_growth:
  !ctx func ss out.
    alloca_inv ss /\ fragment_step ctx func ss out ==> allocation_growth ss out
Proof
  rpt gen_tac >> simp_tac bool_ss [fragment_step_def] >> strip_tac >>
  FIRST [drule_all fragment_jump_allocation_growth >> simp[], drule fragment_prefix_allocation_growth >> simp[]]
QED

Theorem fragment_path_allocation_growth:
  !ctx func ss out.
    fragment_path ctx func ss out /\ alloca_inv ss ==> allocation_growth ss out
Proof
  gen_tac >> gen_tac >> REWRITE_TAC [fragment_path_def, GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac RTC_INDUCT >> conj_tac >- simp[] >>
  MAP_EVERY qx_gen_tac [`ss_start`, `ss_mid`, `ss_final`] >> strip_tac >> DISCH_TAC >>
  `alloca_inv ss_mid` by (drule_all fragment_step_alloca_inv >> simp[]) >>
  `allocation_growth ss_start ss_mid` by (drule_all fragment_step_allocation_growth >> simp[]) >>
  `allocation_growth ss_mid ss_final` by (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  irule allocation_growth_trans >> qexists_tac `ss_mid` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native allocation growth: " ^ name)
  end) (DB.thms "allocationPathGrowth")
