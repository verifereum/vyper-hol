(* TOP-LEVEL: real fragment paths preserve the allocator invariant, including
   completed blocks with internal calls. Helpers lift the existing native
   execution invariant through straight instruction prefixes. *)
Theory abiPathAllocInv
Ancestors
  abiAllocationFrame fragBlockPath exprLoweringProps venomMemProps venomExecProps
  venomExecSemantics venomMemDefs venomState venomInst relation list words arithmetic

Theorem step_inst_base_alloca_inv:
  !inst ss out.
    step_inst_base inst ss = OK out /\ alloca_inv ss ==> alloca_inv out
Proof
  rpt gen_tac >> strip_tac >> drule step_inst_base_OK_not_INVOKE >> DISCH_TAC >>
  mp_tac (Q.SPECL [`0`, `ARB:venom_context`, `inst`, `ss`, `out`] alloca_inv_step_inst) >>
  impl_tac >- simp[step_inst_non_invoke] >> simp[]
QED

Theorem run_inst_seq_alloca_inv:
  !insts ss out. run_inst_seq insts ss = OK out /\ alloca_inv ss ==> alloca_inv out
Proof
  Induct_on `insts` >- simp[run_inst_seq_def] >> qx_gen_tac `inst` >>
  rpt gen_tac >> simp_tac bool_ss [Once run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base inst ss` >> gvs[] >>
  drule_all step_inst_base_alloca_inv >> DISCH_TAC >> first_x_assum drule_all >> simp[]
QED

Theorem fragment_prefix_alloca_inv:
  !func ss out. fragment_prefix func ss out /\ alloca_inv ss ==> alloca_inv out
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fragment_prefix _ _ _` (mp_tac o REWRITE_RULE [fragment_prefix_def]) >>
  disch_then (qx_choose_then `bb` (qx_choose_then `insts` (qx_choose_then `result` strip_assume_tac))) >>
  drule_all run_inst_seq_alloca_inv >> DISCH_TAC >>
  irule abi_allocation_fields_inv >> qexists_tac `result` >> simp[]
QED

Theorem fragment_jump_alloca_inv:
  !ctx func ss out. fragment_jump ctx func ss out /\ alloca_inv ss ==> alloca_inv out
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fragment_jump _ _ _ _` (strip_assume_tac o REWRITE_RULE [fragment_jump_def]) >>
  drule_all alloca_inv_exec_block >> simp[]
QED

Theorem fragment_step_alloca_inv:
  !ctx func ss out. fragment_step ctx func ss out /\ alloca_inv ss ==> alloca_inv out
Proof
  rpt gen_tac >> simp_tac bool_ss [fragment_step_def] >> strip_tac >>
  FIRST [drule_all fragment_jump_alloca_inv >> simp[], drule_all fragment_prefix_alloca_inv >> simp[]]
QED

Theorem fragment_path_alloca_inv:
  !ctx func ss out. fragment_path ctx func ss out /\ alloca_inv ss ==> alloca_inv out
Proof
  gen_tac >> gen_tac >> REWRITE_TAC [fragment_path_def, GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac RTC_INDUCT >> conj_tac >- simp[] >>
  MAP_EVERY qx_gen_tac [`ss_start`, `ss_mid`, `ss_final`] >> strip_tac >> DISCH_TAC >>
  `alloca_inv ss_mid` by (drule_all fragment_step_alloca_inv >> simp[]) >>
  first_x_assum irule >> first_assum MATCH_ACCEPT_TAC
QED
