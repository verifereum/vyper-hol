(* Execution agreement and memory-safe transport for sparse stores. *)
Theory storeSlotsMemoryTransfer
Ancestors
  storeSlotsMemoryPaths exprSimAbiGasBridge abiEncoderPrefixSafety
  fragGasPath abiEncoderObserver fragExec venomState list

Theorem gas_path_first_cut_prefix:
  !ctx fn s n r. gas_path ctx fn s n r ==>
  !cut region t.
    r = OK t /\ (t.vs_current_bb,t.vs_inst_idx) = cut /\ region s /\
    (!u k v. region u /\ gas_path_edge ctx fn u k (OK v) ==>
      region v /\ abi_observer_step ctx fn cut u v) ==>
    local_prefix ctx fn cut s t
Proof
  ho_match_mp_tac gas_path_ind >> rpt strip_tac
  >- (gvs[] >> irule (cj 1 local_prefix_rules) >> simp[])
  >- (gvs[] >>
      rename1 `gas_path_edge ctx fn s n (OK middle)` >>
      irule (cj 2 local_prefix_rules) >>
      qexists_tac `middle` >> conj_tac >- metis_tac[] >>
      first_x_assum irule >> metis_tac[]) >>
  gvs[exit_result_def]
QED

Theorem gas_edge_observer_nonphi:
  gas_path_edge ctx fn s n (OK t) /\
  (s.vs_current_bb,s.vs_inst_idx) <> cut /\
  (!bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst ==>
    inst.inst_opcode <> INVOKE) /\
  (t.vs_inst_idx = 0 ==> ?bb.
    lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) ==>
  abi_observer_step ctx fn cut s t
Proof
  rw[gas_path_edge_def] >> gvs[exit_result_def] >>
  `inst.inst_opcode <> INVOKE` by metis_tac[] >>
  gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  simp[abi_observer_step_def, venomExecSemanticsTheory.step_inst_non_invoke] >>
  gvs[venomStateTheory.jump_to_def] >>
  simp[eval_phis_no_phi] >>
  qpat_x_assum `OK t = _` (assume_tac o SYM) >> gvs[exit_result_def]
QED

Theorem gas_edge_cut_stop:
  lookup_block (FST cut) fn.fn_blocks = SOME bb /\
  get_instruction bb (SND cut) = SOME (mk_inst id STOP [] []) /\
  (s.vs_current_bb,s.vs_inst_idx) = cut ==>
  ~gas_path_edge ctx fn s n (OK t)
Proof
  Cases_on `cut` >>
  simp[gas_path_edge_def] >> rpt strip_tac >> gvs[] >>
  gvs[venomExecSemanticsTheory.step_inst_non_invoke,
      venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      venomInstTheory.mk_inst_def, exit_result_def]
QED

Theorem observer_nonstart_phi_zero:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  lbl <> sa.cs_current_bb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> Cases_on `bb.bb_instructions`
  >- simp[venomExecSemanticsTheory.phi_prefix_length_def] >>
  rename1 `bb.bb_instructions = inst::rest` >>
  Cases_on `(lbl,0) = frag_observer_cut sb`
  >- (gvs[frag_observer_cut_def] >>
      drule frag_observer_lookup_cases >> strip_tac >>
      gvs[venomInstTheory.mk_inst_def,
          venomExecSemanticsTheory.phi_prefix_length_def]) >>
  `get_instruction bb 0 = SOME inst` by simp[venomInstTheory.get_instruction_def] >>
  `(lbl,0) IN frag_observer_region sa sb` by
    (drule frag_observer_lookup_cases >> strip_tac >>
     simp[frag_observer_region_def, MEM_MAP] >> metis_tac[]) >>
  drule_all frag_observer_off_cut_opcodes >> strip_tac >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def]
QED

Theorem gas_path_stop_view_agreement:
  gas_path ctx fn s n (OK t) /\ gas_path ctx fn s m (OK u) /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst id STOP [] []) /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME ub /\
  get_instruction ub u.vs_inst_idx = SOME (mk_inst uid STOP [] []) ==>
  stop_view t = stop_view u
Proof
  strip_tac >>
  `run_from 0 ctx fn t = Halt (stop_view t)` by
    (irule run_from_stop_view >> metis_tac[]) >>
  `run_from 0 ctx fn u = Halt (stop_view u)` by
    (irule run_from_stop_view >> metis_tac[]) >>
  `?a. run_from a ctx fn s = Halt (stop_view t)` by
    (qpat_assum `gas_path _ _ _ _ (OK t)` (mp_tac o MATCH_MP gas_path_normal) >>
     disch_then (mp_tac o CONJUNCT2) >>
     disch_then (qspecl_then [`0`, `Halt (stop_view t)`] mp_tac) >> simp[]) >>
  `?b. run_from b ctx fn s = Halt (stop_view u)` by
    (qpat_assum `gas_path _ _ _ _ (OK u)` (mp_tac o MATCH_MP gas_path_normal) >>
     disch_then (mp_tac o CONJUNCT2) >>
     disch_then (qspecl_then [`0`, `Halt (stop_view u)`] mp_tac) >> simp[]) >>
  `run_from (a+b) ctx fn s = Halt (stop_view t)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `a` >> simp[]) >>
  `run_from (a+b) ctx fn s = Halt (stop_view u)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `b` >> simp[]) >>
  gvs[]
QED
