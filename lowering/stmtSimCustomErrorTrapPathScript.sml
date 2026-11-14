Theory stmtSimCustomErrorTrapPath
Ancestors
  stmtSimCustomErrorTrap fragExec fragGasPathMem gasCount venomExecSemantics
  venomInst venomState list

Theorem ce_trap_eval_phis:
  !is s. eval_phis s (MAP ce_trap_inst is) = eval_phis s is
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[ce_trap_inst_fields, eval_phis_def] >>
  `ce_trap_inst h = h` by simp[ce_trap_inst_def] >> simp[]
QED

Theorem ce_trap_edge_reflect:
  gas_path_mem_edge (ce_trap_ctx ctx) (ce_trap_fn fn) s n r /\
  (!e. r <> Error e) ==>
  n = 0 /\ gas_path_mem_edge ctx fn s 0 r
Proof
  simp[gas_path_mem_edge_def, ce_trap_fn_def, ce_trap_lookup_block] >>
  strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  gvs[ce_trap_get_instruction] >>
  Cases_on `get_instruction x s.vs_inst_idx` >> gvs[] >>
  `x'.inst_opcode <> GAS /\ x'.inst_opcode <> INVOKE` by
    (Cases_on `x'.inst_opcode = GAS` >>
     Cases_on `x'.inst_opcode = INVOKE` >>
     gvs[ce_trap_error, exit_result_def]) >>
  gvs[ce_trap_inst_def, ce_trap_step_context, ce_trap_mem_safe_context,
      ce_trap_revert_forward_at, gas_count_step_def] >>
  qexists_tac `fuel` >>
  gvs[ce_trap_block_def, ce_trap_eval_phis, ce_trap_phi_prefix_length] >>
  metis_tac[]
QED

Theorem ce_trap_path_reflect_ind[local]:
  !c f s n r. gas_path_mem c f s n r ==>
    !ctx fn. c = ce_trap_ctx ctx /\ f = ce_trap_fn fn /\
      (!e. r <> Error e) ==>
      n = 0 /\ gas_path_mem ctx fn s 0 r
Proof
  ho_match_mp_tac gas_path_mem_ind >> rpt conj_tac >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- metis_tac[gas_path_mem_rules]
  >- (rename1 `gas_path_mem_edge _ _ s n (OK t)` >>
       `n = 0 /\ gas_path_mem_edge ctx fn s 0 (OK t)` by
         (irule ce_trap_edge_reflect >> simp[]) >>
       first_x_assum (qspecl_then [`ctx`, `fn`] mp_tac) >>
       simp[] >> strip_tac >>
       gvs[] >> metis_tac[gas_path_mem_rules, arithmeticTheory.ADD_0])
  >> metis_tac[ce_trap_edge_reflect, gas_path_mem_rules]
QED

Theorem custom_error_trap_path_reflect:
  gas_path_mem (ce_trap_ctx ctx) (ce_trap_fn fn) s n r /\
  (!e. r <> Error e) ==>
  n = 0 /\ gas_path_mem ctx fn s 0 r
Proof
  metis_tac[ce_trap_path_reflect_ind]
QED
