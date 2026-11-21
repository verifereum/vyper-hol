Theory deployBodyReachability
Ancestors
  fragGasPath contextRawReachable contextCodegenRel fragExec
  venomExecSemantics venomExecProofs venomInst venomInstProofs venomState list
  cfgNormSim[qualified]

Theorem raw_reachable_gas_edge[local]:
  gas_path_edge ctx fn s n (OK t) /\
  (!bb lbl. lookup_block lbl fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  (!i. active_inst fn i s ==> raw_reachable entry ctx fn i s) /\
  active_inst fn next t ==>
  raw_reachable entry ctx fn next t
Proof
  rw[gas_path_edge_def] >> gvs[] >>
  TRY (qpat_assum `exit_result _` mp_tac >>
       qpat_assum `OK _ = step_inst _ _ _ _` (SUBST1_TAC o GSYM) >>
       simp[exit_result_def] >> NO_TAC) >>
  `active_inst fn inst s` by metis_tac[contextCodegenRelPropsTheory.lookup_instruction_active] >>
  `raw_reachable entry ctx fn inst s` by metis_tac[]
  >- metis_tac[raw_reachable_next]
  >- (`enters_block fn t' (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
        (simp[enters_block_def] >> metis_tac[]) >>
      metis_tac[raw_reachable_block]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  `?target. lookup_block lbl fn.fn_blocks = SOME target` by
    (Cases_on `lookup_block lbl fn.fn_blocks` >> simp[] >>
     qpat_assum `active_inst _ _ (jump_to _ _)` mp_tac >>
     fs[active_inst_def, jump_to_def, cfgNormSimTheory.lookup_block_NONE,
        MEM_MAP] >> metis_tac[]) >>
  `enters_block fn (jump_to lbl s) (jump_to lbl s)` by
    (`phi_prefix_length target.bb_instructions = 0` by metis_tac[] >>
     simp[enters_block_def] >> qexistsl [`target`, `jump_to lbl s`] >>
     simp[jump_to_def, eval_phis_no_phi, venom_state_fupdfupds]) >>
  metis_tac[raw_reachable_block]
QED

Theorem raw_reachable_gas_path:
  gas_path ctx fn s n (OK t) /\
  (!bb lbl. lookup_block lbl fn.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
  (!i. active_inst fn i s ==> raw_reachable entry ctx fn i s) /\
  active_inst fn next t ==>
  raw_reachable entry ctx fn next t
Proof
  `!ctx fn s n out. gas_path ctx fn s n out ==>
    !entry next t. out = OK t /\
      (!bb lbl. lookup_block lbl fn.fn_blocks = SOME bb ==>
         phi_prefix_length bb.bb_instructions = 0) /\
      (!i. active_inst fn i s ==> raw_reachable entry ctx fn i s) /\
      active_inst fn next t ==>
      raw_reachable entry ctx fn next t` suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- simp[]
  >- (rpt strip_tac >> gvs[] >> metis_tac[raw_reachable_gas_edge]) >>
  rpt strip_tac >> gvs[exit_result_def]
QED

Theorem raw_reachable_through_fragment:
  !ctx fn0 s0 fn inst s.
    frag_reachable ctx fn0 s0 fn inst s ==>
    !entry. (!i. active_inst fn0 i s0 ==> raw_reachable entry ctx fn0 i s0) ==>
      raw_reachable entry ctx fn inst s
Proof
  ho_match_mp_tac frag_reachable_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  TRY (first_assum irule >> first_assum ACCEPT_TAC >> NO_TAC)
  >- metis_tac[raw_reachable_next]
  >- metis_tac[raw_reachable_block] >>
  metis_tac[raw_reachable_callee]
QED
