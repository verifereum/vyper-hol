(* The caller PC after one successful marked instruction. *)
Theory createSizeEdgePC
Ancestors
  fragGasOrigin fragExec venomExecProofs venomInstProofs
  venomExecSemantics venomState

Theorem create_ok_edge_pc:
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME i /\
  gas_origin_edge F explicit ctx fn u ms (OK v) ==>
  (~is_terminator i.inst_opcode /\
   v.vs_current_bb = u.vs_current_bb /\ v.vs_inst_idx = SUC u.vs_inst_idx) \/
  (is_terminator i.inst_opcode /\
   ?t. step_inst_base i u = OK t /\ v.vs_current_bb = t.vs_current_bb /\
       (v.vs_inst_idx = 0 \/
        ?target. lookup_block v.vs_current_bb fn.fn_blocks = SOME target /\
                 v.vs_inst_idx = phi_prefix_length target.bb_instructions))
Proof
  rw[gas_origin_edge_def, exit_result_def] >> gvs[]
  >- metis_tac[step_preserves_control_flow]
  >- (drule_then assume_tac eval_phis_preserves_current_bb >>
      imp_res_tac is_terminator_not_invoke >>
      qexists_tac `t` >> fs[step_inst_non_invoke] >> metis_tac[])
  >- (qexists_tac `jump_to lbl u` >>
      qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[step_inst_non_invoke, jump_to_def]) >>
  metis_tac[exit_result_def]
QED
