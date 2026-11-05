(* Last-arrival control boundary, independent of values and allocation. *)
Theory bodyPtrBopInArrival
Ancestors fragGasPath venomInstProofs venomExecProofs venomExecSemantics
  bodyPtrBopInShapeProbe

Theorem phi_prefix_stops_before_nonphi:
  !pre inst rest. inst.inst_opcode <> PHI ==>
    phi_prefix_length (pre ++ inst::rest) <= LENGTH pre
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[phi_prefix_length_def]
QED

Theorem edge_arrival_after_phi_prefix:
  gas_path_edge ctx fn s n (OK t) /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions < t.vs_inst_idx ==>
  s.vs_current_bb = t.vs_current_bb /\
  s.vs_inst_idx = t.vs_inst_idx - 1
Proof
  strip_tac >> gvs[gas_path_edge_def, fragExecTheory.exit_result_def]
  >- (drule_all step_preserves_control_flow >> simp[])
  >- (drule venomExecProofsTheory.eval_phis_preserves_current_bb >>
      strip_tac >> gvs[])
  >> gvs[venomStateTheory.jump_to_def] >>
     qpat_x_assum `OK _ = _` (assume_tac o SYM) >>
     gvs[fragExecTheory.exit_result_def]
QED

Theorem edge_arrival_inside_nonphi_segment:
  lookup_block L fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ seg ++ post /\ seg <> [] /\
  EVERY (\i. i.inst_opcode <> PHI) seg /\
  LENGTH pre < k /\
  gas_path_edge ctx fn s n (OK t) /\
  t.vs_current_bb = L /\ t.vs_inst_idx = k ==>
  s.vs_current_bb = L /\ s.vs_inst_idx = k - 1
Proof
  strip_tac >> Cases_on `seg` >> gvs[] >>
  `phi_prefix_length bb.bb_instructions <= LENGTH pre` by
    (qspecl_then [`pre`, `h`, `t' ++ post`] mp_tac
       phi_prefix_stops_before_nonphi >>
     pure_asm_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
     simp[]) >>
  `phi_prefix_length bb.bb_instructions < t.vs_inst_idx` by decide_tac >>
  drule_all edge_arrival_after_phi_prefix >> simp[]
QED

Theorem probe_segment_has_no_phi:
  EVERY (\i. i.inst_opcode <> PHI)
    (SND (compile_expr probe_cenv (BaseT BoolT) probe_expr
      <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
         cs_current_bb := "entry"; cs_current_insts := [];
         cs_blocks := []; cs_data_sections := [] |>)).cs_current_insts
Proof
  rewrite_tac[probe_exact_instructions] >> EVAL_TAC
QED
