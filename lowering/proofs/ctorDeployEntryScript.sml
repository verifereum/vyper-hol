(* The creation frame's entry Venom state: with the root frame's outputTo
 * shadowed as Memory, it satisfies codegen_correct's initial_ctx_rel, and it
 * is an O1 run state (as entry_venom_state_initial_ctx_rel and
 * generated_entry_code_layout_shape for calls).
 * TOP-LEVEL: deploy_entry_state_ok (a piece of e2e_deploy_correctness).
 *)
Theory ctorDeployEntry
Ancestors
  ctorDeployDefs deployFrameReplay codegenCorrectness o1PassContract
  e2eEntry immutableCodeLayout codegenEncodingWf contextPlanLayoutProps
  e2eDefs e2eDeployDefs compileEnv loweringStateRelDefs vyperArith unitShapeDefs callTrace
  contextCodegenRel lowerDloadDefs venomState unitTransformDefs
  words list rich_list

Theorem deploy_entry_state_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    unit_shape_ok dout.po_unit /\
    deploy_state_rel tops deploy_bc am tx es /\
    LENGTH (FST (HD es.contexts)).msgParams.code <= 24576
    ==>
    initial_ctx_rel cplan prog dout.po_unit.cu_context
      (deploy_entry_state prog cplan tops es) (shadow_root es) /\
    o1_run_state_ok (deploy_entry_state prog cplan tops es)
Proof
  rpt gen_tac >> strip_tac >>
  `codegen_assembly rpolicy dout.po_unit = SOME prog /\
   deploy_bc = assemble prog /\
   ?prefix. prog = prefix ++ [AsmDataHeader "code_end"]` by
    (fs[deploy_phases_def] >> metis_tac[APPEND_ASSOC]) >>
  qpat_x_assum `deploy_phases _ _ _ _` kall_tac >>
  qpat_x_assum `deploy_state_rel _ _ _ _ _` mp_tac >>
  simp[deploy_state_rel_def] >> strip_tac >> gvs[] >>
  `asm_encoding_wf (prefix ++ [AsmDataHeader "code_end"])` by
    (irule codegen_assembly_asm_encoding_wf >> fs[] >>
     goal_assum (drule_at Any) >> fs[]) >>
  drule_at Any immutable_code_end_length >> simp[] >> strip_tac >>
  qabbrev_tac `prog = prefix ++ [AsmDataHeader "code_end"]` >>
  `es.txParams.blockNumber < dimword (:256)` by
    (fs[tx_block_fields_rel_def, tx_env_ok_def] >>
     irule lt_dimword_256 >> qexists_tac `255` >> simp[]) >>
  `call_trace (shadow_root es) = call_trace es /\
   gas_readings (shadow_root es) = gas_readings es` by
    simp[call_trace_def, gas_readings_def, shadow_root_frame_obs] >>
  `wf_state (shadow_root es)` by simp[shadow_root_wf_state] >>
  simp[deploy_entry_state_def] >>
  conj_tac
  >- (simp[initial_ctx_rel_def] >>
      gvs[unit_shape_ok_def, entry_fn_first_def] >>
      simp[shadow_root_def, shadow_root_contexts_def] >>
      fs[shadow_root_def] >>
      simp[initial_state_rel_def, stack_params_rel_def,
           initial_codegen_state_rel_def, entry_venom_state_fresh, entry_venom_state_frame_fields,
           asm_pc_to_offset_zero, context_memory_rel_def] >>
      simp[entry_venom_state_def, msg_ctx_rel_def, tx_ctx_rel_def,
           block_ctx_rel_def, blockhash_rel_def, w2n_n2w, DROP_APPEND,
           init_venom_state_def]) >>
  simp[o1_run_state_ok_def, o1_initial_state_ok_def,
       entry_venom_state_fresh] >>
  conj_tac >- simp[entry_venom_state_def] >>
  simp[code_layout_valid_def, entry_venom_state_frame_fields, DROP_APPEND] >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  simp[entry_venom_state_def]
QED
