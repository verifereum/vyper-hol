Theory o1CodeEndFmpTransport
Ancestors
  o1ContractFmpLowering ctxSealAgree codegenSymRel o1PassContract
  o1ScheduleDecomp list

(* Sealing changes signatures only: the active instruction and its state
   are literally unchanged, including the evaluated code_end offset. *)
Theorem code_end_offset_ok_seal_eq:
  ctx_seal_eq C C' ==>
  (code_end_offset_ok (raw_reachable s) C <=>
   code_end_offset_ok (raw_reachable s) C')
Proof
  strip_tac >> rw[code_end_offset_ok_def] >>
  metis_tac[raw_reachable_seal_eq, ctx_seal_eq_sym]
QED

Theorem fmp_lowering_stage_code_end_offset_ok:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_ctx_shape C /\
  EVERY (\fn. fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn)
    C.ctx_functions /\
  callee_first names C.ctx_functions /\
  code_end_offset_ok (raw_reachable s) C ==>
  code_end_offset_ok (raw_reachable s) C'
Proof
  strip_tac >> drule_all fmp_lowering_stage_sealed >> strip_tac >>
  `ctx_seal_eq C C'`
    by (fs[ctx_seal_eq_def, ctx_pass_stage_def] >>
        irule LIST_REL_mono >> first_x_assum (irule_at Any) >>
        simp[fn_seal_eq_def]) >>
  metis_tac[code_end_offset_ok_seal_eq]
QED

Theorem fmp_lowering_code_end_run_contract:
  o1_stage_contract rpolicy D (EL 3 o1_fn_passes)
    (o1_walk_view rpolicy 3) (o1_pre 3)
    (\C s. o1_inv D 3 C s /\ code_end_offset_ok (raw_reachable s) C)
    (\C s. o1_inv D 4 C s /\ code_end_offset_ok (raw_reachable s) C)
Proof
  mp_tac fmp_lowering_run_contract >>
  simp[o1_run_contract_def, o1_stage_contract_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `ctx_sim D C C' s s /\ o1_inv D 4 C' s`
    by (first_x_assum irule >> simp[]) >>
  simp[] >>
  `EL 3 o1_fn_passes = CFP_Simple VP_FmpLowering` by EVAL_TAC >>
  fs[o1_inv_def, o1_static_inv_def, fmp_free_ctx_def] >>
  metis_tac[fmp_lowering_stage_code_end_offset_ok]
QED
