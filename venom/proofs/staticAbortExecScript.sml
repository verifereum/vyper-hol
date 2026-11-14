(* A straight static-fault prefix cannot leave its block normally. *)
Theory staticAbortExec
Ancestors
  staticAbortDefs venomExecProofs venomExecSemantics venomInstProofs
  venomState venomInst opcodeClass list staticShadowForbidden staticShadowDefs
Libs
  stepInstBaseLib

Theorem static_forbidden_no_normal[local]:
  MEM inst.inst_opcode [SSTORE; TSTORE; LOG] /\ s.vs_call_ctx.cc_static ==>
  step_inst fuel ctx inst s <> OK t /\
  step_inst fuel ctx inst s <> IntRet ret t
Proof
  strip_tac >> fs[]
  >- (simp[step_inst_non_invoke] >> with_opcode_clause simp >>
      Cases_on `eval_operands inst.inst_operands s` >>
      gvs[exec_write2_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[eval_operands_def])
  >- (simp[step_inst_non_invoke] >> with_opcode_clause simp >>
      Cases_on `eval_operands inst.inst_operands s` >>
      gvs[exec_write2_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[eval_operands_def])
  >> `static_shadow_result_rel (step_inst_base inst s) (Error "probe")` by
       (irule static_shadow_forbidden >> simp[]) >>
  gvs[step_inst_non_invoke] >>
  Cases_on `step_inst_base inst s` >> gvs[static_shadow_result_rel_def]
QED

Theorem static_abort_distance_no_normal[local]:
  !n s j bb fuel ctx t ret.
    j = s.vs_inst_idx + n /\ s.vs_call_ctx.cc_static /\
    static_abort_pair bb s.vs_inst_idx j ==>
    exec_block fuel ctx bb s <> OK t /\
    exec_block fuel ctx bb s <> IntRet ret t
Proof
  Induct_on `n`
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      qpat_x_assum `static_abort_pair _ _ _` mp_tac >>
      pure_rewrite_tac[static_abort_pair_def] >> strip_tac >>
      `get_instruction bb s.vs_inst_idx =
       SOME (EL s.vs_inst_idx bb.bb_instructions)` by
        simp[get_instruction_def] >>
      drule_all static_forbidden_no_normal >> strip_tac >>
      once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >> simp[] >>
      Cases_on `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
      gvs[])
  >> rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < j` by simp[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    gvs[static_abort_pair_def] >>
  `get_instruction bb s.vs_inst_idx =
   SOME (EL s.vs_inst_idx bb.bb_instructions)` by simp[get_instruction_def] >>
  `~is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode /\
   (EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE` by
    (qpat_x_assum `static_abort_pair _ _ _` mp_tac >>
     pure_rewrite_tac[static_abort_pair_def] >> strip_tac >>
     first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s`
  >- (gvs[] >> first_x_assum irule >>
      drule step_inst_ok_preserves_call_ctx >> strip_tac >> simp[] >>
      qpat_x_assum `static_abort_pair _ _ _` mp_tac >>
      simp[static_abort_pair_def, arithmeticTheory.ADD_CLAUSES] >>
      strip_tac >> simp[] >>
      rpt strip_tac >>
      qpat_x_assum `!k inst. _` (qspec_then `k` mp_tac) >> simp[])
  >> gvs[] >>
  gvs[step_inst_non_invoke] >>
  metis_tac[step_inst_base_no_intret]
QED

(* Successful intermediate steps preserve the static flag. The pending
   storage/log write either faults statically or has invalid operands. *)
Theorem static_abort_at_no_normal:
  s.vs_call_ctx.cc_static /\ static_abort_at bb s.vs_inst_idx ==>
  exec_block fuel ctx bb s <> OK t /\
  exec_block fuel ctx bb s <> IntRet ret t
Proof
  strip_tac >> gvs[static_abort_at_def] >>
  irule static_abort_distance_no_normal >> simp[] >>
  qexists_tac `j - s.vs_inst_idx` >>
  gvs[static_abort_pair_def] >> gvs[]
QED
