(* Exceptional-consumer audit.  The source restriction is global for MCOPY
   destinations, unlike its suffix-only exclusion for other writes.  This
   does not exclude a second copy into the forwarded DESTINATION. *)
Theory readonlyInvokeCopyFwdHistoryExceptions
Ancestors
  readonlyInvokeCopyFwdHistorySource readonlyInvokeCopyFwdHistoryUses
  readonlyInvokeCopyFwdProtectionSelected
  readonlyInvokeCopyFwdCopySteps readonlyInvokeCopyFwdStepsAborts
  o1LowerDloadAvailableSuffix o1LowerDloadForwardInversion
  invokeCopyFwdCommonDefs memLocDefs venomExecSemantics list

Theorem ricf_source_copy_not_mcopy_destination:
  ricf_src_alloca fn /\ MEM bb fn.fn_blocks /\
  k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = MCOPY /\
  (EL k bb.bb_instructions).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MCOPY /\ mem_write_ops inst = SOME ops ==>
  ops.iao_ofst <> Var sv
Proof
  strip_tac >>
  `!ii. MEM ii (fn_insts fn) /\ MEM (Var sv) ii.inst_operands /\
    ii.inst_opcode = MCOPY ==> EL 0 ii.inst_operands <> Var sv` by
    (fs[ricf_src_alloca_def] >> metis_tac[]) >>
  gvs[mem_write_ops_def, AllCaseEqs()] >> metis_tac[MEM, HD]
QED

Theorem ricf_source_occurrence_not_mcopy_destination:
  ricf_src_alloca fn /\ MEM bb fn.fn_blocks /\
  k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = MCOPY /\
  (EL k bb.bb_instructions).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di /\ occurrence_syntax_origin fn a H /\
  fn_inst_ids_distinct fn /\ MEM ai (fn_insts fn) /\
  ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sv] /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = MCOPY /\
  mem_write_ops inst = SOME ops ==>
  op_prov H ops.iao_ofst <> SOME (a,ai.inst_id)
Proof
  strip_tac >> strip_tac >>
  `!ii. MEM ii (fn_insts fn) /\ MEM (Var sv) ii.inst_operands ==>
    ~is_pointer_preserving_op ii.inst_opcode` by
    (metis_tac[ricf_source_copy_isolated]) >>
  `ops.iao_ofst = Var sv` by
    (irule ricf_isolated_occurrence_operand >> metis_tac[]) >>
  drule_all ricf_source_copy_not_mcopy_destination >> simp[]
QED

(* Availability, not equality of relocated offsets, suffices at REVERT.
   ASSIGN-prefix availability is already handled by AvailableSuffix. *)
Theorem ricf_revert_abort_available:
  inst.inst_opcode = REVERT /\ inst.inst_operands = [off;sz] /\
  IS_SOME (eval_operand off t) /\ IS_SOME (eval_operand sz t) /\
  step_inst_base inst s = Abort reason u ==>
  ?v. step_inst_base inst t = Abort reason v
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand off t` >> Cases_on `eval_operand sz t` >> gvs[]
QED

(* Checked obstruction to using CopySteps while retaining a positive
   certificate for the very destination being overwritten.  No claim is
   made that arbitrary certificate states are reachable. *)
Theorem ricf_forwarded_copy_guard_fresh_destination:
  (db,sb,len) IN cur /\ 0 < len ==>
  ~(!b c z k. (b,c,z) IN cur /\ k < z ==>
      ~(db <= b+k /\ b+k < db+len) /\
      ~(db <= c+k /\ c+k < db+len))
Proof
  strip_tac >> disch_then (qspecl_then [`db`,`sb`,`len`,`0`] mp_tac) >>
  simp[]
QED
