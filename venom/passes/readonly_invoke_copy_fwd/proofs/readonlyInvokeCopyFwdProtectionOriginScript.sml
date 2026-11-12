(* Backward SSA availability for the static roots of forwarding events. *)
Theory readonlyInvokeCopyFwdProtectionOrigin
Ancestors
  ssaAvailablePred internalReturnCopyFwdPlan list venomInst

Theorem ircf_alias_boundary_available_root:
  !fn root v. ircf_alias fn root v ==>
  !bb n. wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    n <= LENGTH bb.bb_instructions /\
    (!P. boundary_pred fn bb n P ==> P v) ==>
    (!P. boundary_pred fn bb n P ==> P root)
Proof
  ho_match_mp_tac ircf_alias_ind >> conj_tac
  >- simp[] >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `!P. boundary_pred fn bb n P ==> P v` by
    (`inst.inst_opcode <> PHI /\ MEM v' inst.inst_outputs` by
       (qpat_assum `inst.inst_opcode = _` (fn th => rewrite_tac[th]) >>
        qpat_assum `inst.inst_outputs = _` (fn th => rewrite_tac[th]) >>
        simp[NoAsms]) >>
     metis_tac[boundary_pred_definition_input_available]) >>
  metis_tac[]
QED
