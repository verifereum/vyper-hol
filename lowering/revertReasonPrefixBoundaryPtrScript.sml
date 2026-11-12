(* Retain the checker certificate: all prefix observations and the path
   refer to these same ghost endpoints. *)
Theory revertReasonPrefixBoundaryPtr
Ancestors
  revertReasonPrefixPtr revertReasonPrefixFramePtr fragGasSeqPtr
  revertReasonLayout fragExec venomInst arithmetic exprLoweringProps

Theorem revert_reason_prefix_checked_path:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts func) /\
  64+ms < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (revert_reason_prefix id v ms)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx func PG G tn
      (revert_reason_prefix id v ms) s Gf tnf /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx + 4))
Proof
  strip_tac >>
  `?s1. step_inst_base (mk_inst id ALLOCA [Lit (n2w (64+ms))]
     [STRING #"%" (toString v)]) s = OK s1` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[revert_reason_prefix_def, Once run_inst_seq_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `?Gf tnf. inst_seq_ptr D 0 ctx func PG G tn
      (revert_reason_prefix id v ms) s Gf tnf` by
    (simp[revert_reason_prefix_def] >>
     irule alloca_store_offset_alloca_checks >>
     gvs[ADD_COMM] >> metis_tac[]) >>
  qexistsl [`Gf`, `tnf`] >> conj_tac >- simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (revert_reason_prefix id v ms)` by
    simp[revert_reason_prefix_def, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[revert_reason_prefix_def, mk_inst_def]
QED
