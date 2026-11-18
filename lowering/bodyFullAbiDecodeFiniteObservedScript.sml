Theory bodyFullAbiDecodeFiniteObserved
Ancestors
  bodyFullAbiDecodeFiniteGuard fragGasSeqAbort fragGasSeq fragGasPath
  fragExec exprLoweringProps instIdxIndep venomExecSemantics venomInstProofs
  venomInst venomState list rich_list

(* The raw certificate fixes the physical successor before any observer is
   selected. No pointer or allocation property of that observer is used. *)
Theorem abi_decode_finite_success_observed:
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  LENGTH (FILTER (\i. i.inst_opcode = GAS) code) = 0 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq code s = OK t ==>
  !obs. fn_has_code sa sb obs ==>
    gas_path ctx obs s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rpt strip_tac >>
  `?bb. lookup_block s.vs_current_bb obs.fn_blocks = SOME bb /\
        isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1, DROP_LENGTH_NIL]) >>
  drule_all tuple_run_inst_seq_gas_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

(* The successful prefix and failing ASSERT certificate determine one fixed
   rejecting cursor, even if the rest of the fragment is never executed. *)
Theorem abi_decode_finite_revert_observed:
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    (prefix ++ mk_inst id ASSERT [cond] [] :: suffix) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix /\
  LENGTH (FILTER (\i. i.inst_opcode = GAS) prefix) = 0 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq prefix s = OK u /\
  step_inst_base (mk_inst id ASSERT [cond] []) u = Abort Revert_abort t ==>
  !obs. fn_has_code sa sb obs ==>
    gas_path ctx obs s 0
      (Abort Revert_abort
        (t with vs_inst_idx := LENGTH sa.cs_current_insts + LENGTH prefix))
Proof
  rpt strip_tac >>
  `?bb. lookup_block s.vs_current_bb obs.fn_blocks = SOME bb /\
    isPREFIX (prefix ++ mk_inst id ASSERT [cond] [] :: suffix)
      (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1, DROP_LENGTH_NIL]) >>
  `isPREFIX prefix (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `gas_path ctx obs s 0
      (OK (u with vs_inst_idx := LENGTH sa.cs_current_insts + LENGTH prefix))` by
    (drule_all tuple_run_inst_seq_gas_path >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (conj_tac >- metis_tac[run_inst_seq_preserves_halted] >>
     metis_tac[exec_block_run_inst_seq]) >>
  `get_instruction bb (LENGTH sa.cs_current_insts + LENGTH prefix) =
    SOME (mk_inst id ASSERT [cond] [])` by
    (drule_all fn_has_code_same_block >> strip_tac >> gvs[] >>
     first_x_assum (qspec_then `LENGTH prefix` mp_tac) >>
     simp[EL_APPEND2]) >>
  `step_inst_base (mk_inst id ASSERT [cond] [])
      (u with vs_inst_idx := LENGTH sa.cs_current_insts + LENGTH prefix) =
    Abort Revert_abort
      (t with vs_inst_idx := LENGTH sa.cs_current_insts + LENGTH prefix)` by
    simp[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def,
         exec_result_map_def] >>
  `gas_path ctx obs
      (u with vs_inst_idx := LENGTH sa.cs_current_insts + LENGTH prefix) 0
      (Abort Revert_abort
        (t with vs_inst_idx := LENGTH sa.cs_current_insts + LENGTH prefix))` by
    (drule_at (Pat `step_inst_base _ _ = Abort _ _`)
       (Q.SPEC `F` gas_marked_path_abort) >>
     simp[fragGasModeTheory.gas_marked_path_def, mk_inst_def,
          is_terminator_def] >>
     disch_then irule >> qexists_tac `bb` >> gvs[mk_inst_def, arithmeticTheory.ADD_COMM]) >>
  drule_all gas_path_then >> simp[]
QED
