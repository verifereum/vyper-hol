Theory concretizePtrOperationalBytes
Ancestors
  concretizePtrByteHistory concretizePtrChronologicalHistory concretizePtrLifetime
  stepWriteFootprintBase calleeTransport contextCodegenRel codegenRel
  ptrDiscipline venomExecSemantics venomInst list pred_set

Theorem ptr_chrono_step_byte_frame:
  !ctx a b. ptr_chrono_step ctx a b ==>
  !x. x NOTIN range_bytes (source_memory_write_ranges a.po_inst a.po_state) ==>
  read_byte x b.po_state.vs_memory = read_byte x a.po_state.vs_memory
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> rpt conj_tac >>
  simp[ptr_observe_def, range_bytes_def] >> rpt strip_tac
  >- (gvs[step_inst_non_invoke] >>
      irule step_inst_base_OK_byte_frame >> metis_tac[arithmeticTheory.ADD_COMM])
  >- (`inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      gvs[step_inst_non_invoke] >>
      drule enters_block_memory >> strip_tac >> asm_rewrite_tac[] >>
      irule step_inst_base_OK_byte_frame >> metis_tac[arithmeticTheory.ADD_COMM])
  >- (drule setup_callee_shared_fields >> strip_tac >>
      drule enters_block_memory >> simp[]) >>
  `rinst.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[step_inst_def, AllCaseEqs()]) >>
  gvs[step_inst_non_invoke] >>
  drule bind_outputs_shared_fields >> simp[] >> strip_tac >>
  irule step_inst_base_IntRet_byte_frame >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ptr_chrono_history_byte_frame:
  ptr_chrono_history vs0 ctx h a /\ SUC k < LENGTH h /\
  x NOTIN range_bytes (source_memory_write_ranges (EL k h).po_inst (EL k h).po_state) ==>
  read_byte x (EL (SUC k) h).po_state.vs_memory =
    read_byte x (EL k h).po_state.vs_memory
Proof
  metis_tac[ptr_chrono_history_adjacent, ptr_chrono_step_byte_frame]
QED

Theorem ptr_chrono_last_writer_agreement:
  ptr_chrono_history vs0 ctx h a /\ ptr_chrono_history vst ctxt ht at /\
  n < LENGTH h /\ n < LENGTH ht /\
  (!x. x IN live ==> ?w. w < n /\
    read_byte x (EL (SUC w) h).po_state.vs_memory =
      read_byte (reloc x) (EL (SUC w) ht).po_state.vs_memory /\
    (!k. w < k /\ k < n ==>
      x NOTIN range_bytes
        (source_memory_write_ranges (EL k h).po_inst (EL k h).po_state) /\
      reloc x NOTIN range_bytes
        (source_memory_write_ranges (EL k ht).po_inst (EL k ht).po_state))) ==>
  ptr_bytes_agree live reloc (EL n h).po_state.vs_memory (EL n ht).po_state.vs_memory
Proof
  strip_tac >>
  irule (BETA_RULE (Q.INST [
    `M` |-> `\k. (EL k h).po_state.vs_memory`,
    `target` |-> `\k. (EL k ht).po_state.vs_memory`]
    (SPEC_ALL ptr_bytes_agree_last_writer_footprints))) >>
  qexistsl_tac [
    `\k. range_bytes (source_memory_write_ranges (EL k h).po_inst (EL k h).po_state)`,
    `\k. range_bytes (source_memory_write_ranges (EL k ht).po_inst (EL k ht).po_state)`] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> irule ptr_chrono_history_byte_frame >>
      simp[] >> metis_tac[])
  >- (rpt strip_tac >> irule ptr_chrono_history_byte_frame >>
      simp[] >> metis_tac[]) >>
  metis_tac[]
QED

(* Sampling a source history at retained boundaries does not require source
   and target event numbers to coincide. This is the source-only frame probe;
   it deliberately makes no assertion about target write exclusion. *)
Theorem ptr_chrono_history_interval_byte_frame:
  !hi lo. ptr_chrono_history vs0 ctx h a /\
    lo <= hi /\ hi < LENGTH h /\
    (!k. lo <= k /\ k < hi ==>
      x NOTIN range_bytes
        (source_memory_write_ranges (EL k h).po_inst (EL k h).po_state)) ==>
    read_byte x (EL hi h).po_state.vs_memory =
      read_byte x (EL lo h).po_state.vs_memory
Proof
  Induct >> rpt strip_tac
  >- (`lo = 0` by decide_tac >> simp[]) >>
  Cases_on `lo = SUC hi` >- simp[] >>
  `lo <= hi` by decide_tac >>
  `read_byte x (EL (SUC hi) h).po_state.vs_memory =
   read_byte x (EL hi h).po_state.vs_memory` by
    (irule ptr_chrono_history_byte_frame >> simp[] >> metis_tac[]) >>
  `read_byte x (EL hi h).po_state.vs_memory =
   read_byte x (EL lo h).po_state.vs_memory` by
    (first_x_assum irule >> simp[] >> metis_tac[arithmeticTheory.LESS_TRANS]) >>
  metis_tac[]
QED
