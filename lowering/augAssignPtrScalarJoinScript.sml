(* Operational join boundaries only.  Clean inputs and suffix preservation
   remain explicit; these lemmas do not certify arbitrary compiler regions. *)
Theory augAssignPtrScalarJoin
Ancestors
  augAssignPtrProvenancePath typedCopyArrayPtr fragGasSeqPtr fragGasPathPtr
  ptrDiscipline ptrSafeRun venomInst venomState venomExecSemantics
  venomExecProofs finite_map pred_set list codegenRel contextCodegenRel gasCount

Theorem assign_clean_provenance:
  op_prov G arg = NONE ==>
  step_prov PG G (mk_inst id ASSIGN [arg] [out]) u =
    DRESTRICT G (COMPL {out})
Proof
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       mk_inst_def]
QED

Theorem assign_clean_result:
  op_prov G arg = NONE ==>
  op_prov (step_prov PG G (mk_inst id ASSIGN [arg] [out]) u)
    (Var out) = NONE
Proof
  simp[assign_clean_provenance, op_prov_def, FLOOKUP_DRESTRICT]
QED

Theorem assign_ptr_edge:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [arg] [out]) /\
  step_inst_base (mk_inst id ASSIGN [arg] [out]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ASSIGN [arg] [out]) u)
    (step_taint (mk_inst id ASSIGN [arg] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  mp_tac (Q.INST [`lo` |-> `0`, `i` |-> `mk_inst id ASSIGN [arg] [out]`]
    straight_line_ptr_edge) >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       mk_inst_def] >>
  simp[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs] >>
  Cases_on `eval_operand arg s` >> simp[update_var_def]
QED

(* The counted relation permits stopping at the raw jump target.  If a run
   enters its phi-free block instead, entry_ghost_no_phi (reused from
   typedCopyArrayPtr) says exactly the same ghost is used. *)
Theorem jump_ptr_edge:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `ptr_safe_step D 0 0 ctx fn PG G tn
    (mk_inst id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >> qexists_tac `0:num` >>
  simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
       step_jmp_behavior, is_terminator_def] >>
  fs[mk_inst_def] >> metis_tac[]
QED

Theorem scalar_join_path:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [arg] [out]) /\
  step_inst_base (mk_inst id ASSIGN [arg] [out]) s = OK u /\
  s1 = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb1 /\
  get_instruction bb1 s1.vs_inst_idx = SOME (mk_inst jid JMP [Label lbl] []) /\
  G1 = step_prov PG G (mk_inst id ASSIGN [arg] [out]) u /\
  tn1 = step_taint (mk_inst id ASSIGN [arg] [out]) s u tn /\
  op_prov G arg = NONE ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK (jump_to lbl s1)) /\
  op_prov G1 (Var out) = NONE /\
  (!x. x <> out ==> FLOOKUP G1 x = FLOOKUP G x /\
       op_taint tn1 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` by
    (gvs[] >> irule assign_ptr_edge >> metis_tac[]) >>
  `~s1.vs_halted` by
    (qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
     simp[mk_inst_def, step_inst_base_opcode_eqs] >>
     Cases_on `eval_operand arg s` >> gvs[update_var_def] >>
     strip_tac >> gvs[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G1 tn1 s1 0 G1 tn1
     (OK (jump_to lbl s1))` by
    (irule jump_ptr_edge >> metis_tac[]) >>
  conj_tac
  >- (`gas_path_ptr D 0 ctx fn PG G1 tn1 (jump_to lbl s1) 0 G1 tn1
        (OK (jump_to lbl s1))` by
        (irule (cj 1 gas_path_ptr_rules) >> gvs[jump_to_def]) >>
      metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]) >>
  conj_tac >- metis_tac[assign_clean_result] >>
  gen_tac >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule decoderGhostFramePtrTheory.step_prov_other_output >> simp[mk_inst_def]) >>
  irule decoderGhostFramePtrTheory.step_taint_other_output >> simp[mk_inst_def]
QED

Theorem scalar_join_entry_clean:
  op_prov G arg = NONE /\ lookup_block lbl fn.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 ==>
  op_prov (entry_prov fn (jump_to lbl s)
    (step_prov PG G (mk_inst id ASSIGN [arg] [out]) u)) (Var out) = NONE
Proof
  strip_tac >>
  `entry_prov fn (jump_to lbl s)
    (step_prov PG G (mk_inst id ASSIGN [arg] [out]) u) =
    step_prov PG G (mk_inst id ASSIGN [arg] [out]) u` by
    (irule (cj 1 entry_ghost_no_phi) >> simp[jump_to_def] >> metis_tac[]) >>
  simp[assign_clean_result]
QED

(* This is a conditional continuation on the SAME ghost/path.  No region
   closure or result-preservation fact is asserted for arbitrary extensions.
   In particular a suffix that writes out or enters a PHI for out needs its
   own transfer proof and does not satisfy this frame premise automatically. *)
Theorem assign_then_preserving_path_untagged:
  op_prov G arg = NONE /\
  gas_path_ptr D lo ctx fn PG
    (step_prov PG G (mk_inst id ASSIGN [arg] [out]) u) tn s n H tm r /\
  region s /\
  (!G0 tn0 s0 k G1 tn1 r0.
     region s0 /\ gas_path_ptr_edge D lo ctx fn PG G0 tn0 s0 k G1 tn1 r0 ==>
     FLOOKUP G1 out = FLOOKUP G0 out /\ (!t. r0 = OK t ==> region t)) ==>
  op_prov H (Var out) = NONE
Proof
  strip_tac >>
  `op_prov (step_prov PG G (mk_inst id ASSIGN [arg] [out]) u)
     (Var out) = NONE` by (irule assign_clean_result >> simp[]) >>
  metis_tac[gas_path_ptr_untagged_frame]
QED
