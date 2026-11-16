(* Own-code opcode facts at arbitrary label offsets. *)
Theory asmSymOwnStep
Ancestors
  asmSymBridge asmSymOwnCode asmSymSem asmSem asmWf symbolResolve
  vfmTypes list finite_map words spillWordBounds asmToBytecodeProofs

(* Reuse the bridge's syntax for its closed-lambda relations. *)
val (core_vars, core_body) = strip_forall (concl sym_step_calldatacopy_sim_core);
val _ = Parse.temp_overload_on
  ("bridge_core", list_mk_abs (List.take (core_vars, 4), fst (dest_imp core_body)));
val result_rel = mk_var ("R", type_of ``asm_sym_rel p env``);
val result_body = subst [``asm_sym_rel p env`` |-> result_rel]
  (lhs (concl asm_sym_step_rel_core_canonical));
val result_vars = result_rel :: List.map (fn name =>
  List.find (fn v => fst (dest_var v) = name) (free_vars result_body)
  |> valOf) ["sr", "cr"];
val _ = Parse.temp_overload_on
  ("bridge_result", list_mk_abs (result_vars, result_body));

Theorem sym_codecopy_own_value_sim_core:
  ∀lo code_ok own cs ss dst src sz stk otp.
    bridge_core lo code_ok cs ss ∧ own = cs.as_code ∧
    ss.sym_stack = Val dst :: Val src :: Val sz :: stk ⇒
    bridge_result (bridge_core lo code_ok)
      (sym_codecopy_own p env own ss) (asm_step_op otp "CODECOPY" cs)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `ct = cs with as_call_ctx :=
    cs.as_call_ctx with cc_calldata := own` >>
  qabbrev_tac `st = ss with sym_base := ss.sym_base with as_call_ctx :=
    ss.sym_base.as_call_ctx with cc_calldata := own` >>
  `bridge_core lo code_ok ct st` by
    (gvs[Abbr `ct`, Abbr `st`] >>
     conj_tac
     >- (rename1 `LENGTH memory = LENGTH cs.as_memory` >>
         qexists_tac `memory` >> simp[]) >> metis_tac[]) >>
  mp_tac (Q.SPECL [`lo`, `code_ok`, `ct`, `st`, `otp`]
    sym_step_calldatacopy_sim_core) >>
  simp[Abbr `ct`, Abbr `st`, sym_step_concrete_def,
    asm_op_arity_def, asm_op_arity_table_def, sval_val_def,
    asm_op_mem_reads_def, asm_op_mem_writes_def, mem_labels_hit_def,
    sym_codecopy_own_def, asm_step_op_def, asm_step_arith_def,
    asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
    asm_step_control_def, asm_step_extcall_def, asm_step_copy_def] >>
  simp[log_table_def] >>
  `∃tail. cs.as_stack = dst :: src :: sz :: tail` by
    (gvs[sval_conc_def] >> metis_tac[]) >>
  simp[asm_copy_to_mem_def, sym_lift_def, asm_next_def] >>
  strip_tac >> gvs[] >>
  gvs[asm_state_component_equality] >> metis_tac[]
QED

Theorem sym_codesize_own_sim:
  asm_sym_rel_own lo p env own cs ss ⇒
  ∃cs' ss'.
    sym_step_op_own p env own "CODESIZE" ss = SymOK ss' ∧
    asm_step_op otp "CODESIZE" cs = AsmOK cs' ∧
    asm_sym_rel_own lo p env own cs' ss'
Proof
  strip_tac >>
  simp[sym_step_op_own_def, sym_set_stack_def,
       asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def, asm_step_copy_def, asm_step_context_def,
       asm_push_val_def] >>
  gvs[asm_sym_rel_own_def, asm_next_def, sval_conc_def] >>
  conj_tac
  >- (rename1 `LENGTH memory = LENGTH cs.as_memory` >>
      qexists_tac `memory` >> simp[]) >> metis_tac[]
QED

Theorem asm_data_env_lo_ok_canonical:
  asm_static_wf p ⇒
  (asm_data_env_lo_ok (SND (compute_label_offsets p)) p env code ⇔
   asm_data_env_ok p env code)
Proof
  strip_tac >>
  `∀l. MEM (AsmDataHeader l) p ⇒
       ∃off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off ∧
             off < dimword (:256) DIV 2` by
    (rpt strip_tac >>
     `l ∈ FDOM (SND (compute_label_offsets p))` by
       (simp[compute_label_offsets_def, clo_step_eq] >>
        irule clo_FDOM >> simp[]) >>
     `∃off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off` by
       gvs[FLOOKUP_DEF] >>
     qexists_tac `off` >> simp[] >>
     `off < 65536` by
       (fs[asm_static_wf_def, asm_encoding_wf_def, pairTheory.UNCURRY] >>
        qpat_x_assum `∀lbl off. FLOOKUP _ lbl = SOME off ⇒ _` drule >>
        simp[symbol_size_def] >> strip_tac >>
        drule encode_num_bytes_length_bound >> simp[]) >>
     simp[dimword_def] >> decide_tac) >>
  simp[asm_data_env_lo_ok_def, asm_data_env_ok_def, sym_data_label_def] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem asm_sym_rel_own_canonical:
  asm_static_wf p ⇒
  (asm_sym_rel_own (SND (compute_label_offsets p)) p env own cs ss ⇔
   asm_sym_rel p env cs ss ∧ cs.as_code = own)
Proof
  strip_tac >> Cases_on `cs.as_code = own` >>
  gvs[asm_sym_rel_own_def, asm_sym_rel_def, asm_data_env_lo_ok_canonical]
QED
