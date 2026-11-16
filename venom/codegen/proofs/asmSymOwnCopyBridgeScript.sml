(* TOP-LEVEL: own-code copying simulated using the exported concrete-op bridge. *)
Theory asmSymOwnCopyBridge
Ancestors
  asmSymBridge asmSymOwnCode asmSymSem asmSem asmWf symbolResolve
  vfmTypes list finite_map

Theorem sym_codecopy_own_value_sim:
  asm_sym_rel p env cs ss /\ own = cs.as_code /\
  ss.sym_stack = Val dst :: Val src :: Val sz :: stk ==>
  asm_sym_step_rel p env (sym_codecopy_own p env own ss)
    (asm_step_op (build_offset_to_pc p) "CODECOPY" cs)
Proof
  strip_tac >>
  qabbrev_tac `ct = cs with as_call_ctx :=
    cs.as_call_ctx with cc_calldata := own` >>
  qabbrev_tac `st = ss with sym_base := ss.sym_base with as_call_ctx :=
    ss.sym_base.as_call_ctx with cc_calldata := own` >>
  `asm_sym_rel p env ct st` by
    (gvs[asm_sym_rel_def, Abbr `ct`, Abbr `st`] >>
     conj_tac >- (qexists_tac `m` >> simp[]) >> metis_tac[]) >>
  mp_tac (Q.INST [`cs` |-> `ct`, `ss` |-> `st`,
    `name` |-> `"CALLDATACOPY"`] sym_step_concrete_sim) >>
  simp[dup_table_def, swap_table_def] >>
  simp[Abbr `ct`, Abbr `st`, sym_step_concrete_def,
    asm_op_arity_def, asm_op_arity_table_def, sval_val_def,
    asm_op_mem_reads_def, asm_op_mem_writes_def, mem_labels_hit_def,
    sym_codecopy_own_def, asm_step_op_def, asm_step_arith_def,
    asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
    asm_step_control_def, asm_step_extcall_def, asm_step_copy_def] >>
  simp[log_table_def] >>
  `?tail. cs.as_stack = dst :: src :: sz :: tail` by
    (gvs[asm_sym_rel_def, sval_conc_def] >> metis_tac[]) >>
  simp[asm_copy_to_mem_def, sym_lift_def, asm_sym_step_rel_def,
    asm_next_def] >>
  strip_tac >>
  gvs[asm_sym_rel_def] >>
  gvs[asm_state_component_equality] >> metis_tac[]
QED

Theorem sym_codecopy_own_sim:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\ own = cs.as_code ==>
  asm_sym_step_rel p env (sym_codecopy_own p env own ss)
    (asm_step_op (build_offset_to_pc p) "CODECOPY" cs)
Proof
  strip_tac >>
  Cases_on `?dst src sz stk. ss.sym_stack = Val dst :: Val src :: Val sz :: stk`
  >- metis_tac[sym_codecopy_own_value_sim] >>
  `sym_codecopy_own p env own ss = sym_codecopy p env ss` by
    (namedCases_on `ss.sym_stack` ["", "a rest"]
     >- simp[sym_codecopy_own_def, sym_codecopy_def] >>
     namedCases_on `rest` ["", "b tail"]
     >- (Cases_on `a` >> simp[sym_codecopy_own_def, sym_codecopy_def]) >>
     namedCases_on `tail` ["", "c stk"]
     >- (Cases_on `a` >> Cases_on `b` >>
         simp[sym_codecopy_own_def, sym_codecopy_def]) >>
     Cases_on `a` >> Cases_on `b` >> Cases_on `c` >>
     gvs[sym_codecopy_own_def, sym_codecopy_def]) >>
  simp[] >> irule sym_codecopy_sim >> simp[]
QED
