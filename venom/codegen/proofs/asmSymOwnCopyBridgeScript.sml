(* TOP-LEVEL: own-code copying simulated using the exported concrete-op bridge. *)
Theory asmSymOwnCopyBridge
Ancestors
  asmSymOwnStep asmSymBridge asmSymOwnCode asmSymSem asmSem asmWf symbolResolve
  vfmTypes list finite_map

Theorem sym_codecopy_own_value_sim:
  asm_sym_rel p env cs ss /\ own = cs.as_code /\
  ss.sym_stack = Val dst :: Val src :: Val sz :: stk ==>
  asm_sym_step_rel p env (sym_codecopy_own p env own ss)
    (asm_step_op (build_offset_to_pc p) "CODECOPY" cs)
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`SND (compute_label_offsets p)`, `asm_data_env_ok p env`,
    `own`, `cs`, `ss`, `dst`, `src`, `sz`, `stk`, `build_offset_to_pc p`]
    sym_codecopy_own_value_sim_core) >>
  simp[asm_sym_rel_core_canonical, asm_sym_step_rel_core_canonical]
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
