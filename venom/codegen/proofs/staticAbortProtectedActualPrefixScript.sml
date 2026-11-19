(* Actual-code concretization of a successful protected symbolic prefix. *)
Theory staticAbortProtectedActualPrefix
Ancestors
  asmDataEnv codegenSymRel asmSymSem asmSymBridge list asmSem

Theorem stopped_symbolic_prefix_actual_code:
  s.as_pc = 0 /\ asm_static_wf p /\ asm_static_wf q /\
  FILTER is_data_inst q = FILTER is_data_inst p /\
  s.as_code = assemble p ++ data /\
  sym_steps q (asm_data_env p (assemble p ++ data)) n (sym_init s) = SymOK ss
  ==> ?t.
    asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q) q n
      (s with as_code := assemble q ++ data) = AsmOK t /\
    asm_sym_rel q (asm_data_env q (assemble q ++ data)) t ss /\
    t.as_pc = ss.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH ss.sym_stack /\
    t.as_call_ctx = ss.sym_base.as_call_ctx /\
    t.as_requests = ss.sym_base.as_requests
Proof
  strip_tac >>
  `asm_data_env p (assemble p ++ data) =
   asm_data_env q (assemble q ++ data)` by
    (irule asm_data_env_agree >> simp[]) >>
  `sym_init (s with as_code := assemble q ++ data) = sym_init s` by
    simp[sym_init_def] >>
  `asm_sym_rel q (asm_data_env q (assemble q ++ data))
     (s with as_code := assemble q ++ data) (sym_init s)` by
    (pop_assum (fn th => rewrite_tac[GSYM th]) >>
     irule asm_sym_rel_init >> simp[asm_data_env_ok_asm_data_env]) >>
  gvs[] >> drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexists_tac `cs'` >> simp[] >>
  `cs'.as_pc = ss.sym_base.as_pc /\
   LENGTH cs'.as_stack = LENGTH ss.sym_stack /\
   cs'.as_call_ctx = ss.sym_base.as_call_ctx /\
   cs'.as_requests = ss.sym_base.as_requests` by
    (gvs[asm_sym_rel_def] >>
     imp_res_tac LIST_REL_LENGTH >> gvs[]) >>
  simp[]
QED
