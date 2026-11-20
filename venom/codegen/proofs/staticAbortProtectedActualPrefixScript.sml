(* Actual-code concretization of a successful protected symbolic prefix. *)
Theory staticAbortProtectedActualPrefix
Ancestors
  asmDataEnv codegenSymRel asmSymSem asmSymBridge list asmSem
  asmRelocDataEnv asmSymModeOwn fnPlanPlaceRevertPostamble asmSpliceOwn

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

(* The concrete prefix uses the current program's code labels and the
   installed program's data offsets. All own-code reads use s.as_code. *)
Theorem stopped_symbolic_prefix_installed_code:
  s.as_pc = 0 /\ asm_static_wf p /\ asm_static_wf installed /\
  FILTER is_data_inst installed = FILTER is_data_inst p /\
  sym_steps_own p (asm_data_env installed s.as_code) s.as_code n (sym_init s) =
    SymOK ss ==>
  ?t. asm_steps (lo_reloc p installed) (build_offset_to_pc p) p n s = AsmOK t /\
      asm_sym_rel_own (lo_reloc p installed) p
        (asm_data_env installed s.as_code) s.as_code t ss /\
      t.as_pc = ss.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH ss.sym_stack /\
      t.as_call_ctx = ss.sym_base.as_call_ctx /\
      t.as_requests = ss.sym_base.as_requests
Proof
  strip_tac >>
  `asm_sym_rel_own (lo_reloc p installed) p (asm_data_env installed s.as_code)
     s.as_code s (sym_init s)` by
    (irule asm_sym_rel_own_init >> simp[] >>
     drule_all lo_reloc_data_env >> simp[]) >>
  `code_labels_agree p (lo_reloc p installed)` by
    simp[lo_reloc_code_labels_agree] >>
  drule_all (Q.INST [`allow_own` |-> `T`] asm_sym_steps_mode_sim
             |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES]) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  fs[asm_sym_rel_own_def] >> imp_res_tac LIST_REL_LENGTH >> gvs[]
QED
