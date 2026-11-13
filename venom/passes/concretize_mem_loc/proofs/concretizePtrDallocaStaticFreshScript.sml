Theory concretizePtrDallocaStaticFresh
Ancestors
  concretizePtrChronologicalHistory concretizePtrLifetime lowerDloadPtrTaintBounds
  ptrDiscipline codegenRel venomExecSemantics venomInst
  finite_map list rich_list pred_set words venomState

Theorem ptr_dalloca_static_fresh_exclusion:
  t.vs_allocas = FEMPTY /\ post.vs_allocas = FEMPTY /\
  y < w2n t.vs_initial_fmp /\
  w2n t.vs_initial_fmp <= w2n t.vs_fmp ==>
  y NOTIN new_site_bytes t post
Proof
  simp[new_site_bytes_def] >> decide_tac
QED

Theorem ptr_dalloca_written_taint_footprint:
  (!op. op_taint tn op SUBSET {k | k < 32}) /\
  (?fuel. step_inst fuel C inst s = OK post) ==>
  written_taint tn inst s SUBSET range_bytes (step_writes inst s post)
Proof
  strip_tac >>
  namedCases_on `inst.inst_operands` ["", "a tail"] >>
  simp[written_taint_def] >>
  namedCases_on `tail` ["", "v rest"] >> simp[written_taint_def] >>
  namedCases_on `rest` ["", "n more"] >> simp[written_taint_def]
  >- (Cases_on `inst.inst_opcode = MSTORE \/ inst.inst_opcode = ISTORE` >> simp[] >>
      Cases_on `eval_operand a s` >> simp[] >>
      `?value. eval_operand v s = SOME value` by
        (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
         gvs[step_inst_non_invoke, step_inst_base_def,
             exec_write2_def, eval_operands_def, AllCaseEqs()] >> metis_tac[]) >>
      gvs[step_writes_def, source_memory_write_ranges_def,
          fixed_source_write_range_def, range_bytes_def, SUBSET_DEF] >>
      rpt strip_tac >> gvs[] >>
      `k < 32` by metis_tac[] >> decide_tac) >>
  namedCases_on `more` ["", "extra extras"] >> simp[] >>
  Cases_on `inst.inst_opcode = MCOPY` >> simp[] >>
  gvs[AllCaseEqs()] >>
  simp[step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, range_bytes_def, SUBSET_DEF] >>
  Cases_on `eval_operand a s` >> simp[] >>
  Cases_on `eval_operand v s` >> simp[] >>
  Cases_on `eval_operand n s` >> simp[] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

(* Freshness is queried at the actual successful post-state.  The call,
   block and return chronology rules leave memory taint unchanged. *)
Theorem ptr_dalloca_chrono_untainted_step:
  ptr_chrono_step C a b /\ ptr_observation_reachable vs C a /\
  y NOTIN a.po_taint.t_mem /\
  y NOTIN range_bytes (step_writes a.po_inst a.po_state b.po_state) /\
  (!fuel post. ~is_terminator a.po_inst.inst_opcode /\
    a.po_inst.inst_opcode <> INVOKE /\
    step_inst fuel C a.po_inst a.po_state = OK post ==>
    y NOTIN new_site_bytes a.po_state post) ==>
  y NOTIN b.po_taint.t_mem
Proof
  strip_tac >>
  `!op. op_taint a.po_taint op SUBSET {k | k < 32}` by
    (fs[ptr_observation_reachable_def] >>
     metis_tac[dload_reachable_op_taint_bound]) >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases] >> strip_tac >>
  gvs[ptr_observe_def, entry_taint_vars_def] >>
  Cases_on `lookup_block s'.vs_current_bb fn.fn_blocks` >> gvs[] >>
  `written_taint tn inst s SUBSET range_bytes (step_writes inst s s')` by
    (irule ptr_dalloca_written_taint_footprint >> simp[] >> metis_tac[]) >>
  `y NOTIN new_site_bytes s s'` by
    (first_x_assum irule >> qexists `fuel` >> simp[]) >>
  gvs[step_taint_def, mem_taint_def, step_writes_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem ptr_dalloca_chrono_untainted_suffix:
  !j n. ptr_chrono_history vs C h endpoint /\ n <= j /\ j < LENGTH h /\
  y NOTIN (EL n h).po_taint.t_mem /\
  (!k. n <= k /\ k < j ==>
    y NOTIN range_bytes
      (step_writes (EL k h).po_inst (EL k h).po_state (EL (SUC k) h).po_state) /\
    (!fuel post. ~is_terminator (EL k h).po_inst.inst_opcode /\
      (EL k h).po_inst.inst_opcode <> INVOKE /\
      step_inst fuel C (EL k h).po_inst (EL k h).po_state = OK post ==>
      y NOTIN new_site_bytes (EL k h).po_state post)) ==>
  y NOTIN (EL j h).po_taint.t_mem
Proof
  Induct >> rpt strip_tac >- gvs[] >>
  Cases_on `n = SUC j` >- gvs[] >>
  `n <= j /\ j < LENGTH h` by decide_tac >>
  `y NOTIN (EL j h).po_taint.t_mem` by
    (first_x_assum irule >> simp[] >> qexists `n` >> simp[] >>
     qx_gen_tac `k` >> strip_tac >>
     qpat_x_assum `!k. n <= k /\ k < SUC j ==> _`
       (qspec_then `k` mp_tac) >> simp[] >> metis_tac[]) >>
  `ptr_chrono_step C (EL j h) (EL (SUC j) h)` by
    (drule ptr_chrono_history_adjacent >>
     disch_then (qspec_then `j` mp_tac) >> simp[]) >>
  `ptr_observation_reachable vs C (EL j h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_MEM] >>
     strip_tac >> first_x_assum irule >> simp[MEM_EL] >>
     qexists `j` >> simp[]) >>
  qpat_x_assum `!k. n <= k /\ k < SUC j ==> _`
    (qspec_then `j` assume_tac) >>
  gvs[] >> drule_all ptr_dalloca_chrono_untainted_step >> simp[]
QED
