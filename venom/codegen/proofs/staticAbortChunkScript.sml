(* Composition at the administrative / emitted-template boundary. *)
Theory staticAbortChunk
Ancestors
  staticAbortStack staticAbortEmit staticAbortTrace planWf stackOpSim
  planExec list arithmetic

Theorem static_abort_chunk_terminal:
  ops = pre ++ emit ++ post /\ prefix_wf lo n pre /\
  prefix_end_len lo n pre = m /\
  generate_emit_ops inst topics ps6 = (emit,ps7) /\
  MEM inst.inst_opcode [SSTORE;TSTORE;LOG] /\
  (inst.inst_opcode = LOG ==> topics <= 4) /\
  (if inst.inst_opcode = LOG then 2 + topics else 2) <= m /\
  s.as_call_ctx.cc_static /\
  s.as_stack = top ++ rest /\ LENGTH top = n /\
  asm_block_at prog s.as_pc (execute_plan fmp ops) ==>
  ?q t. q <= LENGTH (execute_plan fmp ops) + 4 /\
    static_abort_exception lo o2pc prog q s t
Proof
  strip_tac >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[execute_plan_append, asm_block_at_append] >> strip_tac >>
  drule_all prefix_static_abort_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `asm_block_at prog t.as_pc (execute_plan fmp emit)` by simp[] >>
  `LENGTH t.as_stack = m + LENGTH rest` by simp[] >>
  `t.as_call_ctx.cc_static` by simp[] >>
  `(if inst.inst_opcode = LOG then 2 + topics else 2) <= LENGTH t.as_stack` by
    (Cases_on `inst.inst_opcode = LOG` >> gvs[]) >>
  drule_all static_abort_emit_terminal_progress >>
  disch_then (qspecl_then [`o2pc`, `lo`] strip_assume_tac) >>
  qexistsl [`LENGTH (execute_plan fmp pre) + 1`, `t'`] >>
  conj_tac >- simp[] >>
  irule static_abort_exception_append >> goal_assum (drule_at Any) >> simp[]
QED

Theorem static_abort_chunk_progress:
  ops = pre ++ emit ++ post /\ prefix_wf lo n pre /\
  prefix_end_len lo n pre = m /\
  generate_emit_ops inst topics ps6 = (emit,ps7) /\
  static_abort_emit_io inst a b /\ a <= m /\ h + a = m + b /\
  prefix_wf lo h post /\ prefix_end_len lo h post = n' /\
  s.as_stack = top ++ rest /\ LENGTH top = n /\
  asm_block_at prog s.as_pc (execute_plan fmp ops) /\
  static_abort_emit_labels lo o2pc prog fmp
    (s.as_pc + LENGTH (execute_plan fmp pre)) inst emit ==>
  (?q t. q <= LENGTH (execute_plan fmp ops) /\
    static_abort_normal lo o2pc prog q s t /\
    t.as_pc = s.as_pc + LENGTH (execute_plan fmp ops) /\
    LENGTH t.as_stack = n' + LENGTH rest /\ t.as_call_ctx = s.as_call_ctx) \/
  (?q t. q <= LENGTH (execute_plan fmp ops) + 4 /\
    static_abort_exception lo o2pc prog q s t)
Proof
  strip_tac >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[execute_plan_append, asm_block_at_append] >> strip_tac >>
  drule_all prefix_static_abort_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `asm_block_at prog t.as_pc (execute_plan fmp emit) /\
   static_abort_emit_labels lo o2pc prog fmp t.as_pc inst emit` by
    metis_tac[ADD_COMM] >>
  `LENGTH t.as_stack = m + LENGTH rest` by simp[] >>
  `a <= LENGTH t.as_stack` by simp[] >>
  drule_all static_abort_emit_progress >> strip_tac
  >- (rename1 `static_abort_normal lo o2pc prog q t u` >>
      `LENGTH u.as_stack = h + LENGTH rest` by decide_tac >>
      `asm_block_at prog u.as_pc (execute_plan fmp post)` by simp[] >>
      `u.as_stack = TAKE h u.as_stack ++ DROP h u.as_stack /\
       LENGTH (TAKE h u.as_stack) = h /\
       LENGTH (DROP h u.as_stack) = LENGTH rest` by simp[] >>
      drule_all prefix_static_abort_sim >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      `static_abort_normal lo o2pc prog (LENGTH (execute_plan fmp pre) + q) s u` by
        metis_tac[static_abort_normal_append] >>
      `static_abort_normal lo o2pc prog
         ((LENGTH (execute_plan fmp pre) + q) + LENGTH (execute_plan fmp post)) s t'` by
        metis_tac[static_abort_normal_append] >>
      disj1_tac >>
      qexistsl [`LENGTH (execute_plan fmp pre) + q + LENGTH (execute_plan fmp post)`, `t'`] >>
      simp[]) >>
  rename1 `static_abort_exception lo o2pc prog q t u` >>
  disj2_tac >> qexistsl [`LENGTH (execute_plan fmp pre) + q`, `u`] >>
  conj_tac >- simp[] >>
  irule static_abort_exception_append >> goal_assum (drule_at Any) >> simp[]
QED
