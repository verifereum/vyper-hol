Theory asmFinalizerPrefixSplice
Ancestors
  asmSplice asmSymPc finalizerContract asmSymSem asmOptimizer asmWf

Theorem jump_delete_prefix_chunk:
  !pre x rest env ss.
    let p = pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ AsmLabel x :: rest in
    asm_static_wf p /\ ss.sym_base.as_pc = LENGTH pre /\
    ss.sym_base.as_stack = [] ==>
    sym_steps p env 2 ss = SymOK (sym_with_pc (LENGTH pre + 2) ss) /\
    (!i a. i < 2 /\ sym_steps p env i ss = SymOK a ==>
       a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p <> AsmOp "GAS")
Proof
  simp_tac bool_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  `~MEM (AsmLabel x) pre`
    by (fs[asm_static_wf_def] >>
        qpat_x_assum `asm_labels_unique _`
          (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                asm_labels_unique_append_not_mem)) >>
        disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  qabbrev_tac `p = pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++
                   AsmLabel x :: rest` >>
  `LENGTH pre < LENGTH p /\ EL (LENGTH pre) p = AsmPushLabel x /\
   LENGTH pre + 1 < LENGTH p /\ EL (LENGTH pre + 1) p = AsmOp "JUMP" /\
   INDEX_OF (AsmLabel x) p = SOME (LENGTH pre + 2)`
    by simp[Abbr `p`, listTheory.EL_APPEND_EQN, INDEX_OF_APPEND,
            INDEX_OF_CONS] >>
  qabbrev_tac `s1 = ss with <| sym_base := asm_next ss.sym_base;
                               sym_stack := Lab x 0 :: ss.sym_stack |>` >>
  `sym_step p env (AsmPushLabel x) ss = SymOK s1`
    by simp[Abbr `s1`, sym_step_push_label] >>
  `s1.sym_base.as_pc = LENGTH pre + 1 /\
   s1.sym_stack = Lab x 0 :: ss.sym_stack`
    by simp[Abbr `s1`, asmSemTheory.asm_next_def] >>
  `sym_step p env (AsmOp "JUMP") s1 =
   SymOK (s1 with <| sym_base := s1.sym_base with as_pc := LENGTH pre + 2;
                     sym_stack := ss.sym_stack |>)`
    by simp[sym_step_def, sym_step_op_def, sym_jump_def, sym_jump_dest_def] >>
  conj_tac
  >- (simp[sym_steps_pos, sym_steps_def, sym_terminal_def] >>
      simp[Abbr `s1`, sym_with_pc_def, sym_state_component_equality,
           asmSemTheory.asm_state_component_equality, asmSemTheory.asm_next_def]) >>
  rpt gen_tac >> strip_tac >>
  `i = 0 \/ i = 1` by decide_tac >>
  gvs[sym_steps_pos, sym_steps_def, sym_terminal_def, Abbr `s1`,
      asmSemTheory.asm_next_def]
QED
