(* Actual instruction traces and ghost-threaded block continuations. *)
Theory ctorDeployMemoryRunPtrPrefixSequence
Ancestors
  ptrSafeRun exprLoweringProps list rich_list venomInst venomState arithmetic

Theorem prefix_trace_indexed[local]:
  !xs k bb u g q.
    isPREFIX xs (DROP k bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs /\
    (!j. j < LENGTH xs ==>
      step_inst_base (EL j xs) (u j) = OK (u (SUC j)) /\
      step_inst fuel ctx (EL j xs) ((u j) with vs_inst_idx := k+j) =
        OK ((u (SUC j)) with vs_inst_idx := k+j) /\
      ptr_safe_step D lo fuel ctx fn PG (g j) (q j) (EL j xs)
        ((u j) with vs_inst_idx := k+j) /\
      ghost_step fuel ctx PG (g j) (q j) (EL j xs)
        ((u j) with vs_inst_idx := k+j) = (g (SUC j),q (SUC j))) ==>
    run_inst_seq xs (u 0) = OK (u (LENGTH xs)) /\
    (ptr_safe_block D lo fuel ctx fn PG (g (LENGTH xs)) (q (LENGTH xs)) bb
       ((u (LENGTH xs)) with vs_inst_idx := k + LENGTH xs) ==>
     ptr_safe_block D lo fuel ctx fn PG (g 0) (q 0) bb
       ((u 0) with vs_inst_idx := k))
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!j. j < SUC _ ==> _`
    (qspec_then `0` (strip_assume_tac o SRULE [])) >>
  qpat_x_assum `!k bb u g q. _` (qspec_then `SUC k` mp_tac) >>
  disch_then (qspecl_then [`bb`, `u o SUC`, `g o SUC`, `q o SUC`] mp_tac) >>
  (impl_tac >-
    (simp[] >> conj_tac
     >- (Cases_on `DROP k bb.bb_instructions` >> gvs[] >>
         `DROP (SUC k) bb.bb_instructions = t` by
           (`k < LENGTH bb.bb_instructions` by
              (spose_not_then assume_tac >> gvs[DROP_LENGTH_TOO_LONG]) >>
            qspecl_then [`1`,`k`,`bb.bb_instructions`] mp_tac DROP_DROP >>
            simp[ADD1]) >> simp[]) >>
     rpt strip_tac >>
     qpat_x_assum `!j. j < SUC _ ==> _` (qspec_then `SUC j` mp_tac) >>
     simp[arithmeticTheory.ADD_CLAUSES])) >>
  simp[] >> strip_tac >> strip_tac >>
  `get_instruction bb k = SOME h` by
    (Cases_on `DROP k bb.bb_instructions` >> gvs[] >>
     `k < LENGTH bb.bb_instructions` by
       (spose_not_then assume_tac >> gvs[DROP_LENGTH_TOO_LONG]) >>
     gvs[get_instruction_def] >>
     qspecl_then [`0`,`k`,`bb.bb_instructions`] mp_tac EL_DROP >>
     gvs[]) >>
  simp[Once ptr_safe_block_def] >> gvs[ADD_CLAUSES, ADD_COMM]
QED

Theorem prefix_trace_ptr_safe_block:
  !xs bb s G tn u g q D lo fuel ctx fn PG.
    isPREFIX xs (DROP s.vs_inst_idx bb.bb_instructions) /\
    u 0 = s /\ g 0 = G /\ q 0 = tn /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs /\
    (!j. j < LENGTH xs ==>
      step_inst_base (EL j xs) (u j) = OK (u (SUC j)) /\
      step_inst fuel ctx (EL j xs) ((u j) with vs_inst_idx := s.vs_inst_idx+j) =
        OK ((u (SUC j)) with vs_inst_idx := s.vs_inst_idx+j) /\
      ptr_safe_step D lo fuel ctx fn PG (g j) (q j) (EL j xs)
        ((u j) with vs_inst_idx := s.vs_inst_idx+j) /\
      ghost_step fuel ctx PG (g j) (q j) (EL j xs)
        ((u j) with vs_inst_idx := s.vs_inst_idx+j) = (g (SUC j),q (SUC j))) ==>
    run_inst_seq xs s = OK (u (LENGTH xs)) /\
    (ptr_safe_block D lo fuel ctx fn PG (g (LENGTH xs)) (q (LENGTH xs)) bb
       ((u (LENGTH xs)) with vs_inst_idx := s.vs_inst_idx + LENGTH xs) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  rpt strip_tac >>
  drule_all prefix_trace_indexed >> gvs[]
QED
