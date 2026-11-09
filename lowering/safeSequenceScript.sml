(* Prefix-local memory safety for straight-line emitted code. *)
Theory safeSequence
Ancestors
  fragExecMem fragExec exprLoweringProps venomExecSemantics venomState
  unitTransformDefs memSafeRun instIdxIndep venomInst venomInstProofs
  venomExecProofs list rich_list

Theorem run_inst_seq_prefix_safe_append:
  (!pre i post u. xs = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    inst_mem_below_frontier i u) /\
  run_inst_seq xs s = OK t /\
  (!pre i post u. ys = pre ++ i::post /\ run_inst_seq pre t = OK u ==>
    inst_mem_below_frontier i u) ==>
  !pre i post u. xs ++ ys = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    inst_mem_below_frontier i u
Proof
  rpt strip_tac >>
  `(?l. xs = pre ++ [i] ++ l /\ post = l ++ ys) \/
   (?l. pre = xs ++ l /\ ys = l ++ [i] ++ post)` by
    metis_tac[APPEND_EQ_APPEND_MID, APPEND, APPEND_ASSOC] >>
  gvs[]
  >- (qpat_x_assum `!pre' i' post' u'. pre ++ [i] ++ l = _ /\ _ ==> _` irule >>
      qexistsl_tac [`l`, `pre`] >> simp[]) >>
  qpat_x_assum `run_inst_seq xs s = OK t` (mp_tac o MATCH_MP run_inst_seq_append) >>
  disch_then (qspec_then `l` assume_tac) >>
  qpat_x_assum `!pre' i' post' u'. l ++ [i] ++ post = _ /\ _ ==> _` irule >>
  qexistsl_tac [`post`, `l`] >> gvs[]
QED

Theorem inst_mem_below_frontier_inst_idx[simp]:
  inst_mem_below_frontier i (s with vs_inst_idx := n) =
  inst_mem_below_frontier i s
Proof
  simp[inst_mem_below_frontier_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def,
    codegenRelTheory.sized_source_write_range_def,
    contextCodegenRelTheory.memory_range_of_operands_def,
    contextCodegenRelTheory.dret_memory_read_ranges_def,
    eval_op_inst_idx, eval_ops_inst_idx]
QED

Theorem run_inst_seq_prefix_safe_tail[local]:
  step_inst_base h s = OK t ==>
  (!pre i post u. h::xs = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    inst_mem_below_frontier i u) ==>
  !pre i post u. xs = pre ++ i::post ==> run_inst_seq pre t = OK u ==>
    inst_mem_below_frontier i u
Proof
  rpt strip_tac >> first_x_assum irule >>
  qexistsl_tac [`post`, `h::pre`] >> simp[run_inst_seq_def]
QED

Theorem run_inst_seq_prefix_safe_inst_idx[local]:
  !xs s. EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  (!pre i post u. xs = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    inst_mem_below_frontier i u) ==>
  !n pre i post u. xs = pre ++ i::post /\
    run_inst_seq pre (s with vs_inst_idx := n) = OK u ==>
    inst_mem_below_frontier i u
Proof
  rpt strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) pre` by gvs[EVERY_APPEND] >>
  gvs[run_inst_seq_inst_idx] >>
  Cases_on `run_inst_seq pre s` >> gvs[exec_result_map_def] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem prefix_DROP_CONS[local]:
  !l n h rest. DROP n l = h::rest ==>
    n < LENGTH l /\ EL n l = h /\ DROP (SUC n) l = rest
Proof
  Induct >> simp[] >> Cases_on `n` >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem mem_safe_block_run_inst_seq:
  !xs s fuel ctx bb.
    isPREFIX xs (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) xs /\
    (!pre i post u. xs = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      inst_mem_below_frontier i u) ==>
    (!u. run_inst_seq xs s = OK u ==>
       (mem_safe_block fuel ctx bb
          (u with vs_inst_idx := s.vs_inst_idx + LENGTH xs) ==>
        mem_safe_block fuel ctx bb s)) /\
    (!a u. run_inst_seq xs s = Abort a u ==> mem_safe_block fuel ctx bb s)
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >> fs[] >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h::rest /\
    isPREFIX xs rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  `get_instruction bb s.vs_inst_idx = SOME h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = rest` by
    (drule prefix_DROP_CONS >> simp[get_instruction_def]) >>
  `inst_mem_below_frontier h s` by
    (first_x_assum irule >> qexistsl_tac [`xs`, `[]`] >> simp[run_inst_seq_def]) >>
  `mem_safe_block fuel ctx bb s =
    (case step_inst_base h s of
       OK s1 => mem_safe_block fuel ctx bb (s1 with vs_inst_idx := SUC s.vs_inst_idx)
     | _ => T)` by
    (CONV_TAC (LAND_CONV (REWR_CONV mem_safe_block_def)) >>
     asm_simp_tac (srw_ss())
       [mem_safe_step_non_invoke, step_inst_non_invoke]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK s1` >>
  `s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  drule run_inst_seq_prefix_safe_tail >>
  disch_then (qspec_then `xs` (mk_asm "tail")) >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  `!pre i post u. xs = pre ++ i::post /\ run_inst_seq pre s1 = OK u ==>
    inst_mem_below_frontier i u` by
    (rpt strip_tac >> asm "tail" irule >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`post`, `pre`] >> asm_rewrite_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) xs` by fs[EVERY_MEM] >>
  `!pre i post u. xs = pre ++ i::post /\
      run_inst_seq pre (s1 with vs_inst_idx := SUC s.vs_inst_idx) = OK u ==>
      inst_mem_below_frontier i u` by
    (qspecl_then [`xs`, `s1`] mp_tac run_inst_seq_prefix_safe_inst_idx >>
     asm_rewrite_tac[] >> disch_then (qspec_then `SUC s.vs_inst_idx` ACCEPT_TAC)) >>
  first_x_assum (qspecl_then [`s1 with vs_inst_idx := SUC s.vs_inst_idx`,
    `fuel`, `ctx`, `bb`] mp_tac) >>
  asm_rewrite_tac[] >> simp[run_inst_seq_inst_idx] >> strip_tac >>
  Cases_on `run_inst_seq xs s1` >> gvs[exec_result_map_def] >>
  metis_tac[arithmeticTheory.ADD_CLAUSES]
QED

Theorem frag_exec_mem_run_inst_seq:
  !ctx st st' P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
      (emitted_insts st st') /\
    (!s. P s ==>
       (!pre i post u. emitted_insts st st' = pre ++ i::post /\
          run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u) /\
       ((?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
              Q (s' with vs_inst_idx := LENGTH st'.cs_current_insts)) \/
        (?a s'. run_inst_seq (emitted_insts st st') s = Abort a s' /\
                !n. R (Abort a (s' with vs_inst_idx := n))))) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  irule fragExecMemTheory.frag_exec_mem_run_inst_seq >>
  `EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
     (emitted_insts st st') /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_MEM] >>
  simp[] >> rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  simp[] >> irule run_inst_seq_mem_ok_of_prefix_safe >> rw[] >>
  first_x_assum irule >> qexistsl_tac [`post`, `pre`] >> simp[]
QED
