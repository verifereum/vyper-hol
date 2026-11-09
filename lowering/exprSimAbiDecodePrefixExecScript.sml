Theory exprSimAbiDecodePrefixExec
Ancestors
  fragExec venomExecSemantics venomExecProofs venomInstProofs
  venomState venomInst exprLoweringProps instIdxIndep list rich_list

Theorem abi_decode_fetched_prefix_step:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  (!u. step_inst_base inst s <> Halt u) /\
  (!u. step_inst_base inst s = OK u ==> u.vs_current_bb = s.vs_current_bb) /\
  run_from fuel ctx fn s = Halt h ==>
  ?u. step_inst_base inst s = OK u /\
    run_from fuel ctx fn (u with vs_inst_idx := SUC s.vs_inst_idx) = Halt h
Proof
  strip_tac >>
  qpat_x_assum `run_from fuel ctx fn s = Halt h` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >>
  Cases_on `step_inst_base inst s` >> simp[] >>
  strip_tac >> rename1 `step_inst_base inst s = OK u` >>
  simp[Once run_from_def]
QED

Theorem abi_decode_contiguous_prefix_fetch:
  isPREFIX (i::xs) (DROP n bb.bb_instructions) ==>
  get_instruction bb n = SOME i /\
  isPREFIX xs (DROP (SUC n) bb.bb_instructions)
Proof
  strip_tac >>
  `?rest. DROP n bb.bb_instructions = i::rest /\ isPREFIX xs rest` by
    (Cases_on `DROP n bb.bb_instructions` >> gvs[]) >>
  `n < LENGTH bb.bb_instructions` by
    (CCONTR_TAC >> gvs[arithmeticTheory.NOT_LESS, DROP_LENGTH_TOO_LONG]) >>
  gvs[DROP_CONS_EL, get_instruction_def]
QED

Theorem abi_decode_run_prefix_inversion:
  !xs s fuel ctx fn bb h.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX xs (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    (!v z. step_inst_base i v <> Halt z) /\
    (!v z. step_inst_base i v = OK z ==>
      z.vs_current_bb = v.vs_current_bb)) xs /\
  run_from fuel ctx fn s = Halt h ==>
  ?a. run_inst_seq xs s = OK a /\
    run_from fuel ctx fn
      (a with vs_inst_idx := s.vs_inst_idx + LENGTH xs) = Halt h
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (qexists_tac `s` >> simp[run_inst_seq_def]) >>
  drule abi_decode_contiguous_prefix_fetch >> strip_tac >>
  fs[EVERY_DEF] >>
  `?u. step_inst_base h s = OK u /\
    run_from fuel ctx fn (u with vs_inst_idx := SUC s.vs_inst_idx) = Halt h'` by
    (irule abi_decode_fetched_prefix_step >> metis_tac[]) >>
  `u.vs_current_bb = s.vs_current_bb` by metis_tac[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) xs` by fs[EVERY_MEM] >>
  qpat_x_assum `!s fuel ctx fn bb h. _`
    (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then drule_all >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  Cases_on `run_inst_seq xs u` >>
  simp[exec_result_map_def, run_inst_seq_def] >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

(* The compiler-facing form: only the emitted prefix and its end cursor occur. *)
Theorem abi_decode_setup_prefix_inversion:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ xs ++ rest /\
  s.vs_inst_idx = LENGTH pre /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    (!v z. step_inst_base i v <> Halt z) /\
    (!v z. step_inst_base i v = OK z ==>
      z.vs_current_bb = v.vs_current_bb)) xs /\
  run_from fuel ctx fn s = Halt h ==>
  ?a. run_inst_seq xs s = OK a /\
    run_from fuel ctx fn (a with vs_inst_idx := LENGTH (pre ++ xs)) = Halt h
Proof
  strip_tac >>
  `isPREFIX xs (DROP s.vs_inst_idx bb.bb_instructions)` by
    (asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp[IS_PREFIX_APPEND]) >>
  drule_all abi_decode_run_prefix_inversion >> simp[]
QED
