(* Shared protected, read-only straight-line execution boundary. *)
Theory exprSimBopRestWordLoadPath
Ancestors
  fragGasSeq fragGasPath emitHelperProps venomExecSemantics venomState
  venomInst list rich_list finite_map arithmetic

Theorem rest_word_readonly_sequence_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
              ~is_terminator i.inst_opcode) code /\
  run_inst_seq code s = OK t /\
  (!i u v. MEM i code /\ step_inst_base i u = OK v ==>
     v = u with vs_vars := v.vs_vars /\
     (!x. P x ==> FLOOKUP v.vs_vars x = FLOOKUP u.vs_vars x)) ==>
  let u = t with vs_inst_idx := s.vs_inst_idx + LENGTH code in
  gas_path ctx func s 0 (OK u) /\
  u = s with <|vs_vars := t.vs_vars;
                vs_inst_idx := s.vs_inst_idx + LENGTH code|> /\
  (!x. P x ==> FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    gvs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    gvs[FILTER_EQ_NIL, EVERY_MEM] >>
  drule_all tuple_run_inst_seq_gas_path >> simp[] >> strip_tac >>
  drule_all run_inst_seq_protected_frame >> strip_tac >>
  simp[] >>
  qpat_x_assum `t = _` (fn th => simp[Once th])
QED
