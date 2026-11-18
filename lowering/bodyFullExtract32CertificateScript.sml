(* Horizon-independent ghost certification for Extract32. *)
Theory bodyFullExtract32Certificate
Ancestors
  extract32Certificate exprSimExtract32Read exprLoweringProps
  fragGasCopyLoop instSeqPtrLo fragGasSeqPtr ptrDiscipline
  compileEnv venomState venomInst freshWrites list

Theorem extract32_suffix_certificate:
  compile_extract32_load (Var len) (Var data) offset sa = (raw,sm) /\
  compile_clamp_basetype raw typ sm = (result,sb) /\
  not_fresh_at sa len /\ not_fresh_at sa data /\
  (!z. offset = Var z ==> not_fresh_at sa z) /\ (!l. offset <> Label l) /\
  op_prov G offset = NONE /\ op_taint tn offset = {} /\
  op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
  ptr_mem_ok cx ty (BytesV bs) src G tn s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic m))) /\
  eval_operand src s = SOME (n2w p) /\
  eval_operand (Var data) s = SOME (n2w (p+32)) /\
  eval_operand (Var len) s = SOME (n2w (LENGTH bs)) /\
  eval_operand offset s = SOME (n2w n) /\
  n < dimword(:256) /\ p+32+LENGTH bs < dimword(:256) /\
  (!span. 0 < LENGTH bs /\ span <= LENGTH bs ==> ptr_covers G tn data s span) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  ?HG th.
    (!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s HG th) /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      op_prov HG result = NONE /\ op_taint th result = {}) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP HG x = FLOOKUP G x /\
      op_taint th (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `!D. ?HG th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s HG th /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      op_prov HG result = NONE /\ op_taint th result = {}) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP HG x = FLOOKUP G x /\
      op_taint th (Var x) = op_taint tn (Var x))` by
    (gen_tac >> drule_all extract32_tail_ready_certificate >>
     disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
     qexistsl_tac [`HG`,`th`] >> simp[] >>
     first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  first_assum (qspec_then `ARB` strip_assume_tac) >>
  qexistsl_tac [`HG`,`th`] >> simp[] >> gen_tac >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s HG th` by
    (first_x_assum (qspec_then `D` strip_assume_tac) >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  irule inst_seq_ptr_lower_bound_transport >>
  reverse conj_tac >- (simp[] >> qexists_tac `0` >> simp[]) >>
  drule_all extract32_tail_code_cuts >> strip_tac >>
  mp_tac (Q.SPECL [`raw`,`typ`] extract32_read_clamp_basetype) >>
  mp_tac (Q.SPECL [`Var len`,`Var data`,`offset`] extract32_read_load) >>
  simp[extract32_straight_read_frame_def] >>
  ntac 2 (disch_then drule >> strip_tac) >>
  gvs[EVERY_APPEND, EVERY_MEM] >> rpt strip_tac >>
  `fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD` by metis_tac[] >>
  gvs[fresh_write_op_def]
QED
