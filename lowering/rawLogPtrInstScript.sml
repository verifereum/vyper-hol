(* Reusable pointer discipline boundary for LOG's stack-order operands. *)
Theory rawLogPtrInst
Ancestors
  bodyPtrDefs ptrDiscipline ptrSafeRun venomInst venomState
  venomExecSemantics contextCodegenRel codegenRel memLocDefs
  finite_map words list rich_list pred_set fragGasSeqPtr instIdxIndep

Theorem log_access_ok:
  LENGTH topics < dimword (:256) /\
  eval_operand pop s = SOME off /\ eval_operand len s = SOME n /\
  eval_operands topics s = SOME vals /\
  (n <> 0w ==> ?p b sz. pop = Var p /\ FLOOKUP G p = SOME (b,sz) /\
    b <= w2n off /\ w2n off + w2n n <= b + sz) ==>
  access_ok 0 G fn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [len;pop]) []) s
Proof
  strip_tac >>
  simp[access_ok_def, source_memory_read_ranges_def,
    source_memory_write_ranges_def, memory_range_of_operands_def,
    mem_read_ops_def, mk_inst_def, REVERSE_APPEND, eval_operand_def] >>
  Cases_on `topics` >> simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[w2n_eq_0]
QED

Theorem log_taint_ok:
  LENGTH topics < dimword (:256) /\
  eval_operand pop s = SOME off /\ eval_operand len s = SOME n /\
  eval_operands topics s = SOME vals /\
  EVERY (\op. op_taint tn op = {}) topics /\
  op_taint tn pop = {} /\ op_taint tn len = {} /\
  (!i. w2n off <= i /\ i < w2n off + w2n n ==> i NOTIN tn.t_mem) ==>
  taint_ok fn tn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [len;pop]) []) s
Proof
  strip_tac >>
  simp[taint_ok_def, source_memory_read_ranges_def,
    memory_range_of_operands_def, mk_inst_def, REVERSE_APPEND,
    eval_operand_def, MEM_APPEND, MEM_REVERSE] >>
  fs[EVERY_MEM] >>
  `op_taint tn (Lit (n2w (LENGTH topics))) = {}` by simp[op_taint_def] >>
  metis_tac[]
QED

Theorem log_inst_ok:
  LENGTH topics < dimword (:256) /\
  eval_operand pop s = SOME off /\ eval_operand len s = SOME n /\
  eval_operands topics s = SOME vals /\
  (n <> 0w ==> ?p b sz. pop = Var p /\ FLOOKUP G p = SOME (b,sz) /\
    b <= w2n off /\ w2n off + w2n n <= b + sz) /\
  EVERY (\op. op_taint tn op = {}) topics /\
  op_taint tn pop = {} /\ op_taint tn len = {} /\
  (!i. w2n off <= i /\ i < w2n off + w2n n ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [len;pop]) []) s = OK t /\
  t.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [len;pop]) []) s
Proof
  strip_tac >>
  `access_ok 0 G fn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [len;pop]) []) s` by
    (irule log_access_ok >> metis_tac[]) >>
  `taint_ok fn tn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [len;pop]) []) s` by
    (irule log_taint_ok >> metis_tac[]) >>
  simp[ptr_inst_ok_def, allocas_from_def, mk_inst_def, step_inst_non_invoke] >>
  rpt strip_tac >> gvs[]
QED

Theorem log_ghost:
  step_prov PG G (mk_inst id LOG ops []) (s with vs_logs := logs) = G /\
  step_taint (mk_inst id LOG ops []) s (s with vs_logs := logs) tn = tn
Proof
  `new_site_bytes s (s with vs_logs := logs) = {}` by
    simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, step_taint_def, mk_inst_def,
    set_var_taint_def, store_taint_def, adopt_reset_def, mem_taint_def,
    step_writes_def, source_memory_write_ranges_def, written_taint_def,
    range_bytes_def, imm_taint_def, taint_component_equality, DRESTRICT_UNIV] >>
  Cases_on `ops` >> simp[] >> Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >> Cases_on `t` >> simp[]
QED

Theorem log_ghost_frame:
  ghost_inv d cenv cx (es with logs := logs) G tn
    ((s with vs_logs := vlogs) with vs_inst_idx := k) =
    ghost_inv d cenv cx es G tn s
Proof
  simp[ghost_inv_def, ptr_covers_def, return_buf_ptr_def, stor_taint_ok_def,
    lookup_var_def, mem_agree_outside_def] >> Cases_on `d` >> simp[return_buf_ptr_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem log_counted_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [len;pop]) []) /\
  LENGTH topics < dimword (:256) /\
  eval_operand pop s = SOME off /\ eval_operand len s = SOME n /\
  eval_operands topics s = SOME vals /\
  (n <> 0w ==> ?p b sz. pop = Var p /\ FLOOKUP G p = SOME (b,sz) /\
    b <= w2n off /\ w2n off + w2n n <= b + sz) /\
  EVERY (\op. op_taint tn op = {}) topics /\
  op_taint tn pop = {} /\ op_taint tn len = {} /\
  (!i. w2n off <= i /\ i < w2n off + w2n n ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [len;pop]) []) s =
    OK (s with vs_logs := logs) ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn
    (OK ((s with vs_logs := logs) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [len;pop]) []) s` by
    (irule log_inst_ok >> fs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  irule (Q.INST [`i` |->
    `mk_inst id LOG (Lit (n2w (LENGTH topics)) :: REVERSE topics ++ [len;pop]) []`,
    `u` |-> `s with vs_logs := logs`] straight_line_ptr_edge |>
    SRULE [log_ghost] |> SRULE [mk_inst_def, is_terminator_def]) >>
  fs[mk_inst_def]
QED
