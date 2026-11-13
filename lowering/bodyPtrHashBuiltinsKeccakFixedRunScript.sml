(* Counted fixed-input hash instruction sequences. *)
Theory bodyPtrHashBuiltinsKeccakFixedRun
Ancestors bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsKeccakFixed
  bodyPtrDefs allocationPtr fragExecPtr fragGasSeqPtr
  ghostPcTransportPtr instIdxIndep exprSimHash ptrDiscipline venomState
  venomExecSemantics venomInst words finite_map builtinHashing emitHelperProps
  compileEnv emitHelper loweringHalt rich_list context exprLoweringProps

Theorem hash_store_sha3_seq_ptr:
  !D ctx fn PG G tn s sid hid p value out a v m.
    ptr_covers G tn p s 32 /\ lookup_var p s = SOME a /\
    eval_operand value s = SOME v /\ op_taint tn value = {} /\
    m <= 32 /\ ~ctx_has_dalloca ctx ==>
    ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst sid MSTORE [Var p;value] [];
       mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]] s G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst sid MSTORE [Var p;value] []) s =
    OK (mstore (w2n a) v s)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  drule_all hash_store_covered_clean >> strip_tac >>
  simp[inst_seq_ptr_def, ptr_inst_ok_mstore] >>
  qmatch_goalsub_abbrev_tac `ptr_inst_ok D 0 0 ctx fn G1 tn1 _ s1` >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1
    (mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]) s1` by suspend "check" >>
  simp[] >> Cases_on `step_inst_base (mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]) s1` >>
  simp[inst_seq_ptr_def] >> metis_tac[]
QED

Resume hash_store_sha3_seq_ptr[check]:
  irule hash_fixed_input_sha3_ok >>
  simp[Abbr `G1`, Abbr `tn1`, Abbr `s1`] >>
  rpt strip_tac >> gvs[lookup_var_def, mstore_def]
QED

Finalise hash_store_sha3_seq_ptr

Theorem hash_alloc_store_sha3_seq_ptr:
  !D ctx fn PG G tn s aid sid hid p value out m t v cenv cx es.
    stmt_state_rel ctx fn cenv cx es s /\
    MEM (mk_inst aid ALLOCA [Lit 32w] [p]) (fn_insts fn) /\
    step_inst_base (mk_inst aid ALLOCA [Lit 32w] [p]) s = OK t /\
    eval_operand value t = SOME v /\
    op_taint (step_taint (mk_inst aid ALLOCA [Lit 32w] [p]) s t tn) value = {} /\
    m <= 32 /\ ~ctx_has_dalloca ctx ==>
    ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst aid ALLOCA [Lit 32w] [p];
       mk_inst sid MSTORE [Var p;value] [];
       mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]] s G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  `32 < dimword (:256)` by
    simp[dimword_def, fcpTheory.index_bit0, fcpTheory.finite_bit0,
      fcpTheory.index_one, fcpTheory.finite_one] >>
  `ptr_covers (step_prov PG G (mk_inst aid ALLOCA [Lit 32w] [p]) t)
    (step_taint (mk_inst aid ALLOCA [Lit 32w] [p]) s t tn) p t 32` by
    (irule alloca_step_ptr_covers >> simp[] >> metis_tac[]) >>
  `?a. lookup_var p t = SOME a` by gvs[ptr_covers_def] >>
  simp[Once inst_seq_ptr_def, ptr_inst_ok_alloca] >>
  irule hash_store_sha3_seq_ptr >>
  gvs[lookup_var_def]
QED

Theorem hash_fixed_keccak_emission:
  !value m sa op sb.
    compile_keccak256_bytesm value m sa = (op,sb) ==>
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit 32w]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id+1) MSTORE
         [Var (STRING #"%" (toString sa.cs_next_var));value] [];
       mk_inst (sa.cs_next_id+2) SHA3
         [Var (STRING #"%" (toString sa.cs_next_var));Lit (n2w m)]
         [STRING #"%" (toString (sa.cs_next_var+1))]] /\
    op = Var (STRING #"%" (toString (sa.cs_next_var+1)))
Proof
  rpt gen_tac >>
  simp[compile_keccak256_bytesm_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, fresh_var_def, emit_def,
    emitted_insts_def, DROP_LENGTH_APPEND, arithmeticTheory.ADD_ASSOC] >>
  strip_tac >> gvs[listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem hash_alloc_store_sha3_counted:
  !D ctx fn PG G tn s aid sid hid p value out m t v cenv cx es u bb.
    stmt_state_rel ctx fn cenv cx es s /\
    MEM (mk_inst aid ALLOCA [Lit 32w] [p]) (fn_insts fn) /\
    step_inst_base (mk_inst aid ALLOCA [Lit 32w] [p]) s = OK t /\
    eval_operand value t = SOME v /\
    op_taint (step_taint (mk_inst aid ALLOCA [Lit 32w] [p]) s t tn) value = {} /\
    m <= 32 /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX [mk_inst aid ALLOCA [Lit 32w] [p];
       mk_inst sid MSTORE [Var p;value] [];
       mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]]
      (DROP s.vs_inst_idx bb.bb_instructions) /\
    run_inst_seq [mk_inst aid ALLOCA [Lit 32w] [p];
       mk_inst sid MSTORE [Var p;value] [];
       mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]] s = OK u ==>
    ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst aid ALLOCA [Lit 32w] [p];
       mk_inst sid MSTORE [Var p;value] [];
       mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]] s G' tn' /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (u with vs_inst_idx := s.vs_inst_idx+3))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all hash_alloc_store_sha3_seq_ptr >>
  disch_then (qspecl_then [`D`, `PG`, `G`, `sid`, `hid`, `out`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst aid ALLOCA [Lit 32w] [p]; mk_inst sid MSTORE [Var p;value] [];
     mk_inst hid SHA3 [Var p;Lit (n2w m)] [out]]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[is_terminator_def] >> metis_tac[]
QED

Theorem hash_inst_seq_triple_endpoint:
  !D lo ctx fn PG G tn i1 i2 i3 s t1 t2 u G3 tn3.
    inst_seq_ptr D lo ctx fn PG G tn [i1;i2;i3] s G3 tn3 /\
    step_inst_base i1 s = OK t1 /\
    step_inst_base i2 (t1 with vs_inst_idx := SUC s.vs_inst_idx) = OK t2 /\
    step_inst_base i3 (t2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)) = OK u ==>
    G3 = step_prov PG (step_prov PG (step_prov PG G i1 t1) i2 t2) i3 u /\
    tn3 = step_taint i3 (t2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)) u
      (step_taint i2 (t1 with vs_inst_idx := SUC s.vs_inst_idx) t2
        (step_taint i1 s t1 tn))
Proof
  rpt gen_tac >> strip_tac >> gvs[inst_seq_ptr_def]
QED

Theorem hash_inst_seq_triple_endpoint_raw:
  !D lo ctx fn PG G tn i1 i2 i3 s t1 t2 u G3 tn3.
    inst_seq_ptr D lo ctx fn PG G tn [i1;i2;i3] s G3 tn3 /\
    ~is_terminator i2.inst_opcode /\ ~is_terminator i3.inst_opcode /\
    step_inst_base i1 s = OK t1 /\ step_inst_base i2 t1 = OK t2 /\
    step_inst_base i3 t2 = OK u ==>
    G3 = step_prov PG (step_prov PG (step_prov PG G i1 t1) i2 t2) i3 u /\
    tn3 = step_taint i3 t2 u (step_taint i2 t1 t2 (step_taint i1 s t1 tn))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def]
QED
