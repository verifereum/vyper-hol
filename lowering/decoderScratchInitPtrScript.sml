Theory decoderScratchInitPtr
Ancestors
  decoderArrayInitPtr abiScratchDecoderInitReentry
  abiDecoderArrayLoopInit abiDecoderArrayInit abiDecoderReentry
  compileEnv bodyPtrDefs ptrSafeRun ptrDiscipline abiDecoderContract
  abiDecoderArrayInitReentry venomState abiDecoderIndexInit words arithmetic

(* Physical ownership and the ghost follow the same original-state execution.
   In particular generated names may already be bound at loop reentry. *)
Theorem calldata_scratch_array_init_reentry_ptr:
  abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w)
    maxn abi_sz st = (setup,loop_st) /\
  eval_operand src initial = SOME (n2w source_base) /\
  eval_operand (Var root) initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load CALLDATALOAD (n2w source_base:bytes32) initial = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ ptr_covers G tn root initial totalbytes /\
  32 <= totalbytes /\ op_taint tn src = {} ==>
  ?actual slot H u q.
    run_inst_seq (emitted_insts st loop_st) initial = OK actual /\
    inst_extends st loop_st /\
    abi_decoder_array_init_post setup st.cs_next_var limit_st (loop_st.cs_next_id - 2)
      first last b cap d n initial actual /\
    abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
      limit_st d 32 b cap initial actual /\
    FST setup = Var q /\ eval_operand (FST setup) actual = SOME (n2w slot) /\
    b <= slot /\ slot + 32 <= b + cap /\ slot + 32 < dimword (:256) /\
    mload slot actual = 0w /\
    ptr_covers H u q
      (actual with vs_inst_idx := LENGTH (emitted_insts st loop_st) + initial.vs_inst_idx) 32 /\
    ptr_covers H u root
      (actual with vs_inst_idx := LENGTH (emitted_insts st loop_st) + initial.vs_inst_idx) totalbytes /\
    op_taint u (SND setup) = {} /\ op_prov H (SND setup) = NONE /\
    frag_exec_ptr cx ctx PG st loop_st
      (\g z v. g = G /\ z = tn /\ v = initial)
      (\g z v. g = H /\ z = u /\
        v = (actual with vs_inst_idx := LENGTH (emitted_insts st loop_st) + initial.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    u.t_mem = (tn.t_mem DIFF {x | d <= x /\ x < d + 32})
      DIFF {x | slot <= x /\ x < slot + 32} /\
    (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code st loop_st func /\ allocas_from lower initial /\ lower <= initial.vs_alloca_next /\
      ~ctx_has_dalloca ctx' /\ initial.vs_current_bb = st.cs_current_bb /\
      initial.vs_inst_idx = LENGTH st.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (actual with vs_inst_idx := LENGTH loop_st.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD /\
   abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decode_source_opcode_def, abi_decoder_operand_live_def] >>
  drule_all (abi_scratch_decoder_init_reentry |> Q.INST [`hi` |-> `Lit 0w`] |> SRULE []) >> strip_tac >>
  `abi_decoder_array_init_post setup st.cs_next_var limit_st (loop_st.cs_next_id - 2)
    first last b cap d n initial actual` by
    (simp_tac bool_ss [abi_decoder_array_init_post_def] >> qexists_tac `slot` >>
     asm_simp_tac bool_ss []) >>
  drule_all abi_decode_array_loop_init_site_bounds >> strip_tac >>
  `abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
    limit_st d 32 b cap initial actual` by
    (irule abi_scratch_decoder_init_effect >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`n`, `setup`, `loop_st.cs_next_id - 2`] >> simp[]) >>
  `not_fresh_at st root /\ (!x. src = Var x ==> not_fresh_at st x)` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     Cases_on `src` >> fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def]) >>
  `lookup_var root initial = SOME (n2w d)` by fs[eval_operand_def] >>
  drule_all calldata_array_init_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`] strip_assume_tac) >>
  `slot + 32 < dimword (:256)` by
    (drule abi_decoder_budget_word_bound >> decide_tac) >>
  `slot = p` by
    (gvs[] >> metis_tac[n2w_11, LESS_TRANS, DECIDE ``!x:num. x < x + 32``]) >>
  qexistsl_tac [`actual`, `slot`, `H`, `u`, `q`] >> gvs[]
QED
