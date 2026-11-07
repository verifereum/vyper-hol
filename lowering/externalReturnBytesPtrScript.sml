(* Allocated bytestring return: pointer-safe execution boundaries. *)
Theory externalReturnBytesPtr
Ancestors
  abiEncoderBytesPtr protectedAllocCorePtr fragExecPtr fragExec loweringHalt
  straightFragmentFramePtr abiBytesExecution abiDecodeStaticProps emitHelperProps exprLoweringProps rich_list list
  bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
  codegenRel context contextCodegenRel memLocDefs finite_map pred_set words arithmetic

Theorem ptr_inst_ok_return_operand:
  !cx ctx fn G tn s id p len n.
    eval_operand len s = SOME n /\ op_taint tn len = {} /\
    ptr_covers G tn p s (w2n n) /\ stor_taint_ok cx tn s /\
    ~ctx_has_dalloca ctx /\
    (!w i. lookup_var p s = SOME w /\ w2n w <= i /\
      i < w2n w+w2n n ==> i NOTIN tn.t_mem) ==>
    !fuel. ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn
      (mk_inst id RETURN [Var p;len] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    source_memory_write_ranges_def, source_memory_read_ranges_def,
    memory_range_of_operands_def, mk_inst_def, eval_operand_def] >>
  conj_tac >-
    (rpt strip_tac >> gvs[mem_read_ops_def] >> metis_tac[]) >>
  conj_tac >-
    (gen_tac >> Cases_on `op = Var p` >> gvs[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[eval_operand_def, step_taint_def, store_taint_def,
    adopt_reset_def, imm_taint_def, halt_state_def, set_returndata_def, ret_taint_def] >>
  gvs[stor_taint_ok_def, cx_dead_def, SUBSET_DEF] >>
  gen_tac >> Cases_on `x < w2n n` >> simp[] >>
  first_x_assum irule >> decide_tac
QED

Theorem ptr_safe_run_return_operand_halt:
  !cx ctx fn PG G tn s bb id p len n.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id RETURN [Var p;len] []) /\
    eval_operand len s = SOME n /\ op_taint tn len = {} /\
    ptr_covers G tn p s (w2n n) /\ stor_taint_ok cx tn s /\
    ~ctx_has_dalloca ctx /\
    (!w i. lookup_var p s = SOME w /\ w2n w <= i /\
      i < w2n w+w2n n ==> i NOTIN tn.t_mem) ==>
    !fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s /\
      ?ss. run_from fuel ctx fn s = Halt ss
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  conj_tac >-
    (`ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn
       (mk_inst id RETURN [Var p;len] []) s` by
       (irule ptr_inst_ok_return_operand >> metis_tac[]) >>
     simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def,
       step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     gvs[ptr_covers_def, mk_inst_def, eval_operand_def]) >>
  irule_at Any run_from_halt >>
  qrefinel [`_`,`mk_inst id RETURN [Var p;len] []`,`bb`] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  gvs[ptr_covers_def, mk_inst_def, eval_operand_def]
QED

Theorem compile_alloc_bytestring_return_ptr_safe:
  compile_alloc_buffer (32+contractABI$ceil32 cnt) sa = (buf,sb) /\
  compile_abi_encode_to_buf buf.buf_operand (Var src) (AbiBytestring maxlen) sb = (len,sd) /\
  fn_has_code sa sd func /\
  lookup_block sd.cs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH sd.cs_current_insts) =
    SOME (mk_inst id RETURN [buf.buf_operand;len] []) /\
  alloca_inv s /\ alloca_room ctx func s /\
  not_fresh_at sa src /\ eval_operand (Var src) s = SOME (n2w p) /\
  ptr_covers G tn src s (32+cnt) /\ mload p s = n2w cnt /\
  32+cnt <= cap /\ p+cap <= s.vs_alloca_next /\
  val_wf tv v /\ val_footprint tv v <= cap /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v p mem) /\
  (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
    sz = 32+contractABI$ceil32 cnt /\
    (p+cap <= b \/ b+32+contractABI$ceil32 cnt <= p)) /\
  cnt+31 < dimword(:256) /\ 32+contractABI$ceil32 cnt < dimword(:256) /\
  p+32+cnt < dimword(:256) /\
  (!i. p <= i /\ i < p+32+cnt ==> i NOTIN tn.t_mem) /\
  stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  !fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx func PG G tn s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends sa sb` by (drule compile_alloc_buffer_extends >> simp[]) >>
  `cs_extends sb sd` by (drule compile_abi_encode_to_buf_extends >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
    sz = 32+contractABI$ceil32 cnt /\
    (p+cap <= b \/ b+(32+contractABI$ceil32 cnt) <= p)` by
    (pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >> first_assum ACCEPT_TAC) >>
  drule_all protectedAllocExteriorPtrTheory.compile_alloc_buffer_protected_source_exterior_ptr >>
  disch_then (qspecl_then [`cx`,`(\gt r. F)`,`PG`,`G`]
    (qx_choose_then `dst` (qx_choose_then `d` (qx_choose_then `g1`
      (qx_choose_then `u1` (qx_choose_then `s1`
        (map_every assume_tac o CONJUNCTS))))))) >>
  `!i. p <= i /\ i < p+32+cnt ==> i NOTIN u1.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `~(d <= i /\ i < d+(32+contractABI$ceil32 cnt))` by decide_tac >>
     qpat_x_assum `!j. ~_ ==> _` (qspec_then `i` mp_tac) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `ptr_covers g1 u1 src s1 (32+cnt)` by metis_tac[] >>
  `lookup_var src s1 = SOME (n2w p) /\ lookup_var dst s1 = SOME (n2w d)` by
    (qpat_assum `eval_operand (Var src) s1 = _` mp_tac >>
     qpat_assum `eval_operand (Var dst) s1 = _` mp_tac >>
     pure_rewrite_tac[eval_operand_def] >> metis_tac[]) >>
  `mload p s1 = n2w cnt` by
    (qpat_x_assum `mload p s = _` mp_tac >>
     simp_tac (srw_ss()) [venomStateTheory.mload_def] >> asm_rewrite_tac[]) >>
  `d+32+contractABI$ceil32 cnt < dimword(:256)` by decide_tac >>
  `(p+32+cnt <= d \/ d+32+contractABI$ceil32 cnt <= p) = T` by decide_tac >>
  drule compile_alloc_buffer_emission >> strip_tac >>
  drule emitHelperPropsTheory.emit_inst_extends >> strip_tac >>
  `not_fresh_at sb src` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> asm_rewrite_tac[] >> simp_tac (srw_ss()) []) >>
  `compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sb = (len,sd)` by
    metis_tac[] >>
  `dst = p'` by
    (qpat_assum `buf.buf_operand = Var dst` mp_tac >>
     qpat_assum `buf.buf_operand = Var p'` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `not_fresh_at sb dst` by asm_rewrite_tac[] >>
  `(p+32+cnt <= d \/ d+32+contractABI$ceil32 cnt <= p) = T` by decide_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [boolTheory.EQ_CLAUSES]) >>
  drule_all compile_abi_encode_bytestring_frag_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`(\gt r. F)`]
    (qx_choose_then `g2` (qx_choose_then `u2` (qx_choose_then `s2`
      (map_every assume_tac o CONJUNCTS))))) >>
  `ptr_covers g2 u2 dst s2 (32+contractABI$ceil32 cnt) /\
   lookup_var dst s2 = SOME (n2w d)` by suspend "return_resource" >>
  `stor_taint_ok cx u2 s2` by suspend "return_storage" >>
  `frag_exec_ptr cx ctx PG sa sd
    (\g t w. g=G /\ t=tn /\ w=s)
    (\g t w. g=g2 /\ t=u2 /\ w=s2) (\gt r. F)` by
    (irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sa sb _ _ _` (irule_at Any) >> asm_rewrite_tac[]) >>
  irule frag_exec_ptr_complete >>
  qpat_assum `frag_exec_ptr _ _ _ sa sd _ _ _` (irule_at Any) >>
  asm_rewrite_tac[] >> simp_tac bool_ss [] >> rpt gen_tac >> strip_tac >>
  suspend "return_continuation"
QED

Resume compile_alloc_bytestring_return_ptr_safe[return_resource]:
  qpat_assum `!x. not_fresh_at sb x ==> _` (qspec_then `dst` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  conj_tac >-
    (qpat_x_assum `ptr_covers g1 u1 dst s1 _` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[]
QED

Resume compile_alloc_bytestring_return_ptr_safe[return_storage]:
  `~s1.vs_halted /\ s1.vs_current_bb = sb.cs_current_bb /\
   s1.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (asm_rewrite_tac[] >> simp_tac (srw_ss()) [listTheory.LENGTH_APPEND] >> decide_tac) >>
  `dec_straight sb sd` by
    (qpat_assum `compile_abi_encode_to_buf (Var dst) _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[compile_abi_bytes_shape] >> strip_tac >> gvs[] >>
     once_rewrite_tac[abi_bytes_append_prefix] >>
     simp[dec_straight_def, inst_extends_def, emitted_insts_def,
       DROP_LENGTH_APPEND, abi_bytes_append_def, is_terminator_def, mk_inst_def]) >>
  `EVERY (\inst. !w w' t. (step_taint inst w w' t).t_imm = t.t_imm)
    (emitted_insts sb sd)` by
    (qpat_assum `compile_abi_encode_to_buf (Var dst) _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     drule compile_abi_bytes_fragment >> strip_tac >>
     simp[abi_bytes_append_def, step_taint_def, imm_taint_def, mk_inst_def]) >>
  `u2.t_imm = u1.t_imm` by
    (irule frag_exec_ptr_straight_imm_frame >>
     qpat_assum `frag_exec_ptr _ _ _ sb sd _ _ _` (irule_at Any) >> asm_rewrite_tac[]) >>
  `stor_taint_ok cx u1 s1` by metis_tac[] >>
  qpat_x_assum `stor_taint_ok cx u1 s1` mp_tac >>
  pure_rewrite_tac[stor_taint_ok_def] >> asm_rewrite_tac[]
QED

Resume compile_alloc_bytestring_return_ptr_safe[return_continuation]:
  `lookup_block s2.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s2.vs_inst_idx = SOME (mk_inst id RETURN [Var dst;len] [])` by
    asm_rewrite_tac[] >>
  `ptr_covers g2 u2 dst s2 (w2n (n2w (32+contractABI$ceil32 cnt):256 word))` by
    (qpat_assum `32+contractABI$ceil32 cnt < _` (fn th =>
       simp_tac (srw_ss()) [wordsTheory.w2n_n2w, LESS_MOD, th]) >>
     first_assum ACCEPT_TAC) >>
  `!w i. lookup_var dst s2 = SOME w /\ w2n w <= i /\
     i < w2n w+w2n (n2w (32+contractABI$ceil32 cnt):256 word) ==> i NOTIN u2.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `w = n2w d` by metis_tac[optionTheory.SOME_11] >>
     `d < dimword(:256)` by decide_tac >>
     qpat_x_assum `!i. d <= i /\ _ ==> _` irule >>
     qpat_x_assum `w = n2w d` SUBST_ALL_TAC >>
     qpat_x_assum `i < w2n _ + _` mp_tac >>
     qpat_x_assum `w2n _ <= i` mp_tac >>
     asm_simp_tac bool_ss [wordsTheory.w2n_n2w, LESS_MOD] >> decide_tac) >>
  drule_all ptr_safe_run_return_operand_halt >>
  disch_then (qspec_then `PG` (qspec_then `0` strip_assume_tac)) >>
  qexists_tac `0` >> asm_rewrite_tac[] >> simp_tac (srw_ss()) []
QED

Finalise compile_alloc_bytestring_return_ptr_safe
