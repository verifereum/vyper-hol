(* Return-facing composition of the actual normalization allocation and store. *)
Theory externalReturnNormalizeRun
Ancestors
  externalNormalizePremises typedNormalizeRankMem typedNormalizeContinuation
  actualAllocExec memContinuation allocaFootprint fragExecMem
  venomExecSemantics venomState venomInst compileEnv context
  exprLoweringProps exprSim valueEncoding vyperTypeSystem loweringHalt

Theorem normalize_alloc_mem_cont[local]:
  compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc func /\
  exec_alloca (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sb.cs_next_var)]) s (n2w n : bytes32) = OK t /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  ~(t with vs_inst_idx := LENGTH sc.cs_current_insts).vs_halted /\
  (t with vs_inst_idx := LENGTH sc.cs_current_insts).vs_current_bb = sc.cs_current_bb
Proof
  strip_tac >>
  `step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sb.cs_next_var)]) s = OK t` by
    (fs[mk_inst_def] >>
     simp[step_inst_base_def, mk_inst_def, eval_operands_def, eval_operand_def]) >>
  `frag_exec_mem ctx sb sc (\u. u = s)
    (\u. u = t with vs_inst_idx := LENGTH sc.cs_current_insts) (K F)` by
    metis_tac[actual_alloc_buffer_step_mem] >>
  drule mem_cont_sim_from_fragment >> simp[] >>
  disch_then drule_all >> simp[] >> metis_tac[]
QED

(* The terminal block certificate is supplied by the actual Return suffix. *)
Theorem normalize_return_store_mem_cont:
  compile_alloc_buffer (type_memory_bytes cenv dty) sb = (buf,sc) /\
  compile_store_memory_typed cenv buf.buf_operand dty src sty sc = ((),sd) /\
  fn_has_code sb sc func /\ fn_has_code sc sd func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sb /\
  expr_val_at cenv cx sty sa sb es v src s /\ expr_val_rel cx sty v src s /\
  type_widens_to (get_tenv cx) sty dty /\ sty <> dty /\
  ~is_word_type dty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) /\
  type_memory_bytes cenv dty < dimword (:256) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  phi_prefix_length sc.cs_current_insts = 0 /\
  (?bb. lookup_block sd.cs_current_bb func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  eval_operand src s = SOME p /\
  (!x. src = Var x ==> not_fresh_at sb x) ==>
  ?dtv t b. evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
    mem_cont_sim ctx func s t /\ ~t.vs_halted /\
    t.vs_current_bb = sd.cs_current_bb /\ t.vs_inst_idx = LENGTH sd.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    val_in_memory dtv v b t.vs_memory /\
    b + type_memory_size dtv <= t.vs_alloca_next /\
    b + type_memory_size dtv < dimword (:256) /\
    alloca_room ctx func t /\ alloca_inv t
Proof
  strip_tac >> drule_all normalize_return_typed_windows >> strip_tac >>
  drule_all normalize_alloc_mem_cont >> strip_tac >>
  qmatch_asmsub_abbrev_tac `mem_cont_sim ctx func s u` >>
  `u.vs_inst_idx = LENGTH sc.cs_current_insts /\
   eval_operand src u = SOME p /\ eval_operand buf.buf_operand u = SOME (n2w b) /\
   u.vs_memory = t.vs_memory /\ u.vs_alloca_next = t.vs_alloca_next` by
    simp[Abbr `u`, eval_operand_def, lookup_var_def] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `!x. buf.buf_operand = Var x \/ src = Var x ==> not_fresh_at sc x` by metis_tac[] >>
  `w2n (n2w b : bytes32) = b` by
    (simp[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  mp_tac (Q.SPEC `type_rank cenv.ce_struct_fields dty` typed_store_rank_mem_cont) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  FAIL_TAC "store endpoint"
QED
