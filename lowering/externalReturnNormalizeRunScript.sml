(* Return-facing composition of the actual normalization allocation and store. *)
Theory externalReturnNormalizeRun
Ancestors
  externalNormalizePremises typedNormalizeRankMem typedNormalizeContinuation
  actualAllocExec memContinuation allocaFootprint fragExecMem typedStoreEndpoint localPtrsProps
  externalReturnBounds abiBuiltinAllocation finite_map allocaSiteResource
  typedNormalizeEntryBoundary
  venomExecSemantics venomState venomInst compileEnv context
  exprLoweringProps exprSimDefs exprSimProps loweringPosts valueEncoding vyperTypeSystem loweringHalt

Theorem normalize_alloc_mem_cont:
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
     simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operands_def, eval_operand_def]) >>
  `frag_exec_mem ctx sb sc (\u. u = s)
    (\u. u = t with vs_inst_idx := LENGTH sc.cs_current_insts) (K F)` by
    metis_tac[actual_alloc_buffer_step_mem] >>
  drule mem_cont_sim_from_fragment >> simp[] >>
  disch_then drule_all >> simp[] >> metis_tac[]
QED

Theorem normalize_alloc_registered[local]:
  compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc func /\
  stmt_state_rel ctx func cenv cx es s /\ n < dimword (:256) /\
  exec_alloca (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sb.cs_next_var)]) s (n2w n : bytes32) = OK t /\
  eval_operand buf.buf_operand t = SOME (n2w b) /\
  b < dimword (:256) /\ alloca_room ctx func t ==>
  FLOOKUP t.vs_allocas sb.cs_next_id = SOME (b,n)
Proof
  strip_tac >> drule_all actual_alloc_buffer_site >> strip_tac >>
  drule_at (Pat `MEM _ _`) stmt_state_rel_alloca_site >>
  disch_then drule >>
  disch_then (qspec_then `n` mp_tac) >> simp[mk_inst_def] >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
  gvs[exec_alloca_def, mk_inst_def, update_var_def, eval_operand_def,
      lookup_var_def, abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
  drule alloca_room_next_lt >> simp[] >>
  strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all alloca_site_registered_below >> decide_tac
QED

Theorem normalize_alloc_other_sites[local]:
  exec_alloca (mk_inst aid ALLOCA [Lit n] [out]) s n = OK t ==>
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!j. j <> aid ==> FLOOKUP t.vs_allocas j = FLOOKUP s.vs_allocas j)
Proof
  Cases_on `FLOOKUP s.vs_allocas aid`
  >- (simp[exec_alloca_def, mk_inst_def, update_var_def] >>
      rpt strip_tac >> gvs[FLOOKUP_UPDATE]) >>
  PairCases_on `x` >>
  simp[exec_alloca_def, mk_inst_def, update_var_def] >>
  rpt strip_tac >> gvs[]
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
  compile_external_return ret prim raw info msz nr nkey ut iv sd = (x,se) /\
  (nr ==> iv) /\ fn_has_code sd se func /\
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
    alloca_room ctx func t /\ alloca_inv t /\
    FLOOKUP t.vs_allocas sb.cs_next_id = SOME (b,type_memory_bytes cenv dty) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid. aid <> sb.cs_next_id ==>
      FLOOKUP t.vs_allocas aid = FLOOKUP s.vs_allocas aid)
Proof
  strip_tac >>
  Q.SUBGOAL_THEN
    `emitted_blocks sc sd <> [] ==>
      ?bb. lookup_block sd.cs_current_bb func.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0` assume_tac
    >- metis_tac[normalize_typed_external_return_entry] >>
  drule_all normalize_return_typed_windows >>
  disch_then (qx_choose_then `dtv` (qx_choose_then `t`
    (qx_choose_then `b` (map_every assume_tac o CONJUNCTS)))) >>
  `b < dimword (:256)` by decide_tac >>
  drule_all normalize_alloc_other_sites >> strip_tac >>
  drule_all normalize_alloc_registered >> disch_tac >>
  drule_all normalize_alloc_mem_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `mem_cont_sim ctx func s u` >>
  `u.vs_inst_idx = LENGTH sc.cs_current_insts /\
   eval_operand src u = SOME p /\ eval_operand buf.buf_operand u = SOME (n2w b) /\
   u.vs_memory = t.vs_memory /\ u.vs_alloca_next = t.vs_alloca_next` by
    simp[Abbr `u`, eval_operand_def, lookup_var_def] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `!x. buf.buf_operand = Var x \/ src = Var x ==> not_fresh_at sc x` by
    (gen_tac >> strip_tac >> gvs[] >> metis_tac[]) >>
  `w2n (n2w b : bytes32) = b` by
    (simp[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `alloca_inv u /\ alloca_room ctx func u` by
    (conj_tac
     >- (irule alloca_inv_fields >> qexists_tac `t` >> simp[Abbr `u`]) >>
     irule alloca_room_fields >> qexists_tac `t` >> simp[Abbr `u`]) >>
  `val_in_memory stv v (w2n p) u.vs_memory /\
   w2n p + type_memory_size stv <= u.vs_alloca_next /\
   b + type_memory_size dtv <= u.vs_alloca_next` by metis_tac[] >>
  Q.SUBGOAL_THEN
  `w2n (n2w b : bytes32) + type_memory_size dtv <= u.vs_alloca_next /\
   w2n (n2w b : bytes32) + type_memory_size dtv < dimword (:256) /\
   w2n p + type_memory_size stv < dimword (:256) /\
   (w2n p + type_memory_size stv <= w2n (n2w b : bytes32) \/
    w2n (n2w b : bytes32) + type_memory_size dtv <= w2n p)`
    (map_every assume_tac o CONJUNCTS) >- metis_tac[] >>
  drule_all typed_store_mem_cont_resources >>
  disch_then (qx_choose_then `z` (map_every assume_tac o CONJUNCTS)) >>
  `mem_cont_sim ctx func s z` by
    (irule mem_cont_sim_trans >> qexists_tac `u` >> simp[]) >>
  qexistsl_tac [`dtv`,`z`,`b`] >> simp[Abbr `u`] >> metis_tac[]
QED
