(*
 * Expression simulation for the conditional expression (#636, part 3)
 *
 * x if c else y lowers to c's fragment, a JNZ on its operand, one block per
 * branch that lowers its expression and assigns its operand to a fresh
 * variable, and a JMP from each branch to a common exit block
 * (compile_expr_ifexp).  The source evaluates c and then the branch its
 * boolean picks (eval_expr_ifexp_cases).
 *
 * TOP-LEVEL:
 *   compile_ifexp_vv_sim      — expr_vv_sim of an IfExp from expr_sim of its
 *                               condition, expr_vv_sim of its arms and the
 *                               compile-state shape of their lowering
 *   compile_ifexp_word_vv_sim — its word-typed instance
 *
 * Helpers: compile_expr_ifexp, compile_expr_ifexp_states,
 * eval_expr_ifexp_cases, frag_exec_assign, ifexp_arm_outcome,
 * expr_post_ifexp, vv_post_of_expr_post.
 *)

Theory exprSimIfExp
Ancestors
  exprBopSimProps
  exprSimUnwrapProps exprSimMemorySource
  exprSimProps
  exprSimDefs exprSimVVFrame exprSimSource exprSimHypsDefs
  stmtSimProps gasContext gasOutcome gasSummary gasSummaryCompose gasExemptCert
  fragGasPath fragGasMode fragGasSeq vyperStatePreservation
  loweringPosts typedMemoryCopy exprSimTypedAlloc
  list rich_list finite_map marker exprSimHyps exprSimIfExpCompat exprSimLayoutTransport
  fragExec  exprSimOps exprSimUnwrap freshWrites exprBopLowering loweringSlice
  vyperEvalExprPreservesScopesDom exprLowering emitHelperProps
  exprLoweringProps compileEnv context vyperAST vyperInterpreter vyperState
  vyperValue valueEncoding venomExecSemantics venomExecProofs venomInst
  venomState exprSimLiteralBuffer words integer_word vfmConstants valueEncodingProps
  valueTypingMemoryProps copyFwdEquiv allocaRemapDefs valueEncodingProofs
Libs
  pairLib intLib

Theorem compile_ifexp_arm_unwrap[local]:
  !cenv rt at vv.
    is_word_type rt \/ same_memory_layout cenv at rt ==>
    compile_ifexp_arm cenv rt at vv = unwrap_value cenv vv
Proof
  simp[compile_ifexp_arm_def]
QED

Theorem ifexp_layout_refl[local]:
  (!t. punnable cenv t t) /\
  (!ts. punnable_list cenv ts ts)
Proof
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops type_induction) >>
  simp[punnable_def]
QED

Theorem ifexp_copy_types:
  !cenv rt at.
    (at = rt \/
     is_bytestring_type rt /\ is_bytestring_type at /\ arg_type_fits at rt \/
     same_memory_layout cenv at rt) /\
    ~is_word_type rt /\ ~same_memory_layout cenv at rt ==>
    is_bytestring_type rt /\ is_bytestring_type at
Proof
  rpt strip_tac >> gvs[same_memory_layout_def, ifexp_layout_refl]
QED

(* Low-level bytestring copy interface, kept below the operator layer. *)
Theorem ifexp_round_no_wrap[local]:
  !len. 32 + 32 * word_size len < dimword (:256) ==>
    len + 31 < dimword (:256)
Proof
  rpt gen_tac >> rewrite_tac[word_size_def] >> strip_tac >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `len + 31` strip_assume_tac) >>
  `(len + 31) MOD 32 < 32` by simp[] >>
  gvs[] >> intLib.ARITH_TAC
QED

Theorem ifexp_round_size[local]:
  !len. 32 + 32 * word_size len < dimword (:256) ==>
    ((((n2w len:bytes32) + 31w) && i2w (- &32)) + 32w =
     n2w (32 + 32 * word_size len))
Proof
  rpt strip_tac >> drule ifexp_round_no_wrap >> strip_tac >>
  rewrite_tac[exprSimPropsTheory.buffer_round_mask, word_add_n2w] >>
  `n2w (len + 31):bytes32 >>> 5 = n2w ((len + 31) DIV 32)` by
    (simp[GSYM n2w_DIV]) >>
  simp[word_size_def, word_lsl_n2w, word_add_n2w] >>
  AP_TERM_TAC >> decide_tac
QED

Theorem ifexp_emit_mcopy_run[local]:
  !sa sb dst src sz d w n s.
    emit_void MCOPY [dst; src; sz] sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
    eval_operand sz s = SOME n ==>
    run_inst_seq (emitted_insts sa sb) s =
      OK (mcopy (w2n d) (w2n w) (w2n n) s)
Proof
  rpt strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id MCOPY [dst; src; sz] []) s =
     OK (mcopy (w2n d) (w2n w) (w2n n) s)` by
    simp[step_inst_base_def] >>
  simp[run_inst_seq_def]
QED

Theorem ifexp_copy_len_shape[local]:
  !src out sa sb.
    compile_bytestring_copy_len src sa = (out,sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var + 4 /\
    sb.cs_next_id = sa.cs_next_id + 4
Proof
  rpt strip_tac >>
  gvs[compile_bytestring_copy_len_def, emitHelperTheory.emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp[same_blocks_def, emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem ifexp_copy_len_run[local]:
  !src out sa sb s w len.
    compile_bytestring_copy_len src sa = (out,sb) /\
    eval_operand src s = SOME w /\ mload (w2n w) s = n2w len /\
    32 + 32 * word_size len < dimword (:256) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      eval_operand out q = SOME (n2w (32 + 32 * word_size len)) /\
      (q with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  rpt strip_tac >>
  gvs[compile_bytestring_copy_len_def, emitHelperTheory.emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  drule_then assume_tac step_MLOAD >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, run_inst_seq_def] >>
  qmatch_goalsub_abbrev_tac `step_inst_base (mk_inst aid ADD ops [v1]) s1` >>
  `step_inst_base (mk_inst aid ADD ops [v1]) s1 =
     OK (update_var v1 ((n2w len:bytes32) + 31w) s1)` by
    (simp[Abbr `ops`] >> irule step_ADD >> simp[Abbr `s1`, eval_operand_def,
                           lookup_var_update_var]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `step_inst_base (mk_inst bid AND bops [v2]) s2` >>
  `step_inst_base (mk_inst bid AND bops [v2]) s2 =
     OK (update_var v2 (((n2w len:bytes32) + 31w) && i2w (- &32)) s2)` by
    (qunabbrev_tac `bops` >> irule step_AND >> simp[Abbr `s2`, eval_operand_def,
                           lookup_var_update_var]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `step_inst_base (mk_inst cid ADD cops [v3]) s3` >>
  `step_inst_base (mk_inst cid ADD cops [v3]) s3 =
     OK (update_var v3 ((((n2w len:bytes32) + 31w) && i2w (- &32)) + 32w) s3)` by
    (simp[Abbr `cops`] >> irule step_ADD >> simp[Abbr `s3`, eval_operand_def,
                           lookup_var_update_var]) >>
  simp[] >> conj_tac
  >- (qspec_then `len` mp_tac ifexp_round_size >>
      simp[eval_operand_def, lookup_var_update_var]) >>
  simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, update_var_def] >>
  rpt strip_tac >>
  gvs[not_fresh_at_def, Abbr `v1`, Abbr `v2`, Abbr `v3`,
      ASCIInumbersTheory.toString_11, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem ifexp_store_bytestring_run[local]:
  !src dst sa sb s w d len.
    compile_store_bytestring src dst sa = ((),sb) /\
    eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    mload (w2n w) s = n2w len /\
    32 + 32 * word_size len < dimword (:256) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      q.vs_memory = (mcopy (w2n d) (w2n w) (32 + 32 * word_size len) s).vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_store_bytestring_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `compile_bytestring_copy_len src sa = (out,mid)` >>
  drule_all ifexp_copy_len_run >> strip_tac >>
  drule ifexp_copy_len_shape >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> simp[]) >>
  `q.vs_memory = s.vs_memory` by
    (qpat_x_assum `q with vs_vars := _ = s`
       (mp_tac o AP_TERM ``\z. z.vs_memory``) >> simp[]) >>
  `q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|> = s` by
    (qpat_assum `q with vs_vars := _ = s`
       (mp_tac o AP_TERM ``\z. z with vs_memory := s.vs_memory``) >> simp[]) >>
  `eval_operand src q = SOME w` by
    (`eval_operand src q = eval_operand src s` by
       (irule literal_operand_frame >> simp[] >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  `eval_operand dst q = SOME d` by
    (`eval_operand dst q = eval_operand dst s` by
       (irule literal_operand_frame >> simp[] >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  drule_all ifexp_emit_mcopy_run >> strip_tac >>
  qexists_tac `mcopy (w2n d) (w2n w) (32 + 32 * word_size len) q` >>
  conj_tac
  >- (asm_rewrite_tac[] >>
      qpat_assum `run_inst_seq (emitted_insts sa mid) s = OK q`
        (mp_then Any mp_tac run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts mid sb` mp_tac) >> gvs[]) >>
  simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  fs[lookup_var_def]
QED

Theorem ifexp_bytes_header[local]:
  !cap bs src s.
    val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) src s.vs_memory ==>
    mload src s = n2w (LENGTH bs)
Proof
  simp[valueEncodingTheory.val_in_memory_def, mem_word_at_eq_mload]
QED

Theorem ifexp_string_header[local]:
  !cap str src s.
    val_in_memory (BaseTV (StringT cap)) (StringV str) src s.vs_memory ==>
    mload src s = n2w (LENGTH str)
Proof
  simp[valueEncodingTheory.val_in_memory_def, mem_word_at_eq_mload]
QED

Theorem ifexp_typed_bytestring_header[local]:
  !tenv ty tv v p s.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ val_in_memory tv v p s.vs_memory ==>
    ?len. mload p s = n2w len /\
      val_store_size tv v = 32 + 32 * word_size len
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >>
      gvs[is_bytestring_type_def, vyperValueTheory.evaluate_type_def] >>
      Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
      drule ifexp_bytes_header >> strip_tac >>
      qexists_tac `LENGTH l` >> simp[exprSimPropsTheory.val_store_size_def]) >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  drule ifexp_string_header >> strip_tac >>
  qexists_tac `LENGTH s'` >> simp[exprSimPropsTheory.val_store_size_def]
QED

Theorem ifexp_copy_source_bounds:
  !cx ty tv v op s.
    is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v /\ expr_val_rel cx ty v op s ==>
    ?w len. eval_operand op s = SOME w /\
      val_in_memory tv v (w2n w) s.vs_memory /\
      mload (w2n w) s = n2w len /\
      val_store_size tv v = 32 + 32 * word_size len /\
      32 + 32 * word_size len <= type_memory_size tv
Proof
  rpt strip_tac >>
  `~is_word_type ty` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  gvs[expr_val_rel_def] >>
  drule_all ifexp_typed_bytestring_header >> strip_tac >>
  drule value_has_type_memory_wf >> strip_tac >>
  drule val_store_size_le >> strip_tac >>
  qexists_tac `len` >> simp[] >> decide_tac
QED

Theorem ifexp_vv_at_alloc_frame[local]:
  vv_at cenv cx ty sa sb es raw vv s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region cenv es.scopes q n b sz <=>
            local_region cenv es.scopes s n b sz) /\
  sb.cs_next_id <= sm.cs_next_id ==>
  vv_at cenv cx ty sa sm es raw vv q
Proof
  Cases_on `vv` >>
  simp[vv_at_def, vv_operand_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
        metis_tac[])
  >>~- ([`local_region cenv es.scopes s n b sz`],
        disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[])
QED

Theorem ifexp_vv_own_alloc_frame[local]:
  vv_own cenv cx ty sa sb es raw vv s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region cenv es.scopes q n b sz <=>
            local_region cenv es.scopes s n b sz) /\
  sb.cs_next_id <= sm.cs_next_id ==>
  vv_own cenv cx ty sa sm es raw vv q
Proof
  Cases_on `vv` >>
  simp[vv_own_def, vv_operand_def, expr_val_own_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
        metis_tac[])
QED

Theorem ifexp_alloc_local_regions[local]:
  !ctx func cenv cx es sa s q.
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) ==>
    !n b sz. local_region cenv es.scopes q n b sz <=>
             local_region cenv es.scopes s n b sz
Proof
  rpt strip_tac >> eq_tac >> strip_tac
  >- (irule local_region_frame >>
      conj_tac
      >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
      qexistsl_tac [`sa`, `es.scopes`, `q`] >> simp[]) >>
  irule local_region_frame_fwd >>
  qexistsl_tac [`s`, `sa`, `es.scopes`] >> simp[]
QED

Theorem ifexp_bytestring_adapter_parts:
  !cenv t arm_ty vv sa op sb.
    ~is_word_type t /\ ~same_memory_layout cenv arm_ty t /\
    is_bytestring_type t /\ compile_ifexp_arm cenv t arm_ty vv sa = (op,sb) ==>
    ?buf sm src sn.
      compile_alloc_buffer (type_memory_bytes cenv t) sa = (buf,sm) /\
      unwrap_value cenv vv sm = (src,sn) /\
      compile_store_bytestring src buf.buf_operand sn = ((),sb) /\
      op = buf.buf_operand
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_ifexp_arm_def, compile_store_memory_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

(* Aggregate adapters copy from the physical arm layout into the annotation. *)
Theorem ifexp_zero_source_fits[local]:
  (!sty dty. arg_type_fits sty dty ==>
    !tenv tv. evaluate_type tenv sty = SOME tv /\
      type_memory_size tv = 0 ==> sty = dty) /\
  (!stys dtys. arg_types_fit stys dtys ==>
    !tenv tvs. OPT_MMAP (evaluate_type tenv) stys = SOME tvs /\
      type_memory_size_list tvs = 0 ==> stys = dtys)
Proof
  ho_match_mp_tac vyperTypeSystemTheory.arg_type_fits_ind >>
  simp[vyperTypeSystemTheory.arg_type_fits_def] >>
  rpt strip_tac >>
  gvs[evaluate_type_def, evaluate_types_OPT_MMAP, type_memory_size_def,
      AllCaseEqs()] >> metis_tac[]
QED

Theorem ifexp_widened_source_positive[local]:
  type_widens_to tenv sty dty /\ sty <> dty /\
  evaluate_type tenv sty = SOME stv ==>
  0 < type_memory_size stv
Proof
  simp[vyperTypeSystemTheory.type_widens_to_def] >> strip_tac >>
  spose_not_then assume_tac >>
  `type_memory_size stv = 0` by decide_tac >>
  metis_tac[ifexp_zero_source_fits]
QED

Theorem ifexp_physical_source_positive[local]:
  expr_body_pre cenv cx env e es /\
  post_value_type cenv e <> expr_type e /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME stv ==>
  0 < type_memory_size stv
Proof
  strip_tac >> irule ifexp_widened_source_positive >>
  qexistsl_tac [`expr_type e`, `post_value_type cenv e`, `get_tenv cx`] >>
  simp[] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[expr_body_pre_def] >>
  drule_all post_value_type_widens >> simp[]
QED

Theorem ifexp_aggregate_footprint[local]:
  !tenv t tv v.
    evaluate_type tenv t = SOME tv /\ ~is_bytestring_type t ==>
    val_footprint tv v = type_memory_size tv
Proof
  rpt gen_tac >> Cases_on `t` >>
  simp[evaluate_type_def, is_bytestring_type_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), is_bytestring_type_def] >>
  Cases_on `v` >> simp[val_footprint_def]
QED

Theorem ifexp_aggregate_source_region[local]:
  expr_val_at cenv cx ty origin sa es v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  eval_operand src s = SOME w ==>
  type_memory_size tv = 0 \/
  (?aid b sz. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    b <= w2n w /\ w2n w + type_memory_size tv <= b + sz) \/
  (?n b sz. local_region cenv es.scopes s n b sz /\
    b <= w2n w /\ w2n w + type_memory_size tv <= b + sz)
Proof
  strip_tac >>
  `val_footprint tv v = type_memory_size tv` by
    metis_tac[ifexp_aggregate_footprint] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ifexp_typed_adapter_parts[local]:
  ~is_word_type t /\ ~same_memory_layout cenv arm_ty t /\
  ~is_bytestring_type t /\ arm_ty <> t /\
  compile_ifexp_arm cenv t arm_ty vv sa = (op,sb) ==>
  ?buf sm src sn.
    compile_alloc_buffer (type_memory_bytes cenv t) sa = (buf,sm) /\
    unwrap_value cenv vv sm = (src,sn) /\
    compile_store_memory_typed cenv buf.buf_operand t src arm_ty sn = ((),sb) /\
    op = buf.buf_operand
Proof
  strip_tac >>
  gvs[compile_ifexp_arm_def, compile_store_memory_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem ifexp_typed_alloc_source[local]:
  compile_alloc_buffer (type_memory_bytes cenv dty) sa = (buf,sm) /\
  compile_store_memory_typed cenv buf.buf_operand dty src sty sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  type_widens_to (get_tenv cx) sty dty /\ sty <> dty /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size dtv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf dtv v /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx sty origin sa es v src s /\
  eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw) s.vs_memory ==>
  frag_exec ctx sa sb (\z. z = s)
    (\u. ?w. stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      w2n w + type_memory_size dtv < dimword (:256) /\
      val_in_memory dtv v (w2n w) u.vs_memory /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size dtv) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!off len. off + len <= w2n w \/ w2n w + type_memory_size dtv <= off ==>
        mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
      (!name b len. local_region cenv es.scopes s name b len ==>
        regions_disjoint (w2n w) (type_memory_size dtv) b len)) R
Proof
  strip_tac >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (drule_all expr_val_at_bound >>
     `val_footprint stv v = type_memory_size stv` by
       metis_tac[ifexp_aggregate_footprint] >> simp[]) >>
  `0 < type_memory_size stv` by
    (drule_all ifexp_widened_source_positive >> simp[]) >>
  drule_all ifexp_aggregate_source_region >> strip_tac >> gvs[] >>
  `val_wf stv v` by gvs[expr_val_at_def] >>
  irule (SRULE [arithmeticTheory.ADD_COMM] compile_return_normalize_framed_frag) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* Restore the expression frame after a fresh typed normalization. *)
Theorem ifexp_typed_copy_post[local]:
  expr_post ctx func ce cx e es origin sa s0 es' v src r /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  origin.cs_next_var <= sa.cs_next_var /\
  origin.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id < sb.cs_next_id /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\
  stmt_state_rel ctx func ce cx es' u /\ eval_operand op u = SOME w /\
  val_in_memory dtv v (w2n w) u.vs_memory /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size dtv) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x r) /\
  (!aid entry. FLOOKUP r.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!off len. off + len <= w2n w \/ w2n w + type_memory_size dtv <= off ==>
    mem_bytes_at off len u.vs_memory = mem_bytes_at off len r.vs_memory) /\
  (!aid b len. aid < sa.cs_next_id /\ FLOOKUP r.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
  (!name b len. local_region ce es'.scopes r name b len ==>
    regions_disjoint (w2n w) (type_memory_size dtv) b len) ==>
  expr_post ctx func ce cx (IfExp dty c a b) es origin sb s0 es' v op u
Proof
  strip_tac >>
  `!name lb len. local_region ce es'.scopes u name lb len <=>
    local_region ce es'.scopes r name lb len` by
    (drule_all exprSimCopyTheory.copy_buffer_local_region_frame >> simp[]) >>
  `!name lb len. local_region ce es.scopes s0 name lb len ==>
    w2n w + type_memory_size dtv <= lb \/ lb + len <= w2n w` by
    (rpt strip_tac >>
     qpat_x_assum `!name b len. local_region ce es'.scopes r _ _ _ ==> _` mp_tac >>
     simp[regions_disjoint_def] >> disch_then irule >> qexists_tac `name` >>
     irule local_region_frame_fwd >> qexistsl_tac [`s0`, `origin`, `es.scopes`] >>
     gvs[expr_post_def]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_post_def] >> strip_tac >>
  simp[expr_post_def, expr_type_def, expr_val_rel_def] >>
  conj_tac >- suspend "value_at" >>
  conj_tac >- suspend "vars" >>
  conj_tac >- suspend "memory" >>
  suspend "locals"
QED

Resume ifexp_typed_copy_post[value_at]:
  markerLib.RESUME_TAC >> simp[expr_val_at_def] >>
  disj1_tac >> qexistsl_tac [`sa.cs_next_id`, `w2n w`, `type_memory_size dtv`] >>
  simp[] >> conj_tac >- metis_tac[val_footprint_le] >>
  rpt strip_tac >> gvs[regions_disjoint_def] >> metis_tac[]
QED
Resume ifexp_typed_copy_post[vars]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `not_fresh_at sa x` by (irule not_fresh_at_mono >> qexists_tac `origin` >> simp[]) >>
  metis_tac[]
QED
Resume ifexp_typed_copy_post[memory]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `FLOOKUP r.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
  `regions_disjoint (w2n w) (type_memory_size dtv) off sz` by
    (qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `aid` >> simp[] >> decide_tac) >>
  gvs[regions_disjoint_def] >> metis_tac[]
QED
Resume ifexp_typed_copy_post[locals]:
  markerLib.RESUME_TAC >> irule exprSimCopyTheory.copy_buffer_locals_kept_frame >>
  qexistsl_tac [`w2n w`, `r`, `type_memory_size dtv`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ u.vs_memory = _` irule >> decide_tac) >>
  simp[]
QED
Finalise ifexp_typed_copy_post[local]

Theorem ifexp_typed_normalize_post[local]:
  compile_alloc_buffer (type_memory_bytes ce dty) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  sty = post_value_type ce e /\
  type_widens_to (get_tenv cx) sty dty /\ sty <> dty /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_size dtv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf dtv v /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) ==>
  frag_exec ctx sa sb
    (\r. expr_post ctx func ce cx e es origin sa s0 es' v src r)
    (\u. expr_post ctx func ce cx (IfExp dty c a b) es origin sb s0 es' v buf.buf_operand u) R
Proof
  strip_tac >> irule frag_exec_pointwise >> qx_gen_tac `r` >> strip_tac >>
  `stmt_state_rel ctx func ce cx es' r /\
   expr_val_at ce cx sty origin sa es' v src r /\
   value_has_type stv v /\
   ?sw. eval_operand src r = SOME sw /\ val_in_memory stv v (w2n sw) r.vs_memory` by
    gvs[expr_post_def, expr_val_rel_def] >>
  drule_all ifexp_typed_alloc_source >>
  disch_then (qspec_then `R` (mp_tac o MATCH_MP frag_exec_weaken)) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  irule ifexp_typed_copy_post >>
  simp[] >> qexistsl_tac [`e`, `r`, `sa`, `src`] >> simp[] >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  `ci_mono sm sb` by
    (qspecl_then [`ce`, `buf.buf_operand`, `dty`, `src`, `sty`, `sm`] mp_tac
       (cj 1 ci_mono_typed_memory_family) >> simp[]) >>
  gvs[ci_mono_def] >>
  `sa.cs_next_id < sb.cs_next_id` by decide_tac >> metis_tac[]
QED

Theorem ifexp_mcopy_window[local]:
  !dst src n s k. k <= n ==>
    mem_bytes_at dst k (mcopy dst src n s).vs_memory =
    mem_bytes_at src k s.vs_memory
Proof
  rpt strip_tac >> irule LIST_EQ >>
  simp_tac bool_ss [LENGTH_mem_bytes_at_proof] >> rpt strip_tac >>
  asm_simp_tac bool_ss [EL_mem_bytes_at, GSYM mem_byte_at_def] >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
  irule (SRULE [LET_THM] mcopy_establishes_equiv) >> decide_tac
QED

Theorem ifexp_mcopy_exterior[local]:
  !dst src n s a k. a + k <= dst \/ dst + n <= a ==>
    mem_bytes_at a k (mcopy dst src n s).vs_memory =
    mem_bytes_at a k s.vs_memory
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  simp[EL_mem_bytes_at, GSYM mem_byte_at_def] >>
  irule (SRULE [LET_THM] mcopy_preserves_disjoint) >>
  qexists_tac `k` >> simp[]
QED

Theorem ifexp_store_bytestring_encoding[local]:
  !src dst sa sb s w d len tv v.
    compile_store_bytestring src dst sa = ((),sb) /\
    eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    mload (w2n w) s = n2w len /\
    val_in_memory tv v (w2n w) s.vs_memory /\ val_wf tv v /\
    val_store_size tv v = 32 + 32 * word_size len /\
    type_memory_size tv < dimword (:256) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      LENGTH s.vs_memory <= LENGTH q.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  rpt strip_tac >>
  `32 + 32 * word_size len <= type_memory_size tv` by
    metis_tac[val_store_size_le] >>
  `val_footprint tv v <= 32 + 32 * word_size len` by
    metis_tac[val_footprint_le_store_size] >>
  `32 + 32 * word_size len < dimword (:256)` by decide_tac >>
  drule_all ifexp_store_bytestring_run >> strip_tac >>
  qexists_tac `q` >> simp[] >> conj_tac
  >- (irule exprSimMemoryTransportTheory.val_in_memory_relocate_footprint >>
      simp[] >> qexistsl_tac [`s.vs_memory`, `w2n w`] >> simp[] >>
      sym_tac >> irule ifexp_mcopy_window >> decide_tac) >>
  conj_tac
  >- simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity,
          arithmeticTheory.MAX_DEF] >>
  rpt strip_tac >> irule ifexp_mcopy_exterior >> decide_tac
QED

Theorem ifexp_immutable_destination_sep[local]:
  !ctx func cenv cx es s inst dst sz.
    stmt_state_rel ctx func cenv cx es s /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (dst,sz) ==>
    cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) dst sz
Proof
  rpt strip_tac >> fs[stmt_state_rel_def, immutable_alloca_sep_def] >>
  first_x_assum drule_all >> strip_tac >> metis_tac[]
QED

Theorem ifexp_bytestring_store_state[local]:
  !ctx func cenv cx es src dst sa sb s w d len tv v inst.
    compile_store_bytestring src dst sa = ((),sb) /\
    eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    mload (w2n w) s = n2w len /\
    val_in_memory tv v (w2n w) s.vs_memory /\ val_wf tv v /\
    val_store_size tv v = 32 + 32 * word_size len /\
    type_memory_size tv < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv) /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      b + sz <= w2n d \/ w2n d + type_memory_size tv <= b) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      stmt_state_rel ctx func cenv cx es q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  rpt strip_tac >> drule_all ifexp_store_bytestring_encoding >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es q` by
    (irule literal_state_memory_frame >> qexists_tac `s` >> simp[] >>
     rpt conj_tac >> rpt strip_tac
     >~ [`ImmutableLoc _`]
     >- (qpat_x_assum `!a k. _ ==> mem_bytes_at _ _ _ = _` irule >>
         drule_all ifexp_immutable_destination_sep >>
         simp[regions_disjoint_def])
     >~ [`local_region _ _ _ _ _ _`]
     >- (qpat_x_assum `!a k. _ ==> mem_bytes_at _ _ _ = _` irule >> metis_tac[]) >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _` irule >>
     gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qexists_tac `q` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!a k. _ ==> mem_bytes_at _ _ _ = _` irule >> decide_tac
QED

Theorem ifexp_destination_at[local]:
  !cenv cx ty tv v sa sb es op s w aid.
    evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
    eval_operand op s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
      w2n w + type_memory_size tv <= b \/ b + sz <= w2n w) ==>
    expr_val_at cenv cx ty sa sb es v op s
Proof
  rpt strip_tac >> simp[expr_val_at_def] >> rpt strip_tac >> gvs[] >>
  disj1_tac >>
  qexistsl_tac [`aid`, `w2n w`, `type_memory_size tv`] >> simp[] >>
  conj_tac >- (drule val_store_size_le >>
    qspecl_then [`tv`, `v`] mp_tac val_footprint_le_store_size >> decide_tac) >>
  metis_tac[]
QED

Theorem ifexp_alloc_preserves_post:
  !ctx func cenv cx e es origin sa sm buf sz s0 es' raw vv s.
    compile_alloc_buffer sz sa = (buf,sm) /\
    vv_post ctx func cenv cx e es origin sa s0 es' raw vv s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    origin.cs_next_var <= sa.cs_next_var /\ sz < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sa x) ==>
    ?q w. run_inst_seq (emitted_insts sa sm) s = OK q /\
      vv_post ctx func cenv cx e es origin sm s0 es' raw vv q /\
      eval_operand buf.buf_operand q = SOME w /\
      FLOOKUP q.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      q.vs_memory = s.vs_memory
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[vv_post_def] >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  `contract_storage t = contract_storage s /\
   contract_transient t = contract_transient s` by
    metis_tac[exprSimAllocTheory.alloc_buffer_storage] >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >> gvs[eval_operand_def]) >>
  `vv_holds cenv cx (post_value_type cenv e) raw vv es' t` by
    (fs[vv_post_def] >> Cases_on `vv` >>
     gvs[vv_holds_def, vv_operand_def, expr_val_rel_def, storage_holds_def] >>
     BasicProvers.every_case_tac >> gvs[] >> metis_tac[immutable_holds_memory_cong]) >>
  `!n b len. local_region cenv es'.scopes t n b len <=>
             local_region cenv es'.scopes s n b len` by
    (drule_all ifexp_alloc_local_regions >> simp[]) >>
  `vv_at cenv cx (post_value_type cenv e) origin sm es' raw vv t` by
    (irule ifexp_vv_at_alloc_frame >> qexistsl_tac [`s`, `sa`] >>
     fs[vv_post_def] >> decide_tac) >>
  `post_value_type cenv e <> expr_type e ==>
   vv_own cenv cx (post_value_type cenv e) origin sm es' raw vv t` by
    (strip_tac >> irule ifexp_vv_own_alloc_frame >>
     qexistsl_tac [`s`, `sa`] >> fs[vv_post_def] >> decide_tac) >>
  qexistsl_tac [`t`, `w`] >> simp[vv_post_def] >>
  fs[vv_post_def] >> rpt conj_tac
  >- (strip_tac >> fs[] >> Cases_on `vv` >> gvs[vv_operand_def])
  >- (rpt strip_tac >>
      `not_fresh_at sa x` by metis_tac[not_fresh_at_mono] >> metis_tac[])
  >- metis_tac[] >>
  irule locals_kept_mem_tail >> qexists_tac `s` >> simp[]
QED

(* Rebase variables without changing allocation ownership. *)
Theorem ifexp_expr_val_at_start_var[local,simp]:
  expr_val_at ce cx ty (sa with cs_next_var := n) sb es v op s <=>
  expr_val_at ce cx ty sa sb es v op s
Proof
  simp[expr_val_at_def]
QED

Theorem ifexp_vv_at_start_var[local,simp]:
  vv_at ce cx ty (sa with cs_next_var := n) sb es tv vv s <=>
  vv_at ce cx ty sa sb es tv vv s
Proof
  Cases_on `vv` >> simp[vv_at_def]
QED

Theorem ifexp_vv_own_start_var[local,simp]:
  vv_own ce cx ty (sa with cs_next_var := n) sb es tv vv s <=>
  vv_own ce cx ty sa sb es tv vv s
Proof
  Cases_on `vv` >> simp[vv_own_def, expr_val_own_def]
QED

Theorem ifexp_vv_post_rebase[local]:
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r ==>
  vv_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    sm r es' tv vv r
Proof
  simp[vv_post_def]
QED

Theorem ifexp_expr_post_rebased_operand[local]:
  expr_post ctx func ce cx e es (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\ not_fresh_at sm x /\
  eval_operand (Var x) r = SOME w ==>
  eval_operand (Var x) s = SOME w
Proof
  simp[eval_operand_def, expr_post_def, not_fresh_at_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem ifexp_rebased_store_run[local]:
  compile_store_bytestring src (Var x) sn = ((),sb) /\
  expr_post ctx func ce cx e es' (origin with cs_next_var := sm.cs_next_var)
    sn r es' v src s /\
  not_fresh_at sm x /\ eval_operand (Var x) r = SOME d /\
  sm.cs_next_var <= sn.cs_next_var /\
  (!z. src = Var z ==> not_fresh_at sn z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv) /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n d \/ w2n d + type_memory_size tv <= b) ==>
  ?q. run_inst_seq (emitted_insts sn sb) s = OK q /\
    val_in_memory tv v (w2n d) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    eval_operand (Var x) q = SOME d /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    locals_kept ce es' r q
Proof
  strip_tac >>
  `eval_operand (Var x) s = SOME d` by
    (drule_all ifexp_expr_post_rebased_operand >> simp[]) >>
  `!n b k. local_region ce es'.scopes s n b k ==>
    b + k <= w2n d \/ w2n d + type_memory_size tv <= b` by
    (rpt strip_tac >>
     `local_region ce es'.scopes r n b k` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `func` >>
            gvs[expr_post_def, stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sm`, `es'.scopes`, `s`] >>
        gvs[expr_post_def, not_fresh_at_def]) >> metis_tac[]) >>
  `!z. src = Var z \/ Var x = Var z ==> not_fresh_at sn z` by
    (rpt strip_tac >> gvs[] >> metis_tac[not_fresh_at_mono]) >>
  `expr_val_rel cx (expr_type e) v src s /\
   stmt_state_rel ctx func ce cx es' s` by gvs[expr_post_def] >>
  drule_all ifexp_copy_source_bounds >> strip_tac >>
  `val_wf tv v` by metis_tac[value_has_type_memory_wf] >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv)` by
    (fs[expr_post_def] >> metis_tac[]) >>
  drule_all ifexp_bytestring_store_state >> strip_tac >>
  `q.vs_allocas = s.vs_allocas` by
    (qpat_assum `q with <|vs_vars := _; vs_memory := _|> = s`
      (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  `locals_kept ce es' r q` by
    (irule locals_kept_regions_tail >> qexists_tac `s` >>
     reverse conj_tac >- gvs[expr_post_def] >>
     rpt strip_tac >> metis_tac[]) >>
  qexists_tac `q` >> simp[] >>
  gvs[expr_post_def, not_fresh_at_def, eval_operand_def] >>
  rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

Theorem ifexp_rebased_old_memory[local]:
  vv_post ctx func ce cx e es origin sm s0 es' raw vv r /\
  expr_post ctx func ce cx e es' (origin with cs_next_var := sm.cs_next_var)
    sn r es' v src s /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce origin /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  FLOOKUP s.vs_allocas dest_id = SOME (dst,cap) /\
  origin.cs_next_id <= dest_id /\
  (!a k. a + k <= dst \/ dst + cap <= a ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  !aid off sz.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < origin.cs_next_id /\
    (!n b k. local_region ce es.scopes s0 n b k ==>
      off + sz <= b \/ b + k <= off) ==>
    mem_bytes_at off sz q.vs_memory = mem_bytes_at off sz s0.vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `!n b k. local_region ce es'.scopes r n b k ==>
    off + sz <= b \/ b + k <= off` by
    (rpt strip_tac >>
     `local_region ce es.scopes s0 n b k` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `func` >>
            gvs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`origin`, `es'.scopes`, `r`] >>
        gvs[vv_post_def]) >> metis_tac[]) >>
  `FLOOKUP r.vs_allocas aid = SOME (off,sz)` by
    (fs[vv_post_def] >> metis_tac[]) >>
  `mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz r.vs_memory` by
    (fs[expr_post_def] >>
     qpat_x_assum `!aid off sz. _` irule >> simp[] >>
     conj_tac >- metis_tac[] >> qexists_tac `aid` >> simp[]) >>
  `mem_bytes_at off sz r.vs_memory = mem_bytes_at off sz s0.vs_memory` by
    (fs[vv_post_def] >> metis_tac[]) >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `off + sz <= dst \/ dst + cap <= off` by
    (fs[expr_post_def, stmt_state_rel_def,
        venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.allocas_non_overlapping_def,
        venomMemDefsTheory.regions_disjoint_def] >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _ /\ FLOOKUP s.vs_allocas a1 = _ /\ _ ==> _`
       (qspecl_then [`aid`, `dest_id`, `off`, `sz`, `dst`, `cap`] mp_tac) >>
     simp[] >> decide_tac) >>
  metis_tac[]
QED

Theorem ifexp_rebased_store_post_run[local]:
  compile_store_bytestring src (Var x) sn = ((),sb) /\
  vv_post ctx func ce cx e es origin sm s0 es' raw vv r /\
  expr_post ctx func ce cx e es' (origin with cs_next_var := sm.cs_next_var)
    sn r es' v src s /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce origin /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  origin.cs_next_var <= sm.cs_next_var /\
  origin.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id /\
  not_fresh_at sm x /\ eval_operand (Var x) r = SOME d /\
  sm.cs_next_var <= sn.cs_next_var /\
  (!z. src = Var z ==> not_fresh_at sn z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ type_memory_size tv < dimword (:256) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv) /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n d \/ w2n d + type_memory_size tv <= b) ==>
  ?q. run_inst_seq (emitted_insts sn sb) s = OK q /\
    expr_post ctx func ce cx e es origin sb s0 es' v (Var x) q
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx es' r` by fs[vv_post_def] >>
  drule_all ifexp_rebased_store_run >> strip_tac >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv)` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `!aid off sz.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < origin.cs_next_id /\
    (!n b k. local_region ce es.scopes s0 n b k ==>
      off + sz <= b \/ b + k <= off) ==>
    mem_bytes_at off sz q.vs_memory = mem_bytes_at off sz s0.vs_memory` by
    (drule ifexp_rebased_old_memory >> disch_then drule >>
     disch_then (qspecl_then [`q`, `w2n d`, `inst.inst_id`, `type_memory_size tv`] mp_tac) >>
     fs[arithmeticTheory.ADD_COMM] >> strip_tac >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!aid off sz. _` irule >> simp[] >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     qexists_tac `aid` >> simp[]) >>
  `val_wf tv v` by metis_tac[value_has_type_memory_wf] >>
  `!n b k. local_region ce es'.scopes q n b k ==>
    b + k <= w2n d \/ w2n d + type_memory_size tv <= b` by
    (rpt strip_tac >>
     `local_region ce es'.scopes r n b k` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `func` >>
            gvs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sm`, `es'.scopes`, `q`] >> simp[]) >> metis_tac[]) >>
  `expr_val_at ce cx (expr_type e) origin sb es' v (Var x) q` by
    (irule ifexp_destination_at >>
     qexistsl_tac [`inst.inst_id`, `tv`, `d`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!n b k. local_region ce es'.scopes q n b k ==> _` drule >>
     decide_tac) >>
  `~is_word_type (expr_type e)` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  `expr_val_rel cx (expr_type e) v (Var x) q` by
    simp[expr_val_rel_def] >>
  `locals_kept ce es s0 q` by
    (irule locals_kept_trans >> qexistsl_tac [`es'`, `origin`, `r`] >>
     fs[vv_post_def]) >>
  qexists_tac `q` >> simp[expr_post_def] >>
  fs[vv_post_def] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x'` by metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ifexp_expr_post_inst_idx[local,simp]:
  expr_post ctx func ce cx e es sa sb s0 es' v op (s with vs_inst_idx := n) <=>
  expr_post ctx func ce cx e es sa sb s0 es' v op s
Proof
  `!op. eval_operand op (s with vs_inst_idx := n) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[expr_post_def, stmt_state_rel_inst_idx, expr_val_rel_def,
       expr_val_at_def, expr_val_own_def, lookup_var_def, local_region_def]
QED

Theorem ifexp_store_bytestring_straight[local]:
  compile_store_bytestring src dst sa = ((),sb) ==>
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       IS_PREFIX_APPEND, venomInstTheory.mk_inst_def, is_terminator_def]
QED

Theorem ifexp_vv_post_inst_idx[local]:
  vv_post ctx func cenv cx e es sa sb s0 es' raw vv (s with vs_inst_idx := n) <=>
  vv_post ctx func cenv cx e es sa sb s0 es' raw vv s
Proof
  `!op. eval_operand op (s with vs_inst_idx := n) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  Cases_on `vv` >>
  simp[vv_post_def, stmt_state_rel_inst_idx, vv_holds_def, vv_at_def, vv_own_def,
       expr_val_rel_def, expr_val_at_def, expr_val_own_def, lookup_var_def,
       local_region_def, storage_holds_def, immutable_holds_def,
       venomStateTheory.contract_storage_def,
       venomStateTheory.contract_transient_def]
QED

Theorem ifexp_different_type_unwrap_pure[local]:
  !ce e ty sa vv sb.
    lowered_value_type ce e <> expr_type e /\
    ~is_word_type (expr_type e) /\
    ~is_word_type (lowered_value_type ce e) /\
    compile_expr ce ty e sa = (vv,sb) ==>
    ?op. unwrap_value ce vv = comp_return op
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, expr_type_def] >>
  rpt strip_tac
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once (cj 1 compile_expr_raw_def), compile_expr_body_def,
           compile_literal_vv_def, expr_type_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[] >> rpt strip_tac >> gvs[expr_type_def] >>
      simp[unwrap_value_def, base_ptr_def, is_word_type_def, expr_type_def,
           comp_return_def, lower_value_def, comp_bind_def,
           Once (cj 1 compile_expr_raw_def), compile_expr_body_def,
           compile_literal_vv_def] >> metis_tac[])
  >- suspend "bytes"
  >- suspend "concat"
  >- suspend "abi"
  >> suspend "call"
QED

Resume ifexp_different_type_unwrap_pure[bytes]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once (cj 1 compile_expr_raw_def), compile_expr_body_def,
       compile_literal_vv_def, expr_type_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >> gvs[expr_type_def] >>
  simp[unwrap_value_def, base_ptr_def, is_word_type_def, expr_type_def,
       comp_return_def, lower_value_def, comp_bind_def,
       Once (cj 1 compile_expr_raw_def), compile_expr_body_def,
       compile_literal_vv_def] >> metis_tac[]
QED
Resume ifexp_different_type_unwrap_pure[concat]:
  rename1 `Builtin _ (Concat cn) cargs` >>
  `~names_builtin (Concat cn) cargs` by
    (`!bt args. names_builtin bt args ==> !n. bt <> Concat n` suffices_by
       metis_tac[] >>
     ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  simp[unwrap_value_def, base_ptr_def] >> metis_tac[]
QED
Resume ifexp_different_type_unwrap_pure[abi]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once (cj 1 compile_expr_def), compile_expr_body_def, expr_type_def] >>
  simp[Once (cj 3 compile_expr_def), compile_type_builtin_dispatch_body_def] >>
  rpt IF_CASES_TAC >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[oneline as_ptr_val_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[oneline as_ptr_val_def, AllCaseEqs()] >>
  simp[unwrap_value_def, mk_ptr_def, comp_return_def] >> metis_tac[]
QED
Resume ifexp_different_type_unwrap_pure[call]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once (cj 1 compile_expr_def), compile_expr_body_def,
       expr_type_def, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt IF_CASES_TAC >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  simp[unwrap_value_def, base_ptr_def, comp_return_def] >> metis_tac[]
QED
Finalise ifexp_different_type_unwrap_pure[local]

Theorem ifexp_post_annotated[local]:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv) /\
  (~is_word_type (expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) /\
      ?tvp. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tvp) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  expr_post ctx func ce cx e es sa sb s0 es' v op s ==>
  expr_post ctx func ce cx (IfExp (expr_type e) c a b) es sa sb s0 es' v op s
Proof
  strip_tac >> Cases_on `post_value_type ce e = expr_type e`
  >- (gvs[expr_post_def, vyperASTTheory.expr_type_def] >> metis_tac[]) >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[post_value_type_word, post_value_type_bytestring] >>
  `post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> gvs[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >> gvs[post_value_type_def, vyperASTTheory.expr_type_def]) >>
  `lowered_value_type ce e <> expr_type e` by metis_tac[] >>
  gvs[] >> fs[expr_post_def, vyperASTTheory.expr_type_def] >>
  conj_tac >- (irule expr_val_rel_layout_transport >> goal_assum (drule_at Any) >> metis_tac[]) >>
  conj_tac >- (irule expr_val_at_layout_transport >> goal_assum (drule_at Any) >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ifexp_aggregate_source_kind[local]:
  !sty dty. arg_type_fits sty dty /\
    ~is_word_type dty /\ ~is_bytestring_type dty ==>
    ~is_word_type sty /\ ~is_bytestring_type sty
Proof
  Cases >> Cases >> simp[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def, is_bytestring_type_def] >>
  rename1 `arg_type_fits (BaseT sb) (BaseT db)` >>
  Cases_on `sb` >> Cases_on `db` >>
  simp[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def, is_bytestring_type_def] >>
  rename1 `arg_type_fits (BaseT (BytesT sb)) (BaseT (BytesT db))` >>
  Cases_on `sb` >> Cases_on `db` >>
  simp[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def, is_bytestring_type_def]
QED

(* What compile_expr emits for an IfExp. *)
Theorem compile_expr_ifexp:
  !cenv ty t c a b st vv st'.
    compile_expr cenv ty (IfExp t c a b) st = (vv, st') ==>
    ?cond_op s1 rv s2 tl s3 el s4 xl s5 s6 x6 s7 av s7a aop s8 s9 s10 x10 s11 bv s11a bop
     s12 s13 s14 x14.
      lower_value compile_expr cenv (BaseT BoolT) c st = (cond_op, s1) /\
      fresh_var s1 = (rv, s2) /\
      fresh_label "then" s2 = (tl, s3) /\ fresh_label "else" s3 = (el, s4) /\
      fresh_label "exit" s4 = (xl, s5) /\
      emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
      new_block tl s6 = (x6, s7) /\
      compile_expr cenv ty a s7 = (av, s7a) /\
      compile_ifexp_arm cenv t (lowered_value_type cenv a) av s7a = (aop, s8) /\
      emit_inst ASSIGN [aop] [rv] s8 = ((), s9) /\
      emit_inst JMP [Label xl] [] s9 = ((), s10) /\
      new_block el s10 = (x10, s11) /\
      compile_expr cenv ty b s11 = (bv, s11a) /\
      compile_ifexp_arm cenv t (lowered_value_type cenv b) bv s11a = (bop, s12) /\
      emit_inst ASSIGN [bop] [rv] s12 = ((), s13) /\
      emit_inst JMP [Label xl] [] s13 = ((), s14) /\
      new_block xl s14 = (x14, st') /\
      vv = if is_word_type t then StackValue t (Var rv)
           else LocatedValue t (mk_ptr (Var rv) LocMemory)
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def] >>
  rpt (pairarg_tac >> gvs[]) >> rw[] >> gvs[vyperASTTheory.expr_type_def]
QED

Theorem conditional_read_cases:
  !cx raw st res st'.
    (do r <- conditional_result cx raw; read_result cx r od) st = (res,st') ==>
    read_result cx raw st = (res,st') \/
    ?m. conditional_result cx raw st = (INR (Error (TypeError m)),st') /\
        res = INR (Error (TypeError m))
Proof
  rpt gen_tac >> Cases_on `raw` >>
  simp[conditional_result_def, read_result_def, bind_def, return_def, raise_def] >>
  rename1 `place_type_value cx p st` >>
  Cases_on `place_type_value cx p st` >> rename1 `place_type_value cx p st = (pr,pst)` >>
  drule place_type_value_state >> strip_tac >> gvs[] >>
  Cases_on `pr` >> simp[]
  >- (IF_CASES_TAC >> simp[read_result_def, bind_def, return_def] >>
      Cases_on `read_place cx p pst` >> rename1 `read_place cx p pst = (rr,ss)` >>
      Cases_on `rr` >> simp[read_result_def, return_def]) >>
  Cases_on `p` >>
  gvs[place_type_value_def, get_scopes_def, get_immutables_def,
      get_address_immutables_def, bind_def, return_def, lift_option_type_def,
      raise_def, AllCaseEqs()] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem eval_expr_ifexp_cases:
  !cx t c a b es res es'.
    (do result <- eval_expr cx (IfExp t c a b); read_result cx result od) es =
      (res, es') ==>
    (?exc. (do result <- eval_expr cx c; read_result cx result od) es =
             (INR exc, es') /\ res = INR exc) \/
    (?bv es1.
       (do result <- eval_expr cx c; read_result cx result od) es =
         (INL (BoolV bv), es1) /\
       (do result <- eval_expr cx (if bv then a else b);
           read_result cx result od) es1 = (res, es')) \/
    (?v es1 m.
       (do result <- eval_expr cx c; read_result cx result od) es = (INL v, es1) /\
       v <> BoolV T /\ v <> BoolV F /\
       res = INR (Error (TypeError m))) \/
    (?bv es1 raw es2 m.
       (do result <- eval_expr cx c; read_result cx result od) es =
         (INL (BoolV bv), es1) /\
       eval_expr cx (if bv then a else b) es1 = (INL raw, es2) /\
       conditional_result cx raw es2 = (INR (Error (TypeError m)), es') /\
       res = INR (Error (TypeError m)))
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, raise_def] >>
  Cases_on `eval_expr cx c es` >> rename1 `eval_expr cx c es = (cr,cs)` >>
  reverse (Cases_on `cr`)
  >- (simp[] >> rw[] >> simp[]) >>
  rename1 `eval_expr cx c es = (INL rawc,cs)` >>
  Cases_on `read_result cx rawc cs` >>
  rename1 `read_result cx rawc cs = (vr,vs)` >>
  reverse (Cases_on `vr`)
  >- (simp[] >> rw[] >> simp[]) >>
  rename1 `read_result cx rawc cs = (INL cv,vs)` >>
  Cases_on `cv` >> simp[raise_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `read_result cx rawc cs = (INL (BoolV bv),vs)` >>
  Cases_on `bv` >> gvs[] >>
  rename1 `eval_expr cx arm vs` >>
  Cases_on `eval_expr cx arm vs` >>
  rename1 `eval_expr cx arm vs = (ar,ast)` >>
  Cases_on `ar` >> gvs[] >>
  rename1 `read_result cx raw ast = (res,es')` >>
  `read_result cx raw ast = (res,es') \/
   ?m. conditional_result cx raw ast = (INR (Error (TypeError m)),es') /\
       res = INR (Error (TypeError m))` by
    (irule conditional_read_cases >> simp[bind_def]) >>
  metis_tac[]
QED

Theorem expr_post_ifexp:
  !func cenv cx t c a b e es es1 es' sa s1 sc sd sb s0 tt u cop aop
             rv v1 v lbl w k xl ctx.
    expr_post ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
    expr_post ctx func cenv cx e es1 sc sd (jump_to lbl tt) es' v aop u /\
    post_value_type cenv e = expr_type e /\
    expr_type e = t /\ eval_operand aop u = SOME w /\
    (!x. not_fresh_at sa x ==> x <> rv) /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
    sd.cs_next_id <= sb.cs_next_id ==>
    expr_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' v (Var rv)
      (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  rpt gen_tac >> simp[expr_post_def] >> strip_tac >> rfs[] >>
  qabbrev_tac `ss = jump_to xl (update_var rv w u with vs_inst_idx := k)` >>
  `ss.vs_memory = u.vs_memory /\ ss.vs_allocas = u.vs_allocas /\
   lookup_var rv ss = SOME w /\
   (!x. x <> rv ==> lookup_var x ss = lookup_var x u)` by
    simp[Abbr `ss`, jump_to_def, update_var_def, lookup_var_def,
         FLOOKUP_UPDATE] >>
  `!x. (jump_to lbl tt).vs_allocas = tt.vs_allocas /\
       lookup_var x (jump_to lbl tt) = lookup_var x tt /\
       (jump_to lbl tt).vs_memory = tt.vs_memory` by
    simp[jump_to_def, lookup_var_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es' ss` by
    (simp[Abbr `ss`, stmt_state_rel_jump_to, stmt_state_rel_inst_idx,
          update_var_def] >>
     irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> res_tac) >>
     `p <> rv` by metis_tac[] >>
     simp[lookup_var_def, FLOOKUP_UPDATE]) >>
  asm_rewrite_tac[] >> simp[vyperASTTheory.expr_type_def] >>
  conj_tac
  >- (qpat_x_assum `expr_val_rel cx (post_value_type cenv e) v aop u` mp_tac >>
      asm_rewrite_tac[] >>
      simp[expr_val_rel_def, eval_operand_def] >> strip_tac >> gvs[]) >>
  conj_tac
  >- (qpat_x_assum `expr_val_at cenv cx (post_value_type cenv e) sc sd es' v aop u` mp_tac >>
      asm_rewrite_tac[] >>
      simp[expr_val_at_def, eval_operand_def] >> rpt strip_tac >>
      first_x_assum drule_all >> strip_tac
      >- (disj1_tac >> qexists_tac `aid` >> first_assum (irule_at Any) >>
          simp[] >> fs[] >> rpt strip_tac >>
          `local_region cenv es'.scopes u n lb lsz` by
            (irule local_region_frame >> conj_tac
             >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
             qexistsl_tac [`sa`, `es'.scopes`, `ss`] >> simp[] >>
             rpt strip_tac >>
             `x <> rv` by metis_tac[] >>
             qpat_x_assum `!x. x <> rv ==> _` drule >> simp[]) >>
          qpat_x_assum `!n lb lsz. local_region _ _ u _ _ _ ==> _` drule >> simp[])
      >> TRY (disj2_tac >> disj2_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
      disj2_tac >> disj1_tac >> qexists_tac `n` >>
  `local_region cenv es'.scopes ss n b sz` by
    (qpat_x_assum `local_region _ _ u _ _ _` mp_tac >>
     simp[local_region_def] >> strip_tac >>
     `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> res_tac) >>
     `p <> rv` by metis_tac[] >> metis_tac[]) >>
  first_assum (irule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> rename1 `lookup_var z s0 = SOME w'` >>
      `z <> rv` by metis_tac[] >>
      `lookup_var z tt = SOME w'` by metis_tac[] >>
      `not_fresh_at sc z` by
        (qpat_x_assum `!x. not_fresh_at sa x ==> _` irule >> simp[]) >>
      `lookup_var z u = SOME w'` by
        (qpat_x_assum `!x w. not_fresh_at sc x /\ _ ==> _` irule >>
         simp[]) >>
      fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  (* the locals' memory: kept by c, then by e *)
  `locals_kept cenv es s0 ss` by
    (irule locals_kept_mem_tail >> qexists_tac `u` >>
     conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     irule locals_kept_trans >>
     qexistsl_tac [`es1`, `sa`, `jump_to lbl tt`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >~ [`lookup_var _ (jump_to _ _)`] >- metis_tac[] >>
     irule locals_kept_mem_tail >> qexists_tac `tt` >>
     simp[jump_to_def] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `locals_kept cenv es s0 ss` (fn th => rewrite_tac[th]) >>
  rpt strip_tac >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (fn th => rewrite_tac [GSYM th]) >>
  qpat_x_assum `!aid off sz. FLOOKUP (jump_to lbl tt).vs_allocas aid = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  asm_rewrite_tac[] >> disch_then irule >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n b sz'. local_region _ es.scopes s0 _ _ _ ==> _` irule >>
      qexists_tac `n` >>
      irule local_region_frame >>
      conj_tac >- (qexists_tac `func` >>
        gvs[stmt_state_rel_def, state_rel_def]) >>
      qexistsl_tac [`sa`, `es1.scopes`, `tt`] >> asm_rewrite_tac[] >>
      fs[local_region_def] >> metis_tac[])
  >- decide_tac >>
  qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = _ ==> _` irule >>
  first_assum ACCEPT_TAC
QED

(* An ASSIGN as a fragment. *)
Theorem frag_exec_assign:
  !ctx st st' src out P Q R.
    emit_inst ASSIGN [src] [out] st = ((), st') /\
    (!s. P s ==> ?w. eval_operand src s = SOME w /\
                     Q ((update_var out w s) with
                          vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  irule frag_exec_run_inst_seq >>
  `emitted_insts st st' = [mk_inst st.cs_next_id ASSIGN [src] [out]]` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[venomInstTheory.mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> disj1_tac >>
  simp[run_inst_seq_def, step_inst_base_def, exec_pure1_def, comp_bind_def,
       comp_return_def] >> gvs[]
QED

(* expr_post of an operand held by a variable, as vv_post of the value_vv
   compile_expr makes of the variable. *)
Theorem vv_post_of_expr_post:
  !func cenv cx e es sa sb s0 es' v rv s ctx.
    post_value_type cenv e = expr_type e /\
    expr_post ctx func cenv cx e es sa sb s0 es' v (Var rv) s ==>
    vv_post ctx func cenv cx e es sa sb s0 es' (Value v)
      (if is_word_type (expr_type e) then StackValue (expr_type e) (Var rv)
       else LocatedValue (expr_type e) (mk_ptr (Var rv) LocMemory)) s
Proof
  rw[expr_post_def, vv_post_def] >>
  gvs[vv_holds_def, vv_at_def, contextTheory.mk_ptr_def, read_result_def,
      return_def] >>
  fs[expr_val_rel_def, expr_val_at_def] >>
  rpt strip_tac >> res_tac >> gvs[] >> metis_tac[]
QED

Theorem ifexp_root_assign_zero_path[local]:
  emit_inst ASSIGN [op] [rv] sa = ((),sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ eval_operand op s = SOME w ==>
  gas_path ctx func s 0
    (OK ((update_var rv w s) with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ASSIGN [op] [rv]]` by
    metis_tac[emit_inst_extends] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id ASSIGN [op] [rv])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_edge ctx func s 0
    (OK ((update_var rv w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst sa.cs_next_id ASSIGN [op] [rv]`,
                        `u` |-> `update_var rv w s`]
       tuple_straight_line_edge) >>
     simp[venomInstTheory.mk_inst_def, is_terminator_def, step_inst_base_def,
          exec_pure1_def] >> metis_tac[]) >>
  `~((update_var rv w s) with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    simp[update_var_def] >>
  drule (cj 1 gas_path_rules) >> strip_tac >>
  gvs[GSYM arithmeticTheory.ADD1] >>
  qpat_x_assum `gas_path_edge _ _ _ _ _` mp_tac >>
  qpat_x_assum `!ctx fn. gas_path _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  metis_tac[cj 2 gas_path_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_root_eval_forced:
  eval_expr cx (IfExp t c a b) =
  vyperState$bind (vyperState$bind (eval_expr cx c) (read_result cx))
    (\v. if v = BoolV T then vyperState$bind (eval_expr cx a) (conditional_result cx)
         else if v = BoolV F then vyperState$bind (eval_expr cx b) (conditional_result cx)
         else raise (Error (TypeError "not BoolV")))
Proof
  simp[Once evaluate_def, switch_BoolV_def, vyperStateTheory.bind_assoc] >>
  simp[FUN_EQ_THM, vyperStateTheory.bind_def] >> gen_tac >>
  Cases_on `eval_expr cx c x` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `read_result cx captured st` >>
  Cases_on `read_result cx captured st` >> rename1 `_ = (forced,sf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >>
  simp[raise_def, vyperStateTheory.bind_def]
QED

Theorem ifexp_root_condition_admissible:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es ==>
  gas_admissible (vyperState$bind (eval_expr cx c) (read_result cx)) expr_res_ok es
Proof
  rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >>
  simp[ifexp_root_eval_forced, vyperStateTheory.bind_def] >>
  fs[expr_vv_res_ok_def, expr_res_ok_def] >> metis_tac[]
QED

Theorem ifexp_root_branch_admissible:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  (!tail. vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV sel),mid with gas_obs := tail)) ==>
  gas_admissible
    (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    expr_vv_res_ok (mid with gas_obs := [])
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!gs res ee. _` (qspec_then `xs ++ gs` mp_tac) >>
  simp[ifexp_root_eval_forced, vyperStateTheory.bind_def] >>
  Cases_on `sel` >> gvs[]
QED

Theorem ifexp_root_condition_bool:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gs) = (INL v,mid) ==>
  ?sel. v = BoolV sel
Proof
  strip_tac >>
  Cases_on `v = BoolV T` >- metis_tac[] >>
  Cases_on `v = BoolV F` >- metis_tac[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def, ifexp_root_eval_forced] >>
  disch_then (qspec_then `gs` mp_tac) >>
  simp[vyperStateTheory.bind_def, raise_def, expr_vv_res_ok_def]
QED

Theorem ifexp_root_condition_cert:
  gas_exempt_cert memory tops (ctx,func)
    (vyperState$ignore_bind
      (vyperState$bind (eval_expr cx c) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finalst) ==>
  gas_exempt_cert memory tops (ctx,func)
    (vyperState$ignore_bind (eval_expr cx (IfExp t c a b)) (return ()))
    (es,s0) marks (err,ee) (leaf,finalst)
Proof
  strip_tac >> rewrite_tac[ifexp_root_eval_forced] >>
  pure_once_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem ifexp_root_vv_post_of_expr_post_read[local]:
  post_value_type cenv e = expr_type e /\
  expr_post ctx func cenv cx e es sa sb s0 es' v (Var rv) s /\
  read_result cx tv es' = (INL v, es') ==>
  vv_post ctx func cenv cx e es sa sb s0 es' tv
    (if is_word_type (expr_type e) then StackValue (expr_type e) (Var rv)
     else LocatedValue (expr_type e) (mk_ptr (Var rv) LocMemory)) s
Proof
  rw[expr_post_def, vv_post_def] >>
  gvs[vv_holds_def, vv_at_def, contextTheory.mk_ptr_def] >>
  fs[expr_val_rel_def, expr_val_at_def] >>
  rpt strip_tac >> res_tac >> gvs[] >> metis_tac[]
QED

(* compile_expr_ifexp with what the two arms of compile_ifexp_vv_sim need
   of its states, from the compile-state shape of the operands' lowering. *)
Theorem ifexp_new_block_fields[local]:
  !lbl sa old sb.
    new_block lbl sa = (old, sb) ==>
    sb.cs_current_bb = lbl /\ sb.cs_current_insts = [] /\
    sb.cs_next_var = sa.cs_next_var /\ sb.cs_next_id = sa.cs_next_id
Proof
  metis_tac[new_block_props]
QED

Theorem compile_expr_ifexp_states:
  !cenv ty t c a b st vv st'.
    compile_expr cenv ty (IfExp t c a b) st = (vv, st') /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) ==>
    ?cond_op s1 rv tl el xl s5 s6 x6 s7 av s7a aop s8 s9 s10 x10 s11 bv s11a bop s12 s13
     s14 x14.
      lower_value compile_expr cenv (BaseT BoolT) c st = (cond_op, s1) /\
      emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
      new_block tl s6 = (x6, s7) /\
      compile_expr cenv ty a s7 = (av, s7a) /\
      compile_ifexp_arm cenv t (lowered_value_type cenv a) av s7a = (aop, s8) /\
      emit_inst ASSIGN [aop] [rv] s8 = ((), s9) /\
      emit_inst JMP [Label xl] [] s9 = ((), s10) /\
      new_block el s10 = (x10, s11) /\
      compile_expr cenv ty b s11 = (bv, s11a) /\
      compile_ifexp_arm cenv t (lowered_value_type cenv b) bv s11a = (bop, s12) /\
      emit_inst ASSIGN [bop] [rv] s12 = ((), s13) /\
      emit_inst JMP [Label xl] [] s13 = ((), s14) /\
      new_block xl s14 = (x14, st') /\
      vv = (if is_word_type t then StackValue t (Var rv)
            else LocatedValue t (mk_ptr (Var rv) LocMemory)) /\
      s5.cs_current_bb = s1.cs_current_bb /\
      s5.cs_current_insts = s1.cs_current_insts /\
      s7.cs_current_bb = tl /\ s11.cs_current_bb = el /\
      st'.cs_current_bb = xl /\ s7.cs_current_insts = [] /\
      s11.cs_current_insts = [] /\ st'.cs_current_insts = [] /\
      cs_extends st s1 /\ cs_extends s1 s5 /\ cs_extends s7 s8 /\
      cs_extends s7 s11 /\ cs_extends s11 s12 /\ cs_extends s11 st' /\
      cs_extends s1 st' /\
      st.cs_next_var <= s1.cs_next_var /\ st.cs_next_id <= s1.cs_next_id /\
      s1.cs_next_var <= s7.cs_next_var /\ s1.cs_next_id <= s7.cs_next_id /\
      s1.cs_next_var <= s11.cs_next_var /\ s1.cs_next_id <= s11.cs_next_id /\
      s8.cs_next_id <= st'.cs_next_id /\ s12.cs_next_id <= st'.cs_next_id /\
      !x. not_fresh_at st x ==> x <> rv
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_expr_ifexp >> strip_tac >>
  qpat_x_assum `!st sb op. lower_value _ _ (BaseT BoolT) c _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  imp_res_tac (CONJUNCT1 compile_expr_grows) >>
  qspecl_then [`cenv`, `t`, `lowered_value_type cenv a`, `av`, `s7a`]
    mp_tac ci_mono_compile_ifexp_arm >>
  qspecl_then [`cenv`, `t`, `lowered_value_type cenv b`, `bv`, `s11a`]
    mp_tac ci_mono_compile_ifexp_arm >>
  simp[ci_mono_def] >> rpt strip_tac >>
  `cs_extends s7 s8 /\ s7.cs_next_var <= s8.cs_next_var /\
   s7.cs_next_id <= s8.cs_next_id /\
   cs_extends s11 s12 /\ s11.cs_next_var <= s12.cs_next_var /\
   s11.cs_next_id <= s12.cs_next_id` by
    (metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  imp_res_tac fresh_label_props >> imp_res_tac emit_inst_extends >>
  `cs_extends s1 s2` by metis_tac[cs_extends_fresh_var] >>
  `cs_extends s2 s3 /\ cs_extends s3 s4 /\ cs_extends s4 s5` by
     metis_tac[cs_extends_fresh_label] >>
  `cs_extends s5 s6 /\ cs_extends s8 s9 /\ cs_extends s9 s10 /\
   cs_extends s12 s13 /\ cs_extends s13 s14` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s6 s7 /\ cs_extends s10 s11 /\ cs_extends s14 st'` by
    metis_tac[cs_extends_new_block] >>
  `Abbrev (rv = STRING #"%" (toString s1.cs_next_var)) /\
   s2.cs_next_var = s1.cs_next_var + 1 /\ s2.cs_next_id = s1.cs_next_id /\
   s2.cs_current_bb = s1.cs_current_bb /\
   s2.cs_current_insts = s1.cs_current_insts /\ s2.cs_blocks = s1.cs_blocks` by
    (qpat_x_assum `fresh_var s1 = _` mp_tac >>
     simp[fresh_var_def, markerTheory.Abbrev_def] >> strip_tac >> gvs[]) >>
  `!x. not_fresh_at st x ==> x <> rv` by
    (fs[markerTheory.Abbrev_def] >> rw[not_fresh_at_def] >>
     first_x_assum (qspec_then `s1.cs_next_var` mp_tac) >> simp[]) >>
  `s7.cs_next_var = s2.cs_next_var /\ s7.cs_next_id = s1.cs_next_id + 1 /\
   s11.cs_next_var = s10.cs_next_var /\ s11.cs_next_id = s10.cs_next_id /\
   st'.cs_next_var = s14.cs_next_var /\ st'.cs_next_id = s14.cs_next_id /\
   s7.cs_current_insts = [] /\ s11.cs_current_insts = [] /\
   st'.cs_current_insts = [] /\ s7.cs_current_bb = tl /\
   s11.cs_current_bb = el /\ st'.cs_current_bb = xl` by
    (imp_res_tac ifexp_new_block_fields >> simp[]) >>
  `cs_extends s1 s5 /\ cs_extends s7 s11 /\ cs_extends s11 st'` by
    metis_tac[cs_extends_trans] >>
  `cs_extends s1 st'` by metis_tac[cs_extends_trans] >>
  qexistsl_tac [`rv`, `s5`, `s6`, `x6`,
                `s7`, `av`, `s7a`, `aop`, `s8`, `s9`, `s10`, `x10`, `s11`, `bv`, `s11a`, `bop`, `s12`,
                `s13`, `s14`, `x14`] >>
  simp[] >>
  qpat_x_assum `!x. not_fresh_at st x ==> x <> rv` (qspec_then `rv` mp_tac) >>
  simp[]
QED

Theorem ifexp_root_code_layout:
  compile_expr cenv ty (IfExp t c a b) st = (vv,st') /\
  fn_has_code st st' func /\ local_ptrs_reserved cenv st /\
  (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id) /\
  (!e sa sb op. (e = a \/ e = b) /\ lower_value compile_expr cenv ty e sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id) ==>
  ?cop sc sj sn tl el xl rv se av sea aop sx sy sz.
    lower_value compile_expr cenv (BaseT BoolT) c st = (cop,sc) /\
    emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
    sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
    compile_expr cenv ty (if sel then a else b) se = (av,sea) /\
    compile_ifexp_arm cenv t (lowered_value_type cenv (if sel then a else b)) av sea = (aop,sx) /\
    emit_inst ASSIGN [aop] [rv] sx = ((),sy) /\
    emit_inst JMP [Label xl] [] sy = ((),sz) /\
    se.cs_current_bb = (if sel then tl else el) /\ se.cs_current_insts = [] /\
    st'.cs_current_bb = xl /\ st'.cs_current_insts = [] /\
    vv = (if is_word_type t then StackValue t (Var rv)
          else LocatedValue t (mk_ptr (Var rv) LocMemory)) /\
    fn_has_code st sc func /\ fn_has_code sj sn func /\
    fn_has_code se sx func /\ fn_has_code sx sy func /\ fn_has_code sy sz func /\
    local_ptrs_reserved cenv se /\ cs_extends sc st' /\ cs_extends se sx /\
    st.cs_next_var <= sc.cs_next_var /\ st.cs_next_id <= sc.cs_next_id /\
    sc.cs_next_var <= se.cs_next_var /\ sc.cs_next_id <= se.cs_next_id /\
    sx.cs_next_id <= st'.cs_next_id /\ (!x. not_fresh_at st x ==> x <> rv)
Proof
  strip_tac >> drule_all compile_expr_ifexp_states >> strip_tac >>
  `cs_extends s5 s6 /\ cs_extends s8 s9 /\ cs_extends s9 s10 /\
   cs_extends s12 s13 /\ cs_extends s13 s14` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s6 s7 /\ cs_extends s10 s11 /\ cs_extends s14 st'` by
    metis_tac[cs_extends_new_block] >>
  `fn_has_code st s1 func /\ fn_has_code s5 s6 func /\
   fn_has_code s7 s8 func /\ fn_has_code s8 s9 func /\ fn_has_code s9 s10 func /\
   fn_has_code s11 s12 func /\ fn_has_code s12 s13 func /\ fn_has_code s13 s14 func` by
    metis_tac[fn_has_code_mid, fn_has_code_split, cs_extends_trans] >>
  `local_ptrs_reserved cenv s7 /\ local_ptrs_reserved cenv s11` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `~not_fresh_at st rv` by metis_tac[] >>
  Cases_on `sel`
  >- (qexistsl_tac [`cond_op`,`s1`,`s5`,`s6`,`tl`,`el`,`xl`,`rv`,
                   `s7`,`av`,`s7a`,`aop`,`s8`,`s9`,`s10`] >> simp[]) >>
  qexistsl_tac [`cond_op`,`s1`,`s5`,`s6`,`tl`,`el`,`xl`,`rv`,
               `s11`,`bv`,`s11a`,`bop`,`s12`,`s13`,`s14`] >> simp[]
QED

(* Compatibility support is checked independently of the arm composition. *)
Theorem ifexp_abi_size_bound_source:
  evaluate_type env ty = SOME tv /\
  sfields_tenv_consistent (sf : (string, (string # type # num) list) fmap) env ==>
  abi_size_bound sf ty <= vyper_abi_size_bound env ty
Proof
  ACCEPT_TAC ifexp_compat_abi_size_bound_source
QED

Theorem ifexp_abi_tuple_size_bound_source:
  evaluate_types env tys [] = SOME tvs /\
  sfields_tenv_consistent (sf : (string, (string # type # num) list) fmap) env ==>
  abi_size_bound sf (TupleT tys) <= vyper_abi_size_bound env (TupleT tys)
Proof
  ACCEPT_TAC ifexp_compat_abi_tuple_size_bound_source
QED

Theorem ifexp_lowered_type_compatible:
  !ce e env.
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
  (int_calls_expr e = [] \/ same_memory_layout ce (lowered_value_type ce e) (expr_type e)) ==>
  lowered_value_type ce e = expr_type e \/
  is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) \/
  same_memory_layout ce (lowered_value_type ce e) (expr_type e)
Proof
  ACCEPT_TAC ifexp_compat_lowered_type
QED

Theorem ifexp_body_pre_lowered_type_compatible:
  expr_body_pre ce cx env e es /\
  (int_calls_expr e = [] \/ same_memory_layout ce (lowered_value_type ce e) (expr_type e)) ==>
  lowered_value_type ce e = expr_type e \/
  is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) \/
  (same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
   arg_type_fits (lowered_value_type ce e) (expr_type e) /\
   (?tvp. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tvp))
Proof
  ACCEPT_TAC ifexp_compat_body_pre_lowered_type
QED

Theorem ifexp_body_pre_read_typed:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
  ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\ value_has_type tvt v
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_at (Pat `bind _ _ _ = _`) vyperTypeEvalSoundnessTheory.eval_expr_read_type_sound >>
  disch_then (qspec_then `env` mp_tac) >>
  gvs[expr_body_pre_def, expr_sim_inv_def,
      vyperTypeExprSoundnessTheory.value_runtime_typed_def]
QED

(* ===== Counted simulation ===== *)

Theorem ifexp_arm_seq_path[local]:
  sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `?code. sb.cs_current_insts = sa.cs_current_insts ++ code /\
          emitted_insts sa sb = code` by
    (qpat_x_assum `isPREFIX sa.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX sb.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `l` >>
     asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) code) = 0` by
    (simp[LENGTH_NIL, FILTER_EQ_NIL, EVERY_MEM] >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  gvs[EVERY_MEM]
QED

Theorem ifexp_arm_rebased_unwrap_path[local]:
  post_value_type ce e = expr_type e /\
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_path ctx func r 0 (OK u) /\
      expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
        su r es' v op u /\
      u.vs_current_bb = su.cs_current_bb /\
      u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  strip_tac >>
  drule ifexp_vv_post_rebase >> strip_tac >>
  drule vv_post_read_result >> disch_then (fn th => fs[th]) >>
  `local_ptrs_reserved ce (sa with cs_next_var := sm.cs_next_var)` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sm` >> simp[]) >>
  irule unwrap_value_path >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ifexp_arm_store_path[local]:
  compile_store_bytestring src dst sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule ifexp_store_bytestring_straight >> strip_tac >>
  irule ifexp_arm_seq_path >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, IS_PREFIX_APPEND,
       venomInstTheory.mk_inst_def, is_terminator_def]
QED

Theorem ifexp_arm_unwrap_store_path[local]:
  unwrap_value ce vv sm = (src,sn) /\
  compile_store_bytestring src (Var x) sn = ((),sb) /\
  vv_post ctx func ce cx e es origin sm s0 es' raw vv r /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce origin /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  origin.cs_next_var <= sm.cs_next_var /\ origin.cs_next_id <= sm.cs_next_id /\
  origin.cs_next_id <= inst.inst_id /\ inst.inst_id < sm.cs_next_id /\
  not_fresh_at sm x /\ eval_operand (Var x) r = SOME d /\
  ci_mono sm sn /\ ci_mono sn sb /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\
  read_result cx raw es' = (INL v,es') /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv) /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n d \/ w2n d + type_memory_size tv <= b) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_path ctx func r 0 (OK t) /\
      expr_post ctx func ce cx e es origin sb s0 es' v (Var x) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `!z. src = Var z ==> not_fresh_at sn z` by
    (drule_at (Pos hd) exprOperandVarTheory.compiler_unwrap_value_var >>
     Cases_on `vv` >> simp[vv_operand_def] >> metis_tac[]) >>
  `!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    ~is_word_type (expr_type e) ==>
    type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64` by (rpt strip_tac >> gvs[]) >>
  `post_value_type ce e = expr_type e` by metis_tac[post_value_type_bytestring] >>
  drule_all ifexp_arm_rebased_unwrap_path >> strip_tac >>
  `type_memory_size tv < dimword (:256)` by (fs[dimword_def] >> decide_tac) >>
  fs[ci_mono_def] >>
  `?q. run_inst_seq (emitted_insts sn sb) u = OK q /\
       expr_post ctx func ce cx e es origin sb s0 es' v (Var x) q` by
    (irule ifexp_rebased_store_post_run >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`inst`, `raw`, `vv`] >>
     asm_rewrite_tac[] >> decide_tac) >>
  `~u.vs_halted` by metis_tac[gas_path_normal] >>
  drule_all ifexp_arm_store_path >> strip_tac >>
  `q.vs_current_bb = u.vs_current_bb` by
    (irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb` exprLoweringPropsTheory.run_inst_seq_preserves_field)) >>
     goal_assum (drule_at Any) >> rpt strip_tac >>
     drule ifexp_store_bytestring_straight >> strip_tac >>
     fs[EVERY_MEM] >>
     metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke]) >>
  drule ifexp_store_bytestring_straight >> strip_tac >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >>
  qpat_x_assum `!ctx. gas_path ctx func u _ _` (qspec_then `ctx` assume_tac) >>
  metis_tac[gas_path_then, arithmeticTheory.ADD]
QED

Theorem ifexp_arm_alloc_path[local]:
  compile_alloc_buffer sz sa = (buf,sm) /\
  vv_post ctx func ce cx e es origin sa s0 es' raw vv s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sm func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r d. gas_path ctx func s 0 (OK r) /\
    vv_post ctx func ce cx e es origin sm s0 es' raw vv r /\
    eval_operand buf.buf_operand r = SOME d /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n d,sz) /\
    r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >> drule_all ifexp_alloc_preserves_post >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  `emitted_insts sa sm =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `q.vs_current_bb = s.vs_current_bb` by
    (irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb`
       exprLoweringPropsTheory.run_inst_seq_preserves_field)) >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def] >>
     rpt strip_tac >>
     qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[GSYM venomInstTheory.mk_inst_def] >> strip_tac >>
     `!fuel ctx. step_inst fuel ctx
       (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
        [STRING #"%" (toString sa.cs_next_var)]) ss1 = OK ss2` by
       simp[step_inst_non_invoke, venomInstTheory.mk_inst_def] >>
     qpat_x_assum `!fuel ctx. step_inst _ _ _ _ = _`
       (qspecl_then [`0`, `ctx`] assume_tac) >>
     drule venomInstProofsTheory.step_preserves_control_flow >>
     simp[venomInstTheory.mk_inst_def, is_terminator_def]) >>
  `gas_path ctx func s 0 (OK (q with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (irule ifexp_arm_seq_path >> conj_tac >- simp[] >> qexists_tac `sa` >>
     simp[IS_PREFIX_APPEND, venomInstTheory.mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`q with vs_inst_idx := LENGTH sm.cs_current_insts`, `w`] >>
  fs[ifexp_vv_post_inst_idx, eval_operand_def, lookup_var_def]
QED

Theorem ifexp_arm_alloc_separated[local]:
  vv_post ctx func ce cx e es origin sm s0 es' raw vv r /\
  local_ptrs_reserved ce sa /\ fn_inst_ids_distinct func /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) r = SOME d /\
  FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n d,sz) ==>
  !n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n d \/ w2n d + sz <= b
Proof
  strip_tac >>
  `not_local_ptr ce es'.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (gvs[not_local_ptr_def, local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  rpt strip_tac >>
  `regions_disjoint (w2n d) sz b k` suffices_by
    simp[regions_disjoint_def, DISJ_COMM] >>
  irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
  qexistsl_tac [`ce`, `func`, `mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w sz)] [STRING #"%" (toString sa.cs_next_var)]`, `n`,
    `STRING #"%" (toString sa.cs_next_var)`, `es'.scopes`, `r`] >>
  simp[venomInstTheory.mk_inst_def] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ r` mp_tac >>
  simp[vv_post_def, stmt_state_rel_def, state_rel_def]
QED

Theorem ifexp_arm_bytestring_path[local]:
  expr_type e = t /\ is_bytestring_type t /\
  ~is_word_type t /\ ~same_memory_layout ce arm_ty t /\
  compile_ifexp_arm ce t arm_ty vv sa = (op,sb) /\
  read_result cx raw es' = (INL v,es') /\
  evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v /\
  type_memory_bytes ce t = type_memory_size tv /\ type_memory_size tv < 2 ** 64 /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce origin /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  vv_post ctx func ce cx e es origin sa s0 es' raw vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path ctx func s 0 (OK q) /\
    expr_post ctx func ce cx e es origin sb s0 es' v op q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all ifexp_bytestring_adapter_parts >> strip_tac >>
  `ci_mono sa sm` by
    (qspec_then `type_memory_bytes ce t` (qspec_then `sa` mp_tac)
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sn` by
    (qspecl_then [`ce`, `vv`, `sm`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `ci_mono sn sb` by
    (qspecl_then [`src`, `buf.buf_operand`, `sn`] mp_tac
       ci_mono_compile_store_bytestring >> simp[]) >>
  `local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
   local_ptrs_reserved ce sn` by
    (gvs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code sn sb func` by
    (gvs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce t))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
     qpat_x_assum `fn_has_code sa sm func` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND] >> strip_tac >>
     irule lookup_block_fn_insts >> goal_assum (drule_at Any) >> simp[MEM_APPEND]) >>
  `type_memory_bytes ce t < dimword (:256)` by (fs[dimword_def] >> decide_tac) >>
  drule_all ifexp_arm_alloc_path >> strip_tac >>
  suspend "suffix"
QED
Resume ifexp_arm_bytestring_path[suffix]:
  `~r.vs_halted` by metis_tac[gas_path_normal] >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n d \/ w2n d + type_memory_size tv <= b` by
    (gvs[] >> rpt strip_tac >> irule (SRULE [arithmeticTheory.ADD_COMM] ifexp_arm_alloc_separated) >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  `?q. gas_path ctx func r 0 (OK q) /\
    expr_post ctx func ce cx e es origin sb s0 es' v op q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (gvs[] >> irule ifexp_arm_unwrap_store_path >>
     asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     qexistsl_tac [`d`, `sn`, `src`, `tv`] >>
     simp[venomInstTheory.mk_inst_def, arithmeticTheory.ADD_COMM] >>
     first_assum ACCEPT_TAC) >>
  qexists_tac `q` >> simp[] >>
  metis_tac[gas_path_then, arithmeticTheory.ADD]
QED
Finalise ifexp_arm_bytestring_path[local]

Theorem ifexp_arm_raw_admissible[local]:
  gas_admissible (bind (eval_expr cx e) (conditional_result cx))
    expr_vv_res_ok es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >> gvs[expr_vv_res_ok_def]
  >- (rename1 `eval_expr cx e _ = (INL raw,ee)` >>
      Cases_on `raw` >> simp[] >>
      first_x_assum (qspec_then `gs` mp_tac) >>
      simp[bind_def, conditional_result_def, raise_def,
           expr_vv_res_ok_def]) >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[bind_def, expr_vv_res_ok_def]
QED

Theorem ifexp_arm_conditional_read:
  read_result cx raw ee = (INL v,ee) /\
  conditional_result cx raw ee = (res,ss) /\ expr_vv_res_ok res ==>
  ?tv. res = INL tv /\ ss = ee /\
       read_result cx tv ee = (INL v,ee)
Proof
  rpt strip_tac >>
  Cases_on `(do r <- conditional_result cx raw; read_result cx r od) ee` >>
  drule conditional_read_cases >>
  strip_tac >>
  imp_res_tac vyperStatePreservationTheory.conditional_result_state >>
  gvs[expr_vv_res_ok_def, bind_def, AllCaseEqs()]
QED

Theorem ifexp_arm_conditional_gas_obs:
  conditional_result cx raw ee = (INL tv,ee) ==>
  !tail. conditional_result cx raw (ee with gas_obs := tail) =
    (INL tv,ee with gas_obs := tail)
Proof
  Cases_on `raw`
  >- simp[conditional_result_def, return_def]
  >- (simp[conditional_result_def, bind_def] >>
      Cases_on `place_type_value cx p ee` >>
      rename1 `place_type_value cx p ee = (pr,pst)` >>
      drule place_type_value_state >> strip_tac >> gvs[] >>
      `!tail. place_type_value cx p (ee with gas_obs := tail) =
         (pr,ee with gas_obs := tail)` by
        (Cases_on `p` >>
         gvs[place_type_value_def, get_scopes_def, get_immutables_def,
             get_address_immutables_def, bind_def, return_def,
             lift_option_type_def, raise_def, AllCaseEqs()] >>
         rpt gen_tac >>
         rpt (CASE_TAC >> gvs[return_def, raise_def])) >>
      simp[] >> Cases_on `pr` >> simp[] >>
      IF_CASES_TAC >> simp[return_def] >>
      Cases_on `read_place cx p ee` >>
      rename1 `read_place cx p ee = (rr,ss)` >>
      Cases_on `rr` >> simp[return_def] >> rpt strip_tac >>
      gvs[bind_def, return_def] >>
      rename1 `read_place cx p ee = (INL v,ee)` >>
      `read_result cx (PlaceR p) ee = (INL v,ee)` by
        simp[read_result_def] >>
      drule read_result_gas_obs >> simp[read_result_def]) >>
  simp[conditional_result_def, raise_def]
QED

Theorem ifexp_arm_suffix_path[local]:
  post_value_type ce e = expr_type e /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sm = (op,sb) /\
  (~is_word_type (expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
      ~is_word_type (expr_type e) ==>
      type_memory_bytes ce (expr_type e) = type_memory_size tv /\
      type_memory_size tv < 2 ** 64) /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. gas_path ctx func s 0 (OK q) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  Cases_on `is_word_type (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)`
  >- (drule compile_ifexp_arm_unwrap >> strip_tac >> gvs[] >>
      drule vv_post_read_result >> disch_then (fn th => fs[th]) >>
      irule unwrap_value_path >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `is_bytestring_type (expr_type e)` by metis_tac[ifexp_copy_types] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    metis_tac[] >>
  irule ifexp_arm_bytestring_path >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `lowered_value_type ce e` >> gvs[] >> metis_tac[]
QED

Theorem ifexp_arm_marked_suffix[local]:
  post_value_type ce e = expr_type e /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0) marks (INL raw) ee (OK s) /\
  vv_post ctx func ce cx e es sa sm s0 (ee with gas_obs := []) raw vv s /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sm = (op,sb) /\
  (~is_word_type (expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
      ~is_word_type (expr_type e) ==>
      type_memory_bytes ce (expr_type e) = type_memory_size tv /\
      type_memory_size tv < 2 ** 64) /\
  (!gs v es2. ~is_word_type (expr_type e) /\
    (do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,es2) ==>
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?tv v q. gas_marked_exec F (ctx,func) (conditional_result cx raw)
      (ee with gas_obs := [],s) [] (INL tv) (ee with gas_obs := []) (OK q) /\
    read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    expr_post ctx func ce cx e es sa sb s0 (ee with gas_obs := []) v op q /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL raw,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `~s.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  Cases_on `read_result cx raw (ee with gas_obs := [])` >>
  rename1 `_ = (rr,ss)` >>
  `ss = ee with gas_obs := []` by metis_tac[read_result_state] >> gvs[] >>
  reverse (Cases_on `rr`) >- metis_tac[vv_post_failed_read] >>
  rename1 `read_result cx raw _ = (INL v,_)` >>
  suspend "package"
QED
Resume ifexp_arm_marked_suffix[package]:
  `~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    (strip_tac >> first_x_assum irule >> simp[] >>
     qexistsl_tac [`ee with gas_obs := []`, `gas_explicit marks s0.vs_gas_readings`] >>
     simp[bind_def]) >>
  `?q. gas_path ctx func s 0 (OK q) /\
    expr_post ctx func ce cx e es sa sb s0 (ee with gas_obs := []) v op q /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule ifexp_arm_suffix_path >> simp[] >>
     qexistsl_tac [`raw`, `sm`, `vv`] >> asm_rewrite_tac[]) >>
  Cases_on `conditional_result cx raw (ee with gas_obs := [])` >>
  rename1 `_ = (cr,cs)` >>
  `expr_vv_res_ok cr` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def] >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[bind_def]) >>
  drule_all ifexp_arm_conditional_read >> strip_tac >> gvs[] >>
  qexistsl_tac [`tv`, `v`, `q`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  drule ifexp_arm_conditional_gas_obs >> simp[]
QED
Finalise ifexp_arm_marked_suffix[local]

Theorem ifexp_arm_ignore_bind_action[local]:
  ignore_bind (bind a (conditional_result cx)) (return ()) =
  bind a (\tv. ignore_bind (conditional_result cx tv) (return ()))
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def] >>
  gen_tac >> Cases_on `a x` >> Cases_on `q` >> simp[bind_def]
QED

Theorem ifexp_arm_exempt_transport[local]:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind a (return ())) (es,s0) marks (err,ee) (leaf,finstate) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind a (conditional_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate)
Proof
  rewrite_tac[ifexp_arm_ignore_bind_action] >> strip_tac >>
  irule gas_exempt_cert_error_result >> simp[]
QED

Theorem ifexp_arm_outcome[local]:
  !ctx func cenv cx ty e es1 sa sm sb vv op u.
    post_value_type cenv e = expr_type e /\
    expr_vv_sim ctx func cenv cx ty e es1 /\
    compile_expr cenv ty e sa = (vv, sm) /\
    compile_ifexp_arm cenv (expr_type e) (lowered_value_type cenv e) vv sm =
      (op, sb) /\
    (~is_word_type (expr_type e) ==>
      lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
      same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
       ~is_word_type (expr_type e) ==>
       type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
       type_memory_size tvt < 2 ** 64) /\
    (!gs v es2. ~is_word_type (expr_type e) /\
       (do r <- eval_expr cx e; read_result cx r od)
         (es1 with gas_obs := gs) = (INL v, es2) ==>
       ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
             value_has_type tvt v) /\
    gas_admissible (bind (eval_expr cx e) (conditional_result cx))
      expr_vv_res_ok es1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es1 u /\ ~u.vs_halted /\
    u.vs_current_bb = sa.cs_current_bb /\
    u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (bind (eval_expr cx e) (conditional_result cx)) (es1, u)
      (\res ee t. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v, ee) /\
         expr_post ctx func cenv cx e es1 sa sb u ee v op t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  `ci_mono sm sb` by
    (qspecl_then [`cenv`, `expr_type e`, `lowered_value_type cenv e`, `vv`, `sm`]
      mp_tac ci_mono_compile_ifexp_arm >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es1` by
    metis_tac[ifexp_arm_raw_admissible] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `u`] mp_tac) >> simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def]
      >- suspend "success" >>
      suspend "exception") >>
  disj2_tac >> metis_tac[ifexp_arm_exempt_transport]
QED
Resume ifexp_arm_outcome[success]:
  drule (SRULE [] ifexp_arm_marked_suffix) >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`sb`, `op`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexistsl_tac [`INL tv'`, `es_end with gas_obs := []`, `OK q`] >> simp[] >>
  `marks = marks ++ []` by simp[] >> pop_assum SUBST1_TAC >>
  irule gas_marked_exec_bind_normal >> goal_assum drule >> simp[]
QED
Resume ifexp_arm_outcome[exception]:
  Cases_on `res`
  >- (Cases_on `r` >> gvs[expr_exit_def]) >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> goal_assum drule
QED
Finalise ifexp_arm_outcome[local]

Theorem ifexp_root_outcome_suffix[local]:
  gas_outcome F tops (ctx,func) source (es,s0) Q R /\
  (!res ee u. Q res ee u /\ ~u.vs_halted ==>
     ?v. gas_path ctx func u 0 (OK v) /\ Q' res ee v) ==>
  gas_outcome F tops (ctx,func) source (es,s0) Q' R
Proof
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks` >>
  Cases_on `gas_summary_at F (ctx,func) marks source (es,s0) Q R`
  >- (disj1_tac >>
      fs[gas_summary_at_def] >>
      Cases_on `?u. r = OK u /\ Q res (es_end with gas_obs := []) u`
      >- (gvs[] >>
          `~t.vs_halted` by
            (fs[gas_marked_exec_def, gas_marked_path_def] >>
             metis_tac[gas_path_normal]) >>
          first_x_assum drule_all >> strip_tac >>
          qexistsl_tac [`res`,`es_end`,`OK v`] >> simp[] >>
          gvs[gas_marked_exec_def, gas_marked_path_def] >>
          metis_tac[gas_path_then, arithmeticTheory.ADD_CLAUSES]) >>
      metis_tac[]) >> metis_tac[]
QED

Theorem ifexp_root_suffix_path[local]:
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sx sy func /\ fn_has_code sy sz func /\
  ~u.vs_halted /\ u.vs_current_bb = sx.cs_current_bb /\
  u.vs_inst_idx = LENGTH sx.cs_current_insts /\ eval_operand op u = SOME w ==>
  gas_path ctx func u 0
    (OK (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)))
Proof
  strip_tac >> drule_all ifexp_root_assign_zero_path >> strip_tac >>
  `sy.cs_current_bb = sx.cs_current_bb /\ sz.cs_blocks = sy.cs_blocks /\
   sz.cs_current_bb = sy.cs_current_bb /\
   sz.cs_current_insts = sy.cs_current_insts ++
     [mk_inst sy.cs_next_id JMP [Label xl] []]` by
    metis_tac[emit_inst_extends] >>
  `gas_path ctx func
    ((update_var rv w u) with vs_inst_idx := LENGTH sy.cs_current_insts) 0
    (OK (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)))` by
    (irule emit_jump_zero_path >> simp[update_var_def] >>
     qexistsl_tac [`sy`,`sz`] >> simp[]) >>
  qpat_x_assum `!ctx. gas_path _ _ _ _ _` (qspec_then `ctx` mp_tac) >>
  qpat_x_assum `gas_path _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  metis_tac[gas_path_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_root_finish_post[local]:
  post_value_type cenv e = expr_type e /\
  expr_post ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
  expr_post ctx func cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
  read_result cx tv ee = (INL v,ee) /\ expr_type e = t /\
  eval_operand op u = SOME w /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id ==>
  vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv
    (if is_word_type t then StackValue t (Var rv)
     else LocatedValue t (mk_ptr (Var rv) LocMemory))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >>
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `IfExp t c a b`] ifexp_root_vv_post_of_expr_post_read)) >>
  goal_assum (drule_at Any) >>
  irule expr_post_ifexp >>
  `~not_fresh_at sa rv` by metis_tac[] >>
  simp[] >> metis_tac[]
QED

Theorem ifexp_root_arm_finish[local]:
  post_value_type cenv e = expr_type e /\
  expr_post ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
  expr_type e = t /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id /\ sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func /\
  gas_outcome F tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
      expr_post ctx func cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
      u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts) R ==>
  gas_outcome F tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?tv. res = INL tv /\
      vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv
        (if is_word_type t then StackValue t (Var rv)
         else LocatedValue t (mk_ptr (Var rv) LocMemory)) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  strip_tac >> irule ifexp_root_outcome_suffix >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `?w. eval_operand op u = SOME w` by fs[expr_post_def, expr_val_rel_def] >>
  qexists_tac `jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)` >>
  conj_tac >- (irule ifexp_root_suffix_path >> simp[] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (irule ifexp_root_finish_post >> simp[] >> metis_tac[]) >>
  simp[jump_to_def]
QED

Theorem ifexp_root_condition_scopes:
  vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gs) = (INL v,mid) ==>
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  simp[vyperStateTheory.bind_def] >>
  Cases_on `eval_expr cx c (es with gas_obs := gs)` >>
  rename1 `_ = (raw,st)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  drule read_result_state >> strip_tac >> gvs[] >>
  drule eval_expr_preserves_scopes_dom >> simp[]
QED

Theorem ifexp_root_marked_zero_suffix[local]:
  gas_marked_exec F (ctx,func) source (es,s0) marks res mid (OK u) /\
  gas_path ctx func u 0 (OK v) ==>
  gas_marked_exec F (ctx,func) source (es,s0) marks res mid (OK v)
Proof
  simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >> simp[] >>
  metis_tac[gas_path_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_root_selected_outcome_prefix[local]:
  gas_marked_exec F (ctx,func)
    (vyperState$bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV sel)) mid (OK u) /\
  gas_path ctx func u 0 (OK v) /\
  gas_outcome F tops (ctx,func)
    (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    (mid with gas_obs := [],v) Q R ==>
  gas_outcome F tops (ctx,func) (eval_expr cx (IfExp t c a b)) (es,s0) Q R
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func)
    (vyperState$bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV sel)) mid (OK v)` by
    (irule ifexp_root_marked_zero_suffix >> metis_tac[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (gvs[] >> qexists_tac `marks ++ marks'` >> disj1_tac >>
      qexistsl_tac [`res`,`es_end`,`OK t'`] >> simp[] >>
      rewrite_tac[ifexp_root_eval_forced] >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`mid`,`v`,`BoolV sel`] >> simp[] >> Cases_on `sel` >> fs[]) 
  >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
      qexistsl_tac [`res`,`es_end`,`r`] >> simp[] >>
      rewrite_tac[ifexp_root_eval_forced] >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`mid`,`v`,`BoolV sel`] >> simp[] >> Cases_on `sel` >> fs[]) >>
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  rewrite_tac[ifexp_root_eval_forced] >>
  pure_once_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl_tac [`mid`,`v`,`BoolV sel`] >> simp[] >>
  Cases_on `sel` >> fs[GSYM vyperStateTheory.ignore_bind_def]
QED

Theorem ifexp_root_condition_exit[local]:
  gas_marked_exec F (ctx,func)
    (vyperState$bind (eval_expr cx c) (read_result cx))
    (es,s0) marks res mid r /\ expr_exit res r ==>
  gas_outcome F tops (ctx,func) (eval_expr cx (IfExp t c a b)) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  Cases_on `res` >> simp[] >> strip_tac >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR y`,`mid`,`r`] >> simp[] >>
  conj_tac
  >- (rewrite_tac[ifexp_root_eval_forced] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >>
  Cases_on `r` >> fs[expr_exit_def, exit_result_def] >>
  Cases_on `y` >> fs[expr_exit_def] >>
  rename1 `Error er` >> Cases_on `er` >> fs[expr_exit_def]
QED

Theorem ifexp_root_jnz_path[local]:
  expr_post ctx func cenv cx c es sa sc s0 mid (BoolV sel) cop u /\
  expr_type c = BaseT BoolT /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
  fn_has_code sj sn func /\ sj.cs_current_bb = sc.cs_current_bb /\
  sj.cs_current_insts = sc.cs_current_insts /\
  ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  gas_path ctx func u 0 (OK (jump_to (if sel then tl else el) u))
Proof
  strip_tac >> irule assert_jnz_zero_path >>
  simp[] >> qexistsl_tac [`cop`,`sj`,`sn`] >> simp[] >>
  drule emit_inst_extends >> strip_tac >> simp[] >>
  fs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
     valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def]
QED

(* x if c else y, from expr_sim of c and expr_vv_sim of the arm that c's
   value picks: the condition's run, the JNZ into the arm's block, the arm
   (ifexp_arm_outcome), the ASSIGN to the result variable and the JMP to the
   exit block. *)
Theorem compile_ifexp_vv_sim:
  !ctx func cenv cx ty t c a b es.
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (~is_word_type t ==>
     !e. (e = a \/ e = b) ==>
         lowered_value_type cenv e = expr_type e \/
         is_bytestring_type (expr_type e) /\
         is_bytestring_type (lowered_value_type cenv e) /\
         arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
         same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
    (!e. (e = a \/ e = b) ==> post_value_type cenv e = expr_type e) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
       type_memory_bytes cenv t = type_memory_size tvt /\
       type_memory_size tvt < 2 ** 64) /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    (!gs tv es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       expr_sim ctx func cenv cx ty a es1 /\
       expr_sim ctx func cenv cx ty b es1 /\
       expr_vv_sim ctx func cenv cx ty a es1 /\
       expr_vv_sim ctx func cenv cx ty b es1 /\
       !e gs' v es2. ~is_word_type t /\ (e = a \/ e = b) /\
         (do r <- eval_expr cx e; read_result cx r od)
           (es1 with gas_obs := gs') = (INL v, es2) ==>
         ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v) ==>
    expr_vv_sim ctx func cenv cx ty (IfExp t c a b) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_vv_sim_def] >> rpt strip_tac >>
  `?cop sc. lower_value compile_expr cenv (BaseT BoolT) c sa = (cop,sc) /\
     fn_has_code sa sc func` by
    (drule_all ifexp_root_code_layout >> disch_then (qspec_then `T` mp_tac) >>
     metis_tac[]) >>
  `gas_admissible (vyperState$bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    (irule ifexp_root_condition_admissible >> metis_tac[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ c _` mp_tac >> rewrite_tac[expr_sim_def] >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def, gas_summary_at_def])
  >- (gvs[] >>
      `!tail. vyperState$bind (eval_expr cx c) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,es_end with gas_obs := tail)` by fs[gas_marked_exec_def] >>
      `?sel. v = BoolV sel` by
        (irule ifexp_root_condition_bool >> metis_tac[]) >> gvs[] >>
      suspend "selected")
  >- (irule ifexp_root_condition_exit >> metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  metis_tac[ifexp_root_condition_cert]
QED

Resume compile_ifexp_vv_sim[selected]:
  qmatch_asmsub_abbrev_tac `expr_post _ _ _ _ c es sa sc s0 mid` >>
  `vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL (BoolV sel),mid)` by
    (simp[Abbr `mid`] >> metis_tac[APPEND_NIL]) >>
  last_x_assum (qspecl_then
    [`gas_explicit marks s0.vs_gas_readings`,`BoolV sel`,`mid`] mp_tac) >>
  fs[vyperStateTheory.bind_def] >> strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ a _` kall_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ b _` kall_tac >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (irule ifexp_root_condition_scopes >> fs[vyperStateTheory.bind_def] >> metis_tac[]) >>
  `gas_admissible
    (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    expr_vv_res_ok mid` by
    (simp[Abbr `mid`] >> irule (SRULE [] ifexp_root_branch_admissible) >>
     fs[gas_marked_exec_def] >> metis_tac[]) >>
  drule_all ifexp_root_code_layout >> disch_then (qspec_then `sel` strip_assume_tac) >>
  qpat_x_assum `!sa sb op. lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!e sa sb op. (e = a \/ e = b) /\ _ ==> _` kall_tac >>
  qpat_x_assum `compile_expr _ _ (IfExp _ _ _ _) _ = _` kall_tac >>
  qpat_x_assum `gas_admissible (eval_expr _ _) _ _` kall_tac >>
  qpat_x_assum `gas_admissible (vyperState$bind (eval_expr _ c) _) _ _` kall_tac >>
  gvs[] >> suspend "routed"
QED

Resume compile_ifexp_vv_sim[routed]:
  `~t'.vs_halted` by
    (fs[gas_marked_exec_def, gas_marked_path_def] >> metis_tac[gas_path_normal]) >>
  `gas_path ctx func t' 0 (OK (jump_to (if sel then tl else el) t'))` by
    (irule ifexp_root_jnz_path >> metis_tac[]) >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code sj sn func` kall_tac >>
  qpat_x_assum `fn_has_code sa sb func` kall_tac >>
  qpat_x_assum `fn_has_code sa sc func` kall_tac >>
  irule ifexp_root_selected_outcome_prefix >>
  qexistsl_tac [`marks`,`es_end`,`sel`,`t'`,`jump_to (if sel then tl else el) t'`] >>
  simp[] >>
  irule (SRULE [] ifexp_root_arm_finish) >>
  simp[] >>
  qexistsl_tac [`cop`,`if sel then a else b`,`aop`,`sc`,`se`,`sx`,`sy`,`sz`,`BoolV sel`] >>
  simp[] >> conj_tac >- (Cases_on `sel` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx mid (jump_to (if sel then tl else el) t')` by
    (simp[stmt_state_rel_jump_to] >> fs[expr_post_def]) >>
  conj_tac >- (Cases_on `sel` >> simp[]) >>
  irule ifexp_arm_outcome >>
  simp[] >>
  conj_tac
  >- (Cases_on `sel` >> gvs[vyperStateTheory.bind_def] >> metis_tac[]) >>
  simp[jump_to_def] >>
  Cases_on `sel` >> gvs[] >> metis_tac[]
QED

Finalise compile_ifexp_vv_sim

Theorem compile_ifexp_word_vv_sim:
  !ctx func cenv cx ty t c a b es.
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    is_word_type t /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    (!gs tv es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       expr_sim ctx func cenv cx ty a es1 /\
       expr_sim ctx func cenv cx ty b es1 /\
       expr_vv_sim ctx func cenv cx ty a es1 /\
       expr_vv_sim ctx func cenv cx ty b es1) ==>
    expr_vv_sim ctx func cenv cx ty (IfExp t c a b) es
Proof
  rpt strip_tac >> irule compile_ifexp_vv_sim >> simp[] >> metis_tac[post_value_type_word]
QED
