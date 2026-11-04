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
 *   compile_ifexp_vv_sim   — expr_vv_sim of an IfExp, on results that are
 *                            values, from expr_sim of its three operands and
 *                            the compile-state shape of their lowering
 *   ifexp_branch_sim       — one arm of it, from the condition's fragment
 *                            through the arm's jump to the exit block
 *
 * Helpers: compile_expr_ifexp, compile_expr_ifexp_states,
 * eval_expr_ifexp_cases, frag_exec_assign, ifexp_arm_frag, ifexp_jnz_arm,
 * expr_post_ifexp, vv_post_of_expr_post.
 *)

Theory exprSimIfExp
Ancestors
  list rich_list finite_map marker
  fragExec exprSim exprSimOps exprSimUnwrap freshWrites exprBopLowering loweringSlice
  vyperEvalExprPreservesScopesDom exprLowering emitHelperProps
  exprLoweringProps compileEnv context vyperAST vyperInterpreter vyperState
  vyperValue valueEncoding venomExecSemantics venomExecProofs venomInst
  venomState exprSimLiteralBuffer words integer_word vfmConstants valueEncodingProps
  valueTypingMemoryProps
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

Theorem ifexp_copy_types[local]:
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
  rewrite_tac[exprSimTheory.buffer_round_mask, word_add_n2w] >>
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

Theorem ifexp_store_bytestring_shape[local]:
  !src dst sa sb.
    compile_store_bytestring src dst sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var + 4 /\
    sb.cs_next_id = sa.cs_next_id + 5
Proof
  rpt strip_tac >>
  gvs[compile_store_bytestring_def, compile_bytestring_copy_len_def,
      emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp[same_blocks_def, emitted_insts_def, rich_listTheory.DROP_APPEND1]
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
      qexists_tac `LENGTH l` >> simp[exprSimTheory.val_store_size_def]) >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  drule ifexp_string_header >> strip_tac >>
  qexists_tac `LENGTH s'` >> simp[exprSimTheory.val_store_size_def]
QED

Theorem ifexp_copy_source_bounds[local]:
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

Theorem ifexp_alloc_preserves_holds[local]:
  !ctx func cenv cx es sa sm buf sz s et raw vv.
    compile_alloc_buffer sz sa = (buf,sm) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
    vv_holds cenv cx et raw vv es s ==>
    ?q w. run_inst_seq (emitted_insts sa sm) s = OK q /\
      stmt_state_rel ctx func cenv cx es q /\
      vv_holds cenv cx et raw vv es q /\
      eval_operand buf.buf_operand q = SOME w /\
      FLOOKUP q.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      q.vs_memory = s.vs_memory
Proof
  rpt strip_tac >> drule_all alloc_buffer_frame_run >> strip_tac >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >> gvs[eval_operand_def]) >>
  `vv_holds cenv cx et raw vv es t` by
    (Cases_on `vv` >> gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]) >>
  qexistsl_tac [`t`, `w`] >> simp[]
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

Theorem ifexp_alloc_preserves_at[local]:
  !ctx func cenv cx es origin sa sm buf sz s ty raw vv.
    compile_alloc_buffer sz sa = (buf,sm) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
    vv_at cenv cx ty origin sa es raw vv s ==>
    ?q. run_inst_seq (emitted_insts sa sm) s = OK q /\
        vv_at cenv cx ty origin sm es raw vv q
Proof
  rpt strip_tac >> drule_all alloc_buffer_frame_run >> strip_tac >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >> gvs[eval_operand_def]) >>
  `!n b len. local_region cenv es.scopes t n b len <=>
             local_region cenv es.scopes s n b len` by
    (drule_all ifexp_alloc_local_regions >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  irule ifexp_vv_at_alloc_frame >> qexistsl_tac [`s`, `sa`] >> simp[]
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

Theorem conditional_read_cases[local]:
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
  rpt gen_tac >> simp[expr_post_def] >> strip_tac >>
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
  >- (qpat_x_assum `expr_val_rel cx (expr_type e) v aop u` mp_tac >>
      simp[expr_val_rel_def, eval_operand_def] >> strip_tac >> gvs[]) >>
  conj_tac
  >- (qpat_x_assum `expr_val_at cenv cx (expr_type e) sc sd es' v aop u` mp_tac >>
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
      metis_tac[]) >>
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

(* One arm of an IfExp, lowered to eop between bs and bm, then assigned to
   rv: from the jump into the arm's block, the arm's fragment and the
   ASSIGN run to bn with eop's word in rv. *)
Theorem ifexp_arm_frag:
  !ctx func cenv cx ty e es1 res es' bs bm bn eop rv tt lbl.
    expr_sim ctx func cenv cx ty e es1 /\
    lower_value compile_expr cenv ty e bs = (eop, bm) /\
    emit_inst ASSIGN [eop] [rv] bm = ((), bn) /\
    (do result <- eval_expr cx e; read_result cx result od) es1 = (res, es') /\ expr_res_ok res /\
    fn_has_code bs bm func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv bs /\ stmt_state_rel ctx func cenv cx es1 tt /\
    cs_extends bs bm ==>
    frag_exec ctx bs bn (\s. s = jump_to lbl tt)
      (\s. ?v u w. res = INL v /\
             expr_post ctx func cenv cx e es1 bs bm (jump_to lbl tt) es' v eop u /\
             eval_operand eop u = SOME w /\
             s = (update_var rv w u) with
                   vs_inst_idx := LENGTH bn.cs_current_insts)
      (expr_exit res)
Proof
  rpt strip_tac >>
  `cs_extends bm bn` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  qpat_x_assum `expr_sim _ _ _ _ ty e es1`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`bs`, `bm`, `eop`, `res`, `es'`, `jump_to lbl tt`]
                mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = jump_to lbl tt`, `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[stmt_state_rel_jump_to]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
  asm_rewrite_tac[] >> rpt strip_tac >> fs[] >>
  irule frag_exec_assign >> first_assum (irule_at Any) >>
  rpt strip_tac >> gvs[] >>
  rename1 `expr_post ctx func cenv cx e es1 bs bm _ es' v eop uu` >>
  `?w. eval_operand eop uu = SOME w` by
    (qpat_x_assum `expr_post ctx func cenv cx e _ _ _ _ _ _ _ uu` mp_tac >>
     simp[expr_post_def, expr_val_rel_def] >> strip_tac >>
     qexists_tac `w` >> simp[]) >>
  qexists_tac `w` >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`uu`, `w`] >> asm_rewrite_tac[]
QED

(* The JNZ that ends c's code, from the state tt c's fragment ends in: it
   jumps to bl, the block bs starts, where the arm runs as ifexp_arm_frag
   says, and the arm's JMP reaches the exit block xl, which sb starts. *)
Theorem ifexp_jnz_arm:
  !ctx func cenv cx t c a b e bv es es1 es' res sa sb s0 s1 s5 s6 x6 s7
   bs bm bn bo bx bp tl el xl bl lbl rv cond_op eop tt.
    frag_exec ctx bs bn (\s. s = jump_to bl tt)
      (\s. ?v u w. res = INL v /\
             expr_post ctx func cenv cx e es1 bs bm (jump_to bl tt) es' v eop u /\
             eval_operand eop u = SOME w /\
             s = (update_var rv w u) with
                   vs_inst_idx := LENGTH bn.cs_current_insts)
      (expr_exit res) /\
    expr_post ctx func cenv cx c es sa s1 s0 es1 (BoolV bv) cond_op tt /\
    eval_operand cond_op tt = SOME (val_to_w256 (BoolV bv)) /\
    emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
    new_block tl s6 = (x6, s7) /\
    emit_inst JMP [Label xl] [] bn = ((), bo) /\
    new_block lbl bo = (bx, bp) /\
    (if bv then tl else el) = bl /\ bs.cs_current_bb = bl /\
    bs.cs_current_insts = [] /\
    s5.cs_current_bb = s1.cs_current_bb /\
    s5.cs_current_insts = s1.cs_current_insts /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
    cs_extends s1 s6 /\ cs_extends s6 s7 /\ cs_extends s7 sb /\
    cs_extends s1 bs /\ cs_extends bs bn /\ cs_extends bs bp /\
    cs_extends bp sb /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= bs.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= bs.cs_next_id /\
    bm.cs_next_id <= sb.cs_next_id /\
    expr_type e = t /\ (!x. not_fresh_at sa x ==> x <> rv) /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes ==>
    frag_exec ctx s1 sb (\s. s = tt)
      (\s. ?v. res = INL v /\
                vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' (Value v)
                  (if is_word_type t then StackValue t (Var rv)
                   else LocatedValue t (mk_ptr (Var rv) LocMemory)) s)
      (expr_exit res)
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  PURE_REWRITE_TAC[frag_exec_def] >> BETA_TAC >> rpt strip_tac >>
  qpat_x_assum `_ = tt` SUBST_ALL_TAC >>
  `step_inst_base (mk_inst s5.cs_next_id JNZ [cond_op; Label tl; Label el] [])
     tt = OK (jump_to bl tt)` by
    (qpat_x_assum `(if _ then _ else _) = bl` (SUBST_ALL_TAC o SYM) >>
     simp[venomInstTheory.mk_inst_def] >>
     drule venomExecProofsTheory.step_jnz_behavior >>
     disch_then (fn th => simp[th]) >> Cases_on `bv` >> simp[val_to_w256_def]) >>
  qabbrev_tac `jnz = mk_inst s5.cs_next_id JNZ [cond_op; Label tl; Label el] []` >>
  qabbrev_tac `jbb = <| bb_label := s6.cs_current_bb;
                        bb_instructions := s6.cs_current_insts |>` >>
  `fn_has_code s6 s7 fn` by
    (irule fn_has_code_mid >> asm_rewrite_tac[] >>
     qexistsl_tac [`sb`, `s1`] >> asm_rewrite_tac[]) >>
  `fn_has_code bs bp fn` by
    (irule fn_has_code_mid >> asm_rewrite_tac[] >>
     qexistsl_tac [`sb`, `s1`] >> asm_rewrite_tac[] >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >> metis_tac[cs_extends_trans]) >>
  `lookup_block tt.vs_current_bb fn.fn_blocks = SOME jbb` by
    (`tt.vs_current_bb = s6.cs_current_bb` by fs[] >>
     simp[Abbr `jbb`] >> metis_tac[fn_has_code_new_block]) >>
  `get_instruction jbb tt.vs_inst_idx = SOME jnz` by
    fs[Abbr `jbb`, get_instruction_def, EL_LENGTH_APPEND] >>
  `is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE` by
    simp[Abbr `jnz`, venomInstTheory.mk_inst_def, is_terminator_def] >>
  qspecl_then [`ctx`, `fn`, `tt`, `tt`, `jbb`, `jnz`, `bs`, `bn`, `bo`,
     `bp`, `xl`, `lbl`, `bx`, `\s. s = jump_to bl tt`,
     `\s. ?v u w. res = INL v /\
            expr_post ctx func cenv cx e es1 bs bm (jump_to bl tt) es' v eop u /\
            eval_operand eop u = SOME w /\
            s = (update_var rv w u) with
                  vs_inst_idx := LENGTH bn.cs_current_insts`,
     `expr_exit res`] mp_tac if_branch_to_exit >>
  (impl_tac >- (asm_rewrite_tac[] >> BETA_TAC >> rpt strip_tac >> metis_tac[])) >>
  BETA_TAC >> strip_tac
  >- (disj1_tac >>
      qpat_x_assum `!fuel r. run_from _ _ _ (jump_to xl _) = _ /\ _ ==> _`
        mp_tac >>
      qmatch_goalsub_rename_tac `jump_to xl ss` >> strip_tac >>
      qexists_tac `jump_to xl ss` >> rpt conj_tac
      >- (qexists_tac `v` >> simp[] >>
          qspecl_then [`func`, `cenv`, `cx`, `IfExp t c a b`, `es`, `sa`, `sb`,
                       `s0`, `es'`, `v`, `rv`, `jump_to xl ss`, `ctx`] mp_tac
            vv_post_of_expr_post >>
          simp[vyperASTTheory.expr_type_def] >> disch_then irule >>
          qpat_x_assum `ss = _` SUBST_ALL_TAC >> irule expr_post_ifexp >>
          conj_tac >- (rpt strip_tac >> gvs[]) >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          qexistsl_tac [`eop`, `cond_op`, `e`, `es1`, `bl`, `s1`, `bs`, `bm`,
                        `tt`, `BoolV bv`] >>
          asm_rewrite_tac[] >> fs[])
      >- (qpat_x_assum `~ss.vs_halted` mp_tac >>
          qpat_x_assum `ss = _` (fn th => rewrite_tac[th]) >>
          simp[jump_to_def])
      >- (simp[jump_to_def] >> asm_rewrite_tac[])
      >- (simp[jump_to_def] >> asm_rewrite_tac[listTheory.LENGTH]) >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> metis_tac[]
QED

(* An IfExp whose condition c evaluates to bv, lowered to cond_op between sa
   and s1: the JNZ on cond_op (emitted between s5 and s6) jumps to bl, the
   block bs starts, where the arm e that bv picks runs as ifexp_arm_frag
   says, and a JMP to the exit block xl, which sb starts, ends the arm
   (ifexp_jnz_arm).  Both arms of compile_ifexp_vv_sim are this lemma. *)
Theorem ifexp_branch_sim:
  !ctx func cenv cx ty t c a b e bv es es1 es' res sa sb s0 s1 s5 s6 x6 s7
   bs bm bn bo bx bp tl el xl bl lbl rv cond_op eop.
    expr_type c = BaseT BoolT /\ expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    expr_sim ctx func cenv cx ty e es1 /\
    (do result <- eval_expr cx c; read_result cx result od) es = (INL (BoolV bv), es1) /\
    (do result <- eval_expr cx e; read_result cx result od) es1 = (res, es') /\ expr_res_ok res /\ expr_type e = t /\
    lower_value compile_expr cenv (BaseT BoolT) c sa = (cond_op, s1) /\
    emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
    new_block tl s6 = (x6, s7) /\
    lower_value compile_expr cenv ty e bs = (eop, bm) /\
    emit_inst ASSIGN [eop] [rv] bm = ((), bn) /\
    emit_inst JMP [Label xl] [] bn = ((), bo) /\
    new_block lbl bo = (bx, bp) /\
    (if bv then tl else el) = bl /\ bs.cs_current_bb = bl /\
    bs.cs_current_insts = [] /\
    s5.cs_current_bb = s1.cs_current_bb /\
    s5.cs_current_insts = s1.cs_current_insts /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
    cs_extends sa s1 /\ cs_extends s1 s5 /\ cs_extends s7 bs /\
    cs_extends bs bm /\ cs_extends bp sb /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= bs.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= bs.cs_next_id /\
    bm.cs_next_id <= sb.cs_next_id /\
    (!x. not_fresh_at sa x ==> x <> rv) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?v. res = INL v /\
                vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' (Value v)
                  (if is_word_type t then StackValue t (Var rv)
                   else LocatedValue t (mk_ptr (Var rv) LocMemory)) s)
      (expr_exit res)
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  `cs_extends s5 s6 /\ cs_extends bm bn /\ cs_extends bn bo` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s6 s7 /\ cs_extends bo bp` by metis_tac[cs_extends_new_block] >>
  `cs_extends bs bn` by metis_tac[cs_extends_trans] >>
  `cs_extends bs bp` by metis_tac[cs_extends_trans] >>
  `cs_extends bs sb` by metis_tac[cs_extends_trans] >>
  `cs_extends bm sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 s6` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 s7` by metis_tac[cs_extends_trans] >>
  `cs_extends s7 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 bs` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sa bs` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func` by metis_tac[fn_has_code_split] >>
  `fn_has_code bs bm func` by metis_tac[fn_has_code_mid] >>
  `local_ptrs_reserved cenv bs` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (qpat_x_assum `(do result <- eval_expr cx c; read_result cx result od) es = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     metis_tac[eval_expr_preserves_scopes_dom]) >>
  (* the condition's fragment *)
  qpat_x_assum `expr_sim _ _ _ _ (BaseT BoolT) c _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `cond_op`, `INL (BoolV bv)`,
                           `es1`, `s0`] mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s`,
                           `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
  asm_rewrite_tac[] >> rpt strip_tac >> fs[] >>
  rename1 `expr_post ctx func cenv cx c es sa s1 s0 es1 (BoolV bv) cond_op tt` >>
  `stmt_state_rel ctx func cenv cx es1 tt /\
   eval_operand cond_op tt = SOME (val_to_w256 (BoolV bv))` by
    (fs[expr_post_def] >>
     qspecl_then [`cx`, `BaseT BoolT`, `BoolV bv`, `cond_op`, `tt`] mp_tac
       expr_val_rel_word >>
     simp[word_value_def, is_word_type_def, evaluate_type_def] >>
     disch_then irule >> gvs[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `e`, `es1`, `res`, `es'`,
               `bs`, `bm`, `bn`, `eop`, `rv`, `tt`, `bs.cs_current_bb`] mp_tac
    ifexp_arm_frag >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `t`, `c`, `a`, `b`, `e`, `bv`, `es`,
               `es1`, `es'`, `res`, `sa`, `sb`, `s0`, `s1`, `s5`, `s6`, `x6`,
               `s7`, `bs`, `bm`, `bn`, `bo`, `bx`, `bp`, `tl`, `el`,
               `sb.cs_current_bb`, `bs.cs_current_bb`, `lbl`, `rv`, `cond_op`,
               `eop`, `tt`] mp_tac ifexp_jnz_arm >>
  (impl_tac >- (simp[])) >>
  simp[]
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

Theorem readable_eval_frag_transport[local]:
  eval_expr cx e es = (raw,es') /\ expr_read_res_ok cx es' raw /\
  (!res. (do result <- eval_expr cx e; read_result cx result od) es = (res,es') /\
         expr_res_ok res ==>
         frag_exec ctx sa sb P
           (\s. ?v. res = INL v /\
                vv_post ctx func cenv cx e es sa sb s0 es' (Value v) vv s)
           (expr_exit res)) ==>
  frag_exec ctx sa sb P
    (\s. ?tv. raw = INL tv /\
         vv_post ctx func cenv cx e es sa sb s0 es' tv vv s)
    (expr_exit raw)
Proof
  strip_tac >> fs[expr_read_res_ok_def] >> gvs[]
  >- (qpat_x_assum `!res. _` (qspec_then `INL v` mp_tac) >>
      simp[bind_def, expr_res_ok_def] >>
      drule vv_post_read_result >> strip_tac >>
      `expr_exit (INL v) = (\r. F)` by simp[FUN_EQ_THM] >>
      `expr_exit (INL r) = (\r. F)` by simp[FUN_EQ_THM] >>
      simp[]) >>
  `expr_exit (INR exc : value + exception) =
   expr_exit (INR exc : eval_result + exception)` by
    (fs[expr_res_ok_def] >> rewrite_tac[FUN_EQ_THM] >> Cases >>
     simp[expr_exit_def]) >>
  qpat_x_assum `!res. _` (qspec_then `INR exc` mp_tac) >>
  simp[bind_def]
QED

Theorem compile_ifexp_forced_frag[local]:
  !ctx func cenv cx ty t c a b es.
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    (!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = (INL tv, es1) ==>
       expr_sim ctx func cenv cx ty a es1 /\
       expr_sim ctx func cenv cx ty b es1) ==>
    !sa sb vv res es' s0.
      compile_expr cenv ty (IfExp t c a b) sa = (vv, sb) /\
      (do result <- eval_expr cx (IfExp t c a b); read_result cx result od) es = (res, es') /\ expr_res_ok res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
        (\s. ?v. res = INL v /\
                  vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' (Value v) vv s)
        (expr_exit res)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `stmt_state_rel ctx func cenv cx es s0`)
  >- (`frag_exec ctx sa sb (\s. F) (\s. F) (\r. F)` by
        simp[frag_exec_false_pre] >>
      pop_assum (fn th => irule (MATCH_MP frag_exec_weaken th)) >>
      simp[]) >>
  drule_all compile_expr_ifexp_states >> strip_tac >>
  drule eval_expr_ifexp_cases >> strip_tac
  >- ((* the condition raises *)
      `fn_has_code sa s1 func` by metis_tac[fn_has_code_split] >>
      qpat_x_assum `expr_sim _ _ _ _ (BaseT BoolT) c _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `cond_op`, `INR exc`, `es'`, `s0`]
                    mp_tac) >>
      (impl_tac >- gvs[]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_weaken) >>
      disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s`,
                               `\s. F`, `expr_exit res`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >>
      irule frag_exec_exit_prefix >> qexists_tac `s1` >> simp[])
  >- (qpat_x_assum `!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = _ ==> _` drule >>
      strip_tac >> Cases_on `bv` >> fs[]
      >- (irule ifexp_branch_sim >> simp[cs_extends_refl] >>
          qpat_assum `lower_value _ _ _ a s7 = _` (irule_at Any) >>
          qpat_assum `emit_inst ASSIGN [aop] _ _ = _` (irule_at Any) >>
          qpat_assum `emit_inst JMP _ _ s9 = _` (irule_at Any) >>
          qpat_assum `new_block el s10 = _` (irule_at Any) >>
          simp[] >> qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at Any) >>
          qpat_assum `new_block tl s6 = _` (irule_at Any) >> simp[cs_extends_refl]) >>
      irule ifexp_branch_sim >> simp[cs_extends_refl] >>
      qpat_assum `lower_value _ _ _ b s11 = _` (irule_at Any) >>
      qpat_assum `emit_inst ASSIGN [bop] _ _ = _` (irule_at Any) >>
      qpat_assum `emit_inst JMP _ _ s13 = _` (irule_at Any) >>
      qpat_assum `new_block xl s14 = _` (irule_at Any) >>
      simp[] >> qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at Any) >>
      qpat_assum `new_block tl s6 = _` (irule_at Any) >> simp[cs_extends_refl]) >>
  gvs[expr_res_ok_def]
QED

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
    (!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = (INL tv, es1) ==>
       expr_sim ctx func cenv cx ty a es1 /\
       expr_sim ctx func cenv cx ty b es1 /\
       expr_vv_sim ctx func cenv cx ty a es1 /\
       expr_vv_sim ctx func cenv cx ty b es1 /\
       !e v es2. (e = a \/ e = b) /\
         (do r <- eval_expr cx e; read_result cx r od) es1 = (INL v, es2) ==>
         ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v) ==>
    !sa sb vv res es' s0.
      compile_expr cenv ty (IfExp t c a b) sa = (vv, sb) /\
      eval_expr cx (IfExp t c a b) es = (res, es') /\ expr_read_res_ok cx es' res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
        (\s. ?tv. res = INL tv /\
                  vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' tv vv s)
        (expr_exit res)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule readable_eval_frag_transport >>
  simp[] >> rpt strip_tac >>
  irule compile_ifexp_forced_frag >> simp[] >> qexists_tac `ty` >> simp[] >>
  first_assum ACCEPT_TAC
QED
