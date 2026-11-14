Theory bodyFullHashShaFixedAbort
Ancestors
  bodyFullHashShaFixed bodyFullHashShaSuccess bodyFullHashKeccakBytes
  bodyPtrHashBuiltinsShaFixedPaths bodyPtrHashBuiltinsShaFixed
  bodyPtrHashBuiltinsShaBytes bodyPtrHashBuiltinsShaAlloc
  bodyFullUnwrapRun bodyPtrHashBuiltinsGhostFrame instSeqComposePtr
  builtinHashing emitHelperProps exprLoweringProps compileEnv freshWrites
  bodyPtrDefs ptrDiscipline venomState venomInst fragExec instIdxIndep
  words list rich_list arithmetic finite_map pred_set exprSimHash loweringHalt
  ghostPcTransportPtr bodyFullHashShaAbort

Theorem sha_fixed_abort_ptr_at:
  !D lo ctx fn PG G tn s bb value v m sa op sb d cenv cx es.
  compile_sha256_bytesm value m sa = (op,sb) /\ fn_has_code sa sb fn /\ m <= 32 /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  eval_operand value s = SOME v /\ op_taint tn value = {} /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ghost_inv_at D lo d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst (sa.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var+1))]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  ?t Gf tf. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule hash_sha256_fixed_parts >> strip_tac >>
  drule_all hash_sha256_alloc_tail_layout >> strip_tac >>
  drule_all hash_sha256_fixed_code_split >> strip_tac >>
  drule_all hash_fixed_prepare_emission >> strip_tac >>
  `cs_extends sa sl /\ cs_extends sm sn` by
    metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sl sm /\ cs_extends sc sh` by
    (conj_tac >> irule (SRULE [cs_appends_def] (cj 3 cs_appends_emit_helpers)) >>
     goal_assum drule) >>
  `cs_extends sn sg /\ cs_extends sg sc /\ cs_extends sh sb` by
    (rpt conj_tac >> irule (SRULE [cs_appends_def] (cj 2 cs_appends_emit_helpers)) >>
     goal_assum drule) >>
  `cs_extends sc sb` by (irule cs_extends_trans >> qexists_tac `sh` >> simp[]) >>
  `cs_extends sg sb` by (irule cs_extends_trans >> qexists_tac `sc` >> simp[]) >>
  `cs_extends sn sb` by (irule cs_extends_trans >> qexists_tac `sg` >> simp[]) >>
  `cs_extends sm sb` by (irule cs_extends_trans >> qexists_tac `sn` >> simp[]) >>
  `cs_extends sl sb` by (irule cs_extends_trans >> qexists_tac `sm` >> simp[]) >>
  `fn_has_code sa sl fn /\ fn_has_code sm sn fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all sha_fixed_prepare_frame_at >>
  disch_then (qspec_then `PG`
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))) >>
  qabbrev_tac `a = t with vs_inst_idx := s.vs_inst_idx+2` >>
  `m < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `w2n (n2w m:bytes32) = m` by simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `stmt_state_rel H ctx fn cenv cx es a /\
   ghost_inv_at D lo d cenv cx es G2 tn2 a /\
   eval_operand (Var p) a = SOME w /\
   ptr_covers G2 tn2 p a (w2n (n2w m:bytes32)) /\
   isPREFIX (emitted_insts sm sb) (DROP a.vs_inst_idx bb.bb_instructions) /\
   MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString sm.cs_next_var)]) (fn_insts fn)` by
    simp[Abbr `a`, bytes_ghost_cursor, stmt_state_rel_inst_idx,
      hash_eval_operand_inst_idx, ptr_covers_inst_idx] >>
  `eval_operand (Lit (n2w m)) a = SOME (n2w m) /\
   op_taint tn2 (Lit (n2w m)) = {} /\
   (!x. x=p \/ Lit (n2w m:bytes32)=Var x ==> not_fresh_at sm x)` by
    simp[eval_operand_def, op_taint_def] >>
  Q.SUBGOAL_THEN
   `(w2n (n2w m:bytes32) = 0 \/
     (?aid b k. FLOOKUP a.vs_allocas aid = SOME (b,k) /\
       aid < sm.cs_next_id /\ b <= w2n w /\
       w2n w+w2n (n2w m:bytes32) <= b+k) \/
     (?name b k. local_region cenv es.scopes a name b k /\
       b <= w2n w /\ w2n w+w2n (n2w m:bytes32) <= b+k))` assume_tac >-
    (disj2_tac >> disj1_tac >>
     qexistsl_tac [`sa.cs_next_id`, `w2n w`, `32`] >> simp[Abbr `a`]) >>
  `!i. w2n w <= i /\ i < w2n w+w2n (n2w m:bytes32) ==> i NOTIN tn2.t_mem` by simp[] >>
  `~(?outcome rest. a.vs_outcomes = outcome::rest /\ outcome.co_success)` by
    fs[Abbr `a`] >>
  `~a.vs_halted /\ lookup_block a.vs_current_bb fn.fn_blocks = SOME bb` by
    simp[Abbr `a`] >>
  qpat_x_assum `ib.buf_operand = Var p` SUBST_ALL_TAC >>
  drule_all sha_alloc_abort_ptr_at >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    simp[mk_inst_def, is_terminator_def] >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf` by
    (qpat_assum `emitted_insts sa sb = _` SUBST1_TAC >>
     irule inst_seq_ptr_append_ok >> simp[] >>
     qexistsl_tac [`G2`, `tn2`] >> gvs[Abbr `a`]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule_all hash_sha256_alloc_tail_nonterminators >> simp[]) >>
  `?u. run_inst_seq (emitted_insts sm sb) t = Abort Revert_abort u /\
       t' = u with vs_inst_idx := s.vs_inst_idx+2` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sb) a = _` mp_tac >>
     simp[Abbr `a`, run_inst_seq_inst_idx] >>
     Cases_on `run_inst_seq (emitted_insts sm sb) t` >> simp[exec_result_map_def]) >>
  qexistsl_tac [`u`, `Gf`, `tf`] >> simp[] >>
  qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK t`
    (mp_tac o MATCH_MP run_inst_seq_append) >>
  disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[]
QED

