Theory bodyPtrTypeBuiltinsEmptyWords
Ancestors
  wordLoadStorePtr
  bodyPtrTypeBuiltinsEmptyZero bodyPtrTypeBuiltinsEmptyUniform bodyPtrTypeBuiltinsSeq abiEmptySequence
  builtinSimple emitHelper emitHelperProps compileEnv context exprLoweringProps
  venomInst venomState venomExecSemantics list rich_list words typedCopyPtr
  ptrDiscipline finite_map fragGasSeqPtr

Theorem empty_zero_words_successor_code:
  !n pop sa sm sb.
    compile_zero_words pop n sa = ((),sm) /\
    compile_zero_words pop (SUC n) sa = ((),sb) ==>
    emitted_insts sa sb = emitted_insts sa sm ++
      [mk_inst sm.cs_next_id ADD [pop; Lit (n2w (n*32))]
         [STRING #"%" (toString sm.cs_next_var)];
       mk_inst (sm.cs_next_id+1) MSTORE
         [Var (STRING #"%" (toString sm.cs_next_var)); Lit 0w] []]
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `compile_zero_words pop n sa = _`
    (mp_tac o MATCH_MP abi_empty_zero_words_shape) >> strip_tac >>
  gvs[Once compile_zero_words_def, comp_bind_def, comp_ignore_bind_def,
      emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
      emit_def, comp_return_def] >>
  gvs[inst_extends_def, emitted_insts_def, DROP_APPEND1] >>
  `LENGTH sa.cs_current_insts <= LENGTH sm.cs_current_insts` by
    (qpat_x_assum `sm.cs_current_insts = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
  simp[DROP_APPEND1]
QED

Theorem empty_zero_pair_storage_frame:
  !PG G tn s id p out w off.
    lookup_var p s = SOME w ==>
    (step_taint (mk_inst (id+1) MSTORE [Var out; Lit 0w] [])
      (update_var out (w+n2w off) s)
      (mstore (w2n (w+n2w off)) 0w (update_var out (w+n2w off) s))
      (step_taint (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s
        (update_var out (w+n2w off) s) tn)).t_stor = tn.t_stor /\
    (step_taint (mk_inst (id+1) MSTORE [Var out; Lit 0w] [])
      (update_var out (w+n2w off) s)
      (mstore (w2n (w+n2w off)) 0w (update_var out (w+n2w off) s))
      (step_taint (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s
        (update_var out (w+n2w off) s) tn)).t_trans = tn.t_trans
Proof
  rpt strip_tac >>
  simp[mstore_ghost_frame, copy_len_binop_ghost_frame,
       lookup_var_update_var, eval_operand_def, op_taint_def]
QED

Theorem empty_zero_pair_runtime_frame:
  !s out w off q.
    (mstore off 0w (update_var out w s) with
      <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (q <> out ==> lookup_var q (mstore off 0w (update_var out w s)) =
       lookup_var q s)
Proof
  simp[mstore_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       venomStateTheory.venom_state_component_equality]
QED

Theorem empty_zero_words_nonterminators:
  !n pop sa sb. compile_zero_words pop n sa = ((),sb) ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  Induct >- simp[compile_zero_words_def, comp_return_def, emitted_insts_refl] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_zero_words pop n sa` >>
  rename1 `compile_zero_words pop n sa = (unit_result,sm)` >>
  Cases_on `unit_result` >>
  drule_all empty_zero_words_successor_code >> disch_then SUBST1_TAC >>
  simp[mk_inst_def, is_terminator_def] >> first_x_assum irule >>
  qexists_tac `pop` >> simp[]
QED

Theorem empty_zero_words_certificate:
  !n sa sb s G tn p w sz D ctx func PG.
    compile_zero_words (Var p) n sa = ((),sb) /\
    not_fresh_at sa p /\ lookup_var p s = SOME w /\
    ptr_covers G tn p s sz /\ 32*n <= sz /\
    w2n w+sz < dimword (:256) /\ ~ctx_has_dalloca ctx ==>
    ?t H th. run_inst_seq (emitted_insts sa sb) s = OK t /\
      inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th /\
      lookup_var p t = SOME w /\ ptr_covers H th p t sz /\
      th.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w+32*n} /\
      th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
      (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
        FLOOKUP H q = FLOOKUP G q /\ op_taint th (Var q) = op_taint tn (Var q)) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s
Proof
  Induct >- (simp[compile_zero_words_def, comp_return_def] >>
    rpt strip_tac >> qexistsl_tac [`s`, `G`, `tn`] >>
    simp[emitted_insts_refl, run_inst_seq_def, inst_seq_ptr_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_zero_words (Var p) n sa` >>
  rename1 `compile_zero_words (Var p) n sa = (unit_result,sm)` >>
  Cases_on `unit_result` >>
  `32*n <= sz` by decide_tac >>
  first_x_assum drule_all >>
  disch_then (qspecl_then [`D`, `func`, `PG`] strip_assume_tac) >>
  `sm.cs_next_var = sa.cs_next_var+n` by
    (drule abi_empty_zero_words_shape >> simp[]) >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  `!q. not_fresh_at sa q ==> q <> out` by
    (rpt strip_tac >>
     gvs[not_fresh_at_def, Abbr `out`, ASCIInumbersTheory.toString_11] >> decide_tac) >>
  `p <> out` by metis_tac[] >>
  `32*n+32 <= sz` by decide_tac >>
  drule_all empty_zero_pair_uniform_certificate >>
  disch_then (qspecl_then [`D`, `func`, `PG`, `sm.cs_next_id`] strip_assume_tac) >>
  qabbrev_tac `u = update_var out (w+n2w (32*n)) t` >>
  qabbrev_tac `v = mstore (w2n (w+n2w (32*n))) 0w u` >>
  `emitted_insts sa sb = emitted_insts sa sm ++
     [mk_inst sm.cs_next_id ADD [Var p; Lit (n2w (32*n))] [out];
      mk_inst (sm.cs_next_id+1) MSTORE [Var out; Lit 0w] []]` by
    (simp[Abbr `out`] >> drule_all empty_zero_words_successor_code >> simp[]) >>
  qexistsl_tac [`v`, `G'`, `tn'`] >>
  conj_tac >- suspend "run" >>
  conj_tac >- suspend "sequence" >>
  conj_tac >- (simp[Abbr `v`, Abbr `u`, mstore_def, lookup_var_def,
                   update_var_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
  conj_tac >- simp[Abbr `v`, Abbr `u`] >>
  conj_tac >- suspend "memory" >>
  conj_tac >- suspend "storage" >>
  conj_tac >- suspend "transient" >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "old_vars" >>
  suspend "runtime"
QED

Resume empty_zero_words_certificate[run]:
  `step_inst_base (mk_inst sm.cs_next_id ADD
     [Var p; Lit (n2w (32*n))] [out]) t = OK u` by
    (simp[Abbr `u`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `lookup_var out u = SOME (w+n2w (32*n))` by
    simp[Abbr `u`, lookup_var_update_var] >>
  `step_inst_base (mk_inst (sm.cs_next_id+1) MSTORE
     [Var out; Lit 0w] []) u = OK v` by
    simp[Abbr `v`, step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def] >>
  asm_rewrite_tac[] >>
  drule run_inst_seq_append >> disch_then (fn th => rewrite_tac[th]) >>
  asm_rewrite_tac[run_inst_seq_def] >> simp[mk_inst_def]
QED
Resume empty_zero_words_certificate[memory]:
  simp[pred_setTheory.EXTENSION] >> gen_tac >>
  Cases_on `x IN tn.t_mem` >> simp[] >> decide_tac
QED
Resume empty_zero_words_certificate[sequence]:
  asm_rewrite_tac[] >> irule inst_seq_ptr_append_run >>
  drule_all empty_zero_words_nonterminators >> strip_tac >>
  conj_tac >- simp[] >> qexistsl_tac [`H`, `t`, `th`] >> simp[]
QED
Resume empty_zero_words_certificate[storage]:
  simp[]
QED
Resume empty_zero_words_certificate[transient]:
  simp[]
QED
Resume empty_zero_words_certificate[old_vars]:
  rpt strip_tac >>
  `q <> out` by metis_tac[] >>
  simp[Abbr `v`, Abbr `u`, empty_zero_pair_runtime_frame] >>
  metis_tac[]
QED
Resume empty_zero_words_certificate[runtime]:
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
  simp[Abbr `v`, Abbr `u`, mstore_def, update_var_def,
       venom_state_component_equality]
QED
Finalise empty_zero_words_certificate
