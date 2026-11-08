(* Fixed-run selector boundary: raw payload padding may remain tainted. *)
Theory bodyPtrSignedConvertSignedFixed
Ancestors
  wordLoadStorePtr bodyPtrSignedConvertSignedLoad bodyPtrSignedConvertUnsignedFixed
  bodyPtrSignedConvertIszero bodyPtrSignedConvertScalarOps
  venomState venomInst venomInstProofs venomExecSemantics finite_map words
  arithmetic pred_set ptrDiscipline ptrSafeRun codegenRel contextCodegenRel
  emitHelperProps exprLoweringProps fragGasSeqPtr fragExec typedCopyPtr instIdxIndep

Theorem signed_select_run_endpoint:
  ALL_DISTINCT [len;dp;data;empty;nonempty;selected] /\
  lookup_var len s = SOME nv /\ lookup_var dp s = SOME a /\
  run_inst_seq [mk_inst k MLOAD [Var dp] [data];
    mk_inst l ISZERO [Var len] [empty];
    mk_inst m ISZERO [Var empty] [nonempty];
    mk_inst r MUL [Var data;Var nonempty] [selected]] s = OK t ==>
  ?u v w.
    u = update_var data (mload (w2n a) s) s /\
    v = update_var empty (bool_to_word (nv = 0w)) u /\
    w = update_var nonempty (bool_to_word (nv <> 0w)) v /\
    t = update_var selected (mload (w2n a) s * bool_to_word (nv <> 0w)) w /\
    step_inst_base (mk_inst k MLOAD [Var dp] [data]) s = OK u /\
    step_inst_base (mk_inst l ISZERO [Var len] [empty]) u = OK v /\
    step_inst_base (mk_inst m ISZERO [Var empty] [nonempty]) v = OK w /\
    step_inst_base (mk_inst r MUL [Var data;Var nonempty] [selected]) w = OK t
Proof
  strip_tac >>
  qabbrev_tac `u = update_var data (mload (w2n a) s) s` >>
  qabbrev_tac `v = update_var empty (bool_to_word (nv = 0w)) u` >>
  qabbrev_tac `w = update_var nonempty (bool_to_word (nv <> 0w)) v` >>
  `step_inst_base (mk_inst k MLOAD [Var dp] [data]) s = OK u` by
    (simp[Abbr `u`] >> irule step_MLOAD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst l ISZERO [Var len] [empty]) u = OK v` by
    (simp[Abbr `v`, step_inst_base_def, mk_inst_def, exec_pure1_def] >>
     fs[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst m ISZERO [Var empty] [nonempty]) v = OK w` by
    (simp[Abbr `w`, step_inst_base_def, mk_inst_def, exec_pure1_def] >>
     simp[Abbr `v`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     Cases_on `nv = 0w` >> simp[bool_to_word_def]) >>
  `step_inst_base (mk_inst r MUL [Var data;Var nonempty] [selected]) w =
    OK (update_var selected (mload (w2n a) s * bool_to_word (nv <> 0w)) w)` by
    (irule step_MUL >>
     fs[Abbr `w`, Abbr `v`, Abbr `u`, eval_operand_def,
        lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `t = update_var selected (mload (w2n a) s * bool_to_word (nv <> 0w)) w` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >> simp[run_inst_seq_def]) >>
  qexistsl_tac [`u`,`v`,`w`] >> simp[Abbr `u`, Abbr `v`, Abbr `w`]
QED

Theorem signed_selector_ptr_inst_ok:
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn y = {} /\
  (eval_operand y s = SOME 0w \/ eval_operand y s = SOME 1w) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id MUL [x;y] [z]) s = OK u ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MUL [x;y] [z]) s
Proof
  strip_tac >>
  `taint_ok fn tn (mk_inst id MUL [x;y] [z]) s` by
    metis_tac[convert_mul_selector_right] >>
  `MEM MUL [GT;SLT;SGT;AND;EQ;SIGNEXTEND;SAR;SHR;SHL;MUL;SDIV]` by simp[] >>
  drule_all convert_scalar_run_shape >> strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, allocas_from_def, mk_inst_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
  rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem signed_selector_ghost_update:
  op_taint tn y = {} /\
  step_inst_base (mk_inst id MUL [x;y] [z]) s = OK u ==>
  step_prov PG G (mk_inst id MUL [x;y] [z]) u = DRESTRICT G (COMPL {z}) /\
  step_taint (mk_inst id MUL [x;y] [z]) s u tn =
    (tn with t_var := tn.t_var |+
      (z,if eval_operand y s = SOME 1w then op_taint tn x else {}))
Proof
  strip_tac >>
  `MEM MUL [GT;SLT;SGT;AND;EQ;SIGNEXTEND;SAR;SHR;SHL;MUL;SDIV]` by simp[] >>
  drule_all convert_scalar_run_shape >> strip_tac >>
  `new_site_bytes s u = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, range_bytes_def, out_taint_def, taint_component_equality]
QED

Theorem signed_select_ghost_chain:
  ALL_DISTINCT [len;dp;data;empty;nonempty;selected] /\
  lookup_var len s = SOME nv /\ lookup_var dp s = SOME a /\
  op_taint tn (Var len) = {} /\
  u = update_var data (mload (w2n a) s) s /\
  v = update_var empty (bool_to_word (nv = 0w)) u /\
  w = update_var nonempty (bool_to_word (nv <> 0w)) v /\
  t = update_var selected (mload (w2n a) s * bool_to_word (nv <> 0w)) w ==>
  step_prov PG G (mk_inst k MLOAD [Var dp] [data]) u = DRESTRICT G (COMPL {data}) /\
  step_taint (mk_inst k MLOAD [Var dp] [data]) s u tn =
    (tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a))) /\
  step_prov PG (DRESTRICT G (COMPL {data}))
    (mk_inst l ISZERO [Var len] [empty]) v =
    DRESTRICT G (COMPL {data} INTER COMPL {empty}) /\
  step_taint (mk_inst l ISZERO [Var len] [empty]) u v
    (tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a))) =
    (tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a)) |+ (empty,{})) /\
  step_prov PG (DRESTRICT G (COMPL {data} INTER COMPL {empty}))
    (mk_inst m ISZERO [Var empty] [nonempty]) w =
    DRESTRICT G (COMPL {data} INTER COMPL {empty} INTER COMPL {nonempty}) /\
  step_taint (mk_inst m ISZERO [Var empty] [nonempty]) v w
    (tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a)) |+ (empty,{})) =
    (tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a)) |+
      (empty,{}) |+ (nonempty,{})) /\
  step_prov PG (DRESTRICT G (COMPL {data} INTER COMPL {empty} INTER COMPL {nonempty}))
    (mk_inst r MUL [Var data;Var nonempty] [selected]) t =
    DRESTRICT G (COMPL {data} INTER COMPL {empty} INTER COMPL {nonempty} INTER COMPL {selected}) /\
  step_taint (mk_inst r MUL [Var data;Var nonempty] [selected]) w t
    (tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a)) |+
      (empty,{}) |+ (nonempty,{})) =
    (tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a)) |+
      (empty,{}) |+ (nonempty,{}) |+
      (selected,if nv = 0w then {} else mem_word_taint tn.t_mem (w2n a)))
Proof
  strip_tac >> gvs[] >> fs[lookup_var_def] >>
  simp[step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, range_bytes_def, taint_component_equality,
       new_site_bytes_def, update_var_def, EXTENSION,
       op_taint_def, FLOOKUP_UPDATE, eval_operand_def, lookup_var_def,
       SF CONJ_ss] >>
  Cases_on `nv = 0w` >> simp[bool_to_word_def, FLOOKUP_DEF, SF CONJ_ss]
QED

Theorem signed_select_uniform_checks:
  ALL_DISTINCT [len;dp;data;empty;nonempty;selected] /\ ~ctx_has_dalloca ctx /\
  lookup_var len s = SOME nv /\ lookup_var dp s = SOME a /\
  ptr_covers G tn dp s 32 /\ op_taint tn (Var len) = {} /\
  op_prov G (Var len) = NONE /\
  run_inst_seq [mk_inst k MLOAD [Var dp] [data];
    mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
    mk_inst r MUL [Var data;Var nonempty] [selected]] s = OK t ==>
  !q. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst k MLOAD [Var dp] [data];
     mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
     mk_inst r MUL [Var data;Var nonempty] [selected]] (s with vs_inst_idx := q)
    (DRESTRICT G (COMPL {data} INTER COMPL {empty} INTER COMPL {nonempty} INTER COMPL {selected}))
    (tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a)) |+
      (empty,{}) |+ (nonempty,{}) |+
      (selected,if nv = 0w then {} else mem_word_taint tn.t_mem (w2n a)))
Proof
  strip_tac >> drule_all signed_select_run_endpoint >> strip_tac >>
  drule_all signed_select_ghost_chain >> strip_tac >>
  gvs[] >> fs[op_taint_def] >> gen_tac >>
  simp[inst_seq_ptr_def, unsigned_step_cursor, is_terminator_def, exec_result_map_def] >>
  conj_tac
  >- (irule ptr_inst_ok_mload >> simp[eval_operand_def]) >>
  conj_tac
  >- (irule iszero_ptr_inst_ok >>
      simp[op_taint_def, FLOOKUP_UPDATE, allocas_from_def] >>
      qexists_tac `(update_var empty (bool_to_word (nv = 0w))
        (update_var data (mload (w2n a) s) s)) with vs_inst_idx := SUC q` >>
      simp[unsigned_step_cursor, is_terminator_def, exec_result_map_def]) >>
  conj_tac
  >- (irule iszero_ptr_inst_ok >>
      simp[op_taint_def, FLOOKUP_UPDATE, allocas_from_def] >>
      qexists_tac `(update_var nonempty (bool_to_word (nv <> 0w))
        (update_var empty (bool_to_word (nv = 0w))
          (update_var data (mload (w2n a) s) s))) with vs_inst_idx := SUC (SUC q)` >>
      simp[unsigned_step_cursor, is_terminator_def, exec_result_map_def]) >>
  irule signed_selector_ptr_inst_ok >>
  simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE,
       eval_operand_def, lookup_var_def, update_var_def, bool_to_word_def] >>
  reverse conj_tac >- (Cases_on `nv = 0w` >> simp[bool_to_word_def]) >>
  qexists_tac `(update_var selected (mload (w2n a) s * bool_to_word (nv <> 0w))
    (update_var nonempty (bool_to_word (nv <> 0w))
      (update_var empty (bool_to_word (nv = 0w))
        (update_var data (mload (w2n a) s) s)))) with vs_inst_idx := SUC (SUC (SUC q))` >>
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem signed_select_fixed_frame:
  ALL_DISTINCT [len;dp;data;empty;nonempty;selected] /\ ~ctx_has_dalloca ctx /\
  lookup_var len s = SOME (n2w n) /\ n <= 32 /\ lookup_var dp s = SOME a /\
  ptr_covers G tn dp s 32 /\ op_prov G (Var len) = NONE /\
  op_taint tn (Var len) = {} /\
  run_inst_seq [mk_inst k MLOAD [Var dp] [data];
    mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
    mk_inst r MUL [Var data;Var nonempty] [selected]] s = OK t ==>
  ?H th.
    (!q. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst k MLOAD [Var dp] [data];
       mk_inst l ISZERO [Var len] [empty]; mk_inst m ISZERO [Var empty] [nonempty];
       mk_inst r MUL [Var data;Var nonempty] [selected]] (s with vs_inst_idx := q) H th) /\
    op_prov H (Var selected) = NONE /\
    op_taint th (Var selected) = (if n = 0 then {} else mem_word_taint tn.t_mem (w2n a)) /\
    t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_current_bb = s.vs_current_bb /\
    t = s with vs_vars := t.vs_vars /\
    (!p. ~MEM p [data;empty;nonempty;selected] ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all signed_select_uniform_checks >> strip_tac >>
  drule_all signed_select_run_endpoint >> strip_tac >>
  `n < dimword(:256)` by (simp[dimword_def] >> decide_tac) >>
  `((n2w n : 256 word) = 0w) <=> n = 0` by
    simp[wordsTheory.n2w_11, LESS_MOD] >>
  qexistsl_tac [`DRESTRICT G (COMPL {data} INTER COMPL {empty} INTER COMPL {nonempty} INTER COMPL {selected})`,
    `tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a)) |+
      (empty,{}) |+ (nonempty,{}) |+
      (selected,if n = 0 then {} else mem_word_taint tn.t_mem (w2n a))`] >>
  conj_tac >- metis_tac[] >>
  gvs[] >> simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def,
    FLOOKUP_UPDATE, update_var_def, lookup_var_def] >>
  rpt strip_tac >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem signed_shift_ptr_inst_ok:
  op_prov G bits = NONE /\ op_prov G data = NONE /\
  op_taint tn bits = {} /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id SAR [bits;data] [out]) s = OK u ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id SAR [bits;data] [out]) s
Proof
  strip_tac >>
  `MEM SAR [GT;SLT;SGT;AND;EQ;SIGNEXTEND;SAR;SHR;SHL;MUL;SDIV]` by simp[] >>
  drule_all convert_scalar_run_shape >> strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       allocas_from_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
  rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem signed_shift_ghost_update:
  eval_operand bits s = SOME k /\ op_taint tn bits = {} /\
  step_inst_base (mk_inst id SAR [bits;data] [out]) s = OK u ==>
  step_taint (mk_inst id SAR [bits;data] [out]) s u tn =
    (tn with t_var := tn.t_var |+ (out,shift_taint SAR (w2n k) (op_taint tn data)))
Proof
  strip_tac >>
  `MEM SAR [GT;SLT;SGT;AND;EQ;SIGNEXTEND;SAR;SHR;SHL;MUL;SDIV]` by simp[] >>
  drule_all convert_scalar_run_shape >> strip_tac >>
  `new_site_bytes s u = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, range_bytes_def, out_taint_def, taint_component_equality]
QED

Theorem signed_normalize_ghost_chain:
  ALL_DISTINCT [len;data;sub;bits;dst] /\
  lookup_var len s = SOME nv /\ lookup_var data s = SOME dw /\
  op_prov G (Var len) = NONE /\ op_prov G (Var data) = NONE /\
  op_taint tn (Var len) = {} /\
  u = update_var sub (32w-nv) s /\
  v = update_var bits ((32w-nv)*8w) u /\
  t = update_var dst (word_asr dw (w2n ((32w-nv)*8w))) v /\
  step_inst_base (mk_inst j SUB [Lit 32w;Var len] [sub]) s = OK u /\
  step_inst_base (mk_inst k MUL [Var sub;Lit 8w] [bits]) u = OK v /\
  step_inst_base (mk_inst l SAR [Var bits;Var data] [dst]) v = OK t ==>
  step_prov PG G (mk_inst j SUB [Lit 32w;Var len] [sub]) u =
    DRESTRICT G (COMPL {sub}) /\
  step_taint (mk_inst j SUB [Lit 32w;Var len] [sub]) s u tn =
    (tn with t_var := tn.t_var |+ (sub,{})) /\
  step_prov PG (DRESTRICT G (COMPL {sub}))
    (mk_inst k MUL [Var sub;Lit 8w] [bits]) v =
    DRESTRICT G (COMPL {sub} INTER COMPL {bits}) /\
  step_taint (mk_inst k MUL [Var sub;Lit 8w] [bits]) u v
    (tn with t_var := tn.t_var |+ (sub,{})) =
    (tn with t_var := tn.t_var |+ (sub,{}) |+ (bits,{})) /\
  step_prov PG (DRESTRICT G (COMPL {sub} INTER COMPL {bits}))
    (mk_inst l SAR [Var bits;Var data] [dst]) t =
    DRESTRICT G (COMPL {sub} INTER COMPL {bits} INTER COMPL {dst}) /\
  step_taint (mk_inst l SAR [Var bits;Var data] [dst]) v t
    (tn with t_var := tn.t_var |+ (sub,{}) |+ (bits,{})) =
    (tn with t_var := tn.t_var |+ (sub,{}) |+ (bits,{}) |+
       (dst,shift_taint SAR (w2n ((32w-nv)*8w)) (op_taint tn (Var data))))
Proof
  strip_tac >>
  `op_prov G (Lit 32w) = NONE /\ op_taint tn (Lit 32w) = {}` by
    simp[op_prov_def, op_taint_def] >>
  gvs[] >> fs[op_prov_def, op_taint_def, lookup_var_def] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, range_bytes_def, taint_component_equality,
       new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION,
       op_taint_def, FLOOKUP_UPDATE, eval_operand_def, lookup_var_def,
       SF CONJ_ss] >>
  simp[op_prov_def, FAPPLY_FUPDATE_THM]
QED

Theorem signed_normalize_uniform_checks:
  ALL_DISTINCT [len;data;sub;bits;dst] /\ ~ctx_has_dalloca ctx /\
  lookup_var len s = SOME nv /\ lookup_var data s = SOME dw /\
  op_prov G (Var len) = NONE /\ op_prov G (Var data) = NONE /\
  op_taint tn (Var len) = {} /\
  u = update_var sub (32w-nv) s /\
  v = update_var bits ((32w-nv)*8w) u /\
  t = update_var dst (word_asr dw (w2n ((32w-nv)*8w))) v /\
  step_inst_base (mk_inst j SUB [Lit 32w;Var len] [sub]) s = OK u /\
  step_inst_base (mk_inst k MUL [Var sub;Lit 8w] [bits]) u = OK v /\
  step_inst_base (mk_inst l SAR [Var bits;Var data] [dst]) v = OK t ==>
  !q. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst j SUB [Lit 32w;Var len] [sub];
     mk_inst k MUL [Var sub;Lit 8w] [bits];
     mk_inst l SAR [Var bits;Var data] [dst]] (s with vs_inst_idx := q)
    (DRESTRICT G (COMPL {sub} INTER COMPL {bits} INTER COMPL {dst}))
    (tn with t_var := tn.t_var |+ (sub,{}) |+ (bits,{}) |+
      (dst,shift_taint SAR (w2n ((32w-nv)*8w)) (op_taint tn (Var data))))
Proof
  strip_tac >>
  drule_all signed_normalize_ghost_chain >> disch_then (qspec_then `PG` strip_assume_tac) >>
  gvs[] >> gen_tac >>
  simp[inst_seq_ptr_def, unsigned_step_cursor, is_terminator_def,
       exec_result_map_def] >>
  conj_tac
  >- (irule unsigned_sub_ptr_inst_ok >>
      simp[op_prov_def, op_taint_def] >>
      qexists_tac `32w-nv` >>
      simp[unsigned_step_cursor, is_terminator_def,
           exec_result_map_def] >> simp[update_var_def]) >>
  conj_tac
  >- (irule convert_scalar_ptr_inst_ok >>
      simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
      qexists_tac `(update_var bits ((32w-nv)*8w) (update_var sub (32w-nv) s))
        with vs_inst_idx := SUC q` >>
      simp[unsigned_step_cursor, is_terminator_def,
           exec_result_map_def]) >>
  irule signed_shift_ptr_inst_ok >>
  simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
  reverse conj_tac >- fs[op_prov_def] >>
  qexists_tac `(update_var dst (word_asr dw (w2n ((32w-nv)*8w)))
    (update_var bits ((32w-nv)*8w) (update_var sub (32w-nv) s)))
    with vs_inst_idx := SUC (SUC q)` >>
  simp[unsigned_step_cursor, is_terminator_def, exec_result_map_def]
QED

Theorem signed_normalize_run_endpoint:
  ALL_DISTINCT [len;data;sub;bits;dst] /\ lookup_var len s = SOME nv /\
  run_inst_seq [mk_inst j SUB [Lit 32w;Var len] [sub];
    mk_inst k MUL [Var sub;Lit 8w] [bits];
    mk_inst l SAR [Var bits;Var data] [dst]] s = OK t ==>
  ?dw u v.
    lookup_var data s = SOME dw /\
    u = update_var sub (32w-nv) s /\
    v = update_var bits ((32w-nv)*8w) u /\
    t = update_var dst (word_asr dw (w2n ((32w-nv)*8w))) v /\
    step_inst_base (mk_inst j SUB [Lit 32w;Var len] [sub]) s = OK u /\
    step_inst_base (mk_inst k MUL [Var sub;Lit 8w] [bits]) u = OK v /\
    step_inst_base (mk_inst l SAR [Var bits;Var data] [dst]) v = OK t
Proof
  strip_tac >>
  qabbrev_tac `u = update_var sub (32w-nv) s` >>
  qabbrev_tac `v = update_var bits ((32w-nv)*8w) u` >>
  `step_inst_base (mk_inst j SUB [Lit 32w;Var len] [sub]) s = OK u` by
    (simp[Abbr `u`] >> irule step_SUB >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst k MUL [Var sub;Lit 8w] [bits]) u = OK v` by
    (simp[Abbr `v`] >> irule step_MUL >>
     simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  Cases_on `lookup_var data s`
  >- (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
      simp[run_inst_seq_def] >>
      simp[step_inst_base_opcode_eqs, exec_pure2_def] >>
      fs[Abbr `v`, Abbr `u`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE]) >>
  rename1 `lookup_var data s = SOME dw` >>
  `step_inst_base (mk_inst l SAR [Var bits;Var data] [dst]) v =
    OK (update_var dst (word_asr dw (w2n ((32w-nv)*8w))) v)` by
    (irule step_SAR >>
     fs[Abbr `v`, Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `t = update_var dst (word_asr dw (w2n ((32w-nv)*8w))) v` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >> simp[run_inst_seq_def]) >>
  qexistsl_tac [`dw`,`u`,`v`] >> simp[Abbr `u`, Abbr `v`]
QED

Theorem signed_normalize_fixed_frame:
  ALL_DISTINCT [len;data;sub;bits;dst] /\ ~ctx_has_dalloca ctx /\
  lookup_var len s = SOME (n2w n) /\ n <= 32 /\
  op_prov G (Var len) = NONE /\ op_prov G (Var data) = NONE /\
  op_taint tn (Var len) = {} /\
  (n = 0 ==> op_taint tn (Var data) = {}) /\
  (!i. i IN op_taint tn (Var data) ==> n <= i /\ i < 32) /\
  run_inst_seq [mk_inst j SUB [Lit 32w;Var len] [sub];
    mk_inst k MUL [Var sub;Lit 8w] [bits];
    mk_inst l SAR [Var bits;Var data] [dst]] s = OK t ==>
  ?H th.
    (!q. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst j SUB [Lit 32w;Var len] [sub];
       mk_inst k MUL [Var sub;Lit 8w] [bits];
       mk_inst l SAR [Var bits;Var data] [dst]] (s with vs_inst_idx := q) H th) /\
    op_prov H (Var dst) = NONE /\ op_taint th (Var dst) = {} /\
    op_prov H (Var bits) = NONE /\ op_taint th (Var bits) = {} /\
    eval_operand (Var bits) t = SOME (n2w (8*(32-n))) /\
    t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_current_bb = s.vs_current_bb /\
    t = s with vs_vars := t.vs_vars /\
    (!p. ~MEM p [sub;bits;dst] ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all signed_normalize_run_endpoint >> strip_tac >>
  drule_all signed_normalize_uniform_checks >> strip_tac >>
  drule_all unsigned_shift_count_word >> strip_tac >>
  `shift_taint SAR (8*(32-n)) (op_taint tn (Var data)) = {}` by
    (Cases_on `n = 0`
     >- simp[shift_taint_def, EXTENSION] >>
     irule partial_word_sar_clean >> simp[] >> decide_tac) >>
  qexistsl_tac [`DRESTRICT G (COMPL {sub} INTER COMPL {bits} INTER COMPL {dst})`,
    `tn with t_var := tn.t_var |+ (sub,{}) |+ (bits,{}) |+ (dst,{})`] >>
  conj_tac >- metis_tac[] >>
  gvs[] >> simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def,
    FLOOKUP_UPDATE, update_var_def, lookup_var_def, eval_operand_def] >>
  rpt strip_tac >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED
