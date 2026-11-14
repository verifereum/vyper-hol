(* Occupied bytes only: padding taint is removed by the right shift. *)
Theory bodyFullConvertBytesWordNormalize
Ancestors
  bodyPtrSignedConvertUnsignedFixed bodyPtrSignedConvertUnsignedLoad
  wordLoadStorePtr bodyPtrSignedConvertScalarOps fragGasSeqPtr
  venomState venomInst venomInstProofs venomExecSemantics finite_map words
  arithmetic pred_set fragExec ptrSafeRun ptrDiscipline instIdxIndep
  emitHelperProps exprLoweringProps codegenRel contextCodegenRel

Theorem normalize_ghost_chain[local]:
  ALL_DISTINCT [len;data;sub;bits;dst] /\
  lookup_var len s = SOME nv /\ lookup_var data s = SOME dw /\
  op_prov G (Var len) = NONE /\ op_prov G (Var data) = NONE /\
  op_taint tn (Var len) = {} /\
  u = update_var sub (32w-nv) s /\
  v = update_var bits ((32w-nv)*8w) u /\
  t = update_var dst (word_lsr dw (w2n ((32w-nv)*8w))) v ==>
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
    (mk_inst l SHR [Var bits;Var data] [dst]) t =
    DRESTRICT G (COMPL {sub} INTER COMPL {bits} INTER COMPL {dst}) /\
  step_taint (mk_inst l SHR [Var bits;Var data] [dst]) v t
    (tn with t_var := tn.t_var |+ (sub,{}) |+ (bits,{})) =
    (tn with t_var := tn.t_var |+ (sub,{}) |+ (bits,{}) |+
       (dst,shift_taint SHR (w2n ((32w-nv)*8w)) (op_taint tn (Var data))))
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

Theorem bytes_word_normalize_fixed_frame:
  ALL_DISTINCT [len;dp;data;sub;bits;dst] /\ ~ctx_has_dalloca ctx /\
  lookup_var len s = SOME (n2w n) /\ n <= 32 /\ lookup_var dp s = SOME a /\
  ptr_covers G tn dp s 32 /\ op_prov G (Var len) = NONE /\
  op_taint tn (Var len) = {} /\
  (!x. w2n a <= x /\ x < w2n a+n ==> x NOTIN tn.t_mem) /\
  run_inst_seq [mk_inst i MLOAD [Var dp] [data];
    mk_inst j SUB [Lit 32w;Var len] [sub];
    mk_inst k MUL [Var sub;Lit 8w] [bits];
    mk_inst l SHR [Var bits;Var data] [dst]] s = OK t ==>
  ?H th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst i MLOAD [Var dp] [data];
       mk_inst j SUB [Lit 32w;Var len] [sub];
       mk_inst k MUL [Var sub;Lit 8w] [bits];
       mk_inst l SHR [Var bits;Var data] [dst]] (s with vs_inst_idx := q) H th) /\
    op_prov H (Var dst) = NONE /\ op_taint th (Var dst) = {} /\
    op_prov H (Var bits) = NONE /\ op_taint th (Var bits) = {} /\
    eval_operand (Var bits) t = SOME (n2w (8*(32-n))) /\
    t.vs_memory = s.vs_memory /\ th.t_mem = tn.t_mem /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_current_bb = s.vs_current_bb /\
    t = s with vs_vars := t.vs_vars /\
    (!p. ~MEM p [data;sub;bits;dst] ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_all bodyPtrSignedConvertUnsignedFixedTheory.unsigned_suffix_run_endpoint >>
  disch_then (qx_choose_then `u` (qx_choose_then `v` (qx_choose_then `w` strip_assume_tac))) >>
  `shift_taint SHR (w2n ((32w-n2w n)*8w:256 word))
      (mem_word_taint tn.t_mem (w2n a)) = {}` by
    (simp[bodyPtrSignedConvertUnsignedFixedTheory.unsigned_shift_count_word] >> irule unsigned_data_window_shift_clean >> simp[]) >>
  qexistsl_tac [`DRESTRICT G (COMPL {data} INTER COMPL {sub} INTER COMPL {bits} INTER COMPL {dst})`,
    `tn with t_var := tn.t_var |+ (data,mem_word_taint tn.t_mem (w2n a)) |+
      (sub,{}) |+ (bits,{}) |+ (dst,{})`] >>
  conj_tac >- (rpt gen_tac >> drule_all bodyPtrSignedConvertUnsignedFixedTheory.unsigned_suffix_uniform_checks >> simp[]) >>
  gvs[] >> simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def,
    FLOOKUP_UPDATE, update_var_def, lookup_var_def, eval_operand_def, bodyPtrSignedConvertUnsignedFixedTheory.unsigned_shift_count_word] >>
  rpt strip_tac >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED
