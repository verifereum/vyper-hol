(* The decoder's length load and payload address, before any guard. *)
Theory abiDecodePtrHeaderLoad
Ancestors
  assignTuplePtrLoadStep typedCopyPtr venomExecSemantics venomInst emitHelper
  exprSimAccounts freshWrites fragGasPathPtr fragGasSeqPtr
  abiDecodeStaticProps bodyPtrDefs emitHelperProps exprLoweringProps compileEnv fragExec venomState ptrDiscipline stateFrame words arithmetic

Theorem abi_decode_header_load_path_ptr:
  emit_op MLOAD [Var p] sa = (len,sm) /\
  emit_op ADD [Var p; Lit 32w] sm = (src,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var p s = SOME w /\ not_fresh_at sa p /\
  ptr_covers G tn p s (32+n) /\
  w2n w + 32+n < dimword (:256) /\
  (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tn.t_mem) ==>
  ?t G' tn' q r.
    src = Var q /\ len = Var r /\
    not_fresh_at sb q /\ not_fresh_at sb r /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    run_inst_seq (emitted_insts sa sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    eval_operand len t = SOME (mload (w2n w) s) /\
    op_prov G' len = NONE /\ op_taint tn' len = {} /\
    lookup_var q t = SOME (w+32w) /\ ptr_covers G' tn' q t n /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  drule_all fn_has_code_split >> strip_tac >>
  `ptr_covers G tn p s 32` by
    (fs[ptr_covers_def] >> qexistsl_tac [`w`, `b`, `sz'`] >> simp[]) >>
  `!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn.t_mem` by
    (gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  `!out. ptr_inst_ok D 0 0 ctx func G tn
      (mk_inst sa.cs_next_id MLOAD [Var p] [out]) s` by
    (gen_tac >> irule ptr_inst_ok_mload >> simp[]) >>
  `!out. step_inst_base (mk_inst sa.cs_next_id MLOAD [Var p] [out]) s =
      OK (update_var out (mload (w2n w) s) s)` by
    simp[step_inst_base_def, mk_inst_def, exec_read1_def, eval_operand_def] >>
  drule_all (emit_op_zero_path_ptr |> Q.INST [`opc` |-> `MLOAD`]
    |> SRULE [is_terminator_def]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `len = Var r` >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK u)` >>
  `lookup_var p u = SOME w /\ op_taint tm (Var p) = {}` by
    suspend "input" >>
  `?site. FLOOKUP H p = SOME site` by suspend "site" >>
  `~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts` by suspend "cursor" >>
  `!out. ptr_inst_ok D 0 0 ctx func H tm
      (mk_inst sm.cs_next_id ADD [Var p; Lit 32w] [out]) u` by
    (gen_tac >> irule ptr_inst_ok_copy_len_binop >>
     simp[eval_operand_def, op_taint_def]) >>
  `!out. step_inst_base (mk_inst sm.cs_next_id ADD [Var p; Lit 32w] [out]) u =
      OK (update_var out (w+32w) u)` by
    simp[step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  drule_all (emit_op_zero_path_ptr |> Q.INST [`opc` |-> `ADD`, `PG` |-> `PG`]
    |> SRULE [is_terminator_def]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `src = Var q` >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG H tm u 0 G' tn' (OK t)` >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  qexistsl_tac [`t`, `G'`, `tn'`, `q`, `r`] >>
  asm_rewrite_tac[] >> suspend "outputs"
QED

Resume abi_decode_header_load_path_ptr[input]:
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `p <> r` by
    (strip_tac >> gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  `op_taint tn (Var p) = {}` by fs[ptr_covers_def] >>
  fs[Abbr `u`, Abbr `tm`, update_var_def, lookup_var_def,
       step_taint_def, set_var_taint_def, op_taint_def, mk_inst_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED
Resume abi_decode_header_load_path_ptr[site]:
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `p <> r` by
    (strip_tac >> gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  fs[Abbr `H`, step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
     finite_mapTheory.FLOOKUP_DRESTRICT, ptr_covers_def] >> metis_tac[]
QED
Resume abi_decode_header_load_path_ptr[cursor]:
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  simp[Abbr `u`, update_var_def]
QED
Resume abi_decode_header_load_path_ptr[outputs]:
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `r <> q` by gvs[ASCIInumbersTheory.toString_inj] >>
  `p <> r /\ p <> q` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  `not_fresh_at sb q /\ not_fresh_at sb r` by
    gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  asm_rewrite_tac[] >>
  conj_tac >- suspend "sequence" >>
  conj_tac >- suspend "raw" >>
  conj_tac >- simp[Abbr `t`, Abbr `u`, eval_operand_def,
                         update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- suspend "len_prov" >>
  conj_tac >- suspend "len_taint" >>
  conj_tac >- simp[Abbr `t`, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- suspend "coverage" >>
  `tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by
    suspend "taint_frame" >>
  `!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)` by suspend "old" >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  simp[Abbr `t`, Abbr `u`, update_var_def, state_frame_def]
QED

Resume abi_decode_header_load_path_ptr[raw]:
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  qpat_assum `lookup_var p s = SOME w`
    (assume_tac o REWRITE_RULE [lookup_var_def]) >>
  gvs[] >> simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
       exec_read1_def, exec_pure2_def, eval_operand_def,
       Abbr `t`, Abbr `u`, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  qpat_x_assum `s.vs_inst_idx = _` (SUBST1_TAC o SYM) >> simp[]
QED
Resume abi_decode_header_load_path_ptr[len_prov]:
  simp[Abbr `G'`, copy_len_binop_ghost_frame, op_prov_def,
       Abbr `H`, step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       finite_mapTheory.FLOOKUP_DRESTRICT]
QED
Resume abi_decode_header_load_path_ptr[len_taint]:
  simp[Abbr `tn'`, copy_len_binop_ghost_frame, Abbr `tm`,
       mload_ghost_clean, eval_operand_def]
QED
Resume abi_decode_header_load_path_ptr[coverage]:
  `w2n (w+32w) = w2n w+32` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  `FLOOKUP G p = SOME site` by
    (qpat_x_assum `FLOOKUP H p = SOME site` mp_tac >>
     simp[Abbr `H`, step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
          finite_mapTheory.FLOOKUP_DRESTRICT]) >>
  `FLOOKUP G' q = SOME site` by simp[Abbr `G'`, add_source_site_ptr] >>
  `op_taint tn' (Var q) = {}` by
    simp[Abbr `tn'`, copy_len_binop_ghost_frame] >>
  `lookup_var q t = SOME (w+32w)` by
    simp[Abbr `t`, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  fs[ptr_covers_def] >> gvs[] >> decide_tac
QED
Resume abi_decode_header_load_path_ptr[old]:
  gen_tac >> strip_tac >>
  `x <> r /\ x <> q` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  simp[Abbr `t`, Abbr `u`, Abbr `G'`, Abbr `tn'`,
       copy_len_binop_ghost_frame, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[Abbr `H`, Abbr `tm`, step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, op_taint_def, mk_inst_def,
       finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT]
QED
Resume abi_decode_header_load_path_ptr[taint_frame]:
  simp[Abbr `tn'`, copy_len_binop_ghost_frame, Abbr `tm`,
       mload_ghost_clean, eval_operand_def] >>
  simp[step_taint_def, imm_taint_def, mk_inst_def]
QED

Resume abi_decode_header_load_path_ptr[sequence]:
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  simp[inst_seq_ptr_def, Abbr `u`, Abbr `H`, Abbr `tm`,
       Abbr `t`, Abbr `G'`, Abbr `tn'`] >>
  gvs[]
QED

Finalise abi_decode_header_load_path_ptr
