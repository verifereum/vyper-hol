(* Actual unsigned loader boundaries. No signed-residual dependency. *)
Theory bodyPtrSignedConvertUnsignedLoad
Ancestors
  bodyPtrSignedConvertSourceCompile
  bodyPtrSignedConvertConvertEntry
  exprLowering exprLoweringProps compileEnv loweringStateRelDefs emitHelperProps rich_list builtinBytes
  bodyPtrSignedConvertLoad venomState finite_map ptrDiscipline venomInst
  venomExecSemantics codegenRel bodyPtrSignedConvertScalarOps
  fragGasSeqPtr fragGasPathPtr ptrSafeRun venomInstProofs contextCodegenRel

Theorem unsigned_loader_decompose:
  load_bytestring_as_word x SHR sa = ((out,bits),sb) ==>
  ?len dp data sub s1 s2 s3 s4 s5.
    emit_op MLOAD [x] sa = (len,s1) /\
    emit_op ADD [x;Lit 32w] s1 = (dp,s2) /\
    emit_op MLOAD [dp] s2 = (data,s3) /\
    emit_op SUB [Lit 32w;len] s3 = (sub,s4) /\
    emit_op MUL [sub;Lit 8w] s4 = (bits,s5) /\
    emit_op SHR [bits;data] s5 = (out,sb)
Proof
  simp[load_bytestring_as_word_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[]
QED

Theorem unsigned_loader_source_prefix:
  load_bytestring_as_word x SHR sa = ((out,bits),sb) ==>
  ?len dp sm data sub s3 s4 s5.
    compile_bytestring_src x sa = ((len,dp),sm) /\
    emit_op MLOAD [dp] sm = (data,s3) /\
    emit_op SUB [Lit 32w;len] s3 = (sub,s4) /\
    emit_op MUL [sub;Lit 8w] s4 = (bits,s5) /\
    emit_op SHR [bits;data] s5 = (out,sb)
Proof
  strip_tac >> drule unsigned_loader_decompose >> strip_tac >>
  simp[compile_bytestring_src_def, comp_bind_def, comp_return_def] >>
  metis_tac[]
QED

(* Payload loads are safe without requiring the padding to be clean. *)
Theorem mload_counted_tainted_ambient:
  !D ctx fn PG G tn s bb id src out a.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a ==>
    ?G' tn' t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
      t = (update_var out (mload (w2n a) s) s) with
        vs_inst_idx := SUC s.vs_inst_idx /\
      lookup_var out t = SOME (mload (w2n a) s) /\
      op_taint tn' (Var out) = mem_word_taint tn.t_mem (w2n a) /\
      op_prov G' (Var out) = NONE /\
      t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
      tn'.t_imm = tn.t_imm /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = SUC s.vs_inst_idx /\
      t = s with <| vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx |> /\
      (!p. p <> out ==> lookup_var p t = lookup_var p s /\
        FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >>
  drule_all mload_counted_path >> strip_tac >>
  qexistsl_tac [`step_prov PG G (mk_inst id MLOAD [Var src] [out])
    (update_var out (mload (w2n a) s) s)`,
    `step_taint (mk_inst id MLOAD [Var src] [out]) s
    (update_var out (mload (w2n a) s) s) tn`,
    `(update_var out (mload (w2n a) s) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       mload_ambient_frame, op_prov_def, step_prov_def, out_prov_def,
       set_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, imm_taint_def,
       op_taint_def, eval_operand_def, FLOOKUP_UPDATE, out_taint_def,
       mem_taint_def, adopt_reset_def, store_taint_def,
       new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def,
       source_memory_write_ranges_def, FLOOKUP_DEF] >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem unsigned_shift_ptr_inst_ok:
  op_prov G bits = NONE /\ op_prov G data = NONE /\
  op_taint tn bits = {} /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id SHR [bits;data] [out]) s = OK u ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id SHR [bits;data] [out]) s
Proof
  strip_tac >>
  `MEM SHR [GT;SLT;SGT;AND;EQ;SIGNEXTEND;SAR;SHR;SHL;MUL;SDIV]` by simp[] >>
  drule_all convert_scalar_run_shape >> strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       allocas_from_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
  rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem unsigned_shift_ghost_update:
  eval_operand bits s = SOME k /\ op_taint tn bits = {} /\
  step_inst_base (mk_inst id SHR [bits;data] [out]) s = OK u ==>
  step_taint (mk_inst id SHR [bits;data] [out]) s u tn =
    (tn with t_var := tn.t_var |+ (out,shift_taint SHR (w2n k) (op_taint tn data)))
Proof
  strip_tac >>
  `MEM SHR [GT;SLT;SGT;AND;EQ;SIGNEXTEND;SAR;SHR;SHL;MUL;SDIV]` by simp[] >>
  drule_all convert_scalar_run_shape >> strip_tac >>
  `new_site_bytes s u = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, range_bytes_def, out_taint_def, taint_component_equality]
QED

Theorem unsigned_shift_counted_path:
  !D ctx fn PG G tn s bb id bits data out k w.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id SHR [bits;data] [out]) /\
    eval_operand bits s = SOME k /\ eval_operand data s = SOME w /\
    op_prov G bits = NONE /\ op_prov G data = NONE /\ op_taint tn bits = {} ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id SHR [bits;data] [out])
        (update_var out (word_lsr w (w2n k)) s))
      (step_taint (mk_inst id SHR [bits;data] [out]) s
        (update_var out (word_lsr w (w2n k)) s) tn)
      (OK ((update_var out (word_lsr w (w2n k)) s) with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id SHR [bits;data] [out]) s =
     OK (update_var out (word_lsr w (w2n k)) s)` by
    simp[mk_inst_def, step_SHR] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id SHR [bits;data] [out]) s` by
    (irule unsigned_shift_ptr_inst_ok >> simp[] >> metis_tac[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id SHR [bits;data] [out])
      (update_var out (word_lsr w (w2n k)) s))
    (step_taint (mk_inst id SHR [bits;data] [out]) s
      (update_var out (word_lsr w (w2n k)) s) tn)
    (OK ((update_var out (word_lsr w (w2n k)) s) with
      vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[mk_inst_def] >> irule (SRULE [mk_inst_def]
       (Q.INST [`i` |-> `mk_inst id SHR [bits;data] [out]`]
         straight_line_ptr_edge)) >>
     simp[GSYM mk_inst_def, is_terminator_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  pure_rewrite_tac [arithmeticTheory.ADD_CLAUSES] >>
  disch_then irule >> simp[gas_path_ptr_rules, update_var_def]
QED

Theorem unsigned_shift_counted_clean_ambient:
  !D ctx fn PG G tn s bb id bits data out k w.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id SHR [bits;data] [out]) /\
    eval_operand bits s = SOME k /\ eval_operand data s = SOME w /\
    op_prov G bits = NONE /\ op_prov G data = NONE /\ op_taint tn bits = {} /\
    shift_taint SHR (w2n k) (op_taint tn data) = {} ==>
    ?G' tn' t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
      lookup_var out t = SOME (word_lsr w (w2n k)) /\
      op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
      t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
      tn'.t_imm = tn.t_imm /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = SUC s.vs_inst_idx /\
      t = s with <| vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx |> /\
      (!p. p <> out ==> lookup_var p t = lookup_var p s /\
        FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >>
  drule_all unsigned_shift_counted_path >> strip_tac >>
  `step_inst_base (mk_inst id SHR [bits;data] [out]) s =
     OK (update_var out (word_lsr w (w2n k)) s)` by
    simp[mk_inst_def, step_SHR] >>
  drule_all unsigned_shift_ghost_update >> strip_tac >>
  qexistsl_tac [`step_prov PG G (mk_inst id SHR [bits;data] [out])
    (update_var out (word_lsr w (w2n k)) s)`,
    `step_taint (mk_inst id SHR [bits;data] [out]) s
    (update_var out (word_lsr w (w2n k)) s) tn`,
    `(update_var out (word_lsr w (w2n k)) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- simp[] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def,
       convert_scalar_output_prov, convert_scalar_ghost_frame]
QED

Theorem unsigned_loader_shape_fresh:
  load_bytestring_as_word (Var src) SHR sa = ((out,bits),sb) /\
  not_fresh_at sa src ==>
  ?len dp data sub shift dst.
    out = Var dst /\ bits = Var shift /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id MLOAD [Var src] [len];
       mk_inst (sa.cs_next_id+1) ADD [Var src;Lit 32w] [dp];
       mk_inst (sa.cs_next_id+2) MLOAD [Var dp] [data];
       mk_inst (sa.cs_next_id+3) SUB [Lit 32w;Var len] [sub];
       mk_inst (sa.cs_next_id+4) MUL [Var sub;Lit 8w] [shift];
       mk_inst (sa.cs_next_id+5) SHR [Var shift;Var data] [dst]] /\
    ALL_DISTINCT [src;len;dp;data;sub;shift;dst] /\
    (!p. MEM p [len;dp;data;sub;shift;dst] ==> ~not_fresh_at sa p) /\
    sb.cs_next_var = sa.cs_next_var+6 /\
    sb.cs_current_bb = sa.cs_current_bb
Proof
  strip_tac >> drule unsigned_loader_decompose >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> gvs[] >>
  imp_res_tac emit_op_extends >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`,
    `STRING #"%" (toString (sa.cs_next_var+3))`] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       ASCIInumbersTheory.toString_inj] >>
  fs[same_blocks_def] >>
  qpat_x_assum `not_fresh_at sa src` mp_tac >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED
