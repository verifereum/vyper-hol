(* Dependency-light compiler shape and concrete suffix execution for Concat. *)
Theory exprSimConcatShapeRun
Ancestors
  context compileEnv emitHelper emitHelperProps exprLoweringProps loweringStateRelDefs
  venomExecSemantics venomState venomInst words list rich_list

Theorem concat_prefix_code:
  !bsz sa buf s1 d s2 ob s3 u s4.
    context$compile_alloc_buffer bsz sa = (buf,s1) /\
    emit_op ADD [buf.buf_operand; Lit 32w] s1 = (d,s2) /\
    context$compile_alloc_buffer 64 s2 = (ob,s3) /\
    emit_void MSTORE [ob.buf_operand; Lit 0w] s3 = (u,s4) ==>
    buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
    d = Var (STRING #"%" (toString (sa.cs_next_var + 1))) /\
    ob.buf_operand = Var (STRING #"%" (toString (sa.cs_next_var + 2))) /\
    s1.cs_next_id = sa.cs_next_id + 1 /\ s1.cs_next_var = sa.cs_next_var + 1 /\
    s2.cs_next_id = sa.cs_next_id + 2 /\ s2.cs_next_var = sa.cs_next_var + 2 /\
    s3.cs_next_id = sa.cs_next_id + 3 /\ s3.cs_next_var = sa.cs_next_var + 3 /\
    s4.cs_next_id = sa.cs_next_id + 4 /\ s4.cs_next_var = sa.cs_next_var + 3 /\
    s4.cs_current_bb = sa.cs_current_bb /\ s4.cs_blocks = sa.cs_blocks /\
    emitted_insts sa s1 =
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w bsz)]
         [STRING #"%" (toString sa.cs_next_var)]] /\
    emitted_insts s1 s2 =
      [mk_inst (sa.cs_next_id + 1) ADD
         [Var (STRING #"%" (toString sa.cs_next_var)); Lit 32w]
         [STRING #"%" (toString (sa.cs_next_var + 1))]] /\
    emitted_insts s2 s3 =
      [mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 64w]
         [STRING #"%" (toString (sa.cs_next_var + 2))]] /\
    emitted_insts s3 s4 =
      [mk_inst (sa.cs_next_id + 3) MSTORE
         [Var (STRING #"%" (toString (sa.cs_next_var + 2))); Lit 0w] []] /\
    emitted_insts sa s4 =
      emitted_insts sa s1 ++ (emitted_insts s1 s2 ++
        (emitted_insts s2 s3 ++ emitted_insts s3 s4)) /\
    s4.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa s4
Proof
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem concat_suffix_code:
  !ov bv sa fo sm u sb.
    emit_op MLOAD [Var ov] sa = (fo, sm) /\
    emit_void MSTORE [Var bv; fo] sm = (u, sb) ==>
    fo = Var (STRING #"%" (toString sa.cs_next_var)) /\
    sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks /\
    sb.cs_next_var = sa.cs_next_var + 1 /\ sb.cs_next_id = sa.cs_next_id + 2 /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id MLOAD [Var ov] [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id + 1) MSTORE
         [Var bv; Var (STRING #"%" (toString sa.cs_next_var))] []] /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  simp[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem concat_suffix_run:
  !ov bv sa fo sm u sb s ow bw.
    emit_op MLOAD [Var ov] sa = (fo, sm) /\
    emit_void MSTORE [Var bv; fo] sm = (u, sb) /\
    lookup_var ov s = SOME ow /\ lookup_var bv s = SOME bw /\
    not_fresh_at sa bv ==>
    run_inst_seq (emitted_insts sa sb) s =
      OK (mstore (w2n bw) (mload (w2n ow) s)
            (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n ow) s) s))
Proof
  rpt strip_tac >>
  drule_all concat_suffix_code >> strip_tac >>
  qpat_x_assum `emitted_insts sa sb = _` SUBST1_TAC >>
  `bv <> (STRING #"%" (toString sa.cs_next_var))` by fs[not_fresh_at_def] >>
  `step_inst_base (mk_inst sa.cs_next_id MLOAD [Var ov]
      [STRING #"%" (toString sa.cs_next_var)]) s =
   OK (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n ow) s) s)` by
    (irule step_MLOAD >> simp[eval_operand_def]) >>
  qabbrev_tac `s' = update_var (STRING #"%" (toString sa.cs_next_var))
      (mload (w2n ow) s) s` >>
  `step_inst_base (mk_inst (sa.cs_next_id + 1) MSTORE
      [Var bv; Var (STRING #"%" (toString sa.cs_next_var))] []) s' =
   OK (mstore (w2n bw) (mload (w2n ow) s) s')` by
    (irule step_MSTORE >>
     simp[Abbr `s'`, eval_operand_def, lookup_var_update_var]) >>
  simp[run_inst_seq_def]
QED
