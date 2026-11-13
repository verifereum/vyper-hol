(* Counted arithmetic for the destination offset, including offset zero. *)
Theory bodyPtrMakeArrayAdd
Ancestors
  typedCopyPtr fragGasSeqPtr fragGasPathPtr emitHelper exprLoweringProps
  venomInst venomExecSemantics venomState context compileEnv loweringStateRelDefs

Theorem clean_binop_ptr_path:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id opc [left;right] [out]) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [left;right] [out])
      (update_var out (f a b) s))
    (step_taint (mk_inst id opc [left;right] [out]) s
      (update_var out (f a b) s) tn)
    (OK ((update_var out (f a b) s) with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [left;right] [out])
      (update_var out (f a b) s))
    (step_taint (mk_inst id opc [left;right] [out]) s
      (update_var out (f a b) s) tn)
    (OK ((update_var out (f a b) s) with
      vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id opc [left;right] [out]`,
                     `lo` |-> `0`,
                     `u` |-> `update_var out ((f : 256 word -> 256 word -> 256 word) a b) s`] straight_line_ptr_edge) >>
     gvs[] >>
     simp[mk_inst_def, is_terminator_def, ptr_inst_ok_copy_len_binop,
          Once step_inst_base_def, exec_pure2_def]) >>
  `~((update_var out (f a b) s) with
       vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[update_var_def] >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem emit_clean_binop_ptr_path:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  emit_op opc [left;right] sa = (Var out,sb) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id opc [left;right] [out]) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id opc [left;right] [out])
      (update_var out (f a b) s))
    (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
      (update_var out (f a b) s) tn)
    (OK ((update_var out (f a b) s) with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule clean_binop_ptr_path >> simp[]
QED

Theorem emit_binop_old_frame:
  (opc = ADD \/ opc = AND) /\
  emit_op opc [left;right] sa = (Var out,sb) ==>
  (update_var out w s).vs_memory = s.vs_memory /\
  op_taint (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
    (update_var out w s) tn) (Var out) = {} /\
  (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
    (update_var out w s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
    (update_var out w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
    (update_var out w s) tn).t_trans = tn.t_trans /\
  (!p. not_fresh_at sa p ==>
    lookup_var p ((update_var out w s) with
      vs_inst_idx := SUC s.vs_inst_idx) = lookup_var p s /\
    FLOOKUP (step_prov PG G (mk_inst sa.cs_next_id opc [left;right] [out])
      (update_var out w s)) p = FLOOKUP G p /\
    op_taint (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
      (update_var out w s) tn) (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `!p. not_fresh_at sa p ==> p <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  simp[copy_len_binop_ghost_frame, update_var_def] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[copy_len_binop_ghost_frame, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED
