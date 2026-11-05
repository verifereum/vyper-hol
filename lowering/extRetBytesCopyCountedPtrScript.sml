Theory extRetBytesCopyCountedPtr
Ancestors
  extRetScalarCopyCountedPtr extRetCopyCountedPtr typedCopyPtr
  fragGasSeqPtr fragGasPathPtr fragExec fragExecPtr
  venomExecSemantics venomInstProofs venomInst venomState
  ptrSafeRun ptrDiscipline bodyPtrDefs finite_map context compileEnv emitHelper
  arithmetic

(* An emitted, nonterminating, non-GAS instruction is one zero-count edge.
   The semantic and pointer premises are discharged for each concrete opcode
   below; this is not a conversion from a fixed-run fragment. *)
Theorem emitted_step_counted_ptr:
  fn_has_code sa sb fn /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
  ~is_terminator inst.inst_opcode /\
  ptr_inst_ok D lo 0 ctx fn G tn inst s /\
  step_inst_base inst s = OK t ==>
  gas_path_ptr D lo ctx fn PG G tn s 0
    (step_prov PG G inst t) (step_taint inst s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all straight_line_ptr_edge >> simp[] >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >>
  simp[] >> metis_tac[step_preserves_halted, step_inst_non_invoke]
QED

Theorem emit_copy_len_binop_counted_ptr:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  emit_op opc [left;right] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (f a b) /\ op_taint tnf (Var out) = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc [left;right] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  `opc <> GAS /\ opc <> INVOKE /\ ~is_terminator opc` by
    gvs[is_terminator_def] >>
  qabbrev_tac `t = update_var out (f a b) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id opc [left;right] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id opc [left;right] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (qunabbrev_tac `Gf` >> qunabbrev_tac `tnf` >>
     irule emitted_step_counted_ptr >>
     simp[mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (gvs[] >> pure_once_rewrite_tac[step_inst_base_def] >>
        simp[mk_inst_def, exec_pure2_def, Abbr `t`]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_copy_len_binop) >> metis_tac[]) >>
  gvs[] >> simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[Abbr `tnf`, Abbr `Gf`,
       copy_len_binop_ghost_frame |> SPEC_ALL |> Q.INST [`opc` |-> `ADD`] |> SRULE [],
       copy_len_binop_ghost_frame |> SPEC_ALL |> Q.INST [`opc` |-> `AND`] |> SRULE []] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[copy_len_binop_ghost_frame, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem emit_mload_clean_counted_ptr:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (mload (w2n a) s) /\ op_taint tnf (Var out) = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MLOAD [Var src] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `t = update_var out (mload (w2n a) s) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id MLOAD [Var src] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (qunabbrev_tac `Gf` >> qunabbrev_tac `tnf` >>
     irule emitted_step_counted_ptr >> simp[mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (pure_once_rewrite_tac[step_inst_base_def] >>
        simp[mk_inst_def, exec_read1_def, eval_operand_def, Abbr `t`]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mload) >> simp[]) >>
  `op_taint tnf (Var out) = {} /\ tnf.t_mem = tn.t_mem /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans` by
    (simp[Abbr `tnf`, Abbr `t`] >> irule mload_ghost_clean >>
     simp[eval_operand_def]) >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[Abbr `Gf`, Abbr `tnf`, step_prov_def, set_prov_def,
       out_prov_def, step_taint_def, set_var_taint_def, mk_inst_def,
       op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED
