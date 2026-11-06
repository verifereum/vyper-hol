(* Region-relative immutable loads use the provenance selected by ADD. *)
Theory immutableRegionLoadPtr
Ancestors
  immutableSeqCursorPtr immutableOffsetPtr stmtAppendStorageRunPtr
  storageCopyBodyPtr exprSimCopy context compileEnv emitHelper emitHelperProps
  exprLoweringProps fragGasSeqPtr ptrDiscipline venomExecSemantics
  venomInst venomState finite_map words list bodyPtrDefs ghostPcTransportPtr
  codegenRel contextCodegenRel immutableCopyExecution exprSimStorageCopy
  instSeqComposePtr

Theorem clean_add_checked_uniform:
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [left;right] [out]] (s with vs_inst_idx := k)
    (step_prov PG G (mk_inst id ADD [left;right] [out])
      (update_var out (a+b) s))
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id ADD [left;right] [out])
     (s with vs_inst_idx := k) =
   OK (update_var out (a+b) (s with vs_inst_idx := k))` by
    simp[storage_copy_add_step] >>
  simp[inst_seq_ptr_def] >> conj_tac
  >- (irule append_scalar_inst_check >> simp[update_var_def] >> metis_tac[]) >>
  conj_tac
  >- simp[step_prov_def, out_prov_def] >>
  sym_tac >> irule scalar_add_taint >> simp[update_var_def]
QED

Theorem emit_add_runtime_frame:
  emit_op ADD [left;right] sa = (r,sb) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  ?out. r = Var out /\
    emitted_insts sa sb = [mk_inst sa.cs_next_id ADD [left;right] [out]] /\
    not_fresh_at sb out /\ (!x. not_fresh_at sa x ==> x <> out) /\
    copy_runtime_frame sa s sb (update_var out (a+b) s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >> simp[] >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_blocks = sa.cs_blocks /\
   sb.cs_next_var = sa.cs_next_var + 1` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  simp[not_fresh_at_def] >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [left;right]
      [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) (a+b) s)` by
    simp[storage_copy_add_step] >>
  simp[copy_runtime_frame_def, same_blocks_def,
       run_inst_seq_def, copy_static_def, update_var_def] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[]) >>
  simp[lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem add_selected_provenance:
  op_prov (step_prov PG G (mk_inst id ADD [left;right] [out]) t) (Var out) =
    first_prov G [left;right]
Proof
  Cases_on `first_prov G [left;right]` >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem emit_add_checked_uniform:
  emit_op ADD [left;right] sa = (r,sb) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx ==>
  ?out Gf tf. r = Var out /\
    copy_runtime_frame sa s sb (update_var out (a+b) s) /\
    copy_old_operand sb r /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    op_prov Gf r = first_prov G [left;right] /\ op_taint tf r = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all emit_add_runtime_frame >> strip_tac >>
  qexistsl [`out`,
    `step_prov PG G (mk_inst sa.cs_next_id ADD [left;right] [out])
      (update_var out (a+b) s)`, `tn with t_var := tn.t_var |+ (out,{})`] >>
  simp[copy_old_operand_def, clean_add_checked_uniform, add_selected_provenance,
       op_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> out` by metis_tac[] >> simp[scalar_step_old_prov]
QED

Theorem emit_add_covered_uniform:
  emit_op ADD [left;right] sa = (r,sb) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  first_prov G [left;right] = SOME (lo,sz) /\
  lo <= w2n (a+b) /\ w2n (a+b) + n <= lo + sz /\
  ~ctx_has_dalloca ctx ==>
  ?out Gf tf. r = Var out /\
    copy_runtime_frame sa s sb (update_var out (a+b) s) /\
    copy_old_operand sb r /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    ptr_covers Gf tf out (update_var out (a+b) s) n /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all emit_add_checked_uniform >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
  qexistsl [`out`,`Gf`,`tf`] >>
  gvs[ptr_covers_def, op_prov_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem compile_imm_load_word_region_checked:
  compile_imm_load_word T (SOME region) op sa = (r,sb) /\
  eval_operand op s = SOME a /\ eval_operand region s = SOME b /\
  op_taint tn op = {} /\ op_taint tn region = {} /\
  first_prov G [op;region] = SOME (lo,sz) /\
  lo <= w2n (a+b) /\ w2n (a+b) + 32 <= lo + sz /\
  ~ctx_has_dalloca ctx ==>
  ?t Gf tf.
    copy_runtime_frame sa s sb t /\ copy_old_operand sb r /\
    eval_operand r t = SOME (immutable_copy_read T (a+b) s) /\
    t.vs_memory = s.vs_memory /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    op_prov Gf r = NONE /\
    op_taint tf r = mem_word_taint tn.t_mem (w2n (a+b)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
  simp[compile_imm_load_word_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >>
  drule_all emit_add_covered_uniform >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  gvs[] >>
  `eval_operand (Var out) (update_var out (a+b) s) = SOME (a+b) /\
   op_taint tf (Var out) = {}` by
    gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
        ptr_covers_def] >>
  drule_all (SRULE [] (Q.INST [`ctor` |-> `T`, `op` |-> `Var out`]
    emit_immutable_load_checked)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl [`update_var out' (immutable_copy_read T (a+b) s)
                (update_var out (a+b) s)`,
             `DRESTRICT Gf (COMPL {out'})`, `tf'`] >>
  gvs[immutable_copy_read_def, update_var_def, mload_def] >>
  conj_tac
  >- (irule copy_runtime_frame_trans >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (drule emitted_insts_emit_op >> strip_tac >>
      `emitted_insts sa sb = emitted_insts sa cs' ++ emitted_insts cs' sb` by
        (irule emitted_insts_append >> gvs[copy_runtime_frame_def]) >>
      asm_rewrite_tac[] >> irule inst_seq_ptr_uniform_append >>
      reverse conj_tac
      >- (drule_all emit_add_runtime_frame >> strip_tac >>
          simp[mk_inst_def, is_terminator_def]) >>
      qexistsl [`Gf`,`s with vs_vars := s.vs_vars |+ (out,a+b)`,`tf`] >>
      gvs[copy_runtime_frame_def]) >>
  rpt strip_tac >>
  `not_fresh_at cs' x` by
    (gvs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED
