(* Construct a single enriched compiler witness, never two independent runs.
   This probe retains word_value explicitly: that predicate excludes BytesV.
   Thus is_word_type alone does not extend it to addresses or fixed bytes.
   The residual typed-load obligation is to preserve the same enriched
   outcome using typed_val_to_w256 for those values, rather than val_to_w256;
   no universal typed-word or expression provenance claim is made here. *)
Theory augAssignPtrScalarWitnessProbe
Ancestors
  wordLoadStorePtr augAssignPtrLoad augAssignPtrProvenanceProbe gasSummaryComposePtr bodyPtrDefs
  exprSimNameWord exprSimNameValue exprSimValues stmtFragPtr
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  ptrDiscipline venomInst venomState finite_map loweringSlice venomExecSemantics fragExec
(* This instruction-level helper exposes the actual clearing ghost, in
   contrast to emit_mload_path_ptr's existentially hidden provenance. *)
Theorem emit_mload_explicit_ghost_path:
  emit_op MLOAD [Var p] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME a ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var p] [out])
      (update_var out (mload (w2n a) s) s))
    (step_taint (mk_inst sa.cs_next_id MLOAD [Var p] [out]) s
      (update_var out (mload (w2n a) s) s) tn)
    (OK (update_var out (mload (w2n a) s)
      (s with vs_inst_idx := LENGTH sb.cs_current_insts)))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MLOAD [Var p] [out]]` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id MLOAD [Var p] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id MLOAD [Var p] [out]) s =
    OK (update_var out (mload (w2n a) s) s)` by
    simp[step_inst_base_def, mk_inst_def, exec_read1_def, eval_operand_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all mload_path_ptr >>
  simp[update_var_def, arithmeticTheory.ADD1]
QED

Theorem local_name_enriched_path:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  is_word_type ty /\ lookup_scopes name es.scopes = SOME entry /\
  word_value entry.value /\ emit_op MLOAD [Var p] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    expr_post ctx fn cenv cx (Name ty name) es sa sb s
      (es with gas_obs := []) entry.value (Var out) t /\
    ghost_inv d cenv cx (es with gas_obs := []) H tm t /\
    ghost_kept cenv es sa G tn s H tm /\ op_taint tm (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ op_prov H (Var out) = NONE
Proof
  strip_tac >> drule_all ghost_inv_word_local_inputs >> strip_tac >>
  `!rp. not_fresh_at sa rp ==> rp <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all emit_mload_explicit_ghost_path >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t)` >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `id` |-> `sa.cs_next_id`,
    `arg` |-> `Var p`, `v` |-> `mload (w2n (a:256 word)) s`] load_ambient_frame) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `!rp. not_fresh_at sa rp ==>
     lookup_var rp t = lookup_var rp s /\ FLOOKUP H rp = FLOOKUP G rp /\
     op_taint tm (Var rp) = op_taint tn (Var rp)` by
    (simp[Abbr `H`, Abbr `tm`, Abbr `t`] >> rpt strip_tac >>
     simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`H`, `tm`, `t`] >> simp[] >>
  conj_tac >- (simp[Abbr `t`] >> irule name_word_post >> simp[] >> metis_tac[]) >>
  conj_tac >- (simp[ghost_inv_gas_obs] >> irule ghost_inv_load_frame >>
    qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
    simp[Abbr `H`, Abbr `tm`, Abbr `t`, update_var_def, load_ambient_frame]) >>
  conj_tac >- (simp[ghost_kept_def, Abbr `tm`, load_ambient_frame] >> metis_tac[]) >>
  conj_tac >- (qpat_x_assum `mload _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
    simp[Abbr `tm`, NoAsms] >>
    irule (cj 1 wordLoadStorePtrTheory.mload_ghost_clean) >> simp[eval_operand_def]) >>
  simp[Abbr `t`, update_var_def] >> conj_tac
  >- (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def]) >>
  simp[Abbr `H`, load_result_has_no_provenance]
QED

Theorem local_name_enriched_outcome:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  is_word_type ann /\ lookup_scopes name es.scopes = SOME entry /\
  word_value entry.value /\
  lower_value compile_expr cenv ty (Name ann name) sa = (op,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (bind (eval_expr cx (Name ann name)) (read_result cx)) (es,s,G,tn)
    (\res ee H tm t. ?v. res = INL v /\
      expr_post ctx fn cenv cx (Name ann name) es sa sb s ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee H tm t /\ ptr_val_ok cx ann v op H tm t /\
      (~is_word_type ann ==> ptr_buf_ok cenv (Name ann name) op H t) /\
      ghost_kept cenv es sa G tn s H tm /\ op_prov H op = NONE)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all lower_value_name_word >> strip_tac >>
  `?out. op = Var out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_var_def, fresh_id_def, emit_def] >> metis_tac[]) >> gvs[] >>
  drule_all local_name_enriched_path >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[fragGasPathPtrTheory.gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL entry.value`, `es`, `H`, `tm`, `OK t`] >>
  simp[gasSummaryTheory.gas_explicit_def, ptr_val_ok_def] >>
  gen_tac >>
  qspecl_then [`cx`, `ann`, `name`, `es with gas_obs := tail`, `entry`]
    mp_tac eval_name_word >> simp[] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED
