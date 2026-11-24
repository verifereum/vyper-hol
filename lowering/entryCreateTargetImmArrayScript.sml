(* First-exit scope for constructor immutable array selection. *)
Theory entryCreateTargetImmArray
Ancestors
  bodyFullTargetImmutableArray entryCreateAdminSequence entryCreatePathScope
  exprSimArrayIndex exprLoweringProps abiEncoderProps emitHelper fragExec
  context compileEnv venomInst entryCreateFocusSpec entryCreateCompletedCut
  bodyFullTargetImmutableArraySelected bodyFullSubscriptLiveImmSelect
  entryCreateAdminAbortScope fragGasOriginPtr gasSummary vyperStorageFootprint
  list arithmetic

Theorem immutable_array_suffix_layout[local]:
  compile_array_subscript arg idx dyn cnt 32 esz sgn
    (compile_ptr_load T imm LocCode) sa = (dst,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts sa sb)
Proof
  Cases_on `dyn` >> Cases_on `sgn` >> Cases_on `imm` >>
  simp[compile_array_subscript_split, compile_ptr_load_def,
       compile_imm_load_word_def, array_elem_ptr_def,
       array_bounds_check_def, array_bounds_valid_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, frag_ids_def]
QED

(* The installed slice cannot contain a CREATE or enter a callee.  This
   cut does not require a successful bounds check. *)
Theorem immutable_array_suffix_cut:
  compile_array_subscript arg idx dyn cnt 32 esz sgn
    (compile_ptr_load T imm LocCode) sn = (dst,sb) /\
  fn_has_code sn sb func /\ create_operand_at sn s ==>
  create_operand_cut sn sb E ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> drule immutable_array_suffix_layout >> strip_tac >>
  irule create_admin_sequence_cut >> fs[EVERY_MEM]
QED

Theorem immutable_array_selected_scope[local]:
  compile_array_subscript arg idx dyn cnt 32 esz sgn
    (compile_ptr_load T imm LocCode) sn = (dst,sb) /\
  fn_has_code sn sb func /\ create_operand_at sn s /\ ~s.vs_halted /\
  ((?raw. run_inst_seq (emitted_insts sn sb) s = OK raw /\
          r = OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts)) \/
   (?raw q. run_inst_seq (emitted_insts sn sb) s = Abort Revert_abort raw /\
            r = Abort Revert_abort q)) /\
  gas_origin_path T explicit ctx func s [] r ==>
  create_operand_full_scope sn sb explicit ctx func s [] r
Proof
  strip_tac >> gvs[] >> drule immutable_array_suffix_layout >> strip_tac
  >- (irule create_admin_sequence_scope >> fs[EVERY_MEM]) >>
  irule create_admin_sequence_abort_scope >>
  fs[EVERY_MEM] >> goal_assum (drule_at Any)
QED

Theorem immutable_target_array_tail_scoped_cut:
  body_inv tops ctx cenv cx /\ cenv.ce_is_ctor /\ cenv.ce_module = NONE /\
  expr_sim_inv cenv cx env ee /\ ee.gas_obs = [] /\
  storage_trace_domain cx st0 ee.storage_trace /\
  FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables NONE imms) id = SOME (itv,iv) /\
  off + type_memory_size itv < dimword (:256) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  compile_array_subscript arg iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0) 32
    (type_memory_size etv) sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) sn = (dst,sb) /\
  eval_operand arg s = SOME (n2w (off+k)) /\ copy_old_operand sn arg /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  eval_operand iop s = SOME iw /\ copy_old_operand sn iop /\
  op_taint tn iop = {} /\ op_prov G iop = NONE /\
  (!l. arg <> Label l /\ iop <> Label l) /\
  i = (if sgn then w2i iw else &(w2n iw)) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    wb_frame cenv es ee sa s0 s /\ ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 sn sb
    (bind (extend_place cx (PlaceR (ImmutablePlace NONE id path))
             (ValueSubscript (IntV i))) get_place) (ee,s,G,tn)
    (\H res fin G' tn' q.
       res = INL (ImmutablePlace NONE id (path ++ [ValueSubscript (IntV i)])) /\
       imm_target_post H ctx func cenv cx es sa sb s0 fin id
         (path ++ [ValueSubscript (IntV i)]) et (dst,SOME LocCode,SOME (ValPT et)) q /\
       q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
       s0.vs_alloca_next <= q.vs_alloca_next /\
       ghost_inv_at (DF H) lo d cenv cx fin G' tn' q /\
       target_ptr_ok cenv (PlaceR (ImmutablePlace NONE id (path ++ [ValueSubscript (IntV i)])))
         (dst,SOME LocCode,SOME (ValPT et)) G' tn' q /\
       op_prov G' dst = NONE /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res fin gt r. expr_exit res r /\ halt_exit H cx fin res r /\
      (ctx_has_dalloca ctx ==> !q. r = Halt q ==> allocas_below_fmp q)) /\
  create_operand_cut sn sb explicit ctx func (cx_tops cx) cx st0
    (bind (extend_place cx (PlaceR (ImmutablePlace NONE id path))
             (ValueSubscript (IntV i))) get_place) (ee,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse conj_tac
  >- (irule immutable_array_suffix_cut >> simp[create_operand_at_def] >>
      goal_assum (drule_at Any) >> simp[]) >>
  mp_tac (BETA_RULE (Q.INST [`observe_result` |-> `\r.
    (?raw. run_inst_seq (emitted_insts sn sb) s = OK raw /\
           r = OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts)) \/
    (?raw q. run_inst_seq (emitted_insts sn sb) s = Abort Revert_abort raw /\
             r = Abort Revert_abort q)`] immutable_target_array_tail_selected_by)) >>
  (impl_tac >-
    (asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
     irule (REWRITE_RULE [wordsTheory.n2w_w2n]
       (Q.INST [`i` |-> `w2n (iw:bytes32)`] live_code_select_joint_ctor_observed)) >>
     simp[] >> qexistsl [`arg`,`cenv.ce_is_ctor`,`iop`,`cenv.ce_imm_alloca`] >>
     fs[AC ADD_ASSOC ADD_COMM, boolTheory.COND_EXPAND_IMP] >>
     rpt strip_tac >> simp[] >> goal_assum (drule_at Any) >> simp[])) >>
  disch_then (qx_choosel_then [`res`,`fin`,`r`,`Gf`,`tnf`] strip_assume_tac) >>
  `gas_origin_path T explicit ctx func s [] r` by
    (`valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     drule_then (strip_assume_tac o CONJUNCT1) gas_origin_ptr_path_projections) >>
  `create_operand_full_scope sn sb explicit ctx func s [] r` by
    (irule immutable_array_selected_scope >> simp[create_operand_at_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> qexistsl [`res`,`fin`,`r`,`Gf`,`tnf`] >>
  simp[gas_explicit_def] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (drule_then strip_assume_tac) >> simp[]
QED
