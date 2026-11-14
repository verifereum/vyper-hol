(* Static-inclusive source outcomes for ordered tuple stores. *)
Theory tupleTargetStoreAbort
Ancestors
  tupleTargetStoreProps tupleTargetStoreRun storageStoreFrame
  stmtSimDefs exprSimDefs loweringStateRelDefs fragGasMode
  stmtLowering emitHelper emitHelperProps exprLoweringProps
  stmtSimAssignStorage compileEnv fragExec
  venomState venomInst vyperInterpreter vyperState vyperValue vyperLookup

Theorem tuple_target_source_outcome:
  !cenv cx es g ty tv v.
    tuple_target_aligned cenv cx g ty tv /\
    tuple_target_layout es.scopes g ty tv v /\ value_has_type tv v ==>
    ?res es1.
      (!tail. assign_tuple_targets cx g v (es with gas_obs := tail) =
        (res, es1 with gas_obs := tail)) /\
      (res = INL () \/
       cx.txn.is_static /\ (!id. g <> BaseTarget (NameTarget id)) /\
       res = INR (Error (RuntimeError "write in static context")))
Proof
  rpt strip_tac >>
  drule_all tuple_target_aligned_source >> strip_tac >>
  qexistsl [`FST (assign_tuple_targets cx g v es)`,
            `SND (assign_tuple_targets cx g v es)`] >>
  conj_tac
  >- (gen_tac >> irule tuple_source_target_gas_obs >> metis_tac[]) >>
  Cases_on `cx.txn.is_static`
  >- (qpat_x_assum `tuple_source_target _ _ _ _` mp_tac >>
      simp[tuple_source_target_def] >> strip_tac >> gvs[]
      >- (drule lookup_scopes_find_containing_scope >> strip_tac >>
          simp[evaluate_def, bind_def, ignore_bind_def, type_check_def,
               assert_def, return_def, get_place_def, get_scopes_def] >>
          simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
               lift_option_type_def, type_check_def, assert_def, lift_sum_def,
               replace_memory_entry_def, evaluate_subscripts_def,
               assign_subscripts_def, set_scopes_def, return_def])
      >- (drule_all tuple_target_toplevel_place >> strip_tac >>
          ntac 3 (simp[Once evaluate_def, bind_def] >> asm_rewrite_tac[]) >>
          simp[write_place_def, write_storage_slot_def, ignore_bind_def,
               bind_def]) >>
      drule_all tuple_target_field_place >> strip_tac >>
      ntac 3 (simp[Once evaluate_def, bind_def] >> asm_rewrite_tac[]) >>
      simp[write_place_def, write_storage_slot_def, ignore_bind_def, bind_def]) >>
  drule_all tuple_source_target_safe >> strip_tac >> simp[]
QED

Theorem tuple_target_static_head_exit:
  !ctx func cenv cx es s g ty tv v op st sf RetQ ee.
    compile_tuple_store_all cenv [ty] [g] [op] st = ((),sf) /\
    tuple_target_aligned cenv cx g ty tv /\
    (!id. g <> BaseTarget (NameTarget id)) /\ value_has_type tv v /\
    eval_operand op s = SOME (typed_val_to_w256 tv v) /\
    local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_has_code st sf func /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ cx.txn.is_static ==>
    ?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  rpt gen_tac >> simp[tuple_target_aligned_def] >> strip_tac >> gvs[]
  >- (drule_all compile_get_target_ptr_toplevel >>
      disch_then (qspec_then `st` assume_tac) >> gvs[] >>
      drule_all tuple_store_word_step >> strip_tac >>
      qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
      gvs[compile_tuple_store_all_def, comp_return_def] >>
      `s.vs_call_ctx.cc_static` by
        fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
      `emit_void (if tr then TSTORE else SSTORE) [Lit (n2w k); op] st = ((),sf)` by
        (Cases_on `tr` >> gvs[compile_store_at_loc_def]) >>
      `eval_operand (Lit (n2w k)) s = SOME (n2w k)` by simp[eval_operand_def] >>
      drule_all storage_emit_static_path >> strip_tac >>
      qexists `Abort ExHalt_abort (halt_state (set_returndata [] s))` >>
      simp[exit_result_def, stmt_exit_def, expr_exit_def]) >>
  Cases_on `emit_op ADD [Lit (n2w k); Lit (n2w (struct_field_offset_slots
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))] st` >>
  rename1 `emit_op ADD _ st = (dst,sp)` >>
  drule_all tuple_target_field_pointer >> strip_tac >>
  drule_all tuple_store_word_step >> strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
  gvs[compile_tuple_store_all_def, comp_return_def] >>
  `cs_extends st sp /\ cs_extends sp sf` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def] >>
     metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND]) >>
  `fn_has_code st sp func /\ fn_has_code sp sf func` by
    metis_tac[fn_has_code_split] >>
  drule_all tuple_field_add_frame_path >> strip_tac >>
  rename1 `stmt_state_rel ctx func cenv cx es mid` >>
  `eval_operand op mid = SOME (typed_val_to_w256 tv v)` by
    (Cases_on `op` >> gvs[eval_operand_def]) >>
  `mid.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `emit_void (if tr then TSTORE else SSTORE) [dst; op] sp = ((),sf)` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def]) >>
  drule_all storage_emit_static_path >> strip_tac >>
  qexists `Abort ExHalt_abort (halt_state (set_returndata [] mid))` >>
  simp[exit_result_def, stmt_exit_def, expr_exit_def] >>
  irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexists `mid` >> simp[]
QED
