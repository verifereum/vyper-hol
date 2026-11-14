(* Static-inclusive source outcomes for ordered tuple stores. *)
Theory tupleTargetStoreAbort
Ancestors
  tupleTargetStoreProps tupleTargetStoreRun storageStoreFrame
  stmtSimDefs exprSimDefs loweringStateRelDefs fragGasMode
  stmtLowering emitHelper emitHelperProps exprLoweringProps
  stmtSimAssignStorage compileEnv fragExec loweringSlice freshWrites
  tupleMemoryFrame valueEncoding valueEncodingDefs valueEncodingProps
  list rich_list finite_map tupleAssignParts vyperTyping tupleLocalStoreRun
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

Theorem tuple_source_list_outcome:
  !gs tys tvs vs cenv cx es.
    LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ values_have_types tvs vs /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
      tuple_target_layout es.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) ==>
    ?res es'. !tail.
      assign_tuple_target_list cx gs vs (es with gas_obs := tail) =
        (res,es' with gas_obs := tail)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      qexistsl [`INL ()`, `es`] >> simp[Once evaluate_def, return_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `tys` >- fs[] >> Cases_on `tvs` >- fs[] >>
  Cases_on `vs` >- fs[] >>
  rename1 `values_have_types (tv::tvs1) (v::vs1)` >>
  rename1 `LENGTH (ty::tys1) = LENGTH (tv::tvs1)` >>
  qpat_assum `!i. i < LENGTH (h::gs) ==> _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >> strip_tac >>
  `value_has_type tv v` by fs[value_has_type_def] >>
  drule_all tuple_target_source_outcome >>
  disch_then (qx_choosel_then [`head_res`, `head_es`]
    (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `head_res = INL ()`
  >- (gvs[] >>
      `assign_tuple_targets cx h v (es with gas_obs := []) =
        (INL (),head_es with gas_obs := [])` by simp[] >>
      `tuple_target_layout (es with gas_obs := []).scopes h ty tv v` by simp[] >>
      drule_all tuple_target_assignment_scope_frame >> simp[] >> strip_tac >>
      qpat_x_assum `!tys tvs vs cenv cx es. _`
        (qspecl_then [`tys1`, `tvs1`, `vs1`, `cenv`, `cx`, `head_es`] mp_tac) >>
      (impl_tac
       >- (fs[value_has_type_def] >> rpt strip_tac >>
           drule tuple_target_layout_transport >> disch_tac >>
           qpat_x_assum `!i. _ ==> tuple_target_aligned _ _ _ _ _ /\ _`
             (qspec_then `SUC i` mp_tac) >> simp[])) >>
      disch_then (qx_choosel_then [`res`, `es'`] assume_tac) >>
      qexistsl [`res`, `es'`] >> simp[assign_tuple_target_list_cons] >>
      metis_tac[]) >>
  qpat_x_assum `head_res = INL () \/ _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >> gvs[] >>
  qexistsl [`INR (Error (RuntimeError "write in static context"))`, `head_es`] >>
  simp[assign_tuple_target_list_cons] >> metis_tac[]
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

Theorem tuple_store_targets_outcome:
  !gs m tys tvs vs ops addr b sz ctx func cenv cx es s st st' RetQ.
    compile_tuple_store_all cenv tys gs ops st = ((),st') /\
    LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    (~m ==> EVERY is_word_type tys) /\
    EVERY (\op. ?x. op = Var x) ops /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops /\
    local_ptrs_reserved cenv st /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    (!i. i < LENGTH gs ==>
       ?w. eval_operand (EL i ops) s = SOME w /\
         (if is_word_type (EL i tys) then
            w = typed_val_to_w256 (EL i tvs) (EL i vs)
          else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs)))) /\
    (!i. i < LENGTH gs ==>
       tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
       tuple_target_layout es.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
       type_memory_size (EL i tvs) + 64 < dimword(:256)) /\
    (m ==> (!i. i < LENGTH tys ==>
          evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
          (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)) /\
       b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
       ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
        (?name. local_region cenv es.scopes s name b sz)) /\
       tuple_in_memory vs tvs addr s.vs_memory) /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ stmt_state_rel ctx func cenv cx es s ==>
    ?res es' r.
      (!tail. assign_tuple_target_list cx gs vs (es with gas_obs := tail) =
        (res,es' with gas_obs := tail)) /\
      gas_marked_path F ctx func s 0 r /\
      ((res = INL () /\ ?t. r = OK t /\
        (gs <> [] \/ ~block_is_terminated st ==> ~block_is_terminated st') /\
        stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
        (!c0 e0 sa0 s0. alloca_frame c0 e0 sa0 s0 cenv es s ==>
           alloca_frame c0 e0 sa0 s0 cenv es' t)) \/
       (exit_result r /\ !tail. stmt_exit RetQ (es' with gas_obs := tail) res r))
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_tuple_store_all_def, comp_return_def] >>
      qexistsl [`INL ()`, `es`, `OK s`] >>
      simp[Once evaluate_def, return_def, gas_marked_path_def] >>
      irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `tys` >- fs[] >> Cases_on `tvs` >- fs[] >>
  Cases_on `vs` >- fs[] >> Cases_on `ops` >- fs[] >>
  rename1 `compile_tuple_store_all cenv (ty::tys1) _ (op::ops1) st = _` >>
  rename1 `tuple_val_wf (v::vs1) (tv::tvs1)` >>
  qpat_x_assum `!m tys tvs vs ops addr b sz ctx func cenv cx es s st st' RetQ. _`
    (mk_asm "ih") >>
  qpat_assum `!i. i < LENGTH (h::gs) ==> tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `value_has_type tv v /\ val_wf tv v` by
    (qpat_x_assum `ih :- _` kall_tac >> fs[value_has_type_def, val_wf_def]) >>
  drule_all tuple_target_source_outcome >>
  disch_then (qx_choosel_then [`head_res`, `head_es`] (map_every assume_tac o CONJUNCTS)) >>
  drule_all tuple_target_aligned_compiler >> strip_tac >>
  drule tuple_compiler_target_base >>
  disch_then (qx_choose_then `bt` SUBST_ALL_TAC) >>
  drule tuple_store_base_cons >> strip_tac >>
  qpat_assum `compile_tuple_store_all _ [_] [_] [_] _ = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  qpat_assum `compile_tuple_store_all _ tys1 gs ops1 sm = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  `fn_has_code st sm func /\ fn_has_code sm st' func` by
    metis_tac[fn_has_code_split] >>
  `!x. op = Var x ==> not_fresh_at st x` by fs[] >>
  Cases_on `head_res = INL ()`
  >- suspend "success" >>
  suspend "abort"
QED

Resume tuple_store_targets_outcome[abort]:
  qpat_x_assum `head_res = INL () \/ _` mp_tac >>
  asm_rewrite_tac [] >> strip_tac >>
  qpat_x_assum `head_res = INR _` SUBST_ALL_TAC >>
  `is_word_type ty` by metis_tac[tuple_target_aligned_nonlocal_word] >>
  `eval_operand op s = SOME (typed_val_to_w256 tv v)` by
    (qpat_x_assum `!i. i < LENGTH (_::gs) ==> ?w. _`
      (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all tuple_target_static_head_exit >>
  disch_then (qspecl_then [`RetQ`, `head_es`] strip_assume_tac) >>
  qexistsl [`INR (Error (RuntimeError "write in static context"))`, `head_es`, `r`] >>
  fs[assign_tuple_target_list_cons, stmt_exit_def, expr_exit_def]
QED

Resume tuple_store_targets_outcome[success]:
  qpat_x_assum `head_res = INL ()` SUBST_ALL_TAC >>
  `assign_tuple_targets cx (BaseTarget bt) v es =
    (INL (), head_es with gas_obs := es.gas_obs)` by
    (qpat_x_assum `!tail. assign_tuple_targets _ _ _ _ = _`
      (qspec_then `es.gas_obs` mp_tac) >> simp[]) >>
  `if is_word_type ty then eval_operand op s = SOME (typed_val_to_w256 tv v)
   else ?w. eval_operand op s = SOME w /\
     val_in_memory tv v (w2n w) s.vs_memory /\
     type_memory_size tv + 64 < dimword(:256)` by
    suspend "head_operand" >>
  drule_all tuple_target_store_head_path >>
  disch_then (qx_choose_then `s1` (map_every assume_tac o CONJUNCTS)) >>
  suspend "tail"
QED

Resume tuple_store_targets_outcome[head_operand]:
  qpat_x_assum `ih :- _` kall_tac >>
  qpat_assum `!i. i < LENGTH (_::gs) ==> ?w. _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (qx_choose_then `w` (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `is_word_type ty` >- fs[] >>
  `m` by fs[] >>
  `type_memory_size tv + 64 < dimword(:256)` by
    (qpat_x_assum `!i. i < LENGTH (ty::tys1) /\ _ ==> _`
      (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `m ==> _` mp_tac >> simp[] >> strip_tac >>
  gns[val_in_memory_def] >> qexists `w` >> simp[]
QED

Resume tuple_store_targets_outcome[tail]:
  asm_x "ih" drule >>
  disch_then (qspecl_then [`m`, `tvs1`, `vs1`, `addr + type_memory_size tv`, `b`,
    `sz`, `ctx`, `func`, `cx`, `head_es with gas_obs := es.gas_obs`, `s1`, `RetQ`] mp_tac) >>
  (impl_tac >- suspend "tail_premises") >>
  disch_then (qx_choosel_then [`res`, `es'`, `r`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`res`, `es'`, `r`] >>
  conj_tac >- gvs[assign_tuple_target_list_cons] >>
  conj_tac
  >- (irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
      qexists `s1` >> simp[]) >>
  suspend "compose"
QED

Resume tuple_store_targets_outcome[tail_premises]:
  rpt conj_tac
  >- fs[] >- fs[] >- fs[] >- fs[] >- fs[] >- fs[]
  >- (fs[EVERY_MEM] >> rpt strip_tac >>
      irule not_fresh_at_mono >> qexists `st` >> simp[] >> metis_tac[])
  >- (irule local_ptrs_reserved_next_var >> qexists `st` >> simp[])
  >- fs[value_has_type_def]
  >- fs[val_wf_def]
  >- suspend "tail_operands"
  >- suspend "tail_layout"
  >- (rpt strip_tac >> `i < LENGTH vs1` by fs[] >>
      qpat_x_assum `!i. i < LENGTH (ty::tys1) /\ _ ==> _`
        (qspec_then `SUC i` mp_tac) >> simp[])
  >- suspend "tail_memory"
  >> asm_rewrite_tac []
QED

Resume tuple_store_targets_outcome[tail_operands]:
  gen_tac >> strip_tac >>
  `LENGTH ops1 = LENGTH gs` by fs[] >>
  drule (Q.SPEC `T` tuple_store_operands_tail) >>
  disch_then (qspecl_then [`st`, `s`, `s1`] mp_tac) >>
  disch_then irule >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  qexistsl [`BaseTarget bt`, `op`, `ty`, `v`] >> asm_rewrite_tac []
QED

Resume tuple_store_targets_outcome[tail_layout]:
  drule tuple_target_layout_transport >> disch_tac >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH (BaseTarget bt::gs) ==> tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `SUC i` mp_tac) >> simp[] >>
  `i < LENGTH vs1` by fs[] >> simp[]
QED

Resume tuple_store_targets_outcome[tail_memory]:
  strip_tac >>
  qpat_x_assum `m ==> _` mp_tac >>
  (impl_tac >- asm_rewrite_tac []) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_word_type ty ==> type_memory_size tv = 32` by
    (qpat_assum `!i. _ ==> evaluate_type _ _ = _ /\ _`
      (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
     strip_tac >> asm_rewrite_tac []) >>
  drule_all tuple_target_store_memory_tail >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm_rewrite_tac [] >>
  gen_tac >> strip_tac >>
  `i < LENGTH vs1` by fs[] >>
  qpat_x_assum `!i. i < LENGTH (ty::tys1) ==> _`
    (qspec_then `SUC i` mp_tac) >> simp[]
QED

Resume tuple_store_targets_outcome[compose]:
  `~block_is_terminated sm` by
    (drule_all tuple_store_singleton_open >> simp[]) >>
  qpat_x_assum `(_ /\ ?t. _) \/ _` strip_assume_tac
  >- (`~block_is_terminated st'` by metis_tac[] >>
      disj1_tac >> asm_rewrite_tac[] >>
      qexists `t` >> asm_rewrite_tac[] >>
      conj_tac
      >- (rpt strip_tac >>
          `not_fresh_at sm x` by
            (irule not_fresh_at_mono >> qexists `st` >> simp[]) >>
          metis_tac[]) >>
      conj_tac >- metis_tac[] >>
      rpt strip_tac >> first_x_assum irule >>
      first_x_assum irule >> first_assum ACCEPT_TAC) >>
  disj2_tac >> simp[]
QED

Finalise tuple_store_targets_outcome
