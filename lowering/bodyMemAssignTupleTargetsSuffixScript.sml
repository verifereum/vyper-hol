(* Counted composition of tuple staging, loads, and mixed stores. *)
Theory bodyMemAssignTupleTargetsSuffix
Ancestors
  bodyMemAssignTupleTargetsLoad bodyMemAssignTupleTargetsStore
  bodyMemAssignTupleTargetsGas
  tupleAssignPrefix stmtSimAssignTupleTargets tupleStageProps tupleMemoryLayout
  exprSimDefs exprSimProps exprLoweringProps stmtSimProps stmtSimDefs
  valueEncoding valueEncodingProps vyperTyping vyperInterpreter vyperState
  compileEnv loweringStateRelDefs loweringSlice fragExec freshWrites list rich_list finite_map
  fragGasPathMem bodyMemoryDefs tupleTargetStoreProps stmtSimReturn
  tupleAssignParts stmtLowering exprLowering vyperTypeABI vyperValue
  loweringPosts stmtSimAssignTuple tupleTypedLoad vyperTypeDefaults exprOperandVar
  tupleTargetStoreAbort storageStoreFrame tupleTargetStoreRun tupleLocalStoreRun
  venomExecSemantics venomState venomInst emitHelper emitHelperProps
  valueEncodingDefs localPtrsProps
Libs
  monadsyntax

Theorem tuple_static_success_local[local]:
  tuple_target_aligned cenv cx g ty tv /\ cx.txn.is_static /\
  assign_tuple_targets cx g v es = (INL (),es') ==>
  ?id. g = BaseTarget (NameTarget id)
Proof
  simp[tuple_target_aligned_def] >> strip_tac >> gvs[]
  >- (drule_all tuple_target_toplevel_place >>
      disch_then (qspec_then `es` assume_tac) >>
      drule_all tuple_target_storage_assignment >>
      simp[vyperStorageBackendTheory.write_storage_slot_eq]) >>
  drule_all tuple_target_field_place >>
  disch_then (qspec_then `es` assume_tac) >>
  drule_all tuple_target_storage_assignment >>
  simp[vyperStorageBackendTheory.write_storage_slot_eq]
QED

Theorem tuple_target_static_head_exit_mem:
  !ctx func cenv cx s g ty tv v op st sf RetQ ee d.
    compile_tuple_store_all cenv [ty] [g] [op] st = ((),sf) /\
    tuple_target_aligned cenv cx g ty tv /\
    (!id. g <> BaseTarget (NameTarget id)) /\ value_has_type tv v /\
    eval_operand op s = SOME (typed_val_to_w256 tv v) /\
    local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
    fn_has_code st sf func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_history func s /\ return_buf_frame d cenv st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ s.vs_call_ctx.cc_static ==>
    ?r. gas_path_mem ctx func s 0 r /\ exit_result r /\
      !H:(bool # bytes32 # type_value) list # num list.
        stmt_exit (RetQ H) ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  rpt gen_tac >> simp[tuple_target_aligned_def] >> strip_tac >> gvs[]
  >- suspend "toplevel" >>
  suspend "field"
QED

Resume tuple_target_static_head_exit_mem[toplevel]:
  drule_all stmtSimAssignStorageFactsTheory.compile_get_target_ptr_toplevel >>
  disch_then (qspec_then `st` assume_tac) >> gvs[] >>
  drule_all tuple_store_word_step >> strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
  gvs[compile_tuple_store_all_def, comp_return_def] >>
  `emit_void (if tr then TSTORE else SSTORE) [Lit (n2w k); op] st = ((),sf)` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def]) >>
  `eval_operand (Lit (n2w k)) s = SOME (n2w k)` by simp[eval_operand_def] >>
  drule_all (Q.INST [`memory` |-> `T`] storage_emit_static_path_memory) >>
  simp[fragGasModeTheory.gas_marked_path_def] >> strip_tac >>
  qexists_tac `Abort ExHalt_abort (halt_state (set_returndata [] s))` >>
  simp[exit_result_def, stmt_exit_def, expr_exit_def]
QED

Resume tuple_target_static_head_exit_mem[field]:
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
  drule_all tuple_field_add_frame_path_mem >>
  disch_then (qspec_then `ctx`
    (qx_choose_then `mid` (map_every assume_tac o CONJUNCTS))) >>
  `eval_operand op mid = SOME (typed_val_to_w256 tv v)` by
    (Cases_on `op` >> gvs[eval_operand_def]) >>
  `mid.vs_call_ctx.cc_static` by gvs[] >>
  `emit_void (if tr then TSTORE else SSTORE) [dst; op] sp = ((),sf)` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def]) >>
  drule_all (Q.INST [`memory` |-> `T`] storage_emit_static_path_memory) >>
  simp[fragGasModeTheory.gas_marked_path_def] >> strip_tac >>
  qexists_tac `Abort ExHalt_abort (halt_state (set_returndata [] mid))` >>
  simp[exit_result_def, stmt_exit_def, expr_exit_def] >>
  irule (gas_path_mem_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexists_tac `mid` >> simp[]
QED

Finalise tuple_target_static_head_exit_mem[local]

Theorem tuple_store_targets_static_outcome_mem:
  !gs tys tvs vs ops addr b sz ctx func cenv cx es es' s st st' d RetQ res.
    compile_tuple_store_all cenv tys gs ops st = ((),st') /\
    assign_tuple_target_list cx gs vs es = (res,es') /\
    LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    EVERY (\op. ?x. op = Var x) ops /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops /\
    local_ptrs_reserved cenv st /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    (!i. i < LENGTH gs ==> ?w. eval_operand (EL i ops) s = SOME w /\
      if is_word_type (EL i tys) then
        w = typed_val_to_w256 (EL i tvs) (EL i vs)
      else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs))) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
      tuple_target_layout es.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
    (!i. i < LENGTH tys ==>
      evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
      (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)) /\
    b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
    b + sz <= s.vs_alloca_next /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) /\
    tuple_in_memory vs tvs addr s.vs_memory /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_history func s /\ return_buf_frame d cenv st s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    local_ptrs_rel func cenv es.scopes s /\ alloca_inv s /\
    s.vs_call_ctx.cc_static /\ cx.txn.is_static ==>
    ?r. gas_path_mem ctx func s 0 r /\
      ((res = INL () /\
        es'.storage_trace = es.storage_trace /\
        es'.accounts = es.accounts /\ es'.tStorage = es.tStorage /\
        (gs <> [] \/ ~block_is_terminated st ==> ~block_is_terminated st') /\
        ?t. r = OK t /\
          (!H:(bool # bytes32 # type_value) list # num list.
               stmt_state_rel H ctx func cenv cx es s ==>
               stmt_state_rel H ctx func cenv cx es' t) /\
          ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
          t.vs_inst_idx = LENGTH st'.cs_current_insts /\
          (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
          (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==>
                    FLOOKUP t.vs_allocas aid = SOME bs) /\
          alloca_history func t /\ return_buf_frame d cenv st' t /\
          s.vs_alloca_next <= t.vs_alloca_next) \/
       (exit_result r /\ !(H:(bool # bytes32 # type_value) list # num list) tail.
          stmt_exit (RetQ H) (es' with gas_obs := tail) res r /\
          halt_exit H cx es' res r))
Proof
  Induct
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gvs[compile_tuple_store_all_def, comp_return_def] >>
      qpat_x_assum `assign_tuple_target_list _ [] [] _ = _` mp_tac >>
      simp[Once evaluate_def, return_def] >> strip_tac >> gvs[] >>
      qexists_tac `OK s` >> simp[cj 1 gas_path_mem_rules]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `tys` >- fs[] >> Cases_on `tvs` >- fs[] >>
  Cases_on `vs` >- fs[] >> Cases_on `ops` >- fs[] >>
  rename1 `compile_tuple_store_all cenv (ty::tys1) _ (op::ops1) st = _` >>
  rename1 `assign_tuple_target_list cx _ (v::vs1) es = _` >>
  rename1 `tuple_val_wf (v::vs1) (tv::tvs1)` >>
  qpat_x_assum `!tys tvs vs ops addr b sz ctx func cenv cx es es' s st st' d RetQ res. _`
    (mk_asm "ih") >>
  qpat_assum `!i. i < LENGTH (h::gs) ==> tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `value_has_type tv v /\ val_wf tv v` by
    (qpat_x_assum `ih :- _` kall_tac >> fs[value_has_type_def, val_wf_def]) >>
  drule_all tuple_target_source_outcome >>
  disch_then (qx_choosel_then [`head_res`, `head_es`]
    (map_every assume_tac o CONJUNCTS)) >>
  drule_all tuple_target_aligned_compiler >> strip_tac >>
  drule tuple_compiler_target_base >>
  disch_then (qx_choose_then `bt` SUBST_ALL_TAC) >>
  drule tuple_store_base_cons >> strip_tac >>
  qpat_assum `compile_tuple_store_all _ [_] [_] [_] _ = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  qpat_assum `compile_tuple_store_all _ tys1 gs ops1 sm = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  `fn_has_code st sm func /\ fn_has_code sm st' func` by
    (qpat_x_assum `ih :- _` kall_tac >> metis_tac[fn_has_code_split]) >>
  `!x. op = Var x ==> not_fresh_at st x` by fs[] >>
  Cases_on `head_res = INL ()`
  >- suspend "local" >>
  suspend "abort"
QED

Resume tuple_store_targets_static_outcome_mem[abort]:
  qpat_x_assum `head_res = INL () \/ _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `head_res = INR _` SUBST_ALL_TAC >>
  `is_word_type ty` by
    (qpat_x_assum `ih :- _` kall_tac >>
     metis_tac[tuple_target_aligned_nonlocal_word]) >>
  `eval_operand op s = SOME (typed_val_to_w256 tv v)` by
    (qpat_x_assum `!i. i < LENGTH (_::gs) ==> ?w. _`
      (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all tuple_target_static_head_exit_mem >>
  disch_then (qspecl_then [`ctx`, `RetQ`, `es'`] strip_assume_tac) >>
  `assign_tuple_targets cx (BaseTarget bt) v es =
    (INR (Error (RuntimeError "write in static context")),
     head_es with gas_obs := es.gas_obs)` by
    (qpat_x_assum `!tail. assign_tuple_targets _ _ _ _ = _`
      (qspec_then `es.gas_obs` mp_tac) >>
     simp[NoAsms, evaluation_state_component_equality]) >>
  qexists_tac `r` >>
  gvs[assign_tuple_target_list_cons, stmt_exit_def, expr_exit_def, halt_exit_def]
QED

Resume tuple_store_targets_static_outcome_mem[local]:
  qpat_x_assum `head_res = INL ()` SUBST_ALL_TAC >>
  `assign_tuple_targets cx (BaseTarget bt) v es =
    (INL (),head_es with gas_obs := es.gas_obs)` by
    (qpat_x_assum `!tail. assign_tuple_targets _ _ _ _ = _`
      (qspec_then `es.gas_obs` mp_tac) >>
     simp[NoAsms, evaluation_state_component_equality]) >>
  drule_all tuple_static_success_local >>
  disch_then (qx_choose_then `name` (SUBST_ALL_TAC o SRULE [])) >>
  `if is_word_type ty then eval_operand op s = SOME (typed_val_to_w256 tv v)
   else ?w. eval_operand op s = SOME w /\
     val_in_memory tv v (w2n w) s.vs_memory /\
     type_memory_size tv + 64 < dimword (:256) /\
     w2n w + type_memory_size tv <= s.vs_alloca_next` by
    suspend "head_operand" >>
  drule_all (INST_TYPE [alpha |-> ``:256``] tuple_target_local_head_path_mem) >>
  disch_then (qspec_then `ctx`
    (qx_choosel_then [`s1`, `idp`, `dsz`, `entry`, `dw`]
      (map_every assume_tac o CONJUNCTS))) >>
  drule_all tuple_target_assignment_scope_frame >> strip_tac >>
  `alloca_inv s1` by
    (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  `is_word_type ty ==> type_memory_size tv = 32` by
    (qpat_x_assum `!i. i < LENGTH (ty::tys1) ==> evaluate_type _ _ = _ /\ _`
      (qspec_then `0` mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`func`, `cenv`, `es`, `s`, `s1`, `st`,
    `(head_es with gas_obs := es.gas_obs).scopes`, `BaseTarget (NameTarget name)`,
    `ty`, `tv`, `tvs1`, `v`, `vs1`, `b`, `sz`, `addr`]
    tuple_target_store_memory_tail) >>
  (impl_tac
   >- (asm_rewrite_tac[] >> disj2_tac >>
       qexistsl_tac [`name`, `idp`, `dsz`, `entry`, `dw`] >> asm_rewrite_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >> suspend "tail"
QED

Resume tuple_store_targets_static_outcome_mem[head_operand]:
  qpat_x_assum `ih :- _` kall_tac >>
  qpat_x_assum `!i. i < LENGTH (_::gs) ==> ?w. _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (qx_choose_then `w` (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `is_word_type ty` >- fs[] >>
  `type_memory_size tv + 64 < dimword (:256)` by
    (qpat_x_assum `!i. i < LENGTH (ty::tys1) /\ _ ==> _`
      (qspec_then `0` mp_tac) >> simp[]) >>
  `type_memory_size_list (tv::tvs1) =
    type_memory_size tv + type_memory_size_list tvs1` by simp[type_memory_size_def] >>
  `w2n w + type_memory_size tv <= s.vs_alloca_next` by (fs[] >> decide_tac) >>
  gns[val_in_memory_def, type_memory_size_def] >> qexists_tac `w` >> simp[]
QED

Resume tuple_store_targets_static_outcome_mem[tail]:
  qpat_x_assum `assign_tuple_target_list _ (_::gs) _ es = _` mp_tac >>
  simp[assign_tuple_target_list_cons] >> disch_tac >>
  asm_x "ih" drule >> disch_then drule >>
  disch_then (qspecl_then [`tvs1`, `addr + type_memory_size tv`, `b`, `sz`,
    `ctx`, `func`, `s1`, `d`, `RetQ`] mp_tac) >>
  (impl_tac >- suspend "tail_premises") >>
  disch_then (qx_choose_then `r` (map_every assume_tac o CONJUNCTS)) >>
  qexists_tac `r` >> conj_tac
  >- (irule (gas_path_mem_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
      qexists_tac `s1` >> simp[]) >>
  qpat_x_assum `(res = INL () /\ _) \/ _`
    (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS)
                     (map_every assume_tac o CONJUNCTS))
  >- suspend "compose" >>
  disj2_tac >> asm_rewrite_tac[]
QED

Resume tuple_store_targets_static_outcome_mem[tail_premises]:
  simp_tac (srw_ss()) [] >> rpt conj_tac
  >- fs[] >- fs[] >- fs[] >- fs[] >- fs[]
  >- (fs[EVERY_MEM] >> rpt strip_tac >>
      irule not_fresh_at_mono >> qexists_tac `st` >> simp[] >> metis_tac[])
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[])
  >- fs[value_has_type_def]
  >- fs[val_wf_def]
  >- suspend "tail_operands"
  >- suspend "tail_layout"
  >- (rpt strip_tac >>
      `i < LENGTH vs1` by fs[] >>
      qpat_x_assum `!i. i < LENGTH (ty::tys1) /\ _ ==> _`
        (qspec_then `SUC i` mp_tac) >> simp[])
  >- (rpt strip_tac >>
      `i < LENGTH vs1` by fs[] >>
      qpat_x_assum `!i. i < LENGTH (ty::tys1) ==> evaluate_type _ _ = _ /\ _`
        (qspec_then `SUC i` mp_tac) >> simp[]) >>
  fs[] >> metis_tac[]
QED

Resume tuple_store_targets_static_outcome_mem[tail_operands]:
  gen_tac >> strip_tac >>
  `LENGTH ops1 = LENGTH gs` by fs[] >>
  drule (Q.SPEC `T` tuple_store_operands_tail) >>
  disch_then (qspecl_then [`st`, `s`, `s1`] mp_tac) >>
  disch_then irule >> goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  qexistsl_tac [`BaseTarget (NameTarget name)`, `op`, `ty`, `v`] >>
  asm_rewrite_tac[]
QED

Resume tuple_store_targets_static_outcome_mem[tail_layout]:
  drule tuple_target_layout_transport >> disch_tac >>
  gen_tac >> strip_tac >>
  `i < LENGTH vs1` by fs[] >>
  qpat_x_assum `!i. i < LENGTH (BaseTarget (NameTarget name)::gs) ==>
    tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `SUC i` mp_tac) >> simp[] >> strip_tac >> fs[]
QED

Resume tuple_store_targets_static_outcome_mem[compose]:
  `~block_is_terminated sm` by
    (drule_all tuple_store_singleton_open >> simp[]) >>
  qpat_x_assum `?t. r = OK t /\ _`
    (qx_choose_then `sfv` (map_every assume_tac o CONJUNCTS)) >>
  `~block_is_terminated st'` by fs[] >>
  disj1_tac >> asm_rewrite_tac[] >> qexists_tac `sfv` >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> first_x_assum irule >>
      first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
      metis_tac[])
  >- metis_tac[] >> decide_tac
QED

Finalise tuple_store_targets_static_outcome_mem[local]

Theorem tuple_store_targets_outcome_mem:
  !gs tys tvs vs ops addr b sz ctx func cenv cx es s st st' d RetQ.
    compile_tuple_store_all cenv tys gs ops st = ((),st') /\
    LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    EVERY (\op. ?x. op = Var x) ops /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops /\
    local_ptrs_reserved cenv st /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    (!i. i < LENGTH gs ==> ?w. eval_operand (EL i ops) s = SOME w /\
      if is_word_type (EL i tys) then
        w = typed_val_to_w256 (EL i tvs) (EL i vs)
      else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs))) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
      tuple_target_layout es.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
    (!i. i < LENGTH tys ==>
      evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
      (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)) /\
    b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
    b + sz <= s.vs_alloca_next /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) /\
    tuple_in_memory vs tvs addr s.vs_memory /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_history func s /\ return_buf_frame d cenv st s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list)
      ctx func cenv cx es s ==>
    ?res es' r.
      (!tail. assign_tuple_target_list cx gs vs (es with gas_obs := tail) =
        (res,es' with gas_obs := tail)) /\
      gas_path_mem ctx func s 0 r /\
      ((res = INL () /\ ?t. r = OK t /\
        (gs <> [] \/ ~block_is_terminated st ==> ~block_is_terminated st') /\
        (!st0 H. valid_horizon cx st0 H es'.storage_trace /\
          stmt_state_rel H ctx func cenv cx es s /\
          storage_well_formed_on cx es (FST H) ==>
          stmt_state_rel H ctx func cenv cx es' t /\
          storage_well_formed_on cx es' (FST H)) /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==>
                  FLOOKUP t.vs_allocas aid = SOME bs) /\
        alloca_history func t /\ return_buf_frame d cenv st' t /\
        s.vs_alloca_next <= t.vs_alloca_next) \/
       (exit_result r /\ !(H:(bool # bytes32 # type_value) list # num list) tail.
          stmt_exit (RetQ H) (es' with gas_obs := tail) res r /\
          halt_exit H cx es' res r))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_inv s /\
   s.vs_call_ctx.cc_static = cx.txn.is_static` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule_all tuple_source_list_outcome >>
  disch_then (qx_choosel_then [`res`, `source_end`]
    (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `es' = source_end with gas_obs := es.gas_obs` >>
  `assign_tuple_target_list cx gs vs es = (res,es')` by
    (qpat_assum `!tail. assign_tuple_target_list _ _ _ _ = _`
      (qspec_then `es.gas_obs` mp_tac) >>
     simp[NoAsms, Abbr `es'`, evaluation_state_component_equality]) >>
  `!tail. assign_tuple_target_list cx gs vs (es with gas_obs := tail) =
    (res,es' with gas_obs := tail)` by simp[Abbr `es'`] >>
  Cases_on `cx.txn.is_static`
  >- suspend "static" >>
  suspend "nonstatic"
QED

Resume tuple_store_targets_outcome_mem[static]:
  `s.vs_call_ctx.cc_static` by simp[] >>
  drule_all tuple_store_targets_static_outcome_mem >>
  disch_then (qspecl_then [`ctx`, `RetQ`]
    (qx_choose_then `r` (map_every assume_tac o CONJUNCTS))) >>
  qexistsl_tac [`res`, `es'`, `r`] >> asm_rewrite_tac[] >>
  qpat_x_assum `(res = INL () /\ _) \/ _`
    (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS)
                     (map_every assume_tac o CONJUNCTS))
  >- (qpat_x_assum `?t. r = OK t /\ _`
        (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
      disj1_tac >> asm_rewrite_tac[] >> qexists_tac `t` >>
      asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >> conj_tac
      >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
      `storage_well_formed_on cx es' (FST H) <=>
       storage_well_formed_on cx es (FST H)` by
        (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
         asm_rewrite_tac[]) >> simp[]) >>
  disj2_tac >> asm_rewrite_tac[]
QED

Resume tuple_store_targets_outcome_mem[nonstatic]:
  `LIST_REL (tuple_source_target cx es.scopes) gs tvs` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule tuple_target_aligned_source >>
     qexistsl_tac [`cenv`, `EL n tys`, `EL n vs`] >> simp[]) >>
  `LIST_REL value_has_type tvs vs` by simp[GSYM values_have_types_LIST_REL] >>
  drule_all assign_tuple_target_list_safe >>
  disch_then (qx_choose_then `safe_end` (map_every assume_tac o CONJUNCTS)) >>
  `res = INL ()` by
    (qpat_assum `assign_tuple_target_list _ _ _ _ = (res,es')` mp_tac >>
     asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
  `safe_end = es'` by
    (qpat_assum `assign_tuple_target_list _ _ _ _ = (INL (),es')` mp_tac >>
     asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `safe_end = es'` SUBST_ALL_TAC >>
  `~s.vs_call_ctx.cc_static` by simp[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.SPECL [`gs`, `T`] tuple_store_targets_path_mem)) >>
  disch_then (qspec_then `ctx` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?t. (!st0 H. _) /\ _`
    (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`INL ()`, `es'`, `OK t`] >> asm_rewrite_tac[] >>
  disj1_tac >> qexists_tac `t` >> simp[] >>
  first_assum MATCH_ACCEPT_TAC
QED

Finalise tuple_store_targets_outcome_mem[local]

Theorem tuple_assignment_prefix_path_mem:
  !st0 ctx func cenv cx es1 tys tvs vs sa su sl ss op staged elems sv flag d.
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    0 < type_memory_size_list tvs /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op sv /\
    expr_val_at cenv cx (TupleT tys) sa su es1 (ArrayV (TupleV vs)) op sv /\
    (!x. op = Var x ==> not_fresh_at su x) /\
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
    cs_extends su sl /\ cs_extends sl ss /\
    fn_has_code su sl func /\ fn_has_code sl ss func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv su /\
    (?H. valid_horizon cx st0 H es1.storage_trace) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
         stmt_state_rel H ctx func cenv cx es1 sv) /\ alloca_history func sv /\
    return_buf_frame d cenv su sv /\ ~sv.vs_halted /\
    sv.vs_current_bb = su.cs_current_bb /\
    sv.vs_inst_idx = LENGTH su.cs_current_insts ==>
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems /\
    local_ptrs_reserved cenv ss /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    ?t (w:256 word) b sz.
      (!H. valid_horizon cx st0 H es1.storage_trace ==>
           stmt_state_rel H ctx func cenv cx es1 t) /\ ~t.vs_halted /\
      t.vs_current_bb = ss.cs_current_bb /\
      t.vs_inst_idx = LENGTH ss.cs_current_insts /\
      tuple_in_memory vs tvs (w2n w) t.vs_memory /\ b <= w2n w /\
      w2n w + type_memory_size_list tvs <= b + sz /\
      b + sz <= t.vs_alloca_next /\
      ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
       (?name. local_region cenv es1.scopes t name b sz)) /\
      w2n w + type_memory_size_list tvs < dimword (:256) /\
      (!i. i < LENGTH tys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i tys) then
          v = typed_val_to_w256 (EL i tvs) (EL i vs)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))) /\
      (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x sv) /\
      (!aid entry. FLOOKUP sv.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      alloca_history func t /\ return_buf_frame d cenv ss t /\
      sv.vs_alloca_next <= t.vs_alloca_next /\
      gas_path_mem ctx func sv 0 (OK t) /\
      t.vs_accounts = sv.vs_accounts /\ t.vs_transient = sv.vs_transient /\
      t.vs_requests = sv.vs_requests /\ t.vs_call_ctx = sv.vs_call_ctx
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) tys tvs` by
    (irule evaluate_types_LIST_REL >>
     qpat_assum `evaluate_type _ (TupleT tys) = _` mp_tac >>
     simp_tac (srw_ss()) [evaluate_type_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs` by
    (irule type_memory_bytes_tuple_list >> first_assum ACCEPT_TAC) >>
  `?sw. eval_operand op sv = SOME sw` by metis_tac[expr_val_rel_def] >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  `stmt_state_rel H0 ctx func cenv cx es1 sv` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ sv`
       drule >> disch_then ACCEPT_TAC) >>
  drule_all optional_tuple_stage_path_mem >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t w. _`
    (qx_choosel_then [`st`, `w`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?b sz. _`
    (qx_choosel_then [`b`, `sz`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [GSYM optional_tuple_stage_code]) >>
  drule tuple_stage_grows >> strip_tac >>
  `local_ptrs_reserved cenv sl` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `su` >> simp[]) >>
  `w2n w + type_memory_size_list tvs < dimword (:256)` by
    (drule_all tuple_container_bound >> decide_tac) >>
  `w2n w + type_memory_size_list tvs <= st.vs_alloca_next` by decide_tac >>
  drule_all compile_tuple_load_all_typed_path_mem >> strip_tac >>
  `EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  `t.vs_accounts = sv.vs_accounts` by asm_rewrite_tac[] >>
  `t.vs_transient = sv.vs_transient` by asm_rewrite_tac[] >>
  `t.vs_requests = sv.vs_requests` by asm_rewrite_tac[] >>
  `t.vs_call_ctx = sv.vs_call_ctx` by asm_rewrite_tac[] >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es1 t` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx es1 sv` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ sv`
          drule >> disch_then ACCEPT_TAC) >>
     mp_tac (Q.INST [`H0` |-> `H0`, `u` |-> `t`, `s` |-> `sv`, `es` |-> `es1`]
       (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
         exprLoweringPropsTheory.stmt_state_rel_fields_transport)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  asm_rewrite_tac[] >> qexistsl_tac [`t`, `w`, `b`, `sz`] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sl x` by
        (irule not_fresh_at_mono >> qexists_tac `su` >> fs[cs_extends_def]) >>
      simp[]) >>
  `gas_path_mem ctx func sv (0 + 0) (OK t)` by
    (irule gas_path_mem_then >> qexists_tac `st` >> simp[]) >> gvs[]
QED

Theorem assign_tuple_targets_suffix_mem:
  !ctx func cx st0 lctx cenv gs e es ee v tys tvs sa su sl ss sf op staged elems sv s0 flag d RetQ.
    post_value_type cenv e = expr_type e /\
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         expr_post H ctx func cenv cx e es sa su s0 ee v op sv) /\
    sv.vs_current_bb = su.cs_current_bb /\
    sv.vs_inst_idx = LENGTH su.cs_current_insts /\ ~sv.vs_halted /\
    alloca_history func sv /\ return_buf_frame d cenv su sv /\
    ee.gas_obs = [] /\ value_has_type (TupleTV tvs) v /\
    gs <> [] /\ LENGTH gs = LENGTH tys /\ expr_type e = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
      tuple_target_layout ee.scopes (EL i gs) (EL i tys) (EL i tvs)
        (EL i (case v of ArrayV (TupleV vs) => vs | _ => []))) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
    lower_value compile_expr cenv (TupleT tys) e sa = (op,su) /\
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
    compile_tuple_store_all cenv tys gs elems ss = ((),sf) /\
    cs_extends sa su /\ sa.cs_next_var <= su.cs_next_var /\
    cs_extends su sl /\ cs_extends sl ss /\
    su.cs_next_var <= sl.cs_next_var /\ sl.cs_next_var <= ss.cs_next_var /\
    fn_has_code su sl func /\ fn_has_code sl ss func /\ fn_has_code ss sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
    ?res ee' r.
      (!tail. assign_tuple_targets cx (TupleTarget gs) v (ee with gas_obs := tail) =
        (res, ee' with gas_obs := tail)) /\
      gas_path_mem ctx func sv 0 r /\
      ((?t'. r = OK t' /\
      alloca_history func t' /\ return_buf_frame d cenv sf t' /\
      sv.vs_alloca_next <= t'.vs_alloca_next /\
      stmt_lands lctx sf res t' /\ ~t'.vs_halted /\ ~block_is_terminated sf /\
      cenv_top_ext cenv cenv ee'.scopes /\
      (!H. valid_horizon cx st0 H ee'.storage_trace ==>
           stmt_state_rel H ctx func cenv cx (ee' with gas_obs := []) t' /\
           storage_well_formed_on cx (ee' with gas_obs := []) (FST H)) /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t' = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t'.vs_allocas aid = SOME b)) \/
       (exit_result r /\ !H. valid_horizon cx st0 H ee'.storage_trace ==>
         (!tail. stmt_exit (RetQ H) (ee' with gas_obs := tail) res r) /\
         halt_exit H cx ee' res r))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_type_value >> strip_tac >> gvs[] >>
  `LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    (gvs[evaluate_type_def, AllCaseEqs()] >>
     metis_tac[LIST_REL_LENGTH, values_have_types_length]) >>
  `LIST_REL (tuple_source_target cx ee.scopes) gs tvs` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule tuple_target_aligned_source >>
     qexistsl_tac [`cenv`, `EL n tys`, `EL n vs`] >> simp[]) >>
  `LIST_REL value_has_type tvs vs` by simp[GSYM values_have_types_LIST_REL] >>
  suspend "prefix"
QED

Resume assign_tuple_targets_suffix_mem[prefix]:
  `!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
    0 < type_memory_size (EL i tvs)` by
    (gen_tac >> disch_tac >> irule tuple_target_aligned_sizes >>
     qexists_tac `EL i gs` >> first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  `LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs` by
    simp[LIST_REL_EL_EQN] >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) tys tvs` by
    simp[LIST_REL_EL_EQN] >>
  `tys <> []` by (Cases_on `tys` >> gvs[]) >>
  `0 < type_memory_size_list tvs` by
    (irule tuple_memory_size_positive >> qexistsl_tac [`get_tenv cx`, `tys`] >>
     simp[] >> rpt strip_tac >>
     disj2_tac >> qexistsl_tac [`EL i tys`, `EL i tvs`] >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at su x` by
    metis_tac[compile_lower_value_var] >>
  `local_ptrs_reserved cenv su` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[cs_extends_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `post_value_type _ _ = _`
    (fn th => rewrite_tac[expr_post_def, th]) >>
  strip_tac >>
  `expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op sv` by metis_tac[] >>
  `expr_val_at cenv cx (TupleT tys) sa su ee (ArrayV (TupleV vs)) op sv` by metis_tac[] >>
  `!H'. valid_horizon cx st0 H' ee.storage_trace ==>
        stmt_state_rel H' ctx func cenv cx ee sv` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H'`
         (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [expr_post_def] o UNDISCH))) >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] tuple_assignment_prefix_path_mem) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t w b sz. _`
    (qx_choosel_then [`t`, `w`, `b`, `sz`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "stores"
QED

Resume assign_tuple_targets_suffix_mem[stores]:
  `!i. i < LENGTH gs ==> ?v. eval_operand (EL i elems) t = SOME v /\
    if is_word_type (EL i tys) then
      v = typed_val_to_w256 (EL i tvs) (EL i vs)
    else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)` by
    (gen_tac >> disch_tac >> simp[] >> strip_tac >>
     `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by simp[] >>
     drule_all word_type_sizes >>
     disch_then (qspec_then `cenv` strip_assume_tac) >> simp[]) >>
  `LENGTH elems = LENGTH vs` by decide_tac >>
  `!i. i < LENGTH gs ==>
    tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
    tuple_target_layout ee.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)` by
    (rpt strip_tac >> simp[]) >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `(if flag then _ else _) su = _` kall_tac >>
  qpat_x_assum `compile_tuple_load_all _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `expr_val_rel _ (TupleT tys) _ _ _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ (TupleT tys) _ _ _ _ _ _` kall_tac >>
  `stmt_state_rel H ctx func cenv cx ee t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ ee t` drule >>
     disch_then ACCEPT_TAC) >>
  drule_all tuple_store_targets_outcome_mem >>
  disch_then (qspec_then `RetQ`
    (qx_choosel_then [`res`, `ee'`, `r`]
      (map_every assume_tac o CONJUNCTS))) >>
  qexistsl_tac [`res`, `ee'`, `r`] >> conj_tac
  >- simp[Once evaluate_def] >>
  conj_tac
  >- (drule_all gas_path_mem_then >> simp[]) >>
  qpat_x_assum `(res = INL () /\ _) \/ _`
    (DISJ_CASES_THEN2
      (CONJUNCTS_THEN2 SUBST_ALL_TAC
        (qx_choose_then `sfv` (map_every assume_tac o CONJUNCTS)))
      (map_every assume_tac o CONJUNCTS))
  >- (disj1_tac >> qexists_tac `sfv` >> asm_rewrite_tac[] >>
      `assign_tuple_target_list cx gs vs ee =
        (INL (),ee' with gas_obs := ee.gas_obs)` by
        (qpat_assum `!tail. assign_tuple_target_list _ _ _ _ = _`
          (qspec_then `ee.gas_obs` mp_tac) >>
         simp[NoAsms, evaluation_state_component_equality]) >>
      suspend "post") >>
  disj2_tac >> simp[]
QED

Resume assign_tuple_targets_suffix_mem[post]:
  `sv.vs_alloca_next <= sfv.vs_alloca_next` by decide_tac >>
  `!H'. valid_horizon cx st0 H' ee'.storage_trace ==>
        stmt_state_rel H' ctx func cenv cx (ee' with gas_obs := []) sfv /\
        storage_well_formed_on cx (ee' with gas_obs := []) (FST H')` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H' ee.storage_trace` by
       (irule (INST_TYPE [alpha |-> ``:unit``]
          vyperStorageFootprintTheory.valid_horizon_frame) >>
        qpat_assum `assign_tuple_target_list _ _ _ ee = _` (irule_at Any) >>
        simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H'` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     `stmt_state_rel H' ctx func cenv cx ee t` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ ee t`
          irule >> first_assum ACCEPT_TAC) >>
     `stmt_state_rel H' ctx func cenv cx ee' sfv /\
      storage_well_formed_on cx ee' (FST H')` by
       (qpat_assum `!st0 H. valid_horizon _ st0 H ee'.storage_trace /\ _ ==> _`
          (qspecl_then [`st0`, `H'`] match_mp_tac) >> asm_rewrite_tac[]) >>
     `storage_well_formed_on cx (ee' with gas_obs := []) (FST H')` by
       (`!b. get_storage cx (ee' with gas_obs := []) b = get_storage cx ee' b` by
          (Cases >> simp_tac (srw_ss()) [vyperStorageBackendTheory.get_storage_def]) >>
        fs[vyperStorageFootprintTheory.storage_well_formed_on_def]) >>
     simp[]) >>
  simp[stmt_lands_def, cenv_top_ext_refl] >>
  suspend "frame"
QED

Resume assign_tuple_targets_suffix_mem[frame]:
  RULE_ASSUM_TAC (REWRITE_RULE [stmt_state_rel_start_gas_obs]) >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at su x` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sl x` by
    (irule not_fresh_at_mono >> qexists_tac `su` >> simp[]) >>
  `not_fresh_at ss x` by
    (irule not_fresh_at_mono >> qexists_tac `sl` >> simp[]) >>
  simp[]
QED

Finalise assign_tuple_targets_suffix_mem
