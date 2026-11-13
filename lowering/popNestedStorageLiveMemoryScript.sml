(* Counted live storage/transient suffix, preserving the concrete run. *)
Theory popNestedStorageLiveMemory
Ancestors
  popNestedStorageSuffixMemory exprSimPopNestedBase exprSimMemDefs
  targetPlaceSimMem allocaHistoryFragment
  loweringPosts loweringStateRelDefs exprSimDefs exprSimProps exprSimHypsDefs
  exprSimPopStorage exprLoweringProps compileEnv fragExec list words
  vyperInterpreter vyperState vyperContext vyperStoragePlaceRegion
  vyperStoragePlaceProvenance venomState venomExecSemantics venomInst
  gasSummary gasOutcome fragGasMode exprLowering bodyPtrHashBuiltinsCursor emitHelper

Theorem nested_pop_storage_live_suffix_sim_mem:
  storage_layout_safe cx /\
  storage_place_region cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) /\
  slots_in_range (vyperStorageBackend$get_storage cx es tr) (w2n slot)
    (ArrayTV tv (Dynamic n)) /\
  storage_read_live cx tr (vyperStorageBackend$get_storage cx es tr) slot
    (ArrayTV tv (Dynamic n)) /\
  target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic n))))
    (Type (ArrayT ann (Dynamic n))) (hdr,SOME (slot_loc tr),pt) t /\
  compile_dynarray_pop hdr 1 (type_slot_size tv) cenv.ce_is_ctor
    cenv.ce_imm_alloca (if tr then LocTransient else LocStorage) sm = (q,r) /\
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) es = (res,es') /\
  local_ptrs_reserved cenv sa /\ ci_mono sa sm /\ es.gas_obs = [] /\
  fn_has_code sm r func /\ fn_inst_ids_distinct func /\ alloca_history func t /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_summary_at T (ctx,func) []
    (pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))) (es,t)
    (\res fin u. ?v. res = INL v /\ vv_post ctx func cenv cx (Pop ann bt) es0 sa r s0 fin v
      (LocatedValue ann (mk_ptr q (if tr then LocTransient else LocStorage))) u /\
      vv_store_bound cx (expr_type (Pop ann bt)) (lowered_value_type cenv (Pop ann bt))
        fin v (LocatedValue ann (mk_ptr q (if tr then LocTransient else LocStorage))) u /\
      u.vs_current_bb = r.cs_current_bb /\ u.vs_inst_idx = LENGTH r.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next)
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
  `!tail. pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))
       (es with gas_obs := tail) = (res,es' with gas_obs := tail)` by
    metis_tac[nested_pop_storage_gas_obs] >>
  `stmt_state_rel ctx func cenv cx es t` by fs[target_post_def] >>
  `~cx.txn.is_static /\ ~t.vs_call_ctx.cc_static /\ alloca_inv t` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule nested_pop_storage_target_metadata >> strip_tac >> gvs[] >>
  drule_all nested_pop_storage_natural_region >> strip_tac >>
  drule_all nested_pop_live_array_agree >> strip_tac >>
  drule nested_pop_array_header_load >> strip_tac >>
  qpat_x_assum `storage_layout_safe _` kall_tac >>
  qpat_x_assum `storage_place_region _ _` kall_tac >>
  qpat_x_assum `storage_read_live _ _ _ _ _` kall_tac >>
  qpat_x_assum `pop_place _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss())
      [pop_place_def, vyperStorageBackendTheory.get_storage_backend_eq,
       bind_def, ignore_bind_def, check_def, assert_def, return_def, raise_def,
       vyperStorageBackendTheory.write_storage_slot_eq,
       vyperStorageTheory.encode_value_def, vyperStorageTheory.encode_base_to_slot_def,
       integer_wordTheory.i2w_def]) >>
  Cases_on `lookup_storage slot (vyperStorageBackend$get_storage cx es tr) = 0w`
  >- (simp[assert_def, bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
      drule nested_pop_suffix_shape >> strip_tac >> suspend "empty") >>
  `0 < w2n (lookup_storage slot (vyperStorageBackend$get_storage cx es tr))` by
    (Cases_on `lookup_storage slot (vyperStorageBackend$get_storage cx es tr)` >> gvs[]) >>
  simp[] >> strip_tac >> gvs[] >>
  drule nested_pop_suffix_shape >> strip_tac >> suspend "positive"
QED

Resume nested_pop_storage_live_suffix_sim_mem[empty]:
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
   (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6])` by
    (fs[] >> metis_tac[]) >>
  drule_all nested_pop_suffix_empty >>
  disch_then (qspecl_then [`sm.cs_next_id`, `type_slot_size tv`] strip_assume_tac) >>
  `?j. gas_marked_path T ctx func t 0 (Abort a (s' with vs_inst_idx := j))` by
    (irule nested_pop_suffix_abort_path_mem >> simp[] >> metis_tac[]) >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "pop empty storage array"))`, `es`,
    `Abort a (s' with vs_inst_idx := j)`] >>
  simp[expr_exit_def, exit_result_def] >>
  qpat_x_assum `!tail. pop_place _ _ _ = _`
    (mp_tac o REWRITE_RULE [pop_place_def, check_def, ignore_bind_def]) >>
  simp[]
QED

Resume nested_pop_storage_live_suffix_sim_mem[positive]:
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
   (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6])` by
    (fs[] >> metis_tac[]) >>
  `(if tr then tload (root + n2w delta) t else sload (root + n2w delta) t) <> 0w` by
    metis_tac[] >>
  drule_all nested_pop_suffix_run >>
  disch_then (qspecl_then [`sm.cs_next_id`, `type_slot_size tv`] strip_assume_tac) >>
  qpat_x_assum `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` kall_tac >>
  qpat_x_assum `ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6]` kall_tac >>
  qmatch_asmsub_abbrev_tac `eval_operand hdr t = SOME slot` >>
  qmatch_asmsub_abbrev_tac `0 < w2n lenw` >>
  `lenw - 1w = n2w (w2n lenw - 1)` by simp[wordsTheory.n2w_sub] >>
  `u = (if tr then tstore slot (n2w (w2n lenw - 1)) t
         else sstore slot (n2w (w2n lenw - 1)) t) with vs_vars := u.vs_vars` by
    (Cases_on `tr` >> fs[] >> metis_tac[]) >>
  `!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q t` by
    (fs[ci_mono_def, not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> fs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `stmt_state_rel ctx func cenv cx
    (vyperStorageBackend$set_storage cx es tr
      (apply_writes slot [(0,n2w (w2n lenw - 1))]
        (vyperStorageBackend$get_storage cx es tr))) u` by
    (`w2n slot = w2n root + delta` by simp[arithmeticTheory.ADD_COMM] >>
     qunabbrev_tac `lenw` >> drule_all nested_pop_updated_state_rel >> simp[]) >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func cenv cx fin u` >>
  `storage_holds cx tr ann
    (PlaceR (StoragePlace tr (slot + n2w (1 + (w2n lenw - 1) * type_slot_size tv)) tv))
    (slot + n2w (1 + (w2n lenw - 1) * type_slot_size tv)) fin u` by
    (qunabbrev_tac `fin` >> qunabbrev_tac `lenw` >>
     irule nested_pop_positive_holds >>
     rpt conj_tac >- first_assum ACCEPT_TAC >- REFL_TAC >- REFL_TAC
     >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`n`, `t`] >> rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (qpat_assum `w2n slot = _` (fn th => REWRITE_TAC [th]) >>
         first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  suspend "positive_post"
QED

Resume nested_pop_storage_live_suffix_sim_mem[positive_post]:
  `u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `u = _ with vs_vars := _` (fn th => ONCE_REWRITE_TAC [th]) >>
     Cases_on `tr` >>
     simp_tac (srw_ss()) [NoAsms, sstore_def, tstore_def, LET_THM]) >>
  qpat_x_assum `u = _ with vs_vars := _` kall_tac >>
  qpat_x_assum `u = _ with vs_vars := _` kall_tac >>
  `lookup_var x6 u =
     SOME (slot + n2w (1 + (w2n lenw - 1) * type_slot_size tv))` by
    (qpat_x_assum `lookup_var x6 u = _` mp_tac >>
     qpat_x_assum `(if tr then tload _ _ else sload _ _) = _`
       (fn th => REWRITE_TAC [th]) >>
     qpat_x_assum `lenw - 1w = _` (fn th => REWRITE_TAC [th]) >>
     simp_tac (srw_ss()) [NoAsms, wordsTheory.word_mul_n2w,
       GSYM wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_ASSOC]) >>
  `!q. not_fresh_at sm q ==> lookup_var q u = lookup_var q t` by
    (rpt strip_tac >> qpat_assum `!x. ~MEM x _ ==> _` irule >>
     fs[] >> rpt strip_tac >> gvs[]) >>
  `fin with gas_obs := [] = fin` by
    (qunabbrev_tac `fin` >> Cases_on `tr` >>
     simp[vyperStorageBackendTheory.set_storage_def,
          evaluation_state_component_equality]) >>
  mp_tac (Q.INST [`sa` |-> `sm`, `sb` |-> `r`, `s` |-> `t`, `t` |-> `u`,
                  `id` |-> `sm.cs_next_id`, `esz` |-> `type_slot_size tv`,
                  `code` |-> `nested_pop_suffix hdr tr sm.cs_next_id
                     (type_slot_size tv) x0 x1 x2 x3 x4 x5 x6`]
          nested_pop_suffix_path_mem) >>
  impl_tac >- simp[] >> strip_tac >>
  `alloca_history func (u with vs_inst_idx := LENGTH r.cs_current_insts)` by
    (irule nested_pop_suffix_run_history >> simp[] >> metis_tac[]) >>
  `u.vs_alloca_next = t.vs_alloca_next` by
    (drule nested_pop_suffix_run_alloca_fields >> simp[]) >>
  suspend "finish"
QED

Resume nested_pop_storage_live_suffix_sim_mem[finish]:
  `res = INL (PlaceR (StoragePlace tr
            (slot + n2w (1 + (w2n lenw - 1) * type_slot_size tv)) tv)) /\
   es' = fin` by
    (qpat_x_assum `_ es = (res,es')` mp_tac >>
     simp[Abbr `fin`, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
          vyperStateTheory.assert_def, vyperStateTheory.return_def,
          vyperStorageBackendTheory.write_storage_slot_eq,
          vyperStorageTheory.encode_value_def,
          vyperStorageTheory.encode_base_to_slot_def,
          integer_wordTheory.i2w_def] >> strip_tac >> gvs[] >>
     simp[arithmeticTheory.ADD_COMM, arithmeticTheory.MULT_COMM]) >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`res`, `es'`,
    `OK (u with vs_inst_idx := LENGTH r.cs_current_insts)`] >>
  simp[exprSimVVFrameTheory.vv_post_inst_idx, gas_marked_path_def] >>
  `fin.scopes = es.scopes` by
    (qunabbrev_tac `fin` >> Cases_on `tr` >>
     simp[vyperStorageBackendTheory.set_storage_def]) >>
  conj_tac
  >- (irule nested_pop_suffix_vv_post >>
      qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >> qpat_x_assum `storage_holds _ _ _ _ _ fin u` mp_tac >> simp[]) >>
  conj_tac
  >- (irule vv_store_bound_nonmem >> Cases_on `tr` >> simp[contextTheory.mk_ptr_def]) >>
  conj_tac
  >- (`u.vs_current_bb = t.vs_current_bb` suffices_by simp[] >>
      irule hash_run_inst_seq_current_bb >>
      goal_assum (drule_at Any) >> Cases_on `tr` >>
      simp[nested_pop_suffix_def, mk_inst_def, is_terminator_def]) >>
  qpat_x_assum `alloca_history func (_ with vs_inst_idx := _)` mp_tac >> simp[]
QED
Finalise nested_pop_storage_live_suffix_sim_mem
