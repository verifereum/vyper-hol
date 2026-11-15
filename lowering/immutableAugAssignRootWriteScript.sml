(* Empty-path immutable replacement at the post-RHS source state. *)
Theory immutableAugAssignRootWrite
Ancestors
  immutableDeployAssignRestore
  bodyImmutableAugAssignStore bodyImmutableAugAssignExec stmtSimAugAssignPlaceMemory
  exprSimWordArgs vyperPlaceWriteSoundness loweringPosts vyperState
  bodyImmutableAugAssignPaths bodyDeclMemoryCore bodyDeclMemoryCounted allocaFootprint
  emitHelperProps emitHelper venomInst fragExec fragExecMem venomExecSemantics
  compileEnv fragGasMode venomState valueEncodingDefs loweringStateRelDefs
  exprLoweringProps venomMemProps finite_map alist

Theorem immutable_word_store_path_mem[local]:
  emit_void MSTORE [dst;op] sa = ((),sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME w /\ eval_operand op s = SOME word /\
  w2n w + 32 <= s.vs_alloca_next /\ alloca_history func s /\ alloca_inv s ==>
  gas_marked_path T ctx func s 0
    (OK (mstore (w2n w) word s with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func
    (mstore (w2n w) word s with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK (mstore (w2n w) word s)` by
    (`step_inst_base (mk_inst sa.cs_next_id MSTORE [dst;op] []) s =
        OK (mstore (w2n w) word s)` by
       (irule step_MSTORE >> simp[]) >>
     simp[run_inst_seq_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule emit_mstore_mem_ok >> metis_tac[]) >>
  conj_tac
  >- (simp[gas_marked_path_def] >>
      drule_at (Pat `run_inst_seq _ _ = _`) body_decl_zero_gas_path >> simp[]) >>
  irule body_store_memory_history >> simp[] >>
  qexistsl [`s`, `sa`] >> fs[listTheory.EVERY_MEM]
QED

Theorem immutable_augassign_root_write_callback:
  cenv.ce_is_ctor /\ expr_sim_inv cenv cx env ee /\
  stmt_state_rel ctx func cenv cx ee t /\
  ALOOKUP ee.immutables cx.txn.target = SOME imms /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,a) /\
  value_has_type tv a /\ well_formed_type_value tv /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME ity /\
  is_word_type ity /\ local_ptrs_reserved cenv sa /\
  FLOOKUP env.bare_globals (cenv.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME tv /\ type_memory_size tv = 32 /\
  alloca_frame cenv es_entry sa s_entry cenv ee t /\
  store_lays_out tv tv v /\ value_has_type tv v /\
  emit_void MSTORE [dst;op] s3 = ((),sf) /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\ ~t.vs_halted /\
  t.vs_current_bb = s3.cs_current_bb /\
  t.vs_inst_idx = LENGTH s3.cs_current_insts /\
  eval_operand dst t = SOME w /\ w2n w = off /\
  eval_operand op t = SOME (typed_val_to_w256 tv v) /\
  w2n w + 32 <= t.vs_alloca_next /\ alloca_history func t /\
  ~block_is_terminated sf /\ s_entry.vs_alloca_next <= t.vs_alloca_next /\
  (!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
         lookup_var z t = SOME u) /\
  (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b) ==>
  ?ff u. (!tail. write_place cx (ImmutablePlace cenv.ce_module id []) v
                  (ee with gas_obs := tail) = (INL (),ff with gas_obs := tail)) /\
    gas_marked_path T ctx func t 0 (OK u) /\
    stmt_post ctx func cx lctx cenv cenv sa sf es_entry s_entry (INL ())
      (ff with gas_obs := []) u /\ alloca_history func u /\
    s_entry.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  drule_all immutable_augassign_write_source >>
  disch_then (qspec_then `v` assume_tac) >>
  qmatch_asmsub_abbrev_tac `write_place _ _ _ _ = (INL (),ff)` >>
  `immutable_value_admissible tv v /\
   val_in_memory tv v off (mstore off (typed_val_to_w256 tv v) t).vs_memory /\
   immutable_value_bytes_rel tv v
     (mem_bytes_at off (type_memory_size tv)
       (mstore off (typed_val_to_w256 tv v) t).vs_memory)` by
    metis_tac[immutable_augassign_word_encoding, immutable_augassign_word_representation] >>
  `LENGTH t.vs_memory <=
   LENGTH (mstore off (typed_val_to_w256 tv v) t).vs_memory` by
    simp[LENGTH_mstore_eq] >>
  `!a k. regions_disjoint a k off (type_memory_size tv) ==>
    mem_bytes_at a k (mstore off (typed_val_to_w256 tv v) t).vs_memory =
    mem_bytes_at a k t.vs_memory` by
    (rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx ff (mstore off (typed_val_to_w256 tv v) t)` by
    (irule immutable_store_stmt_state_rel >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`env`, `ee`, `id`, `off`, `t`, `sa`, `cenv.ce_module`, `tv`, `ity`, `v`] >>
     simp[venomStateTheory.mstore_def, venomStateTheory.lookup_var_def,
          venomStateTheory.write_memory_with_expansion_def,
          venomStateTheory.venom_state_component_equality]) >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  drule_all immutable_word_store_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule emit_void_same_blocks >> strip_tac >>
  `gas_marked_path T ctx func t 0
     (OK (mstore off (typed_val_to_w256 tv v) t with
       vs_inst_idx := LENGTH sf.cs_current_insts)) /\
   alloca_history func (mstore off (typed_val_to_w256 tv v) t with
       vs_inst_idx := LENGTH sf.cs_current_insts)` by metis_tac[] >>
  qexistsl [`ff`, `mstore off (typed_val_to_w256 tv v) t with
                    vs_inst_idx := LENGTH sf.cs_current_insts`] >>
  simp[] >> conj_tac
  >- (gen_tac >> drule_all immutable_write_place_gas_obs >> simp[]) >>
  irule aug_place_normal_post >> simp[stmt_state_rel_gas_obs] >>
  `ff.scopes = ee.scopes` by simp[Abbr `ff`] >>
  `alloca_frame cenv es_entry sa s_entry cenv ff
     (mstore off (typed_val_to_w256 tv v) t with
        vs_inst_idx := LENGTH sf.cs_current_insts)` by
    (irule immutable_mstore_alloca_frame >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[stmt_state_rel_inst_idx, venomStateTheory.mstore_def,
      venomStateTheory.lookup_var_def, same_blocks_def]
QED
