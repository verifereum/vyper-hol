(* Empty-path immutable replacement at the post-RHS source state. *)
Theory immutableAugAssignRootWrite
Ancestors
  immutableWordStoreMemory immutableWriteReplay stmtSimAugAssignPlaceMemory
  exprSimWordArgs vyperPlaceWriteSoundness loweringPosts vyperState
  bodyImmutableAugAssignPaths

Theorem immutable_augassign_root_write_callback:
  cenv.ce_is_ctor /\ expr_sim_inv cenv cx env ee /\
  stmt_state_rel ctx func cenv cx ee t /\
  ALOOKUP ee.immutables cx.txn.target = SOME imms /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,a) /\
  value_has_type tv a /\ well_formed_type_value tv /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME tv /\ type_memory_size tv = 32 /\
  alloca_frame cenv es_entry sa s_entry cenv ee t /\
  store_lays_out etv tv v /\ value_has_type tv v /\
  emit_void MSTORE [dst;op] s3 = ((),sf) /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\ ~t.vs_halted /\
  t.vs_current_bb = s3.cs_current_bb /\
  t.vs_inst_idx = LENGTH s3.cs_current_insts /\
  eval_operand dst t = SOME w /\ w2n w = off /\
  eval_operand op t = SOME (typed_val_to_w256 etv v) /\
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
  `mutable_place_path tv [] /\ mem_path_offset tv [] = SOME (0,tv) /\
   evaluate_subscripts tv a [] = INL a /\
   assign_subscripts tv a [] (Replace v) = INL v` by
    simp[mutable_place_path_def, mem_path_offset_def,
         evaluate_subscripts_def, assign_subscripts_def] >>
  drule_all (immutable_word_write_mem |> SPEC_ALL |>
    Q.INST [`path` |-> `[]`, `k` |-> `0`, `ptv` |-> `tv`,
            `old` |-> `a`, `updated` |-> `v`] |>
    SRULE [mem_path_offset_def, mutable_place_path_def,
           evaluate_subscripts_def, assign_subscripts_def] |> GEN_ALL) >>
  strip_tac >>
  qexistsl [`es'`, `mstore off (typed_val_to_w256 etv v) t with
                       vs_inst_idx := LENGTH sf.cs_current_insts`] >>
  simp[venomStateTheory.lookup_var_def, venomStateTheory.mstore_def,
       venomStateTheory.write_memory_with_expansion_def] >>
  conj_tac
  >- (gen_tac >> drule_all immutable_replace_write_replay >>
      strip_tac >> gvs[] >>
      mp_tac (immutable_replace_write_replay |> SPEC_ALL |>
        Q.INST [`es` |-> `ee with gas_obs := tail`] |> GEN_ALL) >>
      simp[]) >>
  irule aug_place_normal_post >>
  simp[stmt_state_rel_gas_obs] >>
  `es'.scopes = ee.scopes` by
    (drule_all immutable_replace_write_replay >> strip_tac >> gvs[]) >>
  `alloca_frame cenv es_entry sa s_entry cenv es'
     (mstore off (typed_val_to_w256 etv v) t with
        vs_inst_idx := LENGTH sf.cs_current_insts)` by
    (irule immutable_mstore_alloca_frame >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[venomStateTheory.mstore_def, venomStateTheory.lookup_var_def]
QED
