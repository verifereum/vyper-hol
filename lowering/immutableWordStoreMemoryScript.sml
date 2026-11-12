(* Constructor immutable scalar replacement: source replay and safe store. *)
Theory immutableWordStoreMemory
Ancestors
  immutablePathReplace immutableWriteReplay immutableWordStoreFrame
  exprSimPopNestedImmutableDeploy exprSimPopImmutableTarget
  bodySimAugPlaceStore stmtSimDeclStore exprSimProps exprLoweringProps
  loweringSlice loweringStateRelDefs loweringPosts vyperPlaceStatePreservation
  vyperState vyperTyping venomState valueEncodingDefs compileEnv
  fragGasMode finite_map alist

Theorem immutable_word_replace_state_rel[local]:
  cenv.ce_is_ctor /\ expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,a) /\
  mutable_place_path tv path /\ value_has_type tv a /\ well_formed_type_value tv /\
  mem_path_offset tv path = SOME (k,ptv) /\
  evaluate_subscripts tv a path = INL old /\
  assign_subscripts tv a path (Replace v) = INL updated /\
  store_lays_out etv ptv v /\ value_has_type ptv v /\
  es' = es with immutables :=
    (cx.txn.target,set_source_immutables cenv.ce_module
      (get_source_immutables cenv.ce_module imms |+ (id,(tv,updated))) imms) ::
    ADELKEY cx.txn.target es.immutables ==>
  stmt_state_rel ctx func cenv cx es'
    (mstore (off+k) (typed_val_to_w256 etv v) s)
Proof
  strip_tac >> drule mem_path_offset_sound >> strip_tac >>
  `immutable_value_admissible tv a /\ val_in_memory tv a off s.vs_memory` by
    (gvs[stmt_state_rel_def, state_rel_def, immutables_rel_def] >>
     first_x_assum drule_all >> simp[]) >>
  `val_wf tv a` by metis_tac[immutable_admissible_val_wf] >>
  `well_formed_type_value ptv` by metis_tac[subscripts_type_well_formed] >>
  `immutable_value_admissible ptv v` by
    (irule immutable_word_replacement_admissible >> gvs[store_lays_out_def]) >>
  `immutable_value_admissible tv updated` by
    (irule immutable_replace_path_admissible >> metis_tac[]) >>
  drule_all aug_place_path_mstore >> strip_tac >>
  `immutable_value_bytes_rel tv updated
     (mem_bytes_at off (type_memory_size tv)
       (mstore (off+k) (typed_val_to_w256 etv v) s).vs_memory)` by
    (irule immutable_admissible_memory_bytes >> simp[]) >>
  irule immutable_word_store_stmt_frame >>
  goal_assum (drule_at Any) >> simp[] >> gvs[store_lays_out_def] >> metis_tac[]
QED

Theorem immutable_word_write_mem:
  cenv.ce_is_ctor /\ expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,a) /\
  mutable_place_path tv path /\ value_has_type tv a /\ well_formed_type_value tv /\
  mem_path_offset tv path = SOME (k,ptv) /\
  evaluate_subscripts tv a path = INL old /\
  assign_subscripts tv a path (Replace v) = INL updated /\
  store_lays_out etv ptv v /\ value_has_type ptv v /\
  emit_void MSTORE [dst;op] sa = ((),sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME w /\ w2n w = off+k /\
  eval_operand op s = SOME (typed_val_to_w256 etv v) /\
  w2n w + 32 <= s.vs_alloca_next /\ alloca_history func s ==>
  ?es' t.
    write_place cx (ImmutablePlace cenv.ce_module id path) v es = (INL (),es') /\
    stmt_state_rel ctx func cenv cx es' t /\
    wb_frame cenv es es' sa s t /\
    alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_allocas = s.vs_allocas /\ (!x. lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    gas_marked_path T ctx func s 0 (OK t) /\
    t = (mstore (off+k) (typed_val_to_w256 etv v) s with
           vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  drule_all immutable_replace_write_replay >> strip_tac >>
  qmatch_asmsub_abbrev_tac `write_place cx _ _ _ = (INL (),es')` >>
  `stmt_state_rel ctx func cenv cx es'
     (mstore (off+k) (typed_val_to_w256 etv v) s)` by
    (irule immutable_word_replace_state_rel >>
     goal_assum (drule_at Any) >> simp[Abbr `es'`] >> metis_tac[]) >>
  `alloca_inv s` by gvs[stmt_state_rel_def] >>
  drule_all immutable_word_store_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule emit_void_same_blocks >> strip_tac >>
  `k + 32 <= type_memory_size tv` by
    (drule mem_path_offset_sound >> gvs[store_lays_out_def]) >>
  `wb_frame cenv es es sa s (mstore (off+k) (typed_val_to_w256 etv v) s)` by
    (irule immutable_store_wb_frame >> metis_tac[]) >>
  qexistsl [`es'`, `mstore (off+k) (typed_val_to_w256 etv v) s with
                          vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
      simp[wb_frame_def, locals_kept_def, popped_kept_def, Abbr `es'`, lookup_var_def]) >>
  simp[lookup_var_def, mstore_def, write_memory_with_expansion_def] >>
  gvs[same_blocks_def, mstore_def]
QED
