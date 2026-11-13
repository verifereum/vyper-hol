(* Memory-safe operator execution with a successful-write callback. *)
Theory augAssignPlaceSuffixMemory
Ancestors
  augAssignPlaceRhsMemory augAssignPlaceWordStoreMemory
  stmtSimAugAssignPlaceMemory placeStore exprSimProps
  bodyBinopFamiliesMemory bodyBinopFragMemory
  stmtSimProps stmtSimDefs loweringPosts exprSimDefs gasOutcome gasSummary fragGasMode

(* Transport the saved destination and its numerical bound across the operator.
   The same adapter handles local memory, storage, and transient words. *)
Theorem aug_place_word_store_after_operator_mem:
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst;op] s3 = ((),sf) /\
  gas_marked_path T ctx func s 0 (OK t) /\
  (!z u. not_fresh_at s2 z /\ lookup_var z s = SOME u ==>
         lookup_var z t = SOME u) /\
  (!z. dst = Var z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  eval_operand dst s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type ty) /\
  local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv s3 /\
  eval_operand op t = SOME (val_to_w256 v) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  value_has_type dtv v /\ word_value v /\ expr_sim_inv cenv cx env ee /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ storage_place_region cx p /\
  stmt_state_rel ctx func cenv cx ee t /\
  write_place cx p v ee = (INL (),ff) /\
  fn_has_code s3 sf func /\ fn_inst_ids_distinct func /\
  ~t.vs_halted /\ t.vs_current_bb = s3.cs_current_bb /\
  t.vs_inst_idx = LENGTH s3.cs_current_insts /\ alloca_history func t /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (loc = LocMemory ==> w2n w + 32 <= s.vs_alloca_next) ==>
  ?u. gas_marked_path T ctx func t 0 (OK u) /\
      stmt_state_rel ctx func cenv cx ff u /\
      (!z. not_fresh_at s3 z ==> lookup_var z u = lookup_var z t) /\
      (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b) /\
      ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
      u.vs_inst_idx = LENGTH sf.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next = u.vs_alloca_next
Proof
  strip_tac >>
  `eval_operand dst t = SOME w` by
    (metis_tac[aug_place_saved_operand]) >>
  `place_ptr_rel cenv cx t (PlaceR p) w (SOME loc) (Type ty)` by
    (Cases_on `p`
     >- fs[place_ptr_rel_def]
     >- metis_tac[aug_place_memory_ptr_frame] >>
     fs[place_ptr_rel_def]) >>
  `expr_val_rel cx ty v op t` by
    simp[expr_val_rel_def, typed_val_to_w256_word_value] >>
  `!id path entry t0.
     p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
     cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (metis_tac[aug_place_store_entry_types]) >>
  `!z. dst = Var z ==> not_fresh_at s3 z` by metis_tac[] >>
  `(loc = LocMemory ==> w2n w + 32 <= t.vs_alloca_next)` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  drule_all place_store_word_run_mem >> simp[]
QED
