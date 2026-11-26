(* The live source window for a RawCreate bytecode snapshot. *)
Theory bodyCreateRawMemoryInputMods
Ancestors
  bodyFullPostsMods rawCallBufferPtr exprSimMemDefs exprSimProps
  loweringPosts bodyPtrDefs valueEncodingDefs valueEncodingProps
  vyperStorageFootprint vyperTyping vyperValue venomState words arithmetic
  context compileEnv loweringStateRelDefs finite_map pred_set

Theorem raw_memory_operand[local]:
  vv_holds_mods cenv cx (BaseT (BytesT (Dynamic n))) raw vv ee t /\
  ptr_vv_ok cx (BaseT (BytesT (Dynamic n))) raw vv ee G tn t /\
  read_result cx raw ee = (INL (BytesV bs),ee) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
  ?w. eval_operand (vv_operand vv) t = SOME w /\
      op_taint tn (vv_operand vv) = {} /\
      ptr_mem_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs)
        (vv_operand vv) G tn t
Proof
  strip_tac >> Cases_on `vv` >>
  fs[vv_location_def, vv_operand_def, vv_holds_mods_def, vv_holds_def,
     ptr_vv_ok_def, ptr_val_ok_def, is_word_type_def, expr_val_rel_def] >>
  metis_tac[]
QED

Theorem raw_memory_frontier[local]:
  vv_store_bound cx (BaseT (BytesT (Dynamic n))) lt ee raw vv t /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) /\
  read_result cx raw ee = (INL (BytesV bs),ee) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  eval_operand (vv_operand vv) t = SOME w ==>
  w2n w + 32 + LENGTH bs <= t.vs_alloca_next
Proof
  strip_tac >>
  `w2n w + val_store_size (BaseTV (BytesT (Dynamic n))) (BytesV bs) <=
     t.vs_alloca_next` by
    (Cases_on `vv` >>
     fs[vv_location_def, vv_operand_def, vv_store_bound_def, is_word_type_def,
        val_store_size_def] >> metis_tac[]) >>
  qspec_then `LENGTH bs` assume_tac le_word_size_mul >>
  fs[val_store_size_def] >> decide_tac
QED

Theorem raw_create_memory_input_mods:
  vv_post_mods (storage_trace_horizon ee.storage_trace) ctx func cenv cx e
      es sa a s ee raw vv t /\
  ptr_vv_ok cx (post_value_type cenv e) raw vv ee G1 tn1 t /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee raw vv t /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) /\
  read_result cx raw ee = (INL (BytesV bs),ee) /\
  (!src. vv_operand vv = Var src ==> not_fresh_at a src) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
  ?src w. vv_operand vv = Var src /\
    not_fresh_at a src /\
    eval_operand (Var src) t = SOME w /\
    ptr_covers G1 tn1 src t (32 + LENGTH bs) /\
    w2n w + 32 + LENGTH bs <= t.vs_alloca_next /\
    mload (w2n w) t = n2w (LENGTH bs) /\
    read_memory (w2n w+32) (LENGTH bs) t = bs /\
    (!i. w2n w <= i /\ i < w2n w+32+LENGTH bs ==> i NOTIN tn1.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type cenv e = BaseT (BytesT (Dynamic n))` by
    simp[post_value_type_bytestring, is_bytestring_type_def] >>
  `vv_holds_mods cenv cx (BaseT (BytesT (Dynamic n))) raw vv ee t` by
    fs[vv_post_mods_def] >>
  qhdtm_x_assum `vv_post_mods` kall_tac >>
  qpat_x_assum `post_value_type _ _ = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  drule_all_then (qx_choose_then `w` strip_assume_tac) raw_memory_operand >>
  drule_all_then assume_tac raw_memory_frontier >>
  drule_all_then (qx_choosel_then [`src`,`b`,`len`] strip_assume_tac)
    ptr_mem_ok_dynamic_bytes_site >>
  drule_all_then strip_assume_tac ptr_mem_ok_dynamic_bytes_clean >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) (w2n w) t.vs_memory` by
    (qhdtm_assum `ptr_mem_ok` (drule_all_then strip_assume_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
     qpat_assum `!mem. mem_agree_outside _ _ mem ==> _`
       (qspec_then `t.vs_memory` mp_tac) >> simp[mem_agree_outside_def]) >>
  `eval_operand (Var src) t = SOME w /\ op_taint tn1 (Var src) = {}` by
    (qpat_assum `vv_operand vv = Var src` (fn th => fs[th])) >>
  `ptr_covers G1 tn1 src t (32 + LENGTH bs)` by
    (pure_rewrite_tac[ptr_covers_def] >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`w`,`b`,`len`] >> fs[eval_operand_def]) >>
  `mload (w2n w) t = n2w (LENGTH bs) /\ read_memory (w2n w+32) (LENGTH bs) t = bs` by
    (qhdtm_assum `val_in_memory` mp_tac >>
     pure_rewrite_tac[val_in_memory_def] >>
     simp[NoAsms, mem_word_at_eq_mload, read_memory_def, mem_bytes_at_def]) >>
  qpat_x_assum `vv_location vv = NONE \/ _` kall_tac >>
  qexistsl [`src`,`w`] >> simp[] >>
  qx_gen_tac `i` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `i < w2n w + 32`
  >- (qpat_assum `!j. w2n w <= j /\ j < w2n w + 32 ==> _` irule >> simp[]) >>
  qpat_assum `!j. w2n w + 32 <= j /\ j < _ ==> _` irule >>
  simp[GSYM NOT_LESS]
QED
