(* Ordinary semantic adapters for the runtime pointer certificate. *)
Theory bodyPtrEnvBuiltinsRuntimeSemantics
Ancestors exprSimHash exprSimHashBoundary bodyPtrEnvBuiltinsSelectorSuffix bodyPtrEnvBuiltinsSelectorBytes
  vyperValue vyperTypeBytesCrypto byte venomMemProps rich_list
  loweringPosts exprLoweringProps compileEnv venomState venomInst builtinHashing vyperTyping
  valueEncoding valueEncodingProofs vyperValue vyperTypeSystem words list exprSimProps
  entrySinkExtraction freshWrites bodyPtrEnvBuiltinsMask

Theorem method_id_mask_frame_transport:
  emit_op SHR [Lit 224w; hash] sh = (sel,sn) /\
  emit_op SHL [Lit 224w; sel] sn = (op,sb) /\
  eval_operand hash h = SOME w /\
  stmt_state_rel ctx fn cenv cx es h /\ local_ptrs_reserved cenv sh /\
  wb_frame cenv es es' sa s0 h /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sh.cs_next_var /\ sa.cs_next_id <= sh.cs_next_id ==>
  ?t. run_inst_seq (emitted_insts sh sb) h = OK t /\
    eval_operand op t = SOME
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 4)))
        (BytesV (TAKE 4 (word_to_bytes w T)))) /\
    stmt_state_rel ctx fn cenv cx es t /\ wb_frame cenv es es' sa s0 t /\
    (t with vs_vars := h.vs_vars) = h
Proof
  strip_tac >> drule_all method_id_mask_frame >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule wb_frame_allocating_tail >> simp[] >>
  qexistsl_tac [`h`, `es.scopes`, `sh`] >>
  gvs[venom_state_component_equality]
QED

Theorem method_id_selector_word_bytes:
  LENGTH bs = 4 ==>
  TAKE 4 (word_to_bytes
    (typed_val_to_w256 (BaseTV (BytesT (Fixed 4))) (BytesV bs)) T) = bs
Proof
  strip_tac >>
  `PAD_RIGHT (0w:word8) 32 bs = TAKE 32 (bs ++ REPLICATE 31 0w)` by
    (simp[PAD_RIGHT, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >> EVAL_TAC) >>
  simp[typed_val_to_w256_def, word_of_bytes_be_def, selector_padded_word_bytes]
QED

Theorem method_id_fixed_hash_root_frame:
  compile_keccak256_bytesm arg (LENGTH bs) sa = (op,sb) /\
  (!x. arg = Var x ==> not_fresh_at sa x) /\
  eval_operand arg s = SOME w /\ LENGTH bs <= 32 /\
  TAKE (LENGTH bs) (word_to_bytes_be w) = bs /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  wb_frame cenv es es sa s t
Proof
  strip_tac >> drule_all compile_keccak256_bytesm_frame >> strip_tac >>
  gvs[] >> simp[wb_frame_def] >> conj_tac
  >- metis_tac[] >>
  irule locals_kept_regions >> metis_tac[]
QED

Theorem method_id_memory_hash_root_frame:
  compile_keccak256_bytes arg sa = (op,sb) /\
  (!x. arg = Var x ==> not_fresh_at sa x) /\
  eval_operand arg s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  wb_frame cenv es es sa s t
Proof
  strip_tac >> drule_all compile_keccak256_bytes_run >> strip_tac >>
  gvs[] >> gvs[venom_state_component_equality] >>
  simp[wb_frame_def, locals_kept_mem]
QED

Theorem method_id_fixed_typed_root_frame:
  expr_post ctx fn cenv cx e es sa sm s0 es' (BytesV bs) arg s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Fixed m))) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\
  compile_method_id_hash (expr_type e) arg sm = (op,sh) /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sm /\ fn_has_code sm sh fn /\
  run_inst_seq (emitted_insts sm sh) s = OK t ==>
  wb_frame cenv es' es' sm s t
Proof
  strip_tac >> `m <= 32` by gvs[evaluate_type_def, AllCaseEqs()] >>
  drule_at (Pat `expr_type _ = _`) hash_fixed_post_view >>
  disch_then drule_all >> strip_tac >>
  `stmt_state_rel ctx fn cenv cx es' s` by fs[expr_post_def] >>
  gvs[compile_method_id_hash_def] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sm.cs_next_var)]) (fn_insts fn)` by
    (irule (cj 1 (Q.INST [`sha` |-> `F`] hash_fixed_alloca_code)) >> simp[] >> metis_tac[]) >>
  irule method_id_fixed_hash_root_frame >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem method_id_memory_typed_root_frame:
  expr_post ctx fn cenv cx e es sa sm s0 es' v arg s /\
  ((?cap bs. expr_type e = BaseT (BytesT (Dynamic cap)) /\ v = BytesV bs /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap)))) \/
   (?cap str. expr_type e = BaseT (StringT cap) /\ v = StringV str /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT cap)))) /\
  compile_method_id_hash (expr_type e) arg sm = (op,sh) /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\
  run_inst_seq (emitted_insts sm sh) s = OK t ==>
  wb_frame cenv es' es' sm s t
Proof
  strip_tac
  >- (gvs[] >> drule_at (Pat `expr_type _ = _`) hash_dynamic_post_view >>
      disch_then drule >> simp[] >> strip_tac >>
      gvs[compile_method_id_hash_def] >>
      irule method_id_memory_hash_root_frame >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[]) >>
  gvs[] >> drule_at (Pat `expr_type _ = _`) hash_string_post_view >>
  disch_then drule >> simp[] >> strip_tac >>
  gvs[compile_method_id_hash_def] >>
  irule method_id_memory_hash_root_frame >> goal_assum (drule_at Any) >>
  simp[] >> qexistsl_tac [`arg`, `MAP (n2w o ORD) str`, `op`, `sh`] >> simp[]
QED

Theorem method_id_hash_typed_root_frame:
  expr_post ctx fn cenv cx e es sa sm s0 es' v arg s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  compile_method_id_hash (expr_type e) arg sm = (op,sh) /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sm /\ fn_has_code sm sh fn /\
  run_inst_seq (emitted_insts sm sh) s = OK t ==>
  wb_frame cenv es' es' sm s t
Proof
  strip_tac >> Cases_on `bty` >> gvs[is_bytes_or_string_type_def]
  >- (Cases_on `v` >> gvs[value_has_type_def] >>
      irule method_id_memory_typed_root_frame >> simp[] >> metis_tac[]) >>
  rename1 `expr_type e = BaseT (BytesT bd)` >>
  Cases_on `bd` >> Cases_on `v` >> gvs[value_has_type_def]
  >- (drule_at (Pat `expr_type _ = _`) method_id_fixed_typed_root_frame >>
      disch_then irule >> simp[value_has_type_def] >> metis_tac[]) >>
  irule method_id_memory_typed_root_frame >> simp[] >> metis_tac[]
QED

Theorem method_id_hash_typed_shape:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  compile_method_id_hash (expr_type e) arg sm = (op,sh) ==>
  same_blocks sm sh /\
  sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sh)
Proof
  strip_tac >> Cases_on `bty` >>
  gvs[is_bytes_or_string_type_def, compile_method_id_hash_def]
  >- (irule keccak_suffix_shape >> metis_tac[]) >>
  Cases_on `b` >> gvs[compile_method_id_hash_def] >>
  irule keccak_suffix_shape >> metis_tac[]
QED

Theorem method_id_hash_mask_semantics:
  expr_post ctx fn cenv cx e es sa sm s0 es' v arg s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (arg,sm) /\
  compile_method_id_hash (expr_type e) arg sm = (hash,sh) /\
  emit_op SHR [Lit 224w; hash] sh = (sel,sn) /\
  emit_op SHL [Lit 224w; sel] sn = (op,sb) /\
  fn_has_code sm sh fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb ==>
  ?h t bs. run_inst_seq (emitted_insts sm sh) s = OK h /\
    run_inst_seq (emitted_insts sh sb) h = OK t /\
    run_inst_seq (emitted_insts sm sb) s = OK t /\ LENGTH bs = 32 /\
    eval_operand hash h = SOME
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs)) /\
    eval_operand op t = SOME
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 4))) (BytesV (TAKE 4 bs))) /\
    stmt_state_rel ctx fn cenv cx es' t /\ wb_frame cenv es' es' sm s t /\
    ~h.vs_halted /\ h.vs_current_bb = sh.cs_current_bb /\
    (t with vs_vars := h.vs_vars) = h /\
    (!ann. builtin_result cx es'.accounts ann MethodId [expr_type e] [v] =
      INL (BytesV (TAKE 4 bs)))
Proof
  strip_tac >> drule_all method_id_hash_typed_post_run >> strip_tac >>
  drule_all method_id_hash_typed_root_frame >> strip_tac >>
  drule_all method_id_hash_grows >> strip_tac >>
  `local_ptrs_reserved cenv sh` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all method_id_mask_frame_transport >> strip_tac >>
  drule_all method_id_hash_typed_shape >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `emitted_insts sm sb = emitted_insts sm sh ++ emitted_insts sh sb` by
    (irule emitted_insts_append >> simp[] >>
     drule_all method_id_mask_compile_code >> strip_tac >> simp[]) >>
  `run_inst_seq (emitted_insts sm sb) s = OK t'` by
    metis_tac[run_inst_seq_append] >>
  qexistsl_tac [`t`, `t'`, `bs`] >>
  gvs[same_blocks_def, hash_full_bytes_roundtrip]
QED
