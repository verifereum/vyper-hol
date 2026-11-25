(* Source typing, address precondition and actual count bounds for code Slice. *)
Theory bodySliceExternalSourceMods
Ancestors
  exprBodyPreProps exprSimSliceSource exprSimSliceCapacityRead exprSimHypsDefs
  allocLimits exprLowering supportedExprTraverse vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperTypeSystem vyperInterpreter vyperState vyperAST
  compileEnv valueTypingMemoryProps words list

Triviality external_slice_typing:
  well_typed_expr env (Builtin ann (Slice n) [Builtin ct (Acc Code) [addr];start;len]) ==>
  ct = BaseT (BytesT (Dynamic 24576)) /\ ann = BaseT (BytesT (Dynamic n)) /\
  expr_type addr = BaseT AddressT /\
  slice_operands_ok (Slice n) [Builtin ct (Acc Code) [addr];start;len]
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def, account_item_type_def,
       expr_type_def] >> strip_tac >> gvs[]
QED

Triviality external_slice_address_pre:
  expr_body_pre_mods mods cenv cx env
    (Builtin ann (Slice n) [Builtin ct (Acc Code) [addr];start;len]) es /\
  expr_sim_inv_mods mods cenv cx env fin ==>
  expr_body_pre_mods mods cenv cx env addr fin
Proof
  simp[expr_body_pre_mods_def, well_typed_expr_def, byte_widths_expr_def,
       alloc_limits_expr_def, is_extcode_def, extcode_addr_expr_def,
       int_calls_expr_def, EVERY_APPEND, supported_expr_exists_def,
       expr_has_evm_run_thm, DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt strip_tac >>
  metis_tac[call_evaluation_safe_append_left,call_evaluation_safe_append_right]
QED

Triviality external_slice_reached_count:
  slice_operands_ok (Slice n) [Builtin ct (Acc Code) [addr];start;len] /\
  bind (eval_expr cx len) (read_result cx) st = (INL (IntV (&k)),ee) ==>
  0 < k /\ k <= n
Proof
  strip_tac >>
  `?lt j. len = Literal lt (IntL j) /\ 1 <= j /\ j <= &n` by
    (qpat_x_assum `slice_operands_ok _ _` mp_tac >>
     simp[Once slice_operands_ok_def] >>
     Cases_on `len` >> simp[] >>
     rename1 `Literal lt lit` >> Cases_on `lit` >> simp[]) >>
  qpat_x_assum `len = _` SUBST_ALL_TAC >>
  drule slice_literal_read_length >> intLib.ARITH_TAC
QED

Theorem slice_external_source_mods:
  expr_body_pre_mods mods cenv cx env
    (Builtin ann (Slice n) [Builtin ct (Acc Code) [addr];start;len]) es ==>
  ct = BaseT (BytesT (Dynamic 24576)) /\ ann = BaseT (BytesT (Dynamic n)) /\
  expr_type addr = BaseT AddressT /\
  32+n <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) /\
  type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < dimword (:256) /\
  (!fin. expr_sim_inv_mods mods cenv cx env fin ==>
         expr_body_pre_mods mods cenv cx env addr fin) /\
  (!st ee k. bind (eval_expr cx len) (read_result cx) st = (INL (IntV (&k)),ee) ==>
             0 < k /\ k <= n)
Proof
  strip_tac >>
  drule_then (strip_assume_tac o MATCH_MP external_slice_typing)
    expr_body_pre_mods_well_typed >>
  asm_rewrite_tac[] >> conj_tac
  >- (qspec_then `n` mp_tac word_size_capacity >>
      simp[type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
  conj_tac
  >- (`type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < 2 ** 64` by
        (qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _` mp_tac >>
         simp[expr_body_pre_mods_def, alloc_limits_expr_def, type_alloc_ok_def,
              is_word_type_def]) >>
      fs[dimword_def] >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> drule_all_then ACCEPT_TAC external_slice_address_pre) >>
  rpt strip_tac >> drule_all_then strip_assume_tac external_slice_reached_count >> simp[]
QED
