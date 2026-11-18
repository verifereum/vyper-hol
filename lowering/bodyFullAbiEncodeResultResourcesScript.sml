Theory bodyFullAbiEncodeResultResources
Ancestors
  exprSimMemDefs rawCallBufferPtr typeLayoutProps

(* The rounded live value and the whole lowered buffer have separate bounds.
   The result's annotation need not describe the allocated capacity. *)
Theorem abi_encode_bytes_full_resources:
  expr_type (TypeBuiltin ann (AbiEncode ensure mid) target args) =
    BaseT (BytesT (Dynamic N)) /\
  eval_operand (Var q) s = SOME w /\ ptr_covers G tn q s capacity /\
  w2n w + capacity <= s.vs_alloca_next /\
  val_store_size (BaseTV (BytesT (Dynamic N))) (BytesV payload) <= capacity /\
  type_memory_bytes ce
    (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args)) <= capacity /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory (BaseTV (BytesT (Dynamic N))) (BytesV payload) (w2n w) mem) ==>
  vv_store_bound cx
    (post_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args))
    (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args))
    ee (Value (BytesV payload)) (LocatedValue ann (mk_ptr (Var q) LocMemory)) s /\
  ptr_vv_ok cx
    (post_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args))
    (Value (BytesV payload)) (LocatedValue ann (mk_ptr (Var q) LocMemory)) ee G tn s /\
  ptr_buf_ok ce (TypeBuiltin ann (AbiEncode ensure mid) target args) (Var q) G s
Proof
  strip_tac >>
  reverse conj_tac
  >- (reverse conj_tac
      >- (irule ptr_buf_ok_from_covers >>
          qexistsl_tac [`capacity`, `tn`] >> simp[]) >>
      qpat_assum `ptr_covers _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
      simp[loweringPostsTheory.post_value_type_def, bodyPtrDefsTheory.ptr_vv_ok_def,
           contextTheory.mk_ptr_def, vyperStateTheory.read_result_def,
           vyperStateTheory.return_def, bodyPtrDefsTheory.ptr_mem_ok_def] >>
      rpt gen_tac >> strip_tac >> drule valueLoadPropsTheory.evaluate_type_base_identity >>
      strip_tac >> gvs[venomStateTheory.eval_operand_def] >> decide_tac) >>
  qmatch_goalsub_abbrev_tac `vv_store_bound _ _ low` >>
  `?M. low = BaseT (BytesT (Dynamic M))` by
    simp[Abbr `low`, Once exprLoweringTheory.lowered_value_type_def] >>
  `type_memory_bytes ce low <= capacity` by simp[Abbr `low`] >>
  simp[loweringPostsTheory.post_value_type_def, vv_store_bound_def,
       contextTheory.mk_ptr_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule valueLoadPropsTheory.evaluate_type_base_identity >>
      strip_tac >> gvs[] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `type_memory_size tvt <= capacity` by
    (drule type_memory_bytes_base_evaluated >> disch_then (qspec_then `ce` mp_tac) >>
     gvs[]) >>
  decide_tac
QED
