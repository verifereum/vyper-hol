(* Certified safety window of raw_log's dynamic data operand. *)
Theory bodyFullRawLogDynamicData
Ancestors
  bodySimFull representationCleanPtr exprSimMemDefs exprSimProps
  bodyPtrDefs exprLowering memoryValueDefs compileEnv loweringPosts
  vyperValue valueEncoding valueEncodingDefs venomState words list arithmetic

Theorem raw_log_dynamic_data_window:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  ptr_val_ok cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) op G tn s /\
  expr_store_bound cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) op s /\
  eval_operand op s = SOME w ==>
  (?x. op = Var x /\
       ptr_covers G tn x s (32 + 32 * word_size (LENGTH bs))) /\
  w2n w + 32 + LENGTH bs <= s.vs_alloca_next /\
  (!i. w2n w <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `~is_word_type (BaseT (BytesT (Dynamic cap)))` by simp[is_word_type_def] >>
  `(!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) (w2n w) mem) /\
   ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
      b <= w2n w /\ w2n w + 32 + 32 * word_size (LENGTH bs) <= b + sz` by
    (fs[ptr_val_ok_def, ptr_mem_ok_def] >>
     first_x_assum (qspec_then `BaseTV (BytesT (Dynamic cap))` mp_tac) >>
     simp[val_footprint_def, val_store_size_def]) >>
  `(!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
   (!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tn.t_mem)` by
    (drule robust_val_in_memory_bytes_clean >> simp[]) >>
  `LENGTH bs <= 32 * word_size (LENGTH bs)` by simp[le_word_size_mul] >>
  conj_tac
  >- (qexists `x` >> fs[ptr_covers_def, ptr_val_ok_def, eval_operand_def]) >>
  conj_tac
  >- (fs[expr_store_bound_def, val_store_size_def] >>
      qpat_x_assum `!tv. _` (qspec_then `BaseTV (BytesT (Dynamic cap))` mp_tac) >>
      simp[] >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!i. w2n w <= i /\ i < w2n w + 32 ==> _`
    (qspec_then `i` mp_tac) >>
  qpat_x_assum `!i. w2n w + 32 <= i /\ _ ==> _`
    (qspec_then `i` mp_tac) >>
  simp[] >> decide_tac
QED
