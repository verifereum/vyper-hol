Theory entryCreateRawArgExtent
Ancestors
  entryBlueprintRawLength createSizeBlueprintKeywordReplay createSizeByteLength
  exprBodyPreProps exprSimHyps exprSimIfExp allocLimits compileEnv
  exprLowering context loweringPosts valueEncodingDefs valueEncodingProps valueTypingMemoryProps
  vyperTyping vyperTypeSystem vyperValue vyperAST vfmConstants
  venomExecSemantics venomMemProps venomState venomInst arithmetic list words

(* The expression allocation check is the local part of fn_allocs_ok. For
   Bytes[cap] it includes an entire header and the rounded payload capacity. *)
Theorem blueprint_raw_capacity_bound:
  alloc_limits_expr ce e /\ expr_type e = BaseT (BytesT (Dynamic cap)) ==>
  cap < 2 ** 64
Proof
  strip_tac >> drule alloc_limits_expr_type_alloc_ok >>
  simp[type_alloc_ok_def, is_word_type_def, type_memory_bytes_def] >>
  mp_tac (Q.SPEC `cap` word_size_capacity) >>
  simp[word_size_def] >> decide_tac
QED

(* Read typing supplies the capacity bound when replay already identifies
   the successful source operand. A storage materialization may instead
   supply LENGTH bytes <= cap from the selected storage observation. *)
Theorem blueprint_raw_source_length_le_capacity:
  expr_body_pre ce cx env e es /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  bind (eval_expr cx e) (read_result cx) es = (INL (BytesV bytes),ee) ==>
  LENGTH bytes <= cap
Proof
  strip_tac >> drule_all (SRULE [SF ETA_ss] ifexp_body_pre_read_typed) >>
  simp[evaluate_type_def, value_has_type_def] >> IF_CASES_TAC >> simp[]
QED

(* The representation is at u, after snapshot and unwrap. It identifies
   the actual MLOAD input regardless of the original VV location. The frame
   connects the MLOAD's length binding, not the pointer ADD, to the extent ADD. *)
Theorem blueprint_raw_unwrap_length_at_add:
  alloc_limits_expr ce e /\ expr_type e = BaseT (BytesT (Dynamic cap)) /\
  LENGTH bytes <= cap /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_val_rel cx (BaseT (BytesT (Dynamic cap))) (BytesV bytes) raw_op u /\
  cfn ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_create_blueprint_args cfn ce T later [e] ca = ((data,len),cb) /\
  run_inst_seq (emitted_insts cu cb) u = OK r /\
  (!x. len = Var x ==> lookup_var x t = lookup_var x r) ==>
  ?aw. eval_operand len t = SOME aw /\ w2n aw < 2 ** 64
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all blueprint_raw_capacity_bound >> disch_tac >>
  `LENGTH bytes < 2 ** 64` by decide_tac >>
  `?p. eval_operand raw_op u = SOME p /\ mload (w2n p) u = n2w (LENGTH bytes)` by
    (qpat_x_assum `expr_val_rel _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[expr_val_rel_def]) >>
     qpat_x_assum `!tv. evaluate_type _ _ = SOME tv ==> _`
       (qspec_then `BaseTV (BytesT (Dynamic cap))` mp_tac) >>
     simp[is_word_type_def, val_in_memory_def, mem_word_at_eq_mload] >>
     strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
  `w2n (mload (w2n p) u) <= LENGTH bytes` by
    simp[w2n_n2w, MOD_LESS_EQ, ZERO_LT_dimword] >>
  `w2n (mload (w2n p) u) < 2 ** 64` by decide_tac >>
  drule_all raw_blueprint_length_at_add >> simp[]
QED

(* The indexed prefix replay can also hand us the represented length word
   directly at the constructor-preparation exit. In that case only a frame
   for successful SSA lookups is needed across the subsequent keyword steps. *)
Theorem blueprint_raw_replayed_length_at_add:
  alloc_limits_expr ce e /\ expr_type e = BaseT (BytesT (Dynamic cap)) /\
  LENGTH bytes <= cap /\ eval_operand len r = SOME (n2w (LENGTH bytes)) /\
  (!x. len = Var x ==> not_fresh_at cb x) /\
  (!x w. not_fresh_at cb x /\ lookup_var x r = SOME w ==> lookup_var x t = SOME w) /\
  t.vs_labels = r.vs_labels ==>
  eval_operand len t = SOME (n2w (LENGTH bytes)) /\
  w2n (n2w (LENGTH bytes) : bytes32) < 2 ** 64
Proof
  strip_tac >> drule_all blueprint_raw_capacity_bound >> disch_tac >>
  conj_tac >- (irule blueprint_eval_operand_frame >> metis_tac[]) >>
  `w2n (n2w (LENGTH bytes) : bytes32) <= LENGTH bytes` by
    simp[w2n_n2w, MOD_LESS_EQ, ZERO_LT_dimword] >>
  decide_tac
QED
