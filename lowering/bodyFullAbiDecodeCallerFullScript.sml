Theory bodyFullAbiDecodeCallerFull
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeSemantic bodySimFull
  gasOutcomeFullCompose abiBoundaryChecks exprSimProps bodyPtrDefs
  exprSimAbiDecodeEntryLayout exprSimAbiDecodeEntryTyping
  abiEncoderObserver fragGasPath fragGasOriginPtrLoop
  valueEncodingProps valueTypingMemoryProps venomState words finite_map
  exprSimMemDefs loweringPosts exprLowering vyperAST context vyperState

(* A singleton ABI wrapper has precisely the memory representation of its
   result.  In particular, robustness is typed, not cleanliness of unused
   output capacity. *)
Theorem abi_decode_caller_pointer_posts[local]:
  ann = ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv <= cap /\ d + cap < dimword (:256) /\
  d + cap <= t.vs_alloca_next /\ out = Var output /\
  lookup_var output t = SOME (n2w d) /\ FLOOKUP G output = SOME (d,cap) /\
  op_taint tn out = {} /\ val_wf tv v /\ val_in_memory tv v d t.vs_memory /\
  (!v. val_wf (if wrapped then TupleTV [tv] else tv) v /\
       val_in_memory (if wrapped then TupleTV [tv] else tv) v d t.vs_memory ==>
       !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
         val_in_memory (if wrapped then TupleTV [tv] else tv) v d mem) ==>
  ptr_vv_ok cx (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
    (Value v) (LocatedValue ann (mk_ptr out LocMemory)) es G tn t /\
  ptr_buf_ok ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]) out G t /\
  vv_store_bound cx (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
    (lowered_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e])) es
    (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory tv v d mem` by
    (Cases_on `wrapped` >> gvs[] >-
       (first_x_assum (qspec_then `ArrayV (TupleV [v])` mp_tac) >>
        simp[valueEncodingDefsTheory.val_wf_def, val_in_memory_singleton_tuple])) >>
  `d < dimword (:256)` by decide_tac >>
  `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
  simp[ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, vv_store_bound_def,
       post_value_type_def, lowered_value_type_def, expr_type_def, mk_ptr_def,
       read_result_def, return_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >> simp[wordsTheory.w2n_n2w] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_REFL,
            arithmeticTheory.LESS_EQ_ADD, arithmeticTheory.ADD_ASSOC]
QED
