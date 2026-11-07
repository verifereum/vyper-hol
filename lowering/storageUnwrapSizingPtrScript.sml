(* Actual located annotation and rounded storage-copy size at the reason caller. *)
Theory storageUnwrapSizingPtr
Ancestors
  exprSimHyps loweringPosts valueEncodingProps exprSimStorageCopy
  exprLowering compileEnv context vyperValue arithmetic storageStringSourcePtr
  vfmConstants

Theorem located_unwrap_copy_sizing:
  expr_body_pre cenv cx env e es /\
  vv_holds cenv cx (expr_type e) tv (LocatedValue ann p) es' s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  ~is_word_type (expr_type e) ==>
  ann = expr_type e /\
  type_memory_bytes cenv ann = type_memory_size ty /\
  type_memory_bytes cenv ann = 32 * type_slot_size ty /\
  (type_memory_bytes cenv ann + 31) DIV 32 = type_slot_size ty /\
  type_memory_bytes cenv ann < 2 ** 64
Proof
  strip_tac >>
  `ann = expr_type e` by gvs[vv_holds_def] >>
  drule_all expr_body_pre_copy_ok >> strip_tac >>
  simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
  simp[arithmeticTheory.DIV_MULT] >>
  gvs[valueEncodingPropsTheory.type_memory_size_slots]
QED

Theorem storage_string_runtime_copy_capacity:
  storage_holds cx tr ty tv a es s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  read_result cx tv es = (INL (StringV str),es) ==>
  32 + 32 * word_size (LENGTH str) <= 32 * type_slot_size (BaseTV (StringT max))
Proof
  strip_tac >> drule_all storage_holds_string_source_resources >> strip_tac >>
  `word_size (LENGTH str) <=
   word_size (32 * (type_slot_size (BaseTV (StringT max)) - 1))` by
    (irule word_size_monotone >> simp[]) >>
  `word_size (32 * (type_slot_size (BaseTV (StringT max)) - 1)) =
   type_slot_size (BaseTV (StringT max)) - 1` by
    (simp[word_size_def] >> once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
     simp[arithmeticTheory.DIV_MULT]) >> decide_tac
QED

Theorem located_storage_unwrap_layout:
  vv_holds cenv cx t tv (LocatedValue ann p) es s /\
  ~is_word_type t /\ (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  unwrap_value cenv (LocatedValue ann p) =
    do buf <- compile_alloc_buffer (type_memory_bytes cenv ann);
       (if (type_memory_bytes cenv ann + 31) DIV 32 = 1 then
          do v <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
                    [p.ptr_operand];
             emit_void MSTORE [buf.buf_operand;v] od
        else do compile_word_copy_loop p.ptr_operand buf.buf_operand
                  ((type_memory_bytes cenv ann + 31) DIV 32) p.ptr_location LocMemory F;
                return () od);
       return buf.buf_operand
    od
Proof
  strip_tac >> `ann = t` by gvs[vv_holds_def] >>
  simp[unwrap_value_def] >>
  Cases_on `p.ptr_location = LocStorage` >> gvs[] >>
  simp[ensure_storage_memory_layout]
QED
