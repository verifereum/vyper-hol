Theory extRetRecursiveInterfacePtr
Ancestors abiEncoderInput abiEncoderOpenInput abiEncoderInputFrame
  extRetRecursiveDynamicProbePtr stmtLowering exprLowering compileEnv
  emitHelper list rich_list

(* Project the zero-span sibling and the live bytes child without requiring
   a positive memory extent for every member. Robustness uses the same
   arbitrary-memory quantifier as ptr_mem_ok. *)
Theorem robust_empty_bytes_complex_children:
  (!mem. mem_agree_outside bad original mem ==>
    abi_encoder_input
      (AbiComplex [(AbiCopy 0,0,0,F); (AbiBytestring 2,32,64,T)])
      (Tuple [Tuple []; Bytes NONE]) (ListV [ListV []; BytesV bs]) sb cap mem) ==>
  (!mem. mem_agree_outside bad original mem ==>
    abi_encoder_input (AbiCopy 0) (Tuple []) (ListV []) sb 0 mem) /\
  (!mem. mem_agree_outside bad original mem ==>
    abi_encoder_input (AbiBytestring 2) (Bytes NONE) (BytesV bs) sb 64 mem)
Proof
  strip_tac >> conj_tac >> rpt strip_tac >>
  first_x_assum drule >>
  simp[abi_encoder_complex_input_iff, abi_encoder_tuple_type_def,
       abi_encoder_member_span_def] >> strip_tac >> gvs[]
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >> first_x_assum (qspec_then `1` mp_tac) >>
  simp[abi_encoder_member_span_def]
QED

(* This is the actual Return compiler tail, after lower_value, not merely
   the Boolean needs_normalize test. *)
Theorem narrow_call_return_normalization_tail:
  widening_probe_cenv.ce_return_pc = NONE ==>
  (let ty = ArrayT (BaseT (UintT 256)) (Dynamic 2) in
   let e = Call ty (IntCall (NONE,"f")) [] NONE in
   compile_stmt widening_probe_cenv lctx ty (Return (SOME e))) =
  (do op <- lower_value compile_expr widening_probe_cenv
        (ArrayT (BaseT (UintT 256)) (Dynamic 2))
        (Call (ArrayT (BaseT (UintT 256)) (Dynamic 2))
          (IntCall (NONE,"f")) [] NONE);
      buf <- compile_alloc_buffer
        (type_memory_bytes widening_probe_cenv (ArrayT (BaseT (UintT 256)) (Dynamic 2)));
      compile_store_memory_typed widening_probe_cenv buf.buf_operand
        (ArrayT (BaseT (UintT 256)) (Dynamic 2)) op
        (ArrayT (BaseT (UintT 256)) (Dynamic 1));
      compile_external_return (SOME buf.buf_operand) F widening_probe_cenv.ce_raw_return
        widening_probe_cenv.ce_ret_enc_info widening_probe_cenv.ce_max_return_size
        (FST widening_probe_cenv.ce_nonreentrant)
        (FST (SND widening_probe_cenv.ce_nonreentrant))
        (FST (SND (SND widening_probe_cenv.ce_nonreentrant)))
        (SND (SND (SND widening_probe_cenv.ce_nonreentrant)))
   od)
Proof
  strip_tac >>
  simp[Once compile_stmt_def, LET_THM, lowered_value_type_def,
       is_word_type_def, is_bytestring_type_def] >>
  simp[widening_probe_cenv_def, lowered_value_type_def] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  gen_tac >>
  qmatch_goalsub_abbrev_tac `lower_value cc ce ty e x` >>
  Cases_on `lower_value cc ce ty e x` >> simp[] >>
  qmatch_goalsub_abbrev_tac `compile_alloc_buffer bytes cs1` >>
  Cases_on `compile_alloc_buffer bytes cs1` >> simp[] >>
  qmatch_goalsub_abbrev_tac `compile_store_memory_typed ce' dst dt src st cs2` >>
  Cases_on `compile_store_memory_typed ce' dst dt src st cs2` >> simp[]
QED

(* Interface checkpoint (not claims of recursive pointer correctness).

   SOURCE: abiEncoderSourceProducer.abi_encoder_uniform_source consumes
   abi_enc_plan env ty ei and yields source_rep env ty ei ct.  The transport
   theorem in abiEncoderSourceAggregate additionally consumes evaluate_type,
   value_has_type, vyper_to_abi = SOME av, and val_in_memory, and yields an
   encoding-equivalent rv with abi_encoder_open_input ei ct rv sb
   (type_memory_size tv) mem.  No assignability is required by transport.
   However retAbiPlanProps.type_to_abi_enc_info_plan requires assignable_type,
   tenv SUBMAP tenv0, struct-field consistency for both maps, local struct keys,
   and the memory-size/evaluate_type correspondence.  The actual recursive
   supported-place return domain does not supply assignability (mixed empty
   struct fields are admitted).  Thus obtaining the plan remains unresolved.
   Nonassignable aggregates are not inherently excluded by val_in_memory:
   the producer's tuple/struct cases project children, including zero extents.

   ROBUSTNESS: ptr_mem_ok supplies val_in_memory for every memory agreeing
   outside tn.t_mem, and covers only val_store_size when footprint is nonzero.
   source_rep_transport applied pointwise gives !mem. agree ==> ?rv. ... .
   It does NOT directly give one rv with !mem. agree ==> open_input ... rv.
   A fixed representative / open-input live-window transport theorem is still
   needed; full-capacity source bounds cannot be inferred from ptr_mem_ok.
   The checked child projection above preserves the arbitrary-memory quantifier
   but assumes ordinary input; it is not a producer of recursive open input.

   COUNTED ENCODING: abiEncoderSourceInvoke.abi_encoder_source_shared_run
   consumes the plan, evaluate_type, value typing/conversion, evaluated source
   and destination operands, enc_pre, fn_has_code, unhalted state and exact
   entry block/index.  enc_pre entails full source end below scratch lo and
   destination-output end below lo.  Its shared endpoint is not gas_outcome_ptr.
   A pointer consumer must instead carry live readable/clean source windows,
   disjoint allocated destination capacity and scratch, arithmetic no-wrap,
   protected operands, and return a counted normal path with untainted length,
   clean encoded extent, source robustness and outside-write memory agreement.
   Compiler recursion (abiEncoder lines 281-379) allocates parent offset cells,
   array index and offset cells, recurses on dynamic children and updates heads.
   AbiComplex includes zero-span children; static-element loops alone do not
   cover this recursion.  No such general counted bridge is proved here.

   NORMALIZATION: typedCopyPtr.typed_return_normalization_layout consumes
   expr_sim_inv, typed Return, annotation != declared type, evaluated annotation
   and value typing.  It gives declared typing and footprint/default facts,
   NOT the actual lowered source layout.  return_lowered_runtime_layout in
   extRetNormalizeInputsPtr additionally requires supported_expr tops e (not
   available for arbitrary frame eo); return_equal_lowered_robust requires
   lowered_value_type = expr_type (false in the narrow-call probe).  Needed is
   runtime source layout and robust source representation at lowered_value_type
   for arbitrary eo, followed by a counted fresh normalization copy producing
   ptr_val_ok at the declared type, preserving protected operands and memory
   outside the new buffer.  The compiler-tail equation checked above proves
   only emission, not this execution/representation implication.
*)
