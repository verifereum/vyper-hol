Theory abiEncodeEndpointMetadata
Ancestors
  exprSimAggregateLayout exprSimHyps exprSimHypsDefs exprSimSource abiEncodeListSupplier
  compileEnv valueEncoding valueEncodingProps words arithmetic abiTypeBoundProps allocLimits
  abiEncodeArgsCase exprSimAbiEncodeArgsPhysicalCapacity
  vyperTypeSystem list

(* Endpoint layout facts use the abstract environment invariant, not a
   build_compile_env premise.  ABI plan/head metadata is audited separately. *)
Theorem abi_encode_endpoint_memory_layout:
  expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce ty MOD 32 = 0
Proof
  strip_tac >> drule_all expr_sim_inv_memory_size >> strip_tac >>
  simp[type_memory_size_aligned]
QED

Theorem abi_encode_endpoint_memory_bound:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) ==>
  type_memory_bytes ce (expr_type e) < dimword (:256)
Proof
  strip_tac >> drule_all expr_body_pre_copy_ok >> strip_tac >>
  gvs[wordsTheory.dimword_def] >> decide_tac
QED

(* The size-indexed correspondence already accounts for aliases at recursive
   struct descent; full consistency supplies its initial finite threshold. *)
Theorem abi_encode_evaluated_metadata:
  !E ty tv sf.
    evaluate_type E ty = SOME tv /\
    sfields_tenv_consistent sf E ==>
    is_abi_dynamic sf ty = vyper_is_dynamic E ty /\
    abi_size_bound sf ty = vyper_abi_size_bound E ty /\
    (~vyper_is_dynamic E ty ==>
      abi_static_size sf ty = vyper_abi_size_bound E ty)
Proof
  rpt gen_tac >> strip_tac >>
  drule abi_sfields_consistent_upto_init >>
  disch_then (qspec_then `type_value_size tv` assume_tac) >>
  drule_all abi_props_vyper_upto >> simp[]
QED

Theorem abi_encode_body_arg_types_fit:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es ==>
  arg_types_fit (MAP (lowered_value_type ce) args) (MAP expr_type args)
Proof
  strip_tac >>
  `EVERY (\e. expr_body_pre ce cx env e es) args` by
    (`expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
     simp[EVERY_MEM] >> metis_tac[abi_args_body_pre_arg]) >>
  `EVERY (\e. arg_type_fits (lowered_value_type ce e) (expr_type e)) args` by
    (fs[EVERY_MEM] >> metis_tac[expr_body_pre_lowered_fits]) >>
  qpat_x_assum `expr_body_pre _ _ _ _ _` kall_tac >>
  qpat_x_assum `EVERY (\e. expr_body_pre _ _ _ _ _) _` kall_tac >>
  pop_assum mp_tac >> Induct_on `args` >> simp[arg_type_fits_def]
QED

Theorem abi_encode_endpoint_output_size:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es ==>
  32 + 32 * word_size
    (abi_size_bound ce.ce_struct_fields
      (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
       else TupleT (MAP (lowered_value_type ce) args)) +
     (case mid of NONE => 0 | SOME _ => 4)) < 2 ** 64
Proof
  strip_tac >>
  `32 + 32 * word_size
    (abi_size_bound ce.ce_struct_fields
      (if LENGTH args = 1 /\ ~ensure then expr_type (HD args)
       else TupleT (MAP expr_type args)) +
     (case mid of NONE => 0 | SOME _ => 4)) < 2 ** 64` by
    (irule alloc_limits_abi_encode_output >>
     gvs[expr_body_pre_def] >> metis_tac[]) >>
  drule abi_encode_body_arg_types_fit >> strip_tac >>
  `arg_type_fits
    (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
     else TupleT (MAP (lowered_value_type ce) args))
    (if LENGTH args = 1 /\ ~ensure then expr_type (HD args)
     else TupleT (MAP expr_type args))` by
    (Cases_on `LENGTH args = 1 /\ ~ensure` >> simp[arg_type_fits_def] >>
     Cases_on `args` >> gvs[arg_type_fits_def]) >>
  `abi_size_bound ce.ce_struct_fields
    (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
     else TupleT (MAP (lowered_value_type ce) args)) <=
   abi_size_bound ce.ce_struct_fields
    (if LENGTH args = 1 /\ ~ensure then expr_type (HD args)
     else TupleT (MAP expr_type args))` by
    (irule (cj 1 abi_args_fits_size_bound) >> simp[]) >>
  `word_size
    (abi_size_bound ce.ce_struct_fields
      (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
       else TupleT (MAP (lowered_value_type ce) args)) +
     (case mid of NONE => 0 | SOME _ => 4)) <=
   word_size
    (abi_size_bound ce.ce_struct_fields
      (if LENGTH args = 1 /\ ~ensure then expr_type (HD args)
       else TupleT (MAP expr_type args)) +
     (case mid of NONE => 0 | SOME _ => 4))` by
    (irule word_size_monotone >> decide_tac) >>
  decide_tac
QED

Theorem abi_encode_endpoint_staging_size:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  ~(LENGTH args = 1 /\ ~ensure) ==>
  type_memory_bytes ce (TupleT (MAP (lowered_value_type ce) args)) < 2 ** 64
Proof
  strip_tac >>
  `type_memory_bytes ce (TupleT (MAP expr_type args)) < 2 ** 64` by
    (irule alloc_limits_abi_encode_staging >>
     gvs[expr_body_pre_def] >> metis_tac[]) >>
  drule abi_encode_body_arg_types_fit >> strip_tac >>
  drule (cj 2 abi_args_fits_memory_bytes) >>
  disch_then (qspec_then `ce` mp_tac) >>
  gvs[type_memory_bytes_def, SF ETA_ss] >> decide_tac
QED
