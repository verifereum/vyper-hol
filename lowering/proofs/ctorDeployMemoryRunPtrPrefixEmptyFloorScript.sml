(* Empty dynamic descriptors use no payload bytes when the high bound is zero. *)
Theory ctorDeployMemoryRunPtrPrefixEmptyFloor
Ancestors
  abiDecoderEmpty abiDecoderComplexHead abiDecoderContract abiDecoderCoherence
  abiDecoderTypedContract abiEncoderRegisteredEffect abiDecoderReentry abiDecoderLoop
  ctorDeployMemoryRunPtrPrefixAllocationFloor ctorDeployMemoryRunPtrPrefixCanonical
  ptrDiscipline ptrSafeRun allocaFrontierBound ctorAbiActualRecursive
  venomState compileEnv fragExec pred_set

Theorem prefix_empty_inline_code:
  compile_abi_decode_to_buf dst src opc (Lit 0w) (Lit 0w) (DecComplex dynamic []) middle =
    ((),end_st) ==>
  end_st = middle
Proof
  simp[abi_decode_empty_complex_phases, abi_decode_complex_head_guard_def,
       comp_return_def]
QED

Theorem prefix_empty_inline_paired_floor:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) (Lit 0w) (DecComplex T []) middle =
    ((),end_st) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  allocas_from lo initial /\ lo <= initial.vs_alloca_next /\
  ~initial.vs_halted /\ initial.vs_current_bb = middle.cs_current_bb /\
  initial.vs_inst_idx = LENGTH middle.cs_current_insts /\
  fresh_vars_wrt limit_st initial ==>
  end_st = middle /\ type_memory_bytes ce ty = 0 /\
  ?actual H qt B.
    actual = initial /\ H = G /\ qt = tn /\ B = {} /\
    allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
    val_in_memory tv v d actual.vs_memory /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle end_st))
      [(d,type_memory_bytes ce ty)] initial actual /\
    alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
    ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
    actual.vs_data_section = initial.vs_data_section /\
    actual.vs_call_ctx = initial.vs_call_ctx /\
    (!x w. not_fresh_at middle x /\ lookup_var x initial = SOME w ==>
      lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
    actual.vs_labels = initial.vs_labels /\
    FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
    DISJOINT B qt.t_mem /\
    (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
      val_in_memory tv v d mem) /\
    qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)
Proof
  strip_tac >> drule prefix_empty_inline_code >> strip_tac >>
  drule_all abi_decoder_empty_metadata_value >> strip_tac >>
  asm_rewrite_tac[] >> qexistsl [`initial`,`G`,`tn`,`{}`] >>
  simp[abi_encoder_registered_effect_refl, abi_decode_sim_refl]
QED
