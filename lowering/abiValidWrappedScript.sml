Theory abiValidWrapped
Ancestors
  abiValidSingletonArray vyperABI vyperValue contractABI words list abiValidSingletonPrefix
  abiValidDecodedMetadata abiValidStatic abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract abiDecoderReentry compileEnv valueEncoding venomState arithmetic
  abiValidSingletonBytes abiValidSingletonSetup abiDecoderValidBytes abiDecoderBytes
  abiDecoderSingletonSetup abiDecoderReservation abiEncoder emitHelperProps abiDecoderWrapped
  abiDecoderWrappedBytesFragment abiDecoderBytesTyped abiDecoderTypedCompose abiDecoderGuards
  abiDecoderReentrySequence exprLoweringProps emitHelper venomExecSemantics venomInst rich_list

(* ===== Source Value ===== *)

(* A singleton source decode supplies the child conversion without requiring
   the child's suffix to pass another global size-window check. *)

Theorem abi_valid_dynamic_singleton_source:
  is_dynamic (vyper_to_abi_type env ty) /\
  evaluate_abi_decode env (TupleT [ty]) bs = INL (ArrayV (TupleV [v])) ==>
  valid_enc (Tuple [vyper_to_abi_type env ty]) bs /\
  abi_to_vyper env ty
    (dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs)) = SOME v
Proof
  strip_tac >>
  gvs[evaluate_abi_decode_def, decode_abi_value_def, vyper_valid_enc_def,
    vyper_to_abi_type_def, abi_dynamic_singleton_value, abi_to_vyper_def, AllCaseEqs(),
    Excl "valid_enc_def", Excl "dec_def"]
QED

(* ===== Array Input ===== *)

(* Successful wrapped dynamic-array source decoding establishes the logical
   singleton input, including noncanonical offsets and trailing child bytes. *)

Theorem abi_valid_singleton_prefix_pre_from_conversion:
  abi_decoder_coherent ce env sf ty tv /\ is_dynamic (vyper_to_abi_type env ty) /\
  valid_enc (Tuple [vyper_to_abi_type env ty]) bs /\ abi_head_word bs <= LENGTH bs /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs)) = SOME v /\
  LENGTH (enc (vyper_to_abi_type env ty)
    (dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs))) <=
      LENGTH (DROP (abi_head_word bs) bs) /\
  TAKE (LENGTH (enc (vyper_to_abi_type env ty)
    (dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs)))) (DROP (abi_head_word bs) bs) =
    enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs)) /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs) d (type_memory_bytes ce ty) b cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var hi ==>
  abi_valid_singleton_prefix_pre ce env sf ty tv bs
    (dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs)) v
    st src dst opc hi sb d b cap s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `dec (Tuple [vyper_to_abi_type env ty]) bs =
    ListV [dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs)]` by
    (irule abi_dynamic_singleton_value >> asm_simp_tac bool_ss []) >>
  drule_all abi_valid_singleton_dynamic_decode >> strip_tac >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  asm_simp_tac bool_ss [abi_valid_singleton_prefix_pre_def]
QED

Theorem abi_valid_wrapped_array_prefix_pre:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  evaluate_abi_decode env (TupleT [ArrayT ty (Dynamic maxn)]) bs = INL (ArrayV (TupleV [v])) /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var hi ==>
  abi_valid_singleton_prefix_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) bs
    (dec (Array NONE (vyper_to_abi_type env ty)) (DROP (abi_head_word bs) bs)) v
    st src dst opc hi sb d b cap s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `is_dynamic (vyper_to_abi_type env (ArrayT ty (Dynamic maxn)))` by
    simp[vyper_to_abi_type_def] >>
  drule_all abi_valid_dynamic_singleton_source >> strip_tac >>
  `dec (Tuple [Array NONE (vyper_to_abi_type env ty)]) bs =
    ListV [dec (Array NONE (vyper_to_abi_type env ty)) (DROP (abi_head_word bs) bs)]` by
    (irule abi_dynamic_singleton_value >> simp[]) >>
  `valid_enc (Tuple [Array NONE (vyper_to_abi_type env ty)]) bs` by
    fs[vyper_to_abi_type_def, Excl "valid_enc_def"] >>
  drule_all abi_valid_singleton_array_decode >> strip_tac >>
  drule_all abi_valid_static_array_prefix >> strip_tac >>
  `abi_head_word bs <= LENGTH bs` by decide_tac >>
  mp_tac (Q.INST [`ty` |-> `ArrayT ty (Dynamic maxn)`, `tv` |-> `ArrayTV tv (Dynamic maxn)`]
    abi_valid_singleton_prefix_pre_from_conversion) >>
  asm_simp_tac bool_ss [vyper_to_abi_type_def, is_dynamic_def]
QED

(* ===== Bytes Input ===== *)

(* Valid wrapped Bytes/String input establishes the real singleton child input. *)

Definition abi_valid_wrapped_bytes_pre_def:
  abi_valid_wrapped_bytes_pre n at bs payload st src dst hi sb d s <=>
    (at = Bytes NONE \/ at = String) /\ valid_enc (Tuple [at]) bs /\
    dec (Tuple [at]) bs = ListV [contractABI$BytesV payload] /\ LENGTH payload <= n /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
    n < dimword (:256) /\ sb + LENGTH bs < dimword (:256) /\
    d + abi_decode_bytes_copy_size n < dimword (:256) /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    fresh_vars_wrt st s /\
    (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
       sb + LENGTH bs <= h /\ h < dimword (:256))
End

Theorem abi_valid_wrapped_bytes_setup_pre:
  abi_valid_wrapped_bytes_pre n at bs payload st src dst hi sb d s ==>
  abi_valid_singleton_setup_pre st src dst MLOAD hi sb d (abi_head_word bs) s
Proof
  simp_tac bool_ss [abi_valid_wrapped_bytes_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_valid_singleton_bytes_decode >> strip_tac >>
  drule_all abi_valid_singleton_bytes_load >> strip_tac >>
  asm_simp_tac bool_ss [abi_valid_singleton_setup_pre_def,
    abi_decode_source_opcode_def] >>
  Cases_on `hi = Lit 0w` >> simp[] >>
  qpat_x_assum `_ \/ _` mp_tac >> simp[] >> strip_tac >>
  qexists_tac `h` >> simp[] >> decide_tac
QED

Theorem abi_valid_wrapped_bytes_child_pre:
  abi_valid_wrapped_bytes_pre n at bs payload st src dst hi sb d s /\
  eval_operand child_src t = SOME (n2w (sb + abi_head_word bs)) /\
  eval_operand child_dst t = SOME (n2w d) /\ fresh_vars_wrt st' t /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
  t.vs_memory = s.vs_memory ==>
  abi_decoder_valid_bytes_pre n at (DROP (abi_head_word bs) bs) payload
    st' child_src child_dst MLOAD hi (sb + abi_head_word bs) d t
Proof
  strip_tac >> qpat_x_assum `abi_valid_wrapped_bytes_pre _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_wrapped_bytes_pre_def]) >>
  drule_all abi_valid_singleton_bytes_decode >> strip_tac >>
  drule_all abi_valid_singleton_bytes_load >> strip_tac >>
  `sb + abi_head_word bs + LENGTH (DROP (abi_head_word bs) bs) < dimword (:256)` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  `mem_bytes_at (sb + abi_head_word bs) (LENGTH (DROP (abi_head_word bs) bs))
    (abi_decode_source MLOAD t) = DROP (abi_head_word bs) bs` by
    fs[abi_decode_source_def, Excl "dec_def", Excl "valid_enc_def"] >>
  asm_simp_tac bool_ss [abi_decoder_valid_bytes_pre_def, abi_decode_source_opcode_def] >>
  Cases_on `hi = Lit 0w` >> simp[] >>
  qpat_x_assum `_ \/ _` mp_tac >> simp[] >> strip_tac >>
  qexists_tac `h` >> simp[LENGTH_DROP] >> decide_tac
QED

Theorem abi_valid_wrapped_bytes_setup:
  abi_decode_singleton_setup dst src MLOAD hi st = ((child_src,child_dst),st') /\
  abi_valid_wrapped_bytes_pre n at bs payload st src dst hi sb d s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_valid_bytes_pre n at (DROP (abi_head_word bs) bs) payload
      st' child_src child_dst MLOAD hi (sb + abi_head_word bs) d t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    inst_extends st st'
Proof
  strip_tac >> drule abi_valid_wrapped_bytes_setup_pre >> strip_tac >>
  drule_all abi_valid_singleton_setup_sequence >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')` by fs[listTheory.EVERY_CONJ] >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all abi_valid_wrapped_bytes_child_pre >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED

(* ===== Bytes ===== *)

(* Execute the actual dynamic singleton constructor from valid ABI bytes. *)

Theorem abi_valid_wrapped_bytes_sequence:
  compile_abi_decode_to_buf dst src MLOAD hi
    (DecComplex T [(DecBytestring n,32,mem_sz)]) st = ((),st') /\
  abi_valid_wrapped_bytes_pre n at bs payload st src dst hi sb d s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d t.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d t.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    fresh_vars_wrt st' t /\ t.vs_halted = s.vs_halted /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_wrapped_bytes_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_singleton_setup dst src MLOAD hi st = (child_ops,c1)` >>
  PairCases_on `child_ops` >> gvs[] >>
  rename1 `abi_decode_singleton_setup dst src MLOAD hi st = ((child_src,child_dst),c1)` >>
  `compile_abi_decode_to_buf child_dst child_src MLOAD hi (DecBytestring n) c1 =
    ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  drule_all abi_valid_wrapped_bytes_setup >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK mid` >>
  drule_all abi_decoder_valid_bytes_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') mid = OK t` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends c1 st'` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decoder_sequence_halted >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  gvs[abi_decode_frame_def, Excl "dec_def", Excl "valid_enc_def"] >> first_assum ACCEPT_TAC
QED

(* ===== Bytes Source ===== *)

(* Source conversion for valid, possibly noncanonical singleton Bytes/String. *)

Theorem abi_valid_wrapped_bytes_source_decode:
  evaluate_abi_decode env (TupleT [BaseT (BytesT (Dynamic n))]) bs =
    INL (ArrayV (TupleV [v])) ==>
  ?payload. v = vyperValue$BytesV payload /\ valid_enc (Tuple [Bytes NONE]) bs /\
    dec (Tuple [Bytes NONE]) bs = ListV [contractABI$BytesV payload] /\ LENGTH payload <= n
Proof
  simp[evaluate_abi_decode_def, decode_abi_value_def, vyper_valid_enc_def,
    vyper_strict_enc_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
    abi_to_vyper_def, compatible_bound_def, AllCaseEqs()]
QED

Theorem abi_valid_wrapped_string_source_decode:
  evaluate_abi_decode env (TupleT [BaseT (StringT n)]) bs =
    INL (ArrayV (TupleV [v])) ==>
  ?payload. v = StringV (MAP (CHR o w2n) payload) /\ valid_enc (Tuple [String]) bs /\
    dec (Tuple [String]) bs = ListV [contractABI$BytesV payload] /\ LENGTH payload <= n
Proof
  simp[evaluate_abi_decode_def, decode_abi_value_def, vyper_valid_enc_def,
    vyper_strict_enc_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
    abi_to_vyper_def, AllCaseEqs()]
QED
