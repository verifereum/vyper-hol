(* Typed bytestring sources execute using their actual recursive read window. *)
Theory abiEncoderWindowSourceRun
Ancestors
  abiEncoderWindowRun abiEncoderWindowSource abiEncoderWindowContract
  abiEncoderWindow abiEncoderAdmissible abiEncoderRegisteredEffect
  abiEncoderExtendSim abiEncoderProps abiDecoderLoop exprLoweringProps
  fragExec compileEnv venomState venomInst venomExecSemantics venomMemDefs
  venomWf vyperABI vyperValue valueEncoding words list finite_map pred_set

Theorem abi_encoder_window_bytestring_source:
  ((ty = BaseT (BytesT (Dynamic n)) /\ at = Bytes NONE) \/
   (ty = BaseT (StringT n) /\ at = String)) /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME (BytesV bs) /\
  val_in_memory tv v sb mem ==>
  abi_encoder_window_input
    (if wrapped then AbiComplex [(AbiBytestring n,32,type_memory_size tv,T)]
     else AbiBytestring n)
    (if wrapped then Tuple [at] else at)
    (if wrapped then ListV [BytesV bs] else BytesV bs)
    sb (32 + LENGTH bs) mem
Proof
  strip_tac >> Cases_on `wrapped` >> asm_simp_tac bool_ss [] >>
  metis_tac[abi_encoder_window_bytes_source,
            abi_encoder_window_string_source,
            abi_encoder_window_bytes_singleton_source,
            abi_encoder_window_string_singleton_source]
QED

Theorem abi_encoder_window_bytestring_source_run:
  !dst src ei st out st' ctx func initial env ty tv v n at wrapped
   abi_at av bs sb d.
    ((ty = BaseT (BytesT (Dynamic n)) /\ at = Bytes NONE) \/
     (ty = BaseT (StringT n) /\ at = String)) /\
    evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME (BytesV bs) /\
    val_in_memory tv v sb initial.vs_memory /\
    ei = (if wrapped then
            AbiComplex [(AbiBytestring n,32,type_memory_size tv,T)]
          else AbiBytestring n) /\
    abi_at = (if wrapped then Tuple [at] else at) /\
    av = (if wrapped then ListV [BytesV bs] else BytesV bs) /\
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    eval_operand src initial = SOME (n2w sb) /\
    eval_operand dst initial = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv initial /\ alloca_room ctx func initial /\
    sb + (32 + LENGTH bs) <= initial.vs_alloca_next /\
    d + LENGTH (enc abi_at av) <= initial.vs_alloca_next /\
    venomMemDefs$regions_disjoint
      (sb,32 + LENGTH bs) (d,LENGTH (enc abi_at av)) /\
    (!inst b sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\
      venomMemDefs$regions_disjoint (sb,32 + LENGTH bs) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc abi_at av)) (b,sz)) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual. abi_encoder_window_result ctx func st st' out abi_at av d
      initial actual
Proof
  rpt gen_tac >> strip_tac >>
  `abi_encoder_window_input ei abi_at av sb (32 + LENGTH bs)
      initial.vs_memory` by
    (asm_rewrite_tac[] >> irule abi_encoder_window_bytestring_source >>
     metis_tac[]) >>
  drule_all compile_abi_encode_to_buf_window_run >> strip_tac >>
  qexists_tac `actual` >> simp[abi_encoder_window_result_def]
QED
