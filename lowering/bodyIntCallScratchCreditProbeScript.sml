(* Bounded resource-interface probes, NOT counterexamples to the call seam.
   BoolT translates to AbiCopy 32, emitting one MCOPY and no ALLOCA.
   The interval budget charges 32; actual-site credit charges zero. *)
Theory bodyIntCallScratchCreditProbe
Ancestors
  abiEncoder abiDecoderAllocation exprLowering exprLoweringProps emitHelper
  compileEnv venomInst venomState finite_map pred_set list words arithmetic

Theorem intcall_word_encoder_translation_probe:
  type_to_abi_enc_info sf ce (BaseT BoolT) = (AbiCopy 32)
Proof
  simp[type_to_abi_enc_info_def, type_memory_bytes_def]
QED

Theorem intcall_word_encoder_credit_shape:
  st.cs_next_id = 0 /\ st.cs_current_insts = [] ==>
  let (out,last) = compile_abi_encode_to_buf dst src (AbiCopy 32) st in
    last.cs_next_id = 1 /\
    MAP (\i. i.inst_id) last.cs_current_insts = [0] /\
    MAP (\i. i.inst_opcode) last.cs_current_insts = [MCOPY] /\
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) last.cs_current_insts)) = 0
Proof
  simp[compile_abi_encode_child_def, compile_abi_encode_static_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_inst_def]
QED

Theorem intcall_word_encoder_interval_ids:
  abi_decoder_ids 0 1 = {0}
Proof
  simp[abi_decoder_ids_def, EXTENSION] >> decide_tac
QED

(* Even an extra charge k leaves the discrepancy when k < 32.
   This is only a resource-subset test: no stmt_state_rel is claimed. *)
Theorem intcall_word_encoder_credit_gap:
  k < 32 ==>
  let s = initial with <|vs_allocas := FEMPTY;
    vs_alloca_next := dimword (:256) - k - 1|> in
    s.vs_alloca_next + 0 + k < dimword (:256) /\
    0 < 32 * CARD (abi_decoder_missing 0 1 s) /\
    dimword (:256) <= s.vs_alloca_next +
      32 * CARD (abi_decoder_missing 0 1 s) /\
    ~(?b cap. abi_decoder_budget 0 1 b cap s)
Proof
  simp[abi_decoder_missing_def, intcall_word_encoder_interval_ids,
       abi_decoder_budget_def, dimword_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> decide_tac
QED

(* A record at the MCOPY id is not constrained by an ALLOCA-only
   size condition, but is constrained by the interval budget. *)
Theorem intcall_word_encoder_nonalloca_record:
  let s = initial with vs_allocas := FEMPTY |+ (0,(0,1)) in
    (!i. MEM i code /\ i.inst_opcode = ALLOCA ==> i.inst_id <> 0) ==>
    (!i base sz. MEM i code /\ i.inst_opcode = ALLOCA /\
      FLOOKUP s.vs_allocas i.inst_id = SOME (base,sz) ==>
      sz = alloca_lit_size i) /\
    ~(?b cap. abi_decoder_budget 0 1 b cap s)
Proof
  simp[abi_decoder_budget_def, intcall_word_encoder_interval_ids,
       FLOOKUP_UPDATE] >> rpt strip_tac >>
  metis_tac[]
QED

(* The remaining caller allocations and reachable-frame charge cannot be
   discarded. For this frontier the exact alloca_room margin is k.
   Thus a caller charge of 32 or more excludes the k<32 witness above.
   No claim about realizability of a whole internal call is made here. *)
Theorem intcall_word_encoder_caller_charge_test:
  k < dimword (:256) ==>
  let s = initial with vs_alloca_next := dimword (:256) - k - 1 in
    (s.vs_alloca_next + pending_alloca_size func s +
      CARD {g | TC (fn_directly_calls ctx) func.fn_name g} *
        unit_alloca_frame ctx < dimword (:256) <=>
     pending_alloca_size func s +
      CARD {g | TC (fn_directly_calls ctx) func.fn_name g} *
        unit_alloca_frame ctx <= k)
Proof
  simp[] >> decide_tac
QED
