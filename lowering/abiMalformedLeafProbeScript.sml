(* Caller-owned head bounds for primitive reflection on arbitrary bytes. *)
Theory abiMalformedLeafProbe
Ancestors
  abiBoundedLeafReflection abiBoundedBytesExecution abiCanonicalHeadSize
  abiDecoderDynarrayBound abiDecoderLayoutBounds abiDecoderWordTyped
  abiDecoderCoherence abiDecoderBytesBound abiDecoderRange abiDecoderGuard abiDecoderGuards abiEncoder emitHelper
  emitHelperProps exprLoweringProps arithmeticProps venomMemProps
  compileEnv venomExecSemantics venomState valueEncodingProps words arithmetic list rich_list

Theorem abi_checked_head_span:
  H < dimword (:256) /\
  w2n (p:bytes32) <= w2n (p + n2w H) /\
  w2n (p + n2w H) <= w2n (hi:bytes32) ==>
  w2n p + H <= w2n hi /\ w2n p + H < dimword (:256)
Proof
  strip_tac >>
  `w2n p + H < dimword (:256)` by
    (spose_not_then assume_tac >>
     mp_tac (Q.SPECL [`p`, `n2w H`] w2n_add_overflow) >>
     simp[w2n_n2w]) >>
  gvs[word_add_def, w2n_n2w]
QED

Theorem abi_checked_child_span:
  p + H <= hi /\ hi < dimword (:256) /\ off + 32 <= H ==>
  p + off + 32 <= hi /\ p + off < dimword (:256)
Proof
  strip_tac >> decide_tac
QED

Theorem abi_checked_array_word_span:
  p + (cnt:num) * 32 <= hi /\ hi < dimword (:256) /\ i < cnt ==>
  p + i * 32 + 32 <= hi /\ p + i * 32 < dimword (:256)
Proof
  strip_tac >>
  `(i + 1) * 32 <= cnt * 32` by simp[] >>
  gvs[LEFT_ADD_DISTRIB] >> decide_tac
QED

Theorem abi_checked_source_word_window:
  mem_bytes_at B len mem = bs /\ pos + 32 <= len ==>
  mem_bytes_at (B + pos) 32 mem = TAKE 32 (DROP pos bs) /\
  LENGTH (TAKE 32 (DROP pos bs)) = 32
Proof
  strip_tac >>
  drule mem_bytes_at_window >>
  disch_then (qspecl_then [`B`, `mem`] mp_tac) >>
  simp[] >> metis_tac[LENGTH_mem_bytes_at]
QED

(* This is exactly the entry fragment in the bounded DecComplex clause. *)
Theorem abi_aggregate_head_guard_total:
  comp_bind (emit_op ADD [src; sz])
    (\e. compile_abi_decode_range_check src e hi) st = ((),st') /\
  H < dimword (:256) /\ fresh_vars_wrt st s /\
  eval_operand src s = SOME p /\ eval_operand hi s = SOME h /\
  eval_operand sz s = SOME (n2w H) ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (w2n p + H <= w2n h /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\
     fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section)
Proof
  simp[comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st cs') s = OK s1` >>
  `eval_operand src s1 = SOME p /\ eval_operand hi s1 = SOME h` by metis_tac[] >>
  drule_all compile_abi_decode_range_check_total >> strip_tac
  >- (disj1_tac >> drule compile_abi_decode_range_check_shape >> strip_tac >>
      drule_all run_inst_seq_emit_extend >> metis_tac[]) >>
  disj2_tac >>
  `w2n p + H <= w2n h` by metis_tac[abi_checked_head_span] >>
  simp[] >>
  drule compile_abi_decode_range_check_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >> metis_tac[]
QED

Theorem abi_aggregate_primitive_reflected_total:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  abi_decode_source_opcode opc /\
  eval_operand src s = SOME (n2w (p + off)) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  p + H <= len /\ off + 32 <= H /\ B + len < dimword (:256) /\
  mem_bytes_at B len (abi_decode_source opc s) = bs /\
  fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (vyper_decode_valid_enc (vyper_to_abi_type env ty) (TAKE 32 (DROP (p + off) bs)) /\
   abi_vyper_admissible env ty
     (dec (vyper_to_abi_type env ty) (TAKE 32 (DROP (p + off) bs))) /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\
     mem_word_at d t.vs_memory =
       abi_decode_load opc (n2w (B + (p + off)):bytes32) s /\
     abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     inst_extends st st')
Proof
  strip_tac >>
  `p + off + 32 <= len /\ B + (p + off) < dimword (:256)` by decide_tac >>
  `mem_bytes_at (B + (p + off)) 32 (abi_decode_source opc s) =
     TAKE 32 (DROP (p + off) bs)` by
    (irule (cj 1 abi_checked_source_word_window) >> metis_tac[]) >>
  irule abi_decoder_primitive_reflected_total >>
  metis_tac[DECIDE ``32 <= (32:num)``]
QED

Theorem abi_dynarray_payload_checked_total:
  abi_decode_dynarray_payload_guard head cnt stride hi st = ((),st') /\
  hi <> Lit 0w /\ eval_operand head s = SOME p /\
  eval_operand cnt s = SOME (n2w n) /\ eval_operand hi s = SOME h /\
  n * stride < dimword (:256) /\ fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (w2n p + n * stride <= w2n h /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\
     fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section)
Proof
  Cases_on `hi = Lit 0w` >- simp[] >>
  simp[abi_decode_dynarray_payload_guard_def, Once comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w stride)] st = (payload,c1)` >>
  `eval_operand (Lit (n2w stride)) s = SOME (n2w stride)` by simp[eval_operand_def] >>
  drule_all abi_decode_mul_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[word_mul_n2w] >>
  `eval_operand head s1 = SOME p /\ eval_operand hi s1 = SOME h` by metis_tac[] >>
  `inst_extends c1 st'` by
    (gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
     imp_res_tac inst_extends_emit_op >>
     imp_res_tac compile_abi_decode_range_check_shape >>
     metis_tac[inst_extends_trans]) >>
  drule_all abi_aggregate_head_guard_total >> strip_tac
  >- (disj1_tac >> drule_all run_inst_seq_emit_extend >> metis_tac[]) >>
  disj2_tac >> simp[] >>
  drule_all abi_decode_sequence_chain >> strip_tac >> metis_tac[]
QED

(* The real tuple head extent discharges the abstract child-slot premise. *)
Theorem abi_checked_tuple_primitive_span:
  abi_decoder_coherent ce env sf (EL i tys) tv /\
  type_to_abi_dec_info sf ce (EL i tys) = DecPrimWord clamp /\
  i < LENGTH tys /\ p + abi_static_size sf (TupleT tys) <= hi /\
  hi < dimword (:256) ==>
  p + SUM (MAP (abi_embedded_static_size sf) (TAKE i tys)) + 32 <= hi /\
  p + SUM (MAP (abi_embedded_static_size sf) (TAKE i tys)) < dimword (:256)
Proof
  strip_tac >>
  `abi_embedded_static_size sf (EL i tys) = 32` by
    (drule_all abi_decoder_primitive_cases >> strip_tac >>
     gvs[] >> metis_tac[abi_decoder_primitive_base_stride,
                       abi_decoder_primitive_flag_stride]) >>
  drule_all abi_decoder_tuple_primitive_head_bound >> strip_tac >> decide_tac
QED
