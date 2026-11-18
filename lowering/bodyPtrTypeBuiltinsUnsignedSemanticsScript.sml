(* Semantic unsigned decoding ignores arbitrary bytes after the occupied prefix. *)
Theory bodyPtrTypeBuiltinsUnsignedSemantics
Ancestors
  exprSimConvertFromBytes[qualified,ignore_grammar]
  bodyPtrSignedConvertUnsignedValue bodyPtrSignedConvertUnsignedLoad
  bodyPtrSignedConvertUnsignedFixed valueEncodingProofs byte words
  valueEncoding valueEncodingDefs rich_list list emitHelperProps venomInstProofs
  fragExec venomState exprLoweringProps venomExecSemantics

val () = augment_srw_ss [rewrites
  [fcpLib.INDEX_CONV ``dimindex(:8)``,
   fcpLib.INDEX_CONV ``dimindex(:256)``]];









(* Existing emit_op_*_correct interfaces omit allocation preservation. *)




Theorem unsigned_shift_payload_exact[local]:
  emit_op SUB [Lit 32w;len] sa = (sub,s1) /\
  emit_op MUL [sub;Lit 8w] s1 = (k,s2) /\
  emit_op SHR [k;data] s2 = (r,sb) /\
  eval_operand len ss = SOME n /\ eval_operand data ss = SOME d /\
  fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand k sf = SOME ((32w-n)*8w) /\
    eval_operand r sf = SOME (word_lsr d (w2n ((32w-n)*8w))) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  rpt gen_tac >> strip_tac >>
  `?t1. run_inst_seq (emitted_insts sa s1) ss = OK t1 /\
    eval_operand sub t1 = SOME (32w-n) /\ fresh_vars_wrt s1 t1 /\
    t1.vs_memory = ss.vs_memory /\ t1.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p t1 = SOME w)` by
    (irule exprSimConvertFromBytesTheory.dynamic_emit_binary_exact >> simp[] >>
     goal_assum (drule_at (Pat `emit_op`)) >> simp[eval_operand_lit]) >>
  `?t2. run_inst_seq (emitted_insts s1 s2) t1 = OK t2 /\
    eval_operand k t2 = SOME ((32w-n)*8w) /\ fresh_vars_wrt s2 t2 /\
    t2.vs_memory = t1.vs_memory /\ t2.vs_allocas = t1.vs_allocas /\
    (!p w. eval_operand p t1 = SOME w ==> eval_operand p t2 = SOME w)` by
    (irule exprSimConvertFromBytesTheory.dynamic_emit_binary_exact >> simp[] >>
     goal_assum (drule_at (Pat `emit_op`)) >> simp[eval_operand_lit]) >>
  `eval_operand data t2 = SOME d` by metis_tac[] >>
  qpat_assum `emit_op SHR _ _ = _`
    (mp_then Any mp_tac exprSimConvertFromBytesTheory.dynamic_emit_binary_exact) >>
  disch_then (qspecl_then [`word_lsr d (w2n ((32w-n)*8w))`,
                         `d`,`(32w-n)*8w`,`t2`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `t3` strip_assume_tac) >>
  `inst_extends sa s1 /\ inst_extends s1 s2 /\ inst_extends s2 sb` by
    metis_tac[inst_extends_emit_op] >>
  `run_inst_seq (emitted_insts sa s2) ss = OK t2` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`t1`,`s1`] >> simp[]) >>
  `inst_extends sa s2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa sb) ss = OK t3` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`t2`,`s2`] >> simp[]) >>
  qexists_tac `t3` >> simp[] >> metis_tac[]
QED

Theorem unsigned_load_word_raw_exact:
  load_bytestring_as_word v SHR sa = ((r,k),sb) /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand k sf = SOME ((32w-mload (w2n a) ss)*8w) /\
    eval_operand r sf = SOME
      (word_lsr (mload (w2n (a+32w)) ss) (w2n ((32w-mload (w2n a) ss)*8w))) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  strip_tac >> drule unsigned_loader_decompose >> strip_tac >>
  drule_all exprSimConvertFromBytesTheory.dynamic_load_payload_exact >>
  disch_then (qx_choose_then `sm` strip_assume_tac) >>
  drule_all unsigned_shift_payload_exact >>
  disch_then (qx_choose_then `sf` strip_assume_tac) >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends sa s3 /\ inst_extends s3 sb` by
    metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa sb) ss = OK sf` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`sm`,`s3`] >> simp[]) >>
  qexists_tac `sf` >> simp[] >> metis_tac[]
QED

Theorem unsigned_load_word_decoded_exact:
  load_bytestring_as_word v SHR sa = ((r,k),sb) /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= 32 /\ w2n (a+32w) = w2n a+32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a+32) (LENGTH bs) ss.vs_memory = bs ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand k sf = SOME (n2w (8*(32-LENGTH bs))) /\
    eval_operand r sf = SOME
      (word_lsr (word_of_bytes_be bs) (8*(32-LENGTH bs))) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  strip_tac >> drule_all unsigned_load_word_raw_exact >> strip_tac >>
  `mload (w2n a) ss = n2w (LENGTH bs)` by
    gvs[mload_def, mem_word_at_def] >>
  drule unsigned_shift_count_word >> strip_tac >>
  qexists_tac `sf` >> simp[] >>
  gvs[mload_def, GSYM mem_word_at_def] >>
  irule exprSimConvertFromBytesTheory.dynamic_memory_payload_lsr >> simp[]
QED





Theorem unsigned_payload_left_align:
  LENGTH bs <= 32 ==>
  word_lsl (word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs)))
    (8*(32-LENGTH bs)) = word_of_bytes_be bs
Proof
  strip_tac >>
  `!i. i < 8*(32-LENGTH bs) ==> ~((word_of_bytes_be bs:bytes32) ' i)` by
    (gen_tac >> disch_tac >>
     qspec_then `8` mp_tac arithmeticTheory.DIVISION >> simp[] >>
     disch_then (qspec_then `i` strip_assume_tac) >>
     `i < 256 /\ 31 - i DIV 8 < 32 /\ LENGTH bs <= 31 - i DIV 8` by intLib.ARITH_TAC >>
     simp[exprSimConvertFromBytesTheory.dynamic_word_bit_byte, exprSimConvertFromBytesTheory.dynamic_get_byte_encoding,
          wordsTheory.word_0, fcpTheory.FCP_BETA]) >>
  simp[wordsTheory.word_lsl_def, wordsTheory.word_lsr_def,
       fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  rpt strip_tac >> Cases_on `i < 8*(32-LENGTH bs)` >> simp[]
QED
