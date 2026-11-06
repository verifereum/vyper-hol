(* Semantic unsigned decoding ignores arbitrary bytes after the occupied prefix. *)
Theory bodyPtrTypeBuiltinsUnsignedSemantics
Ancestors bodyPtrTypeBuiltinsUnsignedValue bodyPtrTypeBuiltinsUnsignedLoad
  bodyPtrTypeBuiltinsUnsignedFixed valueEncodingProofs byte words
  valueEncoding rich_list list emitHelperProps venomInstProofs
  fragExec venomState exprLoweringProps venomExecSemantics

val () = augment_srw_ss [rewrites
  [fcpLib.INDEX_CONV ``dimindex(:8)``,
   fcpLib.INDEX_CONV ``dimindex(:256)``]];

Theorem unsigned_get_byte_encoding[local]:
  j < 32 ==>
  byte$get_byte (n2w j:bytes32) (word_of_bytes_be bs:bytes32) T =
    if j < LENGTH bs then EL j bs else 0w
Proof
  strip_tac >>
  simp[byteTheory.word_of_bytes_be_def,
       byteTheory.get_byte_word_of_bytes_be, byteTheory.first_byte_at_0w,
       wordsTheory.dimword_def]
QED

Theorem unsigned_get_byte_bit[local]:
  j < 32 /\ r < 8 ==>
  ((byte$get_byte (n2w j:bytes32) (w:bytes32) T : 8 word) ' r =
   w ' (8 * (31 - j) + r))
Proof
  strip_tac >>
  simp[byteTheory.get_byte_def, byteTheory.byte_index_def,
       wordsTheory.dimword_def,
       wordsTheory.w2w, wordsTheory.word_lsr_def, fcpTheory.FCP_BETA] >>
  AP_TERM_TAC >> decide_tac
QED

Theorem unsigned_word_bit_byte[local]:
  i < 256 ==>
  ((w:bytes32) ' i =
   (byte$get_byte (n2w (31 - i DIV 8):bytes32) w T : 8 word) ' (i MOD 8))
Proof
  strip_tac >>
  qspec_then `8` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  `31 - i DIV 8 < 32 /\ i MOD 8 < 8` by simp[] >>
  drule_all unsigned_get_byte_bit >>
  disch_then (qspec_then `w` mp_tac) >>
  `8 * (31 - (31 - i DIV 8)) + i MOD 8 = i` by intLib.ARITH_TAC >>
  simp[]
QED

Theorem unsigned_payload_prefix_bits[local]:
  n <= 32 /\ LENGTH xs = 32 /\ LENGTH bs = n /\ TAKE n xs = bs ==>
  !i. 8 * (32 - n) <= i /\ i < 256 ==>
    ((word_of_bytes_be xs:bytes32) ' i =
     (word_of_bytes_be bs:bytes32) ' i)
Proof
  rpt strip_tac >>
  qspec_then `8` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  `31 - i DIV 8 < n /\ 31 - i DIV 8 < 32` by intLib.ARITH_TAC >>
  simp[unsigned_word_bit_byte, unsigned_get_byte_encoding] >>
  `EL (31 - i DIV 8) bs = EL (31 - i DIV 8) xs` by
    metis_tac[EL_TAKE] >> simp[]
QED

Theorem unsigned_lsr_high_cong[local]:
  (!i. k <= i /\ i < 256 ==> (u:bytes32) ' i = (v:bytes32) ' i) ==>
  word_lsr u k = word_lsr v k
Proof
  strip_tac >>
  simp[wordsTheory.word_lsr_def, fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  rpt strip_tac >> Cases_on `i + k < 256` >> simp[] >>
  first_x_assum irule >> decide_tac
QED

Theorem unsigned_payload_lsr:
  LENGTH xs = 32 /\ LENGTH bs <= 32 /\ TAKE (LENGTH bs) xs = bs ==>
  word_lsr (word_of_bytes_be xs:bytes32) (8 * (32 - LENGTH bs)) =
  word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
Proof
  strip_tac >> irule unsigned_lsr_high_cong >>
  metis_tac[unsigned_payload_prefix_bits]
QED

Theorem unsigned_memory_payload_prefix[local]:
  LENGTH bs <= 32 /\ mem_bytes_at off (LENGTH bs) mem = bs ==>
  LENGTH (TAKE 32 (DROP off mem ++ REPLICATE 32 0w)) = 32 /\
  TAKE (LENGTH bs) (TAKE 32 (DROP off mem ++ REPLICATE 32 0w)) = bs
Proof
  strip_tac >> conj_tac >- simp[LENGTH_TAKE_EQ] >>
  simp[TAKE_TAKE_MIN, arithmeticTheory.MIN_DEF] >>
  `TAKE (LENGTH bs) (DROP off mem ++ REPLICATE 32 0w) =
   TAKE (LENGTH bs) (DROP off mem ++ REPLICATE (LENGTH bs) 0w)` by
    (irule TAKE_append_REPLICATE >> simp[]) >>
  Cases_on `LENGTH bs < 32` >- gvs[mem_bytes_at_def] >>
  `LENGTH bs = 32` by decide_tac >> gvs[mem_bytes_at_def]
QED

Theorem unsigned_memory_payload_lsr:
  LENGTH bs <= 32 /\ mem_bytes_at off (LENGTH bs) mem = bs ==>
  word_lsr (mem_word_at off mem) (8 * (32 - LENGTH bs)) =
  word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
Proof
  strip_tac >> drule_all unsigned_memory_payload_prefix >> strip_tac >>
  simp[mem_word_at_def, GSYM byteTheory.word_of_bytes_be_def] >>
  irule unsigned_payload_lsr >> simp[]
QED

(* Existing emit_op_*_correct interfaces omit allocation preservation. *)
Theorem scalar_emit_update_exact:
  emit_op opc ops st = (v,st') /\ fresh_vars_wrt st ss /\
  step_inst_base (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) ss =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) z ss) ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    eval_operand v ss' = SOME z /\ fresh_vars_wrt st' ss' /\
    ss'.vs_memory = ss.vs_memory /\ ss'.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p ss' = SOME w)
Proof
  rpt strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, eval_operand_update_var] >>
  drule emit_op_extends >> strip_tac >>
  conj_tac
  >- (irule fresh_vars_wrt_advance >> simp[] >>
      goal_assum (drule_at Any) >> gvs[]) >>
  conj_tac >- simp[update_var_def] >> rpt strip_tac >>
  irule eval_operand_update_fresh >> simp[] >>
  goal_assum (drule_at Any) >> gvs[]
QED

Theorem unsigned_emit_load_exact[local]:
  emit_op MLOAD [a] st = (v,st') /\
  eval_operand a ss = SOME x /\ fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    eval_operand v ss' = SOME (mload (w2n x) ss) /\
    fresh_vars_wrt st' ss' /\ ss'.vs_memory = ss.vs_memory /\
    ss'.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p ss' = SOME w)
Proof
  rpt strip_tac >> irule scalar_emit_update_exact >> simp[] >>
  goal_assum (drule_at (Pat `emit_op`)) >> simp[] >>
  irule step_MLOAD >> simp[]
QED

Theorem unsigned_emit_binary_exact[local]:
  emit_op opc [a;b] st = (v,st') /\
  eval_operand a ss = SOME x /\ eval_operand b ss = SOME y /\
  fresh_vars_wrt st ss /\
  ((opc = ADD /\ z = x+y) \/ (opc = SUB /\ z = x-y) \/
   (opc = MUL /\ z = x*y) \/ (opc = SHR /\ z = word_lsr y (w2n x))) ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    eval_operand v ss' = SOME z /\ fresh_vars_wrt st' ss' /\
    ss'.vs_memory = ss.vs_memory /\ ss'.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p ss' = SOME w)
Proof
  rpt strip_tac >> gvs[] >> irule scalar_emit_update_exact >> simp[] >>
  goal_assum (drule_at (Pat `emit_op`)) >> simp[] >>
  FIRST [irule step_ADD, irule (SRULE [] step_SUB), irule step_MUL,
         irule step_SHR] >> simp[]
QED

Theorem unsigned_load_payload_exact[local]:
  emit_op MLOAD [v] sa = (len,s1) /\
  emit_op ADD [v;Lit 32w] s1 = (dp,s2) /\
  emit_op MLOAD [dp] s2 = (data,sb) /\
  eval_operand v ss = SOME addrword /\ fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand len sf = SOME (mload (w2n addrword) ss) /\
    eval_operand data sf = SOME (mload (w2n (addrword+32w)) ss) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  rpt strip_tac >>
  drule_all unsigned_emit_load_exact >>
  disch_then (qx_choose_then `t1` strip_assume_tac) >>
  `eval_operand v t1 = SOME addrword` by metis_tac[] >>
  `?t2. run_inst_seq (emitted_insts s1 s2) t1 = OK t2 /\
    eval_operand dp t2 = SOME (addrword+32w) /\ fresh_vars_wrt s2 t2 /\
    t2.vs_memory = t1.vs_memory /\ t2.vs_allocas = t1.vs_allocas /\
    (!p w. eval_operand p t1 = SOME w ==> eval_operand p t2 = SOME w)` by
    (irule unsigned_emit_binary_exact >> simp[eval_operand_lit] >>
     goal_assum (drule_at (Pat `emit_op`)) >> simp[eval_operand_lit]) >>
  `eval_operand dp t2 = SOME (addrword+32w)` by simp[] >>
  qpat_assum `emit_op MLOAD [dp] _ = _`
    (mp_then Any mp_tac unsigned_emit_load_exact) >>
  disch_then (qspecl_then [`addrword+32w`,`t2`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `t3` strip_assume_tac) >>
  `inst_extends sa s1 /\ inst_extends s1 s2 /\ inst_extends s2 sb` by
    metis_tac[inst_extends_emit_op] >>
  `run_inst_seq (emitted_insts sa s2) ss = OK t2` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`t1`,`s1`] >> simp[]) >>
  `inst_extends sa s2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa sb) ss = OK t3` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`t2`,`s2`] >> simp[]) >>
  qexists_tac `t3` >> simp[mload_def] >> metis_tac[]
QED

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
    (irule unsigned_emit_binary_exact >> simp[] >>
     goal_assum (drule_at (Pat `emit_op`)) >> simp[eval_operand_lit]) >>
  `?t2. run_inst_seq (emitted_insts s1 s2) t1 = OK t2 /\
    eval_operand k t2 = SOME ((32w-n)*8w) /\ fresh_vars_wrt s2 t2 /\
    t2.vs_memory = t1.vs_memory /\ t2.vs_allocas = t1.vs_allocas /\
    (!p w. eval_operand p t1 = SOME w ==> eval_operand p t2 = SOME w)` by
    (irule unsigned_emit_binary_exact >> simp[] >>
     goal_assum (drule_at (Pat `emit_op`)) >> simp[eval_operand_lit]) >>
  `eval_operand data t2 = SOME d` by metis_tac[] >>
  qpat_assum `emit_op SHR _ _ = _`
    (mp_then Any mp_tac unsigned_emit_binary_exact) >>
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
  drule_all unsigned_load_payload_exact >>
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
  irule unsigned_memory_payload_lsr >> simp[]
QED

Theorem unsigned_payload_padding:
  LENGTH bs <= 32 ==>
  word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs)) =
    word_of_bytes_be (PAD_LEFT 0w 32 bs)
Proof
  strip_tac >>
  simp[wordsTheory.word_lsr_def, fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  rpt strip_tac >>
  qspec_then `8` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  Cases_on `i+8*(32-LENGTH bs) < 256`
  >- (simp[unsigned_word_bit_byte, unsigned_get_byte_encoding,
           PAD_LEFT, rich_listTheory.EL_APPEND, EL_GENLIST] >>
      intLib.ARITH_TAC) >>
  simp[unsigned_word_bit_byte, unsigned_get_byte_encoding,
       PAD_LEFT, rich_listTheory.EL_APPEND, EL_GENLIST] >>
  `31 < i DIV 8+32-LENGTH bs` by intLib.ARITH_TAC >>
  simp[wordsTheory.word_0, fcpTheory.FCP_BETA]
QED

Theorem unsigned_payload_bound:
  LENGTH bs <= 32 ==>
  w2n (word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs))) <
    2 ** (8*LENGTH bs)
Proof
  strip_tac >> simp[wordsTheory.w2n_lsr] >>
  `256 = 8*LENGTH bs+8*(32-LENGTH bs)` by decide_tac >>
  mp_tac (Q.ISPEC `(word_of_bytes_be bs:bytes32)` wordsTheory.w2n_lt) >>
  simp[wordsTheory.dimword_def, arithmeticTheory.EXP_ADD,
       arithmeticTheory.DIV_LT_X]
QED
