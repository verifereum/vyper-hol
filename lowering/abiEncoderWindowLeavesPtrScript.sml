(* Robust ABI windows expose clean read bytes, not clean unused capacity. *)
Theory abiEncoderWindowLeavesPtr
Ancestors abiEncoderRobustWindowPtr abiEncoderBytesPtr representationCleanPtr
  abiEncoderWindowLeaves abiEncoderWindowContract abiEncoderWindow
  abiEncoderInput bodyPtrDefs valueEncoding contractABI list arithmetic

Theorem abi_encoder_robust_word_read_clean:
  (!m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input AbiPrimWord at av p cap m) ==>
  !a. p <= a /\ a < p+32 ==> a NOTIN ta
Proof
  rpt gen_tac >> disch_tac >>
  `!m. mem_agree_outside ta mem m ==> mem_bytes_at p 32 m = enc at av` by
    metis_tac[abi_encoder_window_word_iff] >>
  drule robust_mem_bytes_at_clean >> simp[]
QED

Theorem abi_encoder_robust_copy_read_clean:
  (!m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input (AbiCopy n) at av p cap m) ==>
  !a. p <= a /\ a < p+n ==> a NOTIN ta
Proof
  rpt gen_tac >> disch_tac >>
  `!m. mem_agree_outside ta mem m ==> mem_bytes_at p n m = enc at av` by
    metis_tac[abi_encoder_window_copy_iff] >>
  drule robust_mem_bytes_at_clean >> simp[]
QED

Theorem abi_encoder_robust_bytes_read_clean:
  (!m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input (AbiBytestring maxlen) at av p cap m) ==>
  ?bs. av = BytesV bs /\
    (!m. mem_agree_outside ta mem m ==>
      mem_word_at p m = n2w (LENGTH bs) /\
      mem_bytes_at (p+32) (LENGTH bs) m = bs) /\
    (!a. p <= a /\ a < p+32+LENGTH bs ==> a NOTIN ta)
Proof
  rpt gen_tac >> disch_tac >>
  `mem_agree_outside ta mem mem` by simp[mem_agree_outside_def] >>
  first_assum drule >> rewrite_tac[abi_encoder_window_bytes_iff] >> strip_tac >>
  qexists_tac `bs` >> gvs[] >> (
  `!m. mem_agree_outside ta mem m ==>
    mem_word_at p m = n2w (LENGTH bs) /\
    mem_bytes_at (p+32) (LENGTH bs) m = bs` by
      (rpt strip_tac >> first_x_assum drule >>
       simp[abi_encoder_window_bytes_iff]) >>
  conj_tac >- asm_rewrite_tac[] >>
  `!m. mem_agree_outside ta mem m ==>
    mem_word_at p m = n2w (LENGTH bs)` by metis_tac[] >>
  drule robust_mem_word_at_clean >> disch_tac >>
  `!m. mem_agree_outside ta mem m ==>
    mem_bytes_at (p+32) (LENGTH bs) m = bs` by metis_tac[] >>
  drule robust_mem_bytes_at_clean >> disch_tac >>
  rpt strip_tac >>
  Cases_on `a < p+32`
  >- (qpat_x_assum `!i. p <= i /\ i < p+32 ==> _`
        (qspec_then `a` mp_tac) >> simp[]) >>
  qpat_x_assum `!i. p+32 <= i /\ _ ==> _` (qspec_then `a` mp_tac) >>
  simp[])
QED

(* A zero-byte copy still evaluates its address operands. *)
Theorem mcopy_taint_ok_operands_clean:
  taint_ok fn tn (mk_inst id MCOPY [dst;src;len] []) s ==>
  op_taint tn dst = {} /\ op_taint tn src = {} /\ op_taint tn len = {}
Proof
  simp[ptrDisciplineTheory.taint_ok_def, venomInstTheory.mk_inst_def] >>
  metis_tac[]
QED

Theorem zero_copy_tainted_source_rejected[local]:
  !fn s.
    ~taint_ok fn
      (entry_taint with t_var := FEMPTY |+ ("src",{0}))
      (mk_inst 0 MCOPY [Var "dst";Var "src";Lit 0w] []) s
Proof
  rpt gen_tac >> strip_tac >>
  drule mcopy_taint_ok_operands_clean >>
  simp[ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  EVAL_TAC
QED
