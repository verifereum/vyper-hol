(* TOP-LEVEL: create_abi_bytes_state7_frame,
   create_abi_bytes_run_frame, compile_create_abi_bytes_frag_frame.
   The generated dynamic-bytes encoder preserves existing bytes outside its
   destination extent, including the zero word written before MCOPY. *)
Theory createAbiBytesFrameExecution
Ancestors
  createAbiBytesFinalExecution createAbiBytesStepExecution
  createAbiBytesExecution venomMemProps venomExecSemantics venomState
  venomLayout fragExec exprLoweringProps venomInst abiEncoder
  list rich_list words

Theorem create_abi_bytes_write_frame[local]:
  ∀a dst bytes s.
    a < LENGTH s.vs_memory ∧
    (a < dst ∨ dst + LENGTH bytes ≤ a) ⇒
    EL a (write_memory_with_expansion dst bytes s).vs_memory =
    EL a s.vs_memory
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`a`,`1`,`dst`,`bytes`,`s`]
    write_memory_with_expansion_disjoint_read) >>
  impl_tac >- decide_tac >>
  strip_tac >>
  `a < LENGTH (write_memory_with_expansion dst bytes s).vs_memory` by
    (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `LENGTH s.vs_memory` >>
     simp[write_memory_with_expansion_nondecreasing]) >>
  fs[LIST_EQ_REWRITE, LENGTH_TAKE_EQ, LENGTH_DROP,
     EL_TAKE, EL_DROP] >>
  `DROP a s.vs_memory <> []` by simp[LENGTH_DROP] >>
  `EL 0 (DROP a s.vs_memory) = EL a s.vs_memory` by
    simp[EL_DROP] >>
  Cases_on `DROP a s.vs_memory` >>
  fs[]
QED

Theorem create_abi_bytes_state7_frame:
  ∀cs bs s (p:bytes32) (d:bytes32) a.
    LENGTH bs + 32 < dimword (:256) ∧
    w2n d + venomLayout$ceil32 (LENGTH bs) < dimword (:256) ∧
    a < LENGTH s.vs_memory ∧
    (a < w2n d ∨
     w2n d + 32 + venomLayout$ceil32 (LENGTH bs) ≤ a) ⇒
    EL a (create_abi_bytes_state7 cs d p (n2w (LENGTH bs)) s).vs_memory =
    EL a s.vs_memory
Proof
  rpt strip_tac >>
  `LENGTH bs ≤ venomLayout$ceil32 (LENGTH bs)` by
    simp[create_abi_bytes_ceil32_gap] >>
  `w2n (32w + (n2w (LENGTH bs):bytes32)) = LENGTH bs + 32` by
    (irule create_abi_bytes_copy_length_nowrap >> simp[]) >>
  `w2n (d + n2w (venomLayout$ceil32 (LENGTH bs))) =
   w2n d + venomLayout$ceil32 (LENGTH bs)` by
    (irule create_abi_bytes_zero_address_nowrap >> simp[]) >>
  `word_and
     0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
     (31w + (n2w (LENGTH bs):bytes32)) =
   n2w (venomLayout$ceil32 (LENGTH bs))` by
    (irule create_abi_bytes_round_mask_first >> simp[]) >>
  `EL a
     (mstore (w2n d + venomLayout$ceil32 (LENGTH bs)) 0w s).vs_memory =
   EL a s.vs_memory` by
    (simp[mstore_eq_write_mem] >>
     irule create_abi_bytes_write_frame >>
     simp[byteTheory.LENGTH_word_to_bytes] >> decide_tac) >>
  `EL a
     (mcopy (w2n d) (w2n p) (LENGTH bs + 32)
       (mstore (w2n d + venomLayout$ceil32 (LENGTH bs)) 0w s)).vs_memory =
   EL a
     (mstore (w2n d + venomLayout$ceil32 (LENGTH bs)) 0w s).vs_memory` by
    (pure_rewrite_tac[mcopy_def, LET_THM] >> BETA_TAC >>
     irule create_abi_bytes_write_frame >>
     simp[LENGTH_mstore_eq, LENGTH_TAKE_EQ, LENGTH_APPEND,
          LENGTH_DROP, LENGTH_REPLICATE] >> decide_tac) >>
  ONCE_REWRITE_TAC [create_abi_bytes_state7_memory] >>
  asm_rewrite_tac[]
QED

Theorem create_abi_bytes_run_frame:
  ∀cs dst src s s' (p:bytes32) (d:bytes32) bound bs.
    fresh_vars_wrt cs s ∧ eval_operand src s = SOME p ∧
    eval_operand dst s = SOME d ∧
    val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bs)
      (w2n p) s.vs_memory ∧
    LENGTH bs + 32 < dimword (:256) ∧
    w2n d + venomLayout$ceil32 (LENGTH bs) < dimword (:256) ∧
    run_inst_seq (create_abi_bytes_append cs dst src []) s = OK s' ⇒
    ∀a. a < LENGTH s.vs_memory ∧
      (a < w2n d ∨
       w2n d + 32 + venomLayout$ceil32 (LENGTH bs) ≤ a) ⇒
      EL a s'.vs_memory = EL a s.vs_memory
Proof
  rpt strip_tac >>
  `mload (w2n p) s = n2w (LENGTH bs)` by
    metis_tac[create_abi_bytes_mload_length] >>
  `s' = create_abi_bytes_state10 cs (n2w (LENGTH bs))
    (create_abi_bytes_state7 cs d p (n2w (LENGTH bs)) s)` by
    (drule_all create_abi_bytes_full_execution >> simp[]) >>
  asm_rewrite_tac[create_abi_bytes_state10_memory] >>
  irule create_abi_bytes_state7_frame >> simp[]
QED

Theorem compile_create_abi_bytes_frag_frame:
  compile_abi_encode_to_buf dst src (AbiBytestring bound) cs = (result,cs') ∧
  LENGTH bs + 32 < dimword (:256) ∧
  w2n d + venomLayout$ceil32 (LENGTH bs) < dimword (:256) ⇒
  result = Var (create_abi_bytes_var cs 7) ∧ cs_extends cs cs' ∧
  frag_exec ctx cs cs'
    (λs. fresh_vars_wrt cs s ∧
         eval_operand src s = SOME p ∧ eval_operand dst s = SOME d ∧
         val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bs)
           (w2n p) s.vs_memory ∧
         w2n p + 32 + LENGTH bs ≤ LENGTH s.vs_memory ∧
         w2n p + 32 + LENGTH bs ≤
           w2n d + venomLayout$ceil32 (LENGTH bs) ∧
         s.vs_memory = old_memory)
    (λs. mem_bytes_at (w2n d) (32 + venomLayout$ceil32 (LENGTH bs))
           s.vs_memory = enc (Bytes NONE) (contractABI$BytesV bs) ∧
         eval_operand result s =
           SOME (n2w (32 + venomLayout$ceil32 (LENGTH bs))) ∧
         ∀a. a < LENGTH old_memory ∧
             (a < w2n d ∨
              w2n d + 32 + venomLayout$ceil32 (LENGTH bs) ≤ a) ⇒
             EL a s.vs_memory = EL a old_memory)
    (K F)
Proof
  strip_tac >>
  drule compile_create_abi_bytes_fragment >> strip_tac >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  irule frag_exec_run_inst_seq >>
  conj_tac
  >- (rpt strip_tac >>
      mp_tac (Q.SPECL
        [`cs`,`dst`,`src`,`s`,`(p:bytes32)`,`(d:bytes32)`,`bound`,`bs`]
        create_abi_bytes_generated_encoding) >>
      impl_tac >- gvs[] >> strip_tac >>
      `∀a. a < LENGTH old_memory ∧
          (a < w2n d ∨
           w2n d + 32 + venomLayout$ceil32 (LENGTH bs) ≤ a) ⇒
          EL a s'.vs_memory = EL a old_memory` by
        (`∀a. a < LENGTH s.vs_memory ∧
             (a < w2n d ∨
              w2n d + 32 + venomLayout$ceil32 (LENGTH bs) ≤ a) ⇒
             EL a s'.vs_memory = EL a s.vs_memory` by
           (mp_tac (Q.SPECL
              [`cs`,`dst`,`src`,`s`,`s'`,`(p:bytes32)`,`(d:bytes32)`,
               `bound`,`bs`] create_abi_bytes_run_frame) >>
            impl_tac >- fs[] >> simp[]) >>
         gvs[] >> metis_tac[]) >>
      disj1_tac >> qexists_tac `s'` >>
      BETA_TAC >> asm_rewrite_tac
        [create_abi_bytes_memory_inst_idx,
         create_abi_bytes_eval_operand_inst_idx]) >>
  fs[same_blocks_def] >>
  conj_tac >- simp[create_abi_bytes_append_def, is_terminator_def] >>
  drule compile_create_abi_bytes_prefix >> simp[]
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createAbiBytesFrameExecution");
