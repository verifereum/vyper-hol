(* TOP-LEVEL: create_abi_bytes_full_execution,
   create_abi_bytes_generated_encoding, compile_create_abi_bytes_frag.
   Execute the generated dynamic-bytes ABI fragment and prove its encoded
   memory and returned byte length. *)
Theory createAbiBytesFinalExecution
Ancestors
  createAbiBytesStepExecution createAbiBytesExecution emitHelperProps
  exprLoweringProps venomExecSemantics venomState valueEncoding contractABI
  fragExec abiEncoder compileEnv venomInst list rich_list words

Theorem create_abi_bytes_eval_operand_mcopy:
  ∀op dst src n s value.
    eval_operand op s = SOME value ⇒
    eval_operand op (mcopy dst src n s) = SOME value
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, mcopy_def,
       write_memory_with_expansion_def]
QED

Theorem create_abi_bytes_state7_length_var:
  ∀cs d p len_word s.
    eval_operand (Var (create_abi_bytes_var cs 0))
      (create_abi_bytes_state7 cs d p len_word s) = SOME len_word
Proof
  rpt gen_tac >>
  `eval_operand (Var (create_abi_bytes_var cs 0))
     (create_abi_bytes_state5 cs d len_word s) = SOME len_word` by
    (simp[create_abi_bytes_state5_def] >>
     irule eval_operand_mstore >>
     simp[create_abi_bytes_state4_length_var]) >>
  `eval_operand (Var (create_abi_bytes_var cs 0))
     (create_abi_bytes_state6 cs d len_word s) = SOME len_word` by
    simp[create_abi_bytes_state6_def, eval_operand_update_other,
         create_abi_bytes_var_distinct] >>
  simp[create_abi_bytes_state7_def] >>
  irule create_abi_bytes_eval_operand_mcopy >> simp[]
QED

Definition create_abi_bytes_state8_def:
  create_abi_bytes_state8 cs len_word s =
    update_var (create_abi_bytes_var cs 5) (31w + len_word) s
End

Definition create_abi_bytes_state9_def:
  create_abi_bytes_state9 cs len_word s =
    update_var (create_abi_bytes_var cs 6)
      (word_and
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
        (31w + len_word))
      (create_abi_bytes_state8 cs len_word s)
End

Definition create_abi_bytes_state10_def:
  create_abi_bytes_state10 cs len_word s =
    update_var (create_abi_bytes_var cs 7)
      (32w + word_and
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
        (31w + len_word))
      (create_abi_bytes_state9 cs len_word s)
End

Theorem create_abi_bytes_last_three_steps:
  ∀cs dst src s len_word.
    eval_operand (Var (create_abi_bytes_var cs 0)) s = SOME len_word ⇒
    run_inst_seq (DROP 7 (create_abi_bytes_append cs dst src [])) s =
      OK (create_abi_bytes_state10 cs len_word s)
Proof
  rpt strip_tac >>
  `step_inst_base
     (mk_inst (cs.cs_next_id + 7) ADD
       [Lit 31w; Var (create_abi_bytes_var cs 0)]
       [create_abi_bytes_var cs 5]) s =
   OK (create_abi_bytes_state8 cs len_word s)` by
    (simp[create_abi_bytes_state8_def] >>
     irule step_ADD >> simp[eval_operand_def]) >>
  `step_inst_base
     (mk_inst (cs.cs_next_id + 8) AND
       [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
        Var (create_abi_bytes_var cs 5)]
       [create_abi_bytes_var cs 6])
     (create_abi_bytes_state8 cs len_word s) =
   OK (create_abi_bytes_state9 cs len_word s)` by
    (simp[create_abi_bytes_state9_def] >>
     irule step_AND >>
     simp[create_abi_bytes_state8_def, eval_operand_update_var] >>
     simp[eval_operand_def]) >>
  `step_inst_base
     (mk_inst (cs.cs_next_id + 9) ADD
       [Lit 32w; Var (create_abi_bytes_var cs 6)]
       [create_abi_bytes_var cs 7])
     (create_abi_bytes_state9 cs len_word s) =
   OK (create_abi_bytes_state10 cs len_word s)` by
    (simp[create_abi_bytes_state10_def] >>
     irule step_ADD >>
     simp[create_abi_bytes_state9_def, eval_operand_update_var] >>
     simp[eval_operand_def]) >>
  simp[create_abi_bytes_append_def, listTheory.DROP_def,
       run_inst_seq_def]
QED

Theorem create_abi_bytes_full_execution:
  ∀cs dst src s p d len_word.
    fresh_vars_wrt cs s ∧ eval_operand src s = SOME p ∧
    eval_operand dst s = SOME d ∧ mload (w2n p) s = len_word ⇒
    run_inst_seq (create_abi_bytes_append cs dst src []) s =
      OK (create_abi_bytes_state10 cs len_word
        (create_abi_bytes_state7 cs d p len_word s))
Proof
  rpt strip_tac >>
  `run_inst_seq (TAKE 7 (create_abi_bytes_append cs dst src [])) s =
   OK (create_abi_bytes_state7 cs d p len_word s)` by
    (mp_tac (Q.SPECL [`cs`,`dst`,`src`,`s`,`p`,`d`,`len_word`]
       create_abi_bytes_first_seven_steps) >> simp[]) >>
  `run_inst_seq (DROP 7 (create_abi_bytes_append cs dst src []))
     (create_abi_bytes_state7 cs d p len_word s) =
   OK (create_abi_bytes_state10 cs len_word
     (create_abi_bytes_state7 cs d p len_word s))` by
    (irule create_abi_bytes_last_three_steps >>
     simp[create_abi_bytes_state7_length_var]) >>
  `run_inst_seq
     (TAKE 7 (create_abi_bytes_append cs dst src []) ++
      DROP 7 (create_abi_bytes_append cs dst src [])) s =
   run_inst_seq (DROP 7 (create_abi_bytes_append cs dst src []))
     (create_abi_bytes_state7 cs d p len_word s)` by
    (irule run_inst_seq_append >> simp[]) >>
  fs[listTheory.TAKE_DROP]
QED

Theorem create_abi_bytes_state10_memory:
  ∀cs len_word s.
    (create_abi_bytes_state10 cs len_word s).vs_memory = s.vs_memory
Proof
  simp[create_abi_bytes_state10_def, create_abi_bytes_state9_def,
       create_abi_bytes_state8_def, update_var_def]
QED

Theorem create_abi_bytes_state10_result:
  ∀cs n s.
    n ≤ dimword (:256) - 32 ⇒
    eval_operand (Var (create_abi_bytes_var cs 7))
      (create_abi_bytes_state10 cs (n2w n) s) =
    SOME (n2w (32 + venomLayout$ceil32 n))
Proof
  rpt strip_tac >>
  `word_and
     0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
     (31w + (n2w n:bytes32)) =
   n2w (venomLayout$ceil32 n)` by
    (irule create_abi_bytes_round_mask_first >> simp[]) >>
  simp[create_abi_bytes_state10_def, eval_operand_update_var,
       wordsTheory.word_add_n2w]
QED

Theorem create_abi_bytes_generated_encoding:
  ∀cs dst src s (p:bytes32) (d:bytes32) bound bs.
    fresh_vars_wrt cs s ∧ eval_operand src s = SOME p ∧
    eval_operand dst s = SOME d ∧
    val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bs)
      (w2n p) s.vs_memory ∧
    w2n p + 32 + LENGTH bs ≤ LENGTH s.vs_memory ∧
    w2n p + 32 + LENGTH bs ≤
      w2n d + venomLayout$ceil32 (LENGTH bs) ∧
    LENGTH bs + 32 < dimword (:256) ∧
    w2n d + venomLayout$ceil32 (LENGTH bs) < dimword (:256) ⇒
    ∃s'.
      run_inst_seq (create_abi_bytes_append cs dst src []) s = OK s' ∧
      mem_bytes_at (w2n d) (32 + venomLayout$ceil32 (LENGTH bs))
        s'.vs_memory = enc (Bytes NONE) (contractABI$BytesV bs) ∧
      eval_operand (Var (create_abi_bytes_var cs 7)) s' =
        SOME (n2w (32 + venomLayout$ceil32 (LENGTH bs)))
Proof
  rpt strip_tac >>
  `mload (w2n p) s = n2w (LENGTH bs)` by
    metis_tac[create_abi_bytes_mload_length] >>
  `LENGTH bs ≤ dimword (:256) - 32` by decide_tac >>
  qexists_tac
    `create_abi_bytes_state10 cs (n2w (LENGTH bs))
       (create_abi_bytes_state7 cs d p (n2w (LENGTH bs)) s)` >>
  conj_tac
  >- (irule create_abi_bytes_full_execution >> simp[]) >>
  conj_tac
  >- (`mem_bytes_at (w2n d) (32 + venomLayout$ceil32 (LENGTH bs))
         (create_abi_bytes_state7 cs d p (n2w (LENGTH bs)) s).vs_memory =
       enc (Bytes NONE) (contractABI$BytesV bs)` by
        (mp_tac (Q.SPECL
          [`cs`,`bound`,`bs`,`s`,`(p:bytes32)`,`(d:bytes32)`]
          create_abi_bytes_state7_encoding) >> simp[]) >>
      ONCE_REWRITE_TAC [create_abi_bytes_state10_memory] >>
      asm_rewrite_tac[]) >>
  simp[create_abi_bytes_state10_result]
QED

Theorem create_abi_bytes_eval_operand_inst_idx:
  ∀op s n.
    eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem create_abi_bytes_memory_inst_idx:
  ∀s n. (s with vs_inst_idx := n).vs_memory = s.vs_memory
Proof
  simp[]
QED

Theorem compile_create_abi_bytes_prefix:
  compile_abi_encode_to_buf dst src (AbiBytestring bound) cs = (result,cs') ⇒
  isPREFIX cs.cs_current_insts cs'.cs_current_insts
Proof
  strip_tac >> gvs[compile_create_abi_bytes_shape] >>
  ONCE_REWRITE_TAC [create_abi_bytes_append_prefix] >>
  simp[IS_PREFIX_APPEND]
QED

Theorem compile_create_abi_bytes_frag:
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
           w2n d + venomLayout$ceil32 (LENGTH bs))
    (λs. mem_bytes_at (w2n d) (32 + venomLayout$ceil32 (LENGTH bs))
           s.vs_memory = enc (Bytes NONE) (contractABI$BytesV bs) ∧
         eval_operand result s =
           SOME (n2w (32 + venomLayout$ceil32 (LENGTH bs))))
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
      impl_tac >- fs[] >> strip_tac >>
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
  (DB.thms "createAbiBytesFinalExecution");
