(* TOP-LEVEL: abi_bytes_first_four_steps.
   Continue the generated dynamic-bytes encoder through its zero-store address
   calculation while retaining live input operands. *)
Theory abiBytesStepExecution
Ancestors
  abiBytesExecution emitHelperProps exprLoweringProps venomExecSemantics
  venomState venomMemProps
  venomInst list words

Definition abi_bytes_state3_def:
  abi_bytes_state3 cs len_word s =
    update_var (abi_bytes_var cs 2)
      (word_and
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
        (31w + len_word))
      (update_var (abi_bytes_var cs 1) (31w + len_word)
        (update_var (abi_bytes_var cs 0) len_word s))
End

Definition abi_bytes_state4_def:
  abi_bytes_state4 cs d len_word s =
    update_var (abi_bytes_var cs 3)
      (d + word_and
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
        (31w + len_word))
      (abi_bytes_state3 cs len_word s)
End

Definition abi_bytes_state5_def:
  abi_bytes_state5 cs d len_word s =
    mstore
      (w2n (d + word_and
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
        (31w + len_word))) 0w
      (abi_bytes_state4 cs d len_word s)
End

Definition abi_bytes_state6_def:
  abi_bytes_state6 cs d len_word s =
    update_var (abi_bytes_var cs 4) (32w + len_word)
      (abi_bytes_state5 cs d len_word s)
End

Definition abi_bytes_state7_def:
  abi_bytes_state7 cs d p len_word s =
    mcopy (w2n d) (w2n p) (w2n (32w + len_word))
      (abi_bytes_state6 cs d len_word s)
End

Theorem abi_bytes_state3_input:
  ∀cs op s value len_word.
    fresh_vars_wrt cs s ∧ eval_operand op s = SOME value ⇒
    eval_operand op (abi_bytes_state3 cs len_word s) = SOME value
Proof
  rpt strip_tac >>
  `∀k name. op = Var name ⇒ name ≠ abi_bytes_var cs k` by
    metis_tac[abi_bytes_input_disjoint] >>
  simp[abi_bytes_state3_def] >>
  irule eval_operand_update_var_mstore >>
  conj_tac >- metis_tac[] >>
  irule eval_operand_update_var_mstore >>
  conj_tac >- metis_tac[] >>
  irule eval_operand_update_var_mstore >> metis_tac[]
QED

Theorem abi_bytes_state4_input:
  ∀cs op s value d len_word.
    fresh_vars_wrt cs s ∧ eval_operand op s = SOME value ⇒
    eval_operand op (abi_bytes_state4 cs d len_word s) = SOME value
Proof
  rpt strip_tac >>
  simp[abi_bytes_state4_def] >>
  irule eval_operand_update_var_mstore >>
  conj_tac >- metis_tac[abi_bytes_input_disjoint] >>
  metis_tac[abi_bytes_state3_input]
QED

Theorem abi_bytes_state4_length_var:
  ∀cs d len_word s.
    eval_operand (Var (abi_bytes_var cs 0))
      (abi_bytes_state4 cs d len_word s) = SOME len_word
Proof
  simp[abi_bytes_state4_def, abi_bytes_state3_def,
       eval_operand_update_other, eval_operand_update_var,
       abi_bytes_var_distinct]
QED

Theorem abi_bytes_state6_input:
  ∀cs op s value d len_word.
    fresh_vars_wrt cs s ∧ eval_operand op s = SOME value ⇒
    eval_operand op (abi_bytes_state6 cs d len_word s) = SOME value
Proof
  rpt strip_tac >>
  simp[abi_bytes_state6_def] >>
  irule eval_operand_update_var_mstore >>
  conj_tac >- metis_tac[abi_bytes_input_disjoint] >>
  simp[abi_bytes_state5_def] >>
  irule eval_operand_mstore >>
  metis_tac[abi_bytes_state4_input]
QED

Theorem abi_bytes_first_four_steps:
  ∀cs dst src s p d len_word.
    fresh_vars_wrt cs s ∧ eval_operand src s = SOME p ∧
    eval_operand dst s = SOME d ∧ mload (w2n p) s = len_word ⇒
    run_inst_seq (TAKE 4 (abi_bytes_append cs dst src [])) s =
      OK (update_var (abi_bytes_var cs 3)
        (d + word_and
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
          (31w + len_word))
        (abi_bytes_state3 cs len_word s))
Proof
  rpt strip_tac >>
  `TAKE 4 (abi_bytes_append cs dst src []) =
   TAKE 3 (abi_bytes_append cs dst src []) ++
     [mk_inst (cs.cs_next_id + 3) ADD
       [dst; Var (abi_bytes_var cs 2)]
       [abi_bytes_var cs 3]]` by
    simp[abi_bytes_append_def, listTheory.TAKE_def] >>
  `eval_operand dst (abi_bytes_state3 cs len_word s) = SOME d` by
    metis_tac[abi_bytes_state3_input] >>
  `step_inst_base
     (mk_inst (cs.cs_next_id + 3) ADD
       [dst; Var (abi_bytes_var cs 2)]
       [abi_bytes_var cs 3])
     (abi_bytes_state3 cs len_word s) =
   OK (update_var (abi_bytes_var cs 3)
     (d + word_and
       0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
       (31w + len_word))
     (abi_bytes_state3 cs len_word s))` by
    (irule step_ADD >>
     simp[abi_bytes_state3_def, eval_operand_update_var]) >>
  drule_all_then (qspec_then `dst` strip_assume_tac)
    abi_bytes_first_three_steps >>
  fs[abi_bytes_state3_def, wordsTheory.WORD_ADD_COMM] >>
  qpat_x_assum `run_inst_seq (TAKE 3 _) s = OK _`
    (fn th => REWRITE_TAC [MATCH_MP run_inst_seq_append th]) >>
  simp[run_inst_seq_def]
QED

Theorem abi_bytes_first_four_address:
  ∀cs dst src s p d n.
    fresh_vars_wrt cs s ∧ eval_operand src s = SOME p ∧
    eval_operand dst s = SOME d ∧
    mload (w2n p) s = n2w n ∧ n ≤ dimword (:256) - 32 ⇒
    ∃s4.
      run_inst_seq (TAKE 4 (abi_bytes_append cs dst src [])) s =
        OK s4 ∧
      eval_operand (Var (abi_bytes_var cs 3)) s4 =
        SOME (d + n2w (venomLayout$ceil32 n))
Proof
  rpt strip_tac >>
  drule_all abi_bytes_first_four_steps >>
  strip_tac >> goal_assum drule >>
  simp[eval_operand_update_var, abi_bytes_round_mask_first]
QED

Theorem abi_bytes_first_five_steps:
  ∀cs dst src s p d len_word.
    fresh_vars_wrt cs s ∧ eval_operand src s = SOME p ∧
    eval_operand dst s = SOME d ∧ mload (w2n p) s = len_word ⇒
    run_inst_seq (TAKE 5 (abi_bytes_append cs dst src [])) s =
      OK (mstore
        (w2n (d + word_and
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
          (31w + len_word))) 0w
        (abi_bytes_state4 cs d len_word s))
Proof
  rpt strip_tac >>
  `TAKE 5 (abi_bytes_append cs dst src []) =
   TAKE 4 (abi_bytes_append cs dst src []) ++
     [mk_inst (cs.cs_next_id + 4) MSTORE
       [Var (abi_bytes_var cs 3); Lit 0w] []]` by
    simp[abi_bytes_append_def, listTheory.TAKE_def] >>
  `step_inst_base
     (mk_inst (cs.cs_next_id + 4) MSTORE
       [Var (abi_bytes_var cs 3); Lit 0w] [])
     (abi_bytes_state4 cs d len_word s) =
   OK (mstore
     (w2n (d + word_and
       0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
       (31w + len_word))) 0w
     (abi_bytes_state4 cs d len_word s))` by
    (irule step_MSTORE >>
     simp[abi_bytes_state4_def, eval_operand_update_var] >>
     simp[eval_operand_def]) >>
  drule_all abi_bytes_first_four_steps >> strip_tac >>
  fs[abi_bytes_state4_def, wordsTheory.WORD_ADD_COMM] >>
  qpat_x_assum `run_inst_seq (TAKE 4 _) s = OK _`
    (fn th => REWRITE_TAC [MATCH_MP run_inst_seq_append th]) >>
  simp[run_inst_seq_def]
QED

Theorem abi_bytes_first_six_steps:
  ∀cs dst src s p d len_word.
    fresh_vars_wrt cs s ∧ eval_operand src s = SOME p ∧
    eval_operand dst s = SOME d ∧ mload (w2n p) s = len_word ⇒
    run_inst_seq (TAKE 6 (abi_bytes_append cs dst src [])) s =
      OK (abi_bytes_state6 cs d len_word s)
Proof
  rpt strip_tac >>
  `TAKE 6 (abi_bytes_append cs dst src []) =
   TAKE 5 (abi_bytes_append cs dst src []) ++
     [mk_inst (cs.cs_next_id + 5) ADD
       [Lit 32w; Var (abi_bytes_var cs 0)]
       [abi_bytes_var cs 4]]` by
    simp[abi_bytes_append_def, listTheory.TAKE_def] >>
  `eval_operand (Var (abi_bytes_var cs 0))
     (abi_bytes_state5 cs d len_word s) = SOME len_word` by
    (simp[abi_bytes_state5_def] >>
     irule eval_operand_mstore >>
     simp[abi_bytes_state4_length_var]) >>
  `step_inst_base
     (mk_inst (cs.cs_next_id + 5) ADD
       [Lit 32w; Var (abi_bytes_var cs 0)]
       [abi_bytes_var cs 4])
     (abi_bytes_state5 cs d len_word s) =
   OK (abi_bytes_state6 cs d len_word s)` by
    (simp[abi_bytes_state6_def] >>
     irule step_ADD >> simp[eval_operand_def]) >>
  drule_all abi_bytes_first_five_steps >> strip_tac >>
  fs[abi_bytes_state5_def] >>
  qpat_x_assum `run_inst_seq (TAKE 5 _) s = OK _`
    (fn th => REWRITE_TAC [MATCH_MP run_inst_seq_append th]) >>
  simp[run_inst_seq_def]
QED

Theorem abi_bytes_first_seven_steps:
  ∀cs dst src s p d len_word.
    fresh_vars_wrt cs s ∧ eval_operand src s = SOME p ∧
    eval_operand dst s = SOME d ∧ mload (w2n p) s = len_word ⇒
    run_inst_seq (TAKE 7 (abi_bytes_append cs dst src [])) s =
      OK (abi_bytes_state7 cs d p len_word s)
Proof
  rpt strip_tac >>
  `TAKE 7 (abi_bytes_append cs dst src []) =
   TAKE 6 (abi_bytes_append cs dst src []) ++
     [mk_inst (cs.cs_next_id + 6) MCOPY
       [dst; src; Var (abi_bytes_var cs 4)] []]` by
    simp[abi_bytes_append_def, listTheory.TAKE_def] >>
  `eval_operand dst (abi_bytes_state6 cs d len_word s) = SOME d ∧
   eval_operand src (abi_bytes_state6 cs d len_word s) = SOME p` by
    metis_tac[abi_bytes_state6_input] >>
  `eval_operand (Var (abi_bytes_var cs 4))
     (abi_bytes_state6 cs d len_word s) = SOME (32w + len_word)` by
    simp[abi_bytes_state6_def, eval_operand_update_var] >>
  `step_inst_base
     (mk_inst (cs.cs_next_id + 6) MCOPY
       [dst; src; Var (abi_bytes_var cs 4)] [])
     (abi_bytes_state6 cs d len_word s) =
   OK (abi_bytes_state7 cs d p len_word s)` by
    simp[abi_bytes_state7_def, step_inst_base_def] >>
  mp_tac (Q.SPECL [`cs`,`dst`,`src`,`s`,`p`,`d`,`len_word`]
    abi_bytes_first_six_steps) >>
  impl_tac >- simp[] >> strip_tac >>
  `run_inst_seq
     (TAKE 6 (abi_bytes_append cs dst src []) ++
       [mk_inst (cs.cs_next_id + 6) MCOPY
         [dst; src; Var (abi_bytes_var cs 4)] []]) s =
   run_inst_seq
     [mk_inst (cs.cs_next_id + 6) MCOPY
       [dst; src; Var (abi_bytes_var cs 4)] []]
     (abi_bytes_state6 cs d len_word s)` by
    (irule run_inst_seq_append >> asm_rewrite_tac[]) >>
  simp[run_inst_seq_def]
QED

Theorem abi_bytes_mstore_memory_congruent[local]:
  ∀off a b.
    a.vs_memory = b.vs_memory ⇒
    (mstore off 0w a).vs_memory = (mstore off 0w b).vs_memory
Proof
  simp[mstore_def]
QED

Theorem abi_bytes_mcopy_memory_congruent[local]:
  ∀dst src n a b.
    a.vs_memory = b.vs_memory ⇒
    (mcopy dst src n a).vs_memory = (mcopy dst src n b).vs_memory
Proof
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_bytes_state7_memory:
  ∀cs d p len_word s.
    (abi_bytes_state7 cs d p len_word s).vs_memory =
    (mcopy (w2n d) (w2n p) (w2n (32w + len_word))
      (mstore
        (w2n (d + word_and
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
          (31w + len_word))) 0w s)).vs_memory
Proof
  rpt gen_tac >>
  `(abi_bytes_state4 cs d len_word s).vs_memory = s.vs_memory` by
    simp[abi_bytes_state4_def, abi_bytes_state3_def,
         update_var_def] >>
  `(abi_bytes_state5 cs d len_word s).vs_memory =
   (mstore
     (w2n (d + word_and
       0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
       (31w + len_word))) 0w s).vs_memory` by
    (simp[abi_bytes_state5_def] >>
     irule abi_bytes_mstore_memory_congruent >> simp[]) >>
  `(abi_bytes_state6 cs d len_word s).vs_memory =
   (abi_bytes_state5 cs d len_word s).vs_memory` by
    simp[abi_bytes_state6_def, update_var_def] >>
  simp[abi_bytes_state7_def] >>
  irule abi_bytes_mcopy_memory_congruent >> simp[]
QED

Theorem abi_bytes_copy_length_nowrap:
  ∀n. n + 32 < dimword (:256) ⇒
    w2n (32w + (n2w n:bytes32)) = n + 32
Proof
  rpt strip_tac >>
  simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD]
QED

Theorem abi_bytes_zero_address_nowrap:
  ∀(d:bytes32) n.
    w2n d + venomLayout$ceil32 n < dimword (:256) ⇒
    w2n (d + n2w (venomLayout$ceil32 n)) =
      w2n d + venomLayout$ceil32 n
Proof
  rpt strip_tac >>
  `d = n2w (w2n d)` by simp[] >>
  pop_assum SUBST1_TAC >>
  simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD]
QED

Theorem abi_bytes_state7_encoding:
  ∀cs bound bs s (p:bytes32) (d:bytes32).
    val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bs)
      (w2n p) s.vs_memory ∧
    w2n p + 32 + LENGTH bs ≤ LENGTH s.vs_memory ∧
    w2n p + 32 + LENGTH bs ≤
      w2n d + venomLayout$ceil32 (LENGTH bs) ∧
    LENGTH bs + 32 < dimword (:256) ∧
    w2n d + venomLayout$ceil32 (LENGTH bs) < dimword (:256) ⇒
    mem_bytes_at (w2n d) (32 + venomLayout$ceil32 (LENGTH bs))
      (abi_bytes_state7 cs d p (n2w (LENGTH bs)) s).vs_memory =
    enc (Bytes NONE) (contractABI$BytesV bs)
Proof
  rpt strip_tac >>
  `LENGTH bs ≤ dimword (:256) - 32` by decide_tac >>
  `w2n (32w + (n2w (LENGTH bs):bytes32)) = LENGTH bs + 32` by
    (irule abi_bytes_copy_length_nowrap >> simp[]) >>
  `w2n (d + n2w (venomLayout$ceil32 (LENGTH bs))) =
   w2n d + venomLayout$ceil32 (LENGTH bs)` by
    (irule abi_bytes_zero_address_nowrap >> simp[]) >>
  mp_tac (Q.SPECL
    [`bound`,`bs`,`w2n (p:bytes32)`,`w2n (d:bytes32)`,`s`]
    abi_bytes_mstore_mcopy_encoding) >>
  impl_tac >- simp[] >> strip_tac >>
  `LENGTH bs + 32 = 32 + LENGTH bs ∧
   venomLayout$ceil32 (LENGTH bs) + w2n d =
     w2n d + venomLayout$ceil32 (LENGTH bs)` by decide_tac >>
  `word_and
     0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
     (31w + (n2w (LENGTH bs):bytes32)) =
   n2w (venomLayout$ceil32 (LENGTH bs))` by
    (irule abi_bytes_round_mask_first >> simp[]) >>
  `((abi_bytes_state7 cs d p (n2w (LENGTH bs)) s).vs_memory) =
   (mcopy (w2n d) (w2n p) (32 + LENGTH bs)
     (mstore (w2n d + venomLayout$ceil32 (LENGTH bs)) 0w s)).vs_memory` by
    (ONCE_REWRITE_TAC [abi_bytes_state7_memory] >>
     ASM_REWRITE_TAC[]) >>
  asm_rewrite_tac[]
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "abiBytesStepExecution");
