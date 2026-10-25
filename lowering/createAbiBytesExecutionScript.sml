(* TOP-LEVEL: compile_create_abi_bytes_shape,
   create_abi_bytes_mstore_mcopy_encoding, create_abi_bytes_mload_length,
   create_abi_bytes_first_three_round.
   Exact generated code and its source-length, copy, and padding boundaries.
   The fragment execution proof composes these boundaries. *)
Theory createAbiBytesExecution
Ancestors
  abiEncoder compileEnv contractABI createAbiBytesValueEncoding emitHelper
  emitHelperProps exprLoweringProps
  fragExec venomInst
  venomExecSemantics venomLayout venomMemProps venomState valueEncoding
  valueEncodingProps
  list rich_list words byte
Libs
  wordsLib
Theorem create_abi_bytes_mask_not_31:
  (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w:bytes32) =
    ~31w
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem create_abi_bytes_and_complement:
  ∀x m:bytes32. word_and x (word_1comp m) = x - word_and x m
Proof
  rpt gen_tac >>
  `x = word_or (word_and x m) (word_and x (word_1comp m))` by
    simp[GSYM WORD_LEFT_AND_OVER_OR, WORD_OR_COMP, WORD_AND_CLAUSES] >>
  `(x && m) && x = x && m` by
    metis_tac[WORD_AND_ASSOC, WORD_AND_COMM, WORD_AND_IDEM] >>
  `word_and (word_and x m) (word_and x (word_1comp m)) = 0w` by
    metis_tac[WORD_AND_ASSOC, WORD_AND_COMP, WORD_AND_CLAUSES] >>
  metis_tac[WORD_ADD_OR, WORD_ADD_SUB, WORD_ADD_COMM]
QED

Theorem create_abi_bytes_low_five:
  ∀x:bytes32. x && 31w = n2w (w2n x MOD 32)
Proof
  gen_tac >>
  `x = n2w (w2n x)` by simp[] >>
  pop_assum SUBST1_TAC >>
  `31w:bytes32 = n2w (2 ** 5 - 1)` by EVAL_TAC >>
  pop_assum SUBST1_TAC >>
  PURE_REWRITE_TAC [WORD_AND_EXP_SUB1] >>
  simp[wordsTheory.w2n_n2w, wordsTheory.w2n_lt]
QED

Theorem create_abi_bytes_sub_mod_32[local]:
  ∀n. n - n MOD 32 = 32 * (n DIV 32)
Proof
  gen_tac >>
  mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >>
  simp[] >> disch_then (qspec_then `n` mp_tac) >> decide_tac
QED

Theorem create_abi_bytes_mask_shift:
  ∀x:bytes32.
    x && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w =
    word_lsl (word_lsr x 5) 5
Proof
  gen_tac >>
  `x && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w =
     n2w (w2n x - w2n x MOD 32)` by
    (`x = n2w (w2n x)` by simp[] >>
     `w2n x MOD 32 ≤ w2n x` by
       simp[arithmeticTheory.MOD_LESS_EQ] >>
     ONCE_REWRITE_TAC [create_abi_bytes_mask_not_31] >>
     ONCE_REWRITE_TAC [create_abi_bytes_and_complement] >>
     ONCE_REWRITE_TAC [create_abi_bytes_low_five] >>
     metis_tac[wordsTheory.n2w_sub]) >>
  `word_lsl (word_lsr x 5) 5 = n2w (32 * (w2n x DIV 32))` by
    (`word_lsr x 5 = n2w (w2n (word_lsr x 5))` by simp[] >>
     pop_assum SUBST1_TAC >>
     simp[wordsTheory.word_lsl_n2w, wordsTheory.w2n_lsr]) >>
  simp[create_abi_bytes_sub_mod_32]
QED

Theorem create_abi_bytes_ceil32_div[local]:
  ∀n. venomLayout$ceil32 n = ((n + 31) DIV 32) * 32
Proof
  gen_tac >>
  mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >>
  simp[] >> disch_then (qspec_then `n` strip_assume_tac) >>
  Cases_on `n MOD 32 = 0`
  >- (`n + 31 = n DIV 32 * 32 + 31` by decide_tac >>
      PURE_REWRITE_TAC [venomLayoutTheory.ceil32_def] >>
      simp[arithmeticTheory.DIV_MULT] >> decide_tac) >>
  `0 < n MOD 32` by decide_tac >>
  `n + 31 = (n DIV 32 + 1) * 32 + (n MOD 32 - 1)` by decide_tac >>
  `n MOD 32 < 32` by
    (irule arithmeticTheory.MOD_LESS >> simp[]) >>
  `n MOD 32 - 1 < 32` by decide_tac >>
  `(n + 31) DIV 32 = n DIV 32 + 1` by
    (once_rewrite_tac
       [ASSUME ``n + 31 = (n DIV 32 + 1) * 32 + (n MOD 32 - 1)``] >>
     irule arithmeticTheory.DIV_MULT >> simp[]) >>
  rw[venomLayoutTheory.ceil32_def] >> decide_tac
QED

Theorem create_abi_bytes_round_word:
  ∀n. n ≤ dimword (:256) - 32 ⇒
    word_and ((n2w n : bytes32) + 31w)
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w =
    n2w (venomLayout$ceil32 n)
Proof
  rpt strip_tac >>
  `n + 31 < dimword (:256)` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  simp[create_abi_bytes_mask_shift, wordsTheory.word_add_n2w,
       wordsTheory.word_lsl_n2w, wordsTheory.w2n_lsr,
       arithmeticTheory.LESS_MOD, create_abi_bytes_ceil32_div,
       arithmeticTheory.MULT_COMM] >>
  `word_lsr (n2w (n + 31) : bytes32) 5 =
     n2w (w2n (word_lsr (n2w (n + 31) : bytes32) 5))` by simp[] >>
  pop_assum SUBST1_TAC >>
  simp[wordsTheory.word_lsl_n2w, wordsTheory.w2n_lsr,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
       arithmeticTheory.MULT_COMM]
QED

Theorem create_abi_bytes_zero_word[local]:
  word_to_bytes (0w:bytes32) T = REPLICATE 32 (0w:word8)
Proof
  EVAL_TAC
QED

Theorem create_abi_bytes_zero_subword:
  ∀off k s. k ≤ 32 ⇒
    mem_bytes_at (off + k) (32 - k) (mstore off 0w s).vs_memory =
    REPLICATE (32 - k) (0w:word8)
Proof
  rpt strip_tac >>
  `mem_bytes_at off 32 (mstore off 0w s).vs_memory =
     REPLICATE 32 (0w:word8)` by
    (`32 ≤ LENGTH (DROP off
        (write_memory_with_expansion off (REPLICATE 32 0w) s).vs_memory)` by
       simp[LENGTH_DROP, LENGTH_write_memory_with_expansion,
            arithmeticTheory.MAX_DEF] >>
      mp_tac (Q.SPECL [`off`, `REPLICATE 32 (0w:word8)`, `s`]
        write_memory_with_expansion_read_self) >>
      simp[mem_bytes_at_def, mstore_eq_write_mem,
           create_abi_bytes_zero_word, TAKE_APPEND1]) >>
  `off + (k + (32 - k)) ≤ LENGTH (mstore off 0w s).vs_memory` by
    simp[LENGTH_mstore_eq, arithmeticTheory.MAX_DEF] >>
  drule_at_then Any mp_tac mem_bytes_at_split >>
  simp[] >> strip_tac >>
  `DROP k (mem_bytes_at off k (mstore off 0w s).vs_memory) = []` by
    simp[listTheory.DROP_LENGTH_TOO_LONG] >>
  qpat_x_assum `mem_bytes_at off k _ ++ _ = REPLICATE 32 _`
    (mp_tac o Q.AP_TERM `DROP k`) >>
  simp[rich_listTheory.DROP_REPLICATE, LENGTH_mem_bytes_at,
       rich_listTheory.DROP_APPEND1, rich_listTheory.DROP_LENGTH_NIL]
QED

Theorem create_abi_bytes_zero_after_copy:
  ∀off k dst src n s.
    k ≤ 32 ∧ dst + n ≤ off + k ⇒
    mem_bytes_at (off + k) (32 - k)
      (mcopy dst src n (mstore off 0w s)).vs_memory =
    REPLICATE (32 - k) (0w:word8)
Proof
  rpt strip_tac >>
  `off + k + (32 - k) ≤ LENGTH (mstore off 0w s).vs_memory` by
    simp[LENGTH_mstore_eq, arithmeticTheory.MAX_DEF] >>
  `TAKE (32 - k)
      (DROP (off + k)
        (mcopy dst src n (mstore off 0w s)).vs_memory) =
   TAKE (32 - k)
      (DROP (off + k) (mstore off 0w s).vs_memory)` by
    (simp[mcopy_def, GSYM read_memory_def] >>
     irule write_memory_with_expansion_disjoint_read >>
     simp[read_memory_def, LENGTH_TAKE, LENGTH_DROP]) >>
  `off + k + (32 - k) ≤ LENGTH
      (mcopy dst src n (mstore off 0w s)).vs_memory` by
    simp[mcopy_def, LENGTH_write_memory_with_expansion,
         LENGTH_mstore_eq, arithmeticTheory.MAX_DEF] >>
  `mem_bytes_at (off + k) (32 - k) (mstore off 0w s).vs_memory =
   TAKE (32 - k) (DROP (off + k) (mstore off 0w s).vs_memory)` by
    simp[mem_bytes_at_def, TAKE_APPEND1, LENGTH_DROP] >>
  `mem_bytes_at (off + k) (32 - k)
      (mcopy dst src n (mstore off 0w s)).vs_memory =
   TAKE (32 - k)
      (DROP (off + k)
        (mcopy dst src n (mstore off 0w s)).vs_memory)` by
    simp[mem_bytes_at_def, TAKE_APPEND1, LENGTH_DROP] >>
  metis_tac[create_abi_bytes_zero_subword]
QED

Theorem create_abi_bytes_source_read_after_zero:
  ∀src n off s.
    src + n ≤ LENGTH s.vs_memory ∧ src + n ≤ off ⇒
    read_memory src n (mstore off 0w s) = read_memory src n s
Proof
  rpt strip_tac >>
  `TAKE n (DROP src (mstore off 0w s).vs_memory) =
   TAKE n (DROP src s.vs_memory)` by
    (irule mstore_disjoint_read >>
     simp[venomMemDefsTheory.regions_disjoint_def]) >>
  `src + n ≤ LENGTH (mstore off 0w s).vs_memory` by
    simp[LENGTH_mstore_eq, arithmeticTheory.MAX_DEF] >>
  fs[read_memory_def, TAKE_APPEND1, LENGTH_DROP]
QED

Theorem create_abi_bytes_copy_read_self:
  ∀dst src n s.
    mem_bytes_at dst n (mcopy dst src n s).vs_memory = read_memory src n s
Proof
  rpt gen_tac >>
  `LENGTH (read_memory src n s) = n` by
    simp[read_memory_def, LENGTH_TAKE, LENGTH_DROP] >>
  `n ≤ LENGTH (DROP dst
      (write_memory_with_expansion dst (read_memory src n s) s).vs_memory)` by
    simp[LENGTH_DROP, LENGTH_write_memory_with_expansion,
         arithmeticTheory.MAX_DEF] >>
  `mcopy dst src n s =
   write_memory_with_expansion dst (read_memory src n s) s` by
    simp[mcopy_def, read_memory_def] >>
  `TAKE n (DROP dst
      (write_memory_with_expansion dst (read_memory src n s) s).vs_memory) =
   read_memory src n s` by
    metis_tac[write_memory_with_expansion_read_self] >>
  gvs[mem_bytes_at_def, TAKE_APPEND1]
QED

Theorem create_abi_bytes_ceil32_gap:
  ∀n. n ≤ venomLayout$ceil32 n ∧ venomLayout$ceil32 n ≤ n + 32
Proof
  gen_tac >> simp[venomLayoutTheory.ceil32_ge, venomLayoutTheory.ceil32_def] >>
  `n MOD 32 < 32` by simp[] >> decide_tac
QED

Theorem create_abi_bytes_ceil32_eq:
  ∀n. venomLayout$ceil32 n = contractABI$ceil32 n
Proof
  simp[create_abi_bytes_ceil32_div, contractABITheory.ceil32_def,
       arithmeticTheory.MULT_COMM]
QED

Theorem create_abi_bytes_encoding_parts:
  ∀bs.
    enc (Bytes NONE) (contractABI$BytesV bs) =
    TAKE (32 + LENGTH bs) (enc (Bytes NONE) (contractABI$BytesV bs)) ++
    REPLICATE (venomLayout$ceil32 (LENGTH bs) - LENGTH bs) (0w:word8)
Proof
  gen_tac >>
  simp[Once contractABITheory.enc_def, enc_number_def,
       byteTheory.LENGTH_word_to_bytes, TAKE_APPEND1, TAKE_APPEND,
       listTheory.TAKE_LENGTH_TOO_LONG, create_abi_bytes_ceil32_eq,
       venomLayoutTheory.ceil32_ge] >>
  simp[]
QED

Theorem create_abi_bytes_mstore_mcopy_encoding:
  ∀bound bs src dst s.
    val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bs)
      src s.vs_memory ∧
    src + 32 + LENGTH bs ≤ LENGTH s.vs_memory ∧
    src + 32 + LENGTH bs ≤ dst + venomLayout$ceil32 (LENGTH bs) ⇒
    mem_bytes_at dst (32 + venomLayout$ceil32 (LENGTH bs))
      (mcopy dst src (32 + LENGTH bs)
        (mstore (dst + venomLayout$ceil32 (LENGTH bs)) 0w s)).vs_memory =
    enc (Bytes NONE) (contractABI$BytesV bs)
Proof
  rpt strip_tac >>
  `LENGTH bs ≤ venomLayout$ceil32 (LENGTH bs) ∧
   venomLayout$ceil32 (LENGTH bs) ≤ LENGTH bs + 32` by
    simp[create_abi_bytes_ceil32_gap] >>
  `mem_bytes_at dst (32 + LENGTH bs)
      (mcopy dst src (32 + LENGTH bs)
        (mstore (dst + venomLayout$ceil32 (LENGTH bs)) 0w s)).vs_memory =
   TAKE (32 + LENGTH bs)
      (enc (Bytes NONE) (contractABI$BytesV bs))` by
    (simp[create_abi_bytes_copy_read_self] >>
     `read_memory src (32 + LENGTH bs)
        (mstore (dst + venomLayout$ceil32 (LENGTH bs)) 0w s) =
      read_memory src (32 + LENGTH bs) s` by
       (irule create_abi_bytes_source_read_after_zero >> decide_tac) >>
     `mem_bytes_at src (32 + LENGTH bs) s.vs_memory =
      TAKE (32 + LENGTH bs)
        (enc (Bytes NONE) (contractABI$BytesV bs))` by
       (drule_all create_abi_dynamic_bytes_prefix >> simp[]) >>
     gvs[read_memory_def, mem_bytes_at_def]) >>
  `mem_bytes_at (dst + 32 + LENGTH bs)
      (venomLayout$ceil32 (LENGTH bs) - LENGTH bs)
      (mcopy dst src (32 + LENGTH bs)
        (mstore (dst + venomLayout$ceil32 (LENGTH bs)) 0w s)).vs_memory =
   REPLICATE (venomLayout$ceil32 (LENGTH bs) - LENGTH bs) (0w:word8)` by
    (mp_tac (Q.SPECL
       [`dst + venomLayout$ceil32 (LENGTH (bs:byte list))`,
        `32 + LENGTH (bs:byte list) -
           venomLayout$ceil32 (LENGTH (bs:byte list))`,
        `dst`, `src`, `32 + LENGTH (bs:byte list)`, `s`]
        create_abi_bytes_zero_after_copy) >>
     impl_tac >- decide_tac >>
     simp[] >> decide_tac) >>
  `dst + (32 + venomLayout$ceil32 (LENGTH bs)) ≤
   LENGTH (mcopy dst src (32 + LENGTH bs)
     (mstore (dst + venomLayout$ceil32 (LENGTH bs)) 0w s)).vs_memory` by
    simp[mcopy_def, LENGTH_write_memory_with_expansion,
         LENGTH_mstore_eq, arithmeticTheory.MAX_DEF] >>
  mp_tac (Q.SPECL
    [`dst`, `32 + LENGTH (bs:byte list)`,
     `venomLayout$ceil32 (LENGTH (bs:byte list)) -
        LENGTH (bs:byte list)`,
     `(mcopy dst src (32 + LENGTH (bs:byte list))
       (mstore (dst + venomLayout$ceil32 (LENGTH (bs:byte list)))
          0w s)).vs_memory`]
    mem_bytes_at_split) >>
  impl_tac >- decide_tac >>
  strip_tac >>
  gvs[create_abi_bytes_encoding_parts, create_abi_bytes_ceil32_eq,
      TAKE_APPEND1, TAKE_APPEND,
      byteTheory.LENGTH_word_to_bytes, listTheory.TAKE_LENGTH_TOO_LONG] >>
  `LENGTH bs ≤ contractABI$ceil32 (LENGTH bs)` by
    simp[GSYM create_abi_bytes_ceil32_eq,
         venomLayoutTheory.ceil32_ge] >>
  `LENGTH bs + 32 + (contractABI$ceil32 (LENGTH bs) - LENGTH bs) =
   contractABI$ceil32 (LENGTH bs) + 32` by decide_tac >>
  qpat_x_assum `LENGTH bs + 32 + _ = _`
    (fn th => SUBST1_TAC (SYM th)) >>
  asm_rewrite_tac[]
QED

Theorem create_abi_bytes_mload_length:
  val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bs)
    src s.vs_memory ⇒
  mload src s = n2w (LENGTH bs)
Proof
  simp[Once val_in_memory_def, GSYM mem_word_at_eq_mload]
QED

Definition create_abi_bytes_var_def:
  create_abi_bytes_var cs k = "%" ++ toString (cs.cs_next_var + k)
End

Theorem create_abi_bytes_var_distinct:
  ∀cs i j.
    create_abi_bytes_var cs i = create_abi_bytes_var cs j ⇔ i = j
Proof
  simp[create_abi_bytes_var_def] >>
  metis_tac[fresh_var_distinct, DECIDE ``b + i = b + j ⇔ i = j``]
QED

Theorem create_abi_bytes_input_disjoint:
  fresh_vars_wrt cs s ∧ eval_operand op s = SOME value ∧
  op = Var name ⇒ name ≠ create_abi_bytes_var cs k
Proof
  strip_tac >>
  `cs.cs_next_var + k ≥ cs.cs_next_var` by simp[] >>
  drule_all fresh_vars_wrt_eval_operand >>
  simp[create_abi_bytes_var_def, arithmeticTheory.ADD_COMM]
QED

Definition create_abi_bytes_append_def:
  create_abi_bytes_append cs dst src prefix =
    let v = create_abi_bytes_var cs in
    let id = cs.cs_next_id in
    prefix ++ [mk_inst id MLOAD [src] [v 0]] ++
     [mk_inst (id + 1) ADD [Lit 31w; Var (v 0)] [v 1]] ++
     [mk_inst (id + 2) AND
       [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
        Var (v 1)] [v 2]] ++
     [mk_inst (id + 3) ADD [dst; Var (v 2)] [v 3]] ++
     [mk_inst (id + 4) MSTORE [Var (v 3); Lit 0w] []] ++
     [mk_inst (id + 5) ADD [Lit 32w; Var (v 0)] [v 4]] ++
     [mk_inst (id + 6) MCOPY [dst; src; Var (v 4)] []] ++
     [mk_inst (id + 7) ADD [Lit 31w; Var (v 0)] [v 5]] ++
     [mk_inst (id + 8) AND
       [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
        Var (v 5)] [v 6]] ++
     [mk_inst (id + 9) ADD [Lit 32w; Var (v 6)] [v 7]]
End

Theorem create_abi_bytes_append_prefix:
  create_abi_bytes_append cs dst src prefix =
    prefix ++ create_abi_bytes_append cs dst src []
Proof
  simp[create_abi_bytes_append_def, APPEND_ASSOC]
QED

Theorem create_abi_bytes_append_length:
  LENGTH (create_abi_bytes_append cs dst src prefix) = LENGTH prefix + 10
Proof
  simp[create_abi_bytes_append_def]
QED

Theorem create_abi_bytes_first_two_steps:
  ∀cs dst src s p len_word.
    fresh_vars_wrt cs s ∧ eval_operand src s = SOME p ∧
    mload (w2n p) s = len_word ⇒
    run_inst_seq (TAKE 2 (create_abi_bytes_append cs dst src [])) s =
      OK (update_var (create_abi_bytes_var cs 1) (31w + len_word)
        (update_var (create_abi_bytes_var cs 0) len_word s))
Proof
  rpt strip_tac >>
  `eval_operand src
     (update_var (create_abi_bytes_var cs 0) len_word s) = SOME p` by
    (irule eval_operand_update_var_mstore >> simp[] >>
     metis_tac[create_abi_bytes_input_disjoint]) >>
  `step_inst_base
     (mk_inst cs.cs_next_id MLOAD [src] [create_abi_bytes_var cs 0]) s =
   OK (update_var (create_abi_bytes_var cs 0) len_word s)` by
    (qpat_x_assum `mload (w2n p) s = len_word`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     irule step_MLOAD >> simp[]) >>
  `step_inst_base
     (mk_inst (cs.cs_next_id + 1) ADD
       [Lit 31w; Var (create_abi_bytes_var cs 0)]
       [create_abi_bytes_var cs 1])
     (update_var (create_abi_bytes_var cs 0) len_word s) =
   OK (update_var (create_abi_bytes_var cs 1) (31w + len_word)
     (update_var (create_abi_bytes_var cs 0) len_word s))` by
    (irule step_ADD >> simp[eval_operand_def, eval_operand_update_var]) >>
  simp[create_abi_bytes_append_def, run_inst_seq_def,
       listTheory.TAKE_def]
QED

Theorem create_abi_bytes_first_three_steps:
  ∀cs dst src s p len_word.
    fresh_vars_wrt cs s ∧ eval_operand src s = SOME p ∧
    mload (w2n p) s = len_word ⇒
    run_inst_seq (TAKE 3 (create_abi_bytes_append cs dst src [])) s =
      OK (update_var (create_abi_bytes_var cs 2)
        (word_and
          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
          (31w + len_word))
        (update_var (create_abi_bytes_var cs 1) (31w + len_word)
          (update_var (create_abi_bytes_var cs 0) len_word s)))
Proof
  rpt strip_tac >>
  `TAKE 3 (create_abi_bytes_append cs dst src []) =
   TAKE 2 (create_abi_bytes_append cs dst src []) ++
     [mk_inst (cs.cs_next_id + 2) AND
       [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
        Var (create_abi_bytes_var cs 1)]
       [create_abi_bytes_var cs 2]]` by
    simp[create_abi_bytes_append_def, listTheory.TAKE_def] >>
  `step_inst_base
     (mk_inst (cs.cs_next_id + 2) AND
       [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
        Var (create_abi_bytes_var cs 1)]
       [create_abi_bytes_var cs 2])
     (update_var (create_abi_bytes_var cs 1) (31w + len_word)
       (update_var (create_abi_bytes_var cs 0) len_word s)) =
   OK (update_var (create_abi_bytes_var cs 2)
     (word_and
       0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
       (31w + len_word))
     (update_var (create_abi_bytes_var cs 1) (31w + len_word)
       (update_var (create_abi_bytes_var cs 0) len_word s)))` by
    (irule step_AND >> simp[eval_operand_def, eval_operand_update_var]) >>
  drule_all_then (qspec_then `dst` strip_assume_tac)
    create_abi_bytes_first_two_steps >>
  fs[wordsTheory.WORD_ADD_COMM] >>
  qpat_x_assum `run_inst_seq (TAKE 2 _) s = OK _`
    (fn th => REWRITE_TAC [MATCH_MP run_inst_seq_append th]) >>
  simp[run_inst_seq_def]
QED

Theorem create_abi_bytes_round_mask_first:
  ∀n. n ≤ dimword (:256) - 32 ⇒
    word_and
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
      (31w + (n2w n:bytes32)) =
    n2w (venomLayout$ceil32 n)
Proof
  rpt strip_tac >>
  `word_and
     0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
     (31w + (n2w n:bytes32)) =
   word_and ((n2w n:bytes32) + 31w)
     0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w` by
    metis_tac[wordsTheory.WORD_AND_COMM, wordsTheory.WORD_ADD_COMM] >>
  metis_tac[create_abi_bytes_round_word]
QED

Theorem create_abi_bytes_first_three_round:
  ∀cs dst src s p n.
    fresh_vars_wrt cs s ∧ eval_operand src s = SOME p ∧
    mload (w2n p) s = n2w n ∧ n ≤ dimword (:256) - 32 ⇒
    ∃s3.
      run_inst_seq (TAKE 3 (create_abi_bytes_append cs dst src [])) s =
        OK s3 ∧
      eval_operand (Var (create_abi_bytes_var cs 2)) s3 =
        SOME (n2w (venomLayout$ceil32 n))
Proof
  rpt strip_tac >>
  drule_all_then (qspec_then `dst` strip_assume_tac)
    create_abi_bytes_first_three_steps >>
  goal_assum drule >>
  simp[eval_operand_update_var, create_abi_bytes_round_mask_first]
QED

Theorem compile_create_abi_bytes_shape:
  compile_abi_encode_to_buf dst src (AbiBytestring bound) cs =
    (Var (create_abi_bytes_var cs 7),
     cs with <|cs_next_id := cs.cs_next_id + 10;
               cs_next_var := cs.cs_next_var + 8;
               cs_current_insts :=
                 create_abi_bytes_append cs dst src cs.cs_current_insts|>)
Proof
  simp[Once compile_abi_encode_child_def, create_abi_bytes_append_def,
       create_abi_bytes_var_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, LET_THM]
QED

Theorem compile_create_abi_bytes_fragment:
  compile_abi_encode_to_buf dst src (AbiBytestring bound) cs = (result,cs') ⇒
  result = Var (create_abi_bytes_var cs 7) ∧
  same_blocks cs cs' ∧ cs_extends cs cs' ∧
  emitted_insts cs cs' = create_abi_bytes_append cs dst src []
Proof
  strip_tac >> gvs[compile_create_abi_bytes_shape] >>
  `create_abi_bytes_append cs dst src cs.cs_current_insts =
     cs.cs_current_insts ++ create_abi_bytes_append cs dst src []` by
    (irule create_abi_bytes_append_prefix) >>
  pop_assum SUBST_ALL_TAC >>
  simp[same_blocks_def, cs_extends_def, emitted_insts_def,
       IS_PREFIX_APPEND, rich_listTheory.DROP_LENGTH_APPEND]
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createAbiBytesExecution");
