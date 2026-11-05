(* Counted memory safety of the Error(string) revert encoder
   (compile_revert_with_reason): its code, and its straight-line run from a
   message pointer whose rounded footprint is below the frontier. *)
Theory stmtReasonMemory
Ancestors
  fragExecMem instMemFrontier stmtLowering emitHelper emitHelperProps
  exprLoweringProps context compileEnv valueEncoding valueEncodingProps
  valueEncodingProofs venomMemDefs venomMemProps venomExecSemantics venomState venomInst
  memSafeRun words arithmetic list rich_list finite_map
Libs
  monadsyntax blastLib

(* The encoder's code before the message's unwrap_value: the selector
   buffer, its payload pointer and the tuple buffer. *)
Definition reason_head_def:
  reason_head (id:num) (v:num) (M:num) =
    [mk_inst id ALLOCA [Lit (n2w (64 + M))] ["%" ++ toString v];
     mk_inst (id + 1) MSTORE
       [Var ("%" ++ toString v); Lit (0x08c379a0w : bytes32)] [];
     mk_inst (id + 2) ADD [Var ("%" ++ toString v); Lit 32w]
       ["%" ++ toString (v + 1)];
     mk_inst (id + 3) ALLOCA [Lit (n2w M)] ["%" ++ toString (v + 2)]]
End

(* The encoder's code after unwrap_value, up to its REVERT: u numbers its
   own variables, v the head's, op is the message pointer. *)
Definition reason_tail_def:
  reason_tail (j:num) (u:num) (v:num) op =
    let x = \n:num. "%" ++ toString n in
    let mask =
      (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w
         : bytes32) in
    [mk_inst j MLOAD [op] [x u];
     mk_inst (j + 1) ADD [Var (x u); Lit 31w] [x (u + 1)];
     mk_inst (j + 2) AND [Var (x (u + 1)); Lit mask] [x (u + 2)];
     mk_inst (j + 3) ADD [Lit 32w; Var (x (u + 2))] [x (u + 3)];
     mk_inst (j + 4) MCOPY [Var (x (v + 2)); op; Var (x (u + 3))] [];
     mk_inst (j + 5) ALLOCA [Lit 32w] [x (u + 4)];
     mk_inst (j + 6) MSTORE [Var (x (u + 4)); Lit 32w] [];
     mk_inst (j + 7) ADD [Var (x (v + 2)); Lit 0w] [x (u + 5)];
     mk_inst (j + 8) ADD [Var (x (v + 1)); Lit 0w] [x (u + 6)];
     mk_inst (j + 9) MLOAD [Var (x (u + 4))] [x (u + 7)];
     mk_inst (j + 10) ADD [Var (x (v + 1)); Var (x (u + 7))] [x (u + 8)];
     mk_inst (j + 11) MLOAD [Var (x (u + 5))] [x (u + 9)];
     mk_inst (j + 12) ADD [Var (x (u + 9)); Lit 31w] [x (u + 10)];
     mk_inst (j + 13) AND [Var (x (u + 10)); Lit mask] [x (u + 11)];
     mk_inst (j + 14) ADD [Var (x (u + 8)); Var (x (u + 11))] [x (u + 12)];
     mk_inst (j + 15) MSTORE [Var (x (u + 12)); Lit 0w] [];
     mk_inst (j + 16) ADD [Lit 32w; Var (x (u + 9))] [x (u + 13)];
     mk_inst (j + 17) MCOPY
       [Var (x (u + 8)); Var (x (u + 5)); Var (x (u + 13))] [];
     mk_inst (j + 18) ADD [Var (x (u + 9)); Lit 31w] [x (u + 14)];
     mk_inst (j + 19) AND [Var (x (u + 14)); Lit mask] [x (u + 15)];
     mk_inst (j + 20) ADD [Lit 32w; Var (x (u + 15))] [x (u + 16)];
     mk_inst (j + 21) MSTORE [Var (x (u + 6)); Var (x (u + 7))] [];
     mk_inst (j + 22) ADD [Var (x (u + 7)); Var (x (u + 16))] [x (u + 17)];
     mk_inst (j + 23) MSTORE [Var (x (u + 4)); Var (x (u + 17))] [];
     mk_inst (j + 24) MLOAD [Var (x (u + 4))] [x (u + 18)];
     mk_inst (j + 25) ADD [Var (x v); Lit 28w] [x (u + 19)];
     mk_inst (j + 26) ADD [Lit 4w; Var (x (u + 18))] [x (u + 20)];
     mk_inst (j + 27) REVERT [Var (x (u + 19)); Var (x (u + 20))] []]
End

Theorem compile_revert_reason_shape:
  !cenv vv mt M sa sb.
    compile_revert_with_reason cenv vv mt M sa = ((), sb) ==>
    ?op sn.
      unwrap_value cenv vv
        (sa with <| cs_next_id := sa.cs_next_id + 4;
                    cs_next_var := sa.cs_next_var + 3;
                    cs_current_insts := sa.cs_current_insts ++
                      reason_head sa.cs_next_id sa.cs_next_var M |>) =
        (op, sn) /\
      sb = sn with <| cs_next_id := sn.cs_next_id + 28;
                      cs_next_var := sn.cs_next_var + 21;
                      cs_current_insts := sn.cs_current_insts ++
                        reason_tail sn.cs_next_id sn.cs_next_var
                          sa.cs_next_var op |>
Proof
  rpt gen_tac >>
  simp[compile_revert_with_reason_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qexistsl [`msg_op`, `cs'`] >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC, APPEND, reason_head_def,
                   reason_tail_def, LET_THM] >>
  BETA_TAC >> strip_tac >> simp[compile_state_component_equality]
QED

(* The rounding mask on a word that does not wrap. *)
Theorem w2n_round32:
  !n. n + 31 < dimword (:256) ==>
    w2n (word_and (n2w n + 31w : bytes32)
      0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w) =
    ((n + 31) DIV 32) * 32
Proof
  rpt strip_tac >>
  `!w:bytes32. word_and w
      0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w =
    (w >>> 5) << 5` by BBLAST_TAC >>
  `!w:bytes32. w >>> 5 = n2w (w2n w DIV 32)` by
    (gen_tac >>
     `w2n w DIV 32 <= w2n w` by simp[DIV_LESS_EQ] >>
     `w2n w < dimword (:256)` by simp[w2n_lt] >>
     `w2n w DIV 32 < dimword (:256)` by decide_tac >>
     ONCE_REWRITE_TAC[GSYM w2n_11] >> REWRITE_TAC[w2n_lsr, w2n_n2w] >>
     simp[]) >>
  asm_rewrite_tac[] >>
  `(n + 31) DIV 32 * 32 <= n + 31` by
    (qspec_then `32` mp_tac DIVISION >> simp[] >>
     disch_then (qspec_then `n + 31` mp_tac) >> decide_tac) >>
  `(n + 31) DIV 32 * 32 < dimword (:256)` by decide_tac >>
  fs[word_add_n2w, word_lsl_n2w, w2n_n2w]
QED

(* A copy of at least a word moves the word at its source. *)
Theorem mload_mcopy_same:
  !d src n s. 32 <= n ==> mload d (mcopy d src n s) = mload src s
Proof
  rpt strip_tac >>
  `mem_bytes_at d 32 (mcopy d src n s).vs_memory =
   mem_bytes_at src 32 s.vs_memory` by
    (qspecl_then [`d`, `src`, `n`, `s`] mp_tac mcopy_mem_bytes_at_same >>
     `n = 32 + (n - 32)` by decide_tac >>
     pop_assum (fn th => once_rewrite_tac [th]) >>
     simp_tac std_ss [valueEncodingProofsTheory.mem_bytes_at_split_padded] >>
     simp[APPEND_LENGTH_EQ]) >>
  simp[GSYM mem_word_at_eq_mload, mem_word_at_def, GSYM mem_bytes_at_def]
QED

(* ===== Stepping the encoder ===== *)

Theorem dload_mk_inst_other[local]:
  !id op ops outs s.
    op <> DLOAD /\ op <> DLOADBYTES ==>
    inst_dload_in_section (mk_inst id op ops outs) s
Proof
  simp[inst_dload_in_section_def, mk_inst_def]
QED

Theorem step_add_eq[local]:
  step_inst_base (mk_inst id ADD [a; b] [out]) s =
    case (eval_operand a s, eval_operand b s) of
      (SOME x, SOME y) => OK (update_var out (x + y) s)
    | _ => Error "undefined operand"
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def]
QED

Theorem step_and_eq[local]:
  step_inst_base (mk_inst id AND [a; b] [out]) s =
    case (eval_operand a s, eval_operand b s) of
      (SOME x, SOME y) => OK (update_var out (word_and x y) s)
    | _ => Error "undefined operand"
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def]
QED

Theorem step_mload_eq[local]:
  step_inst_base (mk_inst id MLOAD [a] [out]) s =
    case eval_operand a s of
      SOME x => OK (update_var out (mload (w2n x) s) s)
    | NONE => Error "undefined operand"
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def]
QED

Theorem step_mstore_eq[local]:
  step_inst_base (mk_inst id MSTORE [a; b] []) s =
    case (eval_operand a s, eval_operand b s) of
      (SOME x, SOME y) => OK (mstore (w2n x) y s)
    | _ => Error "undefined operand"
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def]
QED

Theorem step_mcopy_eq[local]:
  step_inst_base (mk_inst id MCOPY [a; b; c] []) s =
    case (eval_operand a s, eval_operand b s, eval_operand c s) of
      (SOME d, SOME x, SOME n) => OK (mcopy (w2n d) (w2n x) (w2n n) s)
    | _ => Error "undefined operand"
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def]
QED

Theorem step_alloca_eq[local]:
  step_inst_base (mk_inst id ALLOCA [Lit sz] [out]) s =
    case FLOOKUP s.vs_allocas id of
      SOME (off, n) => OK (update_var out (n2w off) s)
    | NONE =>
        OK (update_var out (n2w s.vs_alloca_next)
              (s with <| vs_allocas :=
                           s.vs_allocas |+ (id, (s.vs_alloca_next, w2n sz));
                         vs_alloca_next := s.vs_alloca_next + w2n sz |>))
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[] >>
  PairCases_on `x` >> simp[]
QED

Theorem step_revert_eq[local]:
  step_inst_base (mk_inst id REVERT [a; b] []) s =
    case (eval_operand a s, eval_operand b s) of
      (SOME off, SOME sz) =>
        Abort Revert_abort (revert_state (set_returndata
          (TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++
                          REPLICATE (w2n sz) 0w)) s))
    | _ => Error "revert: undefined operand"
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def]
QED

Theorem encoder_fields[local,simp]:
  (update_var x w s).vs_alloca_next = s.vs_alloca_next /\
  (update_var x w s).vs_allocas = s.vs_allocas /\
  (mstore a w s).vs_alloca_next = s.vs_alloca_next /\
  (mstore a w s).vs_allocas = s.vs_allocas /\
  (mcopy d src n s).vs_alloca_next = s.vs_alloca_next /\
  (mcopy d src n s).vs_allocas = s.vs_allocas /\
  lookup_var x (mcopy d src n s) = lookup_var x s /\
  lookup_var x (s with <| vs_allocas := al; vs_alloca_next := nx |>) =
    lookup_var x s /\
  mload a (update_var x w s) = mload a s /\
  mload a (s with <| vs_allocas := al; vs_alloca_next := nx |>) = mload a s
Proof
  simp[update_var_def, mstore_def, mcopy_def, lookup_var_def, mload_def,
       write_memory_with_expansion_def]
QED

Theorem mload_mstore_apart[local]:
  !a b w s. a + 32 <= b \/ b + 32 <= a ==>
    mload b (mstore a w s) = mload b s
Proof
  rpt strip_tac >> irule mload_mstore_disjoint >>
  simp[regions_disjoint_def]
QED

Theorem mk_inst_opcode[local,simp]:
  (mk_inst id op ops outs).inst_opcode = op
Proof
  simp[mk_inst_def]
QED

(* One non-terminating step of a run that ends at a REVERT. *)
Theorem tail_step[local]:
  !i is s s'.
    step_inst_base i s = OK s' /\
    inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
    run_inst_seq_mem_ok is s' /\
    (?t. run_inst_seq is s' = Abort Revert_abort t) ==>
    run_inst_seq_mem_ok (i::is) s /\
    ?t. run_inst_seq (i::is) s = Abort Revert_abort t
Proof
  rpt strip_tac >> simp[run_inst_seq_mem_ok_def, run_inst_seq_def]
QED

Theorem tail_last[local]:
  !i s t.
    step_inst_base i s = Abort Revert_abort t /\
    inst_mem_below_frontier i s /\ inst_dload_in_section i s ==>
    run_inst_seq_mem_ok [i] s /\
    ?t. run_inst_seq [i] s = Abort Revert_abort t
Proof
  rpt strip_tac >> simp[run_inst_seq_mem_ok_def, run_inst_seq_def]
QED

val tail_ss =
  [step_add_eq, step_and_eq, step_mload_eq, step_mstore_eq,
   step_mcopy_eq, step_alloca_eq, step_revert_eq,
   below_frontier_MLOAD, below_frontier_MSTORE, below_frontier_MCOPY,
   below_frontier_REVERT, below_frontier_no_ranges,
   eval_operand_def, lookup_var_update_var, word_add_n2w,
   mload_mstore_same, mload_mstore_apart, mload_mcopy_same,
   dload_mk_inst_other];

(* simp may turn the goal's two conjuncts around. *)
fun swap_concl th =
  GEN_ALL (DISCH_ALL (ONCE_REWRITE_RULE [CONJ_COMM] (UNDISCH_ALL (SPEC_ALL th))));

val tail_step_tac =
  (irule tail_step ORELSE irule (swap_concl tail_step)) >> simp tail_ss;

val tail_last_tac =
  (irule tail_last ORELSE irule (swap_concl tail_last)) >> simp tail_ss;

(* The encoder after unwrap_value, from a message pointer p whose length
   word len rounds up within the tuple buffer M and whose rounded footprint
   is below the frontier: every step is below the frontier and the run ends
   at its REVERT.  The size word's ALLOCA is fresh, or a site apart from the
   tuple's first word. *)
Theorem reason_tail_run_mem:
  !j u v op s p len M B TP.
    v + 2 < u /\
    (!x. op = Var x ==> !k. x <> "%" ++ toString (u + k)) /\
    eval_operand op s = SOME (n2w p) /\
    lookup_var ("%" ++ toString v) s = SOME (n2w B) /\
    lookup_var ("%" ++ toString (v + 1)) s = SOME (n2w (B + 32)) /\
    lookup_var ("%" ++ toString (v + 2)) s = SOME (n2w TP) /\
    mload p s = n2w len /\
    32 + ((len + 31) DIV 32) * 32 <= M /\
    p + 32 + ((len + 31) DIV 32) * 32 <= s.vs_alloca_next /\
    B + 64 + M <= s.vs_alloca_next /\ TP + M <= s.vs_alloca_next /\
    s.vs_alloca_next < dimword (:256) /\
    (FLOOKUP s.vs_allocas (j + 5) = NONE ==>
     s.vs_alloca_next + 32 < dimword (:256)) /\
    (!z n. FLOOKUP s.vs_allocas (j + 5) = SOME (z, n) ==>
           z + 32 <= s.vs_alloca_next /\ (z + 32 <= TP \/ TP + 32 <= z)) ==>
    run_inst_seq_mem_ok (reason_tail j u v op) s /\
    ?t. run_inst_seq (reason_tail j u v op) s = Abort Revert_abort t
Proof
  rpt gen_tac >> strip_tac >>
  `len <= (len + 31) DIV 32 * 32 /\ (len + 31) DIV 32 * 32 <= len + 31` by
    (qspec_then `32` mp_tac DIVISION >> impl_tac >- simp[] >>
     disch_then (qspec_then `len + 31` strip_assume_tac) >> decide_tac) >>
  `len + 31 < dimword (:256) /\ (len + 31) DIV 32 * 32 < dimword (:256)` by
    decide_tac >>
  `word_and (n2w (len + 31) : bytes32)
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w =
   n2w ((len + 31) DIV 32 * 32)` by
    (drule w2n_round32 >> simp[word_add_n2w] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  qabbrev_tac `r = (len + 31) DIV 32 * 32` >>
  `word_and
     0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w
     (n2w (len + 31) : bytes32) = n2w r` by
    metis_tac[WORD_AND_COMM] >>
  `!n w s'. u <= n ==>
     eval_operand op (update_var (STRING #"%" (toString n)) w s') =
     eval_operand op s'` by
    (rpt strip_tac >> Cases_on `op` >>
     simp[eval_operand_def, lookup_var_update_var] >>
     rename1 `Var x` >> first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
     disch_then (qspec_then `n - u` mp_tac) >> simp[]) >>
  `p < dimword (:256) /\ B + 96 + r < dimword (:256) /\
   TP + 32 + r < dimword (:256)` by decide_tac >>
  fs[] >>
  Cases_on `FLOOKUP s.vs_allocas (j + 5)`
  >- (qpat_x_assum `NONE = NONE ==> _` mp_tac >> simp_tac std_ss [] >>
    strip_tac >>
    simp_tac std_ss [reason_tail_def, LET_THM] >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_last_tac) >>
  PairCases_on `x` >>
  qpat_x_assum `!z n. SOME _ = SOME _ ==> _`
    (qspecl_then [`x0`, `x1`] mp_tac) >>
  simp_tac std_ss [] >> disch_then (CONJUNCTS_THEN assume_tac) >>
  `!w s'. mload TP (mstore x0 w s') = mload TP s'` by
    (rpt gen_tac >> irule mload_mstore_apart >> asm_rewrite_tac[]) >>
  simp_tac std_ss [reason_tail_def, LET_THM] >>
  tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
    tail_step_tac >>
  tail_last_tac
QED
