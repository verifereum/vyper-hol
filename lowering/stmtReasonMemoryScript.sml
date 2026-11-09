(* Counted memory safety of the Error(string) revert encoder
   (compile_revert_with_reason): its code, and its straight-line run from a
   message pointer whose rounded footprint is below the frontier. *)
Theory stmtReasonMemory
Ancestors
  fragExecMem instMemFrontier stmtLowering emitHelper emitHelperProps
  exprLoweringProps context compileEnv loweringStateRelDefs valueEncoding valueEncodingDefs valueEncodingProps
  valueEncodingProofs venomMemDefs venomMemProps venomExecSemantics venomState venomInst
  fragExec fragGasSeqAbort fragGasMode fragGasPathMem gasCount instIdxIndep
  venomInstProofs
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

(* Every opcode of the encoder's head and tail is neither GAS nor INVOKE,
   and REVERT is its only terminator. *)
Theorem reason_encoder_ops:
  !id v M j u op.
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               (is_terminator i.inst_opcode ==> i.inst_opcode = REVERT))
      (reason_head id v M) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               (is_terminator i.inst_opcode ==> i.inst_opcode = REVERT))
      (reason_tail j u v op)
Proof
  simp[reason_head_def, reason_tail_def, is_terminator_def, mk_inst_def]
QED

(* A length within k words rounds up to at most k words. *)
Theorem round_le_of_le_mult:
  !L k. L <= 32 * k ==> (L + 31) DIV 32 <= k
Proof
  rpt strip_tac >>
  `(L + 31) DIV 32 <= (k * 32 + 31) DIV 32` by
    (irule DIV_LE_MONOTONE >> simp[]) >>
  `(k * 32 + 31) DIV 32 = k` by
    simp[ADD_DIV_ADD_DIV] >>
  fs[]
QED

(* Straight-line code keeps the data section and the labels. *)
Theorem run_inst_seq_data_section:
  !code s t.
    run_inst_seq code s = OK t /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code ==>
    t.vs_data_section = s.vs_data_section /\ t.vs_labels = s.vs_labels
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[] >> rpt strip_tac >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  drule_all step_preserves_data_section >>
  drule_all step_preserves_labels >> first_x_assum drule_all >>
  simp[]
QED


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

Theorem dload_mk_inst_other:
  !id op ops outs s.
    op <> DLOAD /\ op <> DLOADBYTES ==>
    inst_dload_in_section (mk_inst id op ops outs) s
Proof
  simp[inst_dload_in_section_def, mk_inst_def]
QED

Theorem step_add_eq:
  step_inst_base (mk_inst id ADD [a; b] [out]) s =
    case (eval_operand a s, eval_operand b s) of
      (SOME x, SOME y) => OK (update_var out (x + y) s)
    | _ => Error "undefined operand"
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def]
QED

Theorem step_and_eq:
  step_inst_base (mk_inst id AND [a; b] [out]) s =
    case (eval_operand a s, eval_operand b s) of
      (SOME x, SOME y) => OK (update_var out (word_and x y) s)
    | _ => Error "undefined operand"
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def]
QED

Theorem step_mload_eq:
  step_inst_base (mk_inst id MLOAD [a] [out]) s =
    case eval_operand a s of
      SOME x => OK (update_var out (mload (w2n x) s) s)
    | NONE => Error "undefined operand"
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def]
QED

Theorem step_mstore_eq:
  step_inst_base (mk_inst id MSTORE [a; b] []) s =
    case (eval_operand a s, eval_operand b s) of
      (SOME x, SOME y) => OK (mstore (w2n x) y s)
    | _ => Error "undefined operand"
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def]
QED

Theorem step_mcopy_eq:
  step_inst_base (mk_inst id MCOPY [a; b; c] []) s =
    case (eval_operand a s, eval_operand b s, eval_operand c s) of
      (SOME d, SOME x, SOME n) => OK (mcopy (w2n d) (w2n x) (w2n n) s)
    | _ => Error "undefined operand"
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def]
QED

Theorem step_alloca_eq:
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

Theorem step_revert_eq:
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

Theorem mload_mstore_apart:
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

val head_ss =
  [reason_head_def, run_inst_seq_def, run_inst_seq_mem_ok_def,
   step_alloca_eq, step_mstore_eq, step_add_eq,
   below_frontier_MSTORE, below_frontier_no_ranges, dload_mk_inst_other,
   eval_operand_def, lookup_var_update_var, FLOOKUP_UPDATE, word_add_n2w,
   mload_mstore_apart, LESS_MOD];

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

Theorem head_fields[local,simp]:
  (update_var x w s).vs_current_bb = s.vs_current_bb /\
  (update_var x w s).vs_inst_idx = s.vs_inst_idx /\
  (update_var x w s).vs_halted = s.vs_halted /\
  (mstore a w s).vs_current_bb = s.vs_current_bb /\
  (mstore a w s).vs_inst_idx = s.vs_inst_idx /\
  (mstore a w s).vs_halted = s.vs_halted /\
  lookup_var x (mstore a w s) = lookup_var x s
Proof
  simp[update_var_def, mstore_def, lookup_var_def,
       write_memory_with_expansion_def]
QED

Theorem room_by_fields:
  !ctx func ss. alloca_room ctx func ss ==>
    !ss'. ss'.vs_allocas = ss.vs_allocas /\
          ss'.vs_alloca_next = ss.vs_alloca_next ==> alloca_room ctx func ss'
Proof
  metis_tac[alloca_room_fields]
QED

Theorem head_state_eqs[local,simp]:
  (update_var x w s).vs_allocas = s.vs_allocas /\
  (update_var x w s).vs_alloca_next = s.vs_alloca_next /\
  (mstore a w s).vs_allocas = s.vs_allocas /\
  (mstore a w s).vs_alloca_next = s.vs_alloca_next /\
  mload b (update_var x w s) = mload b s /\
  mload b (s with <| vs_allocas := A; vs_alloca_next := N |>) = mload b s /\
  lookup_var x (s with <| vs_allocas := A; vs_alloca_next := N |>) =
    lookup_var x s
Proof
  simp[update_var_def, mstore_def, mload_def, lookup_var_def]
QED

(* One ALLOCA of a site of the function: it hands out a fresh region at
   the frontier, or the region the site already holds. *)
Theorem alloca_step_props:
  !ctx func id n out s.
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\ alloca_room ctx func s /\
    (!b m. FLOOKUP s.vs_allocas id = SOME (b, m) ==>
           m = n /\ b + m <= s.vs_alloca_next) ==>
    ?B A N.
      step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s =
        OK (update_var out (n2w B)
              (s with <| vs_allocas := A; vs_alloca_next := N |>)) /\
      FLOOKUP A id = SOME (B, n) /\
      (!a. a <> id ==> FLOOKUP A a = FLOOKUP s.vs_allocas a) /\
      B + n <= N /\ s.vs_alloca_next <= N /\
      (FLOOKUP s.vs_allocas id = NONE ==> B = s.vs_alloca_next) /\
      (!x. FLOOKUP s.vs_allocas id = SOME x ==> B = FST x) /\
      alloca_room ctx func (s with <| vs_allocas := A; vs_alloca_next := N |>)
Proof
  rpt strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (qspecl_then [`func`, `s`, `mk_inst id ALLOCA [Lit (n2w n)] [out]`,
                   `n2w n`, `ctx`] mp_tac alloca_room_fresh >>
      impl_tac >- fs[mk_inst_def, FLOOKUP_DEF] >>
      disch_then (strip_assume_tac o
        SIMP_RULE (srw_ss()) [mk_inst_def, LESS_MOD,
                              ASSUME ``n < dimword (:256)``]) >>
      qexistsl [`s.vs_alloca_next`,
                `s.vs_allocas |+ (id, (s.vs_alloca_next, n))`,
                `s.vs_alloca_next + n`] >>
      simp[step_alloca_eq, FLOOKUP_UPDATE, LESS_MOD]) >>
  PairCases_on `x` >>
  `x1 = n /\ x0 + x1 <= s.vs_alloca_next` by metis_tac[] >>
  qexistsl [`x0`, `s.vs_allocas`, `s.vs_alloca_next`] >>
  `s with <| vs_allocas := s.vs_allocas;
             vs_alloca_next := s.vs_alloca_next |> = s` by
    simp[venom_state_component_equality] >>
  simp[step_alloca_eq]
QED

(* The encoder's head: the Error(string) buffer and its selector, the
   payload pointer, and the tuple buffer.  Each ALLOCA hands out a fresh
   region at the frontier or the region its site already holds, of the
   size the site asks for. *)
Theorem reason_head_run_mem:
  !ctx func id v M s.
    MEM (mk_inst id ALLOCA [Lit (n2w (64 + M))] ["%" ++ toString v])
      (fn_insts func) /\
    MEM (mk_inst (id + 3) ALLOCA [Lit (n2w M)] ["%" ++ toString (v + 2)])
      (fn_insts func) /\
    64 + M < dimword (:256) /\
    alloca_room ctx func s /\ alloca_next_valid s /\
    (* Stated through SND: as an assumption, a bare `n = _` conclusion
       would rewrite every number. *)
    (!x. FLOOKUP s.vs_allocas id = SOME x ==> SND x = 64 + M) /\
    (!x. FLOOKUP s.vs_allocas (id + 3) = SOME x ==> SND x = M) ==>
    ?B TP.
      run_inst_seq_mem_ok (reason_head id v M) s /\
      ?s1. run_inst_seq (reason_head id v M) s = OK s1 /\
      lookup_var ("%" ++ toString v) s1 = SOME (n2w B) /\
      lookup_var ("%" ++ toString (v + 1)) s1 = SOME (n2w (B + 32)) /\
      lookup_var ("%" ++ toString (v + 2)) s1 = SOME (n2w TP) /\
      (!x. x <> "%" ++ toString v /\ x <> "%" ++ toString (v + 1) /\
           x <> "%" ++ toString (v + 2) ==>
           lookup_var x s1 = lookup_var x s) /\
      FLOOKUP s1.vs_allocas id = SOME (B, 64 + M) /\
      FLOOKUP s1.vs_allocas (id + 3) = SOME (TP, M) /\
      (!a. a <> id /\ a <> id + 3 ==>
           FLOOKUP s1.vs_allocas a = FLOOKUP s.vs_allocas a) /\
      (FLOOKUP s.vs_allocas id = NONE ==> B = s.vs_alloca_next) /\
      (FLOOKUP s.vs_allocas (id + 3) = NONE ==> s.vs_alloca_next <= TP) /\
      B + 64 + M <= s1.vs_alloca_next /\ TP + M <= s1.vs_alloca_next /\
      s.vs_alloca_next <= s1.vs_alloca_next /\
      alloca_room ctx func s1 /\
      (!a. a + 32 <= B \/ B + 32 <= a ==> mload a s1 = mload a s) /\
      s1.vs_current_bb = s.vs_current_bb /\
      s1.vs_inst_idx = s.vs_inst_idx /\
      s1.vs_halted = s.vs_halted /\
      (!x. FLOOKUP s.vs_allocas id = SOME x ==> B = FST x) /\
      (!x. FLOOKUP s.vs_allocas (id + 3) = SOME x ==> TP = FST x)
Proof
  rpt gen_tac >> strip_tac >>
  `M < dimword (:256)` by decide_tac >>
  qspecl_then [`ctx`, `func`, `id`, `64 + M`, `"%" ++ toString v`, `s`]
    mp_tac alloca_step_props >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
               rpt strip_tac >> metis_tac[alloca_next_valid_def, pairTheory.SND]) >>
  strip_tac >>
  `(s with <| vs_allocas := A; vs_alloca_next := N |>).vs_alloca_next <
   dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  pop_assum (assume_tac o
    SIMP_RULE std_ss [venom_state_accfupds, combinTheory.K_THM]) >>
  `B < dimword (:256)` by decide_tac >>
  qabbrev_tac `sa0 = s with <| vs_allocas := A; vs_alloca_next := N |>` >>
  `sa0.vs_allocas = A /\ sa0.vs_alloca_next = N` by simp[Abbr `sa0`] >>
  qabbrev_tac `sd = update_var ("%" ++ toString (v + 1)) (n2w (B + 32))
                      (mstore B 0x08c379a0w
                        (update_var ("%" ++ toString v) (n2w B) sa0))` >>
  `sd.vs_allocas = A /\ sd.vs_alloca_next = N` by simp[Abbr `sd`] >>
  `alloca_room ctx func sd` by
    (irule room_by_fields >> qexists `sa0` >> simp[]) >>
  `id + 3 <> id /\ B + 32 <= N` by decide_tac >>
  `FLOOKUP A (id + 3) = FLOOKUP s.vs_allocas (id + 3)` by metis_tac[] >>
  `w2n (n2w B : bytes32) = B` by metis_tac[w2n_n2w, LESS_MOD] >>
  `step_inst_base (mk_inst (id + 1) MSTORE
      [Var ("%" ++ toString v); Lit (0x08c379a0w : bytes32)] [])
      (update_var ("%" ++ toString v) (n2w B) sa0) =
   OK (mstore B 0x08c379a0w (update_var ("%" ++ toString v) (n2w B) sa0))` by
    asm_simp_tac (srw_ss())
      [step_mstore_eq, eval_operand_def, lookup_var_update_var, LESS_MOD] >>
  `step_inst_base (mk_inst (id + 2) ADD [Var ("%" ++ toString v); Lit 32w]
      ["%" ++ toString (v + 1)])
      (mstore B 0x08c379a0w (update_var ("%" ++ toString v) (n2w B) sa0)) =
   OK sd` by
    (qunabbrev_tac `sd` >>
     asm_simp_tac (srw_ss())
       [step_add_eq, eval_operand_def, lookup_var_update_var, word_add_n2w]) >>
  qspecl_then [`ctx`, `func`, `id + 3`, `M`, `"%" ++ toString (v + 2)`, `sd`]
    mp_tac alloca_step_props >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      `FLOOKUP s.vs_allocas (id + 3) = SOME (b, m)` by metis_tac[] >>
      `m = M /\ b + m <= s.vs_alloca_next` by
        metis_tac[alloca_next_valid_def, pairTheory.SND] >>
      decide_tac) >>
  disch_then (qx_choosel_then [`TP`, `A2`, `N2`] strip_assume_tac) >>
  qabbrev_tac `sb0 = sd with <| vs_allocas := A2; vs_alloca_next := N2 |>` >>
  `sb0.vs_allocas = A2 /\ sb0.vs_alloca_next = N2` by
    (qunabbrev_tac `sb0` >> simp_tac (srw_ss()) []) >>
  `N <= N2` by metis_tac[] >>
  `run_inst_seq_mem_ok (reason_head id v M) s /\
   run_inst_seq (reason_head id v M) s =
     OK (update_var ("%" ++ toString (v + 2)) (n2w TP) sb0)` by
    (simp_tac std_ss [reason_head_def, run_inst_seq_def,
                      run_inst_seq_mem_ok_def] >>
     asm_simp_tac (std_ss ++ simpLib.type_ssfrag ``:exec_result``) [] >>
     asm_simp_tac (srw_ss())
       [below_frontier_MSTORE, below_frontier_no_ranges,
        dload_mk_inst_other, eval_operand_def, lookup_var_update_var,
        LESS_MOD]) >>
  `"%" ++ toString v <> "%" ++ toString (v + 1) /\
   "%" ++ toString v <> "%" ++ toString (v + 2) /\
   "%" ++ toString (v + 1) <> "%" ++ toString (v + 2)` by
    simp_tac (srw_ss() ++ ARITH_ss) [ASCIInumbersTheory.toString_11] >>
  qexistsl [`B`, `TP`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `update_var ("%" ++ toString (v + 2)) (n2w TP) sb0` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt conj_tac
  >- (qunabbrev_tac `sb0` >> qunabbrev_tac `sd` >>
      asm_simp_tac (srw_ss()) [lookup_var_update_var])
  >- (qunabbrev_tac `sb0` >> qunabbrev_tac `sd` >>
      asm_simp_tac (srw_ss()) [lookup_var_update_var])
  >- asm_simp_tac (srw_ss()) [lookup_var_update_var]
  >- (rpt strip_tac >>
      qunabbrev_tac `sb0` >> qunabbrev_tac `sd` >> qunabbrev_tac `sa0` >>
      asm_simp_tac (srw_ss()) [lookup_var_update_var])
  >- asm_simp_tac (srw_ss()) []
  >- asm_simp_tac (srw_ss()) []
  >- (rpt strip_tac >> asm_simp_tac (srw_ss()) [])
  >- first_assum ACCEPT_TAC
  >- (strip_tac >> `TP = N` by metis_tac[] >> decide_tac)
  >- (asm_simp_tac (srw_ss()) [] >> decide_tac)
  >- (asm_simp_tac (srw_ss()) [] >> decide_tac)
  >- (asm_simp_tac (srw_ss()) [] >> decide_tac)
  >- (irule room_by_fields >> qexists `sb0` >> asm_simp_tac (srw_ss()) [])
  >- (rpt gen_tac >> disch_tac >>
      `B + 32 <= a \/ a + 32 <= B` by metis_tac[DISJ_COMM] >>
      qunabbrev_tac `sb0` >> qunabbrev_tac `sd` >> qunabbrev_tac `sa0` >>
      asm_simp_tac (srw_ss()) [mload_mstore_apart]) >>
  (first_assum ACCEPT_TAC ORELSE
   (qunabbrev_tac `sb0` >> qunabbrev_tac `sd` >> qunabbrev_tac `sa0` >>
    simp_tac (srw_ss()) [] >> NO_TAC) ORELSE
   metis_tac[])
QED

(* ===== Straight-line code ending at a REVERT ===== *)

Theorem step_revert_not_ok[local]:
  !i s u. i.inst_opcode = REVERT ==> step_inst_base i s <> OK u
Proof
  rpt strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs] >> BasicProvers.every_case_tac >> simp[]
QED

Theorem step_revert_idx[local]:
  !i s n. i.inst_opcode = REVERT ==>
    step_inst_base i (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n) (step_inst_base i s)
Proof
  rpt strip_tac >> simp[step_inst_base_opcode_eqs, eval_op_inst_idx] >>
  BasicProvers.every_case_tac >>
  simp[exec_result_map_def, revert_state_def, set_returndata_def,
       venom_state_component_equality]
QED

Theorem step_idx_revert[local]:
  !i. (~is_terminator i.inst_opcode \/ i.inst_opcode = REVERT) ==>
    !s n. step_inst_base i (s with vs_inst_idx := n) =
          exec_result_map (\s'. s' with vs_inst_idx := n) (step_inst_base i s)
Proof
  metis_tac[step_inst_inst_idx_indep, step_revert_idx]
QED

Theorem run_idx_revert[local]:
  !is s n.
    EVERY (\i. is_terminator i.inst_opcode ==> i.inst_opcode = REVERT) is ==>
    run_inst_seq is (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n) (run_inst_seq is s)
Proof
  Induct >> rw[run_inst_seq_def, exec_result_map_def] >>
  qspec_then `h` mp_tac step_idx_revert >>
  impl_tac >- metis_tac[] >>
  disch_then (fn th => simp[th]) >>
  Cases_on `step_inst_base h s` >> gvs[exec_result_map_def]
QED

Theorem mem_ok_idx_revert[local]:
  !is s n.
    EVERY (\i. is_terminator i.inst_opcode ==> i.inst_opcode = REVERT) is ==>
    (run_inst_seq_mem_ok is (s with vs_inst_idx := n) <=>
     run_inst_seq_mem_ok is s)
Proof
  Induct >> rw[run_inst_seq_mem_ok_def] >>
  qspec_then `h` mp_tac step_idx_revert >>
  impl_tac >- metis_tac[] >>
  disch_then (fn th => simp[th]) >>
  Cases_on `step_inst_base h s` >> gvs[exec_result_map_def]
QED

Theorem gas_mem_path_abort_any[local]:
  !ctx func s bb i a t.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
    inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
    step_inst_base i s = Abort a t ==>
    gas_marked_path T ctx func s 0 (Abort a t)
Proof
  rpt strip_tac >> simp[gas_marked_path_def] >>
  irule (cj 3 gas_path_mem_rules) >> simp[exit_result_def] >>
  `step_inst 0 ctx i s = Abort a t` by simp[step_inst_non_invoke] >>
  simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
  simp[gas_count_step_def, mem_safe_step_non_invoke, exit_result_def]
QED

(* Straight-line code that ends by aborting, REVERTs allowed among its
   instructions: a memory-safe path with no GAS reads. *)
Theorem run_inst_seq_revert_path_mem:
  !code s t a ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               (is_terminator i.inst_opcode ==> i.inst_opcode = REVERT)) code /\
    run_inst_seq_mem_ok code s /\
    run_inst_seq code s = Abort a t ==>
    ?j. gas_marked_path T ctx func s 0 (Abort a (t with vs_inst_idx := j))
Proof
  Induct_on `code` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, run_inst_seq_mem_ok_def]
  >- (rename1 `step_inst_base h s = OK u` >>
      `~is_terminator h.inst_opcode` by metis_tac[step_revert_not_ok] >>
      `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `EVERY (\i. is_terminator i.inst_opcode ==> i.inst_opcode = REVERT)
         code` by fs[EVERY_MEM] >>
      first_x_assum
        (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      disch_then
        (qspec_then `t with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      simp[run_idx_revert, mem_ok_idx_revert, exec_result_map_def] >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
      simp[] >> strip_tac >> qexists_tac `j` >>
      drule_at (Pat `step_inst_base _ _ = OK _`) gas_marked_path_step >>
      simp[] >> disch_then irule >> metis_tac[]) >>
  qexists_tac `t.vs_inst_idx` >> simp[] >>
  irule gas_mem_path_abort_any >> metis_tac[]
QED

(* ===== The encoder run, from a message pointer ===== *)

(* The encoder with no unwrap code between head and tail, from a message
   pointer op whose length word and rounded payload lie below the
   frontier, apart from the selector word of a held Error buffer. *)
Theorem reason_encoder_run_mem:
  !ctx func id v op s p len M.
    MEM (mk_inst id ALLOCA [Lit (n2w (64 + M))] ["%" ++ toString v])
      (fn_insts func) /\
    MEM (mk_inst (id + 3) ALLOCA [Lit (n2w M)] ["%" ++ toString (v + 2)])
      (fn_insts func) /\
    MEM (mk_inst (id + 4 + 5) ALLOCA [Lit 32w] ["%" ++ toString (v + 3 + 4)])
      (fn_insts func) /\
    64 + M < dimword (:256) /\
    alloca_room ctx func s /\ alloca_next_valid s /\
    (!x. FLOOKUP s.vs_allocas id = SOME x ==>
         SND x = 64 + M /\ (p + 32 <= FST x \/ FST x + 32 <= p)) /\
    (!x. FLOOKUP s.vs_allocas (id + 3) = SOME x ==> SND x = M) /\
    (!x. FLOOKUP s.vs_allocas (id + 4 + 5) = SOME x ==>
         SND x = 32 /\
         !y. FLOOKUP s.vs_allocas (id + 3) = SOME y ==>
             FST x + 32 <= FST y \/ FST y + 32 <= FST x) /\
    (!x. op = Var x ==> !k. x <> "%" ++ toString (v + k)) /\
    (!l. op <> Label l) /\
    eval_operand op s = SOME (n2w p) /\ mload p s = n2w len /\
    32 + ((len + 31) DIV 32) * 32 <= M /\
    p + 32 + ((len + 31) DIV 32) * 32 <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok
      (reason_head id v M ++ reason_tail (id + 4) (v + 3) v op) s /\
    ?t. run_inst_seq
          (reason_head id v M ++ reason_tail (id + 4) (v + 3) v op) s =
        Abort Revert_abort t
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ctx`, `func`, `id`, `v`, `M`, `s`] mp_tac reason_head_run_mem >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  disch_then (qx_choosel_then [`B`, `TP`] strip_assume_tac) >>
  `s1.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `!x. op = Var x ==>
       x <> "%" ++ toString v /\ x <> "%" ++ toString (v + 1) /\
       x <> "%" ++ toString (v + 2)` by
    (rpt gen_tac >> strip_tac >>
     `!k. x <> "%" ++ toString (v + k)` by metis_tac[] >>
     rpt conj_tac >| [
       first_x_assum (qspec_then `0` mp_tac),
       first_x_assum (qspec_then `1` mp_tac),
       first_x_assum (qspec_then `2` mp_tac)] >>
     simp_tac std_ss [ADD_CLAUSES]) >>
  `eval_operand op s1 = SOME (n2w p)` by
    (Cases_on `op` >> fs[] >> qpat_x_assum `eval_operand _ s = _` mp_tac >>
     simp_tac (srw_ss()) [eval_operand_def] >>
     TRY (strip_tac >> metis_tac[])) >>
  `mload p s1 = n2w len` by
    (`p + 32 <= B \/ B + 32 <= p` by
       (Cases_on `FLOOKUP s.vs_allocas id`
        >- (`B = s.vs_alloca_next` by metis_tac[] >> decide_tac) >>
        `B = FST x` by metis_tac[] >> metis_tac[]) >>
     metis_tac[]) >>
  qspecl_then [`id + 4`, `v + 3`, `v`, `op`, `s1`, `p`, `len`, `M`, `B`, `TP`]
    mp_tac reason_tail_run_mem >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >|
      [(* the message operand is not a tail variable *)
       metis_tac[ADD_ASSOC],
       (* a fresh length word fits *)
       strip_tac >>
       qspecl_then [`func`, `s1`,
         `mk_inst (id + 4 + 5) ALLOCA [Lit 32w] ["%" ++ toString (v + 3 + 4)]`,
         `32w`, `ctx`] mp_tac alloca_room_fresh >>
       impl_tac
       >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
           TRY (simp_tac (srw_ss()) [mk_inst_def] >> NO_TAC) >>
           qpat_x_assum `FLOOKUP s1.vs_allocas _ = NONE` mp_tac >>
           simp_tac (srw_ss()) [mk_inst_def, FLOOKUP_DEF]) >>
       disch_then (mp_tac o CONJUNCT1) >> simp_tac (srw_ss()) [],
       (* a held length word lies below the frontier, apart from the
          tuple buffer *)
       rpt gen_tac >> strip_tac >>
       `id + 4 + 5 <> id /\ id + 4 + 5 <> id + 3` by decide_tac >>
       `FLOOKUP s.vs_allocas (id + 4 + 5) = SOME (z, n)` by metis_tac[] >>
       `n = 32 /\ z + n <= s.vs_alloca_next` by
         metis_tac[alloca_next_valid_def, pairTheory.SND] >>
       `z + 32 <= TP \/ TP + 32 <= z` by
         (Cases_on `FLOOKUP s.vs_allocas (id + 3)`
          >- (`s.vs_alloca_next <= TP` by metis_tac[] >> decide_tac) >>
          `TP = FST x` by metis_tac[] >>
          metis_tac[pairTheory.FST]) >>
       conj_tac >> decide_tac]) >>
  strip_tac >>
  conj_tac
  >- (irule run_inst_seq_mem_ok_append >>
      TRY (first_assum ACCEPT_TAC) >> metis_tac[exec_result_11]) >>
  metis_tac[run_inst_seq_append]
QED
