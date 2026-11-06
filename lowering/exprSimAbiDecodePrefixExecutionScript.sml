Theory exprSimAbiDecodePrefixExecution
Ancestors
  exprSimAbiDecodePrefixLayout exprSimAbiDecodeNormalReach
  exprSimAbiDecodeRealizeEntry venomExecSemantics venomState venomInst
  fragGasPath fragExec list arithmetic

(* Each element is the state before the correspondingly numbered instruction.
   The default branch is irrelevant: the checked steps through index 10 are OK. *)
Definition abi_decode_realize_prefix_state_def:
  abi_decode_realize_prefix_state entry 0 = abi_decode_realize_entry_state entry /\
  abi_decode_realize_prefix_state entry (SUC n) =
    (case step_inst 0 ARB
       (EL n (abi_decode_realize_prelude_code 32 0 entry))
       (abi_decode_realize_prefix_state entry n) of
       OK t => t with vs_inst_idx := SUC n
     | _ => abi_decode_realize_prefix_state entry n)
End

Theorem abi_decode_realize_prefix_state_cursor:
  j < 12 ==>
  (abi_decode_realize_prefix_state entry j).vs_current_bb = entry /\
  (abi_decode_realize_prefix_state entry j).vs_inst_idx = j
Proof
  strip_tac >>
  `j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/
   j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11` by decide_tac >>
  gvs[] >>
  EVAL_TAC >> simp[]
QED

Theorem abi_decode_realize_prefix_step:
  j < 11 ==>
  (case step_inst fuel ctx
      (EL j (abi_decode_realize_prelude_code 32 0 entry))
      (abi_decode_realize_prefix_state entry j) of
     OK t => t with vs_inst_idx := SUC j
   | _ => abi_decode_realize_prefix_state entry j) =
  abi_decode_realize_prefix_state entry (SUC j)
Proof
  strip_tac >>
  `j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/
   j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10` by decide_tac >>
  gvs[] >> EVAL_TAC >> simp[]
QED

Theorem abi_decode_realize_prefix_assert:
  step_inst fuel ctx
    (EL 11 (abi_decode_realize_prelude_code 32 0 entry))
    (abi_decode_realize_prefix_state entry 11) <> OK t
Proof
  EVAL_TAC >>
  simp[wordsTheory.WORD_ADD_0, wordsTheory.w2n_n2w,
       wordsTheory.dimword_def] >>
  EVAL_TAC >> simp[]
QED

Theorem abi_decode_realize_prefix_nonterm:
  j < 12 ==>
  ~is_terminator (EL j (abi_decode_realize_prelude_code 32 0 entry)).inst_opcode
Proof
  strip_tac >>
  `j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/
   j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11` by decide_tac >>
  gvs[] >> EVAL_TAC
QED

Theorem abi_decode_realize_prefix_edge:
  j < 12 /\
  lookup_block entry fn.fn_blocks = SOME bb /\
  isPREFIX (abi_decode_realize_prelude_code 32 0 entry) bb.bb_instructions /\
  gas_path_edge ctx fn (abi_decode_realize_prefix_state entry j) n (OK t) ==>
  j < 11 /\ t = abi_decode_realize_prefix_state entry (SUC j)
Proof
  strip_tac >>
  drule abi_decode_realize_prefix_state_cursor >> strip_tac >>
  drule abi_decode_realize_prefix_nonterm >> strip_tac >>
  `get_instruction bb j = SOME (EL j (abi_decode_realize_prelude_code 32 0 entry))` by
    (gvs[rich_listTheory.IS_PREFIX_APPEND, get_instruction_def,
         listTheory.EL_APPEND_EQN]) >>
  reverse (gvs[gas_path_edge_def, exit_result_def])
  >- metis_tac[exit_result_def] >>
  Cases_on `j = 11`
  >- (gvs[] >> metis_tac[abi_decode_realize_prefix_assert]) >>
  `j < 11` by decide_tac >> simp[] >>
  drule abi_decode_realize_prefix_step >>
  disch_then (qspecl_then [`fuel`, `entry`, `ctx`] mp_tac) >>
  simp[]
QED

Definition abi_decode_realize_prefix_states_def:
  abi_decode_realize_prefix_states entry =
    GENLIST (abi_decode_realize_prefix_state entry) 12
End

Theorem abi_decode_realize_prefix_member:
  MEM s (abi_decode_realize_prefix_states entry) <=>
  ?j. j < 12 /\ s = abi_decode_realize_prefix_state entry j
Proof
  pure_rewrite_tac[abi_decode_realize_prefix_states_def, MEM_GENLIST] >> metis_tac[]
QED

Theorem abi_decode_realize_prefix_closed:
  lookup_block entry fn.fn_blocks = SOME bb /\
  isPREFIX (abi_decode_realize_prelude_code 32 0 entry) bb.bb_instructions ==>
  !s n t. MEM s (abi_decode_realize_prefix_states entry) /\
    gas_path_edge ctx fn s n (OK t) ==>
    MEM t (abi_decode_realize_prefix_states entry)
Proof
  simp[abi_decode_realize_prefix_member] >> rpt strip_tac >> gvs[] >>
  drule_all abi_decode_realize_prefix_edge >> strip_tac >>
  qexists_tac `SUC j` >> simp[]
QED

Theorem abi_decode_realize_prefix_no_final:
  0 < k /\ MEM t (abi_decode_realize_prefix_states entry) ==>
  ~(t.vs_current_bb = (abi_decode_realize_final ce k entry).cs_current_bb /\
    t.vs_inst_idx = LENGTH (abi_decode_realize_final ce k entry).cs_current_insts)
Proof
  simp[abi_decode_realize_prefix_member] >> rpt strip_tac >> gvs[] >>
  drule abi_decode_realize_prefix_state_cursor >>
  disch_then (qspec_then `entry` strip_assume_tac) >> gvs[] >>
  metis_tac[abi_decode_realize_final_beyond_guard]
QED

Theorem abi_decode_realize_prefix_entry_member:
  MEM (abi_decode_realize_entry_state entry) (abi_decode_realize_prefix_states entry)
Proof
  rewrite_tac[abi_decode_realize_prefix_member] >>
  qexists_tac `0` >> simp[abi_decode_realize_prefix_state_def]
QED

Theorem abi_decode_realize_prefix_excludes_normal:
  0 < k /\ lookup_block entry fn.fn_blocks = SOME bb /\
  isPREFIX (abi_decode_realize_prelude_code 32 0 entry) bb.bb_instructions ==>
  ~(?n t. gas_path ctx fn (abi_decode_realize_entry_state entry) n (OK t) /\
    t.vs_current_bb = (abi_decode_realize_final ce k entry).cs_current_bb /\
    t.vs_inst_idx = LENGTH (abi_decode_realize_final ce k entry).cs_current_insts)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST
    [`P` |-> `\t. MEM t (abi_decode_realize_prefix_states entry)`]
    abi_decode_normal_path_exclusion) >>
  simp[abi_decode_realize_prefix_entry_member] >>
  conj_tac
  >- metis_tac[abi_decode_realize_prefix_closed] >>
  metis_tac[abi_decode_realize_prefix_no_final]
QED

Theorem abi_decode_realize_overflow_prelude:
  abi_decode_realize_prelude_code 32 (64 + 32 * (2 ** 251 - 2)) entry =
  abi_decode_realize_prelude_code 32 0 entry
Proof
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  `(n2w (64 + 32 * (2 ** 251 - 2)) :256 word) = 0w` by
    simp[wordsTheory.n2w_11, wordsTheory.dimword_def] >>
  simp[abi_decode_realize_prelude_code]
QED

Theorem abi_decode_realize_overflow_no_normal:
  ~(?n t. gas_path ctx
      (abi_decode_realize_function ce (2 ** 251 - 2) entry)
      (abi_decode_realize_entry_state entry) n (OK t) /\
    t.vs_current_bb = (abi_decode_realize_final ce (2 ** 251 - 2) entry).cs_current_bb /\
    t.vs_inst_idx = LENGTH (abi_decode_realize_final ce (2 ** 251 - 2) entry).cs_current_insts)
Proof
  `0 < 2 ** 251 - 2` by EVAL_TAC >>
  drule abi_decode_realize_function_prelude_prefix >>
  disch_then (qspecl_then [`entry`, `ce`] strip_assume_tac) >>
  metis_tac[abi_decode_realize_overflow_prelude,
            abi_decode_realize_prefix_excludes_normal]
QED
