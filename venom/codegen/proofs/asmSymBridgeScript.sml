(*
 * The label-symbolic assembly run against the concrete one
 *
 * asmSymSem runs a program with label values kept symbolic (Lab l d); the
 * codegen simulation runs it concretely (asm_steps), with every label
 * resolved to its byte offset in the assembled code. For a program that
 * meets asm_static_wf, the two runs from the same start state end the
 * same way, in both directions, once the symbolic run uses no label
 * value numerically (label_disciplined).
 *
 * The concrete run's states are related to the symbolic run's by
 * asm_sym_rel: a label value Lab l d is the word n2w (off + d) for l's
 * offset off; memory bytes that hold part of a stored label value are its
 * bytes in the concrete memory and placeholders in the symbolic one; and
 * the data environment is the concrete code from each data header on.
 *
 * TOP-LEVEL:
 *   asm_result_sym      - a concrete result as a symbolic one
 *   asm_data_env_ok     - a data environment matches the concrete code
 *   asm_sym_forward     - a concrete terminal run is a symbolic one
 *   asm_sym_backward    - a symbolic terminal run is a concrete one
 *
 * Helper:
 *   sval_conc, asm_sym_rel, asm_sym_step_rel - values, states and step
 *     results of the two runs against each other
 *)

Theory asmSymBridge
Ancestors
  asmSymSem asmOptimizer asmToBytecodeProofs asmSem asmWf
  symbolResolve spillWordBounds vfmTypes list mem2varBlockSimHelpers spillSim
  asmCallOracleProps asmOpSim

(* ===== Relating the two semantics ===== *)

(* A concrete result as a symbolic one: the state through sym_init, which
   is what sym_obs compares. *)
Definition asm_result_sym_def:
  asm_result_sym (AsmOK s) = SymOK (sym_init s) ∧
  asm_result_sym (AsmHalt s) = SymHalt (sym_init s) ∧
  asm_result_sym (AsmRevert s) = SymRevert (sym_init s) ∧
  asm_result_sym (AsmFault s) = SymFault (sym_init s) ∧
  asm_result_sym (AsmError e) = SymError e
End

(* The data environment is the code from each data header's offset on, for
   every header the symbolic run can read from. *)
Definition asm_data_env_ok_def:
  asm_data_env_ok p (env : string |-> byte list) code ⇔
    ∀l. sym_data_label p env l ⇒
        ∃off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off ∧
              env ' l = DROP off code
End

(* The concrete word of a symbolic value under the label offsets lo. *)
Definition sval_conc_def:
  sval_conc lo (Val w) = SOME w ∧
  sval_conc lo (Lab l d) =
    if sym_delta_ok d then
      OPTION_MAP (λoff. (n2w (off + d) : bytes32)) (FLOOKUP lo l)
    else NONE
End

(* The concrete state cs against the symbolic state ss of program p: the
   same pc and everything else but the stack, memory and code; stacks of
   the same values; memory equal except at label bytes, which hold the
   label's concrete bytes; and env matching the concrete code. *)
Definition asm_sym_rel_def:
  asm_sym_rel p env cs ss ⇔
    LIST_REL (λsv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
      ss.sym_stack cs.as_stack ∧
    (∃m. ss.sym_base = cs with <| as_stack := []; as_code := [];
                                  as_memory := m |> ∧
         LENGTH m = LENGTH cs.as_memory ∧
         ∀i. i < LENGTH cs.as_memory ∧ i ∉ FDOM ss.sym_mem_labels ⇒
             EL i m = EL i cs.as_memory) ∧
    (∀i l d j. FLOOKUP ss.sym_mem_labels i = SOME (l, d, j) ⇒
         i < LENGTH cs.as_memory ∧ j < 32 ∧
         ∃w. sval_conc (SND (compute_label_offsets p)) (Lab l d) = SOME w ∧
             EL i cs.as_memory = EL j (word_to_bytes w T)) ∧
    asm_data_env_ok p env cs.as_code
End

(* One symbolic step's result against the concrete step's. A label misuse
   (SymBad) relates to anything: label_disciplined rules it out. *)
Definition asm_sym_step_rel_def:
  asm_sym_step_rel p env (SymOK ss) r =
    (∃cs. r = AsmOK cs ∧ asm_sym_rel p env cs ss) ∧
  asm_sym_step_rel p env (SymHalt ss) r =
    (∃cs. r = AsmHalt cs ∧ sym_obs ss = sym_obs (sym_init cs)) ∧
  asm_sym_step_rel p env (SymRevert ss) r =
    (∃cs. r = AsmRevert cs ∧ sym_obs ss = sym_obs (sym_init cs)) ∧
  asm_sym_step_rel p env (SymFault ss) r =
    (∃cs. r = AsmFault cs ∧ sym_obs ss = sym_obs (sym_init cs)) ∧
  asm_sym_step_rel p env (SymError _) r = (∃e. r = AsmError e) ∧
  asm_sym_step_rel p env (SymBad _) r = T
End

(* ===== One step: the opcodes sym_step_op hands to asm_step_op ===== *)

Theorem expand_memory_lengths[local]:
  LENGTH m = LENGTH n ==>
  LENGTH (asm_expand_memory k m) = LENGTH (asm_expand_memory k n)
Proof
  strip_tac >> simp[asm_expand_memory_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem expand_memory_grows[local]:
  LENGTH m <= LENGTH (asm_expand_memory k m)
Proof
  simp[asm_expand_memory_def] >> IF_CASES_TAC >> simp[]
QED

Theorem expand_memory_retains[local]:
  i < LENGTH m ==> EL i (asm_expand_memory k m) = EL i m
Proof
  strip_tac >>
  `i < LENGTH (asm_expand_memory k m)` by
    (mp_tac expand_memory_grows >> decide_tac) >>
  simp[el_expand_read_byte]
QED

Theorem expand_memory_agrees[local]:
  LENGTH m = LENGTH n /\
  (!i. i < LENGTH n /\ i NOTIN L ==> EL i m = EL i n) ==>
  !i. i < LENGTH (asm_expand_memory k n) /\ i NOTIN L ==>
    EL i (asm_expand_memory k m) = EL i (asm_expand_memory k n)
Proof
  rpt strip_tac >>
  `i < LENGTH (asm_expand_memory k m)` by metis_tac[expand_memory_lengths] >>
  simp[el_expand_read_byte] >>
  Cases_on `i < LENGTH n` >> simp[]
QED

Theorem expand_memory_read[local]:
  LENGTH m = LENGTH n /\
  (!i. i < LENGTH n /\ i NOTIN L ==> EL i m = EL i n) /\
  (!i. off <= i /\ i < off + sz ==> i NOTIN L) ==>
  TAKE sz (DROP off (asm_expand_memory k m)) =
  TAKE sz (DROP off (asm_expand_memory k n))
Proof
  strip_tac >>
  `LENGTH (asm_expand_memory k m) = LENGTH (asm_expand_memory k n)`
    by (irule expand_memory_lengths >> simp[]) >>
  irule LIST_EQ >>
  reverse conj_tac >- simp[LENGTH_TAKE_EQ, LENGTH_DROP, expand_memory_lengths] >>
  simp[LENGTH_TAKE_EQ, LENGTH_DROP, EL_TAKE, EL_DROP] >> rpt strip_tac >>
  irule expand_memory_agrees >>
  conj_tac
  >- (qexists_tac `L` >> simp[] >> first_x_assum irule >>
      gvs[AllCaseEqs()] >> decide_tac) >>
  gvs[AllCaseEqs()] >> decide_tac
QED

Theorem cleared_labels_lookup[local]:
  FLOOKUP (mem_labels_clear labs P) i =
    if P i then NONE else FLOOKUP labs i
Proof
  Cases_on `P i` >>
  simp[mem_labels_clear_def, finite_mapTheory.FLOOKUP_DRESTRICT]
QED

Theorem splice_memory_agrees[local]:
  LENGTH (m:byte list) = LENGTH n /\
  off + LENGTH bs <= LENGTH n /\
  (!i. i < LENGTH n /\ i NOTIN L ==> EL i m = EL i n) ==>
  !i. i < LENGTH n /\
      i NOTIN (L DIFF {i | in_mem_range off (LENGTH bs) i}) ==>
    EL i (TAKE off m ++ bs ++ DROP (off + LENGTH bs) m) =
    EL i (TAKE off n ++ bs ++ DROP (off + LENGTH bs) n)
Proof
  rpt strip_tac >>
  Cases_on `in_mem_range off (LENGTH bs) i`
  >- (gvs[in_mem_range_def] >>
      simp[mem2varBlockSimHelpersTheory.EL_splice_inside]) >>
  `i < off \/ off + LENGTH bs <= i` by gvs[in_mem_range_def] >>
  simp[EL_splice_outside] >>
  first_x_assum irule >> gvs[]
QED

Theorem cleared_labels_valid[local]:
  LENGTH (old:byte list) <= LENGTH new /\
  (!i. i < LENGTH old /\ ~P i ==> EL i new = EL i old) /\
  (!i l d j. FLOOKUP labs i = SOME (l,d,j) ==>
    i < LENGTH old /\ j < 32 /\
    ?w. sval_conc lo (Lab l d) = SOME w /\
        EL i old = EL j (word_to_bytes w T)) ==>
  !i l d j. FLOOKUP (mem_labels_clear labs P) i = SOME (l,d,j) ==>
    i < LENGTH new /\ j < 32 /\
    ?w. sval_conc lo (Lab l d) = SOME w /\
        EL i new = EL j (word_to_bytes w T)
Proof
  rpt strip_tac >>
  gvs[cleared_labels_lookup, AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >> simp[] >> decide_tac
QED

Theorem concrete_operands[local]:
  !k svs ws args lo.
    LIST_REL (\sv w. sval_conc lo sv = SOME w) svs ws /\
    OPT_MMAP sval_val (TAKE k svs) = SOME args /\ k <= LENGTH svs ==>
    TAKE k ws = args /\
    LIST_REL (\sv w. sval_conc lo sv = SOME w)
      (DROP k svs) (DROP k ws)
Proof
  Induct >- simp[] >>
  Cases_on `svs` >- simp[] >>
  Cases_on `ws` >- simp[] >>
  Cases_on `h` >>
  simp[sval_val_def, sval_conc_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule_all >> simp[]
QED

Theorem concrete_underflow[local]:
  LENGTH s.as_stack < asm_op_arity name ==>
  ?e. asm_step_op otp name s = AsmError e
Proof
  simp[asm_op_arity_def] >>
  Cases_on `ALOOKUP asm_op_arity_table name` >- simp[] >>
  strip_tac >>
  drule alistTheory.ALOOKUP_MEM >>
  simp[asm_op_arity_table_def] >>
  strip_tac >> gvs[] >>
  simp[asm_step_op_def, asm_step_arith_def] >>
  simp[asm_step_compare_def, asm_step_bitwise_def] >>
  simp[asm_step_memory_def, asm_step_control_def] >>
  simp[asm_step_extcall_def, asm_step_copy_def] >>
  simp[asm_step_context_def, dup_table_def, swap_table_def, log_table_def] >>
  simp[asm_binop_def, asm_unop_def, asm_ternop_def, asm_state_unop_def,
       asm_pop_def, asm_mload_def, asm_mstore_def, asm_mstore8_def,
       asm_mcopy_def, asm_sload_def, asm_sstore_def, asm_tload_def,
       asm_tstore_def, asm_sha3_def, asm_jump_def, asm_jumpi_def,
       asm_return_op_def, asm_revert_op_def, asm_exec_call_def,
       asm_exec_staticcall_def, asm_exec_delegatecall_def,
       asm_exec_create_def, asm_exec_create2_def, asm_selfdestruct_def,
       asm_copy_to_mem_def, asm_returndatacopy_def, asm_extcodecopy_def,
       asm_log_def] >>
  Cases_on `s.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED

Theorem related_memory_read[local]:
  asm_sym_rel p env cs ss /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range off sz) ==>
  TAKE sz (DROP off (asm_expand_memory k ss.sym_base.as_memory)) =
  TAKE sz (DROP off (asm_expand_memory k cs.as_memory))
Proof
  rw[asm_sym_rel_def] >> gvs[] >>
  irule expand_memory_read >> simp[] >>
  qexists_tac `FDOM ss.sym_mem_labels` >>
  gvs[mem_labels_hit_def, in_mem_range_def] >> metis_tac[]
QED

Theorem related_call_request[local]:
  asm_sym_rel p env cs ss /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range off sz) ==>
  asm_call_request (ss.sym_base with as_stack := args) addr value off sz st =
  asm_call_request cs addr value off sz st
Proof
  strip_tac >>
  drule_all related_memory_read >>
  disch_then (qspec_then `off + sz` assume_tac) >>
  gvs[asm_sym_rel_def] >>
  simp[asm_call_request_def]
QED

Theorem related_create_request[local]:
  asm_sym_rel p env cs ss /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range off sz) ==>
  asm_create_request (ss.sym_base with as_stack := args) value off sz salt =
  asm_create_request cs value off sz salt
Proof
  strip_tac >>
  drule_all related_memory_read >>
  disch_then (qspec_then `off + sz` assume_tac) >>
  gvs[asm_sym_rel_def] >>
  simp[asm_create_request_def]
QED

Theorem related_delegatecall_state[local]:
  asm_sym_rel p env cs ss ==>
  make_asm_delegatecall_state (ss.sym_base with as_stack := args)
    target gas calldata code st =
  make_asm_delegatecall_state cs target gas calldata code st
Proof
  rw[asm_sym_rel_def] >> gvs[] >>
  simp[make_asm_delegatecall_state_def, asm_to_tx_params_def]
QED

Theorem sym_step_concrete_good[local]:
  asm_sym_rel p env cs ss /\
  (LENGTH cs.as_stack < asm_op_arity name ==>
    ?e. asm_step_op otp name cs = AsmError e) /\
  (!args. args = TAKE (asm_op_arity name) cs.as_stack /\
    asm_op_arity name <= LENGTH cs.as_stack /\
    LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
      (DROP (asm_op_arity name) ss.sym_stack)
      (DROP (asm_op_arity name) cs.as_stack) /\
    ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) ==>
    asm_sym_step_rel p env
      (sym_lift (asm_op_arity name)
        (mem_labels_clear ss.sym_mem_labels (asm_op_mem_writes name args)) ss
        (asm_step_op FEMPTY name (ss.sym_base with as_stack := args)))
      (asm_step_op otp name cs)) ==>
  asm_sym_step_rel p env (sym_step_concrete name ss) (asm_step_op otp name cs)
Proof
  strip_tac >>
  `LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
     ss.sym_stack cs.as_stack` by gvs[asm_sym_rel_def] >>
  `LENGTH ss.sym_stack = LENGTH cs.as_stack` by metis_tac[LIST_REL_LENGTH] >>
  simp[sym_step_concrete_def] >>
  Cases_on `LENGTH ss.sym_stack < asm_op_arity name`
  >- (gvs[asm_sym_step_rel_def] >> metis_tac[]) >>
  simp[] >>
  Cases_on `OPT_MMAP sval_val (TAKE (asm_op_arity name) ss.sym_stack)` >>
  simp[asm_sym_step_rel_def] >>
  rename1 `OPT_MMAP _ _ = SOME args` >>
  Cases_on `mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args)` >>
  simp[asm_sym_step_rel_def] >>
  `asm_op_arity name <= LENGTH ss.sym_stack` by decide_tac >>
  drule_all concrete_operands >>
  strip_tac >> first_x_assum irule >> simp[]
QED

Theorem call_memory_lengths[local]:
  LENGTH m = LENGTH n ==>
  LENGTH (asm_call_memory ao az ro rs m) =
  LENGTH (asm_call_memory ao az ro rs n)
Proof
  strip_tac >> Cases_on `az = 0` >> Cases_on `rs = 0` >>
  simp[asm_call_memory_def, expand_memory_lengths]
QED

Theorem call_memory_retains[local]:
  i < LENGTH m ==> EL i (asm_call_memory ao az ro rs m) = EL i m
Proof
  strip_tac >> Cases_on `az = 0` >> Cases_on `rs = 0` >>
  simp[asm_call_memory_def, expand_memory_retains] >>
  `i < LENGTH (asm_expand_memory (ao + az) m)` by
    metis_tac[expand_memory_grows, arithmeticTheory.LESS_LESS_EQ_TRANS] >>
  simp[expand_memory_retains]
QED

Theorem call_memory_grows[local]:
  LENGTH m <= LENGTH (asm_call_memory ao az ro rs m)
Proof
  Cases_on `az = 0` >> Cases_on `rs = 0` >>
  simp[asm_call_memory_def, expand_memory_grows] >>
  metis_tac[expand_memory_grows, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem call_memory_capacity[local]:
  rs <> 0 ==> ro + rs <= LENGTH (asm_call_memory ao az ro rs m)
Proof
  simp[asm_call_memory_def]
QED

Theorem call_memory_agrees[local]:
  LENGTH m = LENGTH n /\
  (!i. i < LENGTH n /\ i NOTIN L ==> EL i m = EL i n) ==>
  !i. i < LENGTH (asm_call_memory ao az ro rs n) /\ i NOTIN L ==>
    EL i (asm_call_memory ao az ro rs m) =
    EL i (asm_call_memory ao az ro rs n)
Proof
  strip_tac >> Cases_on `az = 0` >> Cases_on `rs = 0` >>
  simp[asm_call_memory_def] >>
  rpt strip_tac >> irule expand_memory_agrees >>
  simp[expand_memory_lengths] >>
  qexists_tac `L` >> simp[] >>
  rpt strip_tac >> irule expand_memory_agrees >> simp[] >>
  qexists_tac `L` >> simp[]
QED

Theorem call_output_length[local]:
  LENGTH bs <= rs ==>
  LENGTH (TAKE ro (asm_call_memory ao az ro rs m) ++ bs ++
    DROP (ro + LENGTH bs) (asm_call_memory ao az ro rs m)) =
  LENGTH (asm_call_memory ao az ro rs m)
Proof
  strip_tac >> Cases_on `rs = 0` >- gvs[LENGTH_TAKE_EQ] >>
  irule (cj 1 overwrite_prefix_length_suffix) >>
  `ro + rs <= LENGTH (asm_call_memory ao az ro rs m)` by
    simp[call_memory_capacity] >> decide_tac
QED

Theorem call_output_agrees[local]:
  LENGTH m = LENGTH n /\ LENGTH bs <= rs /\
  (!i. i < LENGTH n /\ i NOTIN L ==> EL i m = EL i n) ==>
  !i. i < LENGTH (asm_call_memory ao az ro rs n) /\ i NOTIN L ==>
    EL i (TAKE ro (asm_call_memory ao az ro rs m) ++ bs ++
      DROP (ro + LENGTH bs) (asm_call_memory ao az ro rs m)) =
    EL i (TAKE ro (asm_call_memory ao az ro rs n) ++ bs ++
      DROP (ro + LENGTH bs) (asm_call_memory ao az ro rs n))
Proof
  strip_tac >> Cases_on `rs = 0`
  >- (gvs[TAKE_DROP] >> rpt strip_tac >> irule call_memory_agrees >>
      simp[] >> qexists_tac `L` >> simp[]) >>
  rpt strip_tac >> irule splice_memory_agrees >>
  simp[call_memory_lengths] >>
  reverse conj_tac
  >- (`ro + rs <= LENGTH (asm_call_memory ao az ro rs n)` by
        simp[call_memory_capacity] >> decide_tac) >>
  qexists_tac `L` >> simp[] >>
  rpt strip_tac >> irule call_memory_agrees >> simp[] >>
  qexists_tac `L` >> simp[]
QED

Theorem call_output_retains[local]:
  LENGTH bs <= rs /\ i < LENGTH m /\
  ~in_mem_range ro rs i ==>
  EL i (TAKE ro (asm_call_memory ao az ro rs m) ++ bs ++
    DROP (ro + LENGTH bs) (asm_call_memory ao az ro rs m)) = EL i m
Proof
  strip_tac >> Cases_on `rs = 0`
  >- gvs[TAKE_DROP, call_memory_retains] >>
  `ro + rs <= LENGTH (asm_call_memory ao az ro rs m)` by
    simp[call_memory_capacity] >>
  `ro + LENGTH bs <= LENGTH (asm_call_memory ao az ro rs m)` by decide_tac >>
  `i < LENGTH (asm_call_memory ao az ro rs m)` by
    metis_tac[call_memory_grows, arithmeticTheory.LESS_LESS_EQ_TRANS] >>
  `i < ro \/ ro + LENGTH bs <= i` by
    (gvs[in_mem_range_def] >> decide_tac) >>
  simp[EL_splice_outside, call_memory_retains]
QED

Theorem related_call_completion[local]:
  asm_sym_rel p env cs ss /\
  LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    (DROP k ss.sym_stack) tail /\
  (!i. ro <= i /\ i < ro + rs ==> i NOTIN FDOM ss.sym_mem_labels) ==>
  asm_sym_step_rel p env
    (sym_lift k ss.sym_mem_labels ss
      (asm_consume_call_outcome rq ro rs []
        (ss.sym_base with <| as_stack := args;
          as_memory := asm_call_memory ao az ro rs ss.sym_base.as_memory |>)))
    (asm_consume_call_outcome rq ro rs tail
      (cs with as_memory := asm_call_memory ao az ro rs cs.as_memory))
Proof
  strip_tac >> gvs[asm_sym_rel_def] >>
  simp[asm_consume_call_outcome_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  simp[sym_lift_def, asm_sym_step_rel_def, asm_sym_rel_def, asm_next_def,
       sval_conc_def, Excl "LENGTH_APPEND"] >>
  `LENGTH (TAKE rs outcome.co_returnData) <= rs` by simp[LENGTH_TAKE_EQ] >>
  conj_tac
  >- (qexists_tac `TAKE ro (asm_call_memory ao az ro rs m) ++
        TAKE rs outcome.co_returnData ++
        DROP (ro + LENGTH (TAKE rs outcome.co_returnData))
          (asm_call_memory ao az ro rs m)` >>
      simp[call_output_length, call_memory_lengths] >>
      rpt strip_tac >> irule call_output_agrees >>
      simp[call_output_length] >>
      qexists_tac `FDOM ss.sym_mem_labels` >> simp[]) >>
  rpt strip_tac >>
  `i IN FDOM ss.sym_mem_labels` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  `~in_mem_range ro rs i` by
    (gvs[in_mem_range_def] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  `EL i (TAKE ro (asm_call_memory ao az ro rs cs.as_memory) ++
      TAKE rs outcome.co_returnData ++
      DROP (ro + LENGTH (TAKE rs outcome.co_returnData))
        (asm_call_memory ao az ro rs cs.as_memory)) = EL i cs.as_memory` by
    (irule call_output_retains >> simp[]) >>
  simp[call_output_length] >>
  `LENGTH cs.as_memory <= LENGTH (asm_call_memory ao az ro rs cs.as_memory)` by
    simp[call_memory_grows] >>
  gvs[sval_conc_def] >> decide_tac
QED

Theorem related_create_completion[local]:
  asm_sym_rel p env cs ss /\
  LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    (DROP k ss.sym_stack) tail ==>
  asm_sym_step_rel p env
    (sym_lift k ss.sym_mem_labels ss
      (asm_consume_create_outcome rq []
        (ss.sym_base with <| as_stack := args;
          as_memory := asm_call_memory ao az 0 0 ss.sym_base.as_memory |>)))
    (asm_consume_create_outcome rq tail
      (cs with as_memory := asm_call_memory ao az 0 0 cs.as_memory))
Proof
  strip_tac >>
  gvs[asm_sym_rel_def] >>
  simp[asm_consume_create_outcome_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  simp[sym_lift_def, asm_sym_step_rel_def, asm_sym_rel_def, asm_next_def,
       sval_conc_def] >>
  conj_tac
  >- (qexists_tac `asm_call_memory ao az 0 0 m` >>
      simp[call_memory_lengths] >> rpt strip_tac >>
      irule call_memory_agrees >> simp[] >>
      qexists_tac `FDOM ss.sym_mem_labels` >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  simp[call_memory_retains] >>
  `LENGTH cs.as_memory <= LENGTH (asm_call_memory ao az 0 0 cs.as_memory)`
    by simp[call_memory_grows] >>
  gvs[sval_conc_def] >> decide_tac
QED

(* The trunk's CREATE/CREATE2 fault on an oversized init code before
   consuming an outcome; the symbolic step lifts that fault the same way. *)
Theorem related_create_fault[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_step_rel p env
    (sym_lift k labs ss
       (AsmFault (ss.sym_base with <| as_stack := args;
                                      as_returndata := [] |>)))
    (AsmFault (cs with as_returndata := []))
Proof
  rw[asm_sym_rel_def] >>
  simp[sym_lift_def, asm_sym_step_rel_def, sym_obs_def, sym_init_def,
       asmSemTheory.asm_state_component_equality] >>
  qexists_tac `cs with as_returndata := []` >> simp[]
QED

Theorem asm_step_op_create[local]:
  asm_step_op otp "CREATE" s = asm_exec_create s /\
  asm_step_op otp "CREATE2" s = asm_exec_create2 s
Proof
  simp[asm_step_op_def, asm_step_arith_def] >>
  simp[asm_step_compare_def, asm_step_bitwise_def] >>
  simp[asm_step_memory_def, asm_step_control_def, asm_step_extcall_def]
QED

Theorem create_arities[local]:
  asm_op_arity "CREATE" = 3 /\ asm_op_arity "CREATE2" = 4
Proof
  EVAL_TAC
QED

Theorem sym_step_create_sim[local]:
  asm_sym_rel p env cs ss /\ MEM name ["CREATE"; "CREATE2"] ==>
  asm_sym_step_rel p env (sym_step_concrete name ss)
    (asm_step_op otp name cs)
Proof
  strip_tac >> gvs[MEM] >>
  irule sym_step_concrete_good >> simp[concrete_underflow] >>
  simp[create_arities] >> rpt strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[]
  >- (rename1 `cs.as_stack = value :: off :: sz :: tail` >>
      `asm_create_request (ss.sym_base with as_stack := [value; off; sz])
           value (w2n off) (w2n sz) NONE =
       asm_create_request cs value (w2n off) (w2n sz) NONE` by
        (irule related_create_request >>
         gvs[asm_op_mem_reads_def, log_table_def] >> metis_tac[]) >>
      simp[asm_step_op_create, asm_exec_create_def, asm_op_mem_writes_def,
           mem_labels_clear_def, GSYM pred_setTheory.UNIV_DEF,
           finite_mapTheory.DRESTRICT_UNIV] >>
      IF_CASES_TAC >> REWRITE_TAC [] >- (irule related_create_fault >> gvs[]) >>
      irule related_create_completion >> simp[]) >>
  rename1 `cs.as_stack = value :: off :: sz :: tail0` >>
  Cases_on `tail0` >- gvs[] >> gvs[] >>
  rename1 `cs.as_stack = value :: off :: sz :: salt :: tail` >>
  `asm_create_request (ss.sym_base with as_stack := [value; off; sz; salt])
       value (w2n off) (w2n sz) (SOME salt) =
   asm_create_request cs value (w2n off) (w2n sz) (SOME salt)` by
    (irule related_create_request >>
     gvs[asm_op_mem_reads_def, log_table_def] >> metis_tac[]) >>
  simp[asm_step_op_create, asm_exec_create2_def, asm_op_mem_writes_def,
       mem_labels_clear_def, GSYM pred_setTheory.UNIV_DEF,
       finite_mapTheory.DRESTRICT_UNIV] >>
  IF_CASES_TAC >> REWRITE_TAC [] >- (irule related_create_fault >> gvs[]) >>
  irule related_create_completion >> simp[]
QED

Theorem asm_step_op_call[local]:
  asm_step_op otp "CALL" s = asm_exec_call s.as_call_ctx.cc_static s /\
  asm_step_op otp "STATICCALL" s = asm_exec_staticcall s /\
  asm_step_op otp "DELEGATECALL" s = asm_exec_delegatecall s
Proof
  simp[asm_step_op_def, asm_step_arith_def] >>
  simp[asm_step_compare_def, asm_step_bitwise_def] >>
  simp[asm_step_memory_def, asm_step_control_def, asm_step_extcall_def]
QED

Theorem call_arities[local]:
  asm_op_arity "CALL" = 7 /\ asm_op_arity "STATICCALL" = 6 /\
  asm_op_arity "DELEGATECALL" = 6
Proof
  EVAL_TAC
QED

Theorem sym_step_call_sim[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_step_rel p env (sym_step_concrete "CALL" ss)
    (asm_step_op otp "CALL" cs)
Proof
  strip_tac >> irule sym_step_concrete_good >> simp[concrete_underflow] >>
  simp[call_arities] >> rpt strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  rename1 `cs.as_stack = gas :: addr :: value :: ao :: az :: ro :: rs :: tail` >>
  `ss.sym_base.as_call_ctx = cs.as_call_ctx` by gvs[asm_sym_rel_def] >>
  `asm_call_request (ss.sym_base with as_stack := [gas;addr;value;ao;az;ro;rs])
      addr value (w2n ao) (w2n az) cs.as_call_ctx.cc_static =
   asm_call_request cs addr value (w2n ao) (w2n az) cs.as_call_ctx.cc_static` by
    (irule related_call_request >>
     gvs[asm_op_mem_reads_def, log_table_def, mem_labels_hit_def] >> metis_tac[]) >>
  simp[asm_step_op_call, asm_exec_call_def, asm_op_mem_writes_def,
       mem_labels_clear_def, GSYM pred_setTheory.UNIV_DEF,
       finite_mapTheory.DRESTRICT_UNIV] >>
  irule related_call_completion >> simp[] >>
  gvs[asm_op_mem_reads_def, log_table_def, mem_labels_hit_def, in_mem_range_def] >>
  metis_tac[]
QED

Theorem sym_step_staticcall_sim[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_step_rel p env (sym_step_concrete "STATICCALL" ss)
    (asm_step_op otp "STATICCALL" cs)
Proof
  strip_tac >> irule sym_step_concrete_good >> simp[concrete_underflow] >>
  simp[call_arities] >> rpt strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rename1 `cs.as_stack = gas :: addr :: ao :: az :: ro :: rs :: tail` >>
  `asm_call_request (ss.sym_base with as_stack := [gas;addr;ao;az;ro;rs])
      addr 0w (w2n ao) (w2n az) T =
   asm_call_request cs addr 0w (w2n ao) (w2n az) T` by
    (irule related_call_request >>
     gvs[asm_op_mem_reads_def, log_table_def, mem_labels_hit_def] >> metis_tac[]) >>
  simp[asm_step_op_call, asm_exec_staticcall_def, asm_op_mem_writes_def,
       mem_labels_clear_def, GSYM pred_setTheory.UNIV_DEF,
       finite_mapTheory.DRESTRICT_UNIV] >>
  irule related_call_completion >> simp[] >>
  gvs[asm_op_mem_reads_def, log_table_def, mem_labels_hit_def, in_mem_range_def] >>
  metis_tac[]
QED

Theorem delegate_memory_as_call[local]:
  asm_expand_memory (ro + rs) m = asm_call_memory 0 (ro + rs) ro rs m
Proof
  simp[asm_call_memory_def] >>
  Cases_on `ro + rs = 0` >- gvs[asm_expand_memory_def] >>
  Cases_on `rs = 0` >> simp[] >>
  simp[asm_expand_memory_def] >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem related_delegate_completion[local]:
  asm_sym_rel p env cs ss /\
  LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    (DROP k ss.sym_stack) tail /\
  (!i. ro <= i /\ i < ro + rs ==> i NOTIN FDOM ss.sym_mem_labels) ==>
  asm_sym_step_rel p env
    (sym_lift k ss.sym_mem_labels ss
      (case extract_asm_result (ss.sym_base with as_stack := args) 1w ro rs rr of
         SOME (output,s') => AsmOK (asm_next (s' with as_stack := [output]))
       | NONE => AsmError "delegatecall: non-terminating"))
    (case extract_asm_result cs 1w ro rs rr of
       SOME (output,s') => AsmOK (asm_next (s' with as_stack := output :: tail))
     | NONE => AsmError "delegatecall: non-terminating")
Proof
  strip_tac >> Cases_on `rr` >>
  simp[extract_asm_result_def, sym_lift_def, asm_sym_step_rel_def] >>
  PairCases_on `x` >>
  Cases_on `x1.contexts` >>
  simp[extract_asm_result_def, sym_lift_def, asm_sym_step_rel_def] >>
  Cases_on `t` >>
  simp[extract_asm_result_def, sym_lift_def, asm_sym_step_rel_def] >>
  PairCases_on `h` >>
  Cases_on `x0` >> gvs[asm_sym_rel_def] >>
  simp[] >> TRY (Cases_on `y` >> simp[]) >>
  simp[sym_lift_def, asm_sym_step_rel_def, asm_sym_rel_def, asm_next_def,
       sval_conc_def, delegate_memory_as_call, Excl "LENGTH_APPEND"] >>
  `LENGTH (TAKE rs h0.returnData) <= rs` by simp[LENGTH_TAKE_EQ] >>
  (conj_tac
  >- (qexists_tac `TAKE ro (asm_call_memory 0 (ro + rs) ro rs m) ++
        TAKE rs h0.returnData ++
        DROP (ro + LENGTH (TAKE rs h0.returnData))
          (asm_call_memory 0 (ro + rs) ro rs m)` >>
      simp[asm_state_component_equality, call_output_length, call_memory_lengths] >>
      rpt strip_tac >> irule call_output_agrees >>
      simp[call_output_length] >>
      qexists_tac `FDOM ss.sym_mem_labels` >> simp[]) >>
  rpt strip_tac >>
  `i IN FDOM ss.sym_mem_labels` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  `~in_mem_range ro rs i` by
    (gvs[in_mem_range_def] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  `EL i (TAKE ro (asm_call_memory 0 (ro + rs) ro rs cs.as_memory) ++
      TAKE rs h0.returnData ++
      DROP (ro + LENGTH (TAKE rs h0.returnData))
        (asm_call_memory 0 (ro + rs) ro rs cs.as_memory)) = EL i cs.as_memory` by
    (irule call_output_retains >> simp[]) >>
  simp[call_output_length] >>
  `LENGTH cs.as_memory <= LENGTH (asm_call_memory 0 (ro + rs) ro rs cs.as_memory)` by
    simp[call_memory_grows] >>
  gvs[sval_conc_def] >> decide_tac)
QED

Theorem sym_step_delegatecall_sim[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_step_rel p env (sym_step_concrete "DELEGATECALL" ss)
    (asm_step_op otp "DELEGATECALL" cs)
Proof
  strip_tac >> irule sym_step_concrete_good >> simp[concrete_underflow] >>
  simp[call_arities] >> rpt strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rename1 `cs.as_stack = gas :: addr :: ao :: az :: ro :: rs :: tail` >>
  `~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n ao) (w2n az))` by
    (gvs[asm_op_mem_reads_def, log_table_def, mem_labels_hit_def] >> metis_tac[]) >>
  drule_all related_memory_read >>
  disch_then (qspec_then `w2n ao + w2n az` assume_tac) >>
  `ss.sym_base.as_accounts = cs.as_accounts /\
   ss.sym_base.as_call_ctx = cs.as_call_ctx` by gvs[asm_sym_rel_def] >>
  `make_asm_delegatecall_state
      (ss.sym_base with as_stack := [gas;addr;ao;az;ro;rs])
      (w2w addr) (w2n gas)
      (TAKE (w2n az) (DROP (w2n ao)
         (asm_expand_memory (w2n ao + w2n az) cs.as_memory)))
      (lookup_account (w2w addr) cs.as_accounts).code cs.as_call_ctx.cc_static =
   make_asm_delegatecall_state cs (w2w addr) (w2n gas)
      (TAKE (w2n az) (DROP (w2n ao)
         (asm_expand_memory (w2n ao + w2n az) cs.as_memory)))
      (lookup_account (w2w addr) cs.as_accounts).code cs.as_call_ctx.cc_static` by
    (irule related_delegatecall_state >> metis_tac[]) >>
  simp[asm_step_op_call, asm_exec_delegatecall_def, asm_op_mem_writes_def,
       mem_labels_clear_def, GSYM pred_setTheory.UNIV_DEF,
       finite_mapTheory.DRESTRICT_UNIV] >>
  irule related_delegate_completion >> simp[] >>
  gvs[asm_op_mem_reads_def, log_table_def, mem_labels_hit_def, in_mem_range_def] >>
  metis_tac[]
QED

Theorem related_stack_next[local]:
  asm_sym_rel p env cs ss /\
  LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    (DROP k ss.sym_stack) tail ==>
  asm_sym_step_rel p env
    (sym_lift k ss.sym_mem_labels ss
      (AsmOK (asm_next (ss.sym_base with <|as_stack := vals;
        as_logs := ss.sym_base.as_logs ++ events|>))))
    (AsmOK (asm_next (cs with <|as_stack := vals ++ tail;
      as_logs := cs.as_logs ++ events|>)))
Proof
  strip_tac >>
  `LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    (MAP Val vals ++ DROP k ss.sym_stack) (vals ++ tail)` by
    (irule LIST_REL_APPEND_suff >>
     simp[LIST_REL_MAP1, LIST_REL_EL_EQN, sval_conc_def] >>
     gvs[LIST_REL_EL_EQN]) >>
  gvs[asm_sym_rel_def] >>
  simp[sym_lift_def, asm_sym_step_rel_def, asm_sym_rel_def, asm_next_def] >>
  conj_tac >- (qexists_tac `m` >> simp[]) >>
  gvs[sval_conc_def] >> metis_tac[]
QED

Theorem pure_binary_arities[local]:
  EVERY (\name. asm_op_arity name = 2)
    ["ADD"; "MUL"; "SUB"; "DIV"; "SDIV"; "MOD"; "SMOD"; "EXP";
     "LT"; "GT"; "SLT"; "SGT"; "EQ"; "AND"; "OR"; "XOR";
     "SHL"; "SHR"; "SAR"; "SIGNEXTEND"; "BYTE"]
Proof
  EVAL_TAC
QED

Theorem sym_step_pure_binary_sim[local]:
  asm_sym_rel p env cs ss /\
  MEM name ["ADD"; "MUL"; "SUB"; "DIV"; "SDIV"; "MOD"; "SMOD"; "EXP";
     "LT"; "GT"; "SLT"; "SGT"; "EQ"; "AND"; "OR"; "XOR";
     "SHL"; "SHR"; "SAR"; "SIGNEXTEND"; "BYTE"] ==>
  asm_sym_step_rel p env (sym_step_concrete name ss)
    (asm_step_op otp name cs)
Proof
  strip_tac >>
  `asm_op_arity name = 2` by
    (mp_tac pure_binary_arities >> rewrite_tac[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  irule sym_step_concrete_good >> simp[concrete_underflow] >>
  rpt strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >> Cases_on `t` >> gvs[] >>
  gvs[MEM] >>
  simp[asm_step_op_def, asm_step_arith_def] >>
  simp[asm_step_compare_def] >> simp[asm_step_bitwise_def] >>
  simp[asm_binop_def] >> simp[asm_op_mem_writes_def] >>
  simp[mem_labels_clear_def, GSYM pred_setTheory.UNIV_DEF,
       finite_mapTheory.DRESTRICT_UNIV] >>
  irule (SRULE [] (Q.INST [`vals` |-> `[w:bytes32]`, `events` |-> `[]`]
    related_stack_next)) >> simp[]
QED

Theorem pure_small_arities[local]:
  asm_op_arity "ISZERO" = 1 /\ asm_op_arity "NOT" = 1 /\
  asm_op_arity "ADDMOD" = 3 /\ asm_op_arity "MULMOD" = 3
Proof
  EVAL_TAC
QED

Theorem sym_step_pure_unary_sim[local]:
  asm_sym_rel p env cs ss /\ MEM name ["ISZERO"; "NOT"] ==>
  asm_sym_step_rel p env (sym_step_concrete name ss)
    (asm_step_op otp name cs)
Proof
  strip_tac >>
  `asm_op_arity name = 1` by gvs[MEM, pure_small_arities] >>
  irule sym_step_concrete_good >> simp[concrete_underflow] >>
  rpt strip_tac >> Cases_on `cs.as_stack` >> gvs[] >>
  gvs[MEM] >> simp[asm_step_op_def, asm_step_arith_def] >>
  simp[asm_step_compare_def, asm_step_bitwise_def, asm_unop_def,
       asm_op_mem_writes_def, mem_labels_clear_def,
       GSYM pred_setTheory.UNIV_DEF, finite_mapTheory.DRESTRICT_UNIV] >>
  irule (SRULE [] (Q.INST [`vals` |-> `[w:bytes32]`, `events` |-> `[]`]
    related_stack_next)) >> simp[]
QED

Theorem sym_step_pure_ternary_sim[local]:
  asm_sym_rel p env cs ss /\ MEM name ["ADDMOD"; "MULMOD"] ==>
  asm_sym_step_rel p env (sym_step_concrete name ss)
    (asm_step_op otp name cs)
Proof
  strip_tac >>
  `asm_op_arity name = 3` by gvs[MEM, pure_small_arities] >>
  irule sym_step_concrete_good >> simp[concrete_underflow] >>
  rpt strip_tac >> Cases_on `cs.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  gvs[MEM] >> simp[asm_step_op_def, asm_step_arith_def, asm_ternop_def,
       asm_op_mem_writes_def, mem_labels_clear_def,
       GSYM pred_setTheory.UNIV_DEF, finite_mapTheory.DRESTRICT_UNIV] >>
  irule (SRULE [] (Q.INST [`vals` |-> `[w:bytes32]`, `events` |-> `[]`]
    related_stack_next)) >> simp[]
QED

Theorem context_push_arities[local]:
  EVERY (\name. asm_op_arity name = 0)
    ["CALLER"; "ADDRESS"; "CALLVALUE"; "CALLDATASIZE"; "ORIGIN";
     "GASPRICE"; "CHAINID"; "COINBASE"; "TIMESTAMP"; "NUMBER";
     "PREVRANDAO"; "GASLIMIT"; "BASEFEE"; "BLOBBASEFEE";
     "SELFBALANCE"; "RETURNDATASIZE"; "MSIZE"]
Proof
  EVAL_TAC
QED

Theorem sym_step_context_push_sim[local]:
  asm_sym_rel p env cs ss /\
  MEM name ["CALLER"; "ADDRESS"; "CALLVALUE"; "CALLDATASIZE"; "ORIGIN";
     "GASPRICE"; "CHAINID"; "COINBASE"; "TIMESTAMP"; "NUMBER";
     "PREVRANDAO"; "GASLIMIT"; "BASEFEE"; "BLOBBASEFEE";
     "SELFBALANCE"; "RETURNDATASIZE"; "MSIZE"] ==>
  asm_sym_step_rel p env (sym_step_concrete name ss)
    (asm_step_op otp name cs)
Proof
  strip_tac >>
  `asm_op_arity name = 0` by
    (mp_tac context_push_arities >> rewrite_tac[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  irule sym_step_concrete_good >> simp[] >> rpt strip_tac >>
  `ss.sym_base.as_call_ctx = cs.as_call_ctx /\
   ss.sym_base.as_tx_ctx = cs.as_tx_ctx /\
   ss.sym_base.as_block_ctx = cs.as_block_ctx /\
   ss.sym_base.as_accounts = cs.as_accounts /\
   ss.sym_base.as_returndata = cs.as_returndata /\
   LENGTH ss.sym_base.as_memory = LENGTH cs.as_memory` by
    gvs[asm_sym_rel_def] >>
  gvs[MEM] >> simp[asm_step_op_def, asm_step_arith_def] >>
  simp[asm_step_compare_def, asm_step_bitwise_def] >>
  simp[asm_step_memory_def, asm_step_control_def] >>
  simp[asm_step_extcall_def, asm_step_copy_def] >>
  simp[asm_step_context_def] >> simp[asm_push_val_def] >>
  simp[asm_op_mem_writes_def] >>
  simp[mem_labels_clear_def, GSYM pred_setTheory.UNIV_DEF,
       finite_mapTheory.DRESTRICT_UNIV] >>
  irule (SRULE [] (Q.INST [`vals` |-> `[w:bytes32]`, `events` |-> `[]`]
    related_stack_next)) >> simp[]
QED

Theorem context_load_arities[local]:
  EVERY (\name. asm_op_arity name = 1)
    ["CALLDATALOAD"; "BLOCKHASH"; "BLOBHASH"; "BALANCE";
     "EXTCODESIZE"; "EXTCODEHASH"; "SLOAD"; "TLOAD"]
Proof
  EVAL_TAC
QED

Theorem sym_step_context_load_sim[local]:
  asm_sym_rel p env cs ss /\
  MEM name ["CALLDATALOAD"; "BLOCKHASH"; "BLOBHASH"; "BALANCE";
     "EXTCODESIZE"; "EXTCODEHASH"; "SLOAD"; "TLOAD"] ==>
  asm_sym_step_rel p env (sym_step_concrete name ss)
    (asm_step_op otp name cs)
Proof
  strip_tac >>
  `asm_op_arity name = 1` by
    (mp_tac context_load_arities >> rewrite_tac[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  irule sym_step_concrete_good >> simp[concrete_underflow] >>
  rpt strip_tac >> Cases_on `cs.as_stack` >> gvs[] >>
  `ss.sym_base.as_call_ctx = cs.as_call_ctx /\
   ss.sym_base.as_tx_ctx = cs.as_tx_ctx /\
   ss.sym_base.as_block_ctx = cs.as_block_ctx /\
   ss.sym_base.as_accounts = cs.as_accounts /\
   ss.sym_base.as_transient = cs.as_transient` by
    gvs[asm_sym_rel_def] >>
  gvs[MEM] >> simp[asm_step_op_def, asm_step_arith_def] >>
  simp[asm_step_compare_def, asm_step_bitwise_def] >>
  simp[asm_step_memory_def, asm_step_control_def] >>
  simp[asm_step_extcall_def, asm_step_copy_def] >>
  simp[asm_step_context_def, asm_state_unop_def, asm_sload_def, asm_tload_def,
       asm_op_mem_writes_def, mem_labels_clear_def,
       GSYM pred_setTheory.UNIV_DEF, finite_mapTheory.DRESTRICT_UNIV] >>
  irule (SRULE [] (Q.INST [`vals` |-> `[w:bytes32]`, `events` |-> `[]`]
    related_stack_next)) >> simp[]
QED

Theorem remaining_plain_arities[local]:
  asm_op_arity "SSTORE" = 2 /\ asm_op_arity "TSTORE" = 2 /\
  asm_op_arity "POP" = 1 /\ asm_op_arity "SELFDESTRUCT" = 1 /\
  asm_op_arity "GAS" = 0 /\ asm_op_arity "JUMPDEST" = 0 /\
  asm_op_arity "STOP" = 0 /\ asm_op_arity "INVALID" = 0
Proof
  EVAL_TAC
QED

Theorem sym_step_store_sim[local]:
  asm_sym_rel p env cs ss /\ MEM name ["SSTORE"; "TSTORE"] ==>
  asm_sym_step_rel p env (sym_step_concrete name ss)
    (asm_step_op otp name cs)
Proof
  strip_tac >>
  `asm_op_arity name = 2` by gvs[MEM, remaining_plain_arities] >>
  irule sym_step_concrete_good >> simp[concrete_underflow] >>
  rpt strip_tac >> Cases_on `cs.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[MEM] >> simp[asm_step_op_def, asm_step_arith_def] >>
  simp[asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def] >>
  gvs[asm_sym_rel_def] >>
  simp[asm_sstore_def, asm_tstore_def, sym_lift_def, asm_next_def,
       asm_op_mem_writes_def, mem_labels_clear_def,
       GSYM pred_setTheory.UNIV_DEF, finite_mapTheory.DRESTRICT_UNIV,
       asm_sym_step_rel_def, asm_sym_rel_def] >>
  conj_tac >- (qexists_tac `m` >> simp[]) >> metis_tac[]
QED

Theorem sym_step_gas_sim[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_step_rel p env (sym_step_concrete "GAS" ss)
    (asm_step_op otp "GAS" cs)
Proof
  strip_tac >> irule sym_step_concrete_good >>
  simp[remaining_plain_arities] >> rpt strip_tac >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  simp[asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def] >>
  simp[asm_step_extcall_def, asm_step_copy_def, asm_step_context_def] >>
  gvs[asm_sym_rel_def] >> Cases_on `cs.as_gas_readings` >>
  simp[asm_gas_def, asm_push_val_def, sym_lift_def, asm_next_def,
       asm_op_mem_writes_def, mem_labels_clear_def,
       GSYM pred_setTheory.UNIV_DEF, finite_mapTheory.DRESTRICT_UNIV,
       asm_sym_step_rel_def, asm_sym_rel_def, sval_conc_def] >>
  conj_tac >- (qexists_tac `m` >> simp[]) >>
  gvs[sval_conc_def] >> metis_tac[]
QED

Theorem sym_step_plain_control_sim[local]:
  asm_sym_rel p env cs ss /\ MEM name ["POP"; "JUMPDEST"; "STOP"; "INVALID"] ==>
  asm_sym_step_rel p env (sym_step_concrete name ss)
    (asm_step_op otp name cs)
Proof
  strip_tac >> irule sym_step_concrete_good >>
  simp[concrete_underflow] >> rpt strip_tac >>
  gvs[MEM] >> simp[remaining_plain_arities] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  simp[asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def] >>
  gvs[asm_sym_rel_def] >>
  Cases_on `cs.as_stack` >>
  gvs[remaining_plain_arities, asm_pop_def, sym_lift_def, asm_next_def,
      asm_op_mem_writes_def, mem_labels_clear_def,
      GSYM pred_setTheory.UNIV_DEF, finite_mapTheory.DRESTRICT_UNIV,
      asm_sym_step_rel_def, asm_sym_rel_def, sym_obs_def, sym_init_def] >>
  conj_tac >- (qexists_tac `m` >> simp[]) >> metis_tac[]
QED

Theorem sym_step_selfdestruct_sim[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_step_rel p env (sym_step_concrete "SELFDESTRUCT" ss)
    (asm_step_op otp "SELFDESTRUCT" cs)
Proof
  strip_tac >> irule sym_step_concrete_good >>
  simp[remaining_plain_arities, concrete_underflow] >> rpt strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  simp[asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def] >>
  simp[asm_step_extcall_def] >> gvs[asm_sym_rel_def] >>
  simp[asm_selfdestruct_def, sym_lift_def, asm_sym_step_rel_def,
       sym_obs_def, sym_init_def]
QED

Theorem memory_read_arities[local]:
  asm_op_arity "MLOAD" = 1 /\ asm_op_arity "SHA3" = 2 /\
  asm_op_arity "RETURN" = 2 /\ asm_op_arity "REVERT" = 2
Proof
  EVAL_TAC
QED

Theorem sym_step_memory_terminal_sim[local]:
  asm_sym_rel p env cs ss /\ MEM name ["RETURN"; "REVERT"] ==>
  asm_sym_step_rel p env (sym_step_concrete name ss)
    (asm_step_op otp name cs)
Proof
  strip_tac >>
  `asm_op_arity name = 2` by gvs[MEM, memory_read_arities] >>
  irule sym_step_concrete_good >> simp[concrete_underflow] >>
  rpt strip_tac >> Cases_on `cs.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  `~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n h) (w2n h'))` by
    gvs[MEM, asm_op_mem_reads_def] >>
  drule_all related_memory_read >> disch_then (qspec_then `w2n h + w2n h'` assume_tac) >>
  gvs[MEM] >> simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  simp[asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def] >>
  simp[asm_return_op_def, asm_revert_op_def] >>
  Cases_on `w2n h' = 0` >> simp[] >>
  gvs[asm_sym_rel_def] >>
  simp[sym_lift_def, asm_sym_step_rel_def, sym_obs_def, sym_init_def]
QED

Theorem related_expanded_stack_next[local]:
  asm_sym_rel p env cs ss /\
  LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    (DROP k ss.sym_stack) tail ==>
  asm_sym_step_rel p env
    (sym_lift k ss.sym_mem_labels ss
      (AsmOK (asm_next (ss.sym_base with <|as_stack := vals;
        as_memory := asm_expand_memory n ss.sym_base.as_memory;
        as_logs := ss.sym_base.as_logs ++ events|>))))
    (AsmOK (asm_next (cs with <|as_stack := vals ++ tail;
      as_memory := asm_expand_memory n cs.as_memory;
      as_logs := cs.as_logs ++ events|>)))
Proof
  strip_tac >>
  `LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    (MAP Val vals ++ DROP k ss.sym_stack) (vals ++ tail)` by
    (irule LIST_REL_APPEND_suff >>
     simp[LIST_REL_MAP1, LIST_REL_EL_EQN, sval_conc_def] >>
     gvs[LIST_REL_EL_EQN]) >>
  gvs[asm_sym_rel_def] >>
  simp[sym_lift_def, asm_sym_step_rel_def, asm_sym_rel_def, asm_next_def] >>
  conj_tac
  >- (qexists_tac `asm_expand_memory n m` >>
      simp[expand_memory_lengths] >> rpt strip_tac >>
      irule expand_memory_agrees >> simp[] >>
      qexists_tac `FDOM ss.sym_mem_labels` >> simp[]) >>
  rpt gen_tac >> disch_tac >> first_x_assum drule >> strip_tac >>
  simp[expand_memory_retains] >>
  `LENGTH cs.as_memory <= LENGTH (asm_expand_memory n cs.as_memory)` by
    simp[expand_memory_grows] >> decide_tac
QED

Theorem sym_step_mload_sim[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_step_rel p env (sym_step_concrete "MLOAD" ss)
    (asm_step_op otp "MLOAD" cs)
Proof
  strip_tac >> irule sym_step_concrete_good >>
  simp[memory_read_arities, concrete_underflow] >> rpt strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >>
  `~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n h) 32)` by
    gvs[asm_op_mem_reads_def] >>
  drule_all related_memory_read >>
  disch_then (qspec_then `w2n h + 32` assume_tac) >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  simp[asm_step_bitwise_def, asm_step_memory_def, asm_mload_def] >>
  simp[asm_op_mem_writes_def, mem_labels_clear_def,
       GSYM pred_setTheory.UNIV_DEF, finite_mapTheory.DRESTRICT_UNIV] >>
  irule (SRULE [] (Q.INST [`vals` |-> `[v:bytes32]`, `events` |-> `[]`]
    related_expanded_stack_next)) >> simp[]
QED

Theorem sym_step_sha3_sim[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_step_rel p env (sym_step_concrete "SHA3" ss)
    (asm_step_op otp "SHA3" cs)
Proof
  strip_tac >> irule sym_step_concrete_good >>
  simp[memory_read_arities, concrete_underflow] >> rpt strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >> Cases_on `t` >> gvs[] >>
  `~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n h) (w2n h'))` by
    gvs[asm_op_mem_reads_def] >>
  drule_all related_memory_read >>
  disch_then (qspec_then `w2n h + w2n h'` assume_tac) >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  simp[asm_step_bitwise_def, asm_step_memory_def, asm_sha3_def] >>
  simp[asm_op_mem_writes_def, mem_labels_clear_def,
       GSYM pred_setTheory.UNIV_DEF, finite_mapTheory.DRESTRICT_UNIV] >>
  Cases_on `h' = 0w` >> simp[]
  >- (irule (SRULE [] (Q.INST [`vals` |-> `[w:bytes32]`, `events` |-> `[]`]
        related_stack_next)) >> simp[]) >>
  irule (SRULE [] (Q.INST [`vals` |-> `[v:bytes32]`, `events` |-> `[]`]
    related_expanded_stack_next)) >> simp[]
QED

Theorem related_spliced_next[local]:
  asm_sym_rel p env cs ss /\ off + LENGTH bs <= n /\
  LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    (DROP k ss.sym_stack) tail ==>
  asm_sym_step_rel p env
    (sym_lift k (mem_labels_clear ss.sym_mem_labels (in_mem_range off (LENGTH bs))) ss
      (AsmOK (asm_next (ss.sym_base with <|as_stack := [];
        as_memory := TAKE off (asm_expand_memory n ss.sym_base.as_memory) ++ bs ++
          DROP (off + LENGTH bs) (asm_expand_memory n ss.sym_base.as_memory)|>))))
    (AsmOK (asm_next (cs with <|as_stack := tail;
      as_memory := TAKE off (asm_expand_memory n cs.as_memory) ++ bs ++
        DROP (off + LENGTH bs) (asm_expand_memory n cs.as_memory)|>)))
Proof
  strip_tac >> gvs[asm_sym_rel_def] >>
  `off + LENGTH bs <= LENGTH (asm_expand_memory n cs.as_memory)` by
    (mp_tac (Q.SPECL [`n`, `cs.as_memory`] asm_expand_memory_length) >> decide_tac) >>
  `off + LENGTH bs <= LENGTH (asm_expand_memory n m)` by
    metis_tac[expand_memory_lengths] >>
  simp[sym_lift_def, asm_sym_step_rel_def, asm_sym_rel_def, asm_next_def,
       Excl "LENGTH_APPEND"] >>
  conj_tac
  >- (qexists_tac `TAKE off (asm_expand_memory n m) ++ bs ++
        DROP (off + LENGTH bs) (asm_expand_memory n m)` >>
      simp[Excl "LENGTH_APPEND", overwrite_prefix_length_suffix, expand_memory_lengths] >>
      rpt strip_tac >> irule splice_memory_agrees >>
      simp[expand_memory_lengths] >>
      qexists_tac `FDOM ss.sym_mem_labels` >> conj_tac
      >- (rpt strip_tac >> irule expand_memory_agrees >> simp[] >>
          qexists_tac `FDOM ss.sym_mem_labels` >> simp[]) >>
      gvs[mem_labels_clear_def, finite_mapTheory.FDOM_DRESTRICT]) >>
  rpt gen_tac >> disch_tac >> irule cleared_labels_valid >> simp[] >>
  qexistsl_tac [`in_mem_range off (LENGTH bs)`, `ss.sym_mem_labels`, `cs.as_memory`] >>
  simp[expand_memory_grows] >> conj_tac >- metis_tac[] >>
  qx_gen_tac `idx` >> strip_tac >>
  `idx < off \/ off + LENGTH bs <= idx` by gvs[in_mem_range_def] >>
  `idx < LENGTH (asm_expand_memory n cs.as_memory)` by
    (`LENGTH cs.as_memory <= LENGTH (asm_expand_memory n cs.as_memory)` by
      simp[expand_memory_grows] >> decide_tac) >>
  simp[EL_splice_outside, expand_memory_retains]
QED

Theorem memory_write_arities[local]:
  asm_op_arity "MSTORE" = 2 /\ asm_op_arity "MSTORE8" = 2 /\
  asm_op_arity "MCOPY" = 3 /\ asm_op_arity "CALLDATACOPY" = 3 /\
  asm_op_arity "RETURNDATACOPY" = 3 /\ asm_op_arity "EXTCODECOPY" = 4
Proof
  EVAL_TAC
QED

Theorem sym_step_memory_store_sim[local]:
  asm_sym_rel p env cs ss /\ MEM name ["MSTORE"; "MSTORE8"] ==>
  asm_sym_step_rel p env (sym_step_concrete name ss)
    (asm_step_op otp name cs)
Proof
  strip_tac >>
  `asm_op_arity name = 2` by gvs[MEM, memory_write_arities] >>
  irule sym_step_concrete_good >> simp[concrete_underflow] >>
  rpt strip_tac >> Cases_on `cs.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >> gvs[MEM] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  simp[asm_step_bitwise_def, asm_step_memory_def] >>
  simp[asm_mstore_def, asm_mstore8_def, asm_op_mem_writes_def]
  >- (irule (SRULE [] (Q.INST [`bs` |-> `word_to_bytes (h':bytes32) T`]
        related_spliced_next)) >> simp[]) >>
  irule (SRULE [] (Q.INST [`bs` |-> `[w2w (h':bytes32):byte]`]
    related_spliced_next)) >> simp[]
QED

Theorem sym_step_calldatacopy_sim[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_step_rel p env (sym_step_concrete "CALLDATACOPY" ss)
    (asm_step_op otp "CALLDATACOPY" cs)
Proof
  strip_tac >> irule sym_step_concrete_good >>
  simp[memory_write_arities, concrete_underflow] >> rpt strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  `ss.sym_base.as_call_ctx = cs.as_call_ctx` by gvs[asm_sym_rel_def] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  simp[asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def] >>
  simp[asm_step_extcall_def, asm_step_copy_def, asm_copy_to_mem_def,
       asm_op_mem_writes_def] >>
  Cases_on `h'' = 0w` >> simp[]
  >- (simp[mem_labels_clear_def, in_mem_range_def, GSYM pred_setTheory.UNIV_DEF,
          finite_mapTheory.DRESTRICT_UNIV, listTheory.TAKE_DROP] >>
      irule (SRULE [] (Q.INST [`vals` |-> `[]:bytes32 list`, `events` |-> `[]`]
        related_stack_next)) >> simp[]) >>
  qabbrev_tac `bs = TAKE (w2n h'') (DROP (w2n h')
    (asm_expand_memory (w2n h' + w2n h'') cs.as_call_ctx.cc_calldata))` >>
  `LENGTH bs = w2n h''` by
    (simp[Abbr `bs`, LENGTH_TAKE_EQ, LENGTH_DROP] >>
     mp_tac (Q.SPECL [`w2n (h':bytes32) + w2n (h'':bytes32)`, `cs.as_call_ctx.cc_calldata`]
       asm_expand_memory_length) >> decide_tac) >>
  qpat_assum `LENGTH bs = _` (fn th => rewrite_tac[GSYM th]) >>
  irule related_spliced_next >> simp[]
QED

Theorem sym_step_extcodecopy_sim[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_step_rel p env (sym_step_concrete "EXTCODECOPY" ss)
    (asm_step_op otp "EXTCODECOPY" cs)
Proof
  strip_tac >> irule sym_step_concrete_good >>
  simp[memory_write_arities, concrete_underflow] >> rpt strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >> Cases_on `t` >> gvs[] >>
  rename1 `cs.as_stack = addr::dst::src::sz::tail` >>
  `ss.sym_base.as_accounts = cs.as_accounts` by gvs[asm_sym_rel_def] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  simp[asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def] >>
  simp[asm_step_extcall_def, asm_step_copy_def, asm_extcodecopy_def,
       asm_op_mem_writes_def] >>
  Cases_on `sz = 0w` >> simp[]
  >- (simp[mem_labels_clear_def, in_mem_range_def, GSYM pred_setTheory.UNIV_DEF,
          finite_mapTheory.DRESTRICT_UNIV] >>
      irule (SRULE [] (Q.INST [`vals` |-> `[]:bytes32 list`, `events` |-> `[]`]
        related_stack_next)) >> simp[]) >>
  qabbrev_tac `bs = TAKE (w2n sz) (DROP (w2n src)
    (asm_expand_memory (w2n src + w2n sz) (lookup_account (w2w addr) cs.as_accounts).code))` >>
  `LENGTH bs = w2n sz` by
    (simp[Abbr `bs`, LENGTH_TAKE_EQ, LENGTH_DROP] >>
     mp_tac (Q.SPECL [`w2n (src:bytes32) + w2n (sz:bytes32)`,
       `(lookup_account (w2w (addr:bytes32)) cs.as_accounts).code`]
       asm_expand_memory_length) >> decide_tac) >>
  qpat_assum `LENGTH bs = _` (fn th => rewrite_tac[GSYM th]) >>
  irule related_spliced_next >> simp[]
QED

Theorem sym_step_mcopy_sim[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_step_rel p env (sym_step_concrete "MCOPY" ss)
    (asm_step_op otp "MCOPY" cs)
Proof
  strip_tac >> irule sym_step_concrete_good >>
  simp[memory_write_arities, concrete_underflow] >> rpt strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  rename1 `cs.as_stack = dst::src::sz::tail` >>
  `~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n src) (w2n sz))` by
    gvs[asm_op_mem_reads_def, log_table_def] >>
  drule_all related_memory_read >>
  disch_then (qspec_then `MAX (w2n src + w2n sz) (w2n dst + w2n sz)` assume_tac) >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  simp[asm_step_bitwise_def, asm_step_memory_def, asm_mcopy_def,
       asm_op_mem_writes_def] >>
  Cases_on `sz = 0w` >> simp[]
  >- (simp[mem_labels_clear_def, in_mem_range_def, GSYM pred_setTheory.UNIV_DEF,
          finite_mapTheory.DRESTRICT_UNIV] >>
      irule (SRULE [] (Q.INST [`vals` |-> `[]:bytes32 list`, `events` |-> `[]`]
        related_stack_next)) >> simp[]) >>
  qabbrev_tac `n = MAX (w2n src + w2n sz) (w2n dst + w2n sz)` >>
  qabbrev_tac `bs = TAKE (w2n sz) (DROP (w2n src) (asm_expand_memory n cs.as_memory))` >>
  `LENGTH bs = w2n sz` by
    (simp[Abbr `bs`, LENGTH_TAKE_EQ, LENGTH_DROP] >>
     mp_tac (Q.SPECL [`n:num`, `cs.as_memory`] asm_expand_memory_length) >>
     simp[Abbr `n`] >> decide_tac) >>
  qpat_assum `LENGTH bs = _` (fn th => rewrite_tac[GSYM th]) >>
  irule related_spliced_next >> simp[Abbr `n`]
QED

Theorem sym_step_returndatacopy_sim[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_step_rel p env (sym_step_concrete "RETURNDATACOPY" ss)
    (asm_step_op otp "RETURNDATACOPY" cs)
Proof
  strip_tac >> irule sym_step_concrete_good >>
  simp[memory_write_arities, concrete_underflow] >> rpt strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  rename1 `cs.as_stack = dst::src::sz::tail` >>
  `ss.sym_base.as_returndata = cs.as_returndata` by gvs[asm_sym_rel_def] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  simp[asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def] >>
  simp[asm_step_extcall_def, asm_step_copy_def, asm_returndatacopy_def,
       asm_op_mem_writes_def] >>
  Cases_on `LENGTH cs.as_returndata < w2n src + w2n sz` >> simp[]
  >- (gvs[asm_sym_rel_def] >>
      simp[sym_lift_def, asm_sym_step_rel_def, sym_obs_def, sym_init_def]) >>
  Cases_on `sz = 0w` >> simp[]
  >- (simp[mem_labels_clear_def, in_mem_range_def, GSYM pred_setTheory.UNIV_DEF,
          finite_mapTheory.DRESTRICT_UNIV] >>
      irule (SRULE [] (Q.INST [`vals` |-> `[]:bytes32 list`, `events` |-> `[]`]
        related_stack_next)) >> simp[]) >>
  qabbrev_tac `bs = TAKE (w2n sz) (DROP (w2n src) cs.as_returndata)` >>
  `LENGTH bs = w2n sz` by
    (simp[Abbr `bs`, LENGTH_TAKE_EQ, LENGTH_DROP] >> decide_tac) >>
  qpat_assum `LENGTH bs = _` (fn th => rewrite_tac[GSYM th]) >>
  irule related_spliced_next >> simp[]
QED

Theorem log_dispatch[local]:
  ALOOKUP log_table name = SOME n ==>
  asm_op_arity name = n + 2 /\
  asm_step_op otp name s = asm_log n s /\
  (!args. asm_op_mem_reads name args =
    in_mem_range (w2n (EL 0 args)) (w2n (EL 1 args))) /\
  (!args. asm_op_mem_writes name args = (\i. F))
Proof
  simp[log_table_def] >> rpt IF_CASES_TAC >> gvs[] >>
  simp[asm_op_arity_def, asm_op_arity_table_def] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
  simp[asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def] >>
  simp[asm_step_extcall_def, asm_step_copy_def, asm_step_context_def] >>
  simp[dup_table_def, swap_table_def, log_table_def,
       asm_op_mem_reads_def, asm_op_mem_writes_def]
QED

Theorem stack_logs_memory_self[local]:
  s with <|as_stack := stk; as_memory := s.as_memory; as_logs := logs|> =
  s with <|as_stack := stk; as_logs := logs|>
Proof
  simp[asm_state_component_equality]
QED

Theorem sym_step_log_sim[local]:
  asm_sym_rel p env cs ss /\ ALOOKUP log_table name = SOME n ==>
  asm_sym_step_rel p env (sym_step_concrete name ss)
    (asm_step_op otp name cs)
Proof
  strip_tac >>
  `asm_op_arity name = n + 2` by metis_tac[log_dispatch] >>
  irule sym_step_concrete_good >> simp[concrete_underflow] >> rpt strip_tac >>
  drule log_dispatch >> strip_tac >>
  Cases_on `cs.as_stack` >> gvs[] >> Cases_on `t` >> gvs[] >>
  rename1 `cs.as_stack = off::sz::topics` >>
  `~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n off) (w2n sz))` by
    gvs[] >>
  drule_all related_memory_read >>
  disch_then (qspec_then `w2n off + w2n sz` assume_tac) >>
  `ss.sym_base.as_call_ctx = cs.as_call_ctx` by gvs[asm_sym_rel_def] >>
  simp[asm_log_def, listTheory.DROP_TAKE, listTheory.TAKE_TAKE_MIN] >>
  simp[mem_labels_clear_def, GSYM pred_setTheory.UNIV_DEF,
       finite_mapTheory.DRESTRICT_UNIV] >>
  Cases_on `sz = 0w` >> simp[]
  >- (simp[stack_logs_memory_self] >>
      irule (SRULE [] (Q.INST [`vals` |-> `[]:bytes32 list`]
        related_stack_next)) >> simp[]) >>
  irule (SRULE [] (Q.INST [`vals` |-> `[]:bytes32 list`]
    related_expanded_stack_next)) >> simp[]
QED

Theorem sym_step_concrete_sim:
  asm_sym_rel p env cs ss ∧
  name ≠ "JUMP" ∧ name ≠ "JUMPI" ∧ name ≠ "CODECOPY" ∧ name ≠ "CODESIZE" ∧
  ALOOKUP dup_table name = NONE ∧ ALOOKUP swap_table name = NONE ⇒
  asm_sym_step_rel p env (sym_step_concrete name ss)
    (asm_step_op (build_offset_to_pc p) name cs)
Proof
  strip_tac >>
  Cases_on `MEM name ["ADD"; "MUL"; "SUB"; "DIV"; "SDIV"; "MOD"; "SMOD"; "EXP";
    "LT"; "GT"; "SLT"; "SGT"; "EQ"; "AND"; "OR"; "XOR";
    "SHL"; "SHR"; "SAR"; "SIGNEXTEND"; "BYTE"]`
  >- (irule sym_step_pure_binary_sim >> simp[]) >>
  Cases_on `MEM name ["ISZERO"; "NOT"]`
  >- (irule sym_step_pure_unary_sim >> simp[]) >>
  Cases_on `MEM name ["ADDMOD"; "MULMOD"]`
  >- (irule sym_step_pure_ternary_sim >> simp[]) >>
  Cases_on `MEM name ["CALLER"; "ADDRESS"; "CALLVALUE"; "CALLDATASIZE"; "ORIGIN";
    "GASPRICE"; "CHAINID"; "COINBASE"; "TIMESTAMP"; "NUMBER";
    "PREVRANDAO"; "GASLIMIT"; "BASEFEE"; "BLOBBASEFEE";
    "SELFBALANCE"; "RETURNDATASIZE"; "MSIZE"]`
  >- (irule sym_step_context_push_sim >> simp[]) >>
  Cases_on `MEM name ["CALLDATALOAD"; "BLOCKHASH"; "BLOBHASH"; "BALANCE";
    "EXTCODESIZE"; "EXTCODEHASH"; "SLOAD"; "TLOAD"]`
  >- (irule sym_step_context_load_sim >> simp[]) >>
  Cases_on `MEM name ["SSTORE"; "TSTORE"]`
  >- (irule sym_step_store_sim >> simp[]) >>
  Cases_on `MEM name ["POP"; "JUMPDEST"; "STOP"; "INVALID"]`
  >- (irule sym_step_plain_control_sim >> simp[]) >>
  Cases_on `MEM name ["RETURN"; "REVERT"]`
  >- (irule sym_step_memory_terminal_sim >> simp[]) >>
  Cases_on `MEM name ["MSTORE"; "MSTORE8"]`
  >- (irule sym_step_memory_store_sim >> simp[]) >>
  Cases_on `MEM name ["CREATE"; "CREATE2"]`
  >- (irule sym_step_create_sim >> simp[]) >>
  Cases_on `MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "SELFDESTRUCT";
    "GAS"; "MLOAD"; "SHA3"; "CALLDATACOPY"; "EXTCODECOPY"; "MCOPY"; "RETURNDATACOPY"]`
  >- (qpat_x_assum `MEM name ("CALL" :: _)`
        (strip_assume_tac o REWRITE_RULE [MEM]) >>
      simp[sym_step_call_sim, sym_step_staticcall_sim,
        sym_step_delegatecall_sim, sym_step_selfdestruct_sim, sym_step_gas_sim,
        sym_step_mload_sim, sym_step_sha3_sim, sym_step_calldatacopy_sim,
        sym_step_extcodecopy_sim, sym_step_mcopy_sim, sym_step_returndatacopy_sim]) >>
  Cases_on `ALOOKUP log_table name`
  >- (gvs[MEM] >> irule sym_step_concrete_good >> simp[] >> rpt strip_tac >>
      simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def] >>
      simp[asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def] >>
      simp[asm_step_extcall_def, asm_step_copy_def, asm_step_context_def] >>
      simp[sym_lift_def, asm_sym_step_rel_def]) >>
  irule sym_step_log_sim >> simp[]
QED

(* ===== One step: the opcodes with label cases ===== *)

Theorem asm_sym_rel_pc:
  asm_sym_rel p env cs ss ⇒
  ss.sym_base.as_pc = cs.as_pc ∧ LENGTH ss.sym_stack = LENGTH cs.as_stack
Proof
  rw[asm_sym_rel_def] >> gvs[] >> metis_tac[LIST_REL_LENGTH]
QED

Theorem asm_sym_rel_stack_pc[local]:
  asm_sym_rel p env cs ss ∧
  LIST_REL (λsv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    stk cstk ⇒
  asm_sym_rel p env (cs with <| as_stack := cstk; as_pc := n |>)
    (ss with <| sym_base := ss.sym_base with as_pc := n; sym_stack := stk |>)
Proof
  rw[asm_sym_rel_def] >> gvs[] >> metis_tac[]
QED

Theorem asm_sym_rel_next[local]:
  asm_sym_rel p env cs ss ∧
  LIST_REL (λsv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    stk cstk ⇒
  asm_sym_step_rel p env (sym_set_stack stk ss)
    (AsmOK (asm_next (cs with as_stack := cstk)))
Proof
  rw[sym_set_stack_def, asm_sym_step_rel_def, asm_next_def] >>
  drule asm_sym_rel_pc >> strip_tac >>
  drule_all asm_sym_rel_stack_pc >>
  disch_then (qspec_then `cs.as_pc + 1` mp_tac) >> simp[]
QED

Theorem sval_conc_add[local]:
  sval_conc lo (Lab l d) = SOME a ∧ sym_delta_ok (d + w2n w) ⇒
  sval_conc lo (Lab l (d + w2n w)) = SOME (a + w)
Proof
  simp[sval_conc_def] >>
  Cases_on `sym_delta_ok d` >> simp[] >>
  Cases_on `FLOOKUP lo l` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n,
       arithmeticTheory.ADD_ASSOC, wordsTheory.WORD_ADD_ASSOC]
QED

Theorem sym_add_sim:
  asm_sym_rel p env cs ss ⇒
  asm_sym_step_rel p env (sym_add p env ss)
    (asm_step_op (build_offset_to_pc p) "ADD" cs)
Proof
  strip_tac >>
  `asm_sym_step_rel p env (sym_step_concrete "ADD" ss)
     (asm_step_op (build_offset_to_pc p) "ADD" cs)` by
    (irule sym_step_concrete_sim >> simp[dup_table_def, swap_table_def]) >>
  `LIST_REL (λsv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
     ss.sym_stack cs.as_stack` by fs[asm_sym_rel_def] >>
  Cases_on `ss.sym_stack` >- gvs[sym_add_def] >>
  Cases_on `t` >- (Cases_on `h` >> gvs[sym_add_def]) >>
  Cases_on `h` >> Cases_on `h'` >> gvs[sym_add_def] >>
  rw[sym_push_lab_def, asm_sym_step_rel_def] >>
  gvs[LIST_REL_CONS1, CONJUNCT1 sval_conc_def] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_binop_def] >>
  irule asm_sym_rel_next >> simp[] >>
  metis_tac[sval_conc_add, wordsTheory.WORD_ADD_COMM]
QED

Theorem mstore_labels_lookup:
  !n L a l d i.
  FLOOKUP (L |++ GENLIST (\j. (a+j,(l,d,j))) n) i =
    if a <= i /\ i < a+n then SOME (l,d,i-a) else FLOOKUP L i
Proof
  Induct >- simp[finite_mapTheory.FUPDATE_LIST_THM] >>
  rpt gen_tac >> simp[GENLIST, finite_mapTheory.FUPDATE_LIST_SNOC,
                         finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `i = a+n` >- simp[] >>
  Cases_on `a <= i /\ i < a+n` >> simp[] >>
  gvs[] >> `~(a <= i /\ i < a+SUC n)` by decide_tac >> simp[]
QED

Theorem mstore_bytes_length[local]:
  LENGTH (TAKE a (asm_expand_memory (a+32) m) ++
    word_to_bytes (v:bytes32) T ++ DROP (a+32) (asm_expand_memory (a+32) m)) =
  LENGTH (asm_expand_memory (a+32) m)
Proof
  qspecl_then [`a+32`, `m`] assume_tac asm_expand_memory_length >>
  simp[LENGTH_TAKE, LENGTH_DROP] >> decide_tac
QED

Theorem mstore_bytes_inside[local]:
  j < 32 ==>
  EL (a+j) (TAKE a (asm_expand_memory (a+32) m) ++
    word_to_bytes (v:bytes32) T ++ DROP (a+32) (asm_expand_memory (a+32) m)) =
  EL j (word_to_bytes v T)
Proof
  strip_tac >>
  qspecl_then [`a+32`, `m`] assume_tac asm_expand_memory_length >>
  qspecl_then [`a`, `word_to_bytes v T`, `asm_expand_memory (a+32) m`, `a+j`]
    mp_tac EL_splice_inside >>
  simp[byteTheory.LENGTH_word_to_bytes]
QED

Theorem mstore_bytes_outside[local]:
  i < LENGTH (asm_expand_memory (a+32) m) /\ ~(a <= i /\ i < a+32) ==>
  EL i (TAKE a (asm_expand_memory (a+32) m) ++
    word_to_bytes (v:bytes32) T ++ DROP (a+32) (asm_expand_memory (a+32) m)) =
  EL i (asm_expand_memory (a+32) m)
Proof
  strip_tac >>
  qspecl_then [`a+32`, `m`] assume_tac asm_expand_memory_length >>
  qspecl_then [`a`, `word_to_bytes v T`, `asm_expand_memory (a+32) m`, `i`]
    mp_tac EL_splice_outside >>
  simp[byteTheory.LENGTH_word_to_bytes]
QED

Theorem mstore_expansion_equal[local]:
  LENGTH m = LENGTH n /\ i < LENGTH (asm_expand_memory k n) /\
  (i < LENGTH n ==> EL i m = EL i n) ==>
  EL i (asm_expand_memory k m) = EL i (asm_expand_memory k n)
Proof
  rw[asm_expand_memory_def] >>
  Cases_on `i < LENGTH n` >> gvs[EL_APPEND_EQN, rich_listTheory.EL_REPLICATE]
QED

Theorem mstore_label_sim[local]:
  asm_sym_rel p env cs ss /\ ss.sym_stack = Val off :: Lab l d :: stk ==>
  asm_sym_step_rel p env
    (sym_lift 2 (ss.sym_mem_labels |++
       GENLIST (\i. (w2n off+i,(l,d,i))) 32) ss
       (asm_mstore (ss.sym_base with as_stack := [off;0w])))
    (asm_mstore cs)
Proof
  strip_tac >>
  `LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
      ss.sym_stack cs.as_stack` by fs[asm_sym_rel_def] >>
  gvs[LIST_REL_CONS1, sval_conc_def] >>
  qmatch_goalsub_abbrev_tac `sym_lift 2 labs` >>
  `!i. FLOOKUP labs i = if w2n off <= i /\ i < w2n off+32
       then SOME (l,d,i-w2n off) else FLOOKUP ss.sym_mem_labels i`
    by (qspec_then `32` (qspecl_then [`ss.sym_mem_labels`, `w2n off`, `l`, `d`] mp_tac)
          mstore_labels_lookup >> simp[Abbr `labs`]) >>
  simp[asm_mstore_def, sym_lift_def, asm_next_def, asm_sym_step_rel_def,
       Excl "GENLIST", Excl "LENGTH_APPEND"] >>
  fs[asm_sym_rel_def, Excl "GENLIST", Excl "LENGTH_APPEND"] >>
  simp[asm_sym_rel_def, Excl "GENLIST", Excl "LENGTH_APPEND"] >>
  conj_tac
  >- (qexists `TAKE (w2n off) (asm_expand_memory (w2n off+32) m) ++
        word_to_bytes (0w:bytes32) T ++
        DROP (w2n off+32) (asm_expand_memory (w2n off+32) m)` >>
      simp[mstore_bytes_length, expand_memory_lengths, Excl "GENLIST",
           Excl "LENGTH_APPEND"] >>
      rpt strip_tac >>
      `FLOOKUP labs i = NONE` by metis_tac[finite_mapTheory.FLOOKUP_DEF] >>
      `~(w2n off <= i /\ i < w2n off+32) /\ i NOTIN FDOM ss.sym_mem_labels`
        by (qpat_x_assum `!i. FLOOKUP labs i = _` (qspec_then `i` mp_tac) >>
            simp[] >> simp[finite_mapTheory.FLOOKUP_DEF]) >>
      `i < LENGTH (asm_expand_memory (w2n off+32) m)`
        by metis_tac[expand_memory_lengths] >>
      simp[mstore_bytes_outside] >>
      irule mstore_expansion_equal >> simp[]) >>
  rpt gen_tac >>
  Cases_on `w2n off <= i /\ i < w2n off+32`
  >- (simp[] >> strip_tac >> gvs[] >>
      `i = w2n off + (i-w2n off)` by decide_tac >>
      `i-w2n off < 32` by decide_tac >>
      qspecl_then [`w2n off+32`, `cs.as_memory`] assume_tac asm_expand_memory_length >>
      simp[mstore_bytes_length, Excl "LENGTH_APPEND"] >>
      metis_tac[mstore_bytes_inside]) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!i l d j. FLOOKUP ss.sym_mem_labels i = _ ==> _` drule >>
  strip_tac >>
  `i < LENGTH (asm_expand_memory (w2n off+32) cs.as_memory)`
    by (simp[asm_expand_memory_def] >> IF_CASES_TAC >> simp[]) >>
  simp[mstore_bytes_length, mstore_bytes_outside, Excl "LENGTH_APPEND"] >>
  conj_tac
  >- (qspecl_then [`w2n off+32`, `cs.as_memory`] assume_tac asm_expand_memory_length >>
      simp[LENGTH_TAKE] >> decide_tac) >>
  simp[asm_expand_memory_def] >> IF_CASES_TAC >> simp[EL_APPEND_EQN]
QED

Theorem sym_mstore_sim:
  asm_sym_rel p env cs ss ⇒
  asm_sym_step_rel p env (sym_mstore ss)
    (asm_step_op (build_offset_to_pc p) "MSTORE" cs)
Proof
  strip_tac >>
  `asm_sym_step_rel p env (sym_step_concrete "MSTORE" ss)
     (asm_step_op (build_offset_to_pc p) "MSTORE" cs)`
    by (irule sym_step_concrete_sim >> simp[dup_table_def, swap_table_def]) >>
  Cases_on `ss.sym_stack` >- simp[sym_mstore_def] >>
  Cases_on `t` >- simp[sym_mstore_def] >>
  Cases_on `h` >> Cases_on `h'` >> simp[sym_mstore_def] >>
  drule_all mstore_label_sim >> simp[asm_step_op_mstore]
QED

Theorem mem_label_at_bytes[local]:
  mem_label_at labs off = SOME (l,d) ==>
  !i. i < 32 ==> FLOOKUP labs (off+i) = SOME (l,d,i)
Proof
  rw[mem_label_at_def, AllCaseEqs()] >>
  gvs[EVERY_MEM, rich_listTheory.MEM_COUNT_LIST] >> metis_tac[]
QED

Theorem mload_label_value[local]:
  asm_sym_rel p env cs ss /\
  mem_label_at ss.sym_mem_labels off = SOME (l,d) ==>
  ?w. sval_conc (SND (compute_label_offsets p)) (Lab l d) = SOME w /\
      word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP off (asm_expand_memory (off+32) cs.as_memory))) = w
Proof
  strip_tac >>
  drule mem_label_at_bytes >> strip_tac >>
  `!i. i < 32 ==> off+i < LENGTH cs.as_memory /\
       ?w. sval_conc (SND (compute_label_offsets p)) (Lab l d) = SOME w /\
           EL (off+i) cs.as_memory = EL i (word_to_bytes w T)`
    by (rpt strip_tac >> fs[asm_sym_rel_def] >> metis_tac[]) >>
  first_assum (qspec_then `0` assume_tac) >>
  gvs[Excl "word_of_bytes_def"] >>
  `off+32 <= LENGTH cs.as_memory`
    by (first_x_assum (qspec_then `31` mp_tac) >> simp[]) >>
  `TAKE 32 (DROP off (asm_expand_memory (off+32) cs.as_memory)) =
     word_to_bytes w T` suffices_by
       simp[byteTheory.word_of_bytes_word_to_bytes] >>
  simp[asm_expand_memory_def] >> IF_CASES_TAC >> simp[] >>
  irule LIST_EQ >>
  simp[LENGTH_TAKE, LENGTH_DROP, EL_TAKE, EL_DROP, EL_APPEND_EQN] >>
  rpt strip_tac >> res_tac >> fs[]
QED

Theorem asm_sym_rel_expand[local]:
  asm_sym_rel p env cs ss ==>
  asm_sym_rel p env (cs with as_memory := asm_expand_memory n cs.as_memory)
    (ss with sym_base := ss.sym_base with as_memory :=
       asm_expand_memory n ss.sym_base.as_memory)
Proof
  rw[asm_sym_rel_def] >> gvs[]
  >- (qexists_tac `asm_expand_memory n m` >>
      simp[asm_expand_memory_def] >> IF_CASES_TAC >> simp[] >>
      rpt strip_tac >> simp[EL_APPEND_EQN] >>
      Cases_on `i < LENGTH cs.as_memory` >> simp[])
  >> qpat_x_assum `!i l d j. _` drule >> strip_tac >>
  simp[asm_expand_memory_def] >>
  Cases_on `32 * ((n+31) DIV 32) <= LENGTH cs.as_memory` >>
  simp[EL_APPEND_EQN] >> metis_tac[]
QED

Theorem sym_mload_sim:
  asm_sym_rel p env cs ss ⇒
  asm_sym_step_rel p env (sym_mload ss)
    (asm_step_op (build_offset_to_pc p) "MLOAD" cs)
Proof
  strip_tac >>
  `asm_sym_step_rel p env (sym_step_concrete "MLOAD" ss)
     (asm_step_op (build_offset_to_pc p) "MLOAD" cs)`
    by (irule sym_step_concrete_sim >>
        simp[dup_table_def, swap_table_def]) >>
  Cases_on `ss.sym_stack` >> simp[sym_mload_def] >>
  Cases_on `h` >> simp[sym_mload_def] >>
  Cases_on `mem_label_at ss.sym_mem_labels (w2n c)` >>
  simp[] >> PairCases_on `x` >> simp[] >>
  drule_all mload_label_value >> strip_tac >>
  `LIST_REL (\sv cw. sval_conc (SND (compute_label_offsets p)) sv = SOME cw)
     ss.sym_stack cs.as_stack` by fs[asm_sym_rel_def] >>
  gvs[LIST_REL_CONS1, sval_conc_def] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_mload_def,
       asm_sym_step_rel_def] >>
  drule asm_sym_rel_expand >>
  disch_then (qspec_then `w2n c + 32` assume_tac) >>
  `ss.sym_base.as_pc = cs.as_pc` by (fs[asm_sym_rel_def] >> gvs[]) >>
  qpat_x_assum `asm_sym_rel _ _ (_ with as_memory := _) _` mp_tac >>
  simp[asm_next_def] >>
  strip_tac >>
  `LIST_REL (\sv cw. sval_conc (SND (compute_label_offsets p)) sv = SOME cw)
      (Lab x0 x1 :: t) (n2w (off+x1) :: t')` by simp[sval_conc_def] >>
  qpat_x_assum `LIST_REL _ t t'` kall_tac >>
  qpat_x_assum `asm_sym_rel p env cs ss` kall_tac >>
  drule_all asm_sym_rel_stack_pc >>
  disch_then (qspec_then `cs.as_pc+1` mp_tac) >> simp[]
QED

(* asm_static_wf bounds label offsets (asm_encoding_wf), so a data label's
   concrete address off + d doesn't wrap. *)
Theorem sym_codecopy_address[local]:
  asm_static_wf p /\ asm_data_env_ok p env code /\
  sym_data_label p env l /\
  sval_conc (SND (compute_label_offsets p)) (Lab l d) = SOME w ==>
  ?off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
        env ' l = DROP off code /\ w2n w = off + d
Proof
  strip_tac >>
  fs[asm_data_env_ok_def] >>
  first_x_assum drule >> strip_tac >>
  `off < 65536` by
    (gvs[asm_static_wf_def, asm_encoding_wf_def, pairTheory.UNCURRY] >>
     qpat_x_assum `!lbl off. FLOOKUP _ lbl = SOME off ==> _` drule >>
     simp[symbol_size_def] >> strip_tac >>
     drule encode_num_bytes_length_bound >> simp[]) >>
  gvs[sval_conc_def, sym_delta_ok_def] >>
  `off + d < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  simp[arithmeticTheory.LESS_MOD]
QED

Theorem sym_codecopy_slice[local]:
  TAKE n (if n = 0 then DROP a xs else asm_expand_memory n (DROP a xs)) =
  TAKE n (DROP a (if n = 0 then xs else asm_expand_memory (a+n) xs))
Proof
  Cases_on `n = 0` >- simp[] >>
  simp[] >> irule LIST_EQ >>
  simp[LENGTH_TAKE, LENGTH_DROP] >>
  reverse conj_tac
  >- (mp_tac (Q.SPECL [`a+n`, `xs`] asm_expand_memory_length) >>
      strip_tac >> simp[LENGTH_TAKE_EQ, LENGTH_DROP] >> decide_tac) >>
  rpt strip_tac >>
  `a+n <= LENGTH (asm_expand_memory (a+n) xs)` by simp[] >>
  `x+a < LENGTH (asm_expand_memory (a+n) xs)` by decide_tac >>
  simp[EL_TAKE, EL_DROP] >>
  mp_tac (Q.SPEC `n` n_le_round_up_32) >>
  mp_tac (Q.SPEC `a+n` n_le_round_up_32) >>
  rpt strip_tac >>
  simp[asm_expand_memory_def] >>
  rpt IF_CASES_TAC >>
  gvs[EL_APPEND_EQN, EL_DROP, LENGTH_DROP] >>
  rpt IF_CASES_TAC >>
  gvs[rich_listTheory.EL_REPLICATE]
QED

Theorem sym_copy_write[local]:
  !b n a m. LENGTH b = n /\ (n = 0 \/ a+n <= LENGTH m) ==>
  LENGTH (TAKE a m ++ b ++ DROP (a+n) m) = LENGTH m /\
  (!i. i < LENGTH m ==>
    EL i (TAKE a m ++ b ++ DROP (a+n) m) =
    if a <= i /\ i < a+n then EL (i-a) b else EL i m)
Proof
  rpt gen_tac >> disch_tac >> Cases_on `n = 0`
  >- (`b = []` by fs[] >>
      pure_asm_rewrite_tac[APPEND, APPEND_NIL, arithmeticTheory.ADD_CLAUSES, TAKE_DROP] >> simp[]) >>
  gvs[] >>
  `a <= LENGTH m` by decide_tac >>
  simp[LENGTH_TAKE, LENGTH_DROP] >>
  rpt strip_tac >>
  simp[EL_APPEND_EQN, LENGTH_TAKE, EL_TAKE, EL_DROP] >>
  rpt IF_CASES_TAC >> gvs[] >>
  `i - a - LENGTH b + (a+LENGTH b) = i` by decide_tac >> simp[]
QED

Theorem sym_copy_preserves[local]:
  asm_sym_rel p env cs ss /\
  ss.sym_stack = Val dst :: sv :: Val sz :: stk /\
  cs.as_stack = dst :: w :: sz :: rest /\
  TAKE (w2n sz) (if w2n sz = 0 then src else asm_expand_memory (w2n sz) src) =
  TAKE (w2n sz) (DROP (w2n w) (if w2n sz = 0 then cs.as_code
    else asm_expand_memory (w2n w + w2n sz) cs.as_code)) ==>
  asm_sym_step_rel p env
    (sym_lift 3 (mem_labels_clear ss.sym_mem_labels
      (in_mem_range (w2n dst) (w2n sz))) ss
      (asm_copy_to_mem src (ss.sym_base with as_stack := [dst;0w;sz])))
    (asm_copy_to_mem cs.as_code cs)
Proof
  strip_tac >>
  gvs[asm_copy_to_mem_def, sym_lift_def, asm_sym_step_rel_def] >>
  gvs[asm_sym_rel_def, asm_next_def] >>
  Cases_on `sz = 0w`
  >- (gvs[mem_labels_clear_def, in_mem_range_def] >>
      pure_rewrite_tac[TAKE_DROP] >>
      simp[LENGTH_TAKE_EQ, finite_mapTheory.DRESTRICT_UNIV, GSYM pred_setTheory.UNIV_DEF] >>
      conj_tac >- (qexists_tac `m` >> simp[]) >>
      rpt strip_tac >>
      qpat_x_assum `!i l d j. _` drule >> strip_tac >>
      IF_CASES_TAC >> simp[] >> decide_tac) >>
  qabbrev_tac `em = asm_expand_memory (w2n dst + w2n sz) m` >>
  qabbrev_tac `ec = asm_expand_memory (w2n dst + w2n sz) cs.as_memory` >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `TAKE (w2n dst) em ++ bytes ++ DROP _ em` >>
  `LENGTH bytes = w2n sz` by
    (simp[Abbr `bytes`, LENGTH_TAKE_EQ, LENGTH_DROP] >>
     mp_tac (Q.SPECL [`w2n (sz:bytes32) + w2n (w:bytes32)`, `cs.as_code`] asm_expand_memory_length) >>
     strip_tac >> simp[] >> decide_tac) >>
  `w2n dst + w2n sz <= LENGTH em /\ LENGTH em = LENGTH ec` by
    (simp[Abbr `em`, Abbr `ec`, asm_expand_memory_def] >>
     mp_tac (Q.SPEC `w2n dst + w2n sz` n_le_round_up_32) >>
     rpt IF_CASES_TAC >> gvs[] >> decide_tac) >>
  qspecl_then [`bytes`, `w2n sz`, `w2n dst`, `em`] mp_tac sym_copy_write >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`bytes`, `w2n sz`, `w2n dst`, `ec`] mp_tac sym_copy_write >>
  impl_tac >- simp[] >> strip_tac >>
  `LENGTH (TAKE (w2n dst) ec) + LENGTH bytes +
    (LENGTH ec - (w2n dst + w2n sz)) = LENGTH ec` by fs[] >>
  simp[] >> conj_tac
  >- (qexists_tac `TAKE (w2n dst) em ++ bytes ++ DROP (w2n dst + w2n sz) em` >>
      simp[] >> rpt strip_tac >> simp[] >>
      Cases_on `w2n dst <= i /\ i < w2n dst + w2n sz` >> simp[] >>
      fs[mem_labels_clear_def, finite_mapTheory.FDOM_DRESTRICT, in_mem_range_def,
         pred_setTheory.IN_INTER, pred_setTheory.SPECIFICATION] >>
      simp[Abbr `em`, Abbr `ec`, el_expand_read_byte] >>
      Cases_on `i < LENGTH cs.as_memory` >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[mem_labels_clear_def, finite_mapTheory.FLOOKUP_DRESTRICT, in_mem_range_def,
      pred_setTheory.SPECIFICATION] >>
  qpat_x_assum `!i l d j. _` drule >> strip_tac >>
  `LENGTH cs.as_memory <= LENGTH ec` by
    (simp[Abbr `ec`, asm_expand_memory_def] >> IF_CASES_TAC >> simp[]) >>
  `i < LENGTH ec` by decide_tac >>
  simp[] >>
  `ec❲i❳ = cs.as_memory❲i❳` by simp[Abbr `ec`, el_expand_read_byte] >>
  metis_tac[]
QED

Theorem sym_codecopy_sim:
  asm_static_wf p ∧ asm_sym_rel p env cs ss ⇒
  asm_sym_step_rel p env (sym_codecopy p env ss)
    (asm_step_op (build_offset_to_pc p) "CODECOPY" cs)
Proof
  strip_tac >>
  `LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    ss.sym_stack cs.as_stack` by fs[asm_sym_rel_def] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def, asm_step_copy_def] >>
  Cases_on `ss.sym_stack` >> Cases_on `cs.as_stack` >> gvs[]
  >- simp[sym_codecopy_def, asm_copy_to_mem_def, asm_sym_step_rel_def] >>
  Cases_on `t` >> Cases_on `t'` >> gvs[]
  >- simp[sym_codecopy_def, asm_copy_to_mem_def, asm_sym_step_rel_def] >>
  rename1 `ss.sym_stack = a::b::tail` >>
  rename1 `cs.as_stack = ca::cb::ctail` >>
  Cases_on `tail` >> Cases_on `ctail` >> gvs[]
  >- (Cases_on `a` >> Cases_on `b` >>
      simp[sym_codecopy_def, asm_copy_to_mem_def, asm_sym_step_rel_def]) >>
  rename1 `ss.sym_stack = a::b::c::stk` >>
  Cases_on `a` >> Cases_on `b` >> Cases_on `c` >>
  gvs[sym_codecopy_def, asm_sym_step_rel_def] >>
  reverse IF_CASES_TAC >- simp[asm_sym_step_rel_def] >>
  `asm_data_env_ok p env cs.as_code` by fs[asm_sym_rel_def] >>
  drule_all sym_codecopy_address >> strip_tac >>
  gvs[sval_conc_def] >>
  irule sym_copy_preserves >> simp[] >>
  simp[rich_listTheory.DROP_DROP_T] >>
  Cases_on `c'' = 0w` >- simp[] >>
  mp_tac (Q.INST [`n` |-> `w2n (c'':bytes32)`, `a` |-> `n+off`,
                  `xs` |-> `cs.as_code`] sym_codecopy_slice) >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >> simp[]
QED

(* ===== Helpers ===== *)

Theorem asm_step_op_jump[local]:
  asm_step_op otp "JUMP" s = asm_jump otp s ∧
  asm_step_op otp "JUMPI" s = asm_jumpi otp s
Proof
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def]
QED

Theorem ALL_DISTINCT_FILTER_IS_SOME_EL[local]:
  ∀ls i j. ALL_DISTINCT (FILTER IS_SOME ls) ∧ i < j ∧ j < LENGTH ls ∧
           EL i ls = EL j ls ⇒ EL i ls = NONE
Proof
  Induct >- simp[] >> rpt strip_tac >>
  `ALL_DISTINCT (FILTER IS_SOME ls) ∧ (IS_SOME h ⇒ ¬MEM h ls)`
    by (Cases_on `IS_SOME h` >> gvs[MEM_FILTER]) >>
  qpat_x_assum `ALL_DISTINCT (FILTER _ (_ :: _))` kall_tac >>
  Cases_on `i` >> Cases_on `j` >> gvs[MEM_EL] >>
  metis_tac[optionTheory.NOT_IS_SOME_EQ_NONE]
QED

(* A code label's offset fits a PUSH2 and maps back to the label. *)
Theorem asm_static_wf_code_label:
  asm_static_wf p ∧ INDEX_OF (AsmLabel l) p = SOME i ⇒
  ∃off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off ∧
        off < 65536 ∧ FLOOKUP (build_offset_to_pc p) off = SOME i
Proof
  rw[INDEX_OF_eq_SOME] >>
  `FLOOKUP (SND (compute_label_offsets p)) l = SOME (asm_pc_to_offset p i)`
    by (irule label_offset_consistent_proof >> rw[]
        >- (strip_tac >> gvs[asm_static_wf_def, asm_labels_unique_def] >>
            qspecl_then [`MAP (λinst. case inst of AsmLabel l => SOME l
                                                 | _ => NONE) p`, `i`, `j`]
              mp_tac ALL_DISTINCT_FILTER_IS_SOME_EL >>
            simp[EL_MAP])
        >- (strip_tac >> gvs[asm_static_wf_def] >>
            `MEM (EL i p) p ∧ MEM (EL j p) p` by simp[EL_MEM] >>
            gvs[] >> metis_tac[])) >>
  simp[] >> conj_tac
  >- (gvs[asm_static_wf_def, asm_encoding_wf_def, pairTheory.UNCURRY] >>
      qpat_x_assum `∀lbl off. FLOOKUP _ lbl = SOME off ⇒ _` drule >>
      simp[symbol_size_def] >> strip_tac >>
      drule encode_num_bytes_length_bound >> simp[]) >>
  irule offset_to_pc_inverse_proof >> simp[asm_inst_size_def]
QED

(* ===== One step: the jumps ===== *)

Theorem sym_jump_dest_conc[local]:
  asm_static_wf p ∧ sym_jump_dest p dest = SOME i ∧
  sval_conc (SND (compute_label_offsets p)) dest = SOME w ⇒
  FLOOKUP (build_offset_to_pc p) (w2n w) = SOME i
Proof
  Cases_on `dest` >> rw[sym_jump_dest_def] >>
  drule_all asm_static_wf_code_label >> strip_tac >>
  gvs[sval_conc_def] >>
  `65536 < dimword (:256)` by simp[wordsTheory.dimword_def] >> simp[arithmeticTheory.LESS_MOD]
QED

Theorem sym_jump_sim:
  asm_static_wf p ∧ asm_sym_rel p env cs ss ⇒
  asm_sym_step_rel p env (sym_jump p ss)
    (asm_step_op (build_offset_to_pc p) "JUMP" cs)
Proof
  strip_tac >>
  `LIST_REL (λsv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
     ss.sym_stack cs.as_stack` by fs[asm_sym_rel_def] >>
  simp[sym_jump_def, asm_step_op_jump, asm_jump_def] >>
  Cases_on `ss.sym_stack` >> gvs[asm_sym_step_rel_def, LIST_REL_CONS1] >>
  Cases_on `sym_jump_dest p h` >> simp[asm_sym_step_rel_def] >>
  drule_all sym_jump_dest_conc >> simp[] >> strip_tac >>
  drule_all asm_sym_rel_stack_pc >> simp[]
QED

Theorem sym_jumpi_sim:
  asm_static_wf p ∧ asm_sym_rel p env cs ss ⇒
  asm_sym_step_rel p env (sym_jumpi p ss)
    (asm_step_op (build_offset_to_pc p) "JUMPI" cs)
Proof
  strip_tac >>
  `LIST_REL (λsv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
     ss.sym_stack cs.as_stack` by fs[asm_sym_rel_def] >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[asm_sym_rel_pc] >>
  simp[sym_jumpi_def, asm_step_op_jump, asm_jumpi_def] >>
  Cases_on `ss.sym_stack` >> gvs[asm_sym_step_rel_def, LIST_REL_CONS1] >>
  Cases_on `t` >> gvs[asm_sym_step_rel_def, LIST_REL_CONS1] >>
  rename1 `sval_conc _ c = SOME cw` >>
  Cases_on `c` >> gvs[sval_conc_def, asm_sym_step_rel_def] >>
  rw[sym_set_stack_def, asm_sym_step_rel_def, asm_next_def]
  >- (drule_all asm_sym_rel_stack_pc >> simp[]) >>
  Cases_on `sym_jump_dest p h` >> simp[asm_sym_step_rel_def] >>
  drule_all sym_jump_dest_conc >> simp[] >> strip_tac >>
  drule_all asm_sym_rel_stack_pc >> simp[]
QED

(* ===== One step: stack-only opcodes ===== *)

Theorem asm_step_op_pop[local]:
  asm_step_op otp "POP" s = asm_pop s
Proof
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def]
QED

Theorem asm_step_op_dup[local]:
  ALOOKUP dup_table name = SOME n ⇒ asm_step_op otp name s = asm_dup n s
Proof
  simp[dup_table_def] >> rpt (IF_CASES_TAC >> simp[]) >> strip_tac >>
  gvs[] >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def, asm_step_copy_def, asm_step_context_def,
       dup_table_def]
QED

Theorem asm_step_op_swap[local]:
  ALOOKUP swap_table name = SOME n ⇒ asm_step_op otp name s = asm_swap n s
Proof
  simp[swap_table_def] >> rpt (IF_CASES_TAC >> simp[]) >> strip_tac >>
  gvs[] >>
  simp[asm_step_op_def] >>
  simp[asm_step_arith_def] >> simp[asm_step_compare_def] >>
  simp[asm_step_bitwise_def] >> simp[asm_step_memory_def] >>
  simp[asm_step_control_def] >> simp[asm_step_extcall_def] >>
  simp[asm_step_copy_def] >> simp[asm_step_context_def] >>
  simp[dup_table_def, swap_table_def]
QED

Theorem sym_pop_sim[local]:
  asm_sym_rel p env cs ss ⇒
  asm_sym_step_rel p env (sym_step_op p env "POP" ss)
    (asm_step_op otp "POP" cs)
Proof
  strip_tac >>
  `LIST_REL (λsv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
     ss.sym_stack cs.as_stack` by fs[asm_sym_rel_def] >>
  simp[sym_step_op_def, asm_step_op_pop, asm_pop_def] >>
  Cases_on `ss.sym_stack` >> gvs[asm_sym_step_rel_def, LIST_REL_CONS1] >>
  irule asm_sym_rel_next >> simp[]
QED

Theorem sym_dup_sim[local]:
  asm_sym_rel p env cs ss ∧ ALOOKUP dup_table name = SOME n ⇒
  asm_sym_step_rel p env (sym_dup n ss) (asm_step_op otp name cs)
Proof
  strip_tac >> drule_then (fn th => simp[th]) asm_step_op_dup >>
  `LIST_REL (λsv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
     ss.sym_stack cs.as_stack` by fs[asm_sym_rel_def] >>
  drule asm_sym_rel_pc >> strip_tac >>
  simp[sym_dup_def, asm_dup_def] >>
  IF_CASES_TAC >> simp[asm_sym_step_rel_def] >>
  `sval_conc (SND (compute_label_offsets p)) (EL n ss.sym_stack) =
   SOME (EL n cs.as_stack)` by fs[LIST_REL_EL_EQN] >>
  irule asm_sym_rel_next >> simp[]
QED

Theorem LIST_REL_swap[local]:
  LIST_REL R l1 l2 ∧ n < LENGTH l1 ∧ 0 < n ⇒
  LIST_REL R (LUPDATE (HD l1) n (LUPDATE (EL n l1) 0 l1))
             (LUPDATE (HD l2) n (LUPDATE (EL n l2) 0 l2))
Proof
  strip_tac >> irule EVERY2_LUPDATE_same >> conj_tac
  >- (Cases_on `l1` >> Cases_on `l2` >> gvs[]) >>
  irule EVERY2_LUPDATE_same >> fs[LIST_REL_EL_EQN]
QED

Theorem sym_swap_sim[local]:
  asm_sym_rel p env cs ss ∧ ALOOKUP swap_table name = SOME n ⇒
  asm_sym_step_rel p env (sym_swap n ss) (asm_step_op otp name cs)
Proof
  strip_tac >> drule_then (fn th => simp[th]) asm_step_op_swap >>
  `LIST_REL (λsv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
     ss.sym_stack cs.as_stack` by fs[asm_sym_rel_def] >>
  drule asm_sym_rel_pc >> strip_tac >>
  simp[sym_swap_def, asm_swap_def] >>
  IF_CASES_TAC >> simp[asm_sym_step_rel_def] >>
  irule asm_sym_rel_next >> simp[] >>
  irule LIST_REL_swap >> simp[]
QED

(* ===== One step ===== *)

Theorem asm_sym_op_step[local]:
  asm_static_wf p ∧ asm_sym_rel p env cs ss ⇒
  asm_sym_step_rel p env (sym_step_op p env name ss)
    (asm_step_op (build_offset_to_pc p) name cs)
Proof
  strip_tac >>
  Cases_on `name = "POP"` >- (gvs[] >> irule sym_pop_sim >> simp[]) >>
  Cases_on `name = "JUMP"`
  >- (simp[sym_step_op_def] >> irule sym_jump_sim >> simp[]) >>
  Cases_on `name = "JUMPI"`
  >- (simp[sym_step_op_def] >> irule sym_jumpi_sim >> simp[]) >>
  Cases_on `name = "ADD"`
  >- (simp[sym_step_op_def] >> irule sym_add_sim >> simp[]) >>
  Cases_on `name = "MSTORE"`
  >- (simp[sym_step_op_def] >> irule sym_mstore_sim >> simp[]) >>
  Cases_on `name = "MLOAD"`
  >- (simp[sym_step_op_def] >> irule sym_mload_sim >> simp[]) >>
  Cases_on `name = "CODECOPY"`
  >- (simp[sym_step_op_def] >> irule sym_codecopy_sim >> simp[]) >>
  Cases_on `name = "CODESIZE"`
  >- simp[sym_step_op_def, asm_sym_step_rel_def] >>
  simp[sym_step_op_def] >>
  Cases_on `ALOOKUP dup_table name` >> simp[]
  >- (Cases_on `ALOOKUP swap_table name` >> simp[]
      >- (irule sym_step_concrete_sim >> simp[]) >>
      irule sym_swap_sim >> simp[]) >>
  irule sym_dup_sim >> simp[]
QED

(* Every label a push refers to has an offset. *)
Theorem clo_FDOM[local]:
  ∀prog off0 (labels0:string|->num).
    l ∈ FDOM labels0 ∨ MEM (AsmLabel l) prog ∨ MEM (AsmDataHeader l) prog ⇒
    l ∈ FDOM (SND (FOLDL (λ(pc:num,labels:string|->num) inst.
                     (pc + asm_inst_size inst,
                      case inst of
                        AsmLabel lbl => labels |+ (lbl, pc)
                      | AsmDataHeader lbl' => labels |+ (lbl', pc)
                      | _ => labels))
              (off0, labels0) prog))
Proof
  Induct >- simp[] >> strip_tac >> Cases_on `h` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> gvs[]
QED

Theorem asm_label_ref_defined[local]:
  asm_static_wf p ∧ (MEM (AsmPushLabel l) p ∨ MEM (AsmPushOfst l d) p) ⇒
  ∃off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off
Proof
  rpt strip_tac >>
  `MEM (AsmLabel l) p ∨ MEM (AsmDataHeader l) p`
    by (fs[asm_static_wf_def] >> first_x_assum irule >>
        simp[asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        first_assum (irule_at Any) >> simp[]) >>
  `l ∈ FDOM (SND (compute_label_offsets p))`
    by (simp[compute_label_offsets_def, clo_step_eq] >> irule clo_FDOM >>
        simp[]) >>
  gvs[finite_mapTheory.FLOOKUP_DEF]
QED

Theorem asm_sym_inst_step[local]:
  asm_static_wf p ∧ asm_sym_rel p env cs ss ∧ MEM inst p ⇒
  asm_sym_step_rel p env (sym_step p env inst ss)
    (asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p) inst cs)
Proof
  strip_tac >>
  `sym_delta_ok 0` by simp[sym_delta_ok_def, wordsTheory.dimword_def] >>
  Cases_on `inst` >> simp[sym_step_def, asm_step_def]
  >~ [`AsmOp name`] >- (irule asm_sym_op_step >> simp[])
  >~ [`AsmPushLabel l`]
  >- (`∃off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off`
        by metis_tac[asm_label_ref_defined] >>
      simp[] >> irule asm_sym_rel_next >> simp[sval_conc_def] >>
      fs[asm_sym_rel_def])
  >~ [`AsmPushOfst l d`]
  >- (`∃off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off`
        by metis_tac[asm_label_ref_defined] >>
      simp[sym_push_lab_def] >>
      IF_CASES_TAC >> simp[asm_sym_step_rel_def] >>
      irule asm_sym_rel_next >> simp[sval_conc_def] >>
      fs[asm_sym_rel_def]) >>
  gvs[sym_lift_def, asm_sym_step_rel_def, asm_next_def, asm_sym_rel_def,
      sval_conc_def] >>
  metis_tac[]
QED

Theorem asm_sym_step:
  asm_static_wf p ∧ asm_sym_rel p env cs ss ∧ cs.as_pc < LENGTH p ⇒
  asm_sym_step_rel p env (sym_step p env (EL cs.as_pc p) ss)
    (asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
       (EL cs.as_pc p) cs)
Proof
  strip_tac >> irule asm_sym_inst_step >> simp[EL_MEM]
QED

(* ===== Runs ===== *)

Theorem asm_sym_rel_init[local]:
  s.as_pc = 0 ∧ asm_data_env_ok p env s.as_code ⇒
  asm_sym_rel p env s (sym_init s)
Proof
  rw[asm_sym_rel_def, sym_init_def, LIST_REL_MAP1, sval_conc_def,
     asm_state_component_equality] >>
  simp[LIST_REL_EL_EQN, sval_conc_def]
QED

Theorem sym_run_SUC[local]:
  sym_run p env (SUC fuel) ss =
  if ss.sym_base.as_pc ≥ LENGTH p then SymError "pc out of bounds"
  else
    case sym_step p env (EL ss.sym_base.as_pc p) ss of
      SymOK ss' => sym_run p env fuel ss'
    | r => r
Proof
  simp[Once sym_run_def]
QED

Theorem asm_sym_run_backward[local]:
  ∀fuel cs ss.
    asm_static_wf p ∧ asm_sym_rel p env cs ss ∧
    sym_terminal (sym_run p env fuel ss) ⇒
    ∃n. sym_result_rel (sym_run p env fuel ss)
          (asm_result_sym
             (asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p)
                p n cs))
Proof
  Induct >- simp[Once sym_run_def, sym_terminal_def] >>
  rpt gen_tac >> strip_tac >>
  drule asm_sym_rel_pc >> strip_tac >>
  reverse (Cases_on `cs.as_pc < LENGTH p`)
  >- gvs[sym_run_SUC, sym_terminal_def] >>
  drule_all asm_sym_step >>
  Cases_on `sym_step p env (EL cs.as_pc p) ss` >>
  gvs[sym_run_SUC, sym_terminal_def, asm_sym_step_rel_def]
  >~ [`SymOK ss1`]
  >- (strip_tac >> first_x_assum drule_all >> strip_tac >>
      qexists_tac `SUC n` >> gvs[asm_steps_def]) >>
  strip_tac >> qexists_tac `SUC 0` >>
  gvs[asm_steps_def, asm_result_sym_def, sym_result_rel_def]
QED

Theorem asm_sym_run_forward[local]:
  ∀n cs ss.
    asm_static_wf p ∧ asm_sym_rel p env cs ss ∧
    (∀fuel msg. sym_run p env fuel ss ≠ SymBad msg) ∧
    sym_terminal (asm_result_sym
      (asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p)
         p n cs)) ⇒
    ∃fuel. sym_result_rel
      (asm_result_sym
         (asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p)
            p n cs))
      (sym_run p env fuel ss)
Proof
  Induct >- simp[asm_steps_def, asm_result_sym_def, sym_terminal_def] >>
  rpt gen_tac >> strip_tac >>
  drule asm_sym_rel_pc >> strip_tac >>
  reverse (Cases_on `cs.as_pc < LENGTH p`)
  >- gvs[asm_steps_def, asm_result_sym_def, sym_terminal_def] >>
  drule_all asm_sym_step >>
  Cases_on `sym_step p env (EL cs.as_pc p) ss` >>
  simp[asm_sym_step_rel_def] >> rpt strip_tac
  >~ [`sym_step _ _ _ _ = SymOK ss1`]
  >- (gvs[asm_steps_def] >>
      rename1 `asm_steps _ _ _ n cs1` >>
      `∀fuel msg. sym_run p env fuel ss1 ≠ SymBad msg`
        by (rpt gen_tac >>
            qpat_x_assum `∀fuel msg. sym_run _ _ _ ss ≠ _`
              (qspecl_then [`SUC fuel`, `msg`] mp_tac) >>
            simp[sym_run_SUC]) >>
      qpat_x_assum `∀cs ss. _ ⇒ _` (qspecl_then [`cs1`, `ss1`] mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac `SUC fuel` >> simp[sym_run_SUC])
  >~ [`sym_step _ _ _ _ = SymBad msg`]
  >- (qpat_x_assum `∀fuel msg. sym_run _ _ _ ss ≠ _`
        (qspecl_then [`SUC 0`, `msg`] mp_tac) >>
      simp[sym_run_SUC]) >>
  qexists_tac `SUC 0` >>
  gvs[asm_steps_def, asm_result_sym_def, sym_run_SUC, sym_result_rel_def,
      sym_terminal_def]
QED

(* TOP-LEVEL: a concrete run that ends (halts, reverts or faults) is a
   symbolic run that ends the same way, for a label-disciplined program. *)
Theorem asm_sym_forward:
  label_disciplined env p s ∧
  (* sym_init starts at instruction 0 *)
  s.as_pc = 0 ∧
  (* CODECOPY from a data label reads env, the concrete code from it on *)
  asm_data_env_ok p env s.as_code ∧
  sym_terminal (asm_result_sym
    (asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n s))
  ⇒
  ∃fuel.
    sym_result_rel
      (asm_result_sym
        (asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n s))
      (sym_run p env fuel (sym_init s))
Proof
  rw[label_disciplined_def] >> irule asm_sym_run_forward >>
  simp[asm_sym_rel_init]
QED

(* TOP-LEVEL: a symbolic run that ends is a concrete run that ends the
   same way. *)
Theorem asm_sym_backward:
  (* labels resolve to the targets the symbolic run jumps to *)
  asm_static_wf p ∧
  (* sym_init starts at instruction 0 *)
  s.as_pc = 0 ∧
  (* CODECOPY from a data label reads env, the concrete code from it on *)
  asm_data_env_ok p env s.as_code ∧
  sym_terminal (sym_run p env fuel (sym_init s))
  ⇒
  ∃n.
    sym_result_rel
      (sym_run p env fuel (sym_init s))
      (asm_result_sym
        (asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n s))
Proof
  strip_tac >> irule asm_sym_run_backward >> simp[asm_sym_rel_init]
QED
