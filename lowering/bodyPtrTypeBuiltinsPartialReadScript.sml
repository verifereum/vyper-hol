(* Partial-word read probe: coverage does not imply clean padding. *)
Theory bodyPtrTypeBuiltinsPartialRead
Ancestors
  bodyPtrTypeBuiltinsBytesRead ptrDiscipline emitHelperProps
  pred_set arithmetic venomInst

Theorem partial_word_shift_clean:
  n <= 32 /\ (!i. i IN m ==> n <= i /\ i < 32) ==>
  shift_taint SHR (8 * (32 - n)) m = {} /\
  (0 < n ==> shift_taint SAR (8 * (32 - n)) m = {})
Proof
  strip_tac >>
  `0 < n ==> 0 NOTIN m` by metis_tac[arithmeticTheory.NOT_LESS] >>
  simp[shift_taint_def, EXTENSION] >>
  rpt strip_tac >> spose_not_then strip_assume_tac >> gvs[] >>
  qpat_x_assum `!i. _` (qspec_then `i` mp_tac) >> simp[] >> decide_tac
QED

Theorem mul_taint_requires_clean_inputs:
  taint_ok fn tn (mk_inst id MUL [x;y] [z]) s ==>
  op_taint tn x = {} /\ op_taint tn y = {}
Proof
  simp[taint_ok_def, mk_inst_def] >> metis_tac[]
QED

Theorem partial_read_examples:
  mem_word_taint {63} 32 = {31} /\
  shift_taint SHR 256 {31} = {} /\
  shift_taint SHR 248 {31} = {} /\
  shift_taint SAR 248 {31} = {} /\
  shift_taint SHR 0 {} = {} /\ shift_taint SAR 0 {} = {}
Proof
  `shift_taint SHR 256 {31} = {}` by
    (mp_tac (Q.INST [`n` |-> `0`, `m` |-> `{31}`] partial_word_shift_clean) >> simp[]) >>
  `shift_taint SHR 248 {31} = {} /\ shift_taint SAR 248 {31} = {}` by
    (mp_tac (Q.INST [`n` |-> `1`, `m` |-> `{31}`] partial_word_shift_clean) >> simp[]) >>
  simp[mem_word_taint_def, shift_taint_def, EXTENSION] >> decide_tac
QED

Theorem partial_data_mul_rejected:
  op_taint tn x = {31} ==>
  ~taint_ok fn tn (mk_inst id MUL [x;Lit 0w] [z]) s
Proof
  strip_tac >> disch_then (mp_tac o MATCH_MP mul_taint_requires_clean_inputs) >>
  simp[EXTENSION] >> metis_tac[]
QED
