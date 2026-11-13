(* Location-independent membership loop invariant.  R carries the read-only
   array view, captured operands, and the protected-variable frame.  Control
   position is kept outside the invariant so jumps do not change its meaning. *)
Theory exprSimBopRestWordLoop
Ancestors
  exprLowering emitHelperProps venomExecSemantics venomState venomInst
  words arithmetic list finite_map

Definition rest_word_membership_inv_def:
  rest_word_membership_inv idx result len needle elem R i s <=>
    i <= len /\ len < dimword (:256) /\
    eval_operand (Var idx) s = SOME (n2w i) /\
    eval_operand (Var result) s = SOME 0w /\
    (!j. j < i ==> elem j <> needle) /\ R s
End

Theorem rest_word_membership_init:
  idx <> result /\ len < dimword (:256) /\
  R (update_var result 0w (update_var idx 0w s)) ==>
  rest_word_membership_inv idx result len needle elem R 0
    (update_var result 0w (update_var idx 0w s))
Proof
  simp[rest_word_membership_inv_def, eval_operand_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem rest_word_membership_exhausted:
  rest_word_membership_inv idx result len needle elem R len s ==>
  ~(?j. j < len /\ elem j = needle)
Proof
  simp[rest_word_membership_inv_def] >> metis_tac[]
QED

Theorem rest_word_membership_found:
  rest_word_membership_inv idx result len needle elem R i s /\
  i < len /\ elem i = needle ==>
  ?j. j < len /\ elem j = needle
Proof
  metis_tac[]
QED

Theorem rest_word_membership_miss:
  rest_word_membership_inv idx result len needle elem R i s /\
  idx <> result /\ i < len /\ elem i <> needle /\
  R (update_var idx (n2w (i+1)) s) ==>
  rest_word_membership_inv idx result len needle elem R (i+1)
    (update_var idx (n2w (i+1)) s)
Proof
  simp[rest_word_membership_inv_def, eval_operand_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `j = i` >> gvs[] >>
  first_x_assum irule >> decide_tac
QED

Theorem rest_word_membership_test:
  rest_word_membership_inv idx result len needle elem R i s /\
  eval_operand len_op s = SOME (n2w len) ==>
  step_inst_base (mk_inst id EQ [Var idx; len_op] [done]) s =
    OK (update_var done (bool_to_word (i = len)) s)
Proof
  strip_tac >>
  `i < dimword (:256)` by (gvs[rest_word_membership_inv_def] >> decide_tac) >>
  gvs[rest_word_membership_inv_def] >>
  qspecl_then [`Var idx`, `len_op`, `(n2w i):bytes32`, `(n2w len):bytes32`]
    mp_tac step_EQ >> simp[wordsTheory.n2w_11] >>
  `i < dimword (:256)` by decide_tac >> simp[]
QED

Theorem rest_word_membership_next_word:
  i < len /\ len < dimword (:256) ==>
  (n2w i:bytes32) + 1w = n2w (i+1) /\ i+1 <= len
Proof
  simp[wordsTheory.word_add_n2w] >> decide_tac
QED

Theorem rest_word_membership_address:
  (a:bytes32) + (if 0 < offset then n2w offset + n2w i * n2w stride
                else n2w i * n2w stride) =
  a + n2w (offset + i * stride)
Proof
  Cases_on `0 < offset` >> gvs[wordsTheory.word_mul_n2w, wordsTheory.word_add_n2w]
QED

Theorem rest_word_membership_inv_frame:
  rest_word_membership_inv idx result len needle elem R i s /\ R t /\
  FLOOKUP t.vs_vars idx = FLOOKUP s.vs_vars idx /\
  FLOOKUP t.vs_vars result = FLOOKUP s.vs_vars result ==>
  rest_word_membership_inv idx result len needle elem R i t
Proof
  simp[rest_word_membership_inv_def, eval_operand_def, lookup_var_def]
QED

Theorem rest_word_membership_branch:
  eval_operand cond s = SOME (bool_to_word p) ==>
  step_inst_base (mk_inst id JNZ [cond; Label yes; Label no] []) s =
    OK (jump_to (if p then yes else no) s)
Proof
  Cases_on `p` >> simp[bool_to_word_def, step_inst_base_opcode_eqs, mk_inst_def]
QED

Theorem rest_word_membership_exit_notin:
  eval_operand (Var result) s = SOME (bool_to_word found) ==>
  step_inst_base (mk_inst id ISZERO [Var result] [out]) s =
    OK (update_var out (bool_to_word (~found)) s)
Proof
  strip_tac >> drule step_ISZERO >>
  Cases_on `found` >> simp[bool_to_word_def]
QED
