Theory readonlyInvokeCopyFwdStepsHash
Ancestors
  readonlyInvokeCopyFwdStepsCore readonlyInvokeCopyFwdValues
  readonlyInvokeCopyFwdRel venomExecSemantics venomState ptrDiscipline
  taintAgree finite_map words list

(* The addresses may relocate.  Equality here is of the concrete padded
   slices, not merely agreement outside a taint mask.  Reachable-use
   reasoning supplies this premise; hashing itself produces a clean scalar. *)
Theorem ricf_cert_sha3:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\ inst.inst_opcode
  = SHA3 /\ inst.inst_operands = [addr;len] /\ inst.inst_outputs = [out] /\ eval_operand addr s
  = SOME p /\ eval_operand addr t = SOME q /\ eval_operand len s = SOME n /\ eval_operand len t
  = SOME n /\ read_memory (w2n p) (w2n n) s = read_memory (w2n q) (w2n n) t ==> step_inst_base
  inst s = OK (update_var out (word_of_bytes T (0w:bytes32) (Keccak_256_w64 (read_memory (w2n p)
  (w2n n) s))) s) /\ step_inst_base inst t = OK (update_var out (word_of_bytes T (0w:bytes32)
  (Keccak_256_w64 (read_memory (w2n p) (w2n n) s))) t) /\ ricf_cert_core D ids stk PG
  (ricf_effective_prov fn (update_var out (word_of_bytes T (0w:bytes32) (Keccak_256_w64
  (read_memory (w2n p) (w2n n) s))) s) (set_prov G0 [out] NONE)) (ricf_effective_taint fn
  (update_var out (word_of_bytes T (0w:bytes32) (Keccak_256_w64 (read_memory (w2n p) (w2n n)
  s))) s) (tn0 with t_var := set_var_taint tn0.t_var [out] {})) fn sites maps targets (set_prov
  G0 [out] NONE) (tn0 with t_var := set_var_taint tn0.t_var [out] {}) cur curs (update_var out
  (word_of_bytes T (0w:bytes32) (Keccak_256_w64 (read_memory (w2n p) (w2n n) s))) s) (update_var
  out (word_of_bytes T (0w:bytes32) (Keccak_256_w64 (read_memory (w2n p) (w2n n) s))) t)
Proof
  strip_tac >> simp[] >>
  simp[step_inst_base_opcode_eqs, GSYM read_memory_def] >>
  `!w:bytes32. ricf_value_agree sites NONE {} w w` by
    simp[ricf_value_agree_inactive, word_agree_except_def] >>
  metis_tac[ricf_cert_bind, ricf_effective_prov_def, ricf_effective_taint_def]
QED
