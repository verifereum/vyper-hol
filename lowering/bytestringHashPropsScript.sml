Theory bytestringHashProps
Ancestors
  exprLowering exprLoweringProps emitHelperProps compileEnv venomExecSemantics
  venomState venomInst byte keccak

Theorem emit_op_SHA3_correct:
  emit_op SHA3 [ptr_op; len_op] st = (op, st') /\
  eval_operand ptr_op ss = SOME p /\ eval_operand len_op ss = SOME n /\
  fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    eval_operand op ss' = SOME (word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (TAKE (w2n n)
        (DROP (w2n p) ss.vs_memory ++ REPLICATE (w2n n) 0w)))) /\
    same_blocks st st' /\ fresh_vars_wrt st' ss' /\
    (!x w. eval_operand x ss = SOME w ==> eval_operand x ss' = SOME w) /\
    ss'.vs_memory = ss.vs_memory
Proof
  rpt strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       eval_operand_update_var] >>
  drule emit_op_extends >> simp[same_blocks_def] >> strip_tac >> gvs[] >>
  conj_tac >- (irule fresh_vars_wrt_advance >> simp[] >>
    goal_assum $ drule_at Any >> gvs[]) >>
  conj_tac >- (rw[] >> irule eval_operand_update_fresh >> rw[] >>
    goal_assum $ drule_at Any >> gvs[]) >>
  simp[update_var_def]
QED

Theorem memory_frame_eq[local]:
  (!a. a < LENGTH ss.vs_memory ==> EL a tt.vs_memory = EL a ss.vs_memory) /\
  LENGTH tt.vs_memory = LENGTH ss.vs_memory ==>
  tt.vs_memory = ss.vs_memory
Proof
  strip_tac >> irule listTheory.LIST_EQ >> simp[]
QED

Theorem compile_bytestring_hash_correct:
  compile_bytestring_hash ptr_op st = (op, st') /\
  eval_operand ptr_op ss = SOME p /\ fresh_vars_wrt st ss /\
  mload (w2n p) ss = n2w (LENGTH contents) /\
  LENGTH contents < dimword (:256) /\
  TAKE (LENGTH contents)
    (DROP (w2n (p + 32w)) ss.vs_memory ++
      REPLICATE (LENGTH contents) 0w) = contents ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    eval_operand op ss' = SOME (word_of_bytes_be (Keccak_256_w64 contents):bytes32) /\
    same_blocks st st' /\ fresh_vars_wrt st' ss' /\
    (!x w. eval_operand x ss = SOME w ==> eval_operand x ss' = SOME w) /\
    ss'.vs_memory = ss.vs_memory
Proof
  rpt strip_tac >>
  gvs[compile_bytestring_hash_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule emit_op_ADD_correct >>
  disch_then (qspecl_then [`p`, `32w`, `ss`] mp_tac) >>
  simp[eval_operand_lit] >>
  disch_then (qx_choose_then `s1` strip_assume_tac) >>
  `s1.vs_memory = ss.vs_memory` by (irule memory_frame_eq >> simp[]) >>
  `eval_operand ptr_op s1 = SOME p` by metis_tac[] >>
  drule_all emit_op_MLOAD_correct >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  `s2.vs_memory = s1.vs_memory` by (irule memory_frame_eq >> simp[]) >>
  `eval_operand data_ptr s2 = SOME (p + 32w)` by metis_tac[] >>
  `mload (w2n p) s1 = n2w (LENGTH contents)` by
    gvs[mload_def] >>
  drule_all emit_op_SHA3_correct >>
  disch_then (qx_choose_then `s3` strip_assume_tac) >>
  `inst_extends st cs'` by
    (irule inst_extends_emit_op >> goal_assum $ drule_at Any) >>
  `inst_extends cs' cs''` by
    (irule inst_extends_emit_op >> goal_assum $ drule_at Any) >>
  `inst_extends cs'' st'` by
    (irule inst_extends_emit_op >> goal_assum $ drule_at Any) >>
  `run_inst_seq (emitted_insts st cs'') ss = OK s2` by
    metis_tac[run_inst_seq_emit_extend] >>
  `run_inst_seq (emitted_insts st st') ss = OK s3` by
    metis_tac[run_inst_seq_emit_extend, inst_extends_trans] >>
  qexists_tac `s3` >>
  gvs[word_of_bytes_be_def] >>
  metis_tac[same_blocks_trans]
QED

(* The literal path uses exactly the runtime SHA3 byte encoding. *)
Theorem bytestring_literal_hash_bytes:
  bytestring_literal_hash (Literal ty (BytesL bs)) =
    SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs))
Proof
  simp[bytestring_literal_hash_def, word_of_bytes_be_def]
QED

Theorem bytestring_literal_hash_string:
  bytestring_literal_hash (Literal ty (StringL s)) =
    SOME (word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (MAP (n2w o ORD) s)))
Proof
  simp[bytestring_literal_hash_def, word_of_bytes_be_def]
QED

(* Collision freedom is required only for these two contents.  This is
   deliberately not an unconditional injectivity claim about Keccak. *)
Theorem emit_bytestring_hash_EQ_correct:
  emit_op EQ [h1; h2] st = (op, st') /\
  eval_operand h1 ss = SOME (word_of_bytes_be (Keccak_256_w64 a)) /\
  eval_operand h2 ss = SOME (word_of_bytes_be (Keccak_256_w64 b)) /\
  fresh_vars_wrt st ss /\
  ((word_of_bytes_be (Keccak_256_w64 a):bytes32) =
    word_of_bytes_be (Keccak_256_w64 b) ==> a = b) ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    eval_operand op ss' = SOME (bool_to_word (a = b)) /\
    same_blocks st st' /\ fresh_vars_wrt st' ss' /\
    (!x w. eval_operand x ss = SOME w ==> eval_operand x ss' = SOME w) /\
    ss'.vs_memory = ss.vs_memory
Proof
  rpt strip_tac >> drule_all emit_op_EQ_correct >> strip_tac >>
  `((word_of_bytes_be (Keccak_256_w64 a):bytes32) =
    word_of_bytes_be (Keccak_256_w64 b)) = (a = b)` by metis_tac[] >>
  qexists_tac `ss'` >> simp[] >> irule memory_frame_eq >> simp[]
QED

Theorem emit_bytestring_hash_NotEq_correct:
  emit_op EQ [h1; h2] st = (eq_op, st1) /\
  emit_op ISZERO [eq_op] st1 = (op, st2) /\
  eval_operand h1 ss = SOME (word_of_bytes_be (Keccak_256_w64 a)) /\
  eval_operand h2 ss = SOME (word_of_bytes_be (Keccak_256_w64 b)) /\
  fresh_vars_wrt st ss /\
  ((word_of_bytes_be (Keccak_256_w64 a):bytes32) =
    word_of_bytes_be (Keccak_256_w64 b) ==> a = b) ==>
  ?ss'. run_inst_seq (emitted_insts st st2) ss = OK ss' /\
    eval_operand op ss' = SOME (bool_to_word (a <> b)) /\
    same_blocks st st2 /\ fresh_vars_wrt st2 ss' /\
    (!x w. eval_operand x ss = SOME w ==> eval_operand x ss' = SOME w) /\
    ss'.vs_memory = ss.vs_memory
Proof
  rpt strip_tac >> drule_all emit_bytestring_hash_EQ_correct >>
  disch_then (qx_choose_then `s1` strip_assume_tac) >>
  drule_all emit_op_ISZERO_correct_mem >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  `inst_extends st st1` by
    (irule inst_extends_emit_op >> goal_assum $ drule_at Any) >>
  `inst_extends st1 st2` by
    (irule inst_extends_emit_op >> goal_assum $ drule_at Any) >>
  qexists_tac `s2` >>
  `s2.vs_memory = s1.vs_memory` by (irule memory_frame_eq >> simp[]) >>
  conj_tac >- metis_tac[run_inst_seq_emit_extend] >>
  simp[bool_to_word_def] >>
  conj_tac >- (Cases_on `a = b` >> gvs[bool_to_word_def]) >>
  metis_tac[same_blocks_trans]
QED

Theorem compile_bytestring_hash_extends[local]:
  compile_bytestring_hash p st = (h, st') ==> inst_extends st st'
Proof
  rw[compile_bytestring_hash_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac inst_extends_emit_op >>
  metis_tac[inst_extends_trans]
QED

(* The two runtime operands can be hashed in source order without losing
   the first digest or the second pointer.  Literal operands need no
   instruction segment and use the two literal equations above instead. *)
Theorem compile_bytestring_hash_pair_correct:
  compile_bytestring_hash p1 st = (h1, st1) /\
  compile_bytestring_hash p2 st1 = (h2, st2) /\
  eval_operand p1 ss = SOME a /\ eval_operand p2 ss = SOME b /\
  fresh_vars_wrt st ss /\
  mload (w2n a) ss = n2w (LENGTH xs) /\
  mload (w2n b) ss = n2w (LENGTH ys) /\
  LENGTH xs < dimword (:256) /\ LENGTH ys < dimword (:256) /\
  TAKE (LENGTH xs) (DROP (w2n (a + 32w)) ss.vs_memory ++
    REPLICATE (LENGTH xs) 0w) = xs /\
  TAKE (LENGTH ys) (DROP (w2n (b + 32w)) ss.vs_memory ++
    REPLICATE (LENGTH ys) 0w) = ys ==>
  ?ss'. run_inst_seq (emitted_insts st st2) ss = OK ss' /\
    eval_operand h1 ss' = SOME (word_of_bytes_be (Keccak_256_w64 xs):bytes32) /\
    eval_operand h2 ss' = SOME (word_of_bytes_be (Keccak_256_w64 ys):bytes32) /\
    same_blocks st st2 /\ fresh_vars_wrt st2 ss' /\
    (!x w. eval_operand x ss = SOME w ==> eval_operand x ss' = SOME w) /\
    ss'.vs_memory = ss.vs_memory
Proof
  rpt strip_tac >>
  drule_all compile_bytestring_hash_correct >>
  disch_then (qx_choose_then `s1` strip_assume_tac) >>
  `eval_operand p2 s1 = SOME b` by metis_tac[] >>
  `mload (w2n b) s1 = n2w (LENGTH ys)` by gvs[mload_def] >>
  `inst_extends st st1` by
    (irule compile_bytestring_hash_extends >> goal_assum $ drule_at Any) >>
  `inst_extends st1 st2` by
    (irule compile_bytestring_hash_extends >> goal_assum $ drule_at Any) >>
  qpat_x_assum `compile_bytestring_hash p1 st = _` kall_tac >>
  `TAKE (LENGTH ys) (DROP (w2n (b + 32w)) s1.vs_memory ++
     REPLICATE (LENGTH ys) 0w) = ys` by simp[] >>
  drule_all compile_bytestring_hash_correct >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  qexists_tac `s2` >> conj_tac
  >- metis_tac[run_inst_seq_emit_extend] >>
  gvs[] >> metis_tac[same_blocks_trans]
QED

(* Kernel-closure regression: DISK_THM is the loader provenance, not an
   admission.  All exported boundaries in this theory must remain closed. *)
val _ = List.app (fn (name, th) =>
  if List.all (fn tag => tag = "DISK_THM")
       (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("Oracle dependency in bytestring hash boundary: " ^ name))
  (DB.thms "bytestringHashProps");
