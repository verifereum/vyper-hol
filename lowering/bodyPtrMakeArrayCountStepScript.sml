(* Installed scalar edges for the bytestring count prefix. *)
Theory bodyPtrMakeArrayCountStep
Ancestors
  typedCopyPtr bodyPtrMakeArrayLoad bodyPtrMakeArrayMloadFrame
  fragGasSeqPtr fragGasPathPtr ptrDiscipline venomExecSemantics venomState
  venomInst finite_map

Theorem copy_len_binop_path:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id opc [left;right] [tmp]) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [left;right] [tmp])
      (update_var tmp (f a b) s))
    (step_taint (mk_inst id opc [left;right] [tmp]) s
      (update_var tmp (f a b) s) tn)
    (OK ((update_var tmp (f a b) s) with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [left;right] [tmp])
      (update_var tmp (f a b) s))
    (step_taint (mk_inst id opc [left;right] [tmp]) s
      (update_var tmp (f a b) s) tn)
    (OK ((update_var tmp (f a b) s) with
      vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id opc [left;right] [tmp]`,
                     `lo` |-> `0`, `u` |-> `update_var tmp ((f:bytes32 -> bytes32 -> bytes32) a b) s`]
                    straight_line_ptr_edge) >>
     gvs[] >> simp[mk_inst_def, is_terminator_def] >>
     disch_then irule >> conj_tac
     >- simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def] >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_copy_len_binop) >> simp[]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[update_var_def]
QED

Theorem copy_len_binop_endpoint:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id opc [left;right] [tmp]) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf = ((update_var tmp (f a b) s) with
      vs_inst_idx := SUC s.vs_inst_idx) /\
    eval_operand (Var tmp) sf = SOME (f a b) /\
    op_taint tnf (Var tmp) = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!x. x <> tmp ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst id opc [left;right] [tmp])
       (update_var tmp (f a b) s)`,
    `step_taint (mk_inst id opc [left;right] [tmp]) s
       (update_var tmp (f a b) s) tn`,
    `(update_var tmp (f a b) s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- (irule copy_len_binop_path >> metis_tac[]) >>
  `opc = ADD \/ opc = AND` by metis_tac[] >>
  simp[copy_len_binop_ghost_frame, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE]
QED

Theorem copy_len_header_endpoint:
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MLOAD [Var src] [tmp]) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf = ((update_var tmp (mload (w2n a) s) s) with
      vs_inst_idx := SUC s.vs_inst_idx) /\
    eval_operand (Var tmp) sf = SOME (mload (w2n a) s) /\
    op_taint tnf (Var tmp) = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!x. x <> tmp ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qexistsl_tac [
    `step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
       (update_var tmp (mload (w2n a) s) s)`,
    `step_taint (mk_inst id MLOAD [Var src] [tmp]) s
       (update_var tmp (mload (w2n a) s) s) tn`,
    `(update_var tmp (mload (w2n a) s) s) with
      vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- (irule mload_ptr_path >> simp[eval_operand_def]) >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  drule_all mload_ghost_clean >> strip_tac >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       mload_ghost_frame]
QED
