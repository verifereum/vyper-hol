(* Counted pointer paths for the Concat append arms. *)
Theory bodyPtrBytestringBuiltinsConcatArms
Ancestors
  bodyPtrBytestringBuiltinsConcatChecks exprSimConcatArgs
  bodyPtrSubscriptSeamMapFrame assignTuplePtrLocalCopyRun
  bodyPtrPrecompileBuiltinsSuffixGhost
  exprSimConcatStep exprSimConcatPath concatMemory
  venomState venomInst venomExecSemantics compileEnv fragGasSeqPtr fragExec
  words arithmetic list rich_list
Libs
  monadsyntax

Theorem concat_fixed_step_path_ptr:
  (do offset_op <- emit_op MLOAD [Var oq];
      dst <- emit_op ADD [Var dp; offset_op];
      emit_void MSTORE [dst; x];
      new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
      emit_void MSTORE [Var oq; new_offset]
   od) sx = ((), sb) /\
  fn_has_code sx sb func /\ ~t.vs_halted /\
  t.vs_current_bb = sx.cs_current_bb /\
  t.vs_inst_idx = LENGTH sx.cs_current_insts /\
  lookup_var dp t = SOME (n2w (B+32)) /\ lookup_var oq t = SOME ow /\
  eval_operand x t = SOME vw /\
  not_fresh_at sx dp /\ not_fresh_at sx oq /\
  (!z. x = Var z ==> not_fresh_at sx z) /\
  ptr_covers G tn dp t (bsz-32) /\ ptr_covers G tn oq t 32 /\
  op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n ow) t = n2w k /\
  B+bsz < dimword (:256) /\ 32+k+32 <= bsz ==>
  ?V Gf tnf.
    gas_path_ptr D 0 ctx func PG G tn t 0 Gf tnf
      (OK (mstore (w2n ow) (n2w k + n2w m)
        (mstore (w2n (n2w (B+32) + n2w k : 256 word)) vw t) with
        <|vs_vars := V; vs_inst_idx := LENGTH sb.cs_current_insts|>)) /\
    (!z. not_fresh_at sx z ==> FLOOKUP V z = FLOOKUP t.vs_vars z) /\
    tnf.t_mem SUBSET tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!z. not_fresh_at sx z ==>
      FLOOKUP Gf z = FLOOKUP G z /\ op_taint tnf (Var z) = op_taint tn (Var z)) /\
    (!i. B+32+k <= i /\ i < B+32+k+32 ==> i NOTIN tnf.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >>
  drule_all concat_fixed_seq_ptr >>
  disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
  `eval_operand (Var dp) t = SOME (n2w (B+32)) /\
   eval_operand (Var oq) t = SOME ow` by simp[eval_operand_def] >>
  drule concat_fixed_step_run >>
  disch_then (qspec_then `t` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`V`,`Gf`,`tnf`] >> simp[] >>
  drule concat_fixed_code_shape >> strip_tac >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sx sb) (DROP t.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sx sb)` by
    (drule concat_fixed_shape >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_gas_path_ptr >>
  drule concat_fixed_shape >> strip_tac >>
  gvs[] >> simp[mk_inst_def, is_terminator_def]
QED

Theorem concat_bytes_step_path_ptr:
  (do arg_len <- emit_op MLOAD [Var src];
      arg_data <- emit_op ADD [Var src; Lit 32w];
      offset_op <- emit_op MLOAD [Var oq];
      dst <- emit_op ADD [Var dp; offset_op];
      emit_void MCOPY [dst; arg_data; arg_len];
      new_offset <- emit_op ADD [offset_op; arg_len];
      emit_void MSTORE [Var oq; new_offset]
   od) sx = ((), sb) /\
  fn_has_code sx sb func /\ ~t.vs_halted /\
  t.vs_current_bb = sx.cs_current_bb /\
  t.vs_inst_idx = LENGTH sx.cs_current_insts /\
  lookup_var src t = SOME sw /\
  lookup_var dp t = SOME (n2w (B+32)) /\ lookup_var oq t = SOME ow /\
  not_fresh_at sx src /\ not_fresh_at sx dp /\ not_fresh_at sx oq /\
  ptr_covers G tn src t (32+N) /\
  ptr_covers G tn dp t (bsz-32) /\ ptr_covers G tn oq t 32 /\
  (!i. w2n sw <= i /\ i < w2n sw+32+N ==> i NOTIN tn.t_mem) /\
  mload (w2n sw) t = n2w N /\
  N < dimword (:256) /\ w2n sw+32 < dimword (:256) /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n ow) t = n2w k /\
  B+bsz < dimword (:256) /\ 32+k+N <= bsz /\ ~ctx_has_dalloca ctx ==>
  ?V Gf tnf.
    gas_path_ptr D 0 ctx func PG G tn t 0 Gf tnf
      (OK (mstore (w2n ow) (n2w k + n2w N)
        (mcopy (w2n (n2w (B+32) + n2w k : 256 word))
          (w2n (sw+32w)) N t) with
        <|vs_vars := V; vs_inst_idx := LENGTH sb.cs_current_insts|>)) /\
    (!z. not_fresh_at sx z ==> FLOOKUP V z = FLOOKUP t.vs_vars z) /\
    tnf.t_mem SUBSET tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!z. not_fresh_at sx z ==>
      FLOOKUP Gf z = FLOOKUP G z /\ op_taint tnf (Var z) = op_taint tn (Var z)) /\
    (!i. B+32+k <= i /\ i < B+32+k+N ==> i NOTIN tnf.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> drule_all concat_bytes_seq_ptr >>
  disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
  `eval_operand (Var dp) t = SOME (n2w (B+32)) /\
   eval_operand (Var oq) t = SOME ow /\
   eval_operand (Var src) t = SOME sw` by simp[eval_operand_def] >>
  drule concat_bytes_step_run >>
  disch_then (qspec_then `t` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`V`,`Gf`,`tnf`] >> simp[w2n_n2w, LESS_MOD] >>
  drule concat_bytes_code_shape >> strip_tac >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sx sb) (DROP t.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sx sb)` by
    (drule concat_bytes_shape >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_gas_path_ptr >>
  drule concat_bytes_shape >> strip_tac >>
  gvs[] >> simp[mk_inst_def, is_terminator_def, LESS_MOD]
QED
