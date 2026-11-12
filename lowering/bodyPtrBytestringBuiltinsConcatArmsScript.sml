(* Counted pointer paths for the Concat append arms. *)
Theory bodyPtrBytestringBuiltinsConcatArms
Ancestors
  bodyPtrBytestringBuiltinsConcatChecks exprSimConcatArgs
  bodyPtrBytestringBuiltinsConcatArmSemantics bodyPtrDefs exprSimProps ptrDiscipline
  bodyPtrSubscriptSeamMapFrame assignTuplePtrLocalCopyRun
  bodyPtrPrecompileBuiltinsSuffixGhost
  exprSimConcatStep exprSimConcatPath concatMemory
  venomState venomInst venomExecSemantics compileEnv fragGasSeqPtr fragExec
  words arithmetic list rich_list pred_set
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

Theorem concat_fixed_arm_ptr:
  (do offset_op <- emit_op MLOAD [Var oq];
      dst <- emit_op ADD [Var dp; offset_op];
      emit_void MSTORE [dst; x];
      new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
      emit_void MSTORE [Var oq; new_offset]
   od) sx = ((), sb) /\
  fn_has_code sx sb func /\ ~t.vs_halted /\
  t.vs_current_bb = sx.cs_current_bb /\
  t.vs_inst_idx = LENGTH sx.cs_current_insts /\
  local_ptrs_reserved cenv sx /\ stmt_state_rel ctx func cenv cx es t /\
  ghost_inv d cenv cx es G tn t /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sx z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sx z) /\
  lookup_var dp t = SOME (n2w (B+32)) /\ lookup_var oq t = SOME ow /\
  eval_operand x t = SOME (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) /\
  not_fresh_at sx dp /\ not_fresh_at sx oq /\
  (!z. x = Var z ==> not_fresh_at sx z) /\
  ptr_covers G tn dp t (bsz-32) /\ ptr_covers G tn oq t 32 /\
  op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas binst.inst_id = SOME (B,bsz) /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
  (B+bsz <= w2n ow \/ w2n ow+64 <= B) /\
  (!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn.t_mem) /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n ow) t = n2w k /\ LENGTH bs = m /\ m <= 32 /\
  B+bsz < dimword (:256) /\ 32+k+32 <= bsz ==>
  ?u Gf tnf.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 Gf tnf (OK u) /\
    stmt_state_rel ctx func cenv cx es u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_allocas = t.vs_allocas /\
    (!z. not_fresh_at sx z ==> lookup_var z u = lookup_var z t) /\
    mem_bytes_at (B+32) (k+m) u.vs_memory = mem_bytes_at (B+32) k t.vs_memory ++ bs /\
    mload (w2n ow) u = n2w (k+m) /\
    (!p n. (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) ==>
      mem_bytes_at p n u.vs_memory = mem_bytes_at p n t.vs_memory) /\
    ghost_inv d cenv cx es Gf tnf u /\ ghost_kept cenv es sx G tn t Gf tnf /\
    ptr_covers Gf tnf dp u (bsz-32) /\ ptr_covers Gf tnf oq u 32 /\
    (!i. B+32 <= i /\ i < B+32+k+m ==> i NOTIN tnf.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tnf.t_mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all concat_fixed_step_path_ptr >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `w2n (n2w (B+32) + n2w k : 256 word) = B+32+k` by
    (simp[word_add_n2w] >> irule LESS_MOD >> fs[dimword_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (OK u)` >>
  `u = (mstore (w2n ow) (n2w (k+m))
      (mstore (B+32+k) (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) t) with
      <|vs_vars := V; vs_inst_idx := LENGTH sb.cs_current_insts|>)` by
    simp[Abbr `u`, word_add_n2w] >>
  drule_all concat_fixed_endpoint_state >> strip_tac >>
  drule_all concat_fixed_endpoint_memory >> strip_tac >>
  drule_all concat_fixed_endpoint_fields >> strip_tac >>
  drule concat_fixed_code_shape >> strip_tac >>
  qpat_x_assum `u = _` kall_tac >> qpat_x_assum `Abbrev _` kall_tac >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >> simp[] >> suspend "ghost"
QED

Resume concat_fixed_arm_ptr[ghost]:
  `ghost_kept cenv es sx G tn t Gf tnf` by
    (irule ghost_kept_memory_subset >> simp[]) >>
  `ptr_covers Gf tnf dp u (bsz-32) /\ ptr_covers Gf tnf oq u 32` by
    (conj_tac >> irule annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr >>
     qexistsl_tac [`G`,`t`,`tn`] >> simp[] >> metis_tac[]) >>
  `stor_taint_ok cx tnf u` by
    (fs[ghost_inv_def, stor_taint_ok_def] >> metis_tac[]) >>
  `ghost_inv d cenv cx es Gf tnf u` by
    (irule hash_ghost_inv_region_frame >> metis_tac[]) >>
  simp[] >> conj_tac >- metis_tac[ADD_COMM] >>
  gen_tac >> strip_tac >>
  Cases_on `i < B+32+k`
  >- metis_tac[SUBSET_DEF] >>
  `B+32+k <= i /\ i < B+32+k+32` by decide_tac >> metis_tac[]
QED

Finalise concat_fixed_arm_ptr

Theorem concat_bytes_arm_ptr:
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
  local_ptrs_reserved cenv sx /\ stmt_state_rel ctx func cenv cx es t /\
  ghost_inv d cenv cx es G tn t /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sx z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sx z) /\
  lookup_var src t = SOME sw /\ lookup_var dp t = SOME (n2w (B+32)) /\
  lookup_var oq t = SOME ow /\
  not_fresh_at sx src /\ not_fresh_at sx dp /\ not_fresh_at sx oq /\
  ptr_covers G tn src t (32+LENGTH bs) /\
  ptr_covers G tn dp t (bsz-32) /\ ptr_covers G tn oq t 32 /\
  (!i. w2n sw <= i /\ i < w2n sw+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  mload (w2n sw) t = n2w (LENGTH bs) /\
  mem_bytes_at (w2n sw+32) (LENGTH bs) t.vs_memory = bs /\
  LENGTH bs < dimword (:256) /\ w2n sw+32 < dimword (:256) /\
  MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas binst.inst_id = SOME (B,bsz) /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
  (B+bsz <= w2n ow \/ w2n ow+64 <= B) /\
  (!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn.t_mem) /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n ow) t = n2w k /\ ~ctx_has_dalloca ctx /\
  B+bsz < dimword (:256) /\ 32+k+LENGTH bs <= bsz ==>
  ?u Gf tnf.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 Gf tnf (OK u) /\
    stmt_state_rel ctx func cenv cx es u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_allocas = t.vs_allocas /\
    (!z. not_fresh_at sx z ==> lookup_var z u = lookup_var z t) /\
    mem_bytes_at (B+32) (k+LENGTH bs) u.vs_memory =
      mem_bytes_at (B+32) k t.vs_memory ++ bs /\
    mload (w2n ow) u = n2w (k+LENGTH bs) /\
    (!p n. (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) ==>
      mem_bytes_at p n u.vs_memory = mem_bytes_at p n t.vs_memory) /\
    ghost_inv d cenv cx es Gf tnf u /\ ghost_kept cenv es sx G tn t Gf tnf /\
    ptr_covers Gf tnf dp u (bsz-32) /\ ptr_covers Gf tnf oq u 32 /\
    (!i. B+32 <= i /\ i < B+32+k+LENGTH bs ==> i NOTIN tnf.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tnf.t_mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all concat_bytes_step_path_ptr >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `w2n (n2w (B+32) + n2w k : 256 word) = B+32+k /\
   w2n (sw+32w) = w2n sw+32` by
    (simp[word_add_n2w, word_add_def] >> conj_tac >> irule LESS_MOD >> fs[dimword_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (OK u)` >>
  `u = (mstore (w2n ow) (n2w (k+LENGTH bs))
      (mcopy (B+32+k) (w2n sw+32) (LENGTH bs) t) with
      <|vs_vars := V; vs_inst_idx := LENGTH sb.cs_current_insts|>)` by
    simp[Abbr `u`, word_add_n2w] >>
  drule_all concat_bytes_endpoint_state >> strip_tac >>
  drule_all concat_bytes_endpoint_memory >> strip_tac >>
  drule_all concat_bytes_endpoint_fields >> strip_tac >>
  drule concat_bytes_code_shape >> strip_tac >>
  qpat_x_assum `u = _` kall_tac >> qpat_x_assum `Abbrev _` kall_tac >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >> simp[] >> suspend "ghost"
QED

Resume concat_bytes_arm_ptr[ghost]:
  `ghost_kept cenv es sx G tn t Gf tnf` by
    (irule ghost_kept_memory_subset >> simp[]) >>
  `ptr_covers Gf tnf dp u (bsz-32) /\ ptr_covers Gf tnf oq u 32` by
    (conj_tac >> irule annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr >>
     qexistsl_tac [`G`,`t`,`tn`] >> simp[] >> metis_tac[]) >>
  `stor_taint_ok cx tnf u` by
    (fs[ghost_inv_def, stor_taint_ok_def] >> metis_tac[]) >>
  `ghost_inv d cenv cx es Gf tnf u` by
    (irule hash_ghost_inv_region_frame >> metis_tac[]) >>
  simp[] >> conj_tac >- metis_tac[ADD_COMM] >>
  gen_tac >> strip_tac >> Cases_on `i < B+32+k`
  >- metis_tac[SUBSET_DEF] >>
  `B+32+k <= i /\ i < B+32+k+LENGTH bs` by decide_tac >> metis_tac[]
QED

Finalise concat_bytes_arm_ptr
