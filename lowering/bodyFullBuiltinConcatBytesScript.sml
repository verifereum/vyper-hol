(* Dynamic Concat append on one joint execution endpoint. *)
Theory bodyFullBuiltinConcatBytes
Ancestors
  bodyFullUnwrapRun concatArmSeqPtr
  bodyPtrBytestringBuiltinsWindowGhost
  bodyPtrBytestringBuiltinsConcatArmSemantics instSeqPtrLo
  exprSimConcatStep exprSimConcatPath concatMemory fragExecMem instMemFrontier
  compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomInst venomExecSemantics words list finite_map pred_set
Libs
  monadsyntax

Theorem concat_bytes_arm_mem_ok:
  (do arg_len <- emit_op MLOAD [Var sp];
      arg_data <- emit_op ADD [Var sp;Lit 32w];
      offset_op <- emit_op MLOAD [Var oq];
      dst <- emit_op ADD [Var dp;offset_op];
      emit_void MCOPY [dst;arg_data;arg_len];
      new_offset <- emit_op ADD [offset_op;arg_len];
      emit_void MSTORE [Var oq;new_offset]
   od) sa = ((),sb) /\
  not_fresh_at sa sp /\ not_fresh_at sa dp /\ not_fresh_at sa oq /\
  lookup_var sp s = SOME (n2w srcbase) /\
  lookup_var dp s = SOME (n2w (B+32)) /\ lookup_var oq s = SOME (n2w ob) /\
  mload srcbase s = n2w (LENGTH bs) /\ mload ob s = n2w k /\
  32+k+LENGTH bs <= bsz /\ B+bsz < dimword (:256) /\
  srcbase+32+LENGTH bs < dimword (:256) /\ ob+64 < dimword (:256) /\
  srcbase+32+LENGTH bs <= s.vs_alloca_next /\
  B+bsz <= s.vs_alloca_next /\ ob+64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `!id ops outs t. inst_mem_below_frontier (mk_inst id ADD ops outs) t` by
    (rpt gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `!n. sa.cs_next_var <= n ==>
    sp <> STRING #"%" (toString n) /\ dp <> STRING #"%" (toString n) /\
    oq <> STRING #"%" (toString n)` by
    metis_tac[loweringStateRelDefsTheory.not_fresh_at_def] >>
  `srcbase < dimword (:256) /\ ob < dimword (:256) /\
   B+32 < dimword (:256) /\ k < dimword (:256) /\
   LENGTH bs < dimword (:256) /\ srcbase+32 < dimword (:256) /\
   B+32+k < dimword (:256)` by decide_tac >>
  drule concat_bytes_shape >> disch_then SUBST1_TAC >>
  gvs[lookup_var_def, mload_def] >>
  simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
    below_frontier_MLOAD, below_frontier_MCOPY, below_frontier_MSTORE,
    step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, exec_pure2_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, mload_def, update_var_def,
    word_add_n2w, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  simp[mcopy_def, write_memory_with_expansion_def, FLOOKUP_UPDATE,
    word_add_n2w, w2n_n2w, arithmeticTheory.LESS_MOD]
QED

Theorem concat_bytes_arm_full_run:
  (do arg_len <- emit_op MLOAD [Var sp];
      arg_data <- emit_op ADD [Var sp;Lit 32w];
      offset_op <- emit_op MLOAD [Var oq];
      dst <- emit_op ADD [Var dp;offset_op];
      emit_void MCOPY [dst;arg_data;arg_len];
      new_offset <- emit_op ADD [offset_op;arg_len];
      emit_void MSTORE [Var oq;new_offset]
   od) sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  lookup_var sp s = SOME (n2w srcbase) /\
  lookup_var dp s = SOME (n2w (B+32)) /\ lookup_var oq s = SOME (n2w ob) /\
  not_fresh_at sa sp /\ not_fresh_at sa dp /\ not_fresh_at sa oq /\
  ptr_covers G tn sp s (32+LENGTH bs) /\
  ptr_covers G tn dp s (bsz-32) /\ ptr_covers G tn oq s 32 /\
  ~ctx_has_dalloca ctx /\
  (!i. srcbase <= i /\ i < srcbase+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  (!i. ob <= i /\ i < ob+32 ==> i NOTIN tn.t_mem) /\
  mload srcbase s = n2w (LENGTH bs) /\ mload ob s = n2w k /\
  32+k+LENGTH bs <= bsz /\ B+bsz < dimword (:256) /\
  srcbase+32+LENGTH bs < dimword (:256) /\ ob+64 < dimword (:256) /\
  srcbase+32+LENGTH bs <= s.vs_alloca_next /\
  B+bsz <= s.vs_alloca_next /\ ob+64 <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u V G' tn'.
    u = (mstore ob (n2w (k+LENGTH bs))
      (mcopy (B+32+k) (srcbase+32) (LENGTH bs) s) with
      <|vs_vars := V; vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
    (!z. not_fresh_at sa z ==> FLOOKUP V z = FLOOKUP s.vs_vars z) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn') /\
    alloca_history func u /\ u.vs_current_bb = sb.cs_current_bb /\
    ~u.vs_halted /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    tn'.t_mem SUBSET tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
      op_taint tn' (Var z) = op_taint tn (Var z)) /\
    (!i. B+32+k <= i /\ i < B+32+k+LENGTH bs ==> i NOTIN tn'.t_mem) /\
    (!i. ob <= i /\ i < ob+32 ==> i NOTIN tn'.t_mem)
Proof
  strip_tac >>
  `B+32 < dimword (:256) /\ k < dimword (:256) /\ ob < dimword (:256) /\
   srcbase < dimword (:256) /\ srcbase+32 < dimword (:256) /\
   LENGTH bs < dimword (:256) /\ B+32+k < dimword (:256)` by decide_tac >>
  `?Gf tnf.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf /\
    tnf.t_mem SUBSET tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==>
      FLOOKUP Gf z = FLOOKUP G z /\ op_taint tnf (Var z) = op_taint tn (Var z)) /\
    (!i. B+32+k <= i /\ i < B+32+k+LENGTH bs ==> i NOTIN tnf.t_mem) /\
    (!i. w2n (n2w ob : bytes32) <= i /\ i < w2n (n2w ob : bytes32)+32 ==>
      i NOTIN tnf.t_mem)` by
    (irule concat_bytes_seq_ptr >> simp[] >>
     qexistsl_tac [`bsz`,`dp`,`oq`,`sp`,`n2w srcbase`] >> gvs[arithmeticTheory.ADD_COMM]) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> simp[]) >>
  drule concat_bytes_step_run >> disch_then (qspec_then `s` mp_tac) >>
  simp[eval_operand_def] >> strip_tac >>
  `w2n (n2w (B+32) + n2w k : bytes32) = B+32+k /\
   w2n (n2w srcbase + 32w : bytes32) = srcbase+32` by
    (rewrite_tac[word_add_n2w,w2n_n2w] >> simp[arithmeticTheory.LESS_MOD]) >>
  `run_inst_seq (emitted_insts sa sb) s =
   OK (mstore ob (n2w (k+LENGTH bs))
     (mcopy (B+32+k) (srcbase+32) (LENGTH bs) s) with vs_vars := V)` by
    fs[word_add_n2w] >>
  drule concat_bytes_code_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule concat_bytes_shape >> disch_then SUBST1_TAC >> simp[mk_inst_def,is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all concat_bytes_arm_mem_ok >> simp[]) >>
  qexistsl_tac [`V`,`Gf`,`tnf`] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (drule_all bodyFullUnwrapRunTheory.emitted_origin_ptr_path >> simp[]) >>
  conj_tac
  >- (`EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
      drule_all bodyFullUnwrapRunTheory.emitted_alloca_history >> simp[]) >>
  simp_tac pure_ss [mstore_def,mcopy_def,write_memory_with_expansion_def,
    LET_THM,venom_state_accessors,venom_state_accfupds] >> simp[]
QED

Theorem concat_bytes_arm_full_frame:
  u = (mstore ob (n2w (k+LENGTH bs))
    (mcopy (B+32+k) src (LENGTH bs) s) with
    <|vs_vars := V; vs_inst_idx := j|>) /\
  (!z. not_fresh_at sa z ==> FLOOKUP V z = FLOOKUP s.vs_vars z) /\
  mem_bytes_at src (LENGTH bs) s.vs_memory = bs /\
  32+k+LENGTH bs <= bsz /\
  (B+bsz <= ob \/ ob+64 <= B) /\ lo <= B /\ lo <= ob /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ local_ptrs_reserved cenv sa /\
  MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas binst.inst_id = SOME (B,bsz) /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas oinst.inst_id = SOME (ob,64) /\
  (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (ob+64 <= lb \/ lb+lsz <= ob)) /\
  local_ptrs_rel func cenv es.scopes s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  tn'.t_mem SUBSET tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
    op_taint tn' (Var z) = op_taint tn (Var z)) ==>
  (!H. stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es u) /\
  (ghost_inv_at D lo d cenv cx es G tn s ==> ghost_inv_at D lo d cenv cx es G' tn' u) /\
  (!sa0 G0 tn0 s0. ghost_kept_at lo cenv es sa0 G0 tn0 s0 G tn /\
    (!z. not_fresh_at sa0 z ==> not_fresh_at sa z) ==>
    ghost_kept_at lo cenv es sa0 G0 tn0 s0 G' tn') /\
  mem_bytes_at (B+32) (k+LENGTH bs) u.vs_memory = mem_bytes_at (B+32) k s.vs_memory ++ bs /\
  mload ob u = n2w (k+LENGTH bs) /\
  (!p n. (p+n <= B \/ B+bsz <= p) /\ (p+n <= ob \/ ob+64 <= p) ==>
    mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory)
Proof
  strip_tac >>
  `mem_bytes_at (B+32) (k+LENGTH bs) u.vs_memory = mem_bytes_at (B+32) k s.vs_memory ++ bs /\
   mload ob u = n2w (k+LENGTH bs) /\
   (!p n. (p+n <= B \/ B+bsz <= p) /\ (p+n <= ob \/ ob+64 <= p) ==>
     mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory)` by
    (irule concat_bytes_endpoint_memory >> simp[] >> qexistsl_tac [`V`,`j`,`src`] >> simp[]) >>
  conj_tac
  >- (gen_tac >> strip_tac >> drule_all concat_bytes_endpoint_state >> simp[]) >>
  conj_tac
  >- (strip_tac >>
      `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
       u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
       u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
       (!z. not_fresh_at sa z ==> lookup_var z u = lookup_var z s)` by
        (drule_all concat_bytes_endpoint_fields >> strip_tac >>
         simp[] >> qpat_x_assum `u = _` SUBST1_TAC >>
         simp_tac pure_ss [mstore_def,mcopy_def,write_memory_with_expansion_def,
           LET_THM,venom_state_accfupds,venom_state_accessors] >> simp[]) >>
      `allocas_from lo u /\ lo <= u.vs_alloca_next` by
        (fs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
      `stor_taint_ok_at D tn' u` by
        fs[bodyPtrDefsTheory.ghost_inv_at_def,bodyPtrDefsTheory.stor_taint_ok_at_def] >>
      irule ghost_inv_at_local_window_transport >> simp[] >>
      qexistsl_tac [`G`,`es`,`func`,`s`,`sa`,`tn`] >> simp[] >> gvs[] >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >> conj_tac
          >- (first_x_assum irule >> metis_tac[arithmeticTheory.ADD_COMM]) >>
          fs[SUBSET_DEF]) >>
      fs[SUBSET_DEF]) >>
  conj_tac
  >- (rpt strip_tac >> irule ghost_kept_at_clean_suffix >>
      qexistsl_tac [`G`,`tn`] >> simp[] >> metis_tac[]) >>
  gvs[] >> metis_tac[]
QED
