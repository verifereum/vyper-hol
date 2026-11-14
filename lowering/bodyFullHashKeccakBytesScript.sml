(* Direct readonly Keccak certificates at an arbitrary allocation bound. *)
Theory bodyFullHashKeccakBytes
Ancestors
  bodyPtrHashBuiltinsKeccakBytesRun bodyPtrHashBuiltinsCursor
  bodyPtrHashBuiltinsKeccakShape
  bodyFullGhostFrame instSeqPtrLo fragGasSeqPtr ptrSafetyTransport
  exprSimHash exprLoweringProps allocaHistoryFragment bodyPtrDefs
  loweringStateRelDefs venomState venomInst
  ptrDiscipline words list finite_map

Theorem bytes_origin_frame[local]:
  !x sa op sb s b G base cap bs ctx fn tn bb lo t explicit PG.
  compile_keccak256_bytes (Var x) sa = (op,sb) /\ not_fresh_at sa x /\
  eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (base:num,cap:num) /\ base <= b /\
  b+32+LENGTH bs <= base+cap /\
  b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf)) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==> FLOOKUP Gf z = FLOOKUP G z /\
      op_taint tnf (Var z) = op_taint tn (Var z))
Proof
  rpt gen_tac >> strip_tac >> drule_all hash_keccak_bytes_inst_seq >>
  disch_then (qspecl_then [`ARB`, `fn`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >> gen_tac >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn'` by
    (drule_all hash_keccak_bytes_inst_seq >>
     disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
     `G' = G'' /\ tn' = tn''` by metis_tac[inst_seq_ptr_ghost_unique] >>
     gvs[] >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `D` >> simp[]) >>
  drule hash_keccak_bytes_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED

Theorem bytes_ghost_cursor:
  ghost_inv_at D lo d cenv cx es G tn (s with vs_inst_idx := k) <=>
  ghost_inv_at D lo d cenv cx es G tn s
Proof
  Cases_on `d` >>
  simp[ghost_inv_at_def, ptr_covers_def, lookup_var_def,
    return_buf_ptr_def, stor_taint_ok_at_def, allocas_from_def] >>
  PairCases_on `x` >>
  simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem hash_bytes_keccak_joint_run:
  !ctx fn PG G tn s bb x sa op sb b base cap bs cenv cx es d lo explicit.
    compile_keccak256_bytes (Var x) sa = (op,sb) /\ not_fresh_at sa x /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\ base <= b /\
    b+32+LENGTH bs <= base+cap /\
    b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
    local_ptrs_reserved cenv sa /\
    (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s ==>
    ?t Gf tnf.
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_current_bb = s.vs_current_bb /\
      eval_operand op t = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
      op_taint tnf op = {} /\ op_prov Gf op = NONE /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf)) /\
      (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s) /\
      t.vs_alloca_next = s.vs_alloca_next /\
      (!H D. stmt_state_rel (H:(bool # 256 word # type_value) list # num list) ctx fn cenv cx es s /\
        ghost_inv_at D lo d cenv cx es G tn s ==>
        stmt_state_rel H ctx fn cenv cx es t /\
        ghost_inv_at D lo d cenv cx es Gf tnf t /\
        ghost_kept_at lo cenv es sa G tn s Gf tnf) /\
      eval_operand op (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) =
        SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
      (!H D. stmt_state_rel (H:(bool # 256 word # type_value) list # num list) ctx fn cenv cx es s /\
        ghost_inv_at D lo d cenv cx es G tn s ==>
        stmt_state_rel H ctx fn cenv cx es
          (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
        ghost_inv_at D lo d cenv cx es Gf tnf
          (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
      (fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s ==>
        alloca_history fn
          (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))
Proof
  rpt gen_tac >> strip_tac >>
  `!z. Var x = Var z ==> not_fresh_at sa z` by simp[] >>
  drule_all compile_keccak256_bytes_run >> strip_tac >>
  drule_all bytes_origin_frame >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >> simp[] >>
  `t.vs_current_bb = s.vs_current_bb /\
   t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    (qpat_x_assum `(t with vs_vars := s.vs_vars) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  simp[] >> conj_asm1_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (drule_all compile_keccak256_bytes_frame >> strip_tac >> gvs[]) >>
      conj_tac
      >- (irule ghost_inv_at_exterior_frame >> simp[] >>
          qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >> simp[]) >>
      simp[ghost_kept_at_def]) >>
  conj_tac
  >- (simp[stmt_state_rel_inst_idx, bytes_ghost_cursor] >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!H D. _` (qspecl_then [`H`, `D`] mp_tac) >> simp[]) >>
  strip_tac >> drule hash_keccak_bytes_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule alloca_history_run_inst_seq >> goal_assum (drule_at Any) >>
  simp[] >> gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]
QED
