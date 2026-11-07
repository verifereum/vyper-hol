(* The decoder's length load and payload address, before any guard. *)
Theory abiDecodePtrHeaderLoad
Ancestors
  assignTuplePtrLoadStep exprSimAccounts freshWrites fragGasPathPtr
  abiDecodeStaticProps bodyPtrDefs emitHelperProps exprLoweringProps compileEnv fragExec venomState ptrDiscipline stateFrame words arithmetic

Theorem abi_decode_header_load_path_ptr:
  emit_op MLOAD [Var p] sa = (len,sm) /\
  emit_op ADD [Var p; Lit 32w] sm = (src,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var p s = SOME w /\ not_fresh_at sa p /\
  ptr_covers G tn p s (32+n) /\
  w2n w + 32+n < dimword (:256) /\
  (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tn.t_mem) ==>
  ?t G' tn' q r.
    src = Var q /\ len = Var r /\
    not_fresh_at sb q /\ not_fresh_at sb r /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    eval_operand len t = SOME (mload (w2n w) s) /\
    op_prov G' len = NONE /\ op_taint tn' len = {} /\
    lookup_var q t = SOME (w+32w) /\ ptr_covers G' tn' q t n /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  drule_all fn_has_code_split >> strip_tac >>
  `ptr_covers G tn p s 32` by
    (fs[ptr_covers_def] >> qexistsl_tac [`w`, `b`, `sz'`] >> simp[]) >>
  `!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn.t_mem` by
    (gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  drule_all emit_mload_member_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `len = Var length_reg` >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK u)` >>
  qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `p` mp_tac) >>
  disch_then (mp_tac o SPEC_ALL) >>
  impl_tac >- simp[] >> strip_tac >>
  `lookup_var p u = SOME w /\ op_taint tm (Var p) = {}` by
    (qpat_x_assum `ptr_covers G tn p s (32+n)` mp_tac >> simp[ptr_covers_def]) >>
  `?b cap. FLOOKUP H p = SOME (b,cap) /\ b <= w2n w /\
      w2n w + (32+n) <= b+cap` by
    (qpat_x_assum `ptr_covers G tn p s (32+n)` mp_tac >> simp[ptr_covers_def]) >>
  drule_all emit_add_member_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `src = Var payload_reg` >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `w2n (w+32w) = w2n w+32` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  `ptr_covers G' tn' payload_reg t n` by
    (simp[ptr_covers_def] >> qexistsl_tac [`b`, `cap`] >> decide_tac) >>
  qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `length_reg` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx)` by
    suspend "frame" >>
  `!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qexistsl_tac [`t`, `G'`, `tn'`, `payload_reg`, `length_reg`] >>
  asm_rewrite_tac[eval_operand_def] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `op_prov H (Var length_reg) = NONE` mp_tac >>
  simp[op_prov_def]
QED

Resume abi_decode_header_load_path_ptr[frame]:
  qpat_x_assum `state_frame t = _` mp_tac >>
  qpat_x_assum `state_frame u = _` mp_tac >>
  simp[state_frame_def]
QED

Finalise abi_decode_header_load_path_ptr
