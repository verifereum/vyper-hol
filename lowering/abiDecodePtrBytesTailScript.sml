(* Pointer certificates for the exact runtime bytes tail. *)
Theory abiDecodePtrBytesTail
Ancestors
  abiDecoderBytesRuntime abiDecoderRange abiDecodeStaticProps abiDecodePtrRead abiDecodePtrNormalized
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq bodyPtrBopScalarOutcome
  abiDecodePtrMemberFrame assignTuplePtrCopyLen fragGasSeqPtr
  assignTuplePtrLocalBytesCopy assignTuplePtrBytesCopy
  emitHelperProps exprLoweringProps compileEnv emitHelper freshWrites
  venomState venomExecSemantics venomInst ptrDiscipline typedCopyPtr bodyPtrDefs
  list pred_set finite_map words arithmetic

(* Rounding is scalar even though the following address ADD is not. *)
Theorem abi_decode_bytes_round_scalar:
  emit_op ADD [cnt;Lit 31w] sa = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,sb) /\
  cnt IN A /\ Lit 31w IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  bop_scalar_seq R A (emitted_insts sa sb)
    (rounded INSERT mask INSERT up INSERT A)
Proof
  strip_tac >>
  `!x. x IN R ==> not_fresh_at c1 x` by
    (qpat_assum `emit_op ADD _ sa = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!x. x IN R ==> not_fresh_at c2 x` by
    (qpat_assum `emit_op NOT _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `bop_scalar_seq R A (emitted_insts sa c1) (up INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[cnt;Lit 31w]`] >> simp[]) >>
  `bop_scalar_seq R (up INSERT A) (emitted_insts c1 c2)
     (mask INSERT up INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`NOT`, `[Lit 31w]`] >> simp[]) >>
  `bop_scalar_seq R (mask INSERT up INSERT A) (emitted_insts c2 sb)
     (rounded INSERT mask INSERT up INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`AND`, `[up;mask]`] >> simp[]) >>
  imp_res_tac emit_op_extends >>
  `emitted_insts sa c2 = emitted_insts sa c1 ++ emitted_insts c1 c2` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa c2 ++ emitted_insts c2 sb` by
    (irule emitted_insts_append >> simp[APPEND_ASSOC]) >>
  simp[] >> irule bop_scalar_seq_append >>
  qexists_tac `mask INSERT up INSERT A` >> simp[] >>
  irule bop_scalar_seq_append >> qexists_tac `up INSERT A` >> simp[]
QED

Theorem abi_decode_bytes_round_sequence:
  emit_op ADD [cnt;Lit 31w] sa = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,sb) /\
  eval_operand cnt s = SOME (n2w c) /\
  c+31 < dimword(:256) /\ fresh_vars_wrt sa s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand rounded t = SOME (n2w (32*((c+31) DIV 32))) /\
    fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  `eval_operand (Lit 31w) s = SOME 31w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  `eval_operand (Lit 31w) s1 = SOME 31w` by simp[eval_operand_def] >>
  drule_all emit_op_NOT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand up s2 = SOME ((n2w c:bytes32)+31w)` by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 sb) s2 = OK t` >>
  rpt (qpat_x_assum `!a. a < LENGTH _ ==> _` kall_tac) >>
  rpt (qpat_x_assum `LENGTH _.vs_memory = _` kall_tac) >>
  rpt (qpat_x_assum `same_blocks _ _` kall_tac) >>
  drule_all (abi_decode_pure_emit_frame |> Q.INST [`opc` |-> `ADD`] |> SRULE []) >>
  strip_tac >>
  drule_all abi_decode_NOT_emit_frame >> strip_tac >>
  drule_all abi_decode_AND_emit_frame >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  ntac 2 (drule_all abi_decode_sequence_chain >> strip_tac) >>
  qexists_tac `t` >> simp[abi_decode_bytes_round_word] >> metis_tac[]
QED


Theorem abi_decode_bytes_round_ptr:
  emit_op ADD [cnt;Lit 31w] sa = (up,c1) /\
  emit_op NOT [Lit 31w] c1 = (mask,c2) /\
  emit_op AND [up;mask] c2 = (rounded,sb) /\
  eval_operand cnt s = SOME (n2w c) /\
  c+31 < dimword(:256) /\ fresh_vars_wrt sa s /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\ ~ctx_has_dalloca ctx /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    eval_operand rounded t = SOME (n2w (32*((c+31) DIV 32))) /\
    op_prov G' rounded = NONE /\ op_taint tn' rounded = {} /\
    fresh_vars_wrt sb t /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all abi_decode_bytes_round_sequence >> strip_tac >>
  `bop_scalar_seq R {cnt;Lit 31w} (emitted_insts sa sb)
    (rounded INSERT mask INSERT up INSERT {cnt;Lit 31w})` by
    (irule abi_decode_bytes_round_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {cnt;Lit 31w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def,op_taint_def]) >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `G'`, `tn'`] >>
  `t.vs_inst_idx = s.vs_inst_idx` by
    (qpat_assum `t = s with vs_vars := _`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `fresh_vars_wrt sb (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_x_assum `fresh_vars_wrt sb t` mp_tac >>
     simp[fresh_vars_wrt_def, lookup_var_def]) >>
  `eval_operand rounded (t with vs_inst_idx := LENGTH sb.cs_current_insts) =
     eval_operand rounded t` by
    (Cases_on `rounded` >> simp[NoAsms,eval_operand_def,lookup_var_def]) >>
  `op_prov G' rounded = NONE /\ op_taint tn' rounded = {}` by
    (qpat_x_assum `!op. op IN rounded INSERT _ ==> _`
       (qspec_then `rounded` mp_tac) >> simp[]) >>
  `t with vs_inst_idx := LENGTH sb.cs_current_insts =
     s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>` by
    (qpat_assum `t = s with vs_vars := _`
       (fn th => once_rewrite_tac[th]) >> simp[NoAsms]) >>
  simp[] >> conj_tac
  >- (qpat_assum `t = s with vs_vars := _`
        (fn th => once_rewrite_tac[th]) >> simp[venom_state_component_equality]) >>
  rpt strip_tac >> simp[lookup_var_def] >>
  first_x_assum irule >> simp[]
QED

(* Address formation needs coverage, not initialization of the output buffer. *)
Theorem abi_decode_ptr_output_address_covers:
  ptr_covers G tn dst s cap /\ lookup_var dst s = SOME b /\
  q+k <= cap /\ w2n b+cap < dimword(:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var dst;pos] [out])
      (update_var out (b+n2w q) s))
    (step_taint (mk_inst id ADD [Var dst;pos] [out]) s
      (update_var out (b+n2w q) s) tn)
    out (update_var out (b+n2w q) s with vs_inst_idx := idx) k
Proof
  strip_tac >>
  `w2n (b+n2w q) = w2n b+q` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  fs[ptr_covers_def] >>
  simp[ptr_covers_def, copy_len_binop_ghost_frame,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE] >>
  qexistsl_tac [`b'`, `sz'`] >> simp[] >> decide_tac
QED

(* The output ADD exposes the exact ghosts needed by the following store. *)
Theorem abi_decode_ptr_output_address:
  emit_op ADD [Var dst;pos] sa = (addr,sb) /\
  ptr_covers G tn dst s cap /\ lookup_var dst s = SOME b /\
  eval_operand pos s = SOME (n2w q) /\
  op_taint tn (Var dst) = {} /\ op_taint tn pos = {} /\
  ~ctx_has_dalloca ctx /\ q+k <= cap /\ w2n b+cap < dimword(:256) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  !out. addr = Var out ==>
  let u = update_var out (b+n2w q) s;
      t = u with vs_inst_idx := LENGTH sb.cs_current_insts;
      H = step_prov PG G (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) u;
      tm = step_taint (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) s u tn
  in run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
     inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tm /\
     ptr_covers H tm out t k /\ lookup_var out t = SOME (b+n2w q) /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts /\
     tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
     tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
     (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
       op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `!out. ptr_inst_ok D 0 0 ctx func G tn
    (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) s` by
    (gen_tac >> irule ptr_inst_ok_copy_len_binop >> simp[eval_operand_def]) >>
  `!out. step_inst_base (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) s =
    OK (update_var out (b+n2w q) s)` by
    simp[step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  rpt strip_tac >> gvs[] >> simp[] >>
  conj_tac >- simp[run_inst_seq_def, update_var_def, venom_state_component_equality] >>
  conj_tac >- simp[inst_seq_ptr_def] >>
  conj_tac
  >- (irule (abi_decode_ptr_output_address_covers
        |> SRULE [ghostPcTransportPtrTheory.ptr_covers_inst_idx]) >>
      simp[] >> qexists_tac `cap` >> simp[]) >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       copy_len_binop_ghost_frame] >>
  conj_tac >- simp[step_taint_def, imm_taint_def, mk_inst_def] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  pure_rewrite_tac[GSYM update_var_def, GSYM mk_inst_def] >>
  simp[FLOOKUP_UPDATE, copy_len_binop_ghost_frame]
QED

(* The copy covers the header and payload; the zero store covers the
   remaining padding.  Their windows may overlap, including when c=0. *)
Theorem abi_decode_bytes_tail_initialized:
  (!i. d+32*((c+31) DIV 32) <= i /\
       i < d+32*((c+31) DIV 32)+32 ==> i NOTIN tm.t_mem) /\
  (!i. d <= i /\ i < d+32+c ==> i NOTIN tf.t_mem) /\
  (!i. ~(d <= i /\ i < d+32+c) ==>
       (i IN tf.t_mem <=> i IN tm.t_mem)) ==>
  !i. d <= i /\ i < d+32+32*((c+31) DIV 32) ==> i NOTIN tf.t_mem
Proof
  strip_tac >> rpt strip_tac >>
  Cases_on `i < d+32+c`
  >- gvs[] >>
  `32*((c+31) DIV 32) < c+32` by
    simp[abi_decode_bytes_round_bounds] >>
  `d+32*((c+31) DIV 32) <= i /\
   i < d+32*((c+31) DIV 32)+32` by decide_tac >>
  `i NOTIN tm.t_mem` by (first_x_assum irule >> simp[]) >>
  `~(d <= i /\ i < d+32+c)` by decide_tac >>
  metis_tac[]
QED

Theorem abi_decode_bytes_store_copy_ptr:
  emit_void MSTORE [Var last;Lit 0w] sa = ((),sb) /\
  emit_op ADD [Lit 32w;cnt] sb = (sz,sc) /\
  emit_void MCOPY [Var dst;Var src;sz] sc = ((),sd) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\
  (!x. cnt = Var x ==> not_fresh_at sa x) /\
  lookup_var last s = SOME (n2w (d+q)) /\ ptr_covers G tn last s 32 /\
  lookup_var dst s = SOME (n2w d) /\ ptr_covers G tn dst s (32+c) /\
  abi_decode_ptr_window G tn s src (n2w a) (32+c) /\
  eval_operand cnt s = SOME (n2w c) /\ op_taint tn cnt = {} /\
  d+q < dimword(:256) /\ d < dimword(:256) /\ a < dimword(:256) /\
  32+c < dimword(:256) /\ q = 32*((c+31) DIV 32) /\
  (a+32+c <= d \/ d+q+32 <= a) ==>
  ?Gf tnf t.
    run_inst_seq (emitted_insts sa sd) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sd) s Gf tnf /\
    (!i. d <= i /\ i < d+32+q ==> i NOTIN tnf.t_mem) /\
    abi_decode_ptr_window Gf tnf t src (n2w a) (32+c) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!i. ~(d <= i /\ i < d+32+q) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {}` by
    simp[eval_operand_def,op_taint_def] >>
  `w2n (n2w (d+q):bytes32) = d+q /\ w2n (n2w a:bytes32) = a` by simp[] >>
  qpat_assum `abi_decode_ptr_window G tn s src _ _`
    (mp_then (Pat `abi_decode_ptr_window _ _ _ _ _ _`) mp_tac
      abi_decode_ptr_store_windows) >>
  disch_then (drule_at (Pat `emit_void _ _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  simp[] >>
  disch_then (qspecl_then [`func`, `ctx`, `PG`, `D`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `inst_seq_ptr D 0 ctx func PG G tn _ s G tn1` >>
  rename1 `t1.vs_inst_idx = LENGTH sb.cs_current_insts` >>
  suspend "prepare_copy"
QED

Resume abi_decode_bytes_store_copy_ptr[prepare_copy]:
  `t1 = mstore (d+q) 0w s with vs_inst_idx := LENGTH sb.cs_current_insts` by
    (qpat_assum `emit_void MSTORE _ sa = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_write2_def,
          eval_operand_def, w2n_n2w] >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `eval_operand cnt t1 = SOME (n2w c) /\ op_taint tn1 cnt = {}` by
    (Cases_on `cnt` >> gvs[eval_operand_def,op_taint_def]) >>
  `eval_operand (Lit 32w) t1 = SOME 32w /\ op_taint tn1 (Lit 32w) = {}` by
    simp[eval_operand_def,op_taint_def] >>
  `?sizev. sz = Var sizev` by
    (drule emitted_insts_emit_op >> strip_tac >> simp[]) >>
  qpat_x_assum `sz = Var sizev` SUBST_ALL_TAC >>
  drule_all (emit_copy_len_binop_normalized_ptr
    |> Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`func`, `PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx func PG G tn1 _ t1 G2 tn2` >>
  rename1 `t2.vs_inst_idx = LENGTH sc.cs_current_insts` >>
  suspend "copy"
QED

Resume abi_decode_bytes_store_copy_ptr[copy]:
  `!p. not_fresh_at sa p ==> not_fresh_at sb p` by
    (qpat_assum `emit_void MSTORE _ sa = _`
      (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     gvs[not_fresh_at_def]) >>
  `lookup_var dst t2 = SOME (n2w d) /\
   ptr_covers G2 tn2 dst t2 (32+c)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `abi_decode_ptr_window G2 tn2 t2 src (n2w a) (32+c)` by
    (irule abi_decode_ptr_window_frame >>
     qexistsl_tac [`G`, `t1`, `tn1`] >> simp[] >> gvs[]) >>
  `eval_operand (Var sizev) t2 = SOME (n2w (32+c))` by
    simp[eval_operand_def, word_add_n2w] >>
  suspend "mcopy"
QED

Resume abi_decode_bytes_store_copy_ptr[mcopy]:
  `w2n (n2w d:bytes32) = d /\ c <= q` by
    (mp_tac (Q.SPEC `c` (GEN_ALL abi_decode_bytes_round_bounds)) >>
     simp[] >> decide_tac) >>
  qpat_assum `abi_decode_ptr_window G2 tn2 t2 src _ _`
    (mp_then (Pat `abi_decode_ptr_window _ _ _ _ _ _`) mp_tac
      abi_decode_ptr_copy_windows) >>
  disch_then (drule_at (Pat `emit_void _ _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (qspecl_then [`32+c`, `func`, `ctx`, `PG`, `D`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  rename1 `inst_seq_ptr D 0 ctx func PG G2 tn2 _ t2 G2 tn3` >>
  rename1 `t3.vs_inst_idx = LENGTH sd.cs_current_insts` >>
  suspend "compose"
QED

Resume abi_decode_bytes_store_copy_ptr[compose]:
  qpat_assum `emit_op ADD _ sb = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc)` by
    simp[mk_inst_def,is_terminator_def] >>
  `run_inst_seq (emitted_insts sa sb) s =
     OK (t1 with vs_inst_idx := s.vs_inst_idx) /\
   run_inst_seq (emitted_insts sb sc) t1 =
     OK (t2 with vs_inst_idx := t1.vs_inst_idx)` by simp[] >>
  qpat_assum `run_inst_seq (emitted_insts sa sb) s = OK (t1 with vs_inst_idx := s.vs_inst_idx)`
    (mp_then (Pat `run_inst_seq (emitted_insts sa sb) s = _`) mp_tac
      emitted_insts_join_normalized_ptr) >>
  disch_then drule_all >> strip_tac >>
  qpat_assum `run_inst_seq (emitted_insts sa sc) s = _`
    (mp_then (Pat `run_inst_seq (emitted_insts sa sb) s = _`) mp_tac
      emitted_insts_join_normalized_ptr) >>
  disch_then drule_all >> strip_tac >>
  qexistsl_tac [`G2`, `tn3`, `t3`] >> simp[] >>
  conj_tac >- suspend "initialized" >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  suspend "exterior"
QED

Resume abi_decode_bytes_store_copy_ptr[initialized]:
  `d+(32*((c+31) DIV 32)+32) = d+32+32*((c+31) DIV 32)` by decide_tac >>
  qpat_assum `d+(_+32) = _` (fn th => pure_rewrite_tac [th]) >>
  mp_tac (abi_decode_bytes_tail_initialized
    |> Q.INST [`d` |-> `d`, `c` |-> `c`, `tm` |-> `tn2`, `tf` |-> `tn3`]) >>
  (impl_tac >-
    (qpat_assum `abi_decode_ptr_window G tn1 t1 last _ _` mp_tac >>
     qpat_assum `abi_decode_ptr_window G2 tn3 t3 dst _ _` mp_tac >>
     qpat_assum `tn2.t_mem = tn1.t_mem` mp_tac >>
     qpat_assum `!i. ~(_ /\ _) ==> mem_bytes_at _ _ t3.vs_memory = _ /\ _` mp_tac >>
     qpat_assum `d+q < dimword(:256)` mp_tac >>
     qpat_assum `q = _` mp_tac >>
     qpat_assum `w2n (n2w d:bytes32) = d` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_ptr_window_def] >> rpt strip_tac >>
     rpt conj_tac >> rpt strip_tac >> simp[])) >>
  simp[]
QED

Resume abi_decode_bytes_store_copy_ptr[exterior]:
  qpat_assum `!i. ~(_ /\ _) ==> mem_bytes_at _ _ t3.vs_memory = _ /\ _` mp_tac >>
  qpat_assum `!i. _ \/ _ ==> mem_bytes_at _ _ t1.vs_memory = _ /\ _` mp_tac >>
  qpat_assum `t1 = _` mp_tac >>
  qpat_assum `t2.vs_memory = t1.vs_memory` mp_tac >>
  qpat_assum `tn2.t_mem = tn1.t_mem` mp_tac >>
  qpat_assum `c <= q` mp_tac >>
  qpat_assum `q = _` mp_tac >>
  qpat_assum `w2n (n2w d:bytes32) = d` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `t1.vs_memory = (mstore (d+q) 0w s).vs_memory` by simp[] >>
  `~(d <= i /\ i < d+32+c)` by decide_tac >>
  `~(d+32*((c+31) DIV 32) <= i) \/
   ~(i < d+(32*((c+31) DIV 32)+32))` by decide_tac >>
  metis_tac[]
QED

Finalise abi_decode_bytes_store_copy_ptr
