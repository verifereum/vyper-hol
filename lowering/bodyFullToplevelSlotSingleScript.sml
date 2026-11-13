(* Single-slot TopLevelName materialization: memory and pointer checks on
   the same operational load/store run. *)
Theory bodyFullToplevelSlotSingle
Ancestors
  bodyFullUnwrapRun exprPtrUnwrapSingleSegment bodyStorageCopyMemory
  exprPtrUnwrapEnsureSingle bodyFullUnwrapSlotPost exprPtrUnwrapStoragePost
  exprLoweringProps bodyPtrDefs venomState venomInst words list rich_list
  bodyMemEcArithPrefix exprPtrUnwrapAllocation bufferAllocationExecution fragGasSeqPtr
  fragGasOriginPtrDead fragGasOriginPtr exprPtrUnwrapLoopEntry

Theorem toplevel_slot_single_suffix_origin_ptr:
  compile_expr cenv ty (TopLevelName ann nsid) si = (LocatedValue vt p,sm) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  fn_has_code sa sb func /\
  emitted_insts sa sb =
    [mk_inst id (if p.ptr_location=LocStorage then SLOAD else TLOAD)
       [p.ptr_operand] [out];
     mk_inst (id+1) MSTORE [Var root;Var out] []] /\
  eval_operand p.ptr_operand s = SOME key /\ op_taint tn p.ptr_operand = {} /\
  root <> out /\ ptr_covers G tn root s 32 /\ lookup_var root s = SOME addr /\
  w2n addr + 32 < dimword (:256) /\ w2n addr + 32 <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf t.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf) /\
    t = mstore (w2n addr)
      (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) s key)
      (update_var out
        (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) s key) s) /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) UNION
      {w2n addr+k | k IN key_taint
        (if p.ptr_location=LocStorage then tn.t_stor else tn.t_trans) key} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x <> out ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!x k. x <> out /\ ptr_covers G tn x s k ==> ptr_covers Gf tnf x t k)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  mp_tac (Q.INST [`fn` |-> `func`, `src` |-> `p.ptr_operand`,
    `load` |-> `if p.ptr_location=LocStorage then SLOAD else TLOAD`]
    copy_single_slot_segment) >>
  (impl_tac >- (simp[] >> Cases_on `p.ptr_location=LocStorage` >> simp[])) >>
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (asm_rewrite_tac[] >> irule body_storage_singleton_mem_ok >>
     simp[eval_operand_def] >> qexists `w2n addr` >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_LENGTH_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (asm_rewrite_tac[] >> Cases_on `p.ptr_location=LocStorage` >>
     simp[mk_inst_def, is_terminator_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (irule emitted_origin_ptr_path >> metis_tac[]) >>
  qexistsl [`Gf`, `tnf`, `t`] >> asm_rewrite_tac[] >>
  Cases_on `p.ptr_location=LocStorage` >> gvs[]
QED

Theorem toplevel_slot_alloc_origin_ptr:
  compile_expr cenv ty (TopLevelName ann nsid) si = (LocatedValue vt p,sm) /\
  compile_alloc_buffer nb sa = (buf,sb) /\ fn_has_code sa sb func /\
  nb < dimword (:256) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out u.
    buf.buf_operand = Var out /\ buf.buf_size = nb /\
    u = update_var out (n2w (buffer_allocation_base s sa.cs_next_id))
      (buffer_allocation_fields s sa.cs_next_id nb) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),
       step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [out]) u,
       step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s u tn)
Proof
  strip_tac >> drule_all unwrap_alloc_generated_step >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK u` >>
  `u.vs_requests = s.vs_requests` by
    (simp[Abbr `u`, buffer_allocation_fields_def, update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (simp[Abbr `inst`] >> irule unwrap_alloc_ptr_check >>
     simp[] >> qexists `u` >> simp[]) >>
  `inst_seq_ptr D lo ctx func PG G tn [inst] s
     (step_prov PG G inst u) (step_taint inst s u tn)` by
    simp[inst_seq_ptr_def] >>
  `run_inst_seq [inst] s = OK u` by simp[run_inst_seq_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[ec_alloc_buffer_mem_ok] >>
  drule unwrap_alloc_current_block >> strip_tac >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),
      step_prov PG G inst u, step_taint inst s u tn)` by
    (irule emitted_origin_ptr_path >> metis_tac[]) >>
  qexistsl [`out`, `u`] >> gvs[Abbr `u`, Abbr `inst`]
QED

(* The raw endpoints and ghost updates are selected once, not once per H. *)
Theorem toplevel_slot_single_common_run:
  compile_expr cenv ty (TopLevelName ann nsid) si = (LocatedValue vt p,sm) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  compile_alloc_buffer nb sa = (buf,mid) /\ buf.buf_operand = Var root /\
  fn_has_code sa mid func /\ nb < dimword (:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  u = update_var root (n2w (buffer_allocation_base s sa.cs_next_id))
        (buffer_allocation_fields s sa.cs_next_id nb) /\
  a = u with vs_inst_idx := LENGTH mid.cs_current_insts /\
  G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  same_blocks mid sb /\ isPREFIX mid.cs_current_insts sb.cs_current_insts /\
  fn_has_code mid sb func /\
  emitted_insts mid sb =
    [mk_inst id (if p.ptr_location=LocStorage then SLOAD else TLOAD) [p.ptr_operand] [out];
     mk_inst (id+1) MSTORE [Var root;Var out] []] /\
  eval_operand p.ptr_operand a = SOME key /\ op_taint tn0 p.ptr_operand = {} /\
  root <> out /\ ptr_covers G0 tn0 root a 32 /\ lookup_var root a = SOME addr /\
  w2n addr + 32 < dimword (:256) /\ w2n addr + 32 <= a.vs_alloca_next /\
  allocas_from lo a /\ ~a.vs_halted /\ a.vs_current_bb = mid.cs_current_bb /\
  a.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?Gf tnf t.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)) /\
    t = mstore (w2n addr)
      (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) a key)
      (update_var out
        (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) a key) a) /\
    tnf.t_mem = (tn0.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) UNION
      {w2n addr+k | k IN key_taint
        (if p.ptr_location=LocStorage then tn0.t_stor else tn0.t_trans) key} /\
    tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
    (!x. x <> out ==> FLOOKUP Gf x = FLOOKUP G0 x /\
       op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
    (!x k. x <> out /\ ptr_covers G0 tn0 x a k ==> ptr_covers Gf tnf x t k)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  qabbrev_tac `D0 = <|d_stor := K (K {}); d_trans := K (K {});
    d_imm := K {}; d_ret := K {}|>` >>
  mp_tac (Q.INST [`D` |-> `D0`, `sb` |-> `mid`] toplevel_slot_alloc_origin_ptr) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0)` by
    (gvs[] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp a` by simp[] >>
  drule_all toplevel_slot_single_suffix_origin_ptr >>
  disch_then (qspecl_then [`explicit`, `PG`, `D0`] strip_assume_tac) >>
  `gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    metis_tac[gas_origin_ptr_path_append, APPEND_NIL] >>
  qexistsl [`Gf`, `tnf`, `t`] >> asm_rewrite_tac[] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
  gvs[Abbr `D0`]
QED
