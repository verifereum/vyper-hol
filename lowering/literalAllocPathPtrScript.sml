(* A literal allocation obtains its ghost and structural resources from the
   same concrete execution, without requiring an expression postcondition. *)
Theory literalAllocPathPtr
Ancestors
  normalizerAllocationFrame allocaSiteResource revertAllocationPtr fragExecPtr
  fragGasSeqPtr fragGasPathPtr allocationPtr exprLoweringProps venomMemDefs
  venomInst venomState venomExecSemantics ptrDiscipline ptrSafeRun
  finite_map words arithmetic decoderGhostFramePtr loweringHalt
  exprSimCopy fragExec emitHelperProps rich_list venomInstProofs bodyPtrDefs

Theorem literal_alloca_step_resources_ptr:
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w cap)] [root]) (fn_insts fn) /\
  cap < dimword(:256) /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?t b.
    step_inst_base (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s = OK t /\
    lookup_var root t = SOME (n2w b) /\ b+cap < dimword(:256) /\
    FLOOKUP t.vs_allocas id = SOME (b,cap) /\
    ptr_covers
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w cap)] [root]) t)
      (step_taint (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s t tn)
      root t cap /\
    alloca_inv t /\ alloca_room ctx fn t /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz)) /\
    (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w)
Proof
  strip_tac >>
  drule_at (Pat `alloca_room _ _ _`)
    (SRULE [] (Q.INST [`inst` |-> `mk_inst id ALLOCA [Lit (n2w cap)] [root]`,
      `n` |-> `n2w cap`, `out` |-> `root`]
      literal_alloca_structural_resources)) >>
  disch_then (drule_at (Pat `MEM (mk_inst _ _ _ _) (fn_insts _)`)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `step_inst_base (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s = OK t` by
    fs[step_inst_base_def, mk_inst_def] >>
  `FLOOKUP t.vs_allocas id = SOME (b,cap)` by fs[mk_inst_def] >>
  `b+cap < dimword(:256)` by
    (drule_all alloca_site_registered_below >>
     drule alloca_room_next_lt >> simp[]) >>
  qexistsl [`t`,`b`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  irule (cj 1 alloca_bounds_ptr_covers) >> simp[] >>
  conj_tac >- metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  strip_tac >>
  `id NOTIN FDOM s.vs_allocas` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  drule_at (Pat `MEM _ (fn_insts _)`) alloca_room_fresh >>
  simp[mk_inst_def, FLOOKUP_DEF] >>
  disch_then (qspecl_then [`s`,`ctx`] mp_tac) >>
  simp[FLOOKUP_DEF]
QED

Theorem literal_alloca_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ALLOCA [Lit n] [root]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  step_inst_base (mk_inst id ALLOCA [Lit n] [root]) s = OK t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit n] [root]) t)
    (step_taint (mk_inst id ALLOCA [Lit n] [root]) s t tn)
    (OK (t with vs_inst_idx := s.vs_inst_idx+1))
Proof
  strip_tac >>
  `inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id ALLOCA [Lit n] [root]] s
    (step_prov PG G (mk_inst id ALLOCA [Lit n] [root]) t)
    (step_taint (mk_inst id ALLOCA [Lit n] [root]) s t tn)` by
    simp[inst_seq_ptr_def, ptr_inst_ok_alloca] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    run_inst_seq_gas_path_ptr >>
  fs[run_inst_seq_def, mk_inst_def, is_terminator_def]
QED

Theorem literal_alloca_old_observations:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s = OK t /\
  x <> root ==>
  lookup_var x t = lookup_var x s /\
  FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w cap)] [root]) t) x =
    FLOOKUP G x /\
  op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s t tn)
    (Var x) = op_taint tn (Var x)
Proof
  strip_tac >>
  reverse conj_tac
  >- simp[step_prov_other_output, step_taint_other_output, mk_inst_def] >>
  drule alloca_step_operand_preserved >>
  disch_then (qspec_then `Var x` mp_tac) >> simp[eval_operand_def]
QED

Theorem compile_alloc_buffer_path_resources_ptr:
  compile_alloc_buffer cap sa = (buf,sc) /\ fn_has_code sa sc fn /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  cap < dimword(:256) /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?root t b G1 tn1.
    buf.buf_operand = Var root /\ not_fresh_at sc root /\
    (~not_fresh_at sa root) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    lookup_var root t = SOME (n2w b) /\ b+cap < dimword(:256) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,cap) /\
    ptr_covers G1 tn1 root t cap /\
    alloca_inv t /\ alloca_room ctx fn t /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz)) /\
    (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) /\
    t.vs_labels = s.vs_labels /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_data_section = s.vs_data_section /\
    t.vs_call_ctx = s.vs_call_ctx /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule compile_alloc_buffer_emission >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)] [p]) (fn_insts fn)` by
    (drule_all fn_has_code_split >> strip_tac >>
     drule_all emit_inst_fn_member >> gvs[]) >>
  drule_at (Pat `MEM (mk_inst _ _ _ _) (fn_insts _)`)
    literal_alloca_step_resources_ptr >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `ptr_covers g1 tn1 _ _ _` >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX [mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)] [p]]
      (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
     simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 tn1
    (OK (t with vs_inst_idx := s.vs_inst_idx+1))` by
    (drule_at (Pat `step_inst_base _ _ = _`) literal_alloca_path_ptr >>
     disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
     disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
     disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] mp_tac) >>
     gvs[Abbr `g1`, Abbr `tn1`]) >>
  qexistsl [`p`,`t with vs_inst_idx := s.vs_inst_idx+1`,`b`,`g1`,`tn1`] >>
  suspend "endpoint"
QED
Resume compile_alloc_buffer_path_resources_ptr[endpoint]:
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def, mk_inst_def, exec_alloca_def,
       AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
  `p = STRING #"%" (toString sa.cs_next_var)` by metis_tac[operand_11] >>
  `alloca_inv (t with vs_inst_idx := s.vs_inst_idx+1)` by
    (qpat_x_assum `alloca_inv t` mp_tac >>
     simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]) >>
  `alloca_room ctx fn (t with vs_inst_idx := s.vs_inst_idx+1)` by
    (irule alloca_room_fields >> qexists `t` >> simp[]) >>
  `t.vs_labels = s.vs_labels /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_data_section = s.vs_data_section /\
   t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def, mk_inst_def, exec_alloca_def,
       AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
  `tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    simp[Abbr `tn1`, step_taint_def, out_taint_def, mk_inst_def,
      adopt_reset_def, store_taint_def, imm_taint_def] >>
  simp[] >>
  fs[ptr_covers_def, eval_operand_def, lookup_var_def] >>
  conj_tac >- metis_tac[optionTheory.SOME_11] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (strip_tac >> gvs[]) >>
  drule_at (Pat `step_inst_base _ _ = _`) literal_alloca_old_observations >>
  disch_then (qspec_then `x` mp_tac) >>
  simp[Abbr `g1`, Abbr `tn1`, lookup_var_def]
QED
Finalise compile_alloc_buffer_path_resources_ptr
