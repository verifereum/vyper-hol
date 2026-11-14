(* Slice's read-only length/data capture, on a common full endpoint. *)
Theory bodyFullBuiltinSliceDynamicCapture
Ancestors
  bodyFullUnwrapRun bodyPtrSignedConvertSourceFixed
  exprSimSliceMemory exprSimSliceCaptureControl builtinBytesMemory
  instSeqPtrLo fragGasSeqPtr bodyPtrDefs exprSimSliceOrdinaryFrame
  venomState venomExecSemantics exprLoweringProps list
  wordArgsPtr bodyPtrBopOperandRetention bodyPtrPrecompileBuiltinsGhost
  stmtSimLogArgs loweringPosts exprSimWordArgs

Theorem slice_dynamic_capture_full_run:
  compile_bytestring_src (Var src) sa = ((len,data),sb) /\
  fn_has_code sa sb func /\ not_fresh_at sa src /\
  lookup_var src s = SOME p /\ ptr_covers G tn src s capacity /\
  32 <= capacity /\ w2n p + 32 < dimword (:256) /\
  mload (w2n p) s = n2w (LENGTH bs) /\
  mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
  (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  w2n p + 32 <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    eval_operand data u = SOME (p+32w) /\
    op_taint tn' len = {} /\ op_prov G' len = NONE /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    u = s with vs_vars := u.vs_vars /\
    (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!n. 32 < capacity /\ 32+n <= capacity ==>
       ?dp. data = Var dp /\ ptr_covers G' tn' dp u n)
Proof
  strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
       eval_operand len u = SOME (mload (w2n p) s) /\
       eval_operand data u = SOME (p+32w) /\
       u = s with vs_vars := u.vs_vars /\
       (!x. not_fresh_at sa x ==> FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)` by
    (irule slice_bytestring_src_run >> qexists_tac `Var src` >>
     simp[eval_operand_def]) >>
  `!i. w2n p <= i /\ i < w2n p + 32 ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> gvs[]) >>
  drule_all compile_bytestring_src_fixed_frame >>
  disch_then (qspecl_then [`ARB`,`func`,`PG`] strip_assume_tac) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th` by
    (gen_tac >>
     drule_all compile_bytestring_src_fixed_frame >>
     disch_then (qspecl_then [`D`,`func`,`PG`] strip_assume_tac) >>
     qpat_x_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` assume_tac) >>
     qpat_x_assum `!k. inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` assume_tac) >>
     fs[] >>
     qpat_assum `inst_seq_ptr D _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[inst_seq_ptr_ghost_unique]) >>
  qexistsl_tac [`u`,`H`,`th`] >> simp[] >>
  gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
      qexistsl_tac [`emitted_insts sa sb`,`sa`] >> simp[] >>
      drule slice_bytestring_src_control >> strip_tac >> simp[] >>
      conj_tac >- (drule slice_bytestring_src_zero_code >> simp[EVERY_MEM]) >>
      conj_tac >- metis_tac[compile_bytestring_src_mem_ok, eval_operand_def] >>
      irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> simp[]
QED

(* Full child posts frame the captured window on their actual endpoint. *)
Theorem slice_dynamic_capture_full_frame:
  expr_sim_inv cenv cx env es /\ expr_sim_inv cenv cx env' es1 /\
  stmt_state_rel H ctx func cenv cx es s /\
  expr_val_at cenv cx (BaseT bt) sa sb es v src s /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME vt /\
  ~is_word_type (BaseT bt) /\ eval_operand src s = SOME p /\
  32 + LENGTH bs <= val_footprint vt v /\
  mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
  (!i. w2n p + 32 <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
  local_ptrs_reserved cenv sb /\ sb.cs_next_id <= sc.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (!z. src = Var z ==> not_fresh_at sb z) /\ (!l. src <> Label l) /\
  expr_post H ctx func cenv cx start es sb sc s es1 v1 op1 t /\
  expr_post H ctx func cenv cx length es1 sc sd t es2 v2 op2 u /\
  ghost_kept_at lo cenv es sb G tn s G1 tn1 /\
  ghost_kept_at lo cenv es1 sc G1 tn1 t G2 tn2 ==>
  mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
  (!i. w2n p + 32 <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn2.t_mem) /\
  (!op w. (!z. op = Var z ==> not_fresh_at sb z /\ not_fresh_at sc z) /\
          (!l. op <> Label l) /\ eval_operand op s = SOME w ==>
          eval_operand op u = SOME w) /\
  (!dp n. not_fresh_at sb dp /\ not_fresh_at sc dp /\
          ptr_covers G tn dp s n ==> ptr_covers G2 tn2 dp u n)
Proof
  strip_tac >>
  `wb_frame cenv es es1 sb s t` by
    (irule expr_post_frame >> goal_assum (drule_at Any)) >>
  `!n b sz. local_region cenv es1.scopes t n b sz <=>
             local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> drule_all log_frame_local_region >> simp[]) >>
  `ghost_kept_at lo cenv es sb G tn s G2 tn2` by
    (irule ghost_kept_at_trans >> goal_assum (drule_at Any) >>
     qexistsl_tac [`G1`,`sc`,`tn1`] >>
     gvs[expr_post_def]) >>
  `ghost_kept cenv es sb G tn s G2 tn2` by
    (qpat_x_assum `ghost_kept_at lo cenv es sb G tn s G2 tn2` mp_tac >>
     simp[ghost_kept_def, ghost_kept_at_def] >> metis_tac[]) >>
  `log_arg_clear cenv cx (BaseT bt) v` by
    (irule log_arg_clear_base >> goal_assum (drule_at Any)) >>
  conj_tac >- (drule_all slice_dynamic_payload_two_operands >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> spose_not_then assume_tac >>
      `w2n p <= i /\ i < w2n p + val_footprint vt v` by decide_tac >>
      drule_all bop_argument_taint_kept >> metis_tac[]) >>
  conj_tac >- metis_tac[slice_two_posts_operands] >>
  rpt strip_tac >>
  `?w. eval_operand (Var dp) s = SOME w` by
    gvs[ptr_covers_def, eval_operand_def] >>
  `eval_operand (Var dp) u = SOME w` by
    (irule slice_captured_operand_two_posts >> simp[] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  irule ghost_kept_ptr_covers >>
  goal_assum (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  qexists_tac `w` >> simp[]
QED
