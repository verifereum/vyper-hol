(* Scope the physical storage/transient slot-copy run at its installed exit. *)
Theory entryStageSlotUnwrap
Ancestors
  createCtorUnwrapSlotArrival createCtorSegmentArrival entryCreateUnwrapSlot
  entryCreatePathScope entryCreateFocusSpec createSizeCutRegion createSizeLocationCode
  createSizePrefixReplay createMarkedPath
  fragGasOrigin gasEvents venomExecSemantics venomExecProofs venomState fragGasOriginPtr
  exprSimAbiGasBridge abiEncoderProps fragExec compileEnv relation list
  bodyFullUnwrapSlotOrigin ptrSafeRun loweringStateRelDefs context ptrDiscipline
  bufferAllocationExecution slotCopyExecution exprSimPtrTopLevelStorageCopy
  words finite_map pred_set arithmetic pair

Theorem slot_band_origin_edge[local]:
  ~u.vs_halted /\ ctor_segment_fetch f u = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ctor_segment_next f u i = SOME v ==>
  gas_origin_edge F E C f u [] (OK v) /\ ~v.vs_halted
Proof
  simp[ctor_segment_fetch_def, ctor_segment_next_def, ctor_segment_entry_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac step_inst_base_OK_preserves_halted >>
  TRY (qpat_assum `OK _ = eval_phis _ _` (assume_tac o SYM) >>
       drule eval_phis_preserves_halted >> strip_tac) >>
  gvs[gas_origin_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke,Once gas_events_step_def] >> metis_tac[]
QED

Theorem slot_band_prefix[local]:
  create_cut_code {} a b /\ fn_has_code a b f /\
  (!target. lookup_block b.cs_current_bb f.fn_blocks = SOME target ==>
            phi_prefix_length target.bb_instructions <= LENGTH b.cs_current_insts) /\
  (!i. MEM i (frag_code a b) ==> i.inst_opcode <> GAS) /\
  (!bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids a b) /\
  create_operand_at a s /\ ~s.vs_halted /\
  RTC (\u v. ?i. ctor_segment_fetch f u = SOME i /\ i.inst_id IN frag_ids a b /\
                 i.inst_opcode <> INVOKE /\ ctor_segment_next f u i = SOME v) s t ==>
  create_expr_prefix a b E C f s [] t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_cut_region_rules >> strip_tac >>
  `create_cut_region a b s` by fs[create_operand_at_def] >>
  qpat_x_assum `RTC _ s t` mp_tac >>
  `!u. create_cut_region a b u /\ ~u.vs_halted /\
       create_expr_prefix a b E C f s [] u ==>
       !v i. ctor_segment_fetch f u = SOME i /\ i.inst_id IN frag_ids a b /\
             i.inst_opcode <> INVOKE /\ ctor_segment_next f u i = SOME v ==>
             create_cut_region a b v /\ ~v.vs_halted /\
             create_expr_prefix a b E C f s [] v` by
    (gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
     `?bb. lookup_block u.vs_current_bb f.fn_blocks = SOME bb /\
           get_instruction bb u.vs_inst_idx = SOME i` by
       fs[ctor_segment_fetch_def, AllCaseEqs()] >>
     `~(u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts)` by
       metis_tac[] >>
     `MEM i (frag_code a b)` by metis_tac[] >>
     `i.inst_opcode <> GAS` by metis_tac[] >>
     drule_all slot_band_origin_edge >>
     disch_then (qspecl_then [`E`,`C`] strip_assume_tac) >>
     `create_cut_region a b v` by metis_tac[] >> simp[] >>
     `create_expr_prefix a b E C f u [] v` by
       (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
        simp[create_marked_edge_def,create_prefix_step_def] >> metis_tac[]) >>
     metis_tac[APPEND_NIL,create_expr_prefix_append]) >>
  disch_tac >>
  qabbrev_tac `P = \u. create_cut_region a b u /\ ~u.vs_halted /\
                        create_expr_prefix a b E C f s [] u` >>
  `P t` suffices_by simp[Abbr `P`] >>
  irule RTC_lifts_invariants >> first_assum (irule_at Any) >>
  conj_tac >- simp[Abbr `P`] >>
  simp_tac bool_ss [Abbr `P`, PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!u. _ ==> !v i. _` drule_all >> simp[]
QED

(* The next fetch, if present, belongs to the supplied continuation rather
   than to the slot-copy fragment. It is not executed by this witness. *)
Theorem stage_ensure_slot_origin_scoped:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword (:256) /\ 32*n <= nb /\ n < 2**256 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ alloca_history func s /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb ==>
         phi_prefix_length bb.bb_instructions = 0) /\
  (!bb i. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH sb.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?root d a G0 tn0 Gf tnf t sm buf u.
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    op = Var root /\ d = n2w (buffer_allocation_base s sa.cs_next_id) /\
    compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root /\
    gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0) /\
    gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (a,G0,tn0) [] (OK t,Gf,tnf) /\
    gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    create_expr_prefix sa sb explicit ctx func s [] t /\ create_operand_at sb t /\
    (n <> 1 ==> ?cv ds.
      toplevel_copy_inv cv ds root src loc p (w2n d) n a G0 tn0 n Gf tnf t /\
      (!x. not_fresh_at sm x ==> ~MEM x ds) /\ ~t.vs_halted) /\
    (n = 1 ==>
      t = (mstore (w2n d) (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p)
        (update_var (STRING #"%" (toString sm.cs_next_var))
          (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p) a)
            with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      tnf.t_mem = (tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32}) UNION
        {w2n d+k | k IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) p} /\
      tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
      (!x. x <> STRING #"%" (toString sm.cs_next_var) ==>
         FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `n <> 1 ==> !bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb ==>
                    phi_prefix_length bb.bb_instructions = 0` by simp[] >>
  drule_all ctor_ensure_slot_band_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    (qx_choosel_then [`root`,`d`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`t`,`sm`,`buf`,`u`]
      strip_assume_tac)) >>
  `create_cut_code {} sa sb` by metis_tac[create_ensure_in_memory_cut_code,SND] >>
  `!i. MEM i (frag_code sa sb) ==> i.inst_opcode <> GAS` by
    (rpt strip_tac >> drule_all unwrap_slot_ensure_opcodes >> simp[]) >>
  `create_expr_prefix sa sb explicit ctx func s [] t` by
    (irule slot_band_prefix >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- simp[]
     >- simp[create_operand_at_def]
     >> simp_tac bool_ss [frag_ids_def, GSPECIFICATION, PAIR_EQ, EQ_CLAUSES,
                         GSYM CONJ_ASSOC] >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`root`,`d`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`t`,`sm`,`buf`,`u`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[create_operand_at_def]]
QED
