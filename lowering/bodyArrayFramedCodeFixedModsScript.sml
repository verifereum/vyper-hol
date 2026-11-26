(* A fixed array needs no header load or skip; its selector is
   location-independent once the base has been captured. *)
Theory bodyArrayFramedCodeFixedMods
Ancestors
  bodyArrayFramedMemoryAddressMods exprSimArrayIndex loweringShapeRules compileEnv
  fragGasOriginPtr fragExec venomState ptrDiscipline words finite_map pair

Theorem fixed_selector_emit_cuts[local]:
  compile_array_subscript bop iop F n ws elemBytes signed loader sa = (dst,sb) ==>
  ?sc sm offset out.
    array_bounds_check iop (Lit (n2w n)) signed sa = ((),sc) /\
    emit_op MUL [iop;Lit (n2w elemBytes)] sc = (Var offset,sm) /\
    emit_op ADD [bop;Var offset] sm = (Var out,sb) /\ dst = Var out
Proof
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[oneTheory.one] >>
  qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
  simp[array_elem_ptr_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_assum `emit_op MUL _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  gvs[] >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  gvs[]
QED

Theorem framed_code_fixed_address_mods:
  compile_array_subscript bop iop F n ws elemBytes signed loader sa = (dst,sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand bop s = SOME w /\ op_taint tn bop = {} /\ op_prov G bop = NONE /\
  eval_operand iop s = SOME iw /\ op_taint tn iop = {} /\ op_prov G iop = NONE /\
  (!q. bop = Var q ==> not_fresh_at sa q) /\ (!l. bop <> Label l) /\
  (!q. iop = Var q ==> not_fresh_at sa q) /\ (!l. iop <> Label l) /\
  idx_in_range signed iw (n2w n) ==>
  ?Gf tnf sf.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand dst sf = SOME (w + n2w (w2n iw * elemBytes)) /\
    op_taint tnf dst = {} /\ op_prov Gf dst = NONE /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_data_section = s.vs_data_section /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf)
Proof
  strip_tac >> drule_then strip_assume_tac fixed_selector_emit_cuts >>
  gvs[] >>
  drule_all (Q.INST [`i` |-> `w2n (iw:bytes32)`] framed_memory_fixed_address_run |> SRULE []) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gf`,`tnf`,`sf`] strip_assume_tac)) >>
  qexistsl [`Gf`,`tnf`,`sf`] >> simp[eval_operand_def]
QED
